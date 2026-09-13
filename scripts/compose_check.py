#!/usr/bin/env python3
"""Prove a template's compose stack is one Docker will accept, its images
exist, and (nightly, a rotating few) that it actually comes up.

    python3 scripts/compose_check.py                    # every template: render + compose config
    python3 scripts/compose_check.py --changed origin/main   # only templates a PR touched
    python3 scripts/compose_check.py --manifests        # also `docker manifest inspect` every image
    python3 scripts/compose_check.py --up 5             # also start 5 templates (rotates daily)
    python3 scripts/compose_check.py --ids ghost,gitea  # an explicit set

Layers, cheapest first, each one gating the next for a template:

1. render   - substitute every ${VAR} the way the panel's installer does
              (declared defaults, generated placeholders for password/random/
              uuid/port, ${APP_NAME}, ${SERVICE_*} magic). An unresolved token
              fails here; the panel would ship it to Docker verbatim.
2. config   - `docker compose config` on the rendered file. Catches YAML the
              panel's own validator cannot judge: unknown keys, bad port
              syntax, a volume used but never declared, a malformed healthcheck.
3. manifest - `docker manifest inspect <image>` for every image the stack
              references, without pulling. A retagged or deleted upstream image
              is the single most common way a working template silently dies.
              Counts against the registry's anonymous pull rate limit, so PRs
              run it for changed templates only and the nightly sweeps all.
4. up       - `compose up`, wait until every service reports running (or a
              one-shot exits 0), request the first declared HTTP port, then
              `compose down -v`. Templates that need hardware, host networking
              or elevated privileges are skipped; a CI runner has none of those.

Needs PyYAML and the docker CLI with the compose plugin. Exit 1 on any error.
Writes a Markdown summary to $GITHUB_STEP_SUMMARY when set.
"""
from __future__ import annotations

import argparse
import base64
import datetime as dt
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.request
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
TEMPLATES_DIR = ROOT / "templates"
VAR_PATTERN = re.compile(r"\$\{([A-Z_][A-Z0-9_]*)\}")
# Compose keys that mean "this needs the real machine", not a CI runner.
HOST_BOUND_KEYS = ("devices", "privileged", "network_mode", "cap_add", "pid", "ipc")
# Runner memory is ~7 GB; leave room for Docker and the runner itself.
UP_MEMORY_LIMIT_MB = 3072
UP_READY_SECONDS = 180
UP_HTTP_SECONDS = 120


def sh(args, *, timeout=300, cwd=None, env=None, check=True):
    result = subprocess.run(args, cwd=cwd, env=env, capture_output=True, text=True, timeout=timeout)
    if check and result.returncode != 0:
        raise RuntimeError((result.stderr or result.stdout).strip()[-800:] or f"exit {result.returncode}")
    return result


# --------------------------------------------------------------------- render

def placeholder(name: str, var: dict, port_base: list[int]) -> str:
    kind = var.get("type", "string")
    default = var.get("default", "")
    if kind == "port":
        # The panel always allocates a free port; here any unused high port
        # is fine as long as templates in one `up` batch never collide.
        port_base[0] += 1
        return str(port_base[0])
    if kind == "password":
        length = int(var.get("length", 32) or 32)
        return ("Ci" + hashlib.sha256(name.encode()).hexdigest())[:max(8, length)]
    if kind == "random":
        length = int(var.get("length", 16) or 16)
        return hashlib.sha256(("r" + name).encode()).hexdigest()[:max(4, length)]
    if kind == "uuid":
        return "00000000-0000-4000-8000-" + hashlib.md5(name.encode()).hexdigest()[:12]
    return str(default) if default not in (None, "") else "ci"


def magic(name: str) -> str | None:
    if name.startswith("SERVICE_PASSWORD_"):
        return "CiMagicPassword" + hashlib.sha256(name.encode()).hexdigest()[:16]
    if name.startswith("SERVICE_USER_"):
        return "ciuser"
    if name.startswith("SERVICE_FQDN_"):
        return "ci.example.test"
    if name.startswith("SERVICE_URL_"):
        return "http://ci.example.test"
    if name.startswith("SERVICE_BASE64_"):
        return base64.b64encode(hashlib.sha256(name.encode()).digest()).decode()
    return None


def apply_files(compose: dict, template: dict, values: dict) -> list[tuple[str, str]]:
    """Mirror the panel: every `files:` entry with an absolute path is written
    beside the compose file and bind-mounted into every service, replacing a
    named volume whose target is that file's directory. Returns the files to
    write as (basename, content)."""
    written, mounts = [], []
    for spec in template.get("files") or []:
        if not isinstance(spec, dict) or not spec.get("path"):
            continue
        content = VAR_PATTERN.sub(lambda m: values.get(m.group(1), m.group(0)), str(spec.get("content", "")))
        name = os.path.basename(spec["path"])
        written.append((name, content))
        if str(spec["path"]).startswith("/"):
            mounts.append((f"./{name}", spec["path"], os.path.dirname(spec["path"]).rstrip("/")))
    if mounts:
        removed = set()
        for service in (compose.get("services") or {}).values():
            if not isinstance(service, dict):
                continue
            kept = []
            for volume in service.get("volumes") or []:
                parts = volume.split(":") if isinstance(volume, str) else []
                if len(parts) >= 2 and any(parts[1].rstrip("/") == d for _, _, d in mounts):
                    removed.add(parts[0])
                    continue
                kept.append(volume)
            kept += [f"{local}:{target}" for local, target, _ in mounts if f"{local}:{target}" not in kept]
            service["volumes"] = kept
        for name in removed:
            (compose.get("volumes") or {}).pop(name, None)
        if "volumes" in compose and not compose["volumes"]:
            del compose["volumes"]
    return written


def render(template: dict, app_name: str, port_base: list[int]) -> tuple[str, dict, list[tuple[str, str]]]:
    """The compose file as the panel would write it, the variables used, and
    the companion files to write next to it."""
    values = {"APP_NAME": app_name}
    raw_vars = template.get("variables") or []
    declared = raw_vars if isinstance(raw_vars, list) else [
        {"name": k, **(v if isinstance(v, dict) else {"default": v})} for k, v in raw_vars.items()]
    for var in declared:
        if isinstance(var, dict) and var.get("name"):
            values[var["name"]] = placeholder(var["name"], var, port_base)
    compose = json.loads(json.dumps(template["compose"]))  # a private copy to mutate
    unresolved = set()

    def sub(match):
        name = match.group(1)
        if name in values:
            return values[name]
        value = magic(name)
        if value is None:
            unresolved.add(name)
            return match.group(0)
        values[name] = value
        return value

    dump = lambda doc: yaml.safe_dump(doc, sort_keys=False, default_flow_style=False, allow_unicode=True)
    text = VAR_PATTERN.sub(sub, dump(compose))
    if unresolved:
        raise RuntimeError("unresolved variable(s): " + ", ".join(sorted(unresolved)))
    # Files come after the variable pass so their bind mounts land in the same
    # document; every magic value they need is already in `values`.
    files = apply_files(compose, template, values)
    if files:
        text = VAR_PATTERN.sub(sub, dump(compose))
    return text, values, files


def host_bound(compose: dict) -> str | None:
    for service_name, service in (compose.get("services") or {}).items():
        if not isinstance(service, dict):
            continue
        for key in HOST_BOUND_KEYS:
            if key in service and service[key] not in (None, False, "bridge"):
                return f"{service_name} uses {key}"
    return None


def memory_mb(template: dict) -> int:
    raw = str((template.get("requirements") or {}).get("memory", "0")).strip().upper()
    match = re.match(r"(\d+(?:\.\d+)?)\s*([KMGT]?)B?", raw)
    if not match:
        return 0
    value, unit = float(match.group(1)), match.group(2)
    return int(value * {"": 1 / 1024 / 1024, "K": 1 / 1024, "M": 1, "G": 1024, "T": 1024 * 1024}[unit])


# --------------------------------------------------------------------- checks

class Report:
    def __init__(self):
        self.rows: list[tuple[str, str, str, str]] = []  # id, layer, status, detail
        self.errors = 0

    def ok(self, tid, layer, detail=""):
        self.rows.append((tid, layer, "ok", detail))

    def skip(self, tid, layer, detail):
        self.rows.append((tid, layer, "skipped", detail))

    def fail(self, tid, layer, detail):
        self.errors += 1
        self.rows.append((tid, layer, "FAIL", detail))

    def markdown(self) -> str:
        lines = ["| template | layer | result | detail |", "|---|---|---|---|"]
        for tid, layer, status, detail in self.rows:
            if status == "ok" and layer in ("render", "config"):
                continue  # keep the summary readable; failures and skips matter
            lines.append(f"| {tid} | {layer} | {status} | {detail.replace('|', '/')[:160]} |")
        checked = len({r[0] for r in self.rows})
        return f"{checked} templates checked, {self.errors} error(s)\n\n" + "\n".join(lines) + "\n"


def compose_config(workdir: Path, project: str) -> list[str]:
    sh(["docker", "compose", "-p", project, "-f", str(workdir / "docker-compose.yml"), "config", "-q"], cwd=workdir)
    images = sh(["docker", "compose", "-p", project, "-f", str(workdir / "docker-compose.yml"), "config", "--images"],
                cwd=workdir).stdout.split()
    return sorted(set(images))


_manifest_cache: dict[str, str | None] = {}


def manifest_exists(image: str) -> str | None:
    """None when the image resolves; otherwise the registry's complaint."""
    if image not in _manifest_cache:
        try:
            sh(["docker", "manifest", "inspect", image], timeout=120)
            _manifest_cache[image] = None
        except (RuntimeError, subprocess.TimeoutExpired) as exc:
            _manifest_cache[image] = str(exc).splitlines()[-1][:200] if str(exc) else "manifest inspect failed"
    return _manifest_cache[image]


def http_port(template: dict, values: dict) -> str | None:
    for entry in template.get("ports") or []:
        if isinstance(entry, dict) and entry.get("protocol", "http") in ("http", "https"):
            port = str(entry.get("port", ""))
            port = VAR_PATTERN.sub(lambda m: values.get(m.group(1), m.group(0)), port)
            if port.isdigit():
                return port
    return None


def bring_up(workdir: Path, project: str, template: dict, values: dict) -> str:
    compose = ["docker", "compose", "-p", project, "-f", str(workdir / "docker-compose.yml")]
    try:
        sh(compose + ["up", "-d", "--quiet-pull"], timeout=900, cwd=workdir)
        deadline = time.time() + UP_READY_SECONDS
        while True:
            raw = sh(compose + ["ps", "-a", "--format", "json"], cwd=workdir).stdout
            services = [json.loads(line) for line in raw.splitlines() if line.strip()]
            if not services:
                raise RuntimeError("compose up started no services")
            exited_badly = [s for s in services if s.get("State") == "exited" and s.get("ExitCode") not in (0, None)]
            if exited_badly:
                logs = sh(compose + ["logs", "--no-color", "--tail", "20", exited_badly[0]["Service"]],
                          cwd=workdir, check=False).stdout
                raise RuntimeError(f"{exited_badly[0]['Service']} exited {exited_badly[0].get('ExitCode')}: "
                                   + logs.strip()[-300:])
            pending = [s for s in services if s.get("State") not in ("running", "exited")
                       or (s.get("Health") or "") == "starting"]
            if not pending:
                break
            if time.time() > deadline:
                raise RuntimeError("services still not running after %ss: %s" % (
                    UP_READY_SECONDS, ", ".join(f"{s['Service']}={s.get('State')}/{s.get('Health') or '-'}" for s in pending)))
            time.sleep(5)
        unhealthy = [s for s in services if (s.get("Health") or "") == "unhealthy"]
        if unhealthy:
            raise RuntimeError("unhealthy: " + ", ".join(s["Service"] for s in unhealthy))
        port = http_port(template, values)
        if port:
            deadline = time.time() + UP_HTTP_SECONDS
            last = "no response"
            while time.time() < deadline:
                try:
                    with urllib.request.urlopen(f"http://127.0.0.1:{port}/", timeout=5) as res:
                        return f"running; HTTP {res.status} on :{port}"
                except urllib.error.HTTPError as exc:
                    return f"running; HTTP {exc.code} on :{port}"  # answering at all is the point
                except (OSError, urllib.error.URLError) as exc:
                    last = str(exc)[:80]
                time.sleep(3)
            raise RuntimeError(f"running but nothing answered on :{port} within {UP_HTTP_SECONDS}s ({last})")
        return "running (no HTTP port declared)"
    finally:
        sh(compose + ["down", "-v", "--remove-orphans", "--timeout", "20"], timeout=300, cwd=workdir, check=False)


# ----------------------------------------------------------------------- main

def load(tid: str) -> dict:
    with (TEMPLATES_DIR / f"{tid}.yaml").open(encoding="utf-8") as fh:
        return yaml.safe_load(fh) or {}


def changed_ids(base: str) -> list[str]:
    out = sh(["git", "diff", "--name-only", f"{base}...HEAD", "--", "templates/"], cwd=ROOT).stdout
    ids = []
    for line in out.splitlines():
        path = ROOT / line.strip()
        if path.suffix in (".yaml", ".yml") and path.exists():
            ids.append(path.stem)
    return sorted(set(ids))


def rotation(ids: list[str], count: int, seed: str | None) -> list[str]:
    """A different slice each day so the whole catalog is covered over time."""
    if count >= len(ids):
        return ids
    key = seed or dt.date.today().isoformat()
    start = int(hashlib.sha256(key.encode()).hexdigest(), 16) % len(ids)
    ordered = ids[start:] + ids[:start]
    return ordered[:count]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--ids", help="comma-separated template ids")
    parser.add_argument("--changed", metavar="BASE", help="only templates changed since this git ref")
    parser.add_argument("--manifests", action="store_true", help="verify every referenced image exists")
    parser.add_argument("--up", type=int, default=0, metavar="N", help="bring N templates up (daily rotation)")
    parser.add_argument("--seed", help="rotation seed (default: today's date)")
    parser.add_argument("--keep-images", action="store_true", help="do not remove pulled images after --up")
    args = parser.parse_args()

    if args.ids:
        ids = [i.strip() for i in args.ids.split(",") if i.strip()]
    elif args.changed:
        ids = changed_ids(args.changed)
    else:
        ids = sorted(p.stem for p in TEMPLATES_DIR.glob("*.yaml"))
    report = Report()
    if not ids:
        print("no templates selected")
        return 0

    rendered: dict[str, tuple[Path, dict, dict]] = {}
    port_base = [18000]
    tmp = Path(tempfile.mkdtemp(prefix="sk-templates-"))
    try:
        for tid in ids:
            try:
                template = load(tid)
            except Exception as exc:  # noqa: BLE001 - reported per template
                report.fail(tid, "render", f"cannot parse: {exc}")
                continue
            if template.get("kind") == "repo" or "compose" not in template:
                report.skip(tid, "render", "repo template or no compose block")
                continue
            project = f"skci-{tid}"[:60]
            workdir = tmp / tid
            workdir.mkdir()
            try:
                text, values, files = render(template, project, port_base)
                (workdir / "docker-compose.yml").write_text(text, encoding="utf-8")
                for name, content in files:
                    (workdir / name).write_text(content, encoding="utf-8")
                report.ok(tid, "render")
            except Exception as exc:  # noqa: BLE001
                report.fail(tid, "render", str(exc))
                continue
            try:
                images = compose_config(workdir, project)
                report.ok(tid, "config", ", ".join(images))
            except Exception as exc:  # noqa: BLE001
                report.fail(tid, "config", str(exc))
                continue
            rendered[tid] = (workdir, template, values)
            if args.manifests:
                for image in images:
                    problem = manifest_exists(image)
                    if problem:
                        report.fail(tid, "manifest", f"{image}: {problem}")
                    else:
                        report.ok(tid, "manifest", image)

        if args.up:
            for tid in rotation(sorted(rendered), args.up, args.seed):
                workdir, template, values = rendered[tid]
                reason = host_bound(template["compose"])
                if reason:
                    report.skip(tid, "up", reason)
                    continue
                need = memory_mb(template)
                if need > UP_MEMORY_LIMIT_MB:
                    report.skip(tid, "up", f"declares {need} MB of memory")
                    continue
                try:
                    report.ok(tid, "up", bring_up(workdir, f"skci-{tid}"[:60], template, values))
                except Exception as exc:  # noqa: BLE001
                    report.fail(tid, "up", str(exc))
                if not args.keep_images:
                    sh(["docker", "image", "prune", "-af"], check=False, timeout=300)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    summary = report.markdown()
    print(summary)
    step_summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if step_summary:
        with open(step_summary, "a", encoding="utf-8") as fh:
            fh.write("## Template compose check\n\n" + summary)
    return 1 if report.errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
