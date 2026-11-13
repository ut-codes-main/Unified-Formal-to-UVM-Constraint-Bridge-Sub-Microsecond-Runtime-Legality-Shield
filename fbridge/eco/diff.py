from __future__ import annotations

import re
import subprocess
from dataclasses import asdict, dataclass
from pathlib import Path

HUNK = re.compile(r"^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@")


@dataclass(frozen=True)
class Hunk:
    file: str
    old_start: int
    old_len: int
    new_start: int
    new_len: int

    def old_range(self) -> tuple[int, int]:
        if self.old_len == 0:
            return self.old_start, self.old_start + 1
        return self.old_start, self.old_start + self.old_len - 1

    def new_range(self) -> tuple[int, int]:
        if self.new_len == 0:
            return self.new_start, self.new_start + 1
        return self.new_start, self.new_start + self.new_len - 1

    def to_dict(self) -> dict:
        return asdict(self)


def parse_unified_diff(text: str) -> list[Hunk]:
    out, cur = [], None
    for line in text.splitlines():
        if line.startswith("+++ "):
            path = line[4:].strip().split("\t")[0]
            cur = None if path == "/dev/null" else re.sub(r"^[ab]/", "", path)
            continue
        if line.startswith("--- "):
            continue
        m = HUNK.match(line)
        if m and cur is not None:
            out.append(Hunk(cur, int(m.group(1)), int(m.group(2) or 1), int(m.group(3)), int(m.group(4) or 1)))
    return out


def git_toplevel(path: str | Path) -> Path:
    r = subprocess.run(["git", "rev-parse", "--show-toplevel"], cwd=str(path), capture_output=True, text=True, check=True)
    return Path(r.stdout.strip())


def git_head(path: str | Path) -> str:
    r = subprocess.run(["git", "rev-parse", "HEAD"], cwd=str(path), capture_output=True, text=True)
    return r.stdout.strip() if r.returncode == 0 else ""


def git_diff(repo: str | Path, base: str, paths: list[str] | None = None) -> str:
    cmd = ["git", "diff", "-U0", "--no-color", base]
    if paths:
        cmd += ["--"] + paths
    r = subprocess.run(cmd, cwd=str(repo), capture_output=True, text=True, check=True)
    return r.stdout


def overlaps(a: tuple[int, int], b: tuple[int, int]) -> bool:
    return a[0] <= b[1] and b[0] <= a[1]
