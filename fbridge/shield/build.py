from __future__ import annotations

import importlib.util
import os
import shlex
import shutil
import subprocess
import sys
from pathlib import Path


class BuildError(Exception):
    pass


def c_compiler() -> list[str]:
    env = os.environ.get("FBRIDGE_CC")
    if env:
        return shlex.split(env)
    if importlib.util.find_spec("ziglang") is not None:
        return [sys.executable, "-m", "ziglang", "cc"]
    for cc in ("clang", "gcc", "cc"):
        path = shutil.which(cc)
        if path:
            return [path]
    raise BuildError("no C compiler found; pip install ziglang or set FBRIDGE_CC")


def shared_suffix() -> str:
    if sys.platform.startswith("win"):
        return ".dll"
    if sys.platform == "darwin":
        return ".dylib"
    return ".so"


def exe_suffix() -> str:
    return ".exe" if sys.platform.startswith("win") else ""


def _run(cmd: list[str]) -> None:
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode:
        raise BuildError(f"compile failed: {' '.join(cmd)}\n{r.stdout}\n{r.stderr}")


def build_shared(sources: list[Path], out: Path, opt: str = "-O3", defines: list[str] | None = None) -> Path:
    out = out.with_suffix(shared_suffix())
    out.parent.mkdir(parents=True, exist_ok=True)
    cmd = c_compiler() + [opt, "-shared", "-std=c99", "-Wall", "-Wno-unused-function"]
    if not sys.platform.startswith("win"):
        cmd.append("-fPIC")
    cmd += [f"-D{d}" for d in defines or []]
    cmd += ["-I", str(sources[0].parent), "-o", str(out)] + [str(s) for s in sources]
    _run(cmd)
    return out


def build_exe(sources: list[Path], out: Path, include_dirs: list[Path], opt: str = "-O3", defines: list[str] | None = None) -> Path:
    out = out.with_suffix(exe_suffix()) if exe_suffix() else out
    out.parent.mkdir(parents=True, exist_ok=True)
    cmd = c_compiler() + [opt, "-std=c99", "-Wall", "-Wno-unused-function"]
    if os.environ.get("FBRIDGE_MARCH", "native") and not sys.platform == "darwin":
        cmd.append(f"-march={os.environ.get('FBRIDGE_MARCH', 'native')}")
    cmd += [f"-D{d}" for d in defines or []]
    for d in include_dirs:
        cmd += ["-I", str(d)]
    cmd += ["-o", str(out)] + [str(s) for s in sources]
    _run(cmd)
    return out
