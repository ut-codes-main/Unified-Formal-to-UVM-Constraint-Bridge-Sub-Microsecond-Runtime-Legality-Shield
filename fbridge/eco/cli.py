from __future__ import annotations

import argparse
import glob
import json
import sys
from pathlib import Path

from .cones import load_design
from .diff import git_diff, git_head, git_toplevel, parse_unified_diff
from .tracker import evaluate, import_sby, load_certs, save_index, seal, svh_include, unreachable_bins


def _files(patterns: list[str]) -> list[Path]:
    out = []
    for p in patterns:
        hits = glob.glob(p, recursive=True)
        out += [Path(h) for h in (hits or [p])]
    return sorted(set(out))


def _root(a) -> Path:
    if a.root:
        return Path(a.root).resolve()
    try:
        return git_toplevel(Path.cwd())
    except Exception:
        return Path.cwd().resolve()


def _design(a, root: Path):
    return load_design([p.resolve() for p in _files(a.rtl)], root)


def cmd_import_sby(a) -> int:
    root = _root(a)
    design = _design(a, root)
    certs = import_sby(Path(a.log).read_text(), design, a.engine)
    rev = a.rev or git_head(root)
    certs = [seal(c, design, rev) for c in certs]
    save_index(a.out, certs, {"root": str(root), "rev": rev, "source": a.log})
    print(f"eco_unreach_tracker: {len(certs)} unreachability certificates indexed -> {a.out}")
    for c in certs:
        print(f"  {c.bin}: cone {len(c.cone)} signals, {len(c.files)} files")
    return 0


def cmd_index(a) -> int:
    root = _root(a)
    design = _design(a, root)
    certs, meta = load_certs(a.certs)
    rev = a.rev or git_head(root)
    certs = [seal(c, design, rev) for c in certs]
    meta.update({"root": str(root), "rev": rev})
    save_index(a.out, certs, meta)
    print(f"eco_unreach_tracker: re-indexed {len(certs)} certificates -> {a.out}")
    return 0


def cmd_update(a) -> int:
    root = _root(a)
    design = _design(a, root)
    certs, meta = load_certs(a.index)
    hunks = []
    if a.diff:
        hunks = parse_unified_diff(Path(a.diff).read_text())
    elif a.git_base:
        rels = sorted({f for c in certs for f in c.files})
        hunks = parse_unified_diff(git_diff(root, a.git_base, rels or None))
    verdicts = evaluate(certs, design, hunks)
    result = unreachable_bins(certs, verdicts, {"index": str(a.index), "base_rev": meta.get("rev", ""), "head_rev": git_head(root),
                                                 "hunks": len(hunks)})
    out = Path(a.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2))
    if a.svh:
        Path(a.svh).write_text(svh_include(result, certs))
    s = result["summary"]
    print(f"eco_unreach_tracker: {s['unreachable']} still unreachable, {s['invalidated']} invalidated (of {s['certificates']}) -> {out}")
    for v in result["invalidated"]:
        touched = f" touched: {', '.join(v['touched_signals'])}" if v["touched_signals"] else ""
        print(f"  re-prove {v['bin']}: {v['reason']}.{touched}")
    if a.refresh_index:
        valid = {v.certificate for v in verdicts if v.valid}
        keep = [seal(c, design) if c.id in valid else c for c in certs]
        save_index(a.index, keep, meta)
    return 1 if (a.fail_on_invalidated and s["invalidated"]) else 0


def cmd_cone(a) -> int:
    root = _root(a)
    design = _design(a, root)
    cone = design.cone(a.signals)
    for n in sorted(cone):
        drv = design.drivers.get(n, [])
        lines = ", ".join(f"{d.file}:{d.start}" for d in drv if d.start)
        print(f"{n}  {lines}")
    return 0


def main(argv=None) -> int:
    p = argparse.ArgumentParser(prog="eco_unreach_tracker", description="Incremental unreachability cone index")
    sub = p.add_subparsers(dest="cmd", required=True)

    def common(sp):
        sp.add_argument("--rtl", nargs="+", required=True, help="RTL/formal source files or globs")
        sp.add_argument("--root", help="path that file names are relative to (default: git toplevel)")

    s = sub.add_parser("import-sby", help="create certificates from a SymbiYosys cover-mode log")
    common(s)
    s.add_argument("--log", required=True)
    s.add_argument("--engine")
    s.add_argument("--rev")
    s.add_argument("--out", default="unreach_index.json")
    s.set_defaults(fn=cmd_import_sby)

    i = sub.add_parser("index", help="(re)compute cones and fingerprints for certificates")
    common(i)
    i.add_argument("--certs", required=True)
    i.add_argument("--rev")
    i.add_argument("--out", default="unreach_index.json")
    i.set_defaults(fn=cmd_index)

    u = sub.add_parser("update", help="apply an RTL change and emit the live unreachable_bins mask")
    common(u)
    u.add_argument("--index", required=True)
    u.add_argument("--diff", help="unified diff file describing the ECO")
    u.add_argument("--git-base", help="git revision to diff the working tree against")
    u.add_argument("--out", default="unreachable_bins.json")
    u.add_argument("--svh", help="also write an SV include with the bin list and ignore_bins macros")
    u.add_argument("--refresh-index", action="store_true", help="rewrite index for certificates that remain valid")
    u.add_argument("--fail-on-invalidated", action="store_true")
    u.set_defaults(fn=cmd_update)

    c = sub.add_parser("cone", help="print the fan-in cone of signals")
    common(c)
    c.add_argument("signals", nargs="+", help="module.signal names")
    c.set_defaults(fn=cmd_cone)

    a = p.parse_args(argv)
    return a.fn(a)


if __name__ == "__main__":
    sys.exit(main())
