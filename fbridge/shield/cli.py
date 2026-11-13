from __future__ import annotations

import argparse
import sys
from pathlib import Path

from .build import build_shared
from .compile import compile_shield
from .emit import write_artifacts
from .inputs import load_shield_spec
from .model import ShieldModel


def _kv(text: str | None) -> dict[str, int]:
    out = {}
    for part in (text or "").split(","):
        if part.strip():
            k, v = part.split("=", 1)
            out[k.strip()] = v.strip()
    return out


def _resolve(spec, values: dict[str, str]) -> dict[str, int]:
    out = {}
    for k, v in values.items():
        f = spec.field(k)
        names = dict(f.enum)
        out[k] = names[v] if v in names else int(v, 0)
    return out


def cmd_compile(a) -> int:
    spec = load_shield_spec(a.spec)
    imm = {x.strip() for x in (a.immutable or "").split(",") if x.strip()}
    comp = compile_shield(spec, imm)
    art = write_artifacts(comp, a.out, a.prefix, aliases=not a.no_aliases)
    st = comp.stats
    print(f"shield_gen: {spec.name} mode={comp.mode} reachable={st['reachable_states']}/{st['state_space']} "
          f"classes={st['classes']} nodes={st['table_nodes']} depth={st['depth']}")
    for w in comp.warnings:
        print(f"  warning: {w}")
    for k, p in art.paths.items():
        print(f"  {k}: {p}")
    if a.build:
        lib = build_shared([art.paths["c"]], Path(a.out) / "sv_legality_shield")
        print(f"  lib: {lib}")
    return 0


def cmd_query(a) -> int:
    spec = load_shield_spec(a.spec)
    comp = compile_shield(spec)
    model = ShieldModel(comp)
    s = spec.pack(_resolve(spec, _kv(a.state)), "state")
    tx = spec.pack(_resolve(spec, _kv(a.action)), "action")
    legal = model.is_action_legal(s, tx)
    status, rep, masks = model.project_or_mask_action(s, tx)
    print(f"state_hash=0x{s:X} candidate_tx=0x{tx:X} legal={int(legal)} class={model.class_of(s)} reachable={int(model.is_state_reachable(s))}")
    ex = model.explain(s, tx)
    bad = [n for i, n in enumerate(comp.rule_names) if (ex >> i) & 1]
    if bad:
        print(f"  violated: {', '.join(bad)}")
    print(f"  project status={status} repaired=0x{rep:X} {spec.unpack(rep, 'action')}")
    return 0 if legal else 1


def cmd_bench(a) -> int:
    from .bench import main as bench_main
    return bench_main([a.spec, "--out", a.out, "--rounds", str(a.rounds), "--budget-ns", str(a.budget_ns)])


def main(argv=None) -> int:
    p = argparse.ArgumentParser(prog="shield_gen", description="Offline formal-to-runtime legality shield compiler")
    sub = p.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("compile", help="compile a shield spec into C/DPI/SV artifacts")
    c.add_argument("spec")
    c.add_argument("--out", default="build/shield")
    c.add_argument("--prefix", help="C/SV symbol prefix (default: spec name)")
    c.add_argument("--immutable", help="comma-separated action fields that repair must never change")
    c.add_argument("--no-aliases", action="store_true", help="omit unprefixed is_action_legal/project_or_mask_action")
    c.add_argument("--build", action="store_true", help="also build a shared library with the bundled C compiler")
    c.set_defaults(fn=cmd_compile)
    q = sub.add_parser("query", help="evaluate one state/action pair with the reference model")
    q.add_argument("spec")
    q.add_argument("--state", required=True, help="e.g. line=S,pend=NONE,credits=3,excl=0")
    q.add_argument("--action", required=True, help="e.g. op=CleanUnique,size=6")
    q.set_defaults(fn=cmd_query)
    b = sub.add_parser("bench", help="compile, build and measure latency")
    b.add_argument("spec")
    b.add_argument("--out", default="build/bench")
    b.add_argument("--rounds", type=int, default=200000)
    b.add_argument("--budget-ns", type=float, default=1000.0)
    b.set_defaults(fn=cmd_bench)
    a = p.parse_args(argv)
    return a.fn(a)


if __name__ == "__main__":
    sys.exit(main())
