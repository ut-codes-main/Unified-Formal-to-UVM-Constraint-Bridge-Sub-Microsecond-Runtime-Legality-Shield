from __future__ import annotations

import argparse
import sys
from pathlib import Path

from ..backends.sva_emit import emit_assumes
from ..backends.uvm_emit import emit_item_class
from ..frontends.fbr_dsl import load_single_source
from ..frontends.sva_assume import load_sva
from ..frontends.uvm_constraints import load_uvm_item
from ..mapping import load_mapping
from .checker import run_audit
from .report import unified_ast, write_reports

SEVERITY = {"never": -1, "error": 0, "warning": 1, "info": 2}


def cmd_check(a) -> int:
    mapping = load_mapping(a.map)
    uvm = load_uvm_item(a.uvm, a.cls) if a.uvm else None
    spec = load_single_source(a.spec, a.item).cset if a.spec else None
    item_schema = (uvm.cset.schema if uvm else spec.schema)
    sva = load_sva(a.sva, schema=mapping.signal_schema(item_schema))
    sig = mapping.signal_schema(item_schema).merged(sva.cset.schema)
    audit = run_audit(uvm.cset if uvm else None, sva.cset.rules, sig, mapping, spec)
    for w in (uvm.warnings if uvm else []) + sva.warnings:
        audit.warnings.append(w)
    paths = write_reports(a.out, audit, unified_ast(uvm.cset if uvm else None, sva.cset, mapping, spec, audit))
    counts = audit.counts()
    print(f"uvm_formal_sync: {audit.verdict()} (errors={counts['error']} warnings={counts['warning']} info={counts['info']})")
    for f in audit.findings:
        if SEVERITY[f.severity] <= 1:
            print(f"  [{f.severity}] {f.kind} {f.subject} ({f.pair}, view {f.view})")
    for k, p in paths.items():
        print(f"  {k}: {p}")
    level = SEVERITY[a.fail_on]
    return 1 if any(SEVERITY[f.severity] <= level for f in audit.findings) else 0


def cmd_gen(a) -> int:
    src = load_single_source(a.spec, a.item)
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    item_path = out / f"{src.item}.sv"
    item_path.write_text(emit_item_class(src.cset, a.cls or src.item))
    print(f"  uvm item: {item_path}")
    if a.map:
        mapping = load_mapping(a.map)
        em = emit_assumes(src.cset, mapping, src.protocols, directive=a.directive)
        sva_path = out / f"{src.item}_env_{a.directive}s.sv"
        sva_path.write_text(em.text)
        print(f"  sva {a.directive}s: {sva_path}")
        for w in em.warnings:
            print(f"  warning: {w}")
        for s in em.skipped:
            print(f"  skipped: {s}")
    return 0


def main(argv=None) -> int:
    p = argparse.ArgumentParser(prog="uvm_formal_sync", description="Single-source constraint/assumption compiler and drift checker")
    sub = p.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("check", help="audit UVM constraints against SVA assumes (and optionally a .fbr spec)")
    c.add_argument("--uvm", help="SystemVerilog file containing the uvm_sequence_item")
    c.add_argument("--class", dest="cls", help="sequence item class name")
    c.add_argument("--sva", nargs="+", required=True, help="SVA files with assume properties")
    c.add_argument("--map", required=True, help="bus view mapping YAML")
    c.add_argument("--spec", help="single-source .fbr rule file")
    c.add_argument("--item", help="item name inside the .fbr file")
    c.add_argument("--out", default="build/sync", help="report directory")
    c.add_argument("--fail-on", choices=list(SEVERITY), default="error")
    c.set_defaults(fn=cmd_check)
    g = sub.add_parser("gen", help="compile a .fbr spec into a UVM item and SVA assumes")
    g.add_argument("--spec", required=True)
    g.add_argument("--item")
    g.add_argument("--class", dest="cls")
    g.add_argument("--map")
    g.add_argument("--directive", choices=["assume", "assert"], default="assume")
    g.add_argument("--out", default="build/gen")
    g.set_defaults(fn=cmd_gen)
    a = p.parse_args(argv)
    if a.cmd == "check" and not (a.uvm or a.spec):
        p.error("check needs --uvm and/or --spec")
    return a.fn(a)


if __name__ == "__main__":
    sys.exit(main())
