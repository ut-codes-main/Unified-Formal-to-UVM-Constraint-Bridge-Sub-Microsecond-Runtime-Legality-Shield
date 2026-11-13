from __future__ import annotations

import argparse
import glob
import sys
from pathlib import Path

from ..backends.sva_emit import spec_to_sv
from ..frontends.sva_assume import parse_sva
from ..frontends.uvm_constraints import load_uvm_item
from .emit_seq import SeqOptions, emit_sequence, lift_report
from .lift import lift
from .monitor import load_monitor
from .vcd import load_waveform


def _pairs(items: list[str] | None) -> dict[str, str]:
    out = {}
    for it in items or []:
        k, v = it.split("=", 1)
        out[k.strip()] = v.strip()
    return out


def _files(patterns: list[str]) -> list[Path]:
    out = []
    for p in patterns:
        out += [Path(h) for h in (glob.glob(p) or [p])]
    return sorted(set(out))


def property_from_file(path: str, label: str, defines: list[str]) -> str:
    text = "".join(f"`define {d}\n" for d in defines) + Path(path).read_text()
    for unit in parse_sva(text=text, kinds=("assert", "assume", "cover")):
        if label in unit.specs:
            return spec_to_sv(unit.specs[label], clock=unit.clock)
    raise SystemExit(f"cex_lifter: property '{label}' not found in {path}")


def main(argv=None) -> int:
    p = argparse.ArgumentParser(prog="cex_lifter", description="Lift a formal counterexample waveform into a UVM sequence")
    p.add_argument("--vcd", required=True, help="VCD (or FST with fst2vcd on PATH) witness trace")
    p.add_argument("--monitor", required=True, help="bus monitor YAML or built-in profile name (axi4_lite, axi4)")
    p.add_argument("--prefix", help="override the monitor signal prefix")
    p.add_argument("--rtl", nargs="+", required=True, help="RTL sources used for dynamic slicing")
    p.add_argument("--top", required=True, help="top module (VCD scope)")
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument("--property", help="failing SVA property text")
    g.add_argument("--assert-label", help="label of the failing assertion in --assert-file")
    p.add_argument("--assert-file", help="file containing the labelled assertion")
    p.add_argument("--define", action="append", default=[], help="macro defined while reading --assert-file")
    p.add_argument("--uvm", help="UVM sequence item source (enables legality checking and enum mapping)")
    p.add_argument("--class", dest="cls", help="sequence item class name")
    p.add_argument("--map", nargs="*", help="monitor value to enum member, e.g. WRITE=AXIL_WRITE")
    p.add_argument("--field-map", nargs="*", help="monitor field to item field, e.g. data=wdata")
    p.add_argument("--keep-timing", action="store_true", help="keep transactions that only influence handshake timing")
    p.add_argument("--name", default="cex")
    p.add_argument("--cycle-time", default="10ns")
    p.add_argument("--out", default="build/cex")
    a = p.parse_args(argv)

    prop = a.property
    if prop is None:
        if not a.assert_file:
            p.error("--assert-label requires --assert-file")
        prop = property_from_file(a.assert_file, a.assert_label, a.define)
    mon = load_monitor(a.monitor, a.prefix)
    item = load_uvm_item(a.uvm, a.cls) if a.uvm else None
    wf = load_waveform(a.vcd)
    res = lift(wf, mon, _files(a.rtl), a.top, prop, item.cset if item else None, _pairs(a.map), a.keep_timing)
    opts = SeqOptions(a.name, item.name if item else (a.cls or "uvm_sequence_item"), a.cycle_time, _pairs(a.field_map),
                      _pairs(a.map), Path(a.vcd).name)
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    seq_path = out / f"{a.name}_seq.sv"
    seq_path.write_text(emit_sequence(res, opts, item.cset.schema if item else None))
    (out / f"{a.name}_lift.json").write_text(lift_report(res, opts))
    kept = res.kept()
    print(f"cex_lifter: property fails at cycle {res.fail_cycle}; {len(kept)}/{len(res.transactions)} transactions required")
    for t in kept:
        pinned = [f for f, fl in t.fields.items() if fl.mask > 0]
        print(f"  #{t.txn.index} {t.txn.kind} @ {t.txn.issue_cycle}: pinned {', '.join(pinned) or '-'}")
    for w in res.warnings:
        print(f"  warning: {w}")
    print(f"  sequence: {seq_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
