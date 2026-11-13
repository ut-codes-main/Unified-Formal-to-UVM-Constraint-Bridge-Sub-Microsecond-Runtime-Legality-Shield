from __future__ import annotations

import json
from dataclasses import dataclass

from ..ir.ast import Schema
from .lift import FieldLift, LiftResult, LiftedTxn, item_value


@dataclass
class SeqOptions:
    name: str = "cex_seq"
    item_class: str = "uvm_sequence_item"
    cycle_time: str = "10ns"
    field_map: dict[str, str] | None = None
    kind_map: dict[str, str] | None = None
    source: str = ""


def _contig(mask: int) -> tuple[int, int] | None:
    if mask == 0:
        return None
    lo = (mask & -mask).bit_length() - 1
    hi = mask.bit_length() - 1
    return (hi, lo) if mask == ((1 << (hi + 1)) - 1) ^ ((1 << lo) - 1) else None


def _lit(v: int, w: int) -> str:
    return f"{w}'h{v:X}" if v > 9 or w > 8 else f"{w}'d{v}"


def field_constraint(fl: FieldLift, name: str, schema: Schema | None, kind_map: dict[str, str]) -> str | None:
    if fl.mask == -1:
        f = schema.fields.get(fl.name) if schema else None
        if f is not None and f.enum:
            v = item_value(fl, schema, kind_map)
            member = next(n for n, x in f.enum if x == v)
            return f"{name} == {member}"
        return f"{name} == {kind_map.get(str(fl.value), fl.value)}"
    if fl.mask == 0 or not isinstance(fl.value, int):
        return None
    w = schema.fields[fl.name].width if schema and fl.name in schema.fields else fl.width
    full = (1 << w) - 1
    mask = fl.mask & full
    if mask == full:
        return f"{name} == {_lit(fl.value & full, w)}"
    c = _contig(mask)
    if c is not None:
        hi, lo = c
        sel = f"{name}[{hi}]" if hi == lo else f"{name}[{hi}:{lo}]"
        bw = hi - lo + 1
        return f"{sel} == {_lit((fl.value >> lo) & ((1 << bw) - 1), bw)}"
    return f"({name} & {_lit(mask, w)}) == {_lit(fl.value & mask, w)}"


def _describe(lt: LiftedTxn) -> str:
    parts = []
    for f, fl in lt.fields.items():
        if fl.mask == -1:
            continue
        v = fl.value if isinstance(fl.value, int) else 0
        if fl.mask:
            parts.append(f"{f}=0x{v:X}{'' if fl.mask == (1 << fl.width) - 1 else f' (bits 0x{fl.mask:X})'}")
    return ", ".join(parts) or "timing only"


def emit_sequence(res: LiftResult, opts: SeqOptions, schema: Schema | None = None) -> str:
    fmap = opts.field_map or {}
    kmap = opts.kind_map or {}
    cls = opts.name if opts.name.endswith("_seq") else f"{opts.name}_seq"
    kept = res.kept()
    dropped = [t for t in res.transactions if not t.essential]
    L = [
        f"// Lifted from formal counterexample {opts.source}".rstrip(),
        f"// Property: {res.property_text}",
        f"// Fails at cycle {res.fail_cycle} (observed by cycle {res.fail_end}); {len(kept)} of {len(res.transactions)} bus transactions are required.",
    ]
    for t in dropped:
        L.append(f"// dropped #{t.txn.index} {t.txn.kind} @ cycle {t.txn.issue_cycle}: no influence on the failing property")
    for w in res.warnings:
        L.append(f"// WARNING: {w}")
    L += [
        f"class {cls} extends uvm_sequence #({opts.item_class});",
        f"  `uvm_object_utils({cls})",
        "",
        f"  realtime cycle_time = {opts.cycle_time};",
        f"  int unsigned lifted_items = {len(kept)};",
        "",
        f'  function new(string name = "{cls}");',
        "    super.new(name);",
        "  endfunction",
        "",
        "  virtual task idle_cycles(int unsigned n);",
        "    if (n != 0) #(n * cycle_time);",
        "  endtask",
        "",
        "  virtual task body();",
        f"    {opts.item_class} req;",
    ]
    for k, lt in enumerate(kept):
        tx = lt.txn
        L.append("")
        L.append(f"    // [{k}] {tx.kind} issued @ cycle {tx.issue_cycle}, accepted @ {tx.accept_cycle}: {_describe(lt)}")
        if lt.idle_before:
            L.append(f"    idle_cycles({lt.idle_before});")
        L.append(f'    req = {opts.item_class}::type_id::create("cex_item_{k}");')
        L.append("    start_item(req);")
        for c in lt.disabled_constraints:
            L.append(f"    req.{c}.constraint_mode(0);")
        cons = []
        for f, fl in lt.fields.items():
            if schema is not None and fl.name not in schema.fields:
                continue
            c = field_constraint(fl, fmap.get(f, f), schema, kmap)
            if c:
                cons.append(c)
        body = "; ".join(cons)
        L.append(f"    if (!req.randomize() with {{ {body}; }})" if cons else "    if (!req.randomize())")
        L.append(f'      `uvm_fatal("CEX_LIFT", "lifted item {k} is infeasible under the current item constraints")')
        L.append("    finish_item(req);")
        if tx.observed:
            obs = ", ".join(f"{f}=0x{v:X}" for f, v in tx.observed.items())
            L.append(f"    // formal trace observed response: {obs}")
    L += ["  endtask", "endclass", ""]
    return "\n".join(L)


def lift_report(res: LiftResult, opts: SeqOptions) -> str:
    out = {
        "property": res.property_text,
        "fail_cycle": res.fail_cycle,
        "fail_end": res.fail_end,
        "trace_cycles": res.cycles,
        "warnings": res.warnings,
        "transactions": [
            {
                "index": t.txn.index, "kind": t.txn.kind, "issue_cycle": t.txn.issue_cycle, "accept_cycle": t.txn.accept_cycle,
                "required": t.essential, "timing_relevant": t.timing_relevant, "idle_before": t.idle_before, "legal": t.legal,
                "disabled_constraints": t.disabled_constraints, "observed": t.txn.observed,
                "fields": {f: {"value": fl.value if not isinstance(fl.value, int) else f"0x{fl.value:X}",
                               "pinned_mask": "const" if fl.mask == -1 else f"0x{fl.mask:X}"} for f, fl in t.fields.items()},
            }
            for t in res.transactions
        ],
        "relevant_inputs": {k: {str(t): f"0x{m:X}" for t, m in sorted(v.items())} for k, v in res.relevant_inputs.items()},
        "sequence": opts.name,
    }
    return json.dumps(out, indent=2)
