from __future__ import annotations

import json
from pathlib import Path

from ..ir.ast import ConstraintSet, Rule, schema_to_json, to_json
from ..ir.printer import to_sv
from ..mapping import Mapping
from .checker import Audit

KIND_TEXT = {
    "SIM_ALLOWS_FORMAL_FORBIDS": "Simulation can drive stimulus that formal assumed impossible",
    "FORMAL_ALLOWS_SIM_FORBIDS": "Formal explores stimulus simulation never generates",
    "SVA_EXTRA_ASSUME": "Formal assumption is stricter than the spec (proofs may be vacuous)",
    "SVA_MISSING_SPEC_RULE": "Spec rule is missing from the formal environment (spurious CEX risk)",
    "UVM_MISSING_SPEC_RULE": "UVM permits stimulus the spec forbids (illegal stimulus)",
    "UVM_EXTRA_CONSTRAINT": "UVM is stricter than the spec (coverage loss)",
    "UVM_CONFLICT": "UVM constraints are unsatisfiable",
    "SPEC_CONFLICT": "Spec rules are unsatisfiable",
    "FORMAL_VACUOUS": "Formal environment admits no transaction",
    "REDUNDANT_CONSTRAINT": "Redundant constraint",
    "DEAD_SOFT": "Soft constraint can never hold",
}


def rule_json(r: Rule, source: str) -> dict:
    d = {
        "id": f"{source}:{r.name}",
        "name": r.name,
        "source": source,
        "kind": r.kind,
        "soft": r.soft,
        "sv": to_sv(r.body()),
        "expr": to_json(r.body()),
        "origin": {"file": r.origin.file, "line": r.origin.line, "text": r.origin.text},
    }
    if r.disable is not None:
        d["disable"] = to_sv(r.disable)
    return d


def unified_ast(uvm: ConstraintSet | None, sva: ConstraintSet, mapping: Mapping, spec: ConstraintSet | None, audit: Audit) -> dict:
    out = {"format": "fbridge.unified_ast/1"}
    if spec is not None:
        out["spec"] = {"item": spec.name, "schema": schema_to_json(spec.schema), "rules": [rule_json(r, "spec") for r in spec.rules]}
    if uvm is not None:
        out["uvm"] = {"item": uvm.name, "schema": schema_to_json(uvm.schema), "rules": [rule_json(r, "uvm") for r in uvm.rules]}
    out["sva"] = {"unit": sva.name, "schema": schema_to_json(sva.schema), "rules": [rule_json(r, "sva") for r in sva.rules]}
    out["mapping"] = {
        "item": mapping.item,
        "clock": mapping.clock,
        "disable": mapping.disable_text,
        "views": [{"name": v.name, "when": v.when_text, "sample": v.sample_text,
                   "fields": {f: to_sv(e) for f, e in v.fields.items()}} for v in mapping.views],
    }
    out["projections"] = [{"assume": a.name, "kind": a.kind, "per_view": a.classes, "projected": a.projected} for a in audit.assumes]
    return out


def _md_escape(s: str) -> str:
    return s.replace("|", "\\|")


def markdown(audit: Audit, title: str = "Constraint / Assumption Equivalence Audit") -> str:
    d = audit.to_dict()
    c = d["counts"]
    lines = [f"# {title}", "", f"**Verdict:** `{d['verdict']}`  ", f"errors: {c['error']}, warnings: {c['warning']}, info: {c['info']}", ""]
    lines += ["## Views", "", "| view | when | sample | item sat | formal sat | equivalent |", "|---|---|---|---|---|---|"]
    for v in d["views"]:
        eq = "-" if v["equivalent"] is None else ("yes" if v["equivalent"] else "no")
        lines.append(f"| {v['name']} | `{_md_escape(v['when'])}` | `{_md_escape(v['sample'])}` | {v['item_satisfiable']} | {v['formal_satisfiable']} | {eq} |")
    lines.append("")
    order = {"error": 0, "warning": 1, "info": 2}
    findings = sorted(d["findings"], key=lambda f: (order[f["severity"]], f["pair"], f["kind"], f["subject"]))
    lines += ["## Findings", ""]
    if not findings:
        lines += ["No drift detected.", ""]
    for i, f in enumerate(findings, 1):
        lines.append(f"### {i}. [{f['severity'].upper()}] {f['kind']} - `{f['subject']}`")
        lines.append("")
        lines.append(f"*{KIND_TEXT.get(f['kind'], f['kind'])}* ({f['pair']}{', view ' + f['view'] if f['view'] else ''})")
        lines.append("")
        lines.append(f["message"])
        if f["origin"] and f["origin"]["file"]:
            lines += ["", f"Source: `{f['origin']['file']}:{f['origin']['line']}`"]
            if f["origin"]["text"]:
                lines += ["", "```systemverilog", f["origin"]["text"], "```"]
        if f["witness"]:
            w = ", ".join(f"{k}={v}" for k, v in f["witness"].items())
            lines += ["", f"Witness: `{w}`"]
        if f["related"]:
            lines += ["", f"Jointly with: {', '.join(f['related'])}"]
        if f["suggestion"]:
            lines += ["", "Suggested alignment:", "", "```systemverilog", f["suggestion"], "```"]
        lines.append("")
    lines += ["## Assumption classification", "", "| assume | kind | per view | projected |", "|---|---|---|---|"]
    for a in d["assumes"]:
        pv = ", ".join(f"{k}:{v}" for k, v in a["classes"].items())
        pj = "; ".join(f"{k}: `{_md_escape(v)}`" for k, v in a["projected"].items())
        lines.append(f"| {a['name']} | {a['kind']} | {pv} | {pj} |")
    if d["warnings"]:
        lines += ["", "## Warnings", ""] + [f"- {w}" for w in d["warnings"]]
    return "\n".join(lines) + "\n"


def write_reports(out_dir: str | Path, audit: Audit, unified: dict) -> dict[str, Path]:
    out = Path(out_dir)
    out.mkdir(parents=True, exist_ok=True)
    paths = {"json": out / "audit.json", "md": out / "audit.md", "ast": out / "unified_ast.json"}
    paths["json"].write_text(json.dumps(audit.to_dict(), indent=2))
    paths["md"].write_text(markdown(audit))
    paths["ast"].write_text(json.dumps(unified, indent=2))
    return paths
