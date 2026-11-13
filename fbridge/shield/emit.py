from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from .codegen_c import CSource, generate_c
from .codegen_sv import SvSource, generate_sv
from .compile import CompiledShield


@dataclass
class ShieldArtifacts:
    out_dir: Path
    c: CSource
    sv: SvSource
    paths: dict[str, Path]


def report(comp: CompiledShield) -> dict:
    spec = comp.spec
    classes = []
    for i, c in enumerate(comp.classes, 1):
        states = [s for s, k in enumerate(comp.class_of_state or []) if k == i]
        classes.append({
            "id": i,
            "legal_actions": c.action_count,
            "states": [spec.unpack(s, "state") for s in states[:32]],
            "num_states": len(states) if comp.class_of_state is not None else None,
            "narrow_masks": {k: f"0x{v:X}" for k, v in c.masks.items()},
            "intervals": {k: [[f"0x{a:X}", f"0x{b:X}"] for a, b in v] for k, v in c.intervals.items()},
            "approximate": c.approx,
        })
    return {
        "shield": spec.name,
        "mode": comp.mode,
        "stats": comp.stats,
        "reach": {"converged": comp.reach_converged, "iterations": comp.reach_iterations, "states": comp.reachable_states},
        "state_layout": [{"name": f.name, "lsb": f.lsb, "width": f.width, "enum": dict(f.enum)} for f in spec.state],
        "action_layout": [{"name": f.name, "lsb": f.lsb, "width": f.width, "enum": dict(f.enum),
                           "mutable": fi.mutable} for f, fi in zip(spec.action, comp.fields)],
        "rules": comp.rule_names,
        "invariants": [{"label": i.label, "format": i.facts.fmt, "source": i.facts.source} for i in spec.invariants],
        "classes": classes,
        "warnings": comp.warnings,
    }


def write_artifacts(comp: CompiledShield, out_dir: str | Path, prefix: str | None = None, aliases: bool = True) -> ShieldArtifacts:
    out = Path(out_dir)
    out.mkdir(parents=True, exist_ok=True)
    c = generate_c(comp, prefix, aliases=aliases)
    sv = generate_sv(comp, prefix)
    paths = {
        "c": out / c.source_name,
        "h": out / c.header_name,
        "sv_pkg": out / sv.package_name,
        "sv_item": out / sv.mixin_name,
        "report": out / "shield_report.json",
    }
    paths["c"].write_text(c.source)
    paths["h"].write_text(c.header)
    paths["sv_pkg"].write_text(sv.package)
    paths["sv_item"].write_text(sv.mixin)
    paths["report"].write_text(json.dumps(report(comp), indent=2))
    return ShieldArtifacts(out, c, sv, paths)
