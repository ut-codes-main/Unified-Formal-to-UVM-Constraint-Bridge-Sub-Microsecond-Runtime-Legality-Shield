from __future__ import annotations

import hashlib
import json
import re
from dataclasses import asdict, dataclass, field
from pathlib import Path, PurePosixPath

from .cones import Design
from .diff import Hunk, overlaps

SBY_UNREACHED = re.compile(r"[Uu]nreached cover statement at (\S+?):(\d+)(?:\.\d+)?")
SBY_ENGINE = re.compile(r"\]\s+(engine_\d+): (\S+(?: \S+)?)$")


@dataclass
class Certificate:
    id: str
    bin: str
    module: str
    label: str
    signals: list[str]
    status: str = "unreachable"
    engine: str = ""
    source: dict = field(default_factory=dict)
    coverage: dict = field(default_factory=dict)
    directive_text: str = ""
    cone: list[str] = field(default_factory=list)
    fingerprint: str = ""
    drivers: list[dict] = field(default_factory=list)
    files: dict[str, str] = field(default_factory=dict)
    proven_at: str = ""

    @staticmethod
    def from_dict(d: dict) -> "Certificate":
        return Certificate(**{k: v for k, v in d.items() if k in Certificate.__dataclass_fields__})


def _same_file(a: str, b: str) -> bool:
    pa, pb = PurePosixPath(a.replace("\\", "/")), PurePosixPath(b.replace("\\", "/"))
    return pa == pb or pa.name == pb.name and (str(pa).endswith(str(pb)) or str(pb).endswith(str(pa)))


def import_sby(log_text: str, design: Design, engine: str | None = None) -> list[Certificate]:
    engines = {}
    for line in log_text.splitlines():
        m = SBY_ENGINE.search(line)
        if m and not m.group(2).startswith(("starting", "finished", "##")):
            engines[m.group(1)] = m.group(2)
    seen, out = set(), []
    for line in log_text.splitlines():
        m = SBY_UNREACHED.search(line)
        if not m:
            continue
        f, ln = m.group(1), int(m.group(2))
        if (f, ln) in seen:
            continue
        seen.add((f, ln))
        hits = [d for d in design.directives if d.kind == "cover" and d.line == ln and _same_file(d.file, f)]
        if not hits:
            raise ValueError(f"no cover directive found at {f}:{ln}")
        d = hits[0]
        eng = engine or ", ".join(sorted(set(engines.values()))) or "unknown"
        out.append(Certificate(f"{d.module}.{d.label}", f"{d.module}.{d.label}", d.module, d.label, list(d.signals),
                               engine=eng, source={"file": d.file, "line": d.line}, directive_text=d.text))
    return out


def _directive_for(cert: Certificate, design: Design):
    for d in design.directives:
        if d.module == cert.module and d.label == cert.label:
            return d
    return None


def seal(cert: Certificate, design: Design, proven_at: str = "") -> Certificate:
    d = _directive_for(cert, design)
    if d is not None:
        cert.signals = list(d.signals)
        cert.directive_text = d.text
        cert.source = {"file": d.file, "line": d.line}
    cone = design.cone(cert.signals)
    drivers = design.cone_drivers(cone)
    cert.cone = sorted(cone)
    cert.fingerprint = _fingerprint(design, cone, cert.directive_text)
    cert.drivers = [{"file": x.file, "start": x.start, "end": x.end, "targets": list(x.targets)} for x in drivers if x.start]
    files = {x.file for x in drivers if x.start} | ({d.file} if d else set())
    cert.files = {f: design.files.get(f, "") for f in sorted(files)}
    cert.proven_at = proven_at or cert.proven_at
    return cert


def _fingerprint(design: Design, cone: set[str], directive_text: str) -> str:
    return hashlib.sha256((design.fingerprint(cone) + "|" + directive_text).encode()).hexdigest()


@dataclass
class Verdict:
    certificate: str
    bin: str
    valid: bool
    reason: str
    touched_signals: list[str] = field(default_factory=list)
    hunks: list[dict] = field(default_factory=list)
    cone_size: int = 0


def touched_signals(hunks: list[Hunk], design: Design, old_drivers: list[dict] | None = None) -> tuple[set[str], list[Hunk]]:
    sigs, used = set(), []
    for h in hunks:
        hit = False
        for drv in design.all_drivers():
            if drv.start and _same_file(drv.file, h.file) and overlaps((drv.start, drv.end), h.new_range()):
                sigs |= set(drv.targets)
                hit = True
        for name, (f, s, e, _) in design.decls.items():
            if _same_file(f, h.file) and overlaps((s, e), h.new_range()):
                sigs.add(name)
                hit = True
        for drv in old_drivers or ():
            if _same_file(drv["file"], h.file) and overlaps((drv["start"], drv["end"]), h.old_range()):
                sigs |= set(drv["targets"])
                hit = True
        if hit:
            used.append(h)
    return sigs, used


def evaluate(certs: list[Certificate], design: Design, hunks: list[Hunk] | None = None) -> list[Verdict]:
    out = []
    for c in certs:
        d = _directive_for(c, design)
        if d is None:
            out.append(Verdict(c.id, c.bin, False, "cover directive removed or renamed"))
            continue
        cone = design.cone(d.signals)
        fp = _fingerprint(design, cone, d.text)
        if fp == c.fingerprint:
            out.append(Verdict(c.id, c.bin, True, "cone fingerprint unchanged", cone_size=len(cone)))
            continue
        old_cone = set(c.cone)
        sigs, used = touched_signals(hunks or [], design, c.drivers)
        touched = sorted((sigs & (cone | old_cone)))
        rel_hunks = [h.to_dict() for h in used if any(t in sigs for t in touched)] if touched else []
        if d.text != c.directive_text:
            reason = "cover property text changed"
        elif cone != old_cone:
            added = sorted(cone - old_cone)
            removed = sorted(old_cone - cone)
            reason = f"cone structure changed (+{len(added)} / -{len(removed)} signals)"
        else:
            reason = "logic inside the cone changed"
        out.append(Verdict(c.id, c.bin, False, reason, touched, rel_hunks, len(cone)))
    return out


def unreachable_bins(certs: list[Certificate], verdicts: list[Verdict], meta: dict | None = None) -> dict:
    by_id = {c.id: c for c in certs}
    valid = [v for v in verdicts if v.valid]
    bad = [v for v in verdicts if not v.valid]
    return {
        "format": "fbridge.unreachable_bins/1",
        "meta": meta or {},
        "summary": {"certificates": len(certs), "unreachable": len(valid), "invalidated": len(bad)},
        "unreachable_bins": [
            {"bin": v.bin, "certificate": v.certificate, "engine": by_id[v.certificate].engine,
             "proven_at": by_id[v.certificate].proven_at, "cone_size": v.cone_size,
             **({"coverage": by_id[v.certificate].coverage} if by_id[v.certificate].coverage else {})}
            for v in valid
        ],
        "invalidated": [
            {"bin": v.bin, "certificate": v.certificate, "reason": v.reason, "touched_signals": v.touched_signals, "hunks": v.hunks}
            for v in bad
        ],
        "mask": {v.bin: True for v in valid},
    }


def svh_include(result: dict, certs: list[Certificate]) -> str:
    by_id = {c.id: c for c in certs}
    bins = [b["bin"] for b in result["unreachable_bins"]]
    lines = [
        "`ifndef FB_UNREACHABLE_BINS_SVH",
        "`define FB_UNREACHABLE_BINS_SVH",
        "",
        f"`define FB_NUM_UNREACHABLE_BINS {len(bins)}",
        "`define FB_UNREACHABLE_BINS '{" + ", ".join(f'"{b}"' for b in bins) + "}" if bins else '`define FB_UNREACHABLE_BINS \'{""}',
    ]
    groups: dict[tuple[str, str], list[tuple[str, str]]] = {}
    for b in result["unreachable_bins"]:
        cov = by_id[b["certificate"]].coverage
        if cov.get("covergroup") and cov.get("coverpoint") and cov.get("values"):
            groups.setdefault((cov["covergroup"], cov["coverpoint"]), []).append((cov.get("bin_name") or by_id[b["certificate"]].label, cov["values"]))
    for (cg, cp), items in sorted(groups.items()):
        body = " ".join(f"ignore_bins {name}_unreach = {{{vals}}};" for name, vals in items)
        lines.append(f"`define FB_IGNORE_{cg.upper()}_{cp.upper()} {body}")
    lines += ["", "`endif", ""]
    return "\n".join(lines)


def save_index(path: str | Path, certs: list[Certificate], meta: dict) -> None:
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    Path(path).write_text(json.dumps({"format": "fbridge.unreach_index/1", "meta": meta, "certificates": [asdict(c) for c in certs]}, indent=2))


def load_certs(path: str | Path) -> tuple[list[Certificate], dict]:
    d = json.loads(Path(path).read_text())
    return [Certificate.from_dict(c) for c in d["certificates"]], d.get("meta", {})
