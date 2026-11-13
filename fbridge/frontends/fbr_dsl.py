from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path

from ..ir.ast import Const, ConstraintSet, Field, Origin, Rule, Schema, conj
from ..ir.evaluate import evaluate
from .svparse import FbrConst, FbrItem, FbrProtocol, FbrRule, PropertySpec, lower_spec, parse_fbr


@dataclass
class Protocol:
    name: str
    spec: PropertySpec
    rule: Rule


@dataclass
class SingleSource:
    item: str
    cset: ConstraintSet
    protocols: list[Protocol] = field(default_factory=list)
    consts: dict[str, int] = field(default_factory=dict)


def load_fbr(path: str | Path | None = None, text: str | None = None) -> list[SingleSource]:
    src = str(path or "<text>")
    if text is None:
        text = Path(path).read_text()
    consts: dict[str, int] = {}
    decls = parse_fbr(text, consts)
    out: list[SingleSource] = []
    cur: SingleSource | None = None
    lines = text.splitlines()
    for d in decls:
        if isinstance(d, FbrConst):
            s = Schema()
            for k, v in consts.items():
                s.consts[k] = Const(v, 32, True)
            consts[d.name] = evaluate(d.expr, s, {})
        elif isinstance(d, FbrItem):
            schema = Schema()
            for k, v in consts.items():
                schema.consts[k] = Const(v, 32, True)
            for f in d.fields:
                members = []
                if f.enum:
                    nxt = 0
                    for name, ve in f.enum:
                        if ve is not None:
                            nxt = evaluate(ve, schema, {})
                        members.append((name, nxt))
                        nxt += 1
                schema.add(Field(f.name, f.width, f.signed, f.kind, tuple(members)))
            cur = SingleSource(d.name, ConstraintSet(d.name, schema, source=src), consts=dict(consts))
            out.append(cur)
        elif isinstance(d, FbrRule):
            if cur is None:
                raise ValueError(f"{src}:{d.line}: rule '{d.name}' declared before any item")
            for k, v in consts.items():
                cur.cset.schema.consts.setdefault(k, Const(v, 32, True))
            body = conj(d.exprs)
            text_line = lines[d.line - 1].strip() if 0 < d.line <= len(lines) else ""
            cur.cset.rules.append(Rule(d.name, body, "rule", d.soft, Origin(src, d.line, text_line), guard=d.guard))
        elif isinstance(d, FbrProtocol):
            if cur is None:
                raise ValueError(f"{src}:{d.line}: protocol '{d.name}' declared before any item")
            expr, disable = lower_spec(d.spec)
            text_line = lines[d.line - 1].strip() if 0 < d.line <= len(lines) else ""
            cur.protocols.append(Protocol(d.name, d.spec, Rule(d.name, expr, "protocol", False, Origin(src, d.line, text_line), disable=disable)))
    return out


def load_single_source(path: str | Path, item: str | None = None) -> SingleSource:
    srcs = load_fbr(path)
    for s in srcs:
        if item is None or s.item == item:
            return s
    raise ValueError(f"item '{item}' not found in {path}")
