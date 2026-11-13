from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path

import yaml
import z3

from .ir.ast import TRUE, Const, Expr, Field, Schema, Var, free_vars
from .ir.smt import Encoder
from .frontends.svparse import parse_expr


@dataclass
class View:
    name: str
    sample: Expr
    fields: dict[str, Expr]
    when: Expr = TRUE
    when_text: str = ""
    sample_text: str = ""


@dataclass
class Mapping:
    item: str
    views: list[View]
    clock: str = "clk"
    disable: Expr | None = None
    disable_text: str = ""
    signals: dict[str, int] = field(default_factory=dict)
    module: str = ""

    def signal_schema(self, item_schema: Schema | None = None) -> Schema:
        s = Schema()
        for name, w in self.signals.items():
            s.add(Field(name, w, False, "signal"))
        for v in self.views:
            for n in free_vars(v.sample):
                if n not in s.fields:
                    s.add(Field(n, 1, False, "signal"))
            for f, e in v.fields.items():
                if isinstance(e, Var) and e.name not in s.fields:
                    w = item_schema.fields[f].width if item_schema is not None and f in item_schema.fields else 1
                    s.add(Field(e.name, w, False, "signal"))
        if self.disable is not None:
            for n in free_vars(self.disable):
                if n not in s.fields:
                    s.add(Field(n, 1, False, "signal"))
        if self.clock not in s.fields:
            s.add(Field(self.clock, 1, False, "signal"))
        return s


def load_mapping(path: str | Path) -> Mapping:
    d = yaml.safe_load(Path(path).read_text())
    views = []
    for v in d["views"]:
        when_text = str(v.get("when", "")).strip()
        views.append(View(
            v["name"],
            parse_expr(str(v["sample"])),
            {k: parse_expr(str(s)) for k, s in v["fields"].items()},
            parse_expr(when_text) if when_text else TRUE,
            when_text,
            str(v["sample"]),
        ))
    dis = str(d.get("disable", "")).strip()
    return Mapping(
        d["item"], views, d.get("clock", "clk"),
        parse_expr(dis) if dis else None, dis,
        {k: int(w) for k, w in (d.get("signals") or {}).items()},
        d.get("module", ""),
    )


def pinned_fields(view: View, item_schema: Schema) -> dict[str, Const]:
    enc = Encoder(item_schema)
    out = {}
    if view.when == TRUE:
        return out
    s = z3.Solver()
    s.add(enc.bool(view.when))
    if s.check() != z3.sat:
        return out
    m = s.model()
    for name in free_vars(view.when):
        if name not in item_schema.fields or name in view.fields:
            continue
        v = m.eval(enc.var(name), model_completion=True).as_long()
        s.push()
        s.add(enc.var(name) != v)
        if s.check() == z3.unsat:
            f = item_schema.fields[name]
            out[name] = Const(v, f.width, f.signed)
        s.pop()
    return out
