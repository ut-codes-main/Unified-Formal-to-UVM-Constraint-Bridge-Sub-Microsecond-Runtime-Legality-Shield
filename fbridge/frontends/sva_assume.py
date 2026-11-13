from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path

from pyslang import syntax as S

from ..ir.ast import Const, ConstraintSet, Expr, Field, Origin, Rule, Schema
from .slang_util import (
    add_enum_consts, collect_enums, collect_params, kind, line_of, load_tree, text_of, tok, type_info, walk,
)
from .svparse import ParseError, PropertyLoweringError, PropertySpec, lower_spec, parse_expr, parse_property

DIRECTIVES = {"AssumePropertyStatement": "assume", "AssertPropertyStatement": "assert", "CoverPropertyStatement": "cover"}


@dataclass
class SvaUnit:
    name: str
    cset: ConstraintSet
    specs: dict[str, PropertySpec] = field(default_factory=dict)
    clock: str | None = None
    warnings: list[str] = field(default_factory=list)


def _declare(schema: Schema, decl_type, declarators, consts, enums, warn, tree, src):
    info = type_info(decl_type, consts, enums) if decl_type is not None else (1, False, [])
    for d in declarators:
        if not isinstance(d, S.SyntaxNode) or kind(d) != "Declarator":
            continue
        name = tok(d.name)
        if info is None or len(list(d.dimensions)):
            warn.append(f"{src}:{line_of(tree, d)}: signal '{name}' has unsupported type; ignored")
            continue
        w, signed, members = info
        schema.add(Field(name, w, signed, "signal", tuple(members)))


def parse_sva(path: str | Path | None = None, text: str | None = None, kinds=("assume",),
              consts: dict[str, int] | None = None, schema: Schema | None = None) -> list[SvaUnit]:
    tree = load_tree(path, text)
    src = str(path or "<text>")
    consts = dict(consts or {})
    collect_params(tree.root, consts)
    enums = collect_enums(tree.root, consts)
    units = []
    for unit in walk(tree.root):
        if kind(unit) not in ("ModuleDeclaration", "InterfaceDeclaration", "CheckerDeclaration", "ProgramDeclaration"):
            continue
        name = tok(unit.header.name) if hasattr(unit, "header") else tok(unit.name)
        sch = Schema() if schema is None else schema.merged(Schema())
        add_enum_consts(sch, enums)
        for k, v in consts.items():
            sch.consts.setdefault(k, Const(v, 32, True))
        su = SvaUnit(name, ConstraintSet(name, sch, source=src))
        default_disable: Expr | None = None
        named_props: dict[str, PropertySpec] = {}
        ports = getattr(unit.header, "ports", None) if hasattr(unit, "header") else None
        last_ty = None
        if ports is not None and kind(ports) == "AnsiPortList":
            for p in ports.ports:
                if not isinstance(p, S.SyntaxNode) or kind(p) != "ImplicitAnsiPort":
                    continue
                ty = getattr(p.header, "dataType", None)
                explicit = getattr(p.header, "direction", None) is not None and tok(p.header.direction)
                if not explicit and ty is not None and kind(ty) == "ImplicitType" and not len(list(ty.dimensions)) and last_ty is not None:
                    ty = last_ty
                last_ty = ty
                _declare(sch, ty, [p.declarator], consts, enums, su.warnings, tree, src)
        for n in walk(unit):
            k = kind(n)
            if k == "PortDeclaration":
                ty = getattr(n.header, "dataType", None)
                _declare(sch, ty, n.declarators, consts, enums, su.warnings, tree, src)
            elif k == "DataDeclaration":
                _declare(sch, n.type, n.declarators, consts, enums, su.warnings, tree, src)
            elif k == "NetDeclaration":
                _declare(sch, n.type, n.declarators, consts, enums, su.warnings, tree, src)
            elif k == "DefaultDisableDeclaration":
                default_disable = parse_expr(text_of(n.expr), consts)
            elif k == "ClockingDeclaration" and su.clock is None:
                ev = [x for x in walk(n) if kind(x) == "SignalEventExpression"]
                if ev:
                    su.clock = text_of(ev[0].expr)
            elif k == "PropertyDeclaration":
                try:
                    named_props[tok(n.name)] = parse_property(text_of(n.propertySpec), consts)
                except ParseError as ex:
                    su.warnings.append(f"{src}:{line_of(tree, n)}: property {n.name}: {ex}")
        for n in walk(unit):
            directive = DIRECTIVES.get(kind(n))
            if directive is None or directive not in kinds:
                continue
            line = line_of(tree, n)
            label = tok(n.label.name) if n.label is not None else f"{directive}_L{line}"
            ptext = text_of(n.propertySpec)
            try:
                if ptext in named_props:
                    spec = named_props[ptext]
                else:
                    spec = parse_property(ptext, consts)
                expr, disable = lower_spec(spec)
            except (ParseError, PropertyLoweringError) as ex:
                su.warnings.append(f"{src}:{line}: {label}: {ex}")
                continue
            if disable is None:
                disable = default_disable
            if spec.clock is not None and su.clock is None:
                su.clock = text_of_expr(spec.clock)
            su.specs[label] = spec
            su.cset.rules.append(Rule(label, expr, directive, False, Origin(src, line, text_of(n)), disable=disable))
        units.append(su)
    return units


def text_of_expr(e: Expr) -> str:
    from ..ir.printer import to_sv
    return to_sv(e)


def load_sva(paths, kinds=("assume",), schema: Schema | None = None, consts: dict[str, int] | None = None) -> SvaUnit:
    if isinstance(paths, (str, Path)):
        paths = [paths]
    merged: SvaUnit | None = None
    for p in paths:
        for u in parse_sva(p, kinds=kinds, schema=schema, consts=consts):
            if merged is None:
                merged = u
                continue
            merged.cset.schema = merged.cset.schema.merged(u.cset.schema)
            merged.cset.rules += u.cset.rules
            merged.specs.update(u.specs)
            merged.warnings += u.warnings
            merged.clock = merged.clock or u.clock
    if merged is None:
        raise ValueError(f"no module/interface/checker found in {paths}")
    return merged
