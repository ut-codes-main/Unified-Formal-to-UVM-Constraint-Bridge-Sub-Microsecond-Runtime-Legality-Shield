from __future__ import annotations

from pathlib import Path
from typing import Iterator

from pyslang import syntax as S

from ..ir.ast import Const, Schema
from ..ir.evaluate import evaluate
from .svparse import parse_expr

INT_TYPES = {
    "IntType": (32, True), "IntegerType": (32, True), "ShortIntType": (16, True), "LongIntType": (64, True),
    "ByteType": (8, True), "BitType": (1, False), "LogicType": (1, False), "RegType": (1, False),
    "ImplicitType": (1, False), "TimeType": (64, False),
}


def load_tree(path: str | Path | None = None, text: str | None = None) -> S.SyntaxTree:
    if text is None:
        text = Path(path).read_text()
    return S.SyntaxTree.fromText(text, str(path or "<text>"))


BENIGN_DIAGS = ("CouldNotOpenIncludeFile", "UnknownDirective", "UnknownSystemName")


def syntax_errors(text: str, name: str = "<generated>") -> list[str]:
    tree = S.SyntaxTree.fromText(text, name)
    out = []
    for d in tree.diagnostics:
        code = str(d.code)
        if any(b in code for b in BENIGN_DIAGS):
            continue
        out.append(f"{code} at line {tree.sourceManager.getLineNumber(d.location)}")
    return out


def line_of(tree: S.SyntaxTree, node) -> int:
    return tree.sourceManager.getLineNumber(node.sourceRange.start)


def text_of(node) -> str:
    return str(node).strip()


def tok(t) -> str:
    if t is None:
        return ""
    v = getattr(t, "valueText", None)
    return (v if v is not None else str(t)).strip()


def walk(node) -> Iterator:
    yield node
    for c in node:
        if isinstance(c, S.SyntaxNode):
            yield from walk(c)


def kind(node) -> str:
    return node.kind.name


def const_int(text: str, consts: dict[str, int]) -> int:
    e = parse_expr(text, consts)
    s = Schema()
    for k, v in consts.items():
        s.consts[k] = Const(v, 32, True)
    return evaluate(e, s, {})


def dims_width(dims, consts: dict[str, int]) -> int | None:
    width = 1
    for d in dims:
        spec = d.specifier
        if spec is None or kind(spec) != "RangeDimensionSpecifier":
            return None
        sel = spec.selector
        if kind(sel) != "SimpleRangeSelect":
            return None
        hi = const_int(text_of(sel.left), consts)
        lo = const_int(text_of(sel.right), consts)
        width *= abs(hi - lo) + 1
    return width


def type_info(ty, consts: dict[str, int], enums: dict[str, tuple[int, list[tuple[str, int]]]]) -> tuple[int, bool, list[tuple[str, int]]] | None:
    k = kind(ty)
    if k == "NamedType":
        name = text_of(ty.name).split("::")[-1]
        if name in enums:
            w, members = enums[name]
            return w, False, members
        return None
    if k == "EnumType":
        return enum_info(ty, consts)
    if k not in INT_TYPES:
        return None
    base_w, signed = INT_TYPES[k]
    sign_tok = getattr(ty, "signing", None)
    if sign_tok is not None and tok(sign_tok):
        signed = tok(sign_tok) == "signed"
    dims = list(getattr(ty, "dimensions", []) or [])
    if dims:
        w = dims_width(dims, consts)
        if w is None:
            return None
        return w * (base_w if base_w > 1 else 1), signed, []
    return base_w, signed, []


def enum_info(ty, consts) -> tuple[int, bool, list[tuple[str, int]]]:
    width = 32
    if ty.baseType is not None:
        bi = type_info(ty.baseType, consts, {})
        if bi is not None:
            width = bi[0]
    members = []
    nxt = 0
    for d in ty.members:
        if not isinstance(d, S.SyntaxNode) or kind(d) != "Declarator":
            continue
        name = tok(d.name)
        if d.initializer is not None:
            nxt = const_int(text_of(d.initializer.expr), consts)
        members.append((name, nxt))
        nxt += 1
    return width, False, members


def collect_params(root, consts: dict[str, int]) -> None:
    for n in walk(root):
        if kind(n) == "ParameterDeclaration":
            for d in n.declarators:
                if not isinstance(d, S.SyntaxNode) or kind(d) != "Declarator" or d.initializer is None:
                    continue
                try:
                    consts[tok(d.name)] = const_int(text_of(d.initializer.expr), consts)
                except Exception:
                    pass


def collect_enums(root, consts: dict[str, int]) -> dict[str, tuple[int, list[tuple[str, int]]]]:
    enums = {}
    for n in walk(root):
        if kind(n) == "TypedefDeclaration" and kind(n.type) == "EnumType":
            w, _, members = enum_info(n.type, consts)
            enums[tok(n.name)] = (w, members)
            for name, v in members:
                consts.setdefault(name, v)
    return enums


def add_enum_consts(schema: Schema, enums) -> None:
    for w, members in enums.values():
        for name, v in members:
            schema.consts.setdefault(name, Const(v, w, False))
