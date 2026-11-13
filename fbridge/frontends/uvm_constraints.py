from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path

from pyslang import syntax as S

from ..ir.ast import TRUE, Binary, ConstraintSet, Const, Expr, Field, Origin, Rule, Schema, Unary, conj
from .slang_util import (
    add_enum_consts, collect_enums, collect_params, kind, line_of, load_tree, text_of, tok, type_info, walk,
)
from .svparse import ParseError, parse_expr


@dataclass
class UvmItem:
    name: str
    base: str
    cset: ConstraintSet
    warnings: list[str] = field(default_factory=list)
    solve_before: list[tuple[str, str]] = field(default_factory=list)
    blocks: dict[str, list[str]] = field(default_factory=dict)


def _items(node) -> list:
    if node is None:
        return []
    k = kind(node)
    if k == "ConstraintBlock":
        return [i for i in node.items if isinstance(i, S.SyntaxNode)]
    return [node]


class _Ctx:
    def __init__(self, tree, path, consts, item: UvmItem):
        self.tree, self.path, self.consts, self.item = tree, path, consts, item

    def expr(self, node) -> Expr:
        return parse_expr(text_of(node), self.consts)

    def lower(self, node, guard: Expr) -> list[tuple[Expr, bool, object]]:
        k = kind(node)
        if k == "ExpressionConstraint":
            e = self.expr(node.expr)
            soft = tok(node.soft) == "soft"
            return [(_guarded(guard, e), soft, node)]
        if k == "ImplicationConstraint":
            g = conj([guard, self.expr(node.left)])
            out = []
            for c in _items(node.constraints):
                out += self.lower(c, g)
            return out
        if k == "ConditionalConstraint":
            c = self.expr(node.condition)
            out = []
            for it in _items(node.constraints):
                out += self.lower(it, conj([guard, c]))
            if node.elseClause is not None:
                for it in _items(node.elseClause.constraints):
                    out += self.lower(it, conj([guard, Unary("!", c)]))
            return out
        if k == "ConstraintBlock":
            out = []
            for it in _items(node):
                out += self.lower(it, guard)
            return out
        if k == "SolveBeforeConstraint":
            before = [text_of(x) for x in node.beforeExpr if isinstance(x, S.SyntaxNode)]
            after = [text_of(x) for x in node.afterExpr if isinstance(x, S.SyntaxNode)]
            self.item.solve_before += [(b, a) for b in before for a in after]
            return []
        if k == "UniquenessConstraint":
            names = [text_of(x) for x in walk(node.ranges) if kind(x) == "IdentifierName"]
            exprs = [parse_expr(n, self.consts) for n in names]
            pairs = [Binary("!=", exprs[i], exprs[j]) for i in range(len(exprs)) for j in range(i + 1, len(exprs))]
            return [(_guarded(guard, conj(pairs)), False, node)] if pairs else []
        self.item.warnings.append(f"{self.path}:{line_of(self.tree, node)}: unsupported constraint item '{k}' skipped")
        return []


def _guarded(guard: Expr, e: Expr) -> Expr:
    return e if guard == TRUE else Binary("->", guard, e)


def _is_rand(prop) -> bool:
    return any(tok(q) in ("rand", "randc") for q in prop.qualifiers)


def parse_uvm_items(path: str | Path | None = None, text: str | None = None, class_name: str | None = None,
                    consts: dict[str, int] | None = None) -> list[UvmItem]:
    tree = load_tree(path, text)
    src = str(path or "<text>")
    consts = dict(consts or {})
    collect_params(tree.root, consts)
    enums = collect_enums(tree.root, consts)
    out = []
    for cls in walk(tree.root):
        if kind(cls) != "ClassDeclaration":
            continue
        name = tok(cls.name)
        if class_name and name != class_name:
            continue
        base = text_of(cls.extendsClause.baseName) if cls.extendsClause is not None else ""
        schema = Schema()
        add_enum_consts(schema, enums)
        for k, v in consts.items():
            if k not in schema.consts:
                schema.consts[k] = Const(v, 32, True)
        item = UvmItem(name, base, ConstraintSet(name, schema, source=src))
        for m in cls.items:
            if kind(m) != "ClassPropertyDeclaration" or kind(m.declaration) != "DataDeclaration":
                continue
            decl = m.declaration
            info = type_info(decl.type, consts, enums)
            for d in decl.declarators:
                if not isinstance(d, S.SyntaxNode) or kind(d) != "Declarator":
                    continue
                fname = tok(d.name)
                if info is None or len(list(d.dimensions)):
                    item.warnings.append(f"{src}:{line_of(tree, d)}: field '{fname}' has unsupported type; ignored")
                    continue
                w, signed, members = info
                schema.add(Field(fname, w, signed, "rand" if _is_rand(m) else "state", tuple(members)))
        ctx = _Ctx(tree, src, consts, item)
        for m in cls.items:
            if kind(m) != "ConstraintDeclaration":
                continue
            bname = tok(m.name)
            lowered = []
            for it in _items(m.block):
                try:
                    lowered += ctx.lower(it, TRUE)
                except ParseError as ex:
                    item.warnings.append(f"{src}:{line_of(tree, it)}: {ex}")
            names = []
            for i, (e, soft, node) in enumerate(lowered):
                rname = bname if len(lowered) == 1 else f"{bname}[{i}]"
                names.append(rname)
                item.cset.rules.append(Rule(rname, e, "constraint", soft, Origin(src, line_of(tree, node), text_of(node))))
            item.blocks[bname] = names
        out.append(item)
    return out


def load_uvm_item(path: str | Path, class_name: str | None = None) -> UvmItem:
    items = parse_uvm_items(path, class_name=class_name)
    if class_name is None:
        seq = [i for i in items if "sequence_item" in i.base or "transaction" in i.base]
        items = seq or items
    if not items:
        raise ValueError(f"no class '{class_name or '*'}' found in {path}")
    return items[0]
