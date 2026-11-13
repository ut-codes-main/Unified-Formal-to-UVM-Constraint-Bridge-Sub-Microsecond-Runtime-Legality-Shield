from __future__ import annotations

import hashlib
import re
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path

from pyslang import syntax as S

from ..frontends.slang_util import kind, tok, walk

ASSIGN_KINDS = ("AssignmentExpression", "NonblockingAssignmentExpression")
COMPOUND_ASSIGN = re.compile(r".*AssignmentExpression$")
PROC_KINDS = ("AlwaysFFBlock", "AlwaysCombBlock", "AlwaysLatchBlock", "AlwaysBlock", "InitialBlock", "FinalBlock")
DIRECTIVES = ("AssertPropertyStatement", "AssumePropertyStatement", "CoverPropertyStatement", "CoverSequenceStatement")


@dataclass(frozen=True)
class Driver:
    module: str
    targets: tuple[str, ...]
    deps: tuple[str, ...]
    file: str
    start: int
    end: int
    text: str
    kind: str
    conds: tuple[str, ...] = ()
    cond_deps: tuple[str, ...] = ()
    rhs: str = ""
    partial: bool = False


@dataclass
class Directive:
    module: str
    label: str
    kind: str
    signals: tuple[str, ...]
    file: str
    line: int
    text: str


@dataclass
class Design:
    drivers: dict[str, list[Driver]] = field(default_factory=lambda: defaultdict(list))
    decls: dict[str, tuple[str, int, int, str]] = field(default_factory=dict)
    directives: list[Directive] = field(default_factory=list)
    modules: dict[str, dict] = field(default_factory=dict)
    files: dict[str, str] = field(default_factory=dict)

    def all_drivers(self) -> list[Driver]:
        seen, out = set(), []
        for ds in self.drivers.values():
            for d in ds:
                if id(d) not in seen:
                    seen.add(id(d))
                    out.append(d)
        return out

    def cone(self, roots) -> set[str]:
        out, stack = set(), list(roots)
        while stack:
            n = stack.pop()
            if n in out:
                continue
            out.add(n)
            for d in self.drivers.get(n, ()):
                stack.extend(x for x in d.deps if x not in out)
        return out

    def cone_drivers(self, cone: set[str]) -> list[Driver]:
        seen, out = set(), []
        for n in sorted(cone):
            for d in self.drivers.get(n, ()):
                key = (d.file, d.start, d.end, d.targets)
                if key not in seen:
                    seen.add(key)
                    out.append(d)
        return out

    def fingerprint(self, cone: set[str]) -> str:
        h = hashlib.sha256()
        for n in sorted(cone):
            h.update(n.encode())
            decl = self.decls.get(n)
            h.update(b"|decl:" + (decl[3].encode() if decl else b"?"))
            for d in sorted(self.drivers.get(n, ()), key=lambda d: d.text):
                h.update(b"|drv:" + d.text.encode())
            h.update(b"\n")
        return h.hexdigest()


def normalize(text: str) -> str:
    text = re.sub(r"//[^\n]*", "", text)
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    return re.sub(r"\s+", " ", text).strip()


def _line(tree, loc) -> int:
    return tree.sourceManager.getLineNumber(loc)


def _span(tree, node) -> tuple[int, int]:
    r = node.sourceRange
    return _line(tree, r.start), _line(tree, r.end)


def _idents(node, scope: str, local: set[str] | None = None) -> set[str]:
    out = set()
    if node is None:
        return out
    for n in walk(node):
        k = kind(n)
        if k in ("IdentifierName", "IdentifierSelectName"):
            name = tok(n.identifier)
            if name and (local is None or name not in local):
                out.add(f"{scope}.{name}")
    return out


def _targets(node, scope: str) -> tuple[set[str], set[str]]:
    k = kind(node)
    if k == "IdentifierName":
        return {f"{scope}.{tok(node.identifier)}"}, set()
    if k == "IdentifierSelectName":
        deps = set()
        for sel in node.selectors:
            if isinstance(sel, S.SyntaxNode):
                deps |= _idents(sel, scope)
        return {f"{scope}.{tok(node.identifier)}"}, deps
    if k == "ConcatenationExpression":
        t, d = set(), set()
        for e in node.expressions:
            if isinstance(e, S.SyntaxNode):
                a, b = _targets(e, scope)
                t |= a
                d |= b
        return t, d
    if k == "ParenthesizedExpression":
        return _targets(node.expression, scope)
    if k == "MemberAccessExpression":
        return _targets(node.left, scope)
    if k == "ElementSelectExpression":
        a, b = _targets(node.left, scope)
        return a, b | _idents(node.select, scope)
    return _idents(node, scope), set()


class _Builder:
    def __init__(self, design: Design, tree, path: str):
        self.d = design
        self.tree = tree
        self.path = path

    def add(self, module, targets, deps, node, kind_, ctx_text: tuple[str, ...] = (), conds: tuple[str, ...] = (),
            cond_deps: set[str] | None = None, rhs: str = "", partial: bool = False):
        start, end = _span(self.tree, node)
        text = " ".join(ctx_text + (normalize(str(node)),))
        drv = Driver(module, tuple(sorted(targets)), tuple(sorted(set(deps) - set(targets))), self.path, start, end, text, kind_,
                     conds, tuple(sorted(cond_deps or ())), rhs, partial)
        for t in targets:
            self.d.drivers[t].append(drv)

    def stmt(self, module: str, node, ctx: set[str], kind_: str, local: set[str], ctx_text: tuple[str, ...] = (),
             conds: tuple[str, ...] = ()):
        k = kind(node)
        if k == "ExpressionStatement":
            e = node.expr
            if COMPOUND_ASSIGN.match(kind(e)):
                t, d = _targets(e.left, module)
                t = {x for x in t if x.split(".", 1)[1] not in local}
                deps = d | _idents(e.right, module, local) | ctx
                if kind(e) not in ASSIGN_KINDS:
                    deps |= t
                if t:
                    partial = kind(e.left) != "IdentifierName"
                    self.add(module, t, deps, node, kind_, ctx_text, conds, ctx, normalize(str(e.right)), partial)
            elif kind(e) in ("PostincrementExpression", "PreincrementExpression", "PostdecrementExpression", "PredecrementExpression"):
                t, _ = _targets(e.operand, module)
                t = {x for x in t if x.split(".", 1)[1] not in local}
                if t:
                    self.add(module, t, t | ctx, node, kind_, ctx_text, conds, ctx)
            return
        if k == "ConditionalStatement":
            cond = normalize(str(node.predicate))
            c = ctx | _idents(node.predicate, module, local)
            self.stmt(module, node.statement, c, kind_, local, ctx_text + (f"if({cond})",), conds + (f"({cond})",))
            if node.elseClause is not None:
                self.stmt(module, node.elseClause.clause, c, kind_, local, ctx_text + (f"else({cond})",), conds + (f"!({cond})",))
            return
        if k == "CaseStatement":
            sel = normalize(str(node.expr))
            c = ctx | _idents(node.expr, module, local)
            matched = []
            for it in node.items:
                if not isinstance(it, S.SyntaxNode):
                    continue
                ci = set(c)
                label = "default"
                if kind(it) == "StandardCaseItem":
                    exprs = [normalize(str(e)) for e in it.expressions if isinstance(e, S.SyntaxNode)]
                    label = ",".join(exprs)
                    for e in it.expressions:
                        if isinstance(e, S.SyntaxNode):
                            ci |= _idents(e, module, local)
                    here = " || ".join(f"({sel}) == ({x})" for x in exprs)
                    matched.append(here)
                    guard = f"({here})"
                else:
                    guard = f"!({' || '.join(matched)})" if matched else "1"
                self.stmt(module, it.clause, ci, kind_, local, ctx_text + (f"case({sel}:{label})",), conds + (guard,))
            return
        if k == "SequentialBlockStatement":
            for it in node.items:
                if isinstance(it, S.SyntaxNode):
                    self.stmt(module, it, ctx, kind_, local, ctx_text, conds)
            return
        if k == "TimingControlStatement":
            tc = normalize(str(node.timingControl))
            self.stmt(module, node.statement, ctx | _idents(node.timingControl, module, local), kind_, local, ctx_text + (tc,), conds)
            return
        if k in ("ForLoopStatement", "LoopStatement", "WhileStatement", "DoWhileStatement", "ForeverStatement", "ForeachLoopStatement"):
            loc = set(local)
            for n in walk(node):
                if kind(n) == "ForVariableDeclaration":
                    loc.add(tok(n.declarator.name))
            c = ctx
            head = []
            for attr in ("initializers", "stopExpr", "steps", "expr"):
                sub = getattr(node, attr, None)
                if isinstance(sub, S.SyntaxNode):
                    c = c | _idents(sub, module, loc)
                    head.append(normalize(str(sub)))
            self.stmt(module, node.statement, c, kind_, loc, ctx_text + (f"loop({';'.join(head)})",), conds + ("?loop",))
            return
        for c in node:
            if isinstance(c, S.SyntaxNode) and kind(c).endswith("Statement"):
                self.stmt(module, c, ctx, kind_, local, ctx_text, conds)

    def instance(self, mod_name: str, n) -> None:
        info = self.d.modules[mod_name]
        child = tok(n.type)
        for inst in n.instances:
            if not isinstance(inst, S.SyntaxNode):
                continue
            iname = tok(inst.decl.name) if inst.decl is not None else child
            conns = {}
            for c in inst.connections:
                if not isinstance(c, S.SyntaxNode):
                    continue
                if kind(c) == "NamedPortConnection":
                    conns[tok(c.name)] = _idents(c.expr, mod_name) if c.expr is not None else set()
                elif kind(c) == "WildcardPortConnection":
                    conns["*"] = set()
            info["instances"].append((iname, child, conns))

    def module(self, mod):
        name = tok(mod.header.name)
        info = {"file": self.path, "ports": {}, "instances": []}
        self.d.modules[name] = info
        ports = getattr(mod.header, "ports", None)
        if ports is not None and kind(ports) == "AnsiPortList":
            direction = "inout"
            for p in ports.ports:
                if isinstance(p, S.SyntaxNode) and kind(p) == "ImplicitAnsiPort":
                    dtok = tok(getattr(p.header, "direction", None))
                    direction = dtok or direction
                    pname = tok(p.declarator.name)
                    info["ports"][pname] = direction
                    s, e = _span(self.tree, p)
                    self.d.decls[f"{name}.{pname}"] = (self.path, s, e, normalize(str(p)))
        for n in walk(mod):
            k = kind(n)
            if k in ("DataDeclaration", "NetDeclaration", "PortDeclaration"):
                ty = normalize(str(getattr(n, "type", "") or getattr(n, "header", "")))
                for d in n.declarators:
                    if not isinstance(d, S.SyntaxNode) or kind(d) != "Declarator":
                        continue
                    sig = f"{name}.{tok(d.name)}"
                    s, e = _span(self.tree, d)
                    self.d.decls[sig] = (self.path, s, e, f"{ty} {normalize(str(d.dimensions))}".strip())
                    if d.initializer is not None and k != "PortDeclaration":
                        self.add(name, {sig}, _idents(d.initializer.expr, name), n, "assign")
                    if k == "PortDeclaration":
                        info["ports"][tok(d.name)] = tok(getattr(n.header, "direction", None)) or "inout"
            elif k == "ParameterDeclaration":
                for d in n.declarators:
                    if isinstance(d, S.SyntaxNode) and kind(d) == "Declarator":
                        sig = f"{name}.{tok(d.name)}"
                        s, e = _span(self.tree, d)
                        self.d.decls[sig] = (self.path, s, e, normalize(str(d)))
                        if d.initializer is not None:
                            self.add(name, {sig}, _idents(d.initializer.expr, name), d, "param")
            elif k == "ContinuousAssign":
                for a in n.assignments:
                    if isinstance(a, S.SyntaxNode) and kind(a) in ASSIGN_KINDS:
                        t, deps = _targets(a.left, name)
                        self.add(name, t, deps | _idents(a.right, name), a, "assign", rhs=normalize(str(a.right)))
            elif k in PROC_KINDS:
                self.stmt(name, n.statement, set(), "ff" if k == "AlwaysFFBlock" else "comb", set())
            elif k == "FunctionDeclaration":
                fname = tok(n.prototype.name.identifier) if hasattr(n.prototype.name, "identifier") else tok(n.prototype.name)
                local = {fname}
                for p in walk(n.prototype):
                    if kind(p) == "Declarator":
                        local.add(tok(p.name))
                for it in n.items:
                    if isinstance(it, S.SyntaxNode):
                        for dd in walk(it):
                            if kind(dd) == "Declarator":
                                local.add(tok(dd.name))
                deps = set()
                for it in n.items:
                    if isinstance(it, S.SyntaxNode):
                        deps |= _idents(it, name, local)
                self.add(name, {f"{name}.{fname}"}, deps, n, "function")
            elif k == "HierarchyInstantiation":
                self.instance(name, n)
            elif k in DIRECTIVES:
                label = tok(n.label.name) if n.label is not None else f"L{_span(self.tree, n)[0]}"
                sigs = _idents(n.propertySpec, name)
                self.d.directives.append(Directive(name, label, k.replace("PropertyStatement", "").replace("SequenceStatement", "").lower(),
                                                   tuple(sorted(sigs)), self.path, _span(self.tree, n)[0], normalize(str(n))))


def _link_instances(d: Design) -> None:
    for mod, info in d.modules.items():
        for iname, child, conns in info["instances"]:
            cinfo = d.modules.get(child)
            if "*" in conns and cinfo is not None:
                for port in cinfo["ports"]:
                    conns.setdefault(port, {f"{mod}.{port}"})
                del conns["*"]
            for port, sigs in conns.items():
                direction = cinfo["ports"].get(port, "inout") if cinfo else "inout"
                cport = f"{child}.{port}"
                if direction in ("input", "inout"):
                    d.drivers[cport].append(Driver(mod, (cport,), tuple(sorted(sigs)), info["file"], 0, 0, f"{iname}.{port}<-{sorted(sigs)}", "port"))
                if direction in ("output", "inout"):
                    for s in sigs:
                        d.drivers[s].append(Driver(mod, (s,), (cport,), info["file"], 0, 0, f"{s}<-{iname}.{port}", "port"))


def load_design(paths, root: str | Path | None = None) -> Design:
    d = Design()
    pending_binds = []
    for p in paths:
        p = Path(p)
        text = p.read_text()
        rel = p.relative_to(root).as_posix() if root is not None and p.is_relative_to(root) else p.as_posix()
        d.files[rel] = hashlib.sha256(text.encode()).hexdigest()
        tree = S.SyntaxTree.fromText(text, rel)
        b = _Builder(d, tree, rel)
        binds = []
        for n in walk(tree.root):
            if kind(n) in ("ModuleDeclaration", "InterfaceDeclaration", "ProgramDeclaration", "CheckerDeclaration"):
                b.module(n)
            elif kind(n) == "BindDirective":
                binds.append((b, n))
        pending_binds.extend(binds)
    for b, n in pending_binds:
        target = normalize(str(n.target))
        if target not in d.modules:
            d.modules[target] = {"file": b.path, "ports": {}, "instances": []}
        b.instance(target, n.instantiation)
    _link_instances(d)
    return d
