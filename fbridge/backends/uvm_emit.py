from __future__ import annotations

import re

from ..ir.ast import Binary, ConstraintSet, Field, Rule
from ..ir.printer import to_sv


def sv_ident(name: str) -> str:
    return re.sub(r"[^A-Za-z0-9_]", "_", name)


def field_decl(f: Field, enum_type: str | None = None) -> str:
    q = "rand " if f.kind == "rand" else ""
    if enum_type:
        return f"{q}{enum_type} {f.name};"
    sign = " signed" if f.signed else ""
    dim = f" [{f.width - 1}:0]" if f.width > 1 else ""
    return f"{q}bit{sign}{dim} {f.name};"


def rule_constraint(r: Rule, indent: str = "  ") -> str:
    soft = "soft " if r.soft else ""
    name = f"c_{sv_ident(r.name)}"
    body = r.expr
    parts = []
    if isinstance(body, Binary) and body.op == "&&" and not r.soft:
        stack, flat = [body], []
        while stack:
            n = stack.pop()
            if isinstance(n, Binary) and n.op == "&&":
                stack += [n.b, n.a]
            else:
                flat.append(n)
        parts = flat
    else:
        parts = [body]
    if r.guard is not None:
        inner = " ".join(f"{soft}{to_sv(p)};" for p in parts)
        stmt = f"{to_sv(r.guard)} -> {{ {inner} }}"
        lines = [f"{indent}{indent}{stmt}"]
    else:
        lines = [f"{indent}{indent}{soft}{to_sv(p)};" for p in parts]
    src = f"  // {r.origin.file}:{r.origin.line}" if r.origin.file else ""
    return f"{indent}constraint {name} {{{src}\n" + "\n".join(lines) + f"\n{indent}}}"


def enum_member_names(cset: ConstraintSet) -> set[str]:
    return {n for f in cset.schema.fields.values() for n, _ in f.enum}


def plain_consts(cset: ConstraintSet) -> list[tuple[str, int]]:
    members = enum_member_names(cset)
    return [(n, c.value) for n, c in cset.schema.consts.items() if n not in members]


def emit_constraints(cset: ConstraintSet, indent: str = "  ") -> str:
    return "\n\n".join(rule_constraint(r, indent) for r in cset.rules)


def emit_item_class(cset: ConstraintSet, class_name: str | None = None, base: str = "uvm_sequence_item") -> str:
    cname = class_name or cset.name
    lines = [f"class {cname} extends {base};"]
    enums = {}
    for f in cset.schema.fields.values():
        if f.enum:
            tname = f"{f.name}_e"
            enums[f.name] = tname
            members = ", ".join(f"{n} = {v}" for n, v in f.enum)
            dim = f" [{f.width - 1}:0]" if f.width > 1 else ""
            lines.append(f"  typedef enum bit{dim} {{{members}}} {tname};")
    for n, v in plain_consts(cset):
        lines.append(f"  localparam int unsigned {n} = 32'h{v:X};")
    if len(lines) > 1:
        lines.append("")
    for f in cset.schema.fields.values():
        lines.append("  " + field_decl(f, enums.get(f.name)))
    lines += ["", f"  `uvm_object_utils_begin({cname})"]
    for f in cset.schema.fields.values():
        if f.name in enums:
            lines.append(f"    `uvm_field_enum({enums[f.name]}, {f.name}, UVM_ALL_ON)")
        else:
            lines.append(f"    `uvm_field_int({f.name}, UVM_ALL_ON)")
    lines += ["  `uvm_object_utils_end", ""]
    lines.append(emit_constraints(cset))
    lines += [
        "",
        f'  function new(string name = "{cname}");',
        "    super.new(name);",
        "  endfunction",
        "endclass",
        "",
    ]
    return "\n".join(lines)
