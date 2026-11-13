from __future__ import annotations

from dataclasses import dataclass

from .codegen_c import c_ident
from .compile import CompiledShield


@dataclass
class SvSource:
    package: str
    mixin: str
    package_name: str
    mixin_name: str


def _sv_array(name: str, width: int, values, per_line: int = 16) -> str:
    vals = [f"{width}'d{v}" for v in values] or [f"{width}'d0"]
    rows = [", ".join(vals[i:i + per_line]) for i in range(0, len(vals), per_line)]
    body = ",\n    ".join(rows)
    return f"  localparam bit [{width - 1}:0] {name} [{len(vals)}] = '{{\n    {body}\n  }};"


def _sv_hex_array(name: str, width: int, values, per_line: int = 4) -> str:
    vals = [f"{width}'h{v:X}" for v in values] or [f"{width}'h0"]
    rows = [", ".join(vals[i:i + per_line]) for i in range(0, len(vals), per_line)]
    body = ",\n    ".join(rows)
    return f"  localparam bit [{width - 1}:0] {name} [{len(vals)}] = '{{\n    {body}\n  }};"


def generate_sv(comp: CompiledShield, prefix: str | None = None) -> SvSource:
    spec = comp.spec
    P = c_ident(prefix or spec.name)
    pkg = f"{P}_pkg"
    lv = comp.table
    nbits = max(1, (len(lv.var) - 1).bit_length())
    root = lv.index[comp.legal]
    reach_root = lv.index[comp.reach]
    class_nodes = [0] + [lv.index[c.node] for c in comp.classes]
    node_class = [0] * len(lv.var)
    for n, k in comp.node_class().items():
        node_class[n] = k
    kbits = max(1, len(comp.classes).bit_length())
    offsets, off = {}, 0
    for f in comp.fields:
        offsets[f.name] = off
        off += f.mask_words
    mask_words = max(1, off)
    envs = [t for t in spec.transitions if t.kind == "env"]

    p = [
        f"package {pkg};",
        "",
        f"  localparam int STATE_BITS  = {spec.state_bits};",
        f"  localparam int ACTION_BITS = {spec.action_bits};",
        f"  localparam int NUM_CLASSES = {len(comp.classes)};",
        f"  localparam int MASK_WORDS  = {mask_words};",
        f"  localparam int DEPTH  = {lv.depth};",
        f"  localparam int SDEPTH = {comp.state_depth};",
        f"  localparam int ADEPTH = {comp.action_depth};",
        f"  localparam int RDEPTH = {comp.reach_depth};",
        f"  localparam int ROOT = {root};",
        f"  localparam int REACH_ROOT = {reach_root};",
        "",
        "  localparam int SHIELD_LEGAL = 1;",
        "  localparam int SHIELD_REPAIRED = 0;",
        "  localparam int SHIELD_NO_LEGAL_ACTION = -1;",
        "  localparam int SHIELD_FIXED_FIELD_CONFLICT = -2;",
        "",
    ]
    for f in spec.state:
        p.append(f"  localparam int S_{c_ident(f.name).upper()}_LSB = {f.lsb}, S_{c_ident(f.name).upper()}_WIDTH = {f.width};")
    for f in comp.fields:
        n = c_ident(f.name).upper()
        p.append(f"  localparam int A_{n}_LSB = {f.lsb}, A_{n}_WIDTH = {f.width}, MASK_OFF_{n} = {offsets[f.name]}, MASK_LEN_{n} = {f.mask_words};")
    for f in spec.state + spec.action:
        for name, v in f.enum:
            p.append(f"  localparam int {c_ident(f.name).upper()}_{c_ident(name).upper()} = {v};")
    for i, t in enumerate(envs):
        p.append(f"  localparam int ENV_{c_ident(t.name).upper()} = {i};")
    p += [
        "",
        "  typedef longint unsigned u64_t;",
        "  typedef u64_t mask_t [MASK_WORDS];",
        "",
        "`ifndef SHIELD_NO_DPI",
        f'  import "DPI-C" function int {P}_is_action_legal(input longint unsigned state_hash, input longint unsigned candidate_tx);',
        f'  import "DPI-C" function int {P}_is_state_reachable(input longint unsigned state_hash);',
        f'  import "DPI-C" function int {P}_class_of(input longint unsigned state_hash);',
        f'  import "DPI-C" function int {P}_project_or_mask_action(input longint unsigned state_hash, input longint unsigned candidate_tx,',
        "                                                                   output longint unsigned repaired_tx, output longint unsigned field_masks[MASK_WORDS]);",
        f'  import "DPI-C" function longint unsigned {P}_class_bitmap_word(input int class_id, input int word);',
        f'  import "DPI-C" function longint unsigned {P}_explain(input longint unsigned state_hash, input longint unsigned candidate_tx);',
        f'  import "DPI-C" function longint unsigned {P}_step_action(input longint unsigned state_hash, input longint unsigned tx);',
        f'  import "DPI-C" function longint unsigned {P}_step_env(input longint unsigned state_hash, input int env_id);',
        f'  import "DPI-C" function string {P}_rule_name(input int rule_id);',
        "`endif",
        "",
        _sv_array("NV", 7, lv.var),
        _sv_array("NC0", nbits, [c[0] for c in lv.child]),
        _sv_array("NC1", nbits, [c[1] for c in lv.child]),
        _sv_array("CLASS_NODE", nbits, class_nodes),
        _sv_array("NODE_CLASS", kbits, node_class),
    ]
    imm = 0
    for f in comp.fields:
        if not f.mutable:
            imm |= ((1 << f.width) - 1) << f.lsb
    p.append(f"  localparam u64_t IMMUTABLE = 64'h{imm:X};")
    masks = []
    for k in range(len(comp.classes) + 1):
        row = [0] * mask_words
        if k:
            c = comp.classes[k - 1]
            for f in comp.fields:
                o = offsets[f.name]
                if f.narrow:
                    for w in range(f.mask_words):
                        row[o + w] = (c.masks[f.name] >> (64 * w)) & ((1 << 64) - 1)
                else:
                    ivs = c.intervals[f.name]
                    row[o], row[o + 1] = (ivs[0][0], max(h for _, h in ivs)) if ivs else (1, 0)
        else:
            for f in comp.fields:
                if not f.narrow:
                    row[offsets[f.name]] = 1
        masks += row
    p.append(_sv_hex_array("MASKS", 64, masks))
    p += [
        "",
        "  function automatic bit sv_bit(int unsigned pos, u64_t s, u64_t tx);",
        "    return pos >= 64 ? tx[pos - 64] : s[pos];",
        "  endfunction",
        "",
        "  function automatic int unsigned sv_walk(int unsigned n, u64_t s, u64_t tx, int steps);",
        "    for (int i = 0; i < steps; i++) n = sv_bit(NV[n], s, tx) ? NC1[n] : NC0[n];",
        "    return n;",
        "  endfunction",
        "",
        "  function automatic int sv_class_of(u64_t state_hash);",
        "    int unsigned n = ROOT;",
        "    if (STATE_BITS < 64 && (state_hash >> STATE_BITS) != 0) return 0;",
        "    for (int i = 0; i < SDEPTH; i++) if (NV[n] < 64) n = state_hash[NV[n]] ? NC1[n] : NC0[n];",
        "    return NODE_CLASS[n];",
        "  endfunction",
        "",
        "  function automatic bit sv_is_action_legal(u64_t state_hash, u64_t candidate_tx);",
        "    if (STATE_BITS < 64 && (state_hash >> STATE_BITS) != 0) return 0;",
        "    if (ACTION_BITS < 64 && (candidate_tx >> ACTION_BITS) != 0) return 0;",
        "    return sv_walk(ROOT, state_hash, candidate_tx, DEPTH) == 1;",
        "  endfunction",
        "",
        "  function automatic bit sv_is_state_reachable(u64_t state_hash);",
        "    if (STATE_BITS < 64 && (state_hash >> STATE_BITS) != 0) return 0;",
        "    return sv_walk(REACH_ROOT, state_hash, 0, RDEPTH) == 1;",
        "  endfunction",
        "",
        "  function automatic int sv_project_or_mask_action(u64_t state_hash, u64_t candidate_tx, output u64_t repaired_tx, output mask_t field_masks);",
        "    int k = sv_class_of(state_hash);",
        "    int unsigned n;",
        "    u64_t tx, out_tx;",
        "    bit conflict = 0;",
        "    for (int w = 0; w < MASK_WORDS; w++) field_masks[w] = MASKS[k * MASK_WORDS + w];",
        "    repaired_tx = candidate_tx;",
        "    if (k == 0) return SHIELD_NO_LEGAL_ACTION;",
        "    tx = ACTION_BITS < 64 ? candidate_tx & ((64'd1 << ACTION_BITS) - 1) : candidate_tx;",
        "    out_tx = tx;",
        "    n = CLASS_NODE[k];",
        "    for (int i = 0; i < ADEPTH; i++) begin",
        "      int unsigned pos = (NV[n] - 64) & 63;",
        "      bit b = out_tx[pos];",
        "      bit dead = ((b ? NC1[n] : NC0[n]) == 0);",
        "      if (dead) begin",
        "        conflict |= IMMUTABLE[pos];",
        "        out_tx[pos] = !b;",
        "        b = !b;",
        "      end",
        "      n = b ? NC1[n] : NC0[n];",
        "    end",
        "    repaired_tx = out_tx;",
        "    if (out_tx == candidate_tx) return SHIELD_LEGAL;",
        "    return conflict ? SHIELD_FIXED_FIELD_CONFLICT : SHIELD_REPAIRED;",
        "  endfunction",
        "",
        "  function automatic bit is_action_legal(u64_t state_hash, u64_t candidate_tx);",
        "`ifdef SHIELD_NO_DPI",
        "    return sv_is_action_legal(state_hash, candidate_tx);",
        "`else",
        f"    return {P}_is_action_legal(state_hash, candidate_tx) != 0;",
        "`endif",
        "  endfunction",
        "",
        "  function automatic int project_or_mask_action(u64_t state_hash, u64_t candidate_tx, output u64_t repaired_tx, output mask_t field_masks);",
        "`ifdef SHIELD_NO_DPI",
        "    return sv_project_or_mask_action(state_hash, candidate_tx, repaired_tx, field_masks);",
        "`else",
        f"    return {P}_project_or_mask_action(state_hash, candidate_tx, repaired_tx, field_masks);",
        "`endif",
        "  endfunction",
        "",
        "  function automatic int class_of(u64_t state_hash);",
        "`ifdef SHIELD_NO_DPI",
        "    return sv_class_of(state_hash);",
        "`else",
        f"    return {P}_class_of(state_hash);",
        "`endif",
        "  endfunction",
        "",
        f"endpackage : {pkg}",
        "",
    ]

    item = f"{P}_shield_item"
    m = [
        f"`ifndef {P.upper()}_SHIELD_ITEM_SVH",
        f"`define {P.upper()}_SHIELD_ITEM_SVH",
        "",
        f"class {item} #(type BASE = uvm_sequence_item) extends BASE;",
        "",
    ]
    for f in comp.fields:
        m.append(f"  rand bit [{f.width - 1}:0] {f.name};")
    m += [
        "",
        f"  {pkg}::u64_t shield_state_hash;",
        "  bit shield_enable = 1;",
        "  bit shield_exact = 0;",
        "  bit shield_no_legal = 0;",
        "  int shield_class;",
        "  int unsigned shield_repairs;",
        "  int shield_last_status;",
        f"  {pkg}::mask_t shield_masks;",
    ]
    table_mode = comp.bitmaps is not None
    for f in comp.fields:
        if f.narrow:
            m.append(f"  bit [{(1 << f.width) - 1}:0] shield_allow_{f.name};")
        else:
            m.append(f"  bit [{f.width - 1}:0] shield_lo_{f.name}, shield_hi_{f.name};")
    if table_mode:
        nrel = len(comp.relevant_action_bits)
        m.append(f"  bit shield_bitmap [{1 << nrel}];")
    m += ["", "  constraint c_shield_masks {", "    if (shield_enable && !shield_no_legal) {"]
    for f in comp.fields:
        if f.narrow:
            m.append(f"      shield_allow_{f.name}[{f.name}] == 1'b1;")
        else:
            m.append(f"      {f.name} inside {{[shield_lo_{f.name}:shield_hi_{f.name}]}};")
    m += ["    }", "  }", ""]
    if table_mode:
        bits = []
        by_pos = {}
        for f in comp.fields:
            for b in range(f.width):
                by_pos[f.lsb + b] = f"{f.name}[{b}]"
        idx = ", ".join(by_pos[b] for b in reversed(comp.relevant_action_bits))
        m += [
            "  constraint c_shield_exact {",
            f"    if (shield_enable && shield_exact && !shield_no_legal) shield_bitmap[{{{idx}}}] == 1'b1;",
            "  }",
            "",
        ]
    m += [
        f'  function new(string name = "{item}");',
        "    super.new(name);",
        "  endfunction",
        "",
        f"  virtual function {pkg}::u64_t shield_pack();",
        f"    {pkg}::u64_t tx = 0;",
    ]
    for f in comp.fields:
        m.append(f"    tx |= {pkg}::u64_t'({f.name}) << {f.lsb};")
    m += ["    return tx;", "  endfunction", "", f"  virtual function void shield_unpack({pkg}::u64_t tx);"]
    for f in comp.fields:
        m.append(f"    {f.name} = tx[{f.lsb + f.width - 1}:{f.lsb}];")
    m += ["  endfunction", "", "  function void pre_randomize();", f"    {pkg}::u64_t unused;",
          "    super.pre_randomize();", "    if (!shield_enable) return;",
          f"    shield_class = {pkg}::class_of(shield_state_hash);",
          "    shield_no_legal = (shield_class == 0);",
          f"    void'({pkg}::project_or_mask_action(shield_state_hash, 0, unused, shield_masks));"]
    for f in comp.fields:
        o = offsets[f.name]
        if f.narrow:
            for w in range(f.mask_words):
                hi = min((w + 1) * 64, 1 << f.width) - 1
                m.append(f"    shield_allow_{f.name}[{hi}:{w * 64}] = shield_masks[{o + w}][{hi - w * 64}:0];")
        else:
            m.append(f"    shield_lo_{f.name} = shield_masks[{o}];")
            m.append(f"    shield_hi_{f.name} = shield_masks[{o + 1}];")
    if table_mode:
        nrel = len(comp.relevant_action_bits)
        m += [
            "`ifndef SHIELD_NO_DPI",
            "    if (shield_exact && !shield_no_legal)",
            f"      for (int i = 0; i < {1 << nrel}; i++) shield_bitmap[i] = {P}_class_bitmap_word(shield_class, i >> 6) >> (i & 63);",
            "`endif",
        ]
    m += [
        "  endfunction",
        "",
        "  function void post_randomize();",
        f"    {pkg}::u64_t repaired;",
        f"    {pkg}::mask_t unused;",
        "    super.post_randomize();",
        "    if (!shield_enable || shield_no_legal) return;",
        f"    shield_last_status = {pkg}::project_or_mask_action(shield_state_hash, shield_pack(), repaired, unused);",
        f"    if (shield_last_status == {pkg}::SHIELD_REPAIRED || shield_last_status == {pkg}::SHIELD_FIXED_FIELD_CONFLICT) begin",
        "      shield_unpack(repaired);",
        "      shield_repairs++;",
        "    end",
        "  endfunction",
        "",
        "  function bit shield_is_legal();",
        f"    return {pkg}::is_action_legal(shield_state_hash, shield_pack());",
        "  endfunction",
        "endclass",
        "",
        "`endif",
        "",
    ]
    return SvSource("\n".join(p), "\n".join(m), f"{P}_pkg.sv", f"{P}_shield_item.svh")
