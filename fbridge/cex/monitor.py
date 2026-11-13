from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path

import yaml

from .vcd import Waveform

PROFILES = Path(__file__).with_name("profiles")


@dataclass
class Channel:
    name: str
    valid: str
    ready: str | None
    fields: dict[str, str]
    beats: bool = False


@dataclass
class TxnType:
    name: str
    request: list[str]
    response: str | None
    item: dict[str, str]
    observe: dict[str, str] = field(default_factory=dict)


@dataclass
class MonitorDef:
    name: str
    clock: str
    reset: str | None
    reset_active: int
    channels: dict[str, Channel]
    transactions: dict[str, TxnType]

    def signals(self) -> list[str]:
        out = [self.clock] + ([self.reset] if self.reset else [])
        for c in self.channels.values():
            out.append(c.valid)
            if c.ready:
                out.append(c.ready)
            out += list(c.fields.values())
        return out


def load_monitor(spec: str | Path, prefix: str | None = None, overrides: dict | None = None) -> MonitorDef:
    p = Path(spec)
    if not p.exists():
        p = PROFILES / f"{spec}.yaml"
    d = yaml.safe_load(p.read_text())
    if overrides:
        d.update(overrides)
    pre = d.get("prefix", "") if prefix is None else prefix

    def sig(n):
        return None if n is None else f"{pre}{n}"

    chans = {k: Channel(k, sig(c["valid"]), sig(c.get("ready")), {f: sig(s) for f, s in c.get("fields", {}).items()}, bool(c.get("beats")))
             for k, c in d["channels"].items()}
    txns = {k: TxnType(k, list(t["request"]), t.get("response"), dict(t["item"]), dict(t.get("observe") or {}))
            for k, t in d["transactions"].items()}
    rst = d.get("reset") or {}
    return MonitorDef(d.get("name", p.stem), d.get("clock", "clk"), rst.get("signal"), int(rst.get("active", 0)), chans, txns)


@dataclass
class Beat:
    channel: str
    cycle: int
    valid_cycle: int
    fields: dict[str, int]


@dataclass
class Transaction:
    index: int
    kind: str
    issue_cycle: int
    accept_cycle: int
    item: dict[str, object]
    beats: dict[str, list[Beat]]
    response_cycle: int | None = None
    observed: dict[str, int] = field(default_factory=dict)

    def channel_cycles(self) -> dict[str, list[int]]:
        return {ch: [b.cycle for b in bs] for ch, bs in self.beats.items()}


def extract_beats(mon: MonitorDef, cycles: list[dict[str, int]]) -> dict[str, list[Beat]]:
    out: dict[str, list[Beat]] = {k: [] for k in mon.channels}
    for name, ch in mon.channels.items():
        rose = None
        for t, cyc in enumerate(cycles):
            if mon.reset and cyc.get(mon.reset, 1 - mon.reset_active) == mon.reset_active:
                rose = None
                continue
            v = cyc.get(ch.valid, 0)
            if v and rose is None:
                rose = t
            if not v:
                rose = None
                continue
            if ch.ready is None or cyc.get(ch.ready, 0):
                out[name].append(Beat(name, t, rose if rose is not None else t, {f: cyc.get(s, 0) for f, s in ch.fields.items()}))
                rose = None
    return out


def assemble(mon: MonitorDef, cycles: list[dict[str, int]]) -> list[Transaction]:
    beats = extract_beats(mon, cycles)
    txns: list[Transaction] = []
    for tname, tt in mon.transactions.items():
        queues = {c: list(beats[c]) for c in tt.request}
        resp = list(beats[tt.response]) if tt.response else []
        while all(queues[c] for c in tt.request):
            parts = {}
            for c in tt.request:
                ch = mon.channels[c]
                if ch.beats and "last" in ch.fields:
                    seq = []
                    while queues[c]:
                        b = queues[c].pop(0)
                        seq.append(b)
                        if b.fields.get("last", 1):
                            break
                    parts[c] = seq
                else:
                    parts[c] = [queues[c].pop(0)]
            item: dict[str, object] = {}
            for f, src in tt.item.items():
                if "." in src:
                    ch, fld = src.split(".", 1)
                    vals = [b.fields[fld] for b in parts[ch]]
                    item[f] = vals[0] if len(vals) == 1 else vals
                else:
                    item[f] = src
            issue = min(b.valid_cycle for bs in parts.values() for b in bs)
            accept = max(b.cycle for bs in parts.values() for b in bs)
            tx = Transaction(0, tname, issue, accept, item, parts)
            if resp:
                r = resp.pop(0)
                tx.response_cycle = r.cycle
                for f, src in tt.observe.items():
                    ch, fld = src.split(".", 1)
                    tx.observed[f] = r.fields.get(fld, 0)
            txns.append(tx)
    txns.sort(key=lambda t: (t.issue_cycle, t.accept_cycle, t.kind))
    for i, t in enumerate(txns):
        t.index = i
    return txns
