from __future__ import annotations

import bisect
import shutil
import subprocess
import tempfile
from dataclasses import dataclass, field
from pathlib import Path


class VcdError(Exception):
    pass


@dataclass
class VcdVar:
    code: str
    name: str
    width: int
    kind: str


@dataclass
class Waveform:
    timescale: str = "1ns"
    vars: dict[str, VcdVar] = field(default_factory=dict)
    times: dict[str, list[int]] = field(default_factory=dict)
    values: dict[str, list[int]] = field(default_factory=dict)
    unknown: dict[str, list[bool]] = field(default_factory=dict)
    end_time: int = 0

    def names(self) -> list[str]:
        return sorted(self.vars)

    def resolve(self, name: str) -> str:
        if name in self.vars:
            return name
        hits = [n for n in self.vars if n.endswith("." + name)]
        if len(hits) == 1:
            return hits[0]
        if not hits:
            raise VcdError(f"signal '{name}' not found in waveform")
        hits.sort(key=lambda n: n.count("."))
        if hits[0].count(".") < hits[1].count("."):
            return hits[0]
        raise VcdError(f"signal '{name}' is ambiguous: {hits[:4]}")

    def width(self, name: str) -> int:
        return self.vars[self.resolve(name)].width

    def value_before(self, name: str, t: int) -> tuple[int, bool]:
        code = self.vars[self.resolve(name)].code
        ts = self.times.get(code, [])
        i = bisect.bisect_left(ts, t) - 1
        if i < 0:
            return 0, True
        return self.values[code][i], self.unknown[code][i]

    def edges(self, clock: str, rising: bool = True) -> list[int]:
        code = self.vars[self.resolve(clock)].code
        out, prev = [], None
        for t, v in zip(self.times.get(code, []), self.values.get(code, [])):
            if prev is not None and ((rising and prev == 0 and v == 1) or (not rising and prev == 1 and v == 0)):
                out.append(t)
            prev = v
        return out

    def sample(self, names: list[str], clock: str | None = None, period: int | None = None) -> list[dict[str, int]]:
        if clock is not None:
            stamps = self.edges(clock)
        elif period:
            stamps = list(range(period, self.end_time + period, period))
        else:
            raise VcdError("need a clock signal or a sampling period")
        resolved = {n: self.resolve(n) for n in names}
        out = []
        for t in stamps:
            out.append({n: self.value_before(r, t)[0] for n, r in resolved.items()})
        return out


def _parse_value(bits: str) -> tuple[int, bool]:
    bits = bits.lower()
    unknown = any(c in "xzu-" for c in bits)
    clean = "".join("0" if c in "xzu-" else c for c in bits)
    return (int(clean, 2) if clean else 0), unknown


def parse_vcd(text: str) -> Waveform:
    wf = Waveform()
    scope: list[str] = []
    by_code: dict[str, list[str]] = {}
    tokens = iter(text.split())
    t = 0

    def until_end():
        out = []
        for tok in tokens:
            if tok == "$end":
                return out
            out.append(tok)
        raise VcdError("unterminated VCD section")

    def record(code: str, value: int, unk: bool):
        if code not in wf.times:
            return
        ts, vs, us = wf.times[code], wf.values[code], wf.unknown[code]
        if ts and ts[-1] == t:
            vs[-1], us[-1] = value, unk
        else:
            ts.append(t)
            vs.append(value)
            us.append(unk)

    for tok in tokens:
        if tok == "$timescale":
            wf.timescale = "".join(until_end())
        elif tok == "$scope":
            body = until_end()
            scope.append(body[1] if len(body) > 1 else body[0])
        elif tok == "$upscope":
            until_end()
            scope.pop()
        elif tok == "$var":
            body = until_end()
            kind, width, code, ref = body[0], int(body[1]), body[2], body[3]
            name = ".".join(scope + [ref])
            wf.vars[name] = VcdVar(code, name, width, kind)
            by_code.setdefault(code, []).append(name)
            wf.times.setdefault(code, [])
            wf.values.setdefault(code, [])
            wf.unknown.setdefault(code, [])
        elif tok in ("$date", "$version", "$comment", "$enddefinitions", "$dumpvars", "$dumpall", "$dumpon", "$dumpoff"):
            if tok in ("$dumpvars", "$dumpall", "$dumpon", "$dumpoff"):
                continue
            until_end()
        elif tok == "$end":
            continue
        elif tok.startswith("#"):
            t = int(tok[1:])
            wf.end_time = max(wf.end_time, t)
        elif tok[0] in "bB":
            code = next(tokens)
            v, u = _parse_value(tok[1:])
            record(code, v, u)
        elif tok[0] in "rR":
            code = next(tokens)
            record(code, int(float(tok[1:])), False)
        elif tok[0] in "01xXzZuU-":
            v, u = _parse_value(tok[0])
            record(tok[1:], v, u)
    return wf


def load_waveform(path: str | Path) -> Waveform:
    p = Path(path)
    if p.suffix.lower() == ".fst":
        tool = shutil.which("fst2vcd")
        if tool is None:
            raise VcdError("FST input requires 'fst2vcd' (GTKWave) on PATH")
        with tempfile.TemporaryDirectory() as td:
            out = Path(td) / "trace.vcd"
            subprocess.run([tool, "-f", str(p), "-o", str(out)], check=True, capture_output=True)
            return parse_vcd(out.read_text())
    return parse_vcd(p.read_text())


def write_vcd(path: str | Path, scope: str, signals: dict[str, int], cycles: list[dict[str, int]], clock: str = "clk",
              period: int = 10, timescale: str = "1ns") -> None:
    codes = {}
    alphabet = [chr(c) for c in range(33, 127)]
    for i, name in enumerate([clock] + [s for s in signals if s != clock]):
        a, b = divmod(i, len(alphabet))
        codes[name] = (alphabet[a - 1] if a else "") + alphabet[b]
    widths = dict(signals)
    widths[clock] = 1
    lines = [f"$timescale {timescale} $end", f"$scope module {scope} $end"]
    for name, code in codes.items():
        lines.append(f"$var wire {widths[name]} {code} {name} $end")
    lines += ["$upscope $end", "$enddefinitions $end"]

    def emit(name, v):
        if widths[name] == 1:
            return f"{v & 1}{codes[name]}"
        return f"b{v:b} {codes[name]}"

    prev: dict[str, int] = {}
    half = period // 2
    for k, cyc in enumerate(cycles):
        lines.append(f"#{k * period}")
        lines.append(emit(clock, 0))
        for name in signals:
            if name == clock:
                continue
            v = cyc.get(name, 0)
            if prev.get(name) != v:
                lines.append(emit(name, v))
                prev[name] = v
        lines.append(f"#{k * period + half}")
        lines.append(emit(clock, 1))
    lines.append(f"#{len(cycles) * period}")
    lines.append(emit(clock, 0))
    Path(path).write_text("\n".join(lines) + "\n")
