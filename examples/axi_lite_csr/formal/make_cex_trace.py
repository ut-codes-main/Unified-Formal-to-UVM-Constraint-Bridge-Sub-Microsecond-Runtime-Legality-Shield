from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))

from fbridge.cex.vcd import write_vcd  # noqa: E402

A_CTRL, A_STATUS, A_IRQ_EN, A_IRQ_STAT, A_SCRATCH0, A_SCRATCH1 = 0x00, 0x04, 0x08, 0x0C, 0x10, 0x14
A_DMA_SRC, A_DMA_DST, A_DMA_LEN, A_DMA_GO, A_LOCK = 0x20, 0x24, 0x28, 0x2C, 0x80
M32 = 0xFFFFFFFF

SIGNALS = {
    "rst_n": 1, "s_axi_awvalid": 1, "s_axi_awready": 1, "s_axi_awaddr": 32, "s_axi_awprot": 3, "s_axi_wvalid": 1,
    "s_axi_wready": 1, "s_axi_wdata": 32, "s_axi_wstrb": 4, "s_axi_bvalid": 1, "s_axi_bready": 1, "s_axi_bresp": 2,
    "s_axi_arvalid": 1, "s_axi_arready": 1, "s_axi_araddr": 32, "s_axi_arprot": 3, "s_axi_rvalid": 1, "s_axi_rready": 1,
    "s_axi_rdata": 32, "s_axi_rresp": 2, "irq": 1, "ctrl": 32, "irq_en": 32, "irq_stat": 32, "scratch0": 32,
    "scratch1": 32, "dma_src": 32, "dma_dst": 32, "dma_len": 12, "dma_cnt": 13, "dma_busy": 1, "locked": 1,
    "aw_hs": 1, "w_hs": 1, "ar_hs": 1, "waddr": 8, "raddr": 8, "wr_reserved": 1, "rd_reserved": 1,
}


def apply_strb(old: int, d: int, s: int) -> int:
    out = 0
    for i in range(4):
        src = d if (s >> i) & 1 else old
        out |= ((src >> (8 * i)) & 0xFF) << (8 * i)
    return out


class AxilCsrModel:
    def __init__(self):
        self.r = {k: 0 for k in ("ctrl", "irq_en", "irq_stat", "scratch0", "scratch1", "dma_src", "dma_dst", "dma_len",
                                 "dma_cnt", "dma_busy", "locked", "s_axi_bvalid", "s_axi_bresp", "s_axi_rvalid", "s_axi_rdata", "s_axi_rresp")}

    def comb(self, i: dict) -> dict:
        r = self.r
        c = dict(i)
        c.update(r)
        c["s_axi_awready"] = int(not r["s_axi_bvalid"] and i["s_axi_awvalid"] and i["s_axi_wvalid"])
        c["s_axi_wready"] = c["s_axi_awready"]
        c["s_axi_arready"] = int(not r["s_axi_rvalid"])
        c["irq"] = int((r["irq_en"] & r["irq_stat"]) != 0)
        c["aw_hs"] = int(i["s_axi_awvalid"] and c["s_axi_awready"])
        c["w_hs"] = int(i["s_axi_wvalid"] and c["s_axi_wready"])
        c["ar_hs"] = int(i["s_axi_arvalid"] and c["s_axi_arready"])
        c["waddr"] = i["s_axi_awaddr"] & 0xFF
        c["raddr"] = i["s_axi_araddr"] & 0xFF
        c["wr_reserved"] = int(0x40 <= c["waddr"] <= 0x7C or (i["s_axi_awaddr"] >> 8) != 0)
        c["rd_reserved"] = int(0x40 <= c["raddr"] <= 0x7C or (i["s_axi_araddr"] >> 8) != 0)
        return c

    def clock(self, c: dict) -> None:
        r, n = self.r, dict(self.r)
        if not c["rst_n"]:
            for k in n:
                n[k] = 0
            self.r = n
            return
        if r["s_axi_bvalid"] and c["s_axi_bready"]:
            n["s_axi_bvalid"] = 0
        if r["dma_busy"]:
            n["dma_cnt"] = (r["dma_cnt"] - 4) & 0x1FFF
            if r["dma_cnt"] <= 4:
                n["dma_busy"] = 0
                n["irq_stat"] = r["irq_stat"] | 1
        if c["aw_hs"] and c["w_hs"]:
            blocked = c["wr_reserved"] or (r["locked"] and c["waddr"] != A_LOCK)
            n["s_axi_bvalid"] = 1
            n["s_axi_bresp"] = 2 if blocked else 0
            if not blocked:
                wa, d, s = c["waddr"], c["s_axi_wdata"], c["s_axi_wstrb"]
                regs = {A_CTRL: "ctrl", A_IRQ_EN: "irq_en", A_SCRATCH0: "scratch0", A_SCRATCH1: "scratch1",
                        A_DMA_SRC: "dma_src", A_DMA_DST: "dma_dst"}
                if wa in regs:
                    n[regs[wa]] = apply_strb(r[regs[wa]], d, s)
                elif wa == A_IRQ_STAT:
                    n["irq_stat"] = r["irq_stat"] & ~apply_strb(0, d, s) & M32
                elif wa == A_DMA_LEN:
                    n["dma_len"] = d & 0xFFF
                elif wa == A_DMA_GO:
                    if r["ctrl"] & 1 and not r["dma_busy"] and d & 1:
                        n["dma_busy"] = 1
                        n["dma_cnt"] = r["dma_len"]
                elif wa == A_LOCK:
                    n["locked"] = d & 1
        if r["s_axi_rvalid"] and c["s_axi_rready"]:
            n["s_axi_rvalid"] = 0
        if c["ar_hs"]:
            n["s_axi_rvalid"] = 1
            n["s_axi_rresp"] = 2 if c["rd_reserved"] else 0
            ra = c["raddr"]
            table = {A_CTRL: r["ctrl"], A_STATUS: (r["locked"] << 2) | (c["irq"] << 1) | r["dma_busy"], A_IRQ_EN: r["irq_en"],
                     A_IRQ_STAT: r["irq_stat"], A_SCRATCH0: r["scratch0"], A_SCRATCH1: r["scratch1"], A_DMA_SRC: r["dma_src"],
                     A_DMA_DST: r["dma_dst"], A_DMA_LEN: r["dma_len"], A_LOCK: r["locked"]}
            n["s_axi_rdata"] = table.get(ra, 0xDEADBEEF)
        self.r = n


IDLE = {"rst_n": 1, "s_axi_awvalid": 0, "s_axi_awaddr": 0, "s_axi_awprot": 0, "s_axi_wvalid": 0, "s_axi_wdata": 0,
        "s_axi_wstrb": 0, "s_axi_bready": 1, "s_axi_arvalid": 0, "s_axi_araddr": 0, "s_axi_arprot": 0, "s_axi_rready": 1}


def scenario() -> list[dict]:
    steps = [dict(IDLE, rst_n=0), dict(IDLE, rst_n=0), dict(IDLE)]

    def write(addr, data, strb=0xF, prot=0):
        return dict(IDLE, s_axi_awvalid=1, s_axi_awaddr=addr, s_axi_awprot=prot, s_axi_wvalid=1, s_axi_wdata=data, s_axi_wstrb=strb)

    def read(addr):
        return dict(IDLE, s_axi_arvalid=1, s_axi_araddr=addr)

    steps += [write(A_SCRATCH0, 0x0000CAFE), dict(IDLE), write(A_CTRL, 0x00000001), dict(IDLE), read(A_STATUS),
              dict(IDLE), write(A_DMA_LEN, 0xA5A5A900, strb=0x3), dict(IDLE), dict(IDLE),
              write(A_DMA_GO, 0x00000001), dict(IDLE), dict(IDLE)]
    return steps


def simulate(steps: list[dict]) -> list[dict]:
    m = AxilCsrModel()
    out = []
    for i in steps:
        c = m.comb(i)
        out.append(c)
        m.clock(c)
    return out


def main() -> None:
    cycles = simulate(scenario())
    out = Path(__file__).with_name("cex_dma_len.vcd")
    write_vcd(out, "axil_csr", SIGNALS, cycles)
    print(f"wrote {out} ({len(cycles)} cycles)")


if __name__ == "__main__":
    main()
