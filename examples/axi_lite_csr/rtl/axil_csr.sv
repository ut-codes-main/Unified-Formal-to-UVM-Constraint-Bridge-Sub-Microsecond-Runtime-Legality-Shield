module axil_csr #(
  parameter int AW = 32,
  parameter int DW = 32
) (
  input  logic          clk,
  input  logic          rst_n,
  input  logic          s_axi_awvalid,
  output logic          s_axi_awready,
  input  logic [AW-1:0] s_axi_awaddr,
  input  logic [2:0]    s_axi_awprot,
  input  logic          s_axi_wvalid,
  output logic          s_axi_wready,
  input  logic [DW-1:0] s_axi_wdata,
  input  logic [3:0]    s_axi_wstrb,
  output logic          s_axi_bvalid,
  input  logic          s_axi_bready,
  output logic [1:0]    s_axi_bresp,
  input  logic          s_axi_arvalid,
  output logic          s_axi_arready,
  input  logic [AW-1:0] s_axi_araddr,
  input  logic [2:0]    s_axi_arprot,
  output logic          s_axi_rvalid,
  input  logic          s_axi_rready,
  output logic [DW-1:0] s_axi_rdata,
  output logic [1:0]    s_axi_rresp,
  output logic          irq
);
  localparam logic [7:0] A_CTRL     = 8'h00;
  localparam logic [7:0] A_STATUS   = 8'h04;
  localparam logic [7:0] A_IRQ_EN   = 8'h08;
  localparam logic [7:0] A_IRQ_STAT = 8'h0C;
  localparam logic [7:0] A_SCRATCH0 = 8'h10;
  localparam logic [7:0] A_SCRATCH1 = 8'h14;
  localparam logic [7:0] A_DMA_SRC  = 8'h20;
  localparam logic [7:0] A_DMA_DST  = 8'h24;
  localparam logic [7:0] A_DMA_LEN  = 8'h28;
  localparam logic [7:0] A_DMA_GO   = 8'h2C;
  localparam logic [7:0] A_LOCK     = 8'h80;
  localparam logic [11:0] DMA_MAX   = 12'h800;

  logic [31:0] ctrl, irq_en, irq_stat, scratch0, scratch1, dma_src, dma_dst;
  logic [11:0] dma_len;
  logic [12:0] dma_cnt;
  logic        dma_busy, locked;

  wire aw_hs = s_axi_awvalid && s_axi_awready;
  wire w_hs  = s_axi_wvalid && s_axi_wready;
  wire ar_hs = s_axi_arvalid && s_axi_arready;
  wire [7:0] waddr = s_axi_awaddr[7:0];
  wire [7:0] raddr = s_axi_araddr[7:0];
  wire wr_reserved = (waddr >= 8'h40 && waddr <= 8'h7C) || s_axi_awaddr[AW-1:8] != '0;
  wire rd_reserved = (raddr >= 8'h40 && raddr <= 8'h7C) || s_axi_araddr[AW-1:8] != '0;

  function automatic logic [31:0] apply_strb(input logic [31:0] old, input logic [31:0] d, input logic [3:0] s);
    for (int i = 0; i < 4; i++) apply_strb[i*8 +: 8] = s[i] ? d[i*8 +: 8] : old[i*8 +: 8];
  endfunction

  assign s_axi_awready = !s_axi_bvalid && s_axi_awvalid && s_axi_wvalid;
  assign s_axi_wready  = s_axi_awready;
  assign s_axi_arready = !s_axi_rvalid;
  assign irq = |(irq_en & irq_stat);

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      ctrl <= '0; irq_en <= '0; irq_stat <= '0; scratch0 <= '0; scratch1 <= '0;
      dma_src <= '0; dma_dst <= '0; dma_len <= '0; dma_cnt <= '0; dma_busy <= 1'b0; locked <= 1'b0;
      s_axi_bvalid <= 1'b0; s_axi_bresp <= 2'b00;
    end else begin
      if (s_axi_bvalid && s_axi_bready) s_axi_bvalid <= 1'b0;
      if (dma_busy) begin
        dma_cnt <= dma_cnt - 13'd4;
        if (dma_cnt <= 13'd4) begin
          dma_busy <= 1'b0;
          irq_stat[0] <= 1'b1;
        end
      end
      if (aw_hs && w_hs) begin
        s_axi_bvalid <= 1'b1;
        s_axi_bresp  <= (wr_reserved || (locked && waddr != A_LOCK)) ? 2'b10 : 2'b00;
        if (!wr_reserved && !(locked && waddr != A_LOCK)) begin
          unique case (waddr)
            A_CTRL:     ctrl <= apply_strb(ctrl, s_axi_wdata, s_axi_wstrb);
            A_IRQ_EN:   irq_en <= apply_strb(irq_en, s_axi_wdata, s_axi_wstrb);
            A_IRQ_STAT: irq_stat <= irq_stat & ~apply_strb('0, s_axi_wdata, s_axi_wstrb);
            A_SCRATCH0: scratch0 <= apply_strb(scratch0, s_axi_wdata, s_axi_wstrb);
            A_SCRATCH1: scratch1 <= apply_strb(scratch1, s_axi_wdata, s_axi_wstrb);
            A_DMA_SRC:  dma_src <= apply_strb(dma_src, s_axi_wdata, s_axi_wstrb);
            A_DMA_DST:  dma_dst <= apply_strb(dma_dst, s_axi_wdata, s_axi_wstrb);
            A_DMA_LEN:  dma_len <= s_axi_wdata[11:0];
            A_DMA_GO:   if (ctrl[0] && !dma_busy && s_axi_wdata[0]) begin
                          dma_busy <= 1'b1;
                          dma_cnt  <= {1'b0, dma_len};
                        end
            A_LOCK:     locked <= s_axi_wdata[0];
            default: ;
          endcase
        end
      end
    end
  end

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      s_axi_rvalid <= 1'b0; s_axi_rdata <= '0; s_axi_rresp <= 2'b00;
    end else begin
      if (s_axi_rvalid && s_axi_rready) s_axi_rvalid <= 1'b0;
      if (ar_hs) begin
        s_axi_rvalid <= 1'b1;
        s_axi_rresp  <= rd_reserved ? 2'b10 : 2'b00;
        unique case (raddr)
          A_CTRL:     s_axi_rdata <= ctrl;
          A_STATUS:   s_axi_rdata <= {29'd0, locked, irq, dma_busy};
          A_IRQ_EN:   s_axi_rdata <= irq_en;
          A_IRQ_STAT: s_axi_rdata <= irq_stat;
          A_SCRATCH0: s_axi_rdata <= scratch0;
          A_SCRATCH1: s_axi_rdata <= scratch1;
          A_DMA_SRC:  s_axi_rdata <= dma_src;
          A_DMA_DST:  s_axi_rdata <= dma_dst;
          A_DMA_LEN:  s_axi_rdata <= {20'd0, dma_len};
          A_LOCK:     s_axi_rdata <= {31'd0, locked};
          default:    s_axi_rdata <= 32'hDEAD_BEEF;
        endcase
      end
    end
  end

`ifdef FORMAL
  ap_dma_len_bound: assert property (@(posedge clk) disable iff (!rst_n) dma_busy |-> dma_cnt <= {1'b0, DMA_MAX});
  ap_no_slverr_legal: assert property (@(posedge clk) disable iff (!rst_n)
    aw_hs && w_hs && !wr_reserved && !locked |=> s_axi_bresp == 2'b00);
`endif
endmodule
