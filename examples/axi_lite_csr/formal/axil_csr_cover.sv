module axil_csr_cover (
  input logic        clk,
  input logic        rst_n,
  input logic        irq,
  input logic [31:0] irq_en,
  input logic        s_axi_bvalid,
  input logic [1:0]  s_axi_bresp,
  input logic        s_axi_rvalid,
  input logic [1:0]  s_axi_rresp,
  input logic        dma_busy,
  input logic [12:0] dma_cnt
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  c_irq_without_enable: cover property (irq && irq_en == '0);
  c_bresp_exokay:       cover property (s_axi_bvalid && s_axi_bresp == 2'b01);
  c_rresp_decerr:       cover property (s_axi_rvalid && s_axi_rresp == 2'b11);
  c_dma_overrun:        cover property (dma_busy && dma_cnt > 13'h800);
endmodule

bind axil_csr axil_csr_cover u_cov (.*);
