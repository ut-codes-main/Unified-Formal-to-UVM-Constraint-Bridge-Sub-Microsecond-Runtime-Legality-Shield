module axil_env_assumes (
  input logic        clk,
  input logic        rst_n,
  input logic        s_axi_awvalid,
  input logic        s_axi_awready,
  input logic [31:0] s_axi_awaddr,
  input logic [2:0]  s_axi_awprot,
  input logic        s_axi_wvalid,
  input logic        s_axi_wready,
  input logic [31:0] s_axi_wdata,
  input logic [3:0]  s_axi_wstrb,
  input logic        s_axi_arvalid,
  input logic        s_axi_arready,
  input logic [31:0] s_axi_araddr,
  input logic [2:0]  s_axi_arprot
);
  localparam int unsigned CSR_SPAN = 32'h100;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  a_aw_align:    assume property (s_axi_awvalid |-> s_axi_awaddr[1:0] == 2'b00);
  a_ar_align:    assume property (s_axi_arvalid |-> s_axi_araddr[1:0] == 2'b00);
  a_aw_window:   assume property (s_axi_awvalid |-> s_axi_awaddr < CSR_SPAN);
  a_ar_window:   assume property (s_axi_arvalid |-> s_axi_araddr < CSR_SPAN);
  a_aw_reserved: assume property (s_axi_awvalid |-> !(s_axi_awaddr inside {[32'h40:32'h7C]}));
  a_w_strb:      assume property (s_axi_wvalid |-> s_axi_wstrb != 4'h0);
  a_aw_prot:     assume property (s_axi_awvalid |-> s_axi_awprot == 3'b000);
  a_no_lock_wr:  assume property (s_axi_awvalid |-> s_axi_awaddr != 32'h80);

  a_aw_stable:   assume property (s_axi_awvalid && !s_axi_awready |=> s_axi_awvalid && $stable(s_axi_awaddr));
  a_w_stable:    assume property (s_axi_wvalid && !s_axi_wready |=> s_axi_wvalid && $stable(s_axi_wdata));
  a_ar_stable:   assume property (s_axi_arvalid && !s_axi_arready |=> s_axi_arvalid && $stable(s_axi_araddr));
  a_aw_w_pair:   assume property (s_axi_awvalid |-> s_axi_wvalid);
endmodule
