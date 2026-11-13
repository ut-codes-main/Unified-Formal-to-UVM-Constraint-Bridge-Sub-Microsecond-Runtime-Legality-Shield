`include "uvm_macros.svh"
import uvm_pkg::*;

typedef enum bit [0:0] {AXIL_READ = 0, AXIL_WRITE = 1} axil_kind_e;

class axil_item extends uvm_sequence_item;
  localparam int unsigned CSR_SPAN = 32'h100;

  rand axil_kind_e  kind;
  rand bit [31:0]   addr;
  rand bit [31:0]   data;
  rand bit [3:0]    strb;
  rand bit [2:0]    prot;
  bit  [1:0]        resp;

  `uvm_object_utils_begin(axil_item)
    `uvm_field_enum(axil_kind_e, kind, UVM_ALL_ON)
    `uvm_field_int(addr, UVM_ALL_ON)
    `uvm_field_int(data, UVM_ALL_ON)
    `uvm_field_int(strb, UVM_ALL_ON)
    `uvm_field_int(prot, UVM_ALL_ON)
  `uvm_object_utils_end

  constraint c_align    { addr[1:0] == 2'b00; }
  constraint c_window   { addr < CSR_SPAN; }
  constraint c_reserved { !(addr inside {[32'h40:32'h7C]}); }
  constraint c_strb     { kind == AXIL_WRITE -> strb != 4'h0; }
  constraint c_prot     { prot[0] == 1'b0; }
  constraint c_full     { soft strb == 4'hF; }
  constraint c_rd_strb  { if (kind == AXIL_READ) { strb == 4'h0; data == 32'h0; } }
  constraint c_mix      { kind dist { AXIL_READ := 1, AXIL_WRITE := 2 }; solve kind before strb; }

  function new(string name = "axil_item");
    super.new(name);
  endfunction
endclass
