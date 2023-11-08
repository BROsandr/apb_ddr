interface mig_if (
  input logic sys_clk_i,
  input logic sys_reset_ni
);
  import apb_mig_pkg::*;

// START protocol signals
  logic      ui_clk;
  logic      ui_reset_n;
  data_t     apb2mig_data;
  data_t     mig2apb_data;
  strb_t     strb;
  mig_addr_t addr;
  logic      w_ready;
  logic      w_en;
  logic      en;
  logic      valid;
  logic      ready;
  logic      w_ready;
// START protocol signals

// START modports
  modport apb (
    input  .ui_clk_i    (ui_clk),
    input  .ui_reset_ni (ui_reset_n),
    input  .data_i      (mig2apb_data),
    input  .valid_i     (valid),
    input  .w_ready_i   (w_ready),
    input  .ready_i     (ready),
    output .w_en_o      (w_en),
    output .strb_o      (strb),
    output .addr_o      (addr),
    output .en_o        (en),
    output .data_o      (apb2mig_data)
  );

  modport mig (
    input  .sys_clk_i   (sys_clk_i),
    input  .sys_clk_ni  (sys_reset_ni),
    input  .w_en_i      (w_en),
    input  .strb_i      (strb),
    input  .addr_i      (addr),
    input  .en_i        (en),
    input  .data_i      (apb2mig_data),
    output .ui_clk_o    (ui_clk),
    output .ui_reset_no (ui_reset_n),
    output .data_o      (mig2apb_data),
    output .w_ready_o   (w_ready),
    output .valid_o     (valid),
    output .ready_o     (ready)
  );
// END modports

  `include "mig_if_sva.svh"
endinterface
