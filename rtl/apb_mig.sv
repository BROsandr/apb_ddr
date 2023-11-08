module apb_mig (
  apb_if.slave apb_if,
  mig_if.apb   mig_if
);

  import apb_mig_pkg::*;

  typedef struct {
    data_t     data;
    strb_t     strb;
    mig_addr_t addr;
    logic      write;
  } apb2mig_data_t;

  typedef struct {
    logic          w_full;
    logic          r_empty;
    logic          w_en;
    logic          r_en;
    apb2mig_data_t r_data;
    apb2mig_data_t w_data;
  } apb2mig_fifo_t;
  apb2mig_fifo_t apb2mig_fifo_ports;

  async_fifo #(
    .data_t (apb2mig_data_t),
    .DEPTH  (1)
  ) apb2mig_fifo (
    .clk_r_i   (mig_if            .ui_clk_i),
    .clk_w_i   (apb_if            .pclk_i),
    .rst_r_ni  (mig_if            .ui_reset_ni),
    .rst_w_ni  (apb_if            .preset_ni),
    .w_data_i  (apb2mig_fifo_ports.w_data),
    .w_en_i    (apb2mig_fifo_ports.w_en),
    .r_en_i    (apb2mig_fifo_ports.r_en),
    .r_data_o  (apb2mig_fifo_ports.r_data),
    .w_full_o  (apb2mig_fifo_ports.w_full),
    .r_empty_o (apb2mig_fifo_ports.r_empty)
  );

  logic  is_access_phase;
  assign is_access_phase = apb_if.psel_i && apb_if.penable_i;

  assign apb2mig_fifo_ports.r_en         =  ((mig_if.w_ready_i & apb2mig_fifo_ports.r_data.write) |
                                             !apb2mig_fifo_ports.r_data.write)                  &
                                            (mig_if.ready_i & !apb2mig_fifo_ports.r_empty);
  assign apb2mig_fifo_ports.w_en         = is_access_phase && !apb2mig_fifo_ports.w_full && apb_if.pwrite_i;
  assign apb2mig_fifo_ports.w_data.data  = apb_if.pwdata_i;
  assign apb2mig_fifo_ports.w_data.strb  = apb_if.pstrb_i;
  assign apb2mig_fifo_ports.w_data.addr  = mig_addr_t'(apb_if.paddr_i);
  assign apb2mig_fifo_ports.w_data.write = apb_if.pwrite_i;

  typedef struct {
    logic  w_full;
    logic  r_empty;
    logic  w_en;
    logic  r_en;
    data_t r_data;
    data_t w_data;
  } mig2apb_fifo_t;
  mig2apb_fifo_t mig2apb_fifo_ports;

  async_fifo #(
    .data_t (data_t),
    .DEPTH  (1)
  ) mig2apb_fifo (
    .clk_r_i   (mig_if            .ui_clk_i),
    .clk_w_i   (apb_if            .pclk_i),
    .rst_r_ni  (mig_if            .ui_reset_ni),
    .rst_w_ni  (apb_if            .preset_ni),
    .w_data_i  (mig2apb_fifo_ports.w_data),
    .w_en_i    (mig2apb_fifo_ports.w_en),
    .r_en_i    (mig2apb_fifo_ports.r_en),
    .r_data_o  (mig2apb_fifo_ports.r_data),
    .w_full_o  (mig2apb_fifo_ports.w_full),
    .r_empty_o (mig2apb_fifo_ports.r_empty)
  );

  assign mig2apb_fifo_ports.r_en   = !mig2apb_fifo_ports.r_empty;
  assign mig2apb_fifo_ports.w_en   = mig_if.valid_i;
  assign mig2apb_fifo_ports.w_data = mig_if.data_i;

  assign mig_if.en_o   = apb2mig_fifo_ports.r_en;
  assign mig_if.w_en_o = mig_if.en_o && apb2mig_fifo_ports.r_data.write;
  assign mig_if.data_o = apb2mig_fifo_ports.r_data.data;
  assign mig_if.strb_o = apb2mig_fifo_ports.r_data.strb;
  assign mig_if.addr_o = apb2mig_fifo_ports.r_data.addr;

  assign apb_if.pready_o  = (mig2apb_fifo_ports.w_en && apb2mig_fifo_ports.w_data.write) ||
                                mig2apb_fifo_ports.r_en;
  assign apb_if.prdata_o  = mig2apb_fifo_ports.r_data;
  assign apb_if.pslverr_o = 1'b0;


endmodule
