timeunit      1ns;
timeprecision 1ps;

module tb_abp ();

  logic                   pclk;
  localparam int unsigned PCLK_PERIOD = 20;

  initial begin
    pclk <= 1'b0;
    forever #(PCLK_PERIOD/2) pclk <= ~pclk;
  end

  logic preset_n;

  apb_if apb_if (
    .pclk_i    (pclk),
    .preset_ni (preset_n)
  );

  logic  sys_clk;
  assign sys_clk = pclk;

  logic  sys_reset_n;
  assign sys_reset_n = preset_n;

  mig_if mig_if (
    .sys_clk_i    (sys_clk),
    .sys_reset_ni (sys_reset_n)
  );

  import apb_mig_pkg::*;

  data_t mem[mig_addr_t];

  assign mig_if.ui_clk       = sys_clk;
  assign mig_if.ui_reset_n   = sys_reset_n;
  assign mig_if.w_ready      = 1'b1;
  assign mig_if.ready        = 1'b1;

  initial begin : mig
    @(posedge mig_if.ui_clk);
    mig_if.valid <= 1'b0;
    if (mig_if.en) begin
      if (mig_if.w_en) begin
        foreach (mem[mig_if.addr][strb_idx]) begin
          if (mig_if.strb[strb_idx]) mem[mig_if.addr][strb_idx] <= mig_if.apb2mig_data[strb_idx];
        end
      end else begin
        mig_if.mig2apb_data <= mem[mig_if.addr];
        mig_if.valid        <= 1'b1;
      end
    end
  end

  apb_mig apb_mig (
    .apb_if,
    .mig_if
  );

  bind apb_mig : apb_mig apb_mig_sva apb_mig_sva_instance (
    .mig2apb_fifo_w_full  (apb_mig.mig2apb_fifo_ports.w_full),
    .mig2apb_fifo_r_empty (apb_mig.mig2apb_fifo_ports.r_empty),
    .*
  );

  typedef struct {
    data_t     data;
    strb_t     strb;
    apb_addr_t addr;
    logic      write;
    logic      pslverr;
  } packet_t;

  mailbox #(packet_t) seq2drv_mbx = new(1);

  `define _RESET          \
    apb_if.psel    <= '0; \
    apb_if.penable <= '0; \
    apb_if.paddr   <= '0; \
    apb_if.pwdata  <= '0; \
    apb_if.pstrb   <= '0; \
    apb_if.pwrite  <= '0;

  task driver(int unsigned min_delay = 0, int unsigned max_delay = 10);
    fork begin
      forever begin
        fork
          forever begin
            int delay;
            packet_t packet;
            wait(preset_n);
            delay = $urandom_range(min_delay, max_delay);
            seq2drv_mbx.get(packet);
            repeat (delay) @(posedge apb_if.pclk_i);

            apb_if.psel   <= 1'b1;
            apb_if.paddr  <= packet.addr;
            apb_if.pwdata <= packet.data;
            apb_if.pstrb  <= packet.strb;
            apb_if.pwrite <= packet.write;

            @(posedge apb_if.pclk_i)

            apb_if.penable <= 1'b1;

            while (!apb_if.pready) @(posedge apb_if.pclk_i);

            `_RESET;
          end
          @(negedge preset_n);
        join_any
        disable fork;
        `_RESET;
      end
    end join
  endtask

  `undef _RESET

  logic  handshake;
  assign handshake = apb_if.penable && apb_if.psel && apb_if.pready;

  packet_t measured_packets[$];

  task monitor();
    forever begin
      @(posedge apb_if.pclk_i);
      if (handshake && apb_if.pwrite) begin
        measured_packets.push_back(packet_t'{data: apb_if.prdata,
            pslverr: apb_if.pslverr, default: 'x});
      end
    end
  endtask

  int unsigned errors_count = 0;

  data_t reference_datas[$];

  event scb_done;

  task scoreboard();
    forever begin
      data_t   reference_data;
      packet_t measured_packet;

      wait(reference_datas .size());
      wait(measured_packets.size());

      reference_data  = reference_datas .pop_front();
      measured_packet = measured_packets.pop_front();

      if(measured_packet.pslverr) begin
        $error("pslverr == 1'b1. Expected pslverr == 1'b0");
        ++errors_count;
        $stop;
      end

      if(reference_data != measured_packet.data) begin
        $error("Data mismatch. reference_data == %x, measured_data == %x",
                reference_data, measured_packet.data);
        ++errors_count;
        $stop;
      end

      $display("PASS");

      ->scb_done;
    end
  endtask

  task env();
    fork
      driver();
      monitor();
      scoreboard();
    join_none
  endtask

  task direct_sequence();
    packet_t packet2driver;

    $display("START direct_sequence");

    packet2driver.data  = '1;
    packet2driver.strb  = '1;
    packet2driver.write = 1'b1;
    
    packet2driver.addr  = apb_addr_t'(1);

    seq2drv_mbx.put(packet2driver);

    reference_datas.push_back(packet2driver.data);

    packet2driver.write = 1'b0;
    packet2driver.data  = '0;
    packet2driver.strb  = '0;

    seq2drv_mbx.put(packet2driver);

    $display("FINISH direct_sequence");
  endtask

  task reset(int unsigned duration = 100);
    preset_n <= 1'b0;

    repeat (duration) @(posedge apb_if.pclk_i);

    preset_n <= 1'b1;
  endtask

  initial begin : test
    $display( "START test");

    env();
    reset();
    direct_sequence();

    wait(scb_done.triggered);

    $display( "FINISH test");

    $display("Number of errors: %d", errors_count);
    if (!errors_count) $display("SUCCESS!!!");
    $finish();
  end
endmodule
