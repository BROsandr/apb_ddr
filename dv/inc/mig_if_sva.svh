// START X Check
  sva_mig_x_ui_reset_n : assert property (
    @(posedge ui_clk)
    !$isunknown(ui_reset_n)
  ) else begin
    $error("ui_reset_n isunknown");
  end

  sva_mig_x_valid : assert property (
    @(posedge ui_clk) disable iff (!ui_reset_n)
    !$isunknown(valid)
  ) else begin
    $error("ui_reset_n isunknown");
  end

  sva_mig_x_en : assert property (
    @(posedge ui_clk) disable iff (!ui_reset_n)
    !$isunknown(en)
  ) else begin
    $error("en isunknown");
  end

  sva_mig_x_w_en : assert property (
    @(posedge ui_clk) disable iff (!ui_reset_n)
    !$isunknown(w_en)
  ) else begin
    $error("w_en isunknown");
  end

  sva_mig_x_w_ready : assert property (
    @(posedge ui_clk) disable iff (!ui_reset_n)
    !$isunknown(w_ready)
  ) else begin
    $error("w_ready isunknown");
  end

  sva_mig_x_ready : assert property (
    @(posedge ui_clk) disable iff (!ui_reset_n)
    !$isunknown(ready)
  ) else begin
    $error("ready isunknown");
  end

  sva_mig_x_apb2mig_data : assert property (
    @(posedge ui_clk) disable iff (!ui_reset_n)
    w_en |-> !$isunknown(apb2mig_data)
  ) else begin
    $error("apb2mig_data isunknown while w_en");
  end

  sva_mig_x_strb : assert property (
    @(posedge ui_clk) disable iff (!ui_reset_n)
    w_en |-> !$isunknown(strb)
  ) else begin
    $error("strb isunknown while w_en");
  end

  sva_mig_x_addr : assert property (
    @(posedge ui_clk) disable iff (!ui_reset_n)
    en |-> !$isunknown(addr)
  ) else begin
    $error("addr isunknown while en");
  end

  sva_mig_x_mig2apb_data : assert property (
    @(posedge ui_clk) disable iff (!ui_reset_n)
    valid |-> !$isunknown(mig2apb_data)
  ) else begin
    $error("mig2apb_data isunknown while valid");
  end
// END X Check

// START Behavioral
  sva_mig_behav_w_en : assert property (
    @(posedge ui_clk) disable iff (!ui_reset_n)
    w_en |-> en
  ) else begin
    $error("w_en and en are not simultaneous");
  end

  sequence read_req;
    !w_en && en;
  endsequence

  sva_mig_behav_read_req : assert property (
    @(posedge ui_clk) disable iff (!ui_reset_n)
    read_req |-> (!valid until read_req) && 0
  ) else begin
    $error("broken read sequence. No response between two read_req");
  end

  sva_mig_behav_valid : assert property (
    @(posedge ui_clk) disable iff (!ui_reset_n)
    valid |-> (!read_req until valid) && 0
  ) else begin
    $error("broken read sequence. No request between two valid");
  end
// END Behavioral
