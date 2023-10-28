// START X Check
  sva_x_check_preset_n : assert property (
    @(posedge pclk)
    !$isunknown(preset_n)
  ) else begin
    $error("preset_n isunknown");
  end

  sva_x_check_psel : assert property (
    @(posedge pclk) disable iff (!preset_n)
    !$isunknown(psel)
  ) else begin
    $error("psel isunknown");
  end

// START psel check

  sva_x_check_paddr : assert property (
    @(posedge pclk) disable iff (!preset_n)
    psel |-> !$isunknown(paddr)
  ) else begin
    $error("paddr isunknown when psel");
  end

  sva_x_check_pwdata : assert property (
    @(posedge pclk) disable iff (!preset_n)
    psel |-> !$isunknown(pwdata & pstrb)
  ) else begin
    $error("pwdata isunknown when psel");
  end

  sva_x_check_pwrite : assert property (
    @(posedge pclk) disable iff (!preset_n)
    psel |-> !$isunknown(pwrite)
  ) else begin
    $error("pwrite isunknown when psel");
  end

  sva_x_check_pstrb : assert property (
    @(posedge pclk) disable iff (!preset_n)
    psel |-> !$isunknown(pstrb)
  ) else begin
    $error("pstrb isunknown when psel");
  end

  sva_x_check_penable : assert property (
    @(posedge pclk) disable iff (!preset_n)
    psel |-> !$isunknown(penable)
  ) else begin
    $error("penable isunknown when psel");
  end

// END psel check

// START access check

  sva_x_check_pready : assert property (
    @(posedge pclk) disable iff (!preset_n)
    is_access_phase |-> !$isunknown(pready)
  ) else begin
    $error("pready isunknown when access_phase");
  end

// END access check

// START handshake check

  sva_x_check_prdata : assert property (
    @(posedge pclk) disable iff (!preset_n)
    (handshake && !pwrite) |-> !$isunknown(prdata)
  ) else begin
    $error("prdata isunknown when handshake && !pwrite");
  end

  sva_x_check_pslverr : assert property (
    @(posedge pclk) disable iff (!preset_n)
    handshake |-> !$isunknown( pslverr_o )
  ) else begin
    $error("pslverr isunknown when handshake");
  end

// END handshake check

// END X Check

// START Behavioral

  sva_behav_psel_pen_sim : assert property (
    @(posedge pclk) disable iff (!preset_n)
    $rose(psel) |-> !penable
  ) else begin
    $error("penable is simultaneous with psel");
  end

  sva_behav_pen_after_psel : assert property (
    @(posedge pclk) disable iff (!preset_n)
    $rose(psel) |-> ##1 penable
  ) else begin
    $error("no penable after psel");
  end

  sva_behav_pen_after_psel_btb : assert property (
    @(posedge pclk) disable iff (!preset_n)
    $fell(pready) && psel |-> ##1 penable
  ) else begin
    $error("no penable after psel in a back-to-back transaction");
  end

  sva_behav_pen_after_hand : assert property (
    @(posedge pclk) disable iff (!preset_n)
    handshake |-> ##1 $fell(penable)
  ) else begin
    $error("penable after handshake");
  end

  sva_behav_ustable_paddr : assert property (
    @(posedge pclk) disable iff (!preset_n)
    is_access_phase |-> $stable(paddr)
  ) else begin
    $error("unstable paddr during access phase");
  end

  sva_behav_ustable_pwrite : assert property (
    @(posedge pclk) disable iff (!preset_n)
    is_access_phase |-> $stable(pwrite)
  ) else begin
    $error("unstable pwrite during access phase");
  end

  sva_behav_ustable_pstrb : assert property (
    @(posedge pclk) disable iff (!preset_n)
    is_access_phase && pwrite |-> $stable(pstrb)
  ) else begin
    $error("unstable pstrb during write access phase");
  end

  sva_behav_ustable_pwdata : assert property (
    @(posedge pclk) disable iff (!preset_n)
    is_access_phase && pwrite |-> $stable(pwdata)
  ) else begin
    $error("unstable pwdata during write access phase");
  end

  sva_behav_one_cyc_hand : assert property (
    @(posedge pclk) disable iff (!preset_n)
    $rose(handshake) |-> ##1 $fell(handshake)
  ) else begin
    $error("handshake lasts longer than 1 clock cycle");
  end

  sva_behav_err_hand : assert property (
    @(posedge pclk) disable iff (!preset_n)
    pslverr |-> handshake
  ) else begin
    $info("pslverr_o when not handshake");
  end

// END Behavioral
