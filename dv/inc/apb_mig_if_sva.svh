// START sequence
  sequence idle_phase;
    !psel;
  endsequence

  sequence setup_phase;
    psel && !penable;
  endsequence

  sequence access_phase;
    psel && penable;
  endsequence

  sequence handshake;
    psel && penable && pready;
  endsequence
// END sequence

// START X Check
  sva_apb_x_check_preset_n : assert property (
    @(posedge pclk)
    !$isunknown(preset_n)
  ) else begin
    $error("preset_n isunknown");
  end

  sva_apb_x_check_psel : assert property (
    @(posedge pclk) disable iff (!preset_n)
    !$isunknown(psel)
  ) else begin
    $error("psel isunknown");
  end

// START psel check

  sva_apb_x_check_paddr : assert property (
    @(posedge pclk) disable iff (!preset_n)
    psel |-> !$isunknown(paddr)
  ) else begin
    $error("paddr isunknown when psel");
  end

  sva_apb_x_check_pwdata : assert property (
    @(posedge pclk) disable iff (!preset_n)
    psel |-> !$isunknown(pwdata & pstrb)
  ) else begin
    $error("pwdata isunknown when psel");
  end

  sva_apb_x_check_pwrite : assert property (
    @(posedge pclk) disable iff (!preset_n)
    psel |-> !$isunknown(pwrite)
  ) else begin
    $error("pwrite isunknown when psel");
  end

  sva_apb_x_check_pstrb : assert property (
    @(posedge pclk) disable iff (!preset_n)
    psel |-> !$isunknown(pstrb)
  ) else begin
    $error("pstrb isunknown when psel");
  end

  sva_apb_x_check_penable : assert property (
    @(posedge pclk) disable iff (!preset_n)
    psel |-> !$isunknown(penable)
  ) else begin
    $error("penable isunknown when psel");
  end

// END psel check

// START access check

  sva_apb_x_check_pready : assert property (
    @(posedge pclk) disable iff (!preset_n)
    access_phase |-> !$isunknown(pready)
  ) else begin
    $error("pready isunknown when access_phase");
  end

// END access check

// START handshake check

  sva_apb_x_check_prdata : assert property (
    @(posedge pclk) disable iff (!preset_n)
    (handshake && !pwrite) |-> !$isunknown(prdata)
  ) else begin
    $error("prdata isunknown when handshake && !pwrite");
  end

  sva_apb_x_check_pslverr : assert property (
    @(posedge pclk) disable iff (!preset_n)
    handshake |-> !$isunknown( pslverr_o )
  ) else begin
    $error("pslverr isunknown when handshake");
  end

// END handshake check

// END X Check

// START Behavioral

  sva_apb_behav_psel_pen_sim : assert property (
    @(posedge pclk) disable iff (!preset_n)
    $rose(psel) |-> !penable
  ) else begin
    $error("penable is simultaneous with psel");
  end

  sva_apb_behav_pen_after_psel : assert property (
    @(posedge pclk) disable iff (!preset_n)
    $rose(psel) |-> ##1 penable
  ) else begin
    $error("no penable after psel");
  end

  sva_apb_behav_pen_after_psel_btb : assert property (
    @(posedge pclk) disable iff (!preset_n)
    $fell(pready) && psel |-> ##1 penable
  ) else begin
    $error("no penable after psel in a back-to-back transaction");
  end

  sva_apb_behav_pen_after_hand : assert property (
    @(posedge pclk) disable iff (!preset_n)
    handshake |-> ##1 $fell(penable)
  ) else begin
    $error("penable after handshake");
  end

  sva_apb_behav_pen_on_hand : assert property (
    @(posedge pclk) disable iff (!preset_n)
    $fell(penable) |-> $past(handshake)
  ) else begin
    $error("penable fell not after handshake");
  end

  sva_apb_behav_ustable_paddr : assert property (
    @(posedge pclk) disable iff (!preset_n)
    access_phase |-> $stable(paddr)
  ) else begin
    $error("unstable paddr during access phase");
  end

  sva_apb_behav_ustable_pwrite : assert property (
    @(posedge pclk) disable iff (!preset_n)
    access_phase |-> $stable(pwrite)
  ) else begin
    $error("unstable pwrite during access phase");
  end

  sva_apb_behav_ustable_pstrb : assert property (
    @(posedge pclk) disable iff (!preset_n)
    access_phase && pwrite |-> $stable(pstrb)
  ) else begin
    $error("unstable pstrb during write access phase");
  end

  sva_apb_behav_ustable_pwdata : assert property (
    @(posedge pclk) disable iff (!preset_n)
    access_phase && pwrite |-> $stable(pwdata)
  ) else begin
    $error("unstable pwdata during write access phase");
  end

  sva_apb_behav_ustable_psel : assert property (
    @(posedge pclk) disable iff (!preset_n)
    psel && !pready |-> ##1 psel
  ) else begin
    $error("unstable psel");
  end

  sva_apb_behav_ustable_penable : assert property (
    @(posedge pclk) disable iff (!preset_n)
    penable && !pready |-> ##1 penable
  ) else begin
    $error("unstable penable");
  end

  sva_apb_behav_one_cyc_hand : assert property (
    @(posedge pclk) disable iff (!preset_n)
    handshake |-> ##1 !handshake
  ) else begin
    $error("handshake lasts longer than 1 clock cycle");
  end

  sva_apb_behav_err_hand : assert property (
    @(posedge pclk) disable iff (!preset_n)
    pslverr |-> handshake
  ) else begin
    $info("pslverr_o when not handshake");
  end

// START fsm state transitions

  sva_apb_behav_setup : assert property (
    @(posedge pclk) disable iff (!preset_n)
    setup_phase |-> ##1 access_phase
  ) else begin
    $error("invalid transition from setup_phase");
  end

  sva_apb_behav_access : assert property (
    @(posedge pclk) disable iff (!preset_n)
    access_phase |-> ##1 access_phase or setup_phase or idle_phase
  ) else begin
    $error("invalid transition from access_phase");
  end

  sva_apb_behav_idle : assert property (
    @(posedge pclk) disable iff (!preset_n)
    idle_phase |-> ##1 idle_phase or setup_phase
  ) else begin
    $error("invalid transition from idle_phase");
  end

// END fsm state transitions

  sva_apb_behav_read_pstrb : assert property (
    @(posedge pclk) disable iff (!preset_n)
    access_phase && !pwrite |-> ~|pstrb
  ) else begin
    $error("active pstrb during read transaction");
  end

  initial begin
    sva_apb_behav_bits_prdata_pwdata :  assert($bits(prdata) == $bits(pwdata))
                                    else $error("$bits(prdata) != $bits(pwdata)");
    sva_apb_behav_bits_pwdata_pstrb :   assert($bits(prdata) / 8. == $real'($bits(pstrb)))
                                    else $error("$bits(prdata) / 8 != $bits(pstrb)");
  end

  sva_apb_behav_reset_control : assert property (
    @(posedge clk)
    !preset_n |-> {psel, penable} == '0
  ) else begin
    $error("while !preset_n not all control == '0");
  end

  sva_apb_behav_control_first_cyc : assert property (
    @(posedge clk)
    !arst_n ##1 arst_n |-> {psel, penable} == '0
  ) else begin
    $error("control is not 0 for the first cycle after reset");
  end

// END Behavioral
