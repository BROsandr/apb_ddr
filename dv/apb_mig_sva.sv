module apb_mig_sva (
  input async_fifo_t mig2apb_fifo,
  mig_if.apb         mig_if,
  apb_if.slave       apb_if
);

  sva_mig2apb_fifo_r_empty : assert property (
    @(posedge apb_if.pclk_i) disable iff (!apb_if.preset_ni)
    !mig2apb_fifo.r_empty |-> is_access_phase && !apb_if.pwrite_i
  ) else begin
    $error("There is a data in mig2apb_fifo while apb is not in the read state.");
  end

  sva_mig_if_valid_i : assert property (
    @(posedge apb_if.pclk_i) disable iff (!apb_if.preset_ni)
    mig_if.valid_i |-> !mig2apb_fifo.w_full
  ) else begin
    $error("mig2apb_fifo is full while mig_if.valid_i. Do you need to increase the fifo's size?");
  end
endmodule
