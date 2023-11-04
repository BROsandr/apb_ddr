package apb_mig_pkg;
  parameter int unsigned             APB_ADDR_WIDTH = 32;
  typedef logic [APB_ADDR_WIDTH-1:0] apb_addr_t;

  parameter int unsigned             MIG_ADDR_WIDTH = 27;
  typedef logic [MIG_ADDR_WIDTH-1:0] mig_addr_t;

  parameter int unsigned DATA_WIDTH = 128;

  parameter int unsigned             STRB_WIDTH = DATA_WIDTH / $bits(byte);
  typedef logic [MIG_ADDR_WIDTH-1:0] strb_t;

  typedef logic [WSTRB_WIDTH-1:0][7:0] data_t;
endpackage
