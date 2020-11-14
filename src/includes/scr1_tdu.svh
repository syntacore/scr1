/// Copyright by Syntacore LLC © 2016-2020. See LICENSE for details
/// @file       <scr1_tdu.svh>
/// @brief      Trigger Debug Module header
///

`ifndef SCR1_INCLUDE_TDU_DEFS
`define SCR1_INCLUDE_TDU_DEFS

//`include "scr1_arch_description.svh"

`ifdef SCR1_TDU_EN
//`include "scr1_csr.svh"

`include "scr1_arch_description.svh"
//`include "scr1_arch_types.svh"
`include "scr1_csr.svh"

parameter int unsigned  SCR1_TDU_MTRIG_NUM             = SCR1_TDU_TRIG_NUM;
`ifdef SCR1_TDU_ICOUNT_EN
parameter int unsigned  SCR1_TDU_ALLTRIG_NUM           = SCR1_TDU_MTRIG_NUM + 1'b1;
`else
parameter int unsigned  SCR1_TDU_ALLTRIG_NUM           = SCR1_TDU_MTRIG_NUM;
`endif

parameter int unsigned  SCR1_TDU_ADDR_W                = `SCR1_XLEN;
parameter int unsigned  SCR1_TDU_DATA_W                = `SCR1_XLEN;

// Register map
parameter                                     SCR1_CSR_ADDR_TDU_OFFS_W        = 3;
parameter bit [SCR1_CSR_ADDR_TDU_OFFS_W-1:0]  SCR1_CSR_ADDR_TDU_OFFS_TSELECT  = 'h0;
parameter bit [SCR1_CSR_ADDR_TDU_OFFS_W-1:0]  SCR1_CSR_ADDR_TDU_OFFS_TDATA1   = 'h1;
parameter bit [SCR1_CSR_ADDR_TDU_OFFS_W-1:0]  SCR1_CSR_ADDR_TDU_OFFS_TDATA2   = 'h2;
parameter bit [SCR1_CSR_ADDR_TDU_OFFS_W-1:0]  SCR1_CSR_ADDR_TDU_OFFS_TINFO    = 'h4;


parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_TDU_TSELECT       = SCR1_CSR_ADDR_TDU_MBASE + SCR1_CSR_ADDR_TDU_OFFS_TSELECT;
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_TDU_TDATA1        = SCR1_CSR_ADDR_TDU_MBASE + SCR1_CSR_ADDR_TDU_OFFS_TDATA1;
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_TDU_TDATA2        = SCR1_CSR_ADDR_TDU_MBASE + SCR1_CSR_ADDR_TDU_OFFS_TDATA2;
parameter bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_CSR_ADDR_TDU_TINFO         = SCR1_CSR_ADDR_TDU_MBASE + SCR1_CSR_ADDR_TDU_OFFS_TINFO;

// TDATA1
parameter int unsigned  SCR1_TDU_TDATA1_TYPE_HI        = `SCR1_XLEN-1;
parameter int unsigned  SCR1_TDU_TDATA1_TYPE_LO        = `SCR1_XLEN-4;
parameter int unsigned  SCR1_TDU_TDATA1_DMODE          = `SCR1_XLEN-5;

// TDATA1: constant bits values
parameter bit           SCR1_TDU_TDATA1_DMODE_VAL      = 1'b0;

// MCONTROL: bits number
parameter int unsigned  SCR1_TDU_MCONTROL_MASKMAX_HI   = `SCR1_XLEN-6;
parameter int unsigned  SCR1_TDU_MCONTROL_MASKMAX_LO   = `SCR1_XLEN-11;
parameter int unsigned  SCR1_TDU_MCONTROL_RESERVEDB_HI = `SCR1_XLEN-12;
parameter int unsigned  SCR1_TDU_MCONTROL_RESERVEDB_LO = 21;
parameter int unsigned  SCR1_TDU_MCONTROL_HIT          = 20;
parameter int unsigned  SCR1_TDU_MCONTROL_SELECT       = 19;
parameter int unsigned  SCR1_TDU_MCONTROL_TIMING       = 18;
parameter int unsigned  SCR1_TDU_MCONTROL_ACTION_HI    = 17;
parameter int unsigned  SCR1_TDU_MCONTROL_ACTION_LO    = 12;
parameter int unsigned  SCR1_TDU_MCONTROL_CHAIN        = 11;
parameter int unsigned  SCR1_TDU_MCONTROL_MATCH_HI     = 10;
parameter int unsigned  SCR1_TDU_MCONTROL_MATCH_LO     = 7;
parameter int unsigned  SCR1_TDU_MCONTROL_M            = 6;
parameter int unsigned  SCR1_TDU_MCONTROL_RESERVEDA    = 5;
parameter int unsigned  SCR1_TDU_MCONTROL_S            = 4;
parameter int unsigned  SCR1_TDU_MCONTROL_U            = 3;
parameter int unsigned  SCR1_TDU_MCONTROL_EXECUTE      = 2;
parameter int unsigned  SCR1_TDU_MCONTROL_STORE        = 1;
parameter int unsigned  SCR1_TDU_MCONTROL_LOAD         = 0;

// MCONTROL: constant bits values
parameter bit [SCR1_TDU_TDATA1_TYPE_HI-SCR1_TDU_TDATA1_TYPE_LO:0]
                        SCR1_TDU_MCONTROL_TYPE_VAL           = 2'd2;

parameter bit           SCR1_TDU_MCONTROL_SELECT_VAL         = 1'b0;
parameter bit           SCR1_TDU_MCONTROL_TIMING_VAL         = 1'b0;

parameter bit [SCR1_TDU_MCONTROL_MASKMAX_HI-SCR1_TDU_MCONTROL_MASKMAX_LO:0]
                        SCR1_TDU_MCONTROL_MASKMAX_VAL        = 1'b0;

parameter bit           SCR1_TDU_MCONTROL_RESERVEDA_VAL      = 1'b0;

// ICOUNT: bits number
parameter int unsigned  SCR1_TDU_ICOUNT_DMODE          = `SCR1_XLEN-5;
parameter int unsigned  SCR1_TDU_ICOUNT_RESERVEDB_HI   = `SCR1_XLEN-6;
parameter int unsigned  SCR1_TDU_ICOUNT_RESERVEDB_LO   = 25;
parameter int unsigned  SCR1_TDU_ICOUNT_HIT            = 24;
parameter int unsigned  SCR1_TDU_ICOUNT_COUNT_HI       = 23;
parameter int unsigned  SCR1_TDU_ICOUNT_COUNT_LO       = 10;
parameter int unsigned  SCR1_TDU_ICOUNT_M              = 9;
parameter int unsigned  SCR1_TDU_ICOUNT_RESERVEDA      = 8;
parameter int unsigned  SCR1_TDU_ICOUNT_S              = 7;
parameter int unsigned  SCR1_TDU_ICOUNT_U              = 6;
parameter int unsigned  SCR1_TDU_ICOUNT_ACTION_HI      = 5;
parameter int unsigned  SCR1_TDU_ICOUNT_ACTION_LO      = 0;

// ICOUNT: constant bits values
parameter bit [SCR1_TDU_TDATA1_TYPE_HI-SCR1_TDU_TDATA1_TYPE_LO:0]
                        SCR1_TDU_ICOUNT_TYPE_VAL             = 2'd3;

parameter bit [SCR1_TDU_ICOUNT_RESERVEDB_HI-SCR1_TDU_ICOUNT_RESERVEDB_LO:0]
                        SCR1_TDU_ICOUNT_RESERVEDB_VAL        = 1'b0;

parameter bit           SCR1_TDU_ICOUNT_RESERVEDA_VAL        = 1'b0;

// CPU pipeline monitors
typedef struct packed {
    logic                                           vd;
    logic                                           req;
    logic [`SCR1_XLEN-1:0]                          addr;
} type_scr1_brkm_instr_mon_s;

typedef struct packed {
    logic                                           vd;
    logic                                           load;
    logic                                           store;
    logic [`SCR1_XLEN-1:0]                          addr;
} type_scr1_brkm_lsu_mon_s;

`endif // SCR1_TDU_EN

`endif // SCR1_INCLUDE_TDU_DEFS
