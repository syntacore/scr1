`ifndef SCR1_INCLUDE_BRKM_DEFS
`define SCR1_INCLUDE_BRKM_DEFS
/// Copyright by Syntacore LLC © 2016-2018. See LICENSE for details
/// @file       <scr1_brkm.svh>
/// @brief      BRKM header file
///

`include "scr1_arch_description.svh"

`ifdef SCR1_BRKM_EN
`include "scr1_csr.svh"

 `define SCR1_BRKM_ARCH_SUPP_OPER_EXEC
 `define SCR1_BRKM_ARCH_SUPP_OPER_LOAD
 `define SCR1_BRKM_ARCH_SUPP_OPER_STORE
 `define SCR1_BRKM_ARCH_SUPP_ADDR_EXACT
 //`define SCR1_BRKM_ARCH_SUPP_ADDR_RANGE
 //`define SCR1_BRKM_ARCH_SUPP_ADDR_RANGE_EXT_EXEC
 //`define SCR1_BRKM_ARCH_SUPP_ADDR_RANGE_EXT_LDST
 `define SCR1_BRKM_ARCH_SUPP_ADDR_MASK
 `define SCR1_BRKM_ARCH_SUPP_ADDR_MASK_EXT_EXEC
 `define SCR1_BRKM_ARCH_SUPP_ADDR_MASK_EXT_LDST
 `ifdef SCR1_BRKM_MATCH_DATA_PLAIN_EN
  `define SCR1_BRKM_ARCH_SUPP_DATA_EXACT
  `define SCR1_BRKM_ARCH_SUPP_DATA_RANGE
  `define SCR1_BRKM_ARCH_SUPP_DATA_MASK
 `else  // SCR1_BRKM_MATCH_DATA_PLAIN_EN
  `undef SCR1_BRKM_ARCH_SUPP_DATA_EXACT
  `undef SCR1_BRKM_ARCH_SUPP_DATA_RANGE
  `undef SCR1_BRKM_ARCH_SUPP_DATA_MASK
 `endif  // SCR1_BRKM_MATCH_DATA_PLAIN_EN
`ifdef SCR1_BRKM_ARCH_SUPP_DATA_EXACT
 `define SCR1_BRKM_ARCH_SUPP_DATA
`endif
`ifdef SCR1_BRKM_ARCH_SUPP_DATA_RANGE
 `define SCR1_BRKM_ARCH_SUPP_DATA
`endif
`ifdef SCR1_BRKM_ARCH_SUPP_DATA_MASK
 `define SCR1_BRKM_ARCH_SUPP_DATA
`endif

//-------------------------------------------------------------------------------
// BRKM Configuration Parameters
//-------------------------------------------------------------------------------
localparam int unsigned SCR1_BRKM_PKG_BRKPT_NUMBER = SCR1_BRKM_BRKPT_NUMBER;

localparam bit SCR1_BRKM_PKG_SUPP_OPER_EXEC             = 1'b1;
localparam bit SCR1_BRKM_PKG_SUPP_OPER_LOAD             = 1'b1;
localparam bit SCR1_BRKM_PKG_SUPP_OPER_STORE            = 1'b1;
localparam bit SCR1_BRKM_PKG_SUPP_ADDR_EXACT            = 1'b1;
localparam bit SCR1_BRKM_PKG_SUPP_ADDR_RANGE            = 1'b0;
localparam bit SCR1_BRKM_PKG_SUPP_ADDR_RANGE_EXT_EXEC   = 1'b0;
localparam bit SCR1_BRKM_PKG_SUPP_ADDR_RANGE_EXT_LDST   = 1'b0;
localparam bit SCR1_BRKM_PKG_SUPP_ADDR_MASK             = 1'b1;
localparam bit SCR1_BRKM_PKG_SUPP_ADDR_MASK_EXT_EXEC    = 1'b1;
localparam bit SCR1_BRKM_PKG_SUPP_ADDR_MASK_EXT_LDST    = 1'b1;
localparam bit SCR1_BRKM_PKG_SUPP_DATA_EXACT            = 1'b0;
localparam bit SCR1_BRKM_PKG_SUPP_DATA_RANGE            = 1'b0;
localparam bit SCR1_BRKM_PKG_SUPP_DATA_MASK             = 1'b0;

localparam bit SCR1_BRKM_PKG_SUPP_ADDR                  = SCR1_BRKM_PKG_SUPP_ADDR_EXACT
                                                        | SCR1_BRKM_PKG_SUPP_ADDR_RANGE
                                                        | SCR1_BRKM_PKG_SUPP_ADDR_MASK;

localparam bit SCR1_BRKM_PKG_SUPP_ADDR_RANGE_OR_MASK    = SCR1_BRKM_PKG_SUPP_ADDR_RANGE
                                                        | SCR1_BRKM_PKG_SUPP_ADDR_MASK;

localparam bit SCR1_BRKM_PKG_SUPP_ADDR_RANGE_EXT        = SCR1_BRKM_PKG_SUPP_ADDR_RANGE_EXT_EXEC
                                                        | SCR1_BRKM_PKG_SUPP_ADDR_RANGE_EXT_LDST;

localparam bit SCR1_BRKM_PKG_SUPP_ADDR_MASK_EXT         = SCR1_BRKM_PKG_SUPP_ADDR_MASK_EXT_EXEC
                                                        | SCR1_BRKM_PKG_SUPP_ADDR_MASK_EXT_LDST;

localparam bit SCR1_BRKM_PKG_SUPP_DATA                  = SCR1_BRKM_PKG_SUPP_DATA_EXACT
                                                        | SCR1_BRKM_PKG_SUPP_DATA_RANGE
                                                        | SCR1_BRKM_PKG_SUPP_DATA_MASK;

localparam bit SCR1_BRKM_PKG_SUPP_DATA_RANGE_OR_MASK    = SCR1_BRKM_PKG_SUPP_DATA_MASK
                                                        | SCR1_BRKM_PKG_SUPP_DATA_RANGE;

localparam int unsigned SCR1_BRKM_PKG_CSR_DATA_WIDTH    = `SCR1_XLEN;
localparam int unsigned SCR1_BRKM_PKG_EXEC_ADDR_WIDTH   = `SCR1_XLEN;
localparam int unsigned SCR1_BRKM_PKG_EXEC_DATA_WIDTH   = `SCR1_XLEN;
localparam int unsigned SCR1_BRKM_PKG_LDST_ADDR_WIDTH   = `SCR1_XLEN;
localparam int unsigned SCR1_BRKM_PKG_LDST_DATA_WIDTH   = `SCR1_DMEM_DWIDTH;

//-------------------------------------------------------------------------------
// CSR definitions
//-------------------------------------------------------------------------------
localparam int unsigned SCR1_BRKM_PKG_CSR_OFFS_WIDTH    = (SCR1_CSR_ADDR_BRKM_MSPAN > 'd1)
                                                        ? $unsigned($clog2(SCR1_CSR_ADDR_BRKM_MSPAN))
                                                        : (SCR1_CSR_ADDR_BRKM_MSPAN);

typedef enum logic [SCR1_BRKM_PKG_CSR_OFFS_WIDTH-1:0] {
    SCR1_BRKM_PKG_CSR_OFFS_BPSELECT         = 3'h0,
    SCR1_BRKM_PKG_CSR_OFFS_BPCONTROL        = 3'h1,
    SCR1_BRKM_PKG_CSR_OFFS_BPLOADDR         = 3'h2,
    SCR1_BRKM_PKG_CSR_OFFS_BPHIADDR         = 3'h3,
    SCR1_BRKM_PKG_CSR_OFFS_BPLODATA         = 3'h4,
    SCR1_BRKM_PKG_CSR_OFFS_BPHIDATA         = 3'h5,
    SCR1_BRKM_PKG_CSR_OFFS_BPCTRLEXT        = 3'h6,
    SCR1_BRKM_PKG_CSR_OFFS_BRKMCTRL         = 3'h7,
    SCR1_BRKM_PKG_CSR_OFFS_XXX              = 'X
} type_scr1_brkm_csr_addr_e;

localparam bit [SCR1_CSR_ADDR_WIDTH-1:0]    SCR1_BRKM_PKG_CSR_ADDR_BPSELECT  = SCR1_CSR_ADDR_BRKM_MBASE + SCR1_BRKM_PKG_CSR_OFFS_BPSELECT;
localparam bit [SCR1_CSR_ADDR_WIDTH-1:0]    SCR1_BRKM_PKG_CSR_ADDR_BPCONTROL = SCR1_CSR_ADDR_BRKM_MBASE + SCR1_BRKM_PKG_CSR_OFFS_BPCONTROL;
localparam bit [SCR1_CSR_ADDR_WIDTH-1:0]    SCR1_BRKM_PKG_CSR_ADDR_BPLOADDR  = SCR1_CSR_ADDR_BRKM_MBASE + SCR1_BRKM_PKG_CSR_OFFS_BPLOADDR;
localparam bit [SCR1_CSR_ADDR_WIDTH-1:0]    SCR1_BRKM_PKG_CSR_ADDR_BPHIADDR  = SCR1_CSR_ADDR_BRKM_MBASE + SCR1_BRKM_PKG_CSR_OFFS_BPHIADDR;
localparam bit [SCR1_CSR_ADDR_WIDTH-1:0]    SCR1_BRKM_PKG_CSR_ADDR_BPLODATA  = SCR1_CSR_ADDR_BRKM_MBASE + SCR1_BRKM_PKG_CSR_OFFS_BPLODATA;
localparam bit [SCR1_CSR_ADDR_WIDTH-1:0]    SCR1_BRKM_PKG_CSR_ADDR_BPHIDATA  = SCR1_CSR_ADDR_BRKM_MBASE + SCR1_BRKM_PKG_CSR_OFFS_BPHIDATA;
localparam bit [SCR1_CSR_ADDR_WIDTH-1:0]    SCR1_BRKM_PKG_CSR_ADDR_BPCTRLEXT = SCR1_CSR_ADDR_BRKM_MBASE + SCR1_BRKM_PKG_CSR_OFFS_BPCTRLEXT;
localparam bit [SCR1_CSR_ADDR_WIDTH-1:0]    SCR1_BRKM_PKG_CSR_ADDR_BRKMCTRL  = SCR1_CSR_ADDR_BRKM_MBASE + SCR1_BRKM_PKG_CSR_OFFS_BRKMCTRL;

//-------------------------------------------------------------------------------
// Breakpoint Select Register (bpselect, @ 0x780)
//-------------------------------------------------------------------------------
localparam int unsigned SCR1_BRKM_PKG_CSR_BPSELECT_BP_WIDTH_MAX = 12;
localparam int unsigned SCR1_BRKM_PKG_CSR_BPSELECT_BP_WIDTH     = (SCR1_BRKM_PKG_BRKPT_NUMBER > 1)
                                                                ? $clog2(SCR1_BRKM_PKG_BRKPT_NUMBER)
                                                                : (SCR1_BRKM_PKG_BRKPT_NUMBER);

typedef enum int {
    SCR1_BRKM_PKG_CSR_BPSELECT_BP_BIT_R      = 0,
    SCR1_BRKM_PKG_CSR_BPSELECT_BP_BIT_L      = SCR1_BRKM_PKG_CSR_BPSELECT_BP_BIT_R+SCR1_BRKM_PKG_CSR_BPSELECT_BP_WIDTH_MAX-1,
    SCR1_BRKM_PKG_CSR_BPSELECT_RSRV0_BIT_R   = SCR1_BRKM_PKG_CSR_BPSELECT_BP_BIT_R+SCR1_BRKM_PKG_CSR_BPSELECT_BP_WIDTH_MAX,
    SCR1_BRKM_PKG_CSR_BPSELECT_RSRV0_BIT_L   = (SCR1_BRKM_PKG_CSR_DATA_WIDTH-1)
} type_scr1_brkm_csr_bpselect_bits_e;

typedef struct packed {
    logic [SCR1_BRKM_PKG_CSR_BPSELECT_RSRV0_BIT_L-SCR1_BRKM_PKG_CSR_BPSELECT_RSRV0_BIT_R:0] rsrv0;
    logic [SCR1_BRKM_PKG_CSR_BPSELECT_BP_BIT_L-SCR1_BRKM_PKG_CSR_BPSELECT_BP_BIT_R:0]       bp;
} type_scr1_brkm_csr_bpselect_s;

//-------------------------------------------------------------------------------
// Breakpoint Control Register (bpcontrol, @ 0x781)
//-------------------------------------------------------------------------------
typedef enum int {
    SCR1_BRKM_PKG_CSR_BPCONTROL_RSRV0_BIT           = 0,
    SCR1_BRKM_PKG_CSR_BPCONTROL_DMASKEN_BIT         = 1,
    SCR1_BRKM_PKG_CSR_BPCONTROL_DRANGEEN_BIT        = 2,
    SCR1_BRKM_PKG_CSR_BPCONTROL_DEN_BIT             = 3,
    SCR1_BRKM_PKG_CSR_BPCONTROL_RSRV1_BIT           = 4,
    SCR1_BRKM_PKG_CSR_BPCONTROL_AMASKEN_BIT         = 5,
    SCR1_BRKM_PKG_CSR_BPCONTROL_ARANGEEN_BIT        = 6,
    SCR1_BRKM_PKG_CSR_BPCONTROL_AEN_BIT             = 7,
    SCR1_BRKM_PKG_CSR_BPCONTROL_EXECEN_BIT          = 8,
    SCR1_BRKM_PKG_CSR_BPCONTROL_STOREEN_BIT         = 9,
    SCR1_BRKM_PKG_CSR_BPCONTROL_LOADEN_BIT          = 10,
    SCR1_BRKM_PKG_CSR_BPCONTROL_RSRV2_BIT           = 11,
    SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_BIT_R        = 12,
    SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_BIT_L        = 14,
    SCR1_BRKM_PKG_CSR_BPCONTROL_MATCHED_BIT         = 15,
    SCR1_BRKM_PKG_CSR_BPCONTROL_RSRV3_BIT           = 16,
    SCR1_BRKM_PKG_CSR_BPCONTROL_DMASKSUP_BIT        = 17,
    SCR1_BRKM_PKG_CSR_BPCONTROL_DRANGESUP_BIT       = 18,
    SCR1_BRKM_PKG_CSR_BPCONTROL_DSUP_BIT            = 19,
    SCR1_BRKM_PKG_CSR_BPCONTROL_RSRV4_BIT           = 20,
    SCR1_BRKM_PKG_CSR_BPCONTROL_AMASKSUP_BIT        = 21,
    SCR1_BRKM_PKG_CSR_BPCONTROL_ARANGESUP_BIT       = 22,
    SCR1_BRKM_PKG_CSR_BPCONTROL_ASUP_BIT            = 23,
    SCR1_BRKM_PKG_CSR_BPCONTROL_EXECSUP_BIT         = 24,
    SCR1_BRKM_PKG_CSR_BPCONTROL_STORESUP_BIT        = 25,
    SCR1_BRKM_PKG_CSR_BPCONTROL_LOADSUP_BIT         = 26,
    SCR1_BRKM_PKG_CSR_BPCONTROL_RSRV5_BIT_R         = 27,
    SCR1_BRKM_PKG_CSR_BPCONTROL_RSRV5_BIT_L         = (SCR1_BRKM_PKG_CSR_DATA_WIDTH-1)
} type_scr1_brkm_csr_bpcontrol_bits_e;

localparam int SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_WIDTH = SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_BIT_L-SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_BIT_R+1;
typedef enum logic [SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_WIDTH-1:0] {
    SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_NONE         = 3'h0,
    SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_DBGEXC       = 3'h1,
    SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_DMODE        = 3'h2,
    SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_TRACE_START  = 3'h3,
    SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_TRACE_STOP   = 3'h4,
    SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_TRACE_PACKT  = 3'h5,
    SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_RSRV0        = 3'h6,
    SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_RSRV1        = 3'h7,
    SCR1_BRKM_PKG_CSR_BPCONTROL_ACTION_XXX          = 'X
} type_scr1_brkm_csr_bpcontrol_action_e;

typedef struct packed {
    logic [SCR1_BRKM_PKG_CSR_BPCONTROL_RSRV5_BIT_L-SCR1_BRKM_PKG_CSR_BPCONTROL_RSRV5_BIT_R:0]   rsrv5;
    logic                                           loadsup;
    logic                                           storesup;
    logic                                           execsup;
    logic                                           asup;
    logic                                           arangesup;
    logic                                           amasksup;
    logic                                           rsrv4;
    logic                                           dsup;
    logic                                           drangesup;
    logic                                           dmasksup;
    logic                                           rsrv3;
    logic                                           matched;
    type_scr1_brkm_csr_bpcontrol_action_e           action;
    logic                                           rsrv2;
    logic                                           loaden;
    logic                                           storeen;
    logic                                           execen;
    logic                                           aen;
    logic                                           arangeen;
    logic                                           amasken;
    logic                                           rsrv1;
    logic                                           den;
    logic                                           drangeen;
    logic                                           dmasken;
    logic                                           rsrv0;
} type_scr1_brkm_csr_bpcontrol_s;

//-------------------------------------------------------------------------------
// Breakpoint Control Extension Register (bpcontrol_ext, @ 0x786)
//-------------------------------------------------------------------------------
typedef enum int {
    SCR1_BRKM_PKG_CSR_BPCTRLEXT_RSRV0_BIT_R         = 0,
    SCR1_BRKM_PKG_CSR_BPCTRLEXT_RSRV0_BIT_L         = 12,
    SCR1_BRKM_PKG_CSR_BPCTRLEXT_ARANGEEXT_EN_BIT    = 15,
    SCR1_BRKM_PKG_CSR_BPCTRLEXT_AMASKEXT_EN_BIT     = 14,
    SCR1_BRKM_PKG_CSR_BPCTRLEXT_DRYRUN_BIT          = 13,
    SCR1_BRKM_PKG_CSR_BPCTRLEXT_RSRV1_BIT_R         = 16,
    SCR1_BRKM_PKG_CSR_BPCTRLEXT_RSRV1_BIT_L         = (SCR1_BRKM_PKG_CSR_DATA_WIDTH-1)
} type_scr1_brkm_csr_bpctrlext_bits_e;

typedef struct packed {
    logic [SCR1_BRKM_PKG_CSR_BPCTRLEXT_RSRV1_BIT_L-SCR1_BRKM_PKG_CSR_BPCTRLEXT_RSRV1_BIT_R:0]   rsrv1;
    logic                                           arangeen;
    logic                                           amasken;
    logic                                           dry_run;
    logic [SCR1_BRKM_PKG_CSR_BPCTRLEXT_RSRV0_BIT_L-SCR1_BRKM_PKG_CSR_BPCTRLEXT_RSRV0_BIT_R:0]   rsrv0;
} type_scr1_brkm_csr_bpctrlext_s;

//-------------------------------------------------------------------------------
// Breakpoint Module Control Register (brkmcontrol, @ 0x787)
//-------------------------------------------------------------------------------
localparam int SCR1_BRKM_PKG_CSR_BRKMCTRL_BP_WIDTH_MAX = SCR1_BRKM_PKG_CSR_BPSELECT_BP_WIDTH_MAX;
localparam int SCR1_BRKM_PKG_CSR_BRKMCTRL_BP_WIDTH     = SCR1_BRKM_PKG_CSR_BPSELECT_BP_WIDTH;

typedef enum int {
    SCR1_BRKM_PKG_CSR_BRKMCTRL_BP_BIT_R             = 0,
    SCR1_BRKM_PKG_CSR_BRKMCTRL_BP_BIT_L             = SCR1_BRKM_PKG_CSR_BRKMCTRL_BP_BIT_R+SCR1_BRKM_PKG_CSR_BRKMCTRL_BP_WIDTH_MAX-1,
    SCR1_BRKM_PKG_CSR_BRKMCTRL_MATCHED_BIT          = SCR1_BRKM_PKG_CSR_BRKMCTRL_BP_BIT_R+SCR1_BRKM_PKG_CSR_BRKMCTRL_BP_WIDTH_MAX,
    SCR1_BRKM_PKG_CSR_BRKMCTRL_RSRV0_BIT            = 13,
    SCR1_BRKM_PKG_CSR_BRKMCTRL_BP_I_SKIP_BIT        = 14,
    SCR1_BRKM_PKG_CSR_BRKMCTRL_INIT_BIT             = 15,
    SCR1_BRKM_PKG_CSR_BRKMCTRL_MODE_BIT             = 16,
    SCR1_BRKM_PKG_CSR_BRKMCTRL_RSRV1_BIT_R          = 17,
    SCR1_BRKM_PKG_CSR_BRKMCTRL_RSRV1_BIT_L          = (SCR1_BRKM_PKG_CSR_DATA_WIDTH-1)
} type_scr1_brkm_csr_brkmctrl_bits_e;

typedef struct packed {
    logic [SCR1_BRKM_PKG_CSR_BRKMCTRL_RSRV1_BIT_L-SCR1_BRKM_PKG_CSR_BRKMCTRL_RSRV1_BIT_R:0] rsrv1;
    logic                                           mode;
    logic                                           init;
    logic                                           bp_i_skip;
    logic                                           rsrv0;
    logic                                           matched;
    logic [SCR1_BRKM_PKG_CSR_BRKMCTRL_BP_BIT_L-SCR1_BRKM_PKG_CSR_BRKMCTRL_BP_BIT_R:0]       bp;
} type_scr1_brkm_csr_brkmctrl_s;

//-------------------------------------------------------------------------------
// Types used in module interfaces
//-------------------------------------------------------------------------------

typedef struct {
    logic                                           vd;
    type_scr1_op_width_e                            width;
    logic [SCR1_BRKM_PKG_EXEC_ADDR_WIDTH-1:0]       addr;
} type_scr1_brkm_instr_mon_s;

typedef struct {
    logic                                           vd;
    logic                                           load;
    logic                                           store;
    type_scr1_op_width_e                            width;
    logic [SCR1_BRKM_PKG_LDST_ADDR_WIDTH-1:0]       addr;
} type_scr1_brkm_lsu_mon_s;

`else // SCR1_BRKM_EN

`undef SCR1_BRKM_ARCH_SUPP_OPER_EXEC
`undef SCR1_BRKM_ARCH_SUPP_OPER_LOAD
`undef SCR1_BRKM_ARCH_SUPP_OPER_STORE
`undef SCR1_BRKM_ARCH_SUPP_ADDR_EXACT
`undef SCR1_BRKM_ARCH_SUPP_ADDR_RANGE
`undef SCR1_BRKM_ARCH_SUPP_ADDR_RANGE_EXT_EXEC
`undef SCR1_BRKM_ARCH_SUPP_ADDR_RANGE_EXT_LDST
`undef SCR1_BRKM_ARCH_SUPP_ADDR_MASK
`undef SCR1_BRKM_ARCH_SUPP_ADDR_MASK_EXT_EXEC
`undef SCR1_BRKM_ARCH_SUPP_ADDR_MASK_EXT_LDST
`undef SCR1_BRKM_ARCH_SUPP_DATA_EXACT
`undef SCR1_BRKM_ARCH_SUPP_DATA_RANGE
`undef SCR1_BRKM_ARCH_SUPP_DATA_MASK
`undef SCR1_BRKM_ARCH_SUPP_DATA

`endif // SCR1_BRKM_EN

`endif // SCR1_INCLUDE_BRKM_DEFS