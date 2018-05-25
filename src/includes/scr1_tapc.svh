`ifndef SCR1_INCLUDE_TAPC_DEFS
`define SCR1_INCLUDE_TAPC_DEFS
/// Copyright by Syntacore LLC © 2016-2018. See LICENSE for details
/// @file       <scr1_tapc.svh>
/// @brief      TAPC header file
///

`include "scr1_arch_description.svh"

`ifdef SCR1_DBGC_EN
package scr1_tapc_pkg;

//-------------------------------------------------------------------------------
// Parameters
//-------------------------------------------------------------------------------
localparam int unsigned                         SCR1_TAP_STATE_WIDTH            = 4;
localparam int unsigned                         SCR1_TAP_INSTRUCTION_WIDTH      = 4;
localparam int unsigned                         SCR1_TAP_DR_IDCODE_WIDTH        = 32;
localparam int unsigned                         SCR1_TAP_DR_DBG_ID_WIDTH        = 32;
localparam int unsigned                         SCR1_TAP_DR_BLD_ID_WIDTH        = 32;
localparam int unsigned                         SCR1_TAP_DR_BYPASS_WIDTH        = 1;
localparam int unsigned                         SCR1_TAP_DR_SYS_CTRL_WIDTH      = 1;
localparam int unsigned                         SCR1_TAP_DR_MTAP_SWITCH_WIDTH   = 1;
localparam bit [SCR1_TAP_DR_IDCODE_WIDTH-1:0]   SCR1_TAP_IDCODE_RISCV_SC        = 32'hDEB01001;
localparam bit [SCR1_TAP_DR_BLD_ID_WIDTH-1:0]   SCR1_TAP_BLD_ID_VALUE           = `SCR1_MIMPID;

//-------------------------------------------------------------------------------
// Types
//-------------------------------------------------------------------------------
typedef enum logic [SCR1_TAP_STATE_WIDTH-1:0] {
    SCR1_TAP_STATE_RESET,
    SCR1_TAP_STATE_IDLE,
    SCR1_TAP_STATE_DR_SEL_SCAN,
    SCR1_TAP_STATE_DR_CAPTURE,
    SCR1_TAP_STATE_DR_SHIFT,
    SCR1_TAP_STATE_DR_EXIT1,
    SCR1_TAP_STATE_DR_PAUSE,
    SCR1_TAP_STATE_DR_EXIT2,
    SCR1_TAP_STATE_DR_UPDATE,
    SCR1_TAP_STATE_IR_SEL_SCAN,
    SCR1_TAP_STATE_IR_CAPTURE,
    SCR1_TAP_STATE_IR_SHIFT,
    SCR1_TAP_STATE_IR_EXIT1,
    SCR1_TAP_STATE_IR_PAUSE,
    SCR1_TAP_STATE_IR_EXIT2,
    SCR1_TAP_STATE_IR_UPDATE,
    SCR1_TAP_STATE_XXX       = 'X
} type_scr1_tap_state_e;

typedef enum logic [SCR1_TAP_INSTRUCTION_WIDTH-1:0] {
    SCR1_TAP_INSTR_DBG_ID            = 4'h3,
    SCR1_TAP_INSTR_BLD_ID            = 4'h4,
    SCR1_TAP_INSTR_DBG_STATUS        = 4'h5,
    SCR1_TAP_INSTR_DAP_CTRL          = 4'h6,
    SCR1_TAP_INSTR_DAP_CTRL_RD       = 4'h7,
    SCR1_TAP_INSTR_DAP_CMD           = 4'h8,
    SCR1_TAP_INSTR_SYS_CTRL          = 4'h9,
    SCR1_TAP_INSTR_PIPELN_STS        = 4'hA,
    SCR1_TAP_INSTR_TARGET_ID         = 4'hB,
    SCR1_TAP_INSTR_MTAP_SWITCH       = 4'hD,
    SCR1_TAP_INSTR_IDCODE            = 4'hE,
    SCR1_TAP_INSTR_BYPASS            = 4'hF,
    SCR1_TAP_INSTR_XXX               = 'X
} type_scr1_tap_instr_e;

endpackage : scr1_tapc_pkg

import scr1_tapc_pkg::*;

`endif // SCR1_DBGC_EN
`endif // SCR1_INCLUDE_TAPC_DEFS
