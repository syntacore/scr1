/// Copyright by Syntacore LLC © 2016-2021. See LICENSE for details
/// @file       <scr1_tapc.svh>
/// @brief      TAPC header file
///

`ifndef SCR1_INCLUDE_TAPC_DEFS
`define SCR1_INCLUDE_TAPC_DEFS

`include "scr1_arch_description.svh"

`ifdef SCR1_DBG_EN

//==============================================================================
// Parameters
//==============================================================================
localparam int unsigned                         SCR1_TAP_STATE_WIDTH            = 4;
localparam int unsigned                         SCR1_TAP_INSTRUCTION_WIDTH      = 5;
localparam int unsigned                         SCR1_TAP_DR_IDCODE_WIDTH        = 32;
localparam int unsigned                         SCR1_TAP_DR_BLD_ID_WIDTH        = 32;
localparam int unsigned                         SCR1_TAP_DR_BYPASS_WIDTH        = 1;
//localparam bit [SCR1_TAP_DR_IDCODE_WIDTH-1:0]   SCR1_TAP_IDCODE_RISCV_SC        = `SCR1_TAP_IDCODE;
localparam bit [SCR1_TAP_DR_BLD_ID_WIDTH-1:0]   SCR1_TAP_BLD_ID_VALUE           = `SCR1_MIMPID;

//==============================================================================
// Types
//==============================================================================
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
    SCR1_TAP_STATE_IR_UPDATE
`ifdef SCR1_XPROP_EN
    ,
    SCR1_TAP_STATE_XXX       = 'X
`endif // SCR1_XPROP_EN
} type_scr1_tap_state_e;

typedef enum logic [SCR1_TAP_INSTRUCTION_WIDTH - 1:0] {
    SCR1_TAP_INSTR_IDCODE            = 5'h01,
    SCR1_TAP_INSTR_BLD_ID            = 5'h04,
    SCR1_TAP_INSTR_SCU_ACCESS        = 5'h09,

    SCR1_TAP_INSTR_DTMCS             = 5'h10,
    SCR1_TAP_INSTR_DMI_ACCESS        = 5'h11,

    SCR1_TAP_INSTR_BYPASS            = 5'h1F
`ifdef SCR1_XPROP_EN
    ,
    SCR1_TAP_INSTR_XXX               = 'X
`endif // SCR1_XPROP_EN
} type_scr1_tap_instr_e;

`endif // SCR1_DBG_EN
`endif // SCR1_INCLUDE_TAPC_DEFS
