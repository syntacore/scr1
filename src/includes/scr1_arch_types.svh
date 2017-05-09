`ifndef SCR1_ARCH_TYPES_SVH
`define SCR1_ARCH_TYPES_SVH
/// Copyright by Syntacore LLC © 2016, 2017. See LICENSE for details
/// @file       <scr1_arch_types.svh>
/// @brief      Pipeline Types
///

`include "scr1_arch_description.svh"

typedef logic [`SCR1_XLEN-1:0]  type_scr1_mprf_v;
typedef logic [`SCR1_XLEN-1:0]  type_scr1_pc_v;

//-------------------------------------------------------------------------------
// Exception codes
//-------------------------------------------------------------------------------
localparam SCR1_EXC_CODE_ALL_NUM_E = 12;
localparam SCR1_EXC_CODE_WIDTH_E   = $clog2(SCR1_EXC_CODE_ALL_NUM_E);
typedef enum logic [SCR1_EXC_CODE_WIDTH_E-1:0] {
    SCR1_EXC_CODE_INSTR_MISALIGN,           // from EXU
    SCR1_EXC_CODE_INSTR_ACCESS_FAULT,       // from IFU
    SCR1_EXC_CODE_ILLEGAL_INSTR,            // from IDU or CSR
    SCR1_EXC_CODE_BREAKPOINT,               // from IDU or BRKM
    SCR1_EXC_CODE_LD_ADDR_MISALIGN,         // from LSU
    SCR1_EXC_CODE_LD_ACCESS_FAULT,          // from LSU
    SCR1_EXC_CODE_ST_AMO_ADDR_MISALIGN,     // from LSU
    SCR1_EXC_CODE_ST_AMO_ACCESS_FAULT,      // from LSU
    SCR1_EXC_CODE_ECALL_U,                  // unused
    SCR1_EXC_CODE_ECALL_S,                  // unused
    SCR1_EXC_CODE_ECALL_H,                  // unused
    SCR1_EXC_CODE_ECALL_M                   // from IDU
} type_scr1_exc_code_e;

//-------------------------------------------------------------------------------
// Operand width for BRKM
//-------------------------------------------------------------------------------
typedef enum logic [1:0] {
    SCR1_OP_WIDTH_BYTE  = 2'b00,
    SCR1_OP_WIDTH_HALF  = 2'b01,
    SCR1_OP_WIDTH_WORD  = 2'b10,
    SCR1_OP_WIDTH_ERROR = 'x
} type_scr1_op_width_e;

`endif //SCR1_ARCH_TYPES_SVH
