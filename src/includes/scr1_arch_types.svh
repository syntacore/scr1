/// Copyright by Syntacore LLC © 2016-2020. See LICENSE for details
/// @file       <scr1_arch_types.svh>
/// @brief      Pipeline types description file
///

`ifndef SCR1_ARCH_TYPES_SVH
`define SCR1_ARCH_TYPES_SVH

`include "scr1_arch_description.svh"

//-------------------------------------------------------------------------------
// MPRF and CSR parameters
//-------------------------------------------------------------------------------

`ifdef SCR1_RVE_EXT
  `define SCR1_MPRF_AWIDTH    4
  `define SCR1_MPRF_SIZE      16
`else // SCR1_RVE_EXT
  `define SCR1_MPRF_AWIDTH    5
  `define SCR1_MPRF_SIZE      32
`endif // SCR1_RVE_EXT

typedef logic [`SCR1_XLEN-1:0]  type_scr1_mprf_v;
typedef logic [`SCR1_XLEN-1:0]  type_scr1_pc_v;

parameter int unsigned  SCR1_CSR_ADDR_WIDTH             = 12;
parameter int unsigned  SCR1_CSR_MTVEC_BASE_ZERO_BITS   = 6;
parameter int unsigned  SCR1_CSR_MTVEC_BASE_VAL_BITS    = `SCR1_XLEN-SCR1_CSR_MTVEC_BASE_ZERO_BITS;
parameter bit [`SCR1_XLEN-1:SCR1_CSR_MTVEC_BASE_ZERO_BITS]  SCR1_CSR_MTVEC_BASE_WR_RST_VAL    =
                                      SCR1_CSR_MTVEC_BASE_VAL_BITS'(SCR1_ARCH_MTVEC_BASE >> SCR1_CSR_MTVEC_BASE_ZERO_BITS);
parameter int unsigned  SCR1_CSR_MTVEC_BASE_RO_BITS = (`SCR1_XLEN-(SCR1_CSR_MTVEC_BASE_ZERO_BITS+SCR1_MTVEC_BASE_WR_BITS));

`define SCR1_MTVAL_ILLEGAL_INSTR_EN

//-------------------------------------------------------------------------------
// Exception and IRQ codes
//-------------------------------------------------------------------------------
parameter int unsigned SCR1_EXC_CODE_WIDTH_E    = 4;

// Exceptions
typedef enum logic [SCR1_EXC_CODE_WIDTH_E-1:0] {
    SCR1_EXC_CODE_INSTR_MISALIGN        = 4'd0,     // from EXU
    SCR1_EXC_CODE_INSTR_ACCESS_FAULT    = 4'd1,     // from IFU
    SCR1_EXC_CODE_ILLEGAL_INSTR         = 4'd2,     // from IDU or CSR
    SCR1_EXC_CODE_BREAKPOINT            = 4'd3,     // from IDU or BRKM
    SCR1_EXC_CODE_LD_ADDR_MISALIGN      = 4'd4,     // from LSU
    SCR1_EXC_CODE_LD_ACCESS_FAULT       = 4'd5,     // from LSU
    SCR1_EXC_CODE_ST_ADDR_MISALIGN      = 4'd6,     // from LSU
    SCR1_EXC_CODE_ST_ACCESS_FAULT       = 4'd7,     // from LSU
    SCR1_EXC_CODE_ECALL_M               = 4'd11     // from IDU
} type_scr1_exc_code_e;

// IRQs, reset
parameter bit [SCR1_EXC_CODE_WIDTH_E-1:0] SCR1_EXC_CODE_IRQ_M_SOFTWARE      = 4'd3;
parameter bit [SCR1_EXC_CODE_WIDTH_E-1:0] SCR1_EXC_CODE_IRQ_M_TIMER         = 4'd7;
parameter bit [SCR1_EXC_CODE_WIDTH_E-1:0] SCR1_EXC_CODE_IRQ_M_EXTERNAL      = 4'd11;
parameter bit [SCR1_EXC_CODE_WIDTH_E-1:0] SCR1_EXC_CODE_RESET               = 4'd0;

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
