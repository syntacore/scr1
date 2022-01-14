/// Copyright by Syntacore LLC © 2016-2021. See LICENSE for details
/// @file       <scr1_pipe_hdu.svh>
/// @brief      HART Debug Unit definitions file
///

`ifdef SCR1_DBG_EN
`ifndef SCR1_INCLUDE_HDU_DEFS
`define SCR1_INCLUDE_HDU_DEFS

`include "scr1_arch_description.svh"
`include "scr1_csr.svh"

`ifdef SCR1_MMU_EN
 `define SCR1_HDU_FEATURE_MPRVEN
`endif // SCR1_MMU_EN

//==============================================================================
// Parameters
//==============================================================================
//localparam int unsigned SCR1_HDU_DEBUGCSR_BASE_ADDR      = 12'h7B0;
localparam int unsigned SCR1_HDU_DEBUGCSR_ADDR_SPAN      = SCR1_CSR_ADDR_HDU_MSPAN;
localparam int unsigned SCR1_HDU_DEBUGCSR_ADDR_WIDTH     = $clog2(SCR1_HDU_DEBUGCSR_ADDR_SPAN);
localparam bit [3:0]    SCR1_HDU_DEBUGCSR_DCSR_XDEBUGVER = 4'h4;
localparam int unsigned SCR1_HDU_PBUF_ADDR_SPAN          = 8;
localparam int unsigned SCR1_HDU_PBUF_ADDR_WIDTH         = $clog2(SCR1_HDU_PBUF_ADDR_SPAN);
localparam int unsigned SCR1_HDU_DATA_REG_WIDTH          = 32;
localparam int unsigned SCR1_HDU_CORE_INSTR_WIDTH        = 32;


//==============================================================================
// Types
//==============================================================================

// HART Debug States:
typedef enum logic [1:0] {
    SCR1_HDU_DBGSTATE_RESET         = 2'b00,
    SCR1_HDU_DBGSTATE_RUN           = 2'b01,
    SCR1_HDU_DBGSTATE_DHALTED       = 2'b10,
    SCR1_HDU_DBGSTATE_DRUN          = 2'b11
`ifdef SCR1_XPROP_EN
    ,
    SCR1_HDU_DBGSTATE_XXX           = 'X
`endif // SCR1_XPROP_EN
} type_scr1_hdu_dbgstates_e;

typedef enum logic [1:0] {
    SCR1_HDU_PBUFSTATE_IDLE          = 2'b00,
    SCR1_HDU_PBUFSTATE_FETCH         = 2'b01,
    SCR1_HDU_PBUFSTATE_EXCINJECT     = 2'b10,
    SCR1_HDU_PBUFSTATE_WAIT4END      = 2'b11
`ifdef SCR1_XPROP_EN
    ,
    SCR1_HDU_PBUFSTATE_XXX           = 'X
`endif // SCR1_XPROP_EN
} type_scr1_hdu_pbufstates_e;

typedef enum logic {
    SCR1_HDU_HARTCMD_RESUME         = 1'b0,
    SCR1_HDU_HARTCMD_HALT           = 1'b1
`ifdef SCR1_XPROP_EN
    ,
    SCR1_HDU_HARTCMD_XXX            = 1'bX
`endif // SCR1_XPROP_EN
} type_scr1_hdu_hart_command_e;

typedef enum logic {
    SCR1_HDU_FETCH_SRC_NORMAL       = 1'b0,
    SCR1_HDU_FETCH_SRC_PBUF         = 1'b1
`ifdef SCR1_XPROP_EN
    ,
    SCR1_HDU_FETCH_SRC_XXX          = 1'bX
`endif // SCR1_XPROP_EN
} type_scr1_hdu_fetch_src_e;

typedef struct packed {
    //logic                               reset_n;
    logic                               except;
    logic                               ebreak;
    type_scr1_hdu_dbgstates_e           dbg_state;
} type_scr1_hdu_hartstatus_s;

// Debug Mode Redirection control:
typedef struct packed {
    logic                               sstep;          // Single Step
    logic                               ebreak;         // Redirection after EBREAK execution
} type_scr1_hdu_redirect_s;

typedef struct packed {
    logic                               irq_dsbl;
    type_scr1_hdu_fetch_src_e           fetch_src;
    logic                               pc_advmt_dsbl;
    logic                               hwbrkpt_dsbl;
    type_scr1_hdu_redirect_s            redirect;
} type_scr1_hdu_runctrl_s;

// HART Halt Status:
typedef enum logic [2:0] {
    SCR1_HDU_HALTCAUSE_NONE         = 3'b000,
    SCR1_HDU_HALTCAUSE_EBREAK       = 3'b001,
    SCR1_HDU_HALTCAUSE_TMREQ        = 3'b010,
    SCR1_HDU_HALTCAUSE_DMREQ        = 3'b011,
    SCR1_HDU_HALTCAUSE_SSTEP        = 3'b100,
    SCR1_HDU_HALTCAUSE_RSTEXIT      = 3'b101
`ifdef SCR1_XPROP_EN
    ,
    SCR1_HDU_HALTCAUSE_XXX          = 'X
`endif // SCR1_XPROP_EN
} type_scr1_hdu_haltcause_e;

typedef struct packed {
    logic                               except;
    type_scr1_hdu_haltcause_e           cause;
} type_scr1_hdu_haltstatus_s;


// Debug CSR map
localparam SCR1_HDU_DBGCSR_OFFS_DCSR       = SCR1_HDU_DEBUGCSR_ADDR_WIDTH'( 'd0 );
localparam SCR1_HDU_DBGCSR_OFFS_DPC        = SCR1_HDU_DEBUGCSR_ADDR_WIDTH'( 'd1 );
localparam SCR1_HDU_DBGCSR_OFFS_DSCRATCH0  = SCR1_HDU_DEBUGCSR_ADDR_WIDTH'( 'd2 );
localparam SCR1_HDU_DBGCSR_OFFS_DSCRATCH1  = SCR1_HDU_DEBUGCSR_ADDR_WIDTH'( 'd3 );

localparam bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_HDU_DBGCSR_ADDR_DCSR      = SCR1_CSR_ADDR_HDU_MBASE + SCR1_HDU_DBGCSR_OFFS_DCSR;
localparam bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_HDU_DBGCSR_ADDR_DPC       = SCR1_CSR_ADDR_HDU_MBASE + SCR1_HDU_DBGCSR_OFFS_DPC;
localparam bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_HDU_DBGCSR_ADDR_DSCRATCH0 = SCR1_CSR_ADDR_HDU_MBASE + SCR1_HDU_DBGCSR_OFFS_DSCRATCH0;
localparam bit [SCR1_CSR_ADDR_WIDTH-1:0] SCR1_HDU_DBGCSR_ADDR_DSCRATCH1 = SCR1_CSR_ADDR_HDU_MBASE + SCR1_HDU_DBGCSR_OFFS_DSCRATCH1;

// Debug CSRs :: DCSR
typedef enum int {
    SCR1_HDU_DCSR_PRV_BIT_R         = 0,
    SCR1_HDU_DCSR_PRV_BIT_L         = 1,
    SCR1_HDU_DCSR_STEP_BIT          = 2,
    SCR1_HDU_DCSR_RSRV0_BIT_R       = 3,
    SCR1_HDU_DCSR_RSRV0_BIT_L       = 5,
    SCR1_HDU_DCSR_CAUSE_BIT_R       = 6,
    SCR1_HDU_DCSR_CAUSE_BIT_L       = 8,
    SCR1_HDU_DCSR_RSRV1_BIT_R       = 9,
    SCR1_HDU_DCSR_RSRV1_BIT_L       = 10,
    SCR1_HDU_DCSR_STEPIE_BIT        = 11,
    SCR1_HDU_DCSR_RSRV2_BIT_R       = 12,
    SCR1_HDU_DCSR_RSRV2_BIT_L       = 14,
    SCR1_HDU_DCSR_EBREAKM_BIT       = 15,
    SCR1_HDU_DCSR_RSRV3_BIT_R       = 16,
    SCR1_HDU_DCSR_RSRV3_BIT_L       = 27,
    SCR1_HDU_DCSR_XDEBUGVER_BIT_R   = 28,
    SCR1_HDU_DCSR_XDEBUGVER_BIT_L   = 31
} type_scr1_hdu_dcsr_bits_e;

//localparam int unsigned SCR1_HDU_DEBUGCSR_DCSR_PRV_WIDTH = SCR1_HDU_DCSR_PRV_BIT_L-SCR1_HDU_DCSR_PRV_BIT_R+1;

typedef struct packed {
    logic [SCR1_HDU_DCSR_XDEBUGVER_BIT_L-SCR1_HDU_DCSR_XDEBUGVER_BIT_R:0]   xdebugver;
    logic [SCR1_HDU_DCSR_RSRV3_BIT_L-SCR1_HDU_DCSR_RSRV3_BIT_R:0]           rsrv3;
    logic                                                                   ebreakm;
    logic [SCR1_HDU_DCSR_RSRV2_BIT_L-SCR1_HDU_DCSR_RSRV2_BIT_R:0]           rsrv2;
    logic                                                                   stepie;
    logic [SCR1_HDU_DCSR_RSRV1_BIT_L-SCR1_HDU_DCSR_RSRV1_BIT_R:0]           rsrv1;
    logic [SCR1_HDU_DCSR_CAUSE_BIT_L-SCR1_HDU_DCSR_CAUSE_BIT_R:0]           cause;
    logic [SCR1_HDU_DCSR_RSRV0_BIT_L-SCR1_HDU_DCSR_RSRV0_BIT_R:0]           rsrv0;
    logic                                                                   step;
    logic [SCR1_HDU_DCSR_PRV_BIT_L-SCR1_HDU_DCSR_PRV_BIT_R:0]               prv;
} type_scr1_hdu_dcsr_s;


`endif // SCR1_INCLUDE_HDU_DEFS
`endif // SCR1_DBG_EN
