`ifndef SCR1_INCLUDE_DBGC_DEFS
`define SCR1_INCLUDE_DBGC_DEFS
/// Copyright by Syntacore LLC © 2016-2018. See LICENSE for details
/// @file       <scr1_dbgc.svh>
/// @brief      DBGC header file
///

`include "scr1_arch_description.svh"

`ifdef SCR1_DBGC_EN
//======================================================================================================================
// Parameters
//======================================================================================================================
localparam int SCR1_DBGC_DAP_CH_ID_WIDTH            = 3;
localparam int SCR1_DBGC_DAP_UNIT_ID_WIDTH          = 2;
localparam int SCR1_DBGC_DAP_FGROUP_WIDTH           = 2;
localparam int SCR1_DBGC_DAP_HEADER_REG_WIDTH       = 4;
localparam int SCR1_DBGC_DAP_DATA_REG_WIDTH         = 32;
localparam int SCR1_DBGC_DAP_CTRL_REG_WIDTH         = SCR1_DBGC_DAP_HEADER_REG_WIDTH;
localparam int SCR1_DBGC_DAP_OPCODE_REG_WIDTH       = SCR1_DBGC_DAP_HEADER_REG_WIDTH;
localparam int SCR1_DBGC_DAP_OPSTAT_REG_WIDTH       = SCR1_DBGC_DAP_HEADER_REG_WIDTH;
localparam int SCR1_DBGC_DAP_OPCODE_EXT_REG_WIDTH   = SCR1_DBGC_DAP_DATA_REG_WIDTH;
//localparam int SCR1_DBGC_DAP_DBG_ID_REG_WIDTH       = SCR1_DBGC_DAP_DATA_REG_WIDTH;
localparam int SCR1_DBGC_DBG_DATA_REG_WIDTH         = SCR1_DBGC_DAP_DATA_REG_WIDTH;
localparam int SCR1_DBGC_FSM_OPCODE_WIDTH           = 2;
localparam int SCR1_DBGC_FSM_STATE_WIDTH            = 2;
localparam int SCR1_DBGC_FSM_DDR_IN_SEL_WIDTH       = 2;
localparam int SCR1_DBGC_REGBLOCK_INDEX_WIDTH       = (SCR1_DBGC_DAP_OPCODE_REG_WIDTH - 1);
localparam int SCR1_DBGC_DBG_CORE_INSTR_WIDTH       = SCR1_DBGC_DAP_DATA_REG_WIDTH;
localparam int SCR1_DBGC_WB_FIFO_INDEX_WIDTH        = 3;

localparam bit [SCR1_DBGC_DAP_DATA_REG_WIDTH-1:0]   SCR1_DBGC_DAP_DBG_ID_VALUE      = 32'h00820000;
`ifdef SCR1_BRKM_EN
localparam bit [SCR1_DBGC_DAP_DATA_REG_WIDTH-1:0]   SCR1_DBGC_DAP_TARGET_ID_VALUE   = 32'h01801000;
`else // SCR1_BRKM_EN
localparam bit [SCR1_DBGC_DAP_DATA_REG_WIDTH-1:0]   SCR1_DBGC_DAP_TARGET_ID_VALUE   = 32'h01001000;
`endif // SCR1_BRKM_EN


//======================================================================================================================
// DAP Definitions
//======================================================================================================================
typedef enum logic [SCR1_DBGC_DAP_CH_ID_WIDTH-1 : 0] {
    SCR1_DAP_CHAIN_ID_DBG_ID,
    SCR1_DAP_CHAIN_ID_DBG_STATUS,
    SCR1_DAP_CHAIN_ID_DAP_CTRL,
    SCR1_DAP_CHAIN_ID_DAP_CTRL_RD,
    SCR1_DAP_CHAIN_ID_DAP_CMD,
    SCR1_DAP_CHAIN_ID_DBG_PIPE_STS,
    SCR1_DAP_CHAIN_ID_TARGET_ID,
    SCR1_DAP_CHAIN_ID_XXX        = 'X
} type_scr1_dap_chain_id_e;

//-------------------------------------------------------------------------------
// DAP OpStatus
//-------------------------------------------------------------------------------
typedef struct packed {
    logic   ready;
    logic   lock;
    logic   error;
    logic   except;
} type_scr1_dbgc_dap_opstatus_s;

//-------------------------------------------------------------------------------
// DAP Control Reg
//-------------------------------------------------------------------------------
typedef enum logic [SCR1_DBGC_DAP_UNIT_ID_WIDTH-1 : 0] {
    SCR1_DBGC_UNIT_ID_HART_0,
    SCR1_DBGC_UNIT_ID_HART_1,
    SCR1_DBGC_UNIT_ID_RSVD,
    SCR1_DBGC_UNIT_ID_CORE,
    SCR1_DBGC_UNIT_ID_XXX    = 'X
} type_scr1_dbgc_unit_id_e;

typedef enum logic [SCR1_DBGC_DAP_FGROUP_WIDTH-1 : 0] {
    SCR1_DBGC_FGRP_CORE_REGTRANS,
    SCR1_DBGC_FGRP_CORE_XXX  = 'X
} type_scr1_dbgc_core_fgroup_e;

typedef enum logic [SCR1_DBGC_DAP_FGROUP_WIDTH-1 : 0] {
    SCR1_DBGC_FGRP_HART_REGTRANS,
    SCR1_DBGC_FGRP_HART_DBGCMD,
    SCR1_DBGC_FGRP_HART_CSR_CAP,
    SCR1_DBGC_FGRP_HART_XXX  = 'X
} type_scr1_dbgc_hart_fgroup_e;

typedef struct packed {
    logic [SCR1_DBGC_DAP_UNIT_ID_WIDTH-1 : 0]       unit;
    logic [SCR1_DBGC_DAP_FGROUP_WIDTH-1 : 0]        fgrp;
} type_scr1_dap_ctrl_reg_s;

//-------------------------------------------------------------------------------
// DAP Command
//-------------------------------------------------------------------------------

// DAPCMD :: Register Transfer (REGTRANS)
typedef struct packed {
    logic                                           write;
    logic [SCR1_DBGC_REGBLOCK_INDEX_WIDTH-1:0]      index;
} type_scr1_dbgc_dap_cmd_opcode_regtrans_s;

// DAPCMD :: Debug Command (DBGCMD)
typedef enum logic [SCR1_DBGC_DAP_OPCODE_REG_WIDTH-1:0] {
    SCR1_DBGC_DAP_OPCODE_DBGCMD_DBG_CTRL            = 4'h0,
    SCR1_DBGC_DAP_OPCODE_DBGCMD_CORE_EXEC           = 4'h1,
    SCR1_DBGC_DAP_OPCODE_DBGCMD_DBGDATA_WR          = 4'h2,
    SCR1_DBGC_DAP_OPCODE_DBGCMD_UNLOCK              = 4'h3,
    SCR1_DBGC_DAP_OPCODE_DBGCMD_XXX                 = 'X
} type_scr1_dbgc_dap_cmd_opcode_dbgcmd_e;

// DAPCMD :: DBGCMD :: DBG_CTRL :: Debug Control Extension Command (DBGCTRL_EXT)
typedef struct packed {
    logic [SCR1_DBGC_DAP_OPCODE_EXT_REG_WIDTH-4:0]  rsrv;
    logic                                           sticky_clr;
    logic                                           dm_resume;
    logic                                           dm_halt;
} type_scr1_dbgc_dap_cmd_opcode_dbgctrl_ext_s;


//======================================================================================================================
// DBGC-HART I/F Definitions
//======================================================================================================================
//-------------------------------------------------------------------------------
// Debug Run Control I/F
//-------------------------------------------------------------------------------
typedef enum logic {
    SCR1_DBGC_HART_RUN_MODE         = 1'b0,
    SCR1_DBGC_HART_DBG_MODE         = 1'b1,
    SCR1_DBGC_HART_XXX_MODE         = 1'bX
} type_scr1_dbgc_hart_dbg_mode_e;

typedef enum logic {
    SCR1_DBGC_HART_IRQ_DSBL_NORMAL  = 1'b0,
    SCR1_DBGC_HART_IRQ_DSBL_ACTIVE  = 1'b1,
    SCR1_DBGC_HART_IRQ_DSBL_XXX     = 1'bX
} type_scr1_dbgc_hart_irq_dsbl_e;

typedef enum logic {
    SCR1_DBGC_HART_FETCH_SRC_NORMAL = 1'b0,
    SCR1_DBGC_HART_FETCH_SRC_DBGC   = 1'b1,
    SCR1_DBGC_HART_FETCH_SRC_XXX    = 1'bX
} type_scr1_dbgc_hart_fetch_src_e;

// Structure for Debug Mode Redirection Control options (Debug Mode Enable bits, part of Hart RunControl)
typedef struct packed {
    logic rst_brk;      // Reset Break: 1 - core after leaving of RESET state must enter Debug Mode (w/o instruction fetching)
    logic sstep;        // Single Step: 1 - halt after single step (single instruction completion)
    logic brkpt;        // Breakpoint:  1 - halt after Breakpoint Exception
} type_scr1_dbgc_dmode_en_s;

typedef struct packed {
    type_scr1_dbgc_hart_irq_dsbl_e  irq_dsbl;       // 0 - normal, as per core architectural state, 1 - IRQs disabled
    type_scr1_dbgc_hart_fetch_src_e fetch_src;      // 0 - normal (from FETCH unit), 1 - from DBGC
    logic                           pc_advmt_dsbl;  // 0 - normal, Program Counter (PC) advancement during Run Mode
    type_scr1_dbgc_dmode_en_s       dmode_en;       // Debug Mode Enable: Set of conditions for Debug Mode entering (requested)
    logic                           brkpt_hw_dsbl;  // 0 - normal HW breakpoints behavior (BRKM functions regularly);
                                                    // 1 - HW breakpoints are disabled (overrides BRKM settings).
} type_scr1_dbgc_hart_runctrl_s;

//-------------------------------------------------------------------------------
// Hart Debug State I/F
//-------------------------------------------------------------------------------
// Structure for Debug Mode Cause (status)
typedef struct packed {
    logic                       enforce;        // Enforce Break: 1 - halted due to enforcement from external source (e.g., debug cable)
    logic                       rst_brk;        // Reset Break:   1 - halted after RESET state leaving
    logic                       sstep;          // Single Step:   1 - halted after single step
    logic                       brkpt;          // Breakpoint:    1 - halted after Breakpoint Exception
    logic                       brkpt_hw;       // Hardware Breakpoint: 1 - halted after Breakpoint Exception from BRKM
} type_scr1_dbgc_dbghalt_s;

typedef struct packed {
    logic                       error;          // 1 - fatal core error
    logic                       halted;         // 1 - core halted, 0 - core running
    logic                       except;         // 1 - core exception
    logic                       commit;         // 1 - instruction retirement was accompanied with results commit to arch.state
    logic                       timeout;        // 1 - time-out occured during an operation
    type_scr1_dbgc_dbghalt_s    dmode_cause;    // Debug Mode Cause: Set of reasons of Debug Mode entering (reported)
} type_scr1_dbgc_hart_state_s;


//======================================================================================================================
// DBGC Internal Logic Definitions
//======================================================================================================================
typedef struct packed {
    logic                       ctrl;
    logic                       dmode_en;
    logic                       dcir;           // Debug Core Instruction Register (DBG_CORE_INSTR_REG, DCIR)
    logic                       ddr;            // Debug Data Register (DBG_DATA_REG, DDR)
} type_scr1_dbgc_hart_reg_sel_s;

typedef struct packed {
    logic                       ctrl;
    logic                       sts;
} type_scr1_dbgc_core_reg_sel_s;

typedef enum logic [SCR1_DBGC_FSM_OPCODE_WIDTH-1:0] {
    SCR1_DBGC_FSM_OPCODE_REGTRANS,
    SCR1_DBGC_FSM_OPCODE_DBGCTRL,
    SCR1_DBGC_FSM_OPCODE_CORE_EXEC,
    SCR1_DBGC_FSM_OPCODE_UNLOCK,
    SCR1_DBGC_FSM_OPCODE_XXX        = 'X
} type_scr1_dbgc_fsm_opcode_e;

typedef enum logic [SCR1_DBGC_FSM_STATE_WIDTH-1 : 0] {
    SCR1_DBGC_FSM_STATE_IDLE,
    SCR1_DBGC_FSM_STATE_CMD_INT,
    SCR1_DBGC_FSM_STATE_CMD_EXT,
    SCR1_DBGC_FSM_STATE_WAIT_EXT,
    SCR1_DBGC_FSM_STATE_XXX         = 'X
} type_scr1_dbgc_fsm_state_e;

typedef enum logic [SCR1_DBGC_FSM_DDR_IN_SEL_WIDTH-1 : 0] {
    SCR1_DBGC_FSM_DDR_IN_SEL_DAP,
    SCR1_DBGC_FSM_DDR_IN_SEL_DBGC,
    SCR1_DBGC_FSM_DDR_IN_SEL_CORE,
    SCR1_DBGC_FSM_DDR_IN_SEL_LOCK,
    SCR1_DBGC_FSM_DDR_IN_SEL_XXX    = 'X
} type_scr1_dbgc_fsm_ddr_input_sel_e;


typedef struct packed {
    type_scr1_dap_ctrl_reg_s                     dap_ctrl;
    logic [SCR1_DBGC_DAP_OPCODE_REG_WIDTH-1:0]   dap_opcode;
    type_scr1_dbgc_fsm_opcode_e                  fsm_opcode;
    logic [SCR1_DBGC_DBG_DATA_REG_WIDTH-$bits(type_scr1_dap_ctrl_reg_s)-SCR1_DBGC_DAP_OPCODE_REG_WIDTH-$bits(type_scr1_dbgc_fsm_opcode_e)-1:0] rsrv;
} type_scr1_dbgc_lock_context_s;

//======================================================================================================================
// DBGC Registers Definitions
//======================================================================================================================

//-------------------------------------------------------------------------------
// Register Map
//-------------------------------------------------------------------------------
typedef enum logic [SCR1_DBGC_REGBLOCK_INDEX_WIDTH-1:0] {
    SCR1_DBGC_CORE_REGS_DEBUG_ID     = 3'h0,
    SCR1_DBGC_CORE_REGS_DBG_CTRL     = 3'h1,
    SCR1_DBGC_CORE_REGS_DBG_STS      = 3'h2,
    //SCR1_DBGC_CORE_REGS_DBG_CMD      = 3'h3,// Not implemented yet
    SCR1_DBGC_CORE_REGS_DBG_PIPE_STS = 3'h4,
    SCR1_DBGC_CORE_REGS_DBG_TGT_ID   = 3'h5,
    SCR1_DBGC_CORE_REGS_XXX          = 'X
} type_scr1_dbgc_regblock_core_e;

typedef enum logic [SCR1_DBGC_REGBLOCK_INDEX_WIDTH-1:0] {
    SCR1_DBGC_HART_REGS_DBG_CTRL     = 3'h0,
    SCR1_DBGC_HART_REGS_DBG_STS      = 3'h1,
    SCR1_DBGC_HART_REGS_DMODE_ENBL   = 3'h2,
    SCR1_DBGC_HART_REGS_DMODE_CAUSE  = 3'h3,
    SCR1_DBGC_HART_REGS_CORE_INSTR   = 3'h4,
    SCR1_DBGC_HART_REGS_DBG_DATA     = 3'h5,
    SCR1_DBGC_HART_REGS_PC_SAMPLE    = 3'h6,
    SCR1_DBGC_HART_REGS_XXX          = 'X
} type_scr1_dbgc_regblock_hart_e;

typedef enum logic [SCR1_DBGC_REGBLOCK_INDEX_WIDTH-1:0] {
    SCR1_DBGC_HART_CSRS_MVENDORID   = 3'h0,
    SCR1_DBGC_HART_CSRS_MARCHID     = 3'h1,
    SCR1_DBGC_HART_CSRS_MIMPID      = 3'h2,
    SCR1_DBGC_HART_CSRS_MHARTID     = 3'h3,
    SCR1_DBGC_HART_CSRS_MISA        = 3'h4,
    SCR1_DBGC_HART_CSRS_XXX         = 'X
} type_scr1_dbgc_regblock_hart_csrro_e;


//-------------------------------------------------------------------------------
// Core Debug Registers
//-------------------------------------------------------------------------------

// Core Debug Control Register (CORE_DBG_CTRL, CDCR)
typedef enum int {
    SCR1_DBGC_CORE_CDCR_HART0_RST_BIT       = 0,
    SCR1_DBGC_CORE_CDCR_RSRV0_BIT_R         = 1,
    SCR1_DBGC_CORE_CDCR_RSRV0_BIT_L         = 7,
    SCR1_DBGC_CORE_CDCR_HART1_RST_BIT       = 8,
    SCR1_DBGC_CORE_CDCR_RSRV1_BIT_R         = 9,
    SCR1_DBGC_CORE_CDCR_RSRV1_BIT_L         = 15,
    SCR1_DBGC_CORE_CDCR_RSRV2_BIT_R         = 16,
    SCR1_DBGC_CORE_CDCR_RSRV2_BIT_L         = 23,
    SCR1_DBGC_CORE_CDCR_RST_BIT             = 24,
    SCR1_DBGC_CORE_CDCR_IRQ_DSBL_BIT        = 25,
    SCR1_DBGC_CORE_CDCR_RSRV3_BIT_R         = 26,
    SCR1_DBGC_CORE_CDCR_RSRV3_BIT_L         = SCR1_DBGC_DAP_DATA_REG_WIDTH-1
} type_scr1_dbgc_core_dbg_ctrl_reg_bits_e;

typedef struct packed {
    logic [SCR1_DBGC_CORE_CDCR_RSRV0_BIT_L-SCR1_DBGC_CORE_CDCR_RSRV0_BIT_R:0] rsrv;
    logic                                   rst;
} type_scr1_dbgc_core_dbg_ctrl_reg_hart_s;

typedef struct packed {
    logic [SCR1_DBGC_CORE_CDCR_RSRV3_BIT_L-SCR1_DBGC_CORE_CDCR_RSRV3_BIT_R:0] rsrv3;
    logic                                   irq_dsbl;
    logic                                   rst;
    logic [SCR1_DBGC_CORE_CDCR_RSRV2_BIT_L-SCR1_DBGC_CORE_CDCR_RSRV2_BIT_R:0] rsrv2;
    type_scr1_dbgc_core_dbg_ctrl_reg_hart_s [1:0]   hart;
} type_scr1_dbgc_core_dbg_ctrl_reg_s;

// Core Debug Status Register (CORE_DBG_STS, CDSR)
typedef enum int {
    SCR1_DBGC_CORE_CDSR_HART0_DMODE_BIT      = 0,
    SCR1_DBGC_CORE_CDSR_HART0_RST_BIT        = 1,
    SCR1_DBGC_CORE_CDSR_HART0_RST_STKY_BIT   = 2,
    SCR1_DBGC_CORE_CDSR_HART0_ERR_BIT        = 3,
    SCR1_DBGC_CORE_CDSR_HART0_ERR_STKY_BIT   = 4,
    SCR1_DBGC_CORE_CDSR_RSRV0_BIT            = 5,
    SCR1_DBGC_CORE_CDSR_HART0_PLVL_BIT_R     = 6,
    SCR1_DBGC_CORE_CDSR_HART0_PLVL_BIT_L     = 7,
    SCR1_DBGC_CORE_CDSR_HART1_DMODE_BIT      = 8,
    SCR1_DBGC_CORE_CDSR_HART1_RST_BIT        = 9,
    SCR1_DBGC_CORE_CDSR_HART1_RST_STKY_BIT   = 10,
    SCR1_DBGC_CORE_CDSR_HART1_ERR_BIT        = 11,
    SCR1_DBGC_CORE_CDSR_HART1_ERR_STKY_BIT   = 12,
    SCR1_DBGC_CORE_CDSR_RSRV1_BIT            = 13,
    SCR1_DBGC_CORE_CDSR_HART1_PLVL_BIT_R     = 14,
    SCR1_DBGC_CORE_CDSR_HART1_PLVL_BIT_L     = 15,
    SCR1_DBGC_CORE_CDSR_ERR_BIT              = 16,
    SCR1_DBGC_CORE_CDSR_ERR_STKY_BIT         = 17,
    SCR1_DBGC_CORE_CDSR_ERR_HWCORE_BIT       = 18,
    SCR1_DBGC_CORE_CDSR_ERR_FSMBUSY_BIT      = 19,
    SCR1_DBGC_CORE_CDSR_ERR_DAP_OPCODE_BIT   = 20,
    SCR1_DBGC_CORE_CDSR_RSRV2_BIT_R          = 21,
    SCR1_DBGC_CORE_CDSR_RSRV2_BIT_L          = SCR1_DBGC_DAP_DATA_REG_WIDTH-5,// Bit 27
    SCR1_DBGC_CORE_CDSR_RST_BIT              = SCR1_DBGC_DAP_DATA_REG_WIDTH-4,
    SCR1_DBGC_CORE_CDSR_RST_STKY_BIT         = SCR1_DBGC_DAP_DATA_REG_WIDTH-3,
    SCR1_DBGC_CORE_CDSR_LOCK_BIT             = SCR1_DBGC_DAP_DATA_REG_WIDTH-2,
    SCR1_DBGC_CORE_CDSR_READY_BIT            = SCR1_DBGC_DAP_DATA_REG_WIDTH-1
} type_scr1_dbgc_core_dbg_sts_reg_bits_e;

typedef struct packed {
    logic [1:0] plvl;
    logic       rsrv;
    logic       err_sticky;
    logic       err;
    logic       rst_sticky;
    logic       rst;
    type_scr1_dbgc_hart_dbg_mode_e   dmode;
} type_scr1_dbgc_core_dbg_sts_reg_hart_s;

typedef struct packed {
    logic       ready;
    logic       lock;
    logic       rst_sticky;
    logic       rst;
    logic [SCR1_DBGC_CORE_CDSR_RSRV2_BIT_L-SCR1_DBGC_CORE_CDSR_RSRV2_BIT_R:0] rsrv2;
    logic       err_dap_opcode;
    logic       err_fsm_busy;
    logic       err_hwcore;
    logic       err_sticky;
    logic       err;
    type_scr1_dbgc_core_dbg_sts_reg_hart_s [1:0]                         hart;
} type_scr1_dbgc_core_dbg_sts_reg_s;

typedef struct packed {
    logic       ifetch;
    logic       id;
    logic       ialu;
    logic       cfu;
    logic       lsu;
`ifdef SCR1_RVM_EXT
    logic       mdu;
`endif //SCR1_RVM_EXT
`ifdef SCR1_RVF_EXT
    logic       fpu;
`endif //SCR1_RVF_EXT
    logic [2:0] wb_cnt;
} type_scr1_dbgc_core_busy_s;

// Core Debug Pipeline Status Register (CORE_DBG_PIPE_STS, CDPSR)
typedef enum int {
    SCR1_DBGC_CORE_CDPSR_BUSY_IF_BIT        = 0,
    SCR1_DBGC_CORE_CDPSR_BUSY_ID_BIT        = 1,
    SCR1_DBGC_CORE_CDPSR_BUSY_CFU_BIT       = 2,
    SCR1_DBGC_CORE_CDPSR_BUSY_LSU_BIT       = 3,
    SCR1_DBGC_CORE_CDPSR_BUSY_IALU_BIT      = 4,
    SCR1_DBGC_CORE_CDPSR_BUSY_MDU_BIT       = 5,
    SCR1_DBGC_CORE_CDPSR_BUSY_FPU_BIT       = 6,
    SCR1_DBGC_CORE_CDPSR_RSRV0_BIT_R        = 7,
    SCR1_DBGC_CORE_CDPSR_RSRV0_BIT_L        = 11,
    SCR1_DBGC_CORE_CDPSR_BUSY_WB_CNT_BIT_R  = 12,
    SCR1_DBGC_CORE_CDPSR_BUSY_WB_CNT_BIT_L  = SCR1_DBGC_CORE_CDPSR_BUSY_WB_CNT_BIT_R+SCR1_DBGC_WB_FIFO_INDEX_WIDTH-1,
    SCR1_DBGC_CORE_CDPSR_RSRV1_BIT_R        = SCR1_DBGC_CORE_CDPSR_BUSY_WB_CNT_BIT_L+1,
    SCR1_DBGC_CORE_CDPSR_RSRV1_BIT_L        = SCR1_DBGC_DAP_DATA_REG_WIDTH-1
} type_scr1_dbgc_core_dbg_pipe_sts_reg_bits_e;

typedef struct packed {
    logic [SCR1_DBGC_CORE_CDPSR_BUSY_WB_CNT_BIT_L-SCR1_DBGC_CORE_CDPSR_BUSY_WB_CNT_BIT_R:0] wb_cnt;
    logic [SCR1_DBGC_CORE_CDPSR_RSRV0_BIT_L-SCR1_DBGC_CORE_CDPSR_RSRV0_BIT_R:0]             rsrv0;
    logic       fpu;
    logic       mdu;
    logic       ialu;
    logic       lsu;
    logic       cfu;
    logic       id;
    logic       ifetch;
} type_scr1_dbgc_core_dbg_pipe_sts_busy_reg_s;

typedef struct packed {
    logic [SCR1_DBGC_CORE_CDPSR_RSRV1_BIT_L-SCR1_DBGC_CORE_CDPSR_RSRV1_BIT_R:0] rsrv0;
    type_scr1_dbgc_core_dbg_pipe_sts_busy_reg_s                                 busy;
} type_scr1_dbgc_core_dbg_pipe_sts_reg_s;

// Core Debug Target ID Register (CORE_DBG_TARGET_ID, CDTIR)
// TBD.

//-------------------------------------------------------------------------------
// Hart Debug Registers
//-------------------------------------------------------------------------------

// Hart Debug Control Register (HART_DBG_CTRL, HDCR)
typedef enum int {
    SCR1_DBGC_HART_HDCR_RST_BIT              = 0,
    SCR1_DBGC_HART_HDCR_RSRV0_BIT_R          = 1,
    SCR1_DBGC_HART_HDCR_RSRV0_BIT_L          = 5,
    SCR1_DBGC_HART_HDCR_PC_ADVMT_DSBL_BIT    = 6,
    SCR1_DBGC_HART_HDCR_RSRV1_BIT_R          = 7,
    SCR1_DBGC_HART_HDCR_RSRV1_BIT_L          = SCR1_DBGC_DAP_DATA_REG_WIDTH-1
} type_scr1_dbgc_hart_dbg_ctrl_reg_bits_e;

typedef struct packed {
    logic [SCR1_DBGC_HART_HDCR_RSRV1_BIT_L-SCR1_DBGC_HART_HDCR_RSRV1_BIT_R:0] rsrv1;
    logic       pc_advmt_dsbl;
    logic [SCR1_DBGC_HART_HDCR_RSRV0_BIT_L-SCR1_DBGC_HART_HDCR_RSRV0_BIT_R:0] rsrv0;
    logic       rst;
} type_scr1_dbgc_hart_dbg_ctrl_reg_s;

// Hart Debug Status Register (HART_DBG_STS, HDSR)
typedef enum int {
    SCR1_DBGC_HART_HDSR_DMODE_BIT            = 0,
    SCR1_DBGC_HART_HDSR_RST_BIT              = 1,
    SCR1_DBGC_HART_HDSR_RST_STKY_BIT         = 2,
    SCR1_DBGC_HART_HDSR_EXCEPT_BIT           = 3,
    SCR1_DBGC_HART_HDSR_PLVL_BIT_R           = 4,
    SCR1_DBGC_HART_HDSR_PLVL_BIT_L           = 5,
    SCR1_DBGC_HART_HDSR_RSRV0_BIT_R          = 6,
    SCR1_DBGC_HART_HDSR_RSRV0_BIT_L          = 15,
    SCR1_DBGC_HART_HDSR_ERR_BIT              = 16,
    SCR1_DBGC_HART_HDSR_ERR_HWTHREAD_BIT     = 17,
    SCR1_DBGC_HART_HDSR_ERR_DAP_OPCODE_BIT   = 18,
    SCR1_DBGC_HART_HDSR_ERR_DBGCMD_NACK_BIT  = 19,
    SCR1_DBGC_HART_HDSR_ERR_ILLEG_DBG_CONTEXT_BIT = 20,
    SCR1_DBGC_HART_HDSR_ERR_UNEXP_RESET_BIT  = 21,
    SCR1_DBGC_HART_HDSR_ERR_TIMEOUT_BIT      = 22,
    SCR1_DBGC_HART_HDSR_RSRV1_BIT_R          = 23,
    SCR1_DBGC_HART_HDSR_RSRV1_BIT_L          = SCR1_DBGC_DAP_DATA_REG_WIDTH-2,// Bit 30
    SCR1_DBGC_HART_HDSR_LOCK_STKY_BIT        = SCR1_DBGC_DAP_DATA_REG_WIDTH-1
} type_scr1_dbgc_hart_dbg_sts_reg_bits_e;

typedef struct packed {
    logic       lock_sticky;
    logic [SCR1_DBGC_HART_HDSR_RSRV1_BIT_L-SCR1_DBGC_HART_HDSR_RSRV1_BIT_R:0] rsrv1;
    logic       err_timeout;
    logic       err_unexp_reset;
    logic       err_illeg_dbg_context;
    logic       err_dbgcmd_nack;
    logic       err_dap_opcode;
    logic       err_hwthread;
    logic       err;
    logic [SCR1_DBGC_HART_HDSR_RSRV0_BIT_L-SCR1_DBGC_HART_HDSR_RSRV0_BIT_R:0] rsrv0;
    logic [1:0] plvl;
    logic       except;
    logic       rst_sticky;
    logic       rst;
    logic       dmode;
} type_scr1_dbgc_hart_dbg_sts_reg_s;

// Hart Debug Mode Enable Register (HART_DMODE_ENBL, HDMER)
typedef enum int {
    SCR1_DBGC_HART_HDMER_RSRV0_BIT_R         = 0,
    SCR1_DBGC_HART_HDMER_RSRV0_BIT_L         = 2,
    SCR1_DBGC_HART_HDMER_SW_BRKPT_BIT        = 3,
    SCR1_DBGC_HART_HDMER_RSRV1_BIT_R         = 4,
    SCR1_DBGC_HART_HDMER_RSRV1_BIT_L         = SCR1_DBGC_DAP_DATA_REG_WIDTH-5,
    SCR1_DBGC_HART_HDMER_SINGLE_STEP_BIT     = SCR1_DBGC_DAP_DATA_REG_WIDTH-4,
    SCR1_DBGC_HART_HDMER_RST_ENTR_BRK_BIT    = SCR1_DBGC_DAP_DATA_REG_WIDTH-3, //! Not implemented, Reserved for future use
    SCR1_DBGC_HART_HDMER_RST_EXIT_BRK_BIT    = SCR1_DBGC_DAP_DATA_REG_WIDTH-2,
    SCR1_DBGC_HART_HDMER_RSRV2_BIT           = SCR1_DBGC_DAP_DATA_REG_WIDTH-1
} type_scr1_dbgc_hart_dmode_enbl_reg_bits_e;

typedef struct packed {
    logic       rsrv2;
    logic       rst_exit_brk;
    logic       rst_entr_brk; //! Not implemented, Reserved for future use
    logic       sstep;
    logic [SCR1_DBGC_HART_HDMER_RSRV1_BIT_L-SCR1_DBGC_HART_HDMER_RSRV1_BIT_R:0] rsrv1;
    logic       brkpt;
    logic [SCR1_DBGC_HART_HDMER_RSRV0_BIT_L-SCR1_DBGC_HART_HDMER_RSRV0_BIT_R:0] rsrv0;
} type_scr1_dbgc_hart_dmode_enbl_reg_s;

// Hart Debug Mode Cause Register (HART_DMODE_CAUSE, HDMCR)
typedef enum int {
    SCR1_DBGC_HART_HDMCR_RSRV0_BIT_R         = 0,
    SCR1_DBGC_HART_HDMCR_RSRV0_BIT_L         = 2,
    SCR1_DBGC_HART_HDMCR_SW_BRKPT_BIT        = 3,
    SCR1_DBGC_HART_HDMCR_RSRV1_BIT_R         = 4,
    SCR1_DBGC_HART_HDMCR_RSRV1_BIT_L         = SCR1_DBGC_DAP_DATA_REG_WIDTH-6,
    SCR1_DBGC_HART_HDMCR_HW_BRKPT_BIT        = SCR1_DBGC_DAP_DATA_REG_WIDTH-5,
    SCR1_DBGC_HART_HDMCR_SINGLE_STEP_BIT     = SCR1_DBGC_DAP_DATA_REG_WIDTH-4,
    SCR1_DBGC_HART_HDMCR_RST_ENTR_BRK_BIT    = SCR1_DBGC_DAP_DATA_REG_WIDTH-3,
    SCR1_DBGC_HART_HDMCR_RST_EXIT_BRK_BIT    = SCR1_DBGC_DAP_DATA_REG_WIDTH-2,
    SCR1_DBGC_HART_HDMCR_ENFORCE_BIT         = SCR1_DBGC_DAP_DATA_REG_WIDTH-1
} type_scr1_dbgc_hart_dmode_cause_reg_bits_e;

typedef struct packed {
    logic       enforce;
    logic       rst_exit_brk;
    logic       rst_entr_brk;
    logic       sstep;
    logic       brkpt_hw;
    logic [SCR1_DBGC_HART_HDMCR_RSRV1_BIT_L-SCR1_DBGC_HART_HDMCR_RSRV1_BIT_R:0] rsrv1;
    logic       brkpt;
    logic [SCR1_DBGC_HART_HDMCR_RSRV0_BIT_L-SCR1_DBGC_HART_HDMCR_RSRV0_BIT_R:0] rsrv0;
} type_scr1_dbgc_hart_dmode_cause_reg_s;

`endif // SCR1_DBGC_EN
`endif // SCR1_INCLUDE_DBGC_DEFS