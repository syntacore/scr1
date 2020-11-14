/// Copyright by Syntacore LLC © 2016-2020. See LICENSE for details
/// @file       <scr1_scu.svh>
/// @brief      SCU header file
///

`ifndef SCR1_INCLUDE_SCU_DEFS
`define SCR1_INCLUDE_SCU_DEFS

//`include "scr1_arch_description.svh"

`ifdef SCR1_DBG_EN

//==============================================================================
// Parameters
//==============================================================================
localparam int unsigned         SCR1_SCU_DR_SYSCTRL_OP_WIDTH        = 2;
localparam int unsigned         SCR1_SCU_DR_SYSCTRL_ADDR_WIDTH      = 2;
localparam int unsigned         SCR1_SCU_DR_SYSCTRL_DATA_WIDTH      = 4;

//==============================================================================
// Types
//==============================================================================
typedef enum logic [SCR1_SCU_DR_SYSCTRL_OP_WIDTH-1:0] {
    SCR1_SCU_SYSCTRL_OP_WRITE       = 2'h0,
    SCR1_SCU_SYSCTRL_OP_READ        = 2'h1,
    SCR1_SCU_SYSCTRL_OP_SETBITS     = 2'h2,
    SCR1_SCU_SYSCTRL_OP_CLRBITS     = 2'h3,
    SCR1_SCU_SYSCTRL_OP_XXX         = 'X
} type_scr1_scu_sysctrl_op_e;

typedef enum logic [SCR1_SCU_DR_SYSCTRL_ADDR_WIDTH-1:0] {
    SCR1_SCU_SYSCTRL_ADDR_CONTROL   = 2'h0,
    SCR1_SCU_SYSCTRL_ADDR_MODE      = 2'h1,
    SCR1_SCU_SYSCTRL_ADDR_STATUS    = 2'h2,
    SCR1_SCU_SYSCTRL_ADDR_STICKY    = 2'h3,
    SCR1_SCU_SYSCTRL_ADDR_XXX       = 'X
} type_scr1_scu_sysctrl_addr_e;

typedef struct packed {
    logic [SCR1_SCU_DR_SYSCTRL_DATA_WIDTH-1:0]  data;
    logic [SCR1_SCU_DR_SYSCTRL_ADDR_WIDTH-1:0]  addr;
    logic [SCR1_SCU_DR_SYSCTRL_OP_WIDTH-1:0]    op;
} type_scr1_scu_sysctrl_dr_s;

typedef enum int unsigned {
    SCR1_SCU_DR_SYSCTRL_OP_BIT_R                  = 'h0,
    SCR1_SCU_DR_SYSCTRL_OP_BIT_L                  = SCR1_SCU_DR_SYSCTRL_OP_WIDTH-1,
    SCR1_SCU_DR_SYSCTRL_ADDR_BIT_R                = SCR1_SCU_DR_SYSCTRL_OP_WIDTH,
    SCR1_SCU_DR_SYSCTRL_ADDR_BIT_L                = SCR1_SCU_DR_SYSCTRL_OP_WIDTH +
                                                    SCR1_SCU_DR_SYSCTRL_ADDR_WIDTH - 1,
    SCR1_SCU_DR_SYSCTRL_DATA_BIT_R                = SCR1_SCU_DR_SYSCTRL_OP_WIDTH +
                                                    SCR1_SCU_DR_SYSCTRL_ADDR_WIDTH,
    SCR1_SCU_DR_SYSCTRL_DATA_BIT_L                = SCR1_SCU_DR_SYSCTRL_OP_WIDTH +
                                                    SCR1_SCU_DR_SYSCTRL_ADDR_WIDTH +
                                                    SCR1_SCU_DR_SYSCTRL_DATA_WIDTH - 1
} type_scr1_scu_sysctrl_dr_bits_e;

typedef struct packed {
    logic [1:0]                                     rsrv;
    logic                                           core_reset;
    logic                                           sys_reset;
} type_scr1_scu_sysctrl_control_reg_s;

typedef struct packed {
    logic [1:0]                                     rsrv;
    logic                                           hdu_rst_bhv;
    logic                                           dm_rst_bhv;
} type_scr1_scu_sysctrl_mode_reg_s;

typedef struct packed {
    logic                                           hdu_reset;
    logic                                           dm_reset;
    logic                                           core_reset;
    logic                                           sys_reset;
} type_scr1_scu_sysctrl_status_reg_s;

`endif // SCR1_DBG_EN
`endif // SCR1_INCLUDE_SCU_DEFS
