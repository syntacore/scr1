`ifndef SCR1_ARCH_DESCRIPTION_SVH
`define SCR1_ARCH_DESCRIPTION_SVH
/// Copyright by Syntacore LLC © 2016, 2017. See LICENSE for details
/// @file       <scr1_arch_description.svh>
/// @brief      Architecture Description File
///

//-------------------------------------------------------------------------------
// Core configurable parameters
//-------------------------------------------------------------------------------
`define SCR1_BUILD_ID               32'h17050800

//`define SCR1_RVE_EXT                // enables RV32E base integer instruction set
`define SCR1_RVM_EXT                // enables standard extension for integer mul/div
`define SCR1_RVC_EXT                // enables standard extension for compressed instructions

`define SCR1_IFU_QUEUE_BYPASS       // enables bypass between IFU and IDU stages
`define SCR1_EXU_STAGE_BYPASS       // enables bypass between IDU and EXU stages

`define SCR1_FAST_MUL               // enables one-cycle multiplication

`define SCR1_CLKCTRL_EN             // enables global clock gating

`define SCR1_DBGC_EN                // enables debug controller
`define SCR1_BRKM_EN                // enables breakpoint module
`define SCR1_IPIC_EN                // enables interrupt controller

//-------------------------------------------------------------------------------
// Core read-only parameters (do not modify)
//-------------------------------------------------------------------------------
`define SCR1_XLEN               32
`define SCR1_FLEN               `SCR1_XLEN      // for test compatibility
`define SCR1_IMEM_AWIDTH        `SCR1_XLEN
`define SCR1_IMEM_DWIDTH        `SCR1_XLEN
`define SCR1_DMEM_AWIDTH        `SCR1_XLEN
`define SCR1_DMEM_DWIDTH        `SCR1_XLEN
`define SCR1_SHAMT_WIDTH        5

`ifndef SCR1_RVE_EXT
`define SCR1_RVI_EXT
`endif // ~SCR1_RVE_EXT

`ifdef SCR1_RVE_EXT
`define SCR1_MPRF_ADDR_WIDTH    4
`else // SCR1_RVE_EXT
`define SCR1_MPRF_ADDR_WIDTH    5
`endif // SCR1_RVE_EXT

parameter int unsigned  SCR1_CSR_ADDR_WIDTH = 12;

//-------------------------------------------------------------------------------
// Parameters for simulation
//-------------------------------------------------------------------------------
`define SCR1_SYN_OFF_EN                 // enable not synthesizable code (asserts, covergroups, tracelog)
`define SCR1_TRACE_LOG_EN               // enable trace log
`define SCR1_TRACE_LOG_FULL             // full trace log

`endif // SCR1_ARCH_DESCRIPTION_SVH