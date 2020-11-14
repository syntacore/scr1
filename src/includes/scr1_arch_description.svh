/// Copyright by Syntacore LLC © 2016-2020. See LICENSE for details
/// @file       <scr1_arch_description.svh>
/// @brief      Architecture description file
///

`ifndef SCR1_ARCH_DESCRIPTION_SVH
`define SCR1_ARCH_DESCRIPTION_SVH

//------------------------------------------------------------------------------
// CORE FUNDAMENTAL PARAMETERS
//------------------------------------------------------------------------------

// SCR1 core identifiers
`define SCR1_MIMPID             32'h20111300
`define SCR1_MVENDORID          32'h00000000

// Width of main registers and busses
`define SCR1_XLEN               32
`define SCR1_IMEM_AWIDTH        `SCR1_XLEN
`define SCR1_IMEM_DWIDTH        `SCR1_XLEN
`define SCR1_DMEM_AWIDTH        `SCR1_XLEN
`define SCR1_DMEM_DWIDTH        `SCR1_XLEN

// TAP IDCODE
`define SCR1_TAP_IDCODE         'hDEB11001

//------------------------------------------------------------------------------
// RECOMMENDED CORE ARCHITECTURE CONFIGURATIONS
//------------------------------------------------------------------------------

// Uncomment one of these defines to set the recommended configuration:

//`define SCR1_CFG_RV32IMC_MAX
//`define SCR1_CFG_RV32IC_BASE
//`define SCR1_CFG_RV32EC_MIN

// If all defines are commented, custom configuration will be used (see below)

//------------------------------------------------------------------------------
// READ-ONLY: settings for recommended configurations
`ifdef  SCR1_CFG_RV32IMC_MAX
  `define SCR1_RVI_EXT
  `define SCR1_RVM_EXT
  `define SCR1_RVC_EXT
  parameter int unsigned SCR1_MTVEC_BASE_WR_BITS = 26;
  `define SCR1_MTVEC_MODE_EN
  `define SCR1_FAST_MUL
  `define SCR1_MPRF_RST_EN
  `define SCR1_MCOUNTEN_EN
  `define SCR1_DBG_EN
  `define SCR1_TDU_EN
  parameter int unsigned SCR1_TDU_TRIG_NUM = 4;
  `define SCR1_TDU_ICOUNT_EN
  `define SCR1_IPIC_EN
  `define SCR1_IPIC_SYNC_EN
  `define SCR1_TCM_EN
`elsif  SCR1_CFG_RV32IC_BASE
  `define SCR1_RVI_EXT
  `define SCR1_RVC_EXT
  parameter int unsigned SCR1_MTVEC_BASE_WR_BITS = 16;
  `define SCR1_MTVEC_MODE_EN
  `define SCR1_NO_DEC_STAGE
  `define SCR1_MPRF_RST_EN
  `define SCR1_MCOUNTEN_EN
  `define SCR1_DBG_EN
  `define SCR1_TDU_EN
  parameter int unsigned SCR1_TDU_TRIG_NUM = 2;
  `define SCR1_TDU_ICOUNT_EN
  `define SCR1_IPIC_EN
  `define SCR1_IPIC_SYNC_EN
  `define SCR1_TCM_EN
`elsif  SCR1_CFG_RV32EC_MIN
  `define SCR1_RVE_EXT
  `define SCR1_RVC_EXT
  parameter int unsigned SCR1_MTVEC_BASE_WR_BITS = 0;
  `define SCR1_NO_DEC_STAGE
  `define SCR1_NO_EXE_STAGE
  `define SCR1_TCM_EN

`else // begin custom configuration section


//------------------------------------------------------------------------------
// CUSTOM CORE ARCHITECTURE CONFIGURATION
//------------------------------------------------------------------------------

// To fine-tune custom configuration, you can change the values in this section.
// Make sure that the defines of the recommended configurations are commented,
// otherwise this section will be inactive.

// RISC-V ISA options
//`define SCR1_RVE_EXT                // enable RV32E base integer instruction set, otherwise RV32I will be used
`define SCR1_RVM_EXT                // enable standard extension "M" for integer hardware multiplier and divider
`define SCR1_RVC_EXT                // enable standard extension "C" for compressed instructions
parameter int unsigned SCR1_MTVEC_BASE_WR_BITS = 26;    // number of writable high-order bits in MTVEC.base field
                                                            // legal values are 0 to 26
                                                            // read-only bits are hardwired to reset value
`define SCR1_MTVEC_MODE_EN          // enable writable MTVEC.mode field to allow vectored irq mode, otherwise only direct mode is possible

`ifndef SCR1_RVE_EXT
  `define SCR1_RVI_EXT // RV32E base integer instruction set if SCR1_RVE_EXT is not enabled
`endif // ~SCR1_RVE_EXT

// Core pipeline options (power-performance-area optimization)
`define SCR1_NO_DEC_STAGE           // disable register between IFU and IDU
`define SCR1_NO_EXE_STAGE           // disable register between IDU and EXU
`define SCR1_NEW_PC_REG             // enable register in IFU for New_PC value
`define SCR1_FAST_MUL               // enable fast one-cycle multiplication, otherwise multiplication takes 32 cycles
`define SCR1_CLKCTRL_EN             // enable global clock gating
`define SCR1_MPRF_RST_EN            // enable reset for MPRF
`define SCR1_MCOUNTEN_EN            // enable custom MCOUNTEN CSR for counter control

// Uncore options
`define SCR1_DBG_EN                 // enable Debug Subsystem (TAPC, DM, SCU, HDU)
`define SCR1_TDU_EN                 // enable Trigger Debug Unit (hardware breakpoints)
parameter int unsigned SCR1_TDU_TRIG_NUM = 2;   // number of hardware triggers
`define SCR1_TDU_ICOUNT_EN          // enable hardware triggers on instruction counter
`define SCR1_IPIC_EN                // enable Integrated Programmable Interrupt Controller
`define SCR1_IPIC_SYNC_EN           // enable IPIC synchronizer
`define SCR1_TCM_EN                 // enable Tightly-Coupled Memory

`endif // end custom configuration section


//------------------------------------------------------------------------------
// CORE INTEGRATION OPTIONS
//------------------------------------------------------------------------------

// Bypasses on AXI/AHB bridge I/O
`define SCR1_IMEM_AHB_IN_BP         // bypass instruction memory AHB bridge input register
`define SCR1_IMEM_AHB_OUT_BP        // bypass instruction memory AHB bridge output register
`define SCR1_DMEM_AHB_IN_BP         // bypass data memory AHB bridge input register
`define SCR1_DMEM_AHB_OUT_BP        // bypass data memory AHB bridge output register
`define SCR1_IMEM_AXI_REQ_BP        // bypass instruction memory AXI bridge request register
`define SCR1_IMEM_AXI_RESP_BP       // bypass instruction memory AXI bridge response register
`define SCR1_DMEM_AXI_REQ_BP        // bypass data memory AXI bridge request register
`define SCR1_DMEM_AXI_RESP_BP       // bypass data memory AXI bridge response register

`ifndef SCR1_ARCH_CUSTOM
// Default address constants (if scr1_arch_custom.svh is not used)
parameter bit [`SCR1_XLEN-1:0]          SCR1_ARCH_RST_VECTOR        = 'h200;            // Reset vector value (start address after reset)
parameter bit [`SCR1_XLEN-1:0]          SCR1_ARCH_MTVEC_BASE        = 'h1C0;            // MTVEC.base field reset value, or constant value for MTVEC.base bits that are hardwired

parameter bit [`SCR1_DMEM_AWIDTH-1:0]   SCR1_TCM_ADDR_MASK          = 'hFFFF0000;       // TCM mask and size; size in bytes is two's complement of the mask value
parameter bit [`SCR1_DMEM_AWIDTH-1:0]   SCR1_TCM_ADDR_PATTERN       = 'h00480000;       // TCM address match pattern

parameter bit [`SCR1_DMEM_AWIDTH-1:0]   SCR1_TIMER_ADDR_MASK        = 'hFFFFFFE0;       // Timer mask
parameter bit [`SCR1_DMEM_AWIDTH-1:0]   SCR1_TIMER_ADDR_PATTERN     = 'h00490000;       // Timer address match pattern

// Device build ID
 `define SCR1_ARCH_BUILD_ID             `SCR1_MIMPID

`else // SCR1_ARCH_CUSTOM

// The external file scr1_arch_custom.svh is used for the open SCR1-SDK project,
// and can also be used for any custom projects.

// The file sets:
// - target platform (FPGA/ASIC), which affects the choice of logical constructs;
// - device build ID;
// - address constants.

// Possible targets:
// `define SCR1_TRGT_FPGA_INTEL         // target platform is Intel FPGAs
// `define SCR1_TRGT_FPGA_INTEL_MAX10   // target platform is Intel MAX 10 FPGAs (used in the SCR1-SDK project)
// `define SCR1_TRGT_FPGA_INTEL_ARRIAV  // target platform is Intel Arria V FPGAs (used in the SCR1-SDK project)
// `define SCR1_TRGT_FPGA_XILINX        // target platform is Xilinx FPGAs (used in the SCR1-SDK project)
// `define SCR1_TRGT_ASIC               // target platform is ASIC
// `define SCR1_TRGT_SIMULATION         // target is simulation (enable simulation code)

 `include "scr1_arch_custom.svh"

`endif // SCR1_ARCH_CUSTOM


//------------------------------------------------------------------------------
// TARGET-SPECIFIC OPTIONS
//------------------------------------------------------------------------------

// RAM-based MPRF can be used for Intel FPGAs only
`ifdef SCR1_TRGT_FPGA_INTEL
  `define SCR1_MPRF_RAM           // implements MPRF with dedicated RAM blocks
`endif

// EXU_STAGE_BYPASS and MPRF_RST_EN must be disabled for RAM-based MPRF
`ifdef SCR1_MPRF_RAM
  `undef  SCR1_NO_EXE_STAGE
  `undef  SCR1_MPRF_RST_EN
`endif


//------------------------------------------------------------------------------
// SIMULATION OPTIONS
//------------------------------------------------------------------------------

//`define SCR1_TRGT_SIMULATION            // enable simulation code (automatically defined by root makefile)
//`define SCR1_TRACE_LOG_EN               // enable tracelog

// Addresses used in testbench
localparam [`SCR1_XLEN-1:0]      SCR1_SIM_EXIT_ADDR      = 32'h0000_00F8;
localparam [`SCR1_XLEN-1:0]      SCR1_SIM_PRINT_ADDR     = 32'hF000_0000;
localparam [`SCR1_XLEN-1:0]      SCR1_SIM_EXT_IRQ_ADDR   = 32'hF000_0100;
localparam [`SCR1_XLEN-1:0]      SCR1_SIM_SOFT_IRQ_ADDR  = 32'hF000_0200;

`endif // SCR1_ARCH_DESCRIPTION_SVH
