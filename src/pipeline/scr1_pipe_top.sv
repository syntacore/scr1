/// Copyright by Syntacore LLC © 2016-2018. See LICENSE for details
/// @file       <scr1_pipe_top.sv>
/// @brief      SCR1 pipeline top
///

`include "scr1_arch_description.svh"
`include "scr1_memif.svh"
`include "scr1_riscv_isa_decoding.svh"
`include "scr1_csr.svh"

`ifdef SCR1_IPIC_EN
`include "scr1_ipic.svh"
`endif // SCR1_IPIC_EN

`ifdef SCR1_DBGC_EN
`include "scr1_dbgc.svh"
`endif // SCR1_DBGC_EN

`ifdef SCR1_BRKM_EN
`include "scr1_brkm.svh"
`endif // SCR1_BRKM_EN

module scr1_pipe_top (
    // Common
    input   logic                                       rst_n,
    input   logic                                       clk,

    // Instruction Memory Interface
    output  logic                                       imem_req,
    output  type_scr1_mem_cmd_e                         imem_cmd,
    output  logic [`SCR1_IMEM_AWIDTH-1:0]               imem_addr,
    input   logic                                       imem_req_ack,
    input   logic [`SCR1_IMEM_DWIDTH-1:0]               imem_rdata,
    input   type_scr1_mem_resp_e                        imem_resp,

    // Data Memory Interface
    output  logic                                       dmem_req,
    output  type_scr1_mem_cmd_e                         dmem_cmd,
    output  type_scr1_mem_width_e                       dmem_width,
    output  logic [`SCR1_DMEM_AWIDTH-1:0]               dmem_addr,
    output  logic [`SCR1_DMEM_DWIDTH-1:0]               dmem_wdata,
    input   logic                                       dmem_req_ack,
    input   logic [`SCR1_DMEM_DWIDTH-1:0]               dmem_rdata,
    input   type_scr1_mem_resp_e                        dmem_resp,

`ifdef SCR1_DBGC_EN
    // DBGC interface
    input   type_scr1_dbgc_hart_dbg_mode_e              dbgc_hart_cmd,
    input   logic                                       dbgc_hart_cmd_req,
    output  logic                                       dbgc_hart_cmd_ack,
    output  logic                                       dbgc_hart_cmd_nack,
    input   type_scr1_dbgc_hart_runctrl_s               dbgc_hart_runctrl,
    output  type_scr1_dbgc_hart_state_s                 dbgc_hart_state,
    input   logic [SCR1_DBGC_DBG_CORE_INSTR_WIDTH-1:0]  dbgc_hart_instr,
    input   logic [SCR1_DBGC_DBG_DATA_REG_WIDTH-1:0]    dbgc_hart_dreg_out,
    output  logic [SCR1_DBGC_DBG_DATA_REG_WIDTH-1:0]    dbgc_hart_dreg_in,
    output  logic                                       dbgc_hart_dreg_wr,
    output  logic [SCR1_DBGC_DBG_DATA_REG_WIDTH-1:0]    dbgc_hart_pcsample,
`endif // SCR1_DBGC_EN

    // IRQ
`ifdef SCR1_IPIC_EN
    input   logic [SCR1_IRQ_LINES_NUM-1:0]              irq_lines,
`else // SCR1_IPIC_EN
    input   logic                                       ext_irq,
`endif // SCR1_IPIC_EN
    input   logic                                       soft_irq,

    // Memory-mapped external timer
    input   logic                                       timer_irq,
    input   logic [63:0]                                mtime_ext,

`ifdef SCR1_CLKCTRL_EN
    // CLK_CTRL interface
    output  logic                                       sleep_pipe,
    output  logic                                       wake_pipe,
    input   logic                                       clk_alw_on,
    input   logic                                       clk_dbgc,
    input   logic                                       clk_pipe_en,
`endif // SCR1_CLKCTRL_EN

    // Block busy interface
    output  logic                                       ifu_busy,
    output  logic                                       idu_busy,
    output  logic                                       exu_busy,
    output  logic                                       lsu_busy,
    output  logic                                       ialu_busy,

    // Fuse
    input   logic [`SCR1_XLEN-1:0]                      fuse_mhartid
);

//-------------------------------------------------------------------------------
// Local signals declaration
//-------------------------------------------------------------------------------

// Pipeline control
logic [`SCR1_XLEN-1:0]                      curr_pc;                // Current PC
logic [`SCR1_XLEN-1:0]                      next_pc;                // Is written to MEPC on interrupt trap
logic                                       new_pc_req;             // New PC request (jumps, branches, traps etc)
logic [`SCR1_XLEN-1:0]                      new_pc;                 // New PC

logic                                       stop_fetch;             // Stop IFU
logic                                       exu_exc_req;            // Exception request
logic                                       brkpt;                  // Breakpoint (sw/hw) on current instruction
logic                                       exu_init_pc;            // Reset exit
logic                                       wfi_run2halt;           // Transition to WFI halted state
logic                                       instret;                // Instruction retirement (with or without exception)
logic                                       instret_nexc;           // Instruction retirement (without exception)
`ifdef SCR1_IPIC_EN
logic                                       ext_irq;                // IRQ request from IPIC
`endif // SCR1_IPIC_EN
`ifdef SCR1_BRKM_EN
logic                                       brkpt_hw;               // Hardware breakpoint on current instruction
`endif // SCR1_BRKM_EN
`ifdef SCR1_CLKCTRL_EN
logic                                       imem_txns_pending;      // There are pending imem transactions
logic                                       wfi_halted;             // WFI halted state
`endif // SCR1_CLKCTRL_EN

// IFU <-> IDU
logic                                       ifu2idu_vd;             // IFU request
logic [`SCR1_IMEM_DWIDTH-1:0]               ifu2idu_instr;          // IFU instruction
logic                                       ifu2idu_imem_err;       // IFU instruction access fault
logic                                       ifu2idu_err_rvi_hi;     // 1 - imem fault when trying to fetch second half of an unaligned RVI instruction
logic                                       idu2ifu_rdy;            // IDU ready for new data

// IDU <-> EXU
logic                                       idu2exu_req;            // IDU request
type_scr1_exu_cmd_s                         idu2exu_cmd;            // IDU command (see scr1_riscv_isa_decoding.svh)
`ifndef SCR1_EXU_STAGE_BYPASS
logic                                       idu2exu_use_rs1;        // Instruction uses rs1
logic                                       idu2exu_use_rs2;        // Instruction uses rs2
logic                                       idu2exu_use_rd;         // Instruction uses rd
logic                                       idu2exu_use_imm;        // Instruction uses immediate
`endif // SCR1_EXU_STAGE_BYPASS
logic                                       exu2idu_rdy;            // EXU ready for new data

// EXU <-> MPRF
logic [`SCR1_MPRF_ADDR_WIDTH-1:0]           exu2mprf_rs1_addr;      // MPRF rs1 read address
logic [`SCR1_XLEN-1:0]                      mprf2exu_rs1_data;      // MPRF rs1 read data
logic [`SCR1_MPRF_ADDR_WIDTH-1:0]           exu2mprf_rs2_addr;      // MPRF rs2 read address
logic [`SCR1_XLEN-1:0]                      mprf2exu_rs2_data;      // MPRF rs2 read data
logic                                       exu2mprf_w_req;         // MPRF write request
logic [`SCR1_MPRF_ADDR_WIDTH-1:0]           exu2mprf_rd_addr;       // MPRF rd write address
logic [`SCR1_XLEN-1:0]                      exu2mprf_rd_data;       // MPRF rd write data

// EXU <-> CSR
logic [SCR1_CSR_ADDR_WIDTH-1:0]             exu2csr_rw_addr;        // CSR read/write address
logic                                       exu2csr_r_req;          // CSR read request
logic [`SCR1_XLEN-1:0]                      csr2exu_r_data;         // CSR read data
logic                                       exu2csr_w_req;          // CSR write request
type_scr1_csr_cmd_sel_e                     exu2csr_w_cmd;          // CSR write command
logic [`SCR1_XLEN-1:0]                      exu2csr_w_data;         // CSR write data
logic                                       csr2exu_rw_exc;         // CSR read/write access exception

// EXU <-> CSR event interface
logic                                       exu2csr_take_irq;       // Take IRQ trap
logic                                       exu2csr_take_exc;       // Take exception trap
logic                                       exu2csr_mret_update;    // MRET update CSR
logic                                       exu2csr_mret_instr;     // MRET instruction
type_scr1_exc_code_e                        exu2csr_exc_code;       // Exception code (see scr1_arch_types.svh)
logic [`SCR1_XLEN-1:0]                      exu2csr_trap_val;       // Trap value
logic [`SCR1_XLEN-1:0]                      csr2exu_new_pc;         // Exception/IRQ/MRET new PC
logic                                       csr2exu_irq;            // IRQ request
logic                                       csr2exu_ip_ie;          // Some IRQ pending and locally enabled
logic                                       csr2exu_mstatus_mie_up; // MSTATUS or MIE update in the current cycle

`ifdef SCR1_IPIC_EN
// CSR <-> IPIC
logic                                       csr2ipic_r_req;         // IPIC read request
logic                                       csr2ipic_w_req;         // IPIC write request
logic [2:0]                                 csr2ipic_addr;          // IPIC address
logic [`SCR1_XLEN-1:0]                      csr2ipic_wdata;         // IPIC write data
logic [`SCR1_XLEN-1:0]                      ipic2csr_rdata;         // IPIC read data
`endif // SCR1_IPIC_EN

`ifdef SCR1_BRKM_EN
// CSR <-> BRKM
logic                                       csr2brkm_req;           // Request to BRKM
type_scr1_csr_cmd_sel_e                     csr2brkm_cmd;           // BRKM command
logic [SCR1_BRKM_PKG_CSR_OFFS_WIDTH-1:0]    csr2brkm_addr;          // BRKM address
logic [SCR1_BRKM_PKG_CSR_DATA_WIDTH-1:0]    csr2brkm_wdata;         // BRKM write data
logic [SCR1_BRKM_PKG_CSR_DATA_WIDTH-1:0]    brkm2csr_rdata;         // BRKM read data
type_scr1_csr_resp_e                        brkm2csr_resp;          // BRKM response

// EXU/LSU <-> BRKM
type_scr1_brkm_instr_mon_s                  exu2brkm_i_mon;         // Instruction monitor
type_scr1_brkm_lsu_mon_s                    lsu2brkm_d_mon;         // Data monitor
logic [SCR1_BRKM_BRKPT_NUMBER-1:0]          brkm2exu_i_match;       // Instruction breakpoint(s) match
logic [SCR1_BRKM_BRKPT_NUMBER-1:0]          brkm2lsu_d_match;       // Data breakpoint(s) match
logic                                       brkm2exu_i_x_req;       // Instruction breakpoint exception
logic                                       brkm2lsu_i_x_req;       // Instruction breakpoint exception
logic                                       brkm2lsu_d_x_req;       // Data breakpoint exception
logic [SCR1_BRKM_BRKPT_NUMBER-1:0]          exu2brkm_bp_retire;     // Instruction with breakpoint flag retire
logic                                       exu2brkm_bp_i_recover;  // Instruction breakpoint state recover
`endif // SCR1_BRKM_EN

`ifdef SCR1_DBGC_EN
// DBGC
logic                                       fetch_dbgc;             // Fetch instructions provided by DBGC
logic [`SCR1_IMEM_DWIDTH-1:0]               dbgc_instr;

logic [SCR1_DBGC_DBG_DATA_REG_WIDTH-1:0]    dbga2csr_ddr;           // DBGA read data (DDR - debug data register interface)
logic [SCR1_DBGC_DBG_DATA_REG_WIDTH-1:0]    csr2dbga_ddr;           // DBGA write data
logic                                       csr2dbga_ddr_we;        // DBGA write request

logic                                       hwbrk_dsbl;             // Disables BRKM
logic                                       brkm2dbga_dmode_req;    // BRKM requests transition to debug mode

logic                                       exu_no_commit;          // Forbid instruction commitment
logic                                       exu_irq_dsbl;           // Disable IRQ
logic                                       exu_pc_advmt_dsbl;      // Forbid PC advancement
logic                                       exu_dmode_sstep_en;     // Enable single-step

logic                                       dbg_halted;             // Debug halted state
logic                                       dbg_run2halt;           // Transition to debug halted state
logic                                       dbg_halt2run;           // Transition to run state
logic                                       dbg_run_start;          // First cycle of run state
`endif // SCR1_DBGC_EN


//-------------------------------------------------------------------------------
// Pipeline logic
//-------------------------------------------------------------------------------
assign stop_fetch   = wfi_run2halt
`ifdef SCR1_DBGC_EN
                    | dbg_run2halt
`endif // SCR1_DBGC_EN
                    ;

`ifdef SCR1_CLKCTRL_EN
assign sleep_pipe   = wfi_halted & ~imem_txns_pending;
assign wake_pipe    = csr2exu_ip_ie
`ifdef SCR1_DBGC_EN
                    | dbgc_hart_cmd_req
`endif // SCR1_DBGC_EN
                    ;
`endif // SCR1_CLKCTRL_EN

`ifdef SCR1_DBGC_EN
assign dbgc_hart_pcsample = curr_pc;
`endif // SCR1_DBGC_EN

//-------------------------------------------------------------------------------
// Instruction fetch unit
//-------------------------------------------------------------------------------
scr1_pipe_ifu i_pipe_ifu (
    .rst_n              (rst_n              ),
    .clk                (clk                ),

    .imem_req_ack       (imem_req_ack       ),
    .imem_req           (imem_req           ),
    .imem_cmd           (imem_cmd           ),
    .imem_addr          (imem_addr          ),
    .imem_rdata         (imem_rdata         ),
    .imem_resp          (imem_resp          ),

    .new_pc             (new_pc             ),
    .new_pc_req         (new_pc_req         ),
    .stop_fetch         (stop_fetch         ),
`ifdef SCR1_DBGC_EN
    .fetch_dbgc         (fetch_dbgc         ),
    .dbgc_instr         (dbgc_instr         ),
`endif // SCR1_DBGC_EN
`ifdef SCR1_CLKCTRL_EN
    .imem_txns_pending  (imem_txns_pending  ),
`endif // SCR1_CLKCTRL_EN
    .idu2ifu_rdy        (idu2ifu_rdy        ),
    .ifu2idu_instr      (ifu2idu_instr      ),
    .ifu2idu_imem_err   (ifu2idu_imem_err   ),
    .ifu2idu_err_rvi_hi (ifu2idu_err_rvi_hi ),
    .ifu2idu_vd         (ifu2idu_vd         ),

    .ifu_busy           (ifu_busy           )
);

//-------------------------------------------------------------------------------
// Instruction decode unit
//-------------------------------------------------------------------------------
scr1_pipe_idu i_pipe_idu (
`ifdef SCR1_SIM_ENV
    .rst_n              (rst_n              ),
    .clk                (clk                ),
`endif // SCR1_SIM_ENV
    .idu2ifu_rdy        (idu2ifu_rdy        ),
    .ifu2idu_instr      (ifu2idu_instr      ),
    .ifu2idu_imem_err   (ifu2idu_imem_err   ),
    .ifu2idu_err_rvi_hi (ifu2idu_err_rvi_hi ),
    .ifu2idu_vd         (ifu2idu_vd         ),

    .idu2exu_req        (idu2exu_req        ),
    .idu2exu_cmd        (idu2exu_cmd        ),
`ifndef SCR1_EXU_STAGE_BYPASS
    .idu2exu_use_rs1    (idu2exu_use_rs1    ),
    .idu2exu_use_rs2    (idu2exu_use_rs2    ),
    .idu2exu_use_rd     (idu2exu_use_rd     ),
    .idu2exu_use_imm    (idu2exu_use_imm    ),
`else // SCR1_EXU_STAGE_BYPASS
    .idu2exu_use_rs1    (),
    .idu2exu_use_rs2    (),
    .idu2exu_use_rd     (),
    .idu2exu_use_imm    (),
`endif // SCR1_EXU_STAGE_BYPASS
    .exu2idu_rdy        (exu2idu_rdy        ),

    .idu_busy           (idu_busy           )
);

//-------------------------------------------------------------------------------
// Execution unit
//-------------------------------------------------------------------------------
scr1_pipe_exu i_pipe_exu (
    .rst_n                  (rst_n                ),
    .clk                    (clk                  ),
`ifdef SCR1_CLKCTRL_EN
    .clk_alw_on             (clk_alw_on           ),
    .clk_pipe_en            (clk_pipe_en          ),
`endif // SCR1_CLKCTRL_EN
    .idu2exu_req            (idu2exu_req          ),
    .exu2idu_rdy            (exu2idu_rdy          ),
    .idu2exu_cmd            (idu2exu_cmd          ),
`ifndef SCR1_EXU_STAGE_BYPASS
    .idu2exu_use_rs1        (idu2exu_use_rs1      ),
    .idu2exu_use_rs2        (idu2exu_use_rs2      ),
    .idu2exu_use_rd         (idu2exu_use_rd       ),
    .idu2exu_use_imm        (idu2exu_use_imm      ),
`endif // SCR1_EXU_STAGE_BYPASS

    .exu2mprf_rs1_addr      (exu2mprf_rs1_addr    ),
    .mprf2exu_rs1_data      (mprf2exu_rs1_data    ),
    .exu2mprf_rs2_addr      (exu2mprf_rs2_addr    ),
    .mprf2exu_rs2_data      (mprf2exu_rs2_data    ),
    .exu2mprf_w_req         (exu2mprf_w_req       ),
    .exu2mprf_rd_addr       (exu2mprf_rd_addr     ),
    .exu2mprf_rd_data       (exu2mprf_rd_data     ),

    .exu2csr_rw_addr        (exu2csr_rw_addr      ),
    .exu2csr_r_req          (exu2csr_r_req        ),
    .csr2exu_r_data         (csr2exu_r_data       ),
    .exu2csr_w_req          (exu2csr_w_req        ),
    .exu2csr_w_cmd          (exu2csr_w_cmd        ),
    .exu2csr_w_data         (exu2csr_w_data       ),
    .csr2exu_rw_exc         (csr2exu_rw_exc       ),
    .exu2csr_take_irq       (exu2csr_take_irq     ),
    .exu2csr_take_exc       (exu2csr_take_exc     ),
    .exu2csr_mret_update    (exu2csr_mret_update  ),
    .exu2csr_mret_instr     (exu2csr_mret_instr   ),
    .exu2csr_exc_code       (exu2csr_exc_code     ),
    .exu2csr_trap_val       (exu2csr_trap_val     ),
    .csr2exu_new_pc         (csr2exu_new_pc       ),
    .csr2exu_irq            (csr2exu_irq          ),
    .csr2exu_ip_ie          (csr2exu_ip_ie        ),
    .csr2exu_mstatus_mie_up (csr2exu_mstatus_mie_up),

    .exu2dmem_req           (dmem_req             ),
    .exu2dmem_cmd           (dmem_cmd             ),
    .exu2dmem_width         (dmem_width           ),
    .exu2dmem_addr          (dmem_addr            ),
    .exu2dmem_wdata         (dmem_wdata           ),
    .dmem2exu_req_ack       (dmem_req_ack         ),
    .dmem2exu_rdata         (dmem_rdata           ),
    .dmem2exu_resp          (dmem_resp            ),
`ifdef SCR1_DBGC_EN
    .exu_no_commit          (exu_no_commit        ),
    .exu_irq_dsbl           (exu_irq_dsbl         ),
    .exu_pc_advmt_dsbl      (exu_pc_advmt_dsbl    ),
    .exu_dmode_sstep_en     (exu_dmode_sstep_en   ),
    .fetch_dbgc             (fetch_dbgc           ),
    .dbg_halted             (dbg_halted           ),
    .dbg_run2halt           (dbg_run2halt         ),
    .dbg_halt2run           (dbg_halt2run         ),
    .dbg_run_start          (dbg_run_start        ),
`endif // SCR1_DBGC_EN
`ifdef SCR1_BRKM_EN
    .exu2brkm_i_mon         (exu2brkm_i_mon       ),
    .brkm2exu_i_match       (brkm2exu_i_match     ),
    .brkm2exu_i_x_req       (brkm2exu_i_x_req     ),
    .lsu2brkm_d_mon         (lsu2brkm_d_mon       ),
    .brkm2lsu_i_x_req       (brkm2lsu_i_x_req     ),
    .brkm2lsu_d_match       (brkm2lsu_d_match     ),
    .brkm2lsu_d_x_req       (brkm2lsu_d_x_req     ),
    .exu2brkm_bp_retire     (exu2brkm_bp_retire   ),
    .exu2brkm_bp_i_recover  (exu2brkm_bp_i_recover),
    .brkpt_hw               (brkpt_hw             ),
`endif // SCR1_BRKM_EN
    .brkpt                  (brkpt                ),
    .exu_exc_req            (exu_exc_req          ),
    .exu_init_pc            (exu_init_pc          ),
    .wfi_run2halt           (wfi_run2halt         ),
    .instret                (instret              ),
    .instret_nexc           (instret_nexc         ),
`ifdef SCR1_CLKCTRL_EN
    .wfi_halted             (wfi_halted           ),
`endif // SCR1_CLKCTRL_EN
    .curr_pc                (curr_pc              ),
    .next_pc                (next_pc              ),
    .new_pc_req             (new_pc_req           ),
    .new_pc                 (new_pc               ),

    .exu_busy               (exu_busy             ),
    .lsu_busy               (lsu_busy             ),
    .ialu_busy              (ialu_busy            )
);

//-------------------------------------------------------------------------------
// Multi-port register file
//-------------------------------------------------------------------------------
scr1_pipe_mprf i_pipe_mprf (
    .rst_n                  (rst_n            ),
    .clk                    (clk              ),
    .exu2mprf_rs1_addr      (exu2mprf_rs1_addr),
    .mprf2exu_rs1_data      (mprf2exu_rs1_data),
    .exu2mprf_rs2_addr      (exu2mprf_rs2_addr),
    .mprf2exu_rs2_data      (mprf2exu_rs2_data),
    .exu2mprf_w_req         (exu2mprf_w_req   ),
    .exu2mprf_rd_addr       (exu2mprf_rd_addr ),
    .exu2mprf_rd_data       (exu2mprf_rd_data )
);

//-------------------------------------------------------------------------------
// Control and status registers
//-------------------------------------------------------------------------------
scr1_pipe_csr i_pipe_csr (
    .rst_n                  (rst_n              ),
    .clk                    (clk                ),
`ifdef SCR1_CLKCTRL_EN
    .clk_alw_on             (clk_alw_on         ),
`endif // SCR1_CLKCTRL_EN

    .exu2csr_r_req          (exu2csr_r_req      ),
    .exu2csr_rw_addr        (exu2csr_rw_addr    ),
    .csr2exu_r_data         (csr2exu_r_data     ),
    .exu2csr_w_req          (exu2csr_w_req      ),
    .exu2csr_w_cmd          (exu2csr_w_cmd      ),
    .exu2csr_w_data         (exu2csr_w_data     ),
    .csr2exu_rw_exc         (csr2exu_rw_exc     ),

    .exu2csr_take_irq       (exu2csr_take_irq   ),
    .exu2csr_take_exc       (exu2csr_take_exc   ),
    .exu2csr_mret_update    (exu2csr_mret_update),
    .exu2csr_mret_instr     (exu2csr_mret_instr ),
`ifdef SCR1_DBGC_EN
    .exu_no_commit          (exu_no_commit      ),
`endif // SCR1_DBGC_EN
    .exu2csr_exc_code       (exu2csr_exc_code   ),
    .exu2csr_trap_val       (exu2csr_trap_val   ),
    .csr2exu_new_pc         (csr2exu_new_pc     ),
    .csr2exu_irq            (csr2exu_irq        ),
    .csr2exu_ip_ie          (csr2exu_ip_ie      ),
    .csr2exu_mstatus_mie_up (csr2exu_mstatus_mie_up),
`ifdef SCR1_IPIC_EN
    .csr2ipic_r_req         (csr2ipic_r_req     ),
    .csr2ipic_w_req         (csr2ipic_w_req     ),
    .csr2ipic_addr          (csr2ipic_addr      ),
    .csr2ipic_wdata         (csr2ipic_wdata     ),
    .ipic2csr_rdata         (ipic2csr_rdata     ),
`endif // SCR1_IPIC_EN
    .curr_pc                (curr_pc            ),
    .next_pc                (next_pc            ),
`ifndef SCR1_CSR_REDUCED_CNT
    .instret_nexc           (instret_nexc       ),
`endif // SCR1_CSR_REDUCED_CNT
    .ext_irq                (ext_irq            ),
    .soft_irq               (soft_irq           ),
    .timer_irq              (timer_irq          ),
    .mtime_ext              (mtime_ext          ),
`ifdef SCR1_DBGC_EN
    .dbga2csr_ddr           (dbga2csr_ddr       ),
    .csr2dbga_ddr           (csr2dbga_ddr       ),
    .csr2dbga_ddr_we        (csr2dbga_ddr_we    ),
`endif // SCR1_DBGC_EN
`ifdef SCR1_BRKM_EN
    .csr2brkm_req           (csr2brkm_req       ),
    .csr2brkm_cmd           (csr2brkm_cmd       ),
    .csr2brkm_addr          (csr2brkm_addr      ),
    .csr2brkm_wdata         (csr2brkm_wdata     ),
    .brkm2csr_rdata         (brkm2csr_rdata     ),
    .brkm2csr_resp          (brkm2csr_resp      ),
`endif // SCR1_BRKM_EN
    .fuse_mhartid           (fuse_mhartid       )
);

//-------------------------------------------------------------------------------
// Integrated programmable interrupt controller
//-------------------------------------------------------------------------------
`ifdef SCR1_IPIC_EN
scr1_ipic i_pipe_ipic (
    .rst_n              (rst_n          ),
`ifdef SCR1_CLKCTRL_EN
    .clk                (clk_alw_on     ),
`else // SCR1_CLKCTRL_EN
    .clk                (clk            ),
`endif // SCR1_CLKCTRL_EN
    .irq_lines          (irq_lines      ),
    .csr2ipic_r_req     (csr2ipic_r_req ),
    .csr2ipic_w_req     (csr2ipic_w_req ),
    .csr2ipic_addr      (csr2ipic_addr  ),
    .csr2ipic_wdata     (csr2ipic_wdata ),
    .ipic2csr_rdata     (ipic2csr_rdata ),
    .irq_m_req          (ext_irq        )
);
`endif // SCR1_IPIC_EN

//-------------------------------------------------------------------------------
// Breakpoint module
//-------------------------------------------------------------------------------
`ifdef SCR1_BRKM_EN
scr1_pipe_brkm i_pipe_brkm (
    .rst_n                  (rst_n                  ),
    .clk                    (clk                    ),
    .clk_en                 (1'b1                   ),
`ifdef SCR1_DBGC_EN
    .init                   (dbg_halt2run           ),
    .dsbl                   (hwbrk_dsbl             ),
`else // SCR1_DBGC_EN
    .init                   (1'b0                   ),
    .dsbl                   (1'b0                   ),
`endif // SCR1_DBGC_EN
    .csr2brkm_req           (csr2brkm_req           ),
    .csr2brkm_cmd           (csr2brkm_cmd           ),
    .csr2brkm_addr          (csr2brkm_addr          ),
    .csr2brkm_wdata         (csr2brkm_wdata         ),
    .brkm2csr_rdata         (brkm2csr_rdata         ),
    .brkm2csr_resp          (brkm2csr_resp          ),
`ifdef SCR1_DBGC_EN
    .brkm2dbga_dmode_req    (brkm2dbga_dmode_req    ),
`else // SCR1_DBGC_EN
    .brkm2dbga_dmode_req    (),
`endif // SCR1_DBGC_EN
    .exu2brkm_i_mon         (exu2brkm_i_mon         ),
    .brkm2exu_i_match       (brkm2exu_i_match       ),
    .brkm2exu_i_x_req       (brkm2exu_i_x_req       ),
    .lsu_brk_en             (),
    .brkm2lsu_i_x_req       (brkm2lsu_i_x_req       ),
    .lsu2brkm_d_mon         (lsu2brkm_d_mon         ),
    .brkm2lsu_d_match       (brkm2lsu_d_match       ),
    .brkm2lsu_d_x_req       (brkm2lsu_d_x_req       ),
    .exu2brkm_bp_retire     (exu2brkm_bp_retire     ),
    .exu2brkm_bp_i_recover  (exu2brkm_bp_i_recover  )
);
`endif // SCR1_BRKM_EN

//-------------------------------------------------------------------------------
// Pipeline debug agent
//-------------------------------------------------------------------------------
`ifdef SCR1_DBGC_EN
scr1_pipe_dbga i_pipe_dbga (
    .rst_n              (rst_n                  ),
`ifdef SCR1_CLKCTRL_EN
    .clk_pipe_en        (clk_pipe_en            ),
    .clk                (clk_dbgc               ),
`else
    .clk                (clk                    ),
`endif // SCR1_CLKCTRL_EN
    .dbgc_hart_cmd      (dbgc_hart_cmd          ),
    .dbgc_hart_cmd_req  (dbgc_hart_cmd_req      ),
    .dbgc_hart_cmd_ack  (dbgc_hart_cmd_ack      ),
    .dbgc_hart_cmd_nack (dbgc_hart_cmd_nack     ),
    .dbgc_hart_runctrl  (dbgc_hart_runctrl      ),
    .dbgc_hart_state    (dbgc_hart_state        ),
    .dbgc_hart_instr    (dbgc_hart_instr        ),
    .dbgc_hart_dreg_out (dbgc_hart_dreg_out     ),
    .dbgc_hart_dreg_in  (dbgc_hart_dreg_in      ),
    .dbgc_hart_dreg_wr  (dbgc_hart_dreg_wr      ),

    .fetch_dbgc         (fetch_dbgc             ),
    .dbgc_instr         (dbgc_instr             ),
    .hwbrk_dsbl         (hwbrk_dsbl             ),
    .brkm_dmode_req     (brkm2dbga_dmode_req    ),
    .brkpt_hw           (brkpt_hw               ),
    .exu_busy           (exu_busy               ),
    .instret            (instret                ),
    .exu_exc_req        (exu_exc_req            ),
    .brkpt              (brkpt                  ),
    .exu_init_pc        (exu_init_pc            ),
    .exu_no_commit      (exu_no_commit          ),
    .exu_irq_dsbl       (exu_irq_dsbl           ),
    .exu_pc_advmt_dsbl  (exu_pc_advmt_dsbl      ),
    .exu_dmode_sstep_en (exu_dmode_sstep_en     ),
    .dbga2csr_ddr       (dbga2csr_ddr           ),
    .csr2dbga_ddr       (csr2dbga_ddr           ),
    .csr2dbga_ddr_we    (csr2dbga_ddr_we        ),
    .dbg_halted         (dbg_halted             ),
    .dbg_run2halt       (dbg_run2halt           ),
    .dbg_halt2run       (dbg_halt2run           ),
    .dbg_run_start      (dbg_run_start          )
);
`endif // SCR1_DBGC_EN

`ifdef SCR1_SIM_ENV
//-------------------------------------------------------------------------------
// Tracelog
//-------------------------------------------------------------------------------

scr1_tracelog i_tracelog (
    .rst_n          (rst_n                              ),
    .clk            (clk                                ),
    .fuse_mhartid   (fuse_mhartid                       ),
    // MPRF
    .mprf_int       (i_pipe_mprf.mprf_int               ),
    .mprf_wr_en     (i_pipe_mprf.exu2mprf_w_req         ),
    .mprf_wr_addr   (i_pipe_mprf.exu2mprf_rd_addr       ),
    .mprf_wr_data   (i_pipe_mprf.exu2mprf_rd_data       ),
    // EXU
    .update_pc_en   (i_pipe_exu.update_pc_en            ),
    .update_pc      (i_pipe_exu.update_pc               ),
    // CSR
    .mstatus_mie    (i_pipe_csr.csr_mstatus_mie         ),
    .mstatus_mpie   (i_pipe_csr.csr_mstatus_mpie        ),
    .mtvec_base     (i_pipe_csr.csr_mtvec_base          ),
    .mtvec_mode     (i_pipe_csr.csr_mtvec_mode          ),
    .mie_meie       (i_pipe_csr.csr_mie_meie            ),
    .mie_mtie       (i_pipe_csr.csr_mie_mtie            ),
    .mie_msie       (i_pipe_csr.csr_mie_msie            ),
    .mip_meip       (i_pipe_csr.csr_mip_meip            ),
    .mip_mtip       (i_pipe_csr.csr_mip_mtip            ),
    .mip_msip       (i_pipe_csr.csr_mip_msip            ),
    .mepc           (i_pipe_csr.csr_mepc                ),
    .mcause_i       (i_pipe_csr.csr_mcause_i            ),
    .mcause_ec      (i_pipe_csr.csr_mcause_ec           ),
    .mtval          (i_pipe_csr.csr_mtval               ),
    .mstatus_mie_up (i_pipe_csr.csr2exu_mstatus_mie_up  )
);

`endif // SCR1_SIM_ENV

endmodule : scr1_pipe_top