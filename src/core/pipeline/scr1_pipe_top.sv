/// Copyright by Syntacore LLC © 2016-2020. See LICENSE for details
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

`ifdef SCR1_DBG_EN
`include "scr1_hdu.svh"
`endif // SCR1_DBG_EN

`ifdef SCR1_TDU_EN
`include "scr1_tdu.svh"
`endif // SCR1_TDU_EN

module scr1_pipe_top (
    // Common
    input   logic                                       pipe_rst_n,                 // Pipe reset
`ifdef SCR1_DBG_EN
    input   logic                                       pipe2hdu_rdc_qlfy_i,        // Pipe RDC qualifier
    input   logic                                       dbg_rst_n,                  // Debug reset
`endif // SCR1_DBG_EN
    input   logic                                       clk,                        // Pipe clock

    // Instruction Memory Interface
    output  logic                                       pipe2imem_req_o,            // IMEM request
    output  type_scr1_mem_cmd_e                         pipe2imem_cmd_o,            // IMEM command
    output  logic [`SCR1_IMEM_AWIDTH-1:0]               pipe2imem_addr_o,           // IMEM address
    input   logic                                       imem2pipe_req_ack_i,        // IMEM request acknowledge
    input   logic [`SCR1_IMEM_DWIDTH-1:0]               imem2pipe_rdata_i,          // IMEM read data
    input   type_scr1_mem_resp_e                        imem2pipe_resp_i,           // IMEM response

    // Data Memory Interface
    output  logic                                       pipe2dmem_req_o,            // DMEM request
    output  type_scr1_mem_cmd_e                         pipe2dmem_cmd_o,            // DMEM command
    output  type_scr1_mem_width_e                       pipe2dmem_width_o,          // DMEM data width
    output  logic [`SCR1_DMEM_AWIDTH-1:0]               pipe2dmem_addr_o,           // DMEM address
    output  logic [`SCR1_DMEM_DWIDTH-1:0]               pipe2dmem_wdata_o,          // DMEM write data
    input   logic                                       dmem2pipe_req_ack_i,        // DMEM request acknowledge
    input   logic [`SCR1_DMEM_DWIDTH-1:0]               dmem2pipe_rdata_i,          // DMEM read data
    input   type_scr1_mem_resp_e                        dmem2pipe_resp_i,           // DMEM response

`ifdef SCR1_DBG_EN
    // Debug interface:
    input  logic                                        dbg_en,                     // 1 - debug operations enabled
    // DM <-> Pipeline: HART Run Control i/f
    input  logic                                        dm2pipe_active_i,           // Debug Module active flag
    input  logic                                        dm2pipe_cmd_req_i,          // Request from Debug Module
    input  type_scr1_hdu_dbgstates_e                    dm2pipe_cmd_i,              // Command from Debug Module
    output logic                                        pipe2dm_cmd_resp_o,         // Response to Debug Module
    output logic                                        pipe2dm_cmd_rcode_o,        // Debug Module return code: 0 - Ok; 1 - Error
    output logic                                        pipe2dm_hart_event_o,       // HART event flag
    output type_scr1_hdu_hartstatus_s                   pipe2dm_hart_status_o,      // HART status

    // DM <-> Pipeline: Program Buffer - HART instruction execution i/f
    output logic [SCR1_HDU_PBUF_ADDR_WIDTH-1:0]         pipe2dm_pbuf_addr_o,        // Program Buffer address
    input  logic [SCR1_HDU_CORE_INSTR_WIDTH-1:0]        dm2pipe_pbuf_instr_i,       // Program Buffer instruction

    // DM <-> Pipeline: HART Abstract Data regs i/f
    output logic                                        pipe2dm_dreg_req_o,         // Abstract Data Register request
    output logic                                        pipe2dm_dreg_wr_o,          // Abstract Data Register write
    output logic [`SCR1_XLEN-1:0]                       pipe2dm_dreg_wdata_o,       // Abstract Data Register write data
    input  logic                                        dm2pipe_dreg_resp_i,        // Abstract Data Register response
    input  logic                                        dm2pipe_dreg_fail_i,        // Abstract Data Register fail - possibly not needed?
    input  logic [`SCR1_XLEN-1:0]                       dm2pipe_dreg_rdata_i,       // Abstract Data Register read data

    // DM <-> Pipeling: PC i/f
    output logic [`SCR1_XLEN-1:0]                       pipe2dm_pc_sample_o,        // Current PC for sampling
`endif // SCR1_DBG_EN

    // IRQ
`ifdef SCR1_IPIC_EN
    input   logic [SCR1_IRQ_LINES_NUM-1:0]              soc2pipe_irq_lines_i,       // External interrupt request lines
`else // SCR1_IPIC_EN
    input   logic                                       soc2pipe_irq_ext_i,         // External interrupt request
`endif // SCR1_IPIC_EN
    input   logic                                       soc2pipe_irq_soft_i,        // Software generated interrupt request
    input   logic                                       soc2pipe_irq_mtimer_i,      // Machine timer interrupt request

    // Memory-mapped external timer
    input   logic [63:0]                                soc2pipe_mtimer_val_i,      // Machine timer value

`ifdef SCR1_CLKCTRL_EN
    // CLK_CTRL interface
    output  logic                                       pipe2clkctl_sleep_req_o,    // CLK disable request to CLK gating circuit
    output  logic                                       pipe2clkctl_wake_req_o,     // CLK enable request to CLK gating circuit
    input   logic                                       clkctl2pipe_clk_alw_on_i,   // Not gated CLK
    input   logic                                       clkctl2pipe_clk_dbgc_i,     // CLK for HDU (not gated for now)
    input   logic                                       clkctl2pipe_clk_en_i,       // CLK enabled flag
`endif // SCR1_CLKCTRL_EN

    // Fuse
    input   logic [`SCR1_XLEN-1:0]                      soc2pipe_fuse_mhartid_i     // Fuse MHARTID value
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
logic                                       brkpt;                  // Breakpoint (sw) on current instruction
logic                                       exu_init_pc;            // Reset exit
logic                                       wfi_run2halt;           // Transition to WFI halted state
logic                                       instret;                // Instruction retirement (with or without exception)
logic                                       instret_nexc;           // Instruction retirement (without exception)
`ifdef SCR1_IPIC_EN
logic                                       ipic2csr_irq;           // IRQ request from IPIC
`endif // SCR1_IPIC_EN
`ifdef SCR1_TDU_EN
logic                                       brkpt_hw;               // Hardware breakpoint on current instruction
`endif // SCR1_TDU_EN
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
logic                                       idu2exu_use_rs1;        // Instruction uses rs1
logic                                       idu2exu_use_rs2;        // Instruction uses rs2
logic                                       idu2exu_use_rd;         // Instruction uses rd
logic                                       idu2exu_use_imm;        // Instruction uses immediate
logic                                       exu2idu_rdy;            // EXU ready for new data

// EXU <-> MPRF
logic [`SCR1_MPRF_AWIDTH-1:0]               exu2mprf_rs1_addr;      // MPRF rs1 read address
logic [`SCR1_XLEN-1:0]                      mprf2exu_rs1_data;      // MPRF rs1 read data
logic [`SCR1_MPRF_AWIDTH-1:0]               exu2mprf_rs2_addr;      // MPRF rs2 read address
logic [`SCR1_XLEN-1:0]                      mprf2exu_rs2_data;      // MPRF rs2 read data
logic                                       exu2mprf_w_req;         // MPRF write request
logic [`SCR1_MPRF_AWIDTH-1:0]               exu2mprf_rd_addr;       // MPRF rd write address
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

`ifdef SCR1_TDU_EN
// CSR <-> TDU
logic                                       csr2tdu_req;           // Request to TDU
type_scr1_csr_cmd_sel_e                     csr2tdu_cmd;           // TDU command
logic [SCR1_CSR_ADDR_TDU_OFFS_W-1:0]        csr2tdu_addr;          // TDU address
logic [`SCR1_XLEN-1:0]                      csr2tdu_wdata;         // TDU write data
logic [`SCR1_XLEN-1:0]                      tdu2csr_rdata;         // TDU read data
type_scr1_csr_resp_e                        tdu2csr_resp;          // TDU response
 `ifdef SCR1_DBG_EN
                                                                    // Qualified TDU input signals from pipe_rst_n
                                                                    // reset domain:
logic                                       csr2tdu_req_qlfy;      //     Request to TDU
 `endif // SCR1_DBG_EN

// EXU/LSU <-> TDU
type_scr1_brkm_instr_mon_s                  exu2tdu_i_mon;         // Instruction monitor
type_scr1_brkm_lsu_mon_s                    lsu2tdu_d_mon;         // Data monitor
logic [SCR1_TDU_ALLTRIG_NUM-1:0]            tdu2exu_i_match;       // Instruction breakpoint(s) match
logic [SCR1_TDU_MTRIG_NUM-1:0]              tdu2lsu_d_match;       // Data breakpoint(s) match
logic                                       tdu2exu_i_x_req;       // Instruction breakpoint exception
logic                                       tdu2lsu_i_x_req;       // Instruction breakpoint exception
logic                                       tdu2lsu_d_x_req;       // Data breakpoint exception
logic [SCR1_TDU_ALLTRIG_NUM-1:0]            exu2tdu_bp_retire;     // Instruction with breakpoint flag retire
 `ifdef SCR1_DBG_EN
                                                                    // Qualified TDU input signals from pipe_rst_n
                                                                    // reset domain:
type_scr1_brkm_instr_mon_s                  exu2tdu_i_mon_qlfy;         // Instruction monitor
type_scr1_brkm_lsu_mon_s                    lsu2tdu_d_mon_qlfy;         // Data monitor
logic [SCR1_TDU_ALLTRIG_NUM-1:0]            exu2tdu_bp_retire_qlfy;     // Instruction with breakpoint flag retire
 `endif // SCR1_DBG_EN
`endif // SCR1_TDU_EN

`ifdef SCR1_DBG_EN
// Debug signals:
logic                                       fetch_pbuf;             // Fetch instructions provided by Program Buffer (via HDU)
logic                                       csr2hdu_req;            // Request to HDU
type_scr1_csr_cmd_sel_e                     csr2hdu_cmd;            // HDU command
logic [SCR1_HDU_DEBUGCSR_ADDR_WIDTH-1:0]    csr2hdu_addr;           // HDU address
logic [`SCR1_XLEN-1:0]                      csr2hdu_wdata;          // HDU write data
logic [`SCR1_XLEN-1:0]                      hdu2csr_rdata;          // HDU read data
type_scr1_csr_resp_e                        hdu2csr_resp;           // HDU response
                                                                    // Qualified HDU input signals from pipe_rst_n
                                                                    // reset domain:
logic                                       csr2hdu_req_qlfy;       //     Request to HDU

logic                                       hwbrk_dsbl;             // Disables TDU
logic                                       hdu_hwbrk_dsbl;         // Disables TDU
logic                                       tdu2hdu_dmode_req;      // TDU requests transition to debug mode

logic                                       exu_no_commit;          // Forbid instruction commitment
logic                                       exu_irq_dsbl;           // Disable IRQ
logic                                       exu_pc_advmt_dsbl;      // Forbid PC advancement
logic                                       exu_dmode_sstep_en;     // Enable single-step

logic                                       dbg_halted;             // Debug halted state
logic                                       dbg_run2halt;           // Transition to debug halted state
logic                                       dbg_halt2run;           // Transition to run state
logic                                       dbg_run_start;          // First cycle of run state
logic [`SCR1_XLEN-1:0]                      dbg_new_pc;             // New PC as starting point for HART Resume

logic                                       ifu2hdu_pbuf_rdy;
logic                                       hdu2ifu_pbuf_vd;
logic                                       hdu2ifu_pbuf_err;
logic [SCR1_HDU_CORE_INSTR_WIDTH-1:0]       hdu2ifu_pbuf_instr;

// Qualified HDU input signals from pipe_rst_n reset domain:
logic                                       ifu2hdu_pbuf_rdy_qlfy;
logic                                       exu_busy_qlfy;
logic                                       instret_qlfy;
logic                                       exu_init_pc_qlfy;
logic                                       exu_exc_req_qlfy;
logic                                       brkpt_qlfy;

`endif // SCR1_DBG_EN

logic                                       exu_busy;


`ifndef SCR1_CLKCTRL_EN
logic                                       pipe2clkctl_wake_req_o;
`endif // SCR1_CLKCTRL_EN

//-------------------------------------------------------------------------------
// Pipeline logic
//-------------------------------------------------------------------------------
assign stop_fetch   = wfi_run2halt
`ifdef SCR1_DBG_EN
                    | fetch_pbuf
`endif // SCR1_DBG_EN
                    ;

`ifdef SCR1_CLKCTRL_EN
assign pipe2clkctl_sleep_req_o = wfi_halted & ~imem_txns_pending;
assign pipe2clkctl_wake_req_o  = csr2exu_ip_ie
`ifdef SCR1_DBG_EN
                    | dm2pipe_active_i
`endif // SCR1_DBG_EN
                    ;
`endif // SCR1_CLKCTRL_EN

`ifdef SCR1_DBG_EN
assign pipe2dm_pc_sample_o = curr_pc;
`endif // SCR1_DBG_EN

//-------------------------------------------------------------------------------
// Instruction fetch unit
//-------------------------------------------------------------------------------
scr1_pipe_ifu i_pipe_ifu (
    .rst_n                    (pipe_rst_n         ),
    .clk                      (clk                ),

    // Instruction memory interface
    .imem2ifu_req_ack_i       (imem2pipe_req_ack_i),
    .ifu2imem_req_o           (pipe2imem_req_o    ),
    .ifu2imem_cmd_o           (pipe2imem_cmd_o    ),
    .ifu2imem_addr_o          (pipe2imem_addr_o   ),
    .imem2ifu_rdata_i         (imem2pipe_rdata_i  ),
    .imem2ifu_resp_i          (imem2pipe_resp_i   ),

    // New PC interface
    .exu2ifu_pc_new_req_i     (new_pc_req         ),
    .exu2ifu_pc_new_i         (new_pc             ),
    .pipe2ifu_stop_fetch_i    (stop_fetch         ),

`ifdef SCR1_DBG_EN
    // IFU <-> HDU Program Buffer interface
    .hdu2ifu_pbuf_fetch_i     (fetch_pbuf         ),
    .ifu2hdu_pbuf_rdy_o       (ifu2hdu_pbuf_rdy   ),
    .hdu2ifu_pbuf_vd_i        (hdu2ifu_pbuf_vd    ),
    .hdu2ifu_pbuf_err_i       (hdu2ifu_pbuf_err   ),
    .hdu2ifu_pbuf_instr_i     (hdu2ifu_pbuf_instr ),
`endif // SCR1_DBG_EN
`ifdef SCR1_CLKCTRL_EN
    .ifu2pipe_imem_txns_pnd_o (imem_txns_pending  ),
`endif // SCR1_CLKCTRL_EN

    // IFU <-> IDU interface
    .idu2ifu_rdy_i            (idu2ifu_rdy        ),
    .ifu2idu_instr_o          (ifu2idu_instr      ),
    .ifu2idu_imem_err_o       (ifu2idu_imem_err   ),
    .ifu2idu_err_rvi_hi_o     (ifu2idu_err_rvi_hi ),
    .ifu2idu_vd_o             (ifu2idu_vd         )
);

//-------------------------------------------------------------------------------
// Instruction decode unit
//-------------------------------------------------------------------------------
scr1_pipe_idu i_pipe_idu (
`ifdef SCR1_TRGT_SIMULATION
    .rst_n                  (pipe_rst_n        ),
    .clk                    (clk               ),
`endif // SCR1_TRGT_SIMULATION
    .idu2ifu_rdy_o          (idu2ifu_rdy       ),
    .ifu2idu_instr_i        (ifu2idu_instr     ),
    .ifu2idu_imem_err_i     (ifu2idu_imem_err  ),
    .ifu2idu_err_rvi_hi_i   (ifu2idu_err_rvi_hi),
    .ifu2idu_vd_i           (ifu2idu_vd        ),

    .idu2exu_req_o          (idu2exu_req       ),
    .idu2exu_cmd_o          (idu2exu_cmd       ),
    .idu2exu_use_rs1_o      (idu2exu_use_rs1   ),
    .idu2exu_use_rs2_o      (idu2exu_use_rs2   ),
    .idu2exu_use_rd_o       (idu2exu_use_rd    ),
    .idu2exu_use_imm_o      (idu2exu_use_imm   ),
    .exu2idu_rdy_i          (exu2idu_rdy       )
);

//-------------------------------------------------------------------------------
// Execution unit
//-------------------------------------------------------------------------------
scr1_pipe_exu i_pipe_exu (
    .rst_n                          (pipe_rst_n              ),
    .clk                            (clk                     ),
`ifdef SCR1_CLKCTRL_EN
    .clk_alw_on                     (clkctl2pipe_clk_alw_on_i),
    .clk_pipe_en                    (clkctl2pipe_clk_en_i),
`endif // SCR1_CLKCTRL_EN

    // IDU <-> EXU interface
    .idu2exu_req_i                  (idu2exu_req             ),
    .exu2idu_rdy_o                  (exu2idu_rdy             ),
    .idu2exu_cmd_i                  (idu2exu_cmd             ),
    .idu2exu_use_rs1_i              (idu2exu_use_rs1         ),
    .idu2exu_use_rs2_i              (idu2exu_use_rs2         ),
`ifndef SCR1_NO_EXE_STAGE
    .idu2exu_use_rd_i               (idu2exu_use_rd          ),
    .idu2exu_use_imm_i              (idu2exu_use_imm         ),
`endif // SCR1_NO_EXE_STAGE

    // EXU <-> MPRF interface
    .exu2mprf_rs1_addr_o            (exu2mprf_rs1_addr       ),
    .mprf2exu_rs1_data_i            (mprf2exu_rs1_data       ),
    .exu2mprf_rs2_addr_o            (exu2mprf_rs2_addr       ),
    .mprf2exu_rs2_data_i            (mprf2exu_rs2_data       ),
    .exu2mprf_w_req_o               (exu2mprf_w_req          ),
    .exu2mprf_rd_addr_o             (exu2mprf_rd_addr        ),
    .exu2mprf_rd_data_o             (exu2mprf_rd_data        ),

    // EXU <-> CSR read/write interface
    .exu2csr_rw_addr_o              (exu2csr_rw_addr         ),
    .exu2csr_r_req_o                (exu2csr_r_req           ),
    .csr2exu_r_data_i               (csr2exu_r_data          ),
    .exu2csr_w_req_o                (exu2csr_w_req           ),
    .exu2csr_w_cmd_o                (exu2csr_w_cmd           ),
    .exu2csr_w_data_o               (exu2csr_w_data          ),
    .csr2exu_rw_exc_i               (csr2exu_rw_exc          ),

    // EXU <-> CSR event interface
    .exu2csr_take_irq_o             (exu2csr_take_irq        ),
    .exu2csr_take_exc_o             (exu2csr_take_exc        ),
    .exu2csr_mret_update_o          (exu2csr_mret_update     ),
    .exu2csr_mret_instr_o           (exu2csr_mret_instr      ),
    .exu2csr_exc_code_o             (exu2csr_exc_code        ),
    .exu2csr_trap_val_o             (exu2csr_trap_val        ),
    .csr2exu_new_pc_i               (csr2exu_new_pc          ),
    .csr2exu_irq_i                  (csr2exu_irq             ),
    .csr2exu_ip_ie_i                (csr2exu_ip_ie           ),
    .csr2exu_mstatus_mie_up_i       (csr2exu_mstatus_mie_up  ),

    // EXU <-> DMEM interface
    .exu2dmem_req_o                 (pipe2dmem_req_o         ),
    .exu2dmem_cmd_o                 (pipe2dmem_cmd_o         ),
    .exu2dmem_width_o               (pipe2dmem_width_o       ),
    .exu2dmem_addr_o                (pipe2dmem_addr_o        ),
    .exu2dmem_wdata_o               (pipe2dmem_wdata_o       ),
    .dmem2exu_req_ack_i             (dmem2pipe_req_ack_i     ),
    .dmem2exu_rdata_i               (dmem2pipe_rdata_i       ),
    .dmem2exu_resp_i                (dmem2pipe_resp_i        ),

`ifdef SCR1_DBG_EN
    // EXU <-> HDU interface
    .hdu2exu_no_commit_i            (exu_no_commit           ),
    .hdu2exu_irq_dsbl_i             (exu_irq_dsbl            ),
    .hdu2exu_pc_advmt_dsbl_i        (exu_pc_advmt_dsbl       ),
    .hdu2exu_dmode_sstep_en_i       (exu_dmode_sstep_en      ),
    .hdu2exu_pbuf_fetch_i           (fetch_pbuf              ),
    .hdu2exu_dbg_halted_i           (dbg_halted              ),
    .hdu2exu_dbg_run2halt_i         (dbg_run2halt            ),
    .hdu2exu_dbg_halt2run_i         (dbg_halt2run            ),
    .hdu2exu_dbg_run_start_i        (dbg_run_start           ),
    .hdu2exu_dbg_new_pc_i           (dbg_new_pc              ),
`endif // SCR1_DBG_EN

`ifdef SCR1_TDU_EN
    // EXU <-> TDU interface
    .exu2tdu_imon_o                 (exu2tdu_i_mon           ),
    .tdu2exu_ibrkpt_match_i         (tdu2exu_i_match         ),
    .tdu2exu_ibrkpt_exc_req_i       (tdu2exu_i_x_req         ),
    .lsu2tdu_dmon_o                 (lsu2tdu_d_mon           ),
    .tdu2lsu_ibrkpt_exc_req_i       (tdu2lsu_i_x_req         ),
    .tdu2lsu_dbrkpt_match_i         (tdu2lsu_d_match         ),
    .tdu2lsu_dbrkpt_exc_req_i       (tdu2lsu_d_x_req         ),
    .exu2tdu_ibrkpt_ret_o           (exu2tdu_bp_retire       ),
    .exu2hdu_ibrkpt_hw_o            (brkpt_hw                ),
`endif // SCR1_TDU_EN

    // EXU control
    .exu2pipe_exc_req_o             (exu_exc_req             ),
    .exu2pipe_brkpt_o               (brkpt                   ),
    .exu2pipe_init_pc_o             (exu_init_pc             ),
    .exu2pipe_wfi_run2halt_o        (wfi_run2halt            ),
    .exu2pipe_instret_o             (instret                 ),
    .exu2csr_instret_no_exc_o       (instret_nexc            ),
    .exu2pipe_exu_busy_o            (exu_busy                ),

    // PC interface
`ifdef SCR1_CLKCTRL_EN
    .exu2pipe_wfi_halted_o          (wfi_halted              ),
`endif // SCR1_CLKCTRL_EN
    .exu2pipe_pc_curr_o             (curr_pc                 ),
    .exu2csr_pc_next_o              (next_pc                 ),
    .exu2ifu_pc_new_req_o           (new_pc_req              ),
    .exu2ifu_pc_new_o               (new_pc                  )
);

//-------------------------------------------------------------------------------
// Multi-port register file
//-------------------------------------------------------------------------------
scr1_pipe_mprf i_pipe_mprf (
`ifdef SCR1_MPRF_RST_EN
    .rst_n                  (pipe_rst_n       ),
`endif // SCR1_MPRF_RST_EN
    .clk                    (clk              ),

    // EXU <-> MPRF interface
    .exu2mprf_rs1_addr_i    (exu2mprf_rs1_addr),
    .mprf2exu_rs1_data_o    (mprf2exu_rs1_data),
    .exu2mprf_rs2_addr_i    (exu2mprf_rs2_addr),
    .mprf2exu_rs2_data_o    (mprf2exu_rs2_data),
    .exu2mprf_w_req_i       (exu2mprf_w_req   ),
    .exu2mprf_rd_addr_i     (exu2mprf_rd_addr ),
    .exu2mprf_rd_data_i     (exu2mprf_rd_data )
);

//-------------------------------------------------------------------------------
// Control and status registers
//-------------------------------------------------------------------------------
scr1_pipe_csr i_pipe_csr (
    .rst_n                      (pipe_rst_n              ),
    .clk                        (clk                     ),
`ifdef SCR1_CLKCTRL_EN
    .clk_alw_on                 (clkctl2pipe_clk_alw_on_i),
`endif // SCR1_CLKCTRL_EN

    // EXU <-> CSR read/write interface
    .exu2csr_r_req_i            (exu2csr_r_req           ),
    .exu2csr_rw_addr_i          (exu2csr_rw_addr         ),
    .csr2exu_r_data_o           (csr2exu_r_data          ),
    .exu2csr_w_req_i            (exu2csr_w_req           ),
    .exu2csr_w_cmd_i            (exu2csr_w_cmd           ),
    .exu2csr_w_data_i           (exu2csr_w_data          ),
    .csr2exu_rw_exc_o           (csr2exu_rw_exc          ),

    // EXU <-> CSR event interface
    .exu2csr_take_irq_i         (exu2csr_take_irq        ),
    .exu2csr_take_exc_i         (exu2csr_take_exc        ),
    .exu2csr_mret_update_i      (exu2csr_mret_update     ),
    .exu2csr_mret_instr_i       (exu2csr_mret_instr      ),
    .exu2csr_exc_code_i         (exu2csr_exc_code        ),
    .exu2csr_trap_val_i         (exu2csr_trap_val        ),
    .csr2exu_new_pc_o           (csr2exu_new_pc          ),
    .csr2exu_irq_o              (csr2exu_irq             ),
    .csr2exu_ip_ie_o            (csr2exu_ip_ie           ),
    .csr2exu_mstatus_mie_up_o   (csr2exu_mstatus_mie_up  ),

`ifdef SCR1_IPIC_EN
    // CSR <-> IPIC interface
    .csr2ipic_r_req_o           (csr2ipic_r_req          ),
    .csr2ipic_w_req_o           (csr2ipic_w_req          ),
    .csr2ipic_addr_o            (csr2ipic_addr           ),
    .csr2ipic_wdata_o           (csr2ipic_wdata          ),
    .ipic2csr_rdata_i           (ipic2csr_rdata          ),
`endif // SCR1_IPIC_EN

    // CSR <-> PC interface
    .exu2csr_pc_curr_i          (curr_pc                 ),
    .exu2csr_pc_next_i          (next_pc                 ),
`ifndef SCR1_CSR_REDUCED_CNT
    .exu2csr_instret_no_exc_i   (instret_nexc            ),
`endif // SCR1_CSR_REDUCED_CNT

    // IRQ
`ifdef SCR1_IPIC_EN
    .soc2csr_irq_ext_i          (ipic2csr_irq            ),
`else // SCR1_IPIC_EN
    .soc2csr_irq_ext_i          (soc2pipe_irq_ext_i      ),
`endif // SCR1_IPIC_EN
    .soc2csr_irq_soft_i         (soc2pipe_irq_soft_i     ),
    .soc2csr_irq_mtimer_i       (soc2pipe_irq_mtimer_i   ),

    // Memory-mapped external timer
    .soc2csr_mtimer_val_i       (soc2pipe_mtimer_val_i   ),

`ifdef SCR1_DBG_EN
    // CSR <-> HDU interface
    .csr2hdu_req_o              (csr2hdu_req             ),
    .csr2hdu_cmd_o              (csr2hdu_cmd             ),
    .csr2hdu_addr_o             (csr2hdu_addr            ),
    .csr2hdu_wdata_o            (csr2hdu_wdata           ),
    .hdu2csr_rdata_i            (hdu2csr_rdata           ),
    .hdu2csr_resp_i             (hdu2csr_resp            ),
    .hdu2csr_no_commit_i        (exu_no_commit           ),
`endif // SCR1_DBG_EN

`ifdef SCR1_TDU_EN
    // CSR <-> TDU interface
    .csr2tdu_req_o              (csr2tdu_req             ),
    .csr2tdu_cmd_o              (csr2tdu_cmd             ),
    .csr2tdu_addr_o             (csr2tdu_addr            ),
    .csr2tdu_wdata_o            (csr2tdu_wdata           ),
    .tdu2csr_rdata_i            (tdu2csr_rdata           ),
    .tdu2csr_resp_i             (tdu2csr_resp            ),
`endif // SCR1_TDU_EN
    .soc2csr_fuse_mhartid_i     (soc2pipe_fuse_mhartid_i )
);

//-------------------------------------------------------------------------------
// Integrated programmable interrupt controller
//-------------------------------------------------------------------------------
`ifdef SCR1_IPIC_EN
scr1_ipic i_pipe_ipic (
    .rst_n                  (pipe_rst_n              ),
`ifdef SCR1_CLKCTRL_EN
    .clk                    (clkctl2pipe_clk_alw_on_i),
`else // SCR1_CLKCTRL_EN
    .clk                    (clk                     ),
`endif // SCR1_CLKCTRL_EN
    .soc2ipic_irq_lines_i   (soc2pipe_irq_lines_i    ),
    .csr2ipic_r_req_i       (csr2ipic_r_req          ),
    .csr2ipic_w_req_i       (csr2ipic_w_req          ),
    .csr2ipic_addr_i        (csr2ipic_addr           ),
    .csr2ipic_wdata_i       (csr2ipic_wdata          ),
    .ipic2csr_rdata_o       (ipic2csr_rdata          ),
    .ipic2csr_irq_m_req_o   (ipic2csr_irq            )
);
`endif // SCR1_IPIC_EN

//-------------------------------------------------------------------------------
// Breakpoint module
//-------------------------------------------------------------------------------
`ifdef SCR1_TDU_EN
scr1_pipe_tdu i_pipe_tdu (
    // Common signals
 `ifdef SCR1_DBG_EN
    .rst_n                      (dbg_rst_n             ),
 `else
    .rst_n                      (pipe_rst_n            ),
 `endif // SCR1_DBG_EN
    .clk                        (clk                   ),
    .clk_en                     (1'b1                  ),
 `ifdef SCR1_DBG_EN
    .tdu_dsbl_i                 (hwbrk_dsbl            ),
 `else // SCR1_DBG_EN
    .tdu_dsbl_i                 (1'b0                  ),
 `endif // SCR1_DBG_EN

    // TDU <-> CSR interface
 `ifdef SCR1_DBG_EN
    .csr2tdu_req_i              (csr2tdu_req_qlfy      ),
    .csr2tdu_cmd_i              (csr2tdu_cmd           ),
    .csr2tdu_addr_i             (csr2tdu_addr          ),
    .csr2tdu_wdata_i            (csr2tdu_wdata         ),
 `else // SCR1_DBG_EN
    .csr2tdu_req_i              (csr2tdu_req           ),
    .csr2tdu_cmd_i              (csr2tdu_cmd           ),
    .csr2tdu_addr_i             (csr2tdu_addr          ),
    .csr2tdu_wdata_i            (csr2tdu_wdata         ),
 `endif // SCR1_DBG_EN
    .tdu2csr_rdata_o            (tdu2csr_rdata         ),
    .tdu2csr_resp_o             (tdu2csr_resp          ),

    // TDU <-> EXU interface
 `ifdef SCR1_DBG_EN
    .exu2tdu_imon_i             (exu2tdu_i_mon_qlfy    ),
 `else // SCR1_DBG_EN
    .exu2tdu_imon_i             (exu2tdu_i_mon         ),
 `endif // SCR1_DBG_EN
    .tdu2exu_ibrkpt_match_o     (tdu2exu_i_match       ),
    .tdu2exu_ibrkpt_exc_req_o   (tdu2exu_i_x_req       ),
 `ifdef SCR1_DBG_EN
    .exu2tdu_bp_retire_i        (exu2tdu_bp_retire_qlfy),
 `else // SCR1_DBG_EN
    .exu2tdu_bp_retire_i        (exu2tdu_bp_retire     ),
 `endif // SCR1_DBG_EN

    // TDU <-> LSU interface
    .tdu2lsu_ibrkpt_exc_req_o   (tdu2lsu_i_x_req       ),
 `ifdef SCR1_DBG_EN
    .lsu2tdu_dmon_i             (lsu2tdu_d_mon_qlfy    ),
 `else // SCR1_DBG_EN
    .lsu2tdu_dmon_i             (lsu2tdu_d_mon         ),
 `endif // SCR1_DBG_EN
    .tdu2lsu_dbrkpt_match_o     (tdu2lsu_d_match       ),
    .tdu2lsu_dbrkpt_exc_req_o   (tdu2lsu_d_x_req       ),
    // EPU I/F
 `ifdef SCR1_DBG_EN
    .tdu2hdu_dmode_req_o        (tdu2hdu_dmode_req     )
 `else // SCR1_DBG_EN
    .tdu2hdu_dmode_req_o        (                      )
 `endif // SCR1_DBG_EN
);

 `ifdef SCR1_DBG_EN
assign hwbrk_dsbl               = (~dbg_en) | hdu_hwbrk_dsbl;
//
assign csr2tdu_req_qlfy         = dbg_en & csr2tdu_req & pipe2hdu_rdc_qlfy_i;
//
assign exu2tdu_i_mon_qlfy.vd    = exu2tdu_i_mon.vd & pipe2hdu_rdc_qlfy_i;
assign exu2tdu_i_mon_qlfy.req   = exu2tdu_i_mon.req;
assign exu2tdu_i_mon_qlfy.addr  = exu2tdu_i_mon.addr;
assign lsu2tdu_d_mon_qlfy.vd    = lsu2tdu_d_mon.vd & pipe2hdu_rdc_qlfy_i;
assign lsu2tdu_d_mon_qlfy.load  = lsu2tdu_d_mon.load;
assign lsu2tdu_d_mon_qlfy.store = lsu2tdu_d_mon.store;
assign lsu2tdu_d_mon_qlfy.addr  = lsu2tdu_d_mon.addr;
assign exu2tdu_bp_retire_qlfy   = exu2tdu_bp_retire & {$bits(exu2tdu_bp_retire){pipe2hdu_rdc_qlfy_i}};
 `endif // SCR1_DBG_EN

`endif // SCR1_TDU_EN

//-------------------------------------------------------------------------------
// HART Debug Unit (HDU)
//-------------------------------------------------------------------------------
`ifdef SCR1_DBG_EN
scr1_pipe_hdu i_pipe_hdu (
    // Common signals
    .rst_n                      (dbg_rst_n             ),
    .clk_en                     (dm2pipe_active_i      ),
`ifdef SCR1_CLKCTRL_EN
    .clk_pipe_en                (clkctl2pipe_clk_en_i  ),
    .clk                        (clkctl2pipe_clk_dbgc_i),
`else
    .clk                        (clk                   ),
`endif // SCR1_CLKCTRL_EN

    // Control/status registers i/f
    .csr2hdu_req_i              (csr2hdu_req_qlfy      ),
    .csr2hdu_cmd_i              (csr2hdu_cmd           ),
    .csr2hdu_addr_i             (csr2hdu_addr          ),
    .csr2hdu_wdata_i            (csr2hdu_wdata         ),
    .hdu2csr_resp_o             (hdu2csr_resp          ),
    .hdu2csr_rdata_o            (hdu2csr_rdata         ),

    // HART Run Control i/f
    .pipe2hdu_rdc_qlfy_i        (pipe2hdu_rdc_qlfy_i   ),
    .dm2hdu_cmd_req_i           (dm2pipe_cmd_req_i     ),
    .dm2hdu_cmd_i               (dm2pipe_cmd_i         ),
    .hdu2dm_cmd_resp_o          (pipe2dm_cmd_resp_o    ),
    .hdu2dm_cmd_rcode_o         (pipe2dm_cmd_rcode_o   ),
    .hdu2dm_hart_event_o        (pipe2dm_hart_event_o  ),
    .hdu2dm_hart_status_o       (pipe2dm_hart_status_o ),

    // Program Buffer - HART instruction execution i/f
    .hdu2dm_pbuf_addr_o         (pipe2dm_pbuf_addr_o   ),
    .dm2hdu_pbuf_instr_i        (dm2pipe_pbuf_instr_i  ),

    // HART Abstract Data regs i/f
    .hdu2dm_dreg_req_o          (pipe2dm_dreg_req_o    ),
    .hdu2dm_dreg_wr_o           (pipe2dm_dreg_wr_o     ),
    .hdu2dm_dreg_wdata_o        (pipe2dm_dreg_wdata_o  ),
    .dm2hdu_dreg_resp_i         (dm2pipe_dreg_resp_i   ),
    .dm2hdu_dreg_fail_i         (dm2pipe_dreg_fail_i   ),
    .dm2hdu_dreg_rdata_i        (dm2pipe_dreg_rdata_i  ),
    //
`ifdef SCR1_TDU_EN
    // HDU <-> TDU interface
    .hdu2tdu_hwbrk_dsbl_o       (hdu_hwbrk_dsbl        ),
    .tdu2hdu_dmode_req_i        (tdu2hdu_dmode_req     ),
    .exu2hdu_ibrkpt_hw_i        (brkpt_hw              ),
`endif // SCR1_TDU_EN

    // HART Run Status
    .pipe2hdu_exu_busy_i        (exu_busy_qlfy         ),
    .pipe2hdu_instret_i         (instret_qlfy          ),
    .pipe2hdu_init_pc_i         (exu_init_pc_qlfy      ),

    // HART Halt Status
    .pipe2hdu_exu_exc_req_i     (exu_exc_req_qlfy      ),
    .pipe2hdu_brkpt_i           (brkpt_qlfy            ),

    // HART Run Control
    .hdu2exu_pbuf_fetch_o       (fetch_pbuf            ),
    .hdu2exu_no_commit_o        (exu_no_commit         ),
    .hdu2exu_irq_dsbl_o         (exu_irq_dsbl          ),
    .hdu2exu_pc_advmt_dsbl_o    (exu_pc_advmt_dsbl     ),
    .hdu2exu_dmode_sstep_en_o   (exu_dmode_sstep_en    ),

    // HART state
    .hdu2exu_dbg_halted_o       (dbg_halted            ),
    .hdu2exu_dbg_run2halt_o     (dbg_run2halt          ),
    .hdu2exu_dbg_halt2run_o     (dbg_halt2run          ),
    .hdu2exu_dbg_run_start_o    (dbg_run_start         ),

    // PC interface
    .pipe2hdu_pc_curr_i         (curr_pc               ),
    .hdu2exu_dbg_new_pc_o       (dbg_new_pc            ),

    // Prgram Buffer Instruction interface
    .ifu2hdu_pbuf_instr_rdy_i   (ifu2hdu_pbuf_rdy_qlfy ),
    .hdu2ifu_pbuf_instr_vd_o    (hdu2ifu_pbuf_vd       ),
    .hdu2ifu_pbuf_instr_err_o   (hdu2ifu_pbuf_err      ),
    .hdu2ifu_pbuf_instr_o       (hdu2ifu_pbuf_instr    )
);

assign csr2hdu_req_qlfy         = csr2hdu_req & dbg_en & pipe2hdu_rdc_qlfy_i;
//
assign exu_busy_qlfy            = exu_busy          & {$bits(exu_busy){pipe2hdu_rdc_qlfy_i}};
assign instret_qlfy             = instret           & {$bits(instret){pipe2hdu_rdc_qlfy_i}};
assign exu_init_pc_qlfy         = exu_init_pc       & {$bits(exu_init_pc){pipe2hdu_rdc_qlfy_i}};
assign exu_exc_req_qlfy         = exu_exc_req       & {$bits(exu_exc_req){pipe2hdu_rdc_qlfy_i}};
assign brkpt_qlfy               = brkpt             & {$bits(brkpt){pipe2hdu_rdc_qlfy_i}};
assign ifu2hdu_pbuf_rdy_qlfy    = ifu2hdu_pbuf_rdy  & {$bits(ifu2hdu_pbuf_rdy){pipe2hdu_rdc_qlfy_i}};

`endif // SCR1_DBG_EN

`ifdef SCR1_TRGT_SIMULATION
//-------------------------------------------------------------------------------
// Tracelog
//-------------------------------------------------------------------------------

scr1_tracelog i_tracelog (
    .rst_n                          (pipe_rst_n                         ),
    .clk                            (clk                                ),
    .soc2pipe_fuse_mhartid_i        (soc2pipe_fuse_mhartid_i            ),

    // MPRF
    .mprf2trace_int_i               (i_pipe_mprf.mprf_int               ),
    .mprf2trace_wr_en_i             (i_pipe_mprf.exu2mprf_w_req_i       ),
    .mprf2trace_wr_addr_i           (i_pipe_mprf.exu2mprf_rd_addr_i     ),
    .mprf2trace_wr_data_i           (i_pipe_mprf.exu2mprf_rd_data_i     ),

    // EXU
    .exu2trace_update_pc_en_i       (i_pipe_exu.update_pc_en            ),
    .exu2trace_update_pc_i          (i_pipe_exu.update_pc               ),

    // IFU
    .ifu2trace_instr_i              (i_pipe_ifu.ifu2idu_instr_o         ),

    // CSR
    .csr2trace_mstatus_mie_i        (i_pipe_csr.csr_mstatus_mie_ff      ),
    .csr2trace_mstatus_mpie_i       (i_pipe_csr.csr_mstatus_mpie_ff     ),
    .csr2trace_mtvec_base_i         (i_pipe_csr.csr_mtvec_base          ),
    .csr2trace_mtvec_mode_i         (i_pipe_csr.csr_mtvec_mode          ),
    .csr2trace_mie_meie_i           (i_pipe_csr.csr_mie_meie_ff         ),
    .csr2trace_mie_mtie_i           (i_pipe_csr.csr_mie_mtie_ff         ),
    .csr2trace_mie_msie_i           (i_pipe_csr.csr_mie_msie_ff         ),
    .csr2trace_mip_meip_i           (i_pipe_csr.csr_mip_meip            ),
    .csr2trace_mip_mtip_i           (i_pipe_csr.csr_mip_mtip            ),
    .csr2trace_mip_msip_i           (i_pipe_csr.csr_mip_msip            ),
    .csr2trace_mepc_i               (i_pipe_csr.csr_mepc_ff             ),
    .csr2trace_mcause_irq_i         (i_pipe_csr.csr_mcause_i_ff         ),
    .csr2trace_mcause_ec_i          (i_pipe_csr.csr_mcause_ec_ff        ),
    .csr2trace_mtval_i              (i_pipe_csr.csr_mtval_ff            ),
    .csr2trace_mstatus_mie_up_i     (i_pipe_csr.csr2exu_mstatus_mie_up_o),

    // Events
    .csr2trace_e_exc_i              (i_pipe_csr.e_exc                   ),
    .csr2trace_e_irq_i              (i_pipe_csr.e_irq                   ),
    .pipe2trace_e_wake_i            (pipe2clkctl_wake_req_o             ),
    .csr2trace_e_mret_i             (i_pipe_csr.e_mret                  )
);

`endif // SCR1_TRGT_SIMULATION

endmodule : scr1_pipe_top
