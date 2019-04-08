/// Copyright by Syntacore LLC © 2016-2019. See LICENSE for details
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
`include "scr1_hdu.svh"
`endif // SCR1_DBGC_EN

`ifdef SCR1_BRKM_EN
`include "scr1_tdu.svh"
`endif // SCR1_BRKM_EN

module scr1_pipe_top (
    // Common
    input   logic                                       pipe_rst_n,
`ifdef SCR1_DBGC_EN
    input  logic                                        pipe_rst_n_qlfy,
    input  logic                                        dbg_rst_n,
`endif // SCR1_DBGC_EN
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
    // Debug interface:
    // DM <-> Pipeline: HART Run Control i/f
    input  logic                                        dm_active,
    input  logic                                        dm_cmd_req,
    input  type_scr1_hdu_dbgstates_e                    dm_cmd,
    output logic                                        dm_cmd_resp,
    output logic                                        dm_cmd_rcode, // 0 - Ok; 1 - Error
    output logic                                        dm_hart_event,
    output type_scr1_hdu_hartstatus_s                   dm_hart_status,
    // DM <-> Pipeline: Program Buffer - HART instruction execution i/f
    output logic [SCR1_HDU_PBUF_ADDR_WIDTH-1:0]         dm_pbuf_addr, // so far request only for 1 instruction
    input  logic [SCR1_HDU_CORE_INSTR_WIDTH-1:0]        dm_pbuf_instr,
    // DM <-> Pipeline: HART Abstract Data regs i/f
    output logic                                        dm_dreg_req,
    output logic                                        dm_dreg_wr,
    output logic [`SCR1_XLEN-1:0]                       dm_dreg_wdata,
    input  logic                                        dm_dreg_resp,
    input  logic                                        dm_dreg_fail, // ? - possibly not needed
    input  logic [`SCR1_XLEN-1:0]                       dm_dreg_rdata,
    //
    output logic [`SCR1_XLEN-1:0]                       dm_pc_sample,
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
logic                                       brkpt;                  // Breakpoint (sw) on current instruction
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
logic                                       idu2exu_use_rs1;        // Instruction uses rs1
logic                                       idu2exu_use_rs2;        // Instruction uses rs2
logic                                       idu2exu_use_rd;         // Instruction uses rd
logic                                       idu2exu_use_imm;        // Instruction uses immediate
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
// CSR <-> TDU
logic                                       csr2tdu_req;           // Request to TDU
type_scr1_csr_cmd_sel_e                     csr2tdu_cmd;           // TDU command
logic [SCR1_CSR_ADDR_TDU_OFFS_W-1:0]        csr2tdu_addr;          // TDU address
logic [`SCR1_XLEN-1:0]                      csr2tdu_wdata;         // TDU write data
logic [`SCR1_XLEN-1:0]                      tdu2csr_rdata;         // TDU read data
type_scr1_csr_resp_e                        tdu2csr_resp;          // TDU response
 `ifdef SCR1_DBGC_EN
                                                                    // Qualified TDU input signals from pipe_rst_n
                                                                    // reset domain:
logic                                       csr2tdu_req_qlfy;      //     Request to TDU
type_scr1_csr_cmd_sel_e                     csr2tdu_cmd_qlfy;      //     TDU command
logic [SCR1_CSR_ADDR_TDU_OFFS_W-1:0]        csr2tdu_addr_qlfy;     //     TDU address
logic [`SCR1_XLEN-1:0]                      csr2tdu_wdata_qlfy;    //     TDU write data
 `endif // SCR1_DBGC_EN

// EXU/LSU <-> TDU
type_scr1_brkm_instr_mon_s                  exu2tdu_i_mon;         // Instruction monitor
type_scr1_brkm_lsu_mon_s                    lsu2tdu_d_mon;         // Data monitor
logic [SCR1_TDU_ALLTRIG_NUM-1:0]            tdu2exu_i_match;       // Instruction breakpoint(s) match
logic [SCR1_TDU_MTRIG_NUM-1:0]              tdu2lsu_d_match;       // Data breakpoint(s) match
logic                                       tdu2exu_i_x_req;       // Instruction breakpoint exception
logic                                       tdu2lsu_i_x_req;       // Instruction breakpoint exception
logic                                       tdu2lsu_d_x_req;       // Data breakpoint exception
logic [SCR1_TDU_ALLTRIG_NUM-1:0]            exu2tdu_bp_retire;     // Instruction with breakpoint flag retire
 `ifdef SCR1_DBGC_EN
                                                                    // Qualified TDU input signals from pipe_rst_n
                                                                    // reset domain:
type_scr1_brkm_instr_mon_s                  exu2tdu_i_mon_qlfy;         // Instruction monitor
type_scr1_brkm_lsu_mon_s                    lsu2tdu_d_mon_qlfy;         // Data monitor
logic [SCR1_TDU_ALLTRIG_NUM-1:0]            exu2tdu_bp_retire_qlfy;     // Instruction with breakpoint flag retire
 `endif // SCR1_DBGC_EN
`endif // SCR1_BRKM_EN

`ifdef SCR1_DBGC_EN
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
type_scr1_csr_cmd_sel_e                     csr2hdu_cmd_qlfy;       //     HDU command
logic [SCR1_HDU_DEBUGCSR_ADDR_WIDTH-1:0]    csr2hdu_addr_qlfy;      //     HDU address
logic [`SCR1_XLEN-1:0]                      csr2hdu_wdata_qlfy;     //     HDU write data

logic                                       hwbrk_dsbl;             // Disables TDU
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
logic                                       exu_busy;
logic                                       exu_busy_qlfy;
logic                                       instret_qlfy;
logic                                       exu_init_pc_qlfy;
logic                                       exu_exc_req_qlfy;
logic                                       brkpt_qlfy;
logic [`SCR1_XLEN-1:0]                      curr_pc_qlfy;

`endif // SCR1_DBGC_EN


//-------------------------------------------------------------------------------
// Pipeline logic
//-------------------------------------------------------------------------------
assign stop_fetch   = wfi_run2halt
`ifdef SCR1_DBGC_EN
                    | fetch_pbuf
`endif // SCR1_DBGC_EN
                    ;

`ifdef SCR1_CLKCTRL_EN
assign sleep_pipe   = wfi_halted & ~imem_txns_pending;
assign wake_pipe    = csr2exu_ip_ie
`ifdef SCR1_DBGC_EN
                    | dm_active
`endif // SCR1_DBGC_EN
                    ;
`endif // SCR1_CLKCTRL_EN

`ifdef SCR1_DBGC_EN
assign dm_pc_sample = curr_pc;
`endif // SCR1_DBGC_EN

//-------------------------------------------------------------------------------
// Instruction fetch unit
//-------------------------------------------------------------------------------
scr1_pipe_ifu i_pipe_ifu (
    .rst_n              (pipe_rst_n         ),
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
    .fetch_pbuf         (fetch_pbuf         ),
    .ifu2hdu_pbuf_rdy   (ifu2hdu_pbuf_rdy   ),
    .hdu2ifu_pbuf_vd    (hdu2ifu_pbuf_vd    ),
    .hdu2ifu_pbuf_err   (hdu2ifu_pbuf_err   ),
    .hdu2ifu_pbuf_instr (hdu2ifu_pbuf_instr ),
`endif // SCR1_DBGC_EN
`ifdef SCR1_CLKCTRL_EN
    .imem_txns_pending  (imem_txns_pending  ),
`endif // SCR1_CLKCTRL_EN
    .idu2ifu_rdy        (idu2ifu_rdy        ),
    .ifu2idu_instr      (ifu2idu_instr      ),
    .ifu2idu_imem_err   (ifu2idu_imem_err   ),
    .ifu2idu_err_rvi_hi (ifu2idu_err_rvi_hi ),
    .ifu2idu_vd         (ifu2idu_vd         )
);

//-------------------------------------------------------------------------------
// Instruction decode unit
//-------------------------------------------------------------------------------
scr1_pipe_idu i_pipe_idu (
`ifdef SCR1_SIM_ENV
    .rst_n              (pipe_rst_n         ),
    .clk                (clk                ),
`endif // SCR1_SIM_ENV
    .idu2ifu_rdy        (idu2ifu_rdy        ),
    .ifu2idu_instr      (ifu2idu_instr      ),
    .ifu2idu_imem_err   (ifu2idu_imem_err   ),
    .ifu2idu_err_rvi_hi (ifu2idu_err_rvi_hi ),
    .ifu2idu_vd         (ifu2idu_vd         ),

    .idu2exu_req        (idu2exu_req        ),
    .idu2exu_cmd        (idu2exu_cmd        ),
    .idu2exu_use_rs1    (idu2exu_use_rs1    ),
    .idu2exu_use_rs2    (idu2exu_use_rs2    ),
    .idu2exu_use_rd     (idu2exu_use_rd     ),
    .idu2exu_use_imm    (idu2exu_use_imm    ),
    .exu2idu_rdy        (exu2idu_rdy        )
);

//-------------------------------------------------------------------------------
// Execution unit
//-------------------------------------------------------------------------------
scr1_pipe_exu i_pipe_exu (
    .rst_n                  (pipe_rst_n           ),
    .clk                    (clk                  ),
`ifdef SCR1_CLKCTRL_EN
    .clk_alw_on             (clk_alw_on           ),
    .clk_pipe_en            (clk_pipe_en          ),
`endif // SCR1_CLKCTRL_EN
    .idu2exu_req            (idu2exu_req          ),
    .exu2idu_rdy            (exu2idu_rdy          ),
    .idu2exu_cmd            (idu2exu_cmd          ),
    .idu2exu_use_rs1        (idu2exu_use_rs1      ),
    .idu2exu_use_rs2        (idu2exu_use_rs2      ),
`ifndef SCR1_EXU_STAGE_BYPASS
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
    .fetch_pbuf             (fetch_pbuf           ),
    .dbg_halted             (dbg_halted           ),
    .dbg_run2halt           (dbg_run2halt         ),
    .dbg_halt2run           (dbg_halt2run         ),
    .dbg_run_start          (dbg_run_start        ),
    .dbg_new_pc             (dbg_new_pc           ),
`endif // SCR1_DBGC_EN
`ifdef SCR1_BRKM_EN
    .exu2tdu_i_mon          (exu2tdu_i_mon        ),
    .tdu2exu_i_match        (tdu2exu_i_match      ),
    .tdu2exu_i_x_req        (tdu2exu_i_x_req      ),
    .lsu2tdu_d_mon          (lsu2tdu_d_mon        ),
    .tdu2lsu_i_x_req        (tdu2lsu_i_x_req      ),
    .tdu2lsu_d_match        (tdu2lsu_d_match      ),
    .tdu2lsu_d_x_req        (tdu2lsu_d_x_req      ),
    .exu2tdu_bp_retire      (exu2tdu_bp_retire    ),
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

    .exu_busy               (exu_busy             )
);

//-------------------------------------------------------------------------------
// Multi-port register file
//-------------------------------------------------------------------------------
scr1_pipe_mprf i_pipe_mprf (
`ifdef SCR1_MPRF_RST_EN
    .rst_n                  (pipe_rst_n       ),
`endif // SCR1_MPRF_RST_EN
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
    .rst_n                  (pipe_rst_n         ),
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
    // CSR <-> HDU interface
    .csr2hdu_req            (csr2hdu_req        ),
    .csr2hdu_cmd            (csr2hdu_cmd        ),
    .csr2hdu_addr           (csr2hdu_addr       ),
    .csr2hdu_wdata          (csr2hdu_wdata      ),
    .hdu2csr_rdata          (hdu2csr_rdata      ),
    .hdu2csr_resp           (hdu2csr_resp       ),
`endif // SCR1_DBGC_EN
`ifdef SCR1_BRKM_EN
    .csr2tdu_req            (csr2tdu_req       ),
    .csr2tdu_cmd            (csr2tdu_cmd       ),
    .csr2tdu_addr           (csr2tdu_addr      ),
    .csr2tdu_wdata          (csr2tdu_wdata     ),
    .tdu2csr_rdata          (tdu2csr_rdata     ),
    .tdu2csr_resp           (tdu2csr_resp      ),
`endif // SCR1_BRKM_EN
    .fuse_mhartid           (fuse_mhartid       )
);

//-------------------------------------------------------------------------------
// Integrated programmable interrupt controller
//-------------------------------------------------------------------------------
`ifdef SCR1_IPIC_EN
scr1_ipic i_pipe_ipic (
    .rst_n              (pipe_rst_n     ),
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
scr1_pipe_tdu i_pipe_tdu (
    // Common signals
 `ifdef SCR1_DBGC_EN
    .rst_n                  (dbg_rst_n              ),
 `else
    .rst_n                  (rst_n                  ),
 `endif // SCR1_DBGC_EN
    .clk                    (clk                    ),
    .clk_en                 (1'b1                   ),
 `ifdef SCR1_DBGC_EN
    .dsbl                   (hwbrk_dsbl             ),
 `else // SCR1_DBGC_EN
    .dsbl                   (1'b0                   ),
 `endif // SCR1_DBGC_EN

    // CSR I/F
 `ifdef SCR1_DBGC_EN
    .csr2tdu_req            (csr2tdu_req_qlfy      ),
    .csr2tdu_cmd            (csr2tdu_cmd_qlfy      ),
    .csr2tdu_addr           (csr2tdu_addr_qlfy     ),
    .csr2tdu_wdata          (csr2tdu_wdata_qlfy    ),
 `else // SCR1_DBGC_EN
    .csr2tdu_req            (csr2tdu_req           ),
    .csr2tdu_cmd            (csr2tdu_cmd           ),
    .csr2tdu_addr           (csr2tdu_addr          ),
    .csr2tdu_wdata          (csr2tdu_wdata         ),
 `endif // SCR1_DBGC_EN
    .csr2tdu_rdata          (tdu2csr_rdata         ),
    .csr2tdu_resp           (tdu2csr_resp          ),
    // ID I/F
 `ifdef SCR1_DBGC_EN
    .exu2tdu_i_mon          (exu2tdu_i_mon_qlfy    ),
 `else // SCR1_DBGC_EN
    .exu2tdu_i_mon          (exu2tdu_i_mon         ),
 `endif // SCR1_DBGC_EN
    // CFU I/F
    .tdu2exu_i_match        (tdu2exu_i_match       ),
    .tdu2exu_i_x_req        (tdu2exu_i_x_req       ),
    // LSU I/F
    .tdu2lsu_i_x_req        (tdu2lsu_i_x_req       ),
 `ifdef SCR1_DBGC_EN
    .tdu2lsu_d_mon          (lsu2tdu_d_mon_qlfy    ),
 `else // SCR1_DBGC_EN
    .tdu2lsu_d_mon          (lsu2tdu_d_mon         ),
 `endif // SCR1_DBGC_EN
    .tdu2lsu_d_match        (tdu2lsu_d_match       ),
    .tdu2lsu_d_x_req        (tdu2lsu_d_x_req       ),
    // EPU I/F
 `ifdef SCR1_DBGC_EN
    .tdu2hdu_dmode_req      (tdu2hdu_dmode_req      ),
    // WB I/F
    .exu2tdu_bp_retire      (exu2tdu_bp_retire_qlfy)
 `else // SCR1_DBGC_EN
    .tdu2hdu_dmode_req      (                       ),
    // WB I/F
    .exu2tdu_bp_retire      (exu2tdu_bp_retire     )
 `endif // SCR1_DBGC_EN
);

 `ifdef SCR1_DBGC_EN
assign csr2tdu_req_qlfy         = csr2tdu_req       & {$bits(csr2tdu_req){pipe_rst_n_qlfy}};
assign csr2tdu_cmd_qlfy         = pipe_rst_n_qlfy   ? csr2tdu_cmd : SCR1_CSR_CMD_NONE;
assign csr2tdu_addr_qlfy        = csr2tdu_addr      & {$bits(csr2tdu_addr){pipe_rst_n_qlfy}};
assign csr2tdu_wdata_qlfy       = csr2tdu_wdata     & {$bits(csr2tdu_wdata){pipe_rst_n_qlfy}};
//
assign exu2tdu_i_mon_qlfy       = pipe_rst_n_qlfy ? exu2tdu_i_mon : '0;
assign lsu2tdu_d_mon_qlfy       = pipe_rst_n_qlfy ? lsu2tdu_d_mon : '0;
assign exu2tdu_bp_retire_qlfy   = exu2tdu_bp_retire & {$bits(exu2tdu_bp_retire){pipe_rst_n_qlfy}};
 `endif // SCR1_DBGC_EN

`endif // SCR1_BRKM_EN

//-------------------------------------------------------------------------------
// HART Debug Unit (HDU)
//-------------------------------------------------------------------------------
`ifdef SCR1_DBGC_EN
scr1_pipe_hdu i_pipe_hdu (
    // Common signals
    .rst_n                  (dbg_rst_n              ),
    .clk_en                 (dm_active              ),
`ifdef SCR1_CLKCTRL_EN
    .clk_pipe_en            (clk_pipe_en            ),
    .clk                    (clk_dbgc               ),
`else
    .clk                    (clk                    ),
`endif // SCR1_CLKCTRL_EN
    // Control/status registers i/f
    .csr_req                (csr2hdu_req_qlfy       ),
    .csr_cmd                (csr2hdu_cmd_qlfy       ),
    .csr_addr               (csr2hdu_addr_qlfy      ),
    .csr_wdata              (csr2hdu_wdata_qlfy     ),
    .csr_resp               (hdu2csr_resp           ),
    .csr_rdata              (hdu2csr_rdata          ),
    // HART Run Control i/f
    .pipe_rst_n_qlfy        (pipe_rst_n_qlfy        ),
    .dm_cmd_req             (dm_cmd_req             ),
    .dm_cmd                 (dm_cmd                 ),
    .dm_cmd_resp            (dm_cmd_resp            ),
    .dm_cmd_rcode           (dm_cmd_rcode           ),
    .dm_hart_event          (dm_hart_event          ),
    .dm_hart_status         (dm_hart_status         ),
    // Program Buffer - HART instruction execution i/f
    .dm_pbuf_addr           (dm_pbuf_addr           ),
    .dm_pbuf_instr          (dm_pbuf_instr          ),
    // HART Abstract Data regs i/f
    .dm_dreg_req            (dm_dreg_req            ),
    .dm_dreg_wr             (dm_dreg_wr             ),
    .dm_dreg_wdata          (dm_dreg_wdata          ),
    .dm_dreg_resp           (dm_dreg_resp           ),
    .dm_dreg_fail           (dm_dreg_fail           ),
    .dm_dreg_rdata          (dm_dreg_rdata          ),
    //
`ifdef SCR1_BRKM_EN
    // HDU <-> TDU
    .hart_hwbrk_dsbl        (hwbrk_dsbl             ),
    .hart_tm_dmode_req      (tdu2hdu_dmode_req      ),
    .hart_brkpt_hw          (brkpt_hw               ),
`endif // SCR1_BRKM_EN

    // HART Run Status
    .hart_exu_busy          (exu_busy_qlfy          ),
    .hart_instret           (instret_qlfy           ),
    .hart_init_pc           (exu_init_pc_qlfy       ),
    // HART Halt Status
    .hart_exu_exc_req       (exu_exc_req_qlfy       ),
    .hart_brkpt             (brkpt_qlfy             ),
    // HART Run Control
    .hart_fetch_pbuf        (fetch_pbuf             ),
    .hart_exu_no_commit     (exu_no_commit          ),
    .hart_exu_irq_dsbl      (exu_irq_dsbl           ),
    .hart_exu_pc_advmt_dsbl (exu_pc_advmt_dsbl      ),
    .hart_exu_dmode_sstep_en(exu_dmode_sstep_en     ),

    // HART state
    .hart_dbg_halted        (dbg_halted             ),
    .hart_dbg_run2halt      (dbg_run2halt           ),
    .hart_dbg_halt2run      (dbg_halt2run           ),
    .hart_dbg_run_start     (dbg_run_start          ),
    .hart_pc                (curr_pc_qlfy           ),
    .hart_new_pc            (dbg_new_pc             ),
    //
    .hart_pbuf_instr_rdy    (ifu2hdu_pbuf_rdy_qlfy  ),
    .hart_pbuf_instr_vd     (hdu2ifu_pbuf_vd        ),
    .hart_pbuf_instr_err    (hdu2ifu_pbuf_err       ),
    .hart_pbuf_instr        (hdu2ifu_pbuf_instr     )
);

assign csr2hdu_req_qlfy         = csr2hdu_req       & {$bits(csr2hdu_req){pipe_rst_n_qlfy}};
assign csr2hdu_cmd_qlfy         = pipe_rst_n_qlfy   ? csr2hdu_cmd : SCR1_CSR_CMD_NONE;
assign csr2hdu_addr_qlfy        = csr2hdu_addr      & {$bits(csr2hdu_addr){pipe_rst_n_qlfy}};
assign csr2hdu_wdata_qlfy       = csr2hdu_wdata     & {$bits(csr2hdu_wdata){pipe_rst_n_qlfy}};
//
assign exu_busy_qlfy            = exu_busy          & {$bits(exu_busy){pipe_rst_n_qlfy}};
assign instret_qlfy             = instret           & {$bits(instret){pipe_rst_n_qlfy}};
assign exu_init_pc_qlfy         = exu_init_pc       & {$bits(exu_init_pc){pipe_rst_n_qlfy}};
assign exu_exc_req_qlfy         = exu_exc_req       & {$bits(exu_exc_req){pipe_rst_n_qlfy}};
assign brkpt_qlfy               = brkpt             & {$bits(brkpt){pipe_rst_n_qlfy}};
assign ifu2hdu_pbuf_rdy_qlfy    = ifu2hdu_pbuf_rdy  & {$bits(ifu2hdu_pbuf_rdy){pipe_rst_n_qlfy}};
assign curr_pc_qlfy             = curr_pc           & {$bits(curr_pc){pipe_rst_n_qlfy}};

`endif // SCR1_DBGC_EN

`ifdef SCR1_SIM_ENV
//-------------------------------------------------------------------------------
// Tracelog
//-------------------------------------------------------------------------------

scr1_tracelog i_tracelog (
    .rst_n          (pipe_rst_n                         ),
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