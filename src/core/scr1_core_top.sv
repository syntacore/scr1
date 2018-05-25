/// Copyright by Syntacore LLC © 2016-2018. See LICENSE for details
/// @file       <scr1_core_top.sv>
/// @brief      SCR1 core top
///

`include "scr1_arch_description.svh"
`include "scr1_arch_types.svh"
`include "scr1_memif.svh"

`ifdef SCR1_DBGC_EN
`include "scr1_tapc.svh"
`include "scr1_dbgc.svh"
`endif // SCR1_DBGC_EN

`ifdef SCR1_IPIC_EN
`include "scr1_ipic.svh"
`endif // SCR1_IPIC_EN

module scr1_core_top (
    // Common
    input   logic                                   rst_n,
    input   logic                                   test_mode,
    input   logic                                   clk,
    output  logic                                   rst_n_out,

    // Fuses
    input   logic [`SCR1_XLEN-1:0]                  fuse_mhartid,

    // IRQ
`ifdef SCR1_IPIC_EN
    input   logic [SCR1_IRQ_LINES_NUM-1:0]          irq_lines,
`else
    input   logic                                   ext_irq,
`endif // SCR1_IPIC_EN
    input   logic                                   soft_irq,

    // Memory-mapped external timer
    input   logic                                   timer_irq,
    input   logic [63:0]                            mtime_ext,

`ifdef SCR1_DBGC_EN
    // Debug Interface
    input   logic                                   trst_n,
    input   logic                                   tck,
    input   logic                                   tms,
    input   logic                                   tdi,
    output  logic                                   tdo,
    output  logic                                   tdo_en,
`endif // SCR1_DBGC_EN

    // Instruction Memory Interface
    input   logic                                   imem_req_ack,
    output  logic                                   imem_req,
    output  type_scr1_mem_cmd_e                     imem_cmd,
    output  logic [`SCR1_IMEM_AWIDTH-1:0]           imem_addr,
    input   logic [`SCR1_IMEM_DWIDTH-1:0]           imem_rdata,
    input   type_scr1_mem_resp_e                    imem_resp,

    // Data Memory Interface
    input   logic                                   dmem_req_ack,
    output  logic                                   dmem_req,
    output  type_scr1_mem_cmd_e                     dmem_cmd,
    output  type_scr1_mem_width_e                   dmem_width,
    output  logic [`SCR1_DMEM_AWIDTH-1:0]           dmem_addr,
    output  logic [`SCR1_DMEM_DWIDTH-1:0]           dmem_wdata,
    input   logic [`SCR1_DMEM_DWIDTH-1:0]           dmem_rdata,
    input   type_scr1_mem_resp_e                    dmem_resp
);

//-------------------------------------------------------------------------------
// Local signals declaration
//-------------------------------------------------------------------------------

// Reset Logic
`ifdef SCR1_DBGC_EN
logic                                           sys_rst_n;
logic                                           sys_rst_n_status;
`endif // SCR1_DBGC_EN
logic                                           core_rst_n;
logic                                           core_rst_n_status;

`ifdef SCR1_DBGC_EN
// TAPC-System Control Interface
logic                                           tapc_sys_rst_ctrl;
logic                                           tapc_sys_rst_sts;
logic                                           tapc_sys_rst_ctrl_tapout;
logic                                           tapc_sys_rst_sts_tapin;
`endif // SCR1_DBGC_EN

`ifdef SCR1_DBGC_EN
// TAPC-DBGC Interface
logic                                           tapc_dap_ch_sel;
logic [SCR1_DBGC_DAP_CH_ID_WIDTH-1:0]           tapc_dap_ch_id;
logic                                           tapc_dap_ch_capture;
logic                                           tapc_dap_ch_shift;
logic                                           tapc_dap_ch_update;
logic                                           tapc_dap_ch_tdi;
logic                                           tapc_dap_ch_tdo;
logic                                           tapc_dap_ch_sel_tapout;
logic [SCR1_DBGC_DAP_CH_ID_WIDTH-1:0]           tapc_dap_ch_id_tapout;
logic                                           tapc_dap_ch_capture_tapout;
logic                                           tapc_dap_ch_shift_tapout;
logic                                           tapc_dap_ch_update_tapout;
logic                                           tapc_dap_ch_tdi_tapout;
logic                                           tapc_dap_ch_tdo_tapin;
`endif // SCR1_DBGC_EN

`ifdef SCR1_DBGC_EN
// DBGC-Pipeline Interface
logic                                           dbgc_core_rst_ctrl;
logic                                           dbgc_core_rst_sts;
type_scr1_dbgc_core_busy_s                      dbgc_core_state_busy;
logic                                           dbgc_hart_rst_ctrl_nc;
logic                                           dbgc_hart_cmd_req;
type_scr1_dbgc_hart_dbg_mode_e                  dbgc_hart_cmd;
logic                                           dbgc_hart_cmd_ack;
logic                                           dbgc_hart_cmd_nack;
type_scr1_dbgc_hart_runctrl_s                   dbgc_hart_runctrl;
type_scr1_dbgc_hart_state_s                     dbgc_hart_state;
logic [SCR1_DBGC_DBG_CORE_INSTR_WIDTH-1:0]      dbgc_hart_instr;
logic [SCR1_DBGC_DBG_DATA_REG_WIDTH-1:0]        dbgc_hart_dreg_out;
logic [SCR1_DBGC_DBG_DATA_REG_WIDTH-1:0]        dbgc_hart_dreg_in;
logic                                           dbgc_hart_dreg_wr;
logic [SCR1_DBGC_DBG_DATA_REG_WIDTH-1:0]        dbgc_hart_pcsample;
`endif // SCR1_DBGC_EN

`ifdef SCR1_CLKCTRL_EN
// Global clock gating logic
logic                                           sleep_pipe;
logic                                           wake_pipe;
logic                                           clk_pipe;
logic                                           clk_pipe_en;
logic                                           clk_dbgc;
logic                                           clk_alw_on;
`endif // SCR1_CLKCTRL_EN

// Block busy signals
logic                                           ifu_busy;
logic                                           idu_busy;
logic                                           exu_busy;
logic                                           lsu_busy;
logic                                           ialu_busy;

//-------------------------------------------------------------------------------
// Reset Logic
//-------------------------------------------------------------------------------
`ifdef SCR1_DBGC_EN
scr1_sync_rstn i_sync_rstn_sts_rstn (
    .rst_n          (rst_n),
    .clk            (clk),
    .test_mode      (test_mode),
    .rst_n_din      (~tapc_sys_rst_ctrl),
    .rst_n_dout     (sys_rst_n),
    .rst_n_status   (sys_rst_n_status)
);

scr1_sync_rstn i_sync_rstn_core_rstn (
    .rst_n          (sys_rst_n),
    .clk            (clk),
    .test_mode      (test_mode),
    .rst_n_din      (~dbgc_core_rst_ctrl),
    .rst_n_dout     (core_rst_n),
    .rst_n_status   (core_rst_n_status)
);

assign tapc_sys_rst_sts     = ~sys_rst_n_status;
assign dbgc_core_rst_sts    = ~core_rst_n_status;
`else // SCR1_DBGC_EN
assign core_rst_n = rst_n;
`endif // SCR1_DBGC_EN
assign rst_n_out = core_rst_n;

//-------------------------------------------------------------------------------
// SCR1 pipeline
//-------------------------------------------------------------------------------
scr1_pipe_top i_pipe_top (
    // Control
    .rst_n                  (core_rst_n         ),
`ifndef SCR1_CLKCTRL_EN
    .clk                    (clk                ),
`else // SCR1_CLKCTRL_EN
    .clk                    (clk_pipe           ),
    .sleep_pipe             (sleep_pipe         ),
    .wake_pipe              (wake_pipe          ),
    .clk_alw_on             (clk_alw_on         ),
    .clk_dbgc               (clk_dbgc           ),
    .clk_pipe_en            (clk_pipe_en        ),
`endif // SCR1_CLKCTRL_EN
    // Instruction memory interface
    .imem_req               (imem_req           ),
    .imem_cmd               (imem_cmd           ),
    .imem_addr              (imem_addr          ),
    .imem_req_ack           (imem_req_ack       ),
    .imem_rdata             (imem_rdata         ),
    .imem_resp              (imem_resp          ),
    // Data memory interface
    .dmem_req               (dmem_req           ),
    .dmem_cmd               (dmem_cmd           ),
    .dmem_width             (dmem_width         ),
    .dmem_addr              (dmem_addr          ),
    .dmem_wdata             (dmem_wdata         ),
    .dmem_req_ack           (dmem_req_ack       ),
    .dmem_rdata             (dmem_rdata         ),
    .dmem_resp              (dmem_resp          ),
`ifdef SCR1_DBGC_EN
    // Debug interface
    .dbgc_hart_cmd          (dbgc_hart_cmd      ),
    .dbgc_hart_cmd_req      (dbgc_hart_cmd_req  ),
    .dbgc_hart_cmd_ack      (dbgc_hart_cmd_ack  ),
    .dbgc_hart_cmd_nack     (dbgc_hart_cmd_nack ),
    .dbgc_hart_runctrl      (dbgc_hart_runctrl  ),
    .dbgc_hart_state        (dbgc_hart_state    ),
    .dbgc_hart_instr        (dbgc_hart_instr    ),
    .dbgc_hart_dreg_out     (dbgc_hart_dreg_out ),
    .dbgc_hart_dreg_in      (dbgc_hart_dreg_in  ),
    .dbgc_hart_dreg_wr      (dbgc_hart_dreg_wr  ),
    .dbgc_hart_pcsample     (dbgc_hart_pcsample ),
`endif // SCR1_DBGC_EN
    // IRQ
`ifdef SCR1_IPIC_EN
    .irq_lines              (irq_lines          ),
`else // SCR1_IPIC_EN
    .ext_irq                (ext_irq            ),
`endif // SCR1_IPIC_EN
    .soft_irq               (soft_irq           ),
    .timer_irq              (timer_irq          ),
    .mtime_ext              (mtime_ext          ),
    // Block busy interface
    .ifu_busy               (ifu_busy           ),
    .idu_busy               (idu_busy           ),
    .exu_busy               (exu_busy           ),
    .lsu_busy               (lsu_busy           ),
    .ialu_busy              (ialu_busy          ),
    // Fuse
    .fuse_mhartid           (fuse_mhartid       )
);


`ifdef SCR1_DBGC_EN
//-------------------------------------------------------------------------------
// TAP Controller (TAPC)
//-------------------------------------------------------------------------------
scr1_tapc i_tapc (
    // JTAG signals
    .trst_n             (trst_n),
    .tck                (tck),
    .tms                (tms),
    .tdi                (tdi),
    .tdo                (tdo),
    .tdo_en             (tdo_en),
    // System Control/Status signals
    .sys_rst_ctrl       (tapc_sys_rst_ctrl_tapout),
    .sys_rst_sts        (tapc_sys_rst_sts_tapin),
    // Master TAP Select signal
    .master_tap_sel     (),
    // DAP scan-chains
    .dap_ch_sel         (tapc_dap_ch_sel_tapout),
    .dap_ch_id          (tapc_dap_ch_id_tapout),
    .dap_ch_capture     (tapc_dap_ch_capture_tapout),
    .dap_ch_shift       (tapc_dap_ch_shift_tapout),
    .dap_ch_update      (tapc_dap_ch_update_tapout),
    .dap_ch_tdi         (tapc_dap_ch_tdi_tapout),
    .dap_ch_tdo         (tapc_dap_ch_tdo_tapin)
);

scr1_tapc_synchronizer i_tapc_synchronizer (
    // JTAG signals
    .tck                (tck),
    .clk                (clk),
    .sys_rst_n          (sys_rst_n),
    .async_rst_n        (rst_n),
    .trst_n             (trst_n),

    // System Control/Status signals
    .sys_rst_ctrl       (tapc_sys_rst_ctrl_tapout),
    .sys_rst_ctrl_core  (tapc_sys_rst_ctrl),

    .sys_rst_sts        (tapc_sys_rst_sts_tapin),
    .sys_rst_sts_core   (tapc_sys_rst_sts),

    // DAP scan-chains
    .dap_ch_sel         (tapc_dap_ch_sel_tapout),
    .dap_ch_sel_core    (tapc_dap_ch_sel),

    .dap_ch_id          (tapc_dap_ch_id_tapout),
    .dap_ch_id_core     (tapc_dap_ch_id),

    .dap_ch_capture     (tapc_dap_ch_capture_tapout),
    .dap_ch_capture_core(tapc_dap_ch_capture),

    .dap_ch_shift       (tapc_dap_ch_shift_tapout),
    .dap_ch_shift_core  (tapc_dap_ch_shift),

    .dap_ch_update      (tapc_dap_ch_update_tapout),
    .dap_ch_update_core (tapc_dap_ch_update),

    .dap_ch_tdi         (tapc_dap_ch_tdi_tapout),
    .dap_ch_tdi_core    (tapc_dap_ch_tdi),

    .dap_ch_tdo         (tapc_dap_ch_tdo_tapin),
    .dap_ch_tdo_core    (tapc_dap_ch_tdo)
);
`endif // SCR1_DBGC_EN


`ifdef SCR1_DBGC_EN

//-------------------------------------------------------------------------------
// Debug Controller (DBGC)
//-------------------------------------------------------------------------------
assign dbgc_core_state_busy.ifetch  = ifu_busy;
assign dbgc_core_state_busy.id      = idu_busy;
assign dbgc_core_state_busy.ialu    = ialu_busy;
assign dbgc_core_state_busy.cfu     = exu_busy;
assign dbgc_core_state_busy.lsu     = lsu_busy;
assign dbgc_core_state_busy.wb_cnt  = '0;
`ifdef SCR1_RVM_EXT
assign dbgc_core_state_busy.mdu     = 1'b0;
`endif // SCR1_RVM_EXT

scr1_dbgc i_dbgc (
    // Common
    .rst_n              (sys_rst_n),
`ifndef SCR1_CLKCTRL_EN
    .clk                (clk),
`else // SCR1_CLKCTRL_EN
    .clk                (clk_dbgc),
    .sleep_rdy          (),
    .sleep_wakeup       (),
`endif // SCR1_CLKCTRL_EN
    // Fuse
    .fuse_mhartid       (fuse_mhartid),
    // DAP scan-chains
    .dap_ch_sel         (tapc_dap_ch_sel),
    .dap_ch_id          (tapc_dap_ch_id),
    .dap_ch_capture     (tapc_dap_ch_capture),
    .dap_ch_shift       (tapc_dap_ch_shift),
    .dap_ch_update      (tapc_dap_ch_update),
    .dap_ch_tdi         (tapc_dap_ch_tdi),
    .dap_ch_tdo         (tapc_dap_ch_tdo),
    // Core debug interface
    .core_rst_ctrl      (dbgc_core_rst_ctrl),
    .core_rst_sts       (dbgc_core_rst_sts),
    .core_state_busy    (dbgc_core_state_busy),
    .hart_rst_ctrl      (dbgc_hart_rst_ctrl_nc),
    .hart_rst_sts       (dbgc_core_rst_sts),
    .hart_dbg_cmd       (dbgc_hart_cmd),
    .hart_dbg_cmd_req   (dbgc_hart_cmd_req),
    .hart_dbg_cmd_ack   (dbgc_hart_cmd_ack),
    .hart_dbg_cmd_nack  (dbgc_hart_cmd_nack),
    .hart_dbg_runctrl   (dbgc_hart_runctrl),
    .hart_dbg_state     (dbgc_hart_state),
    .hart_dbg_instr     (dbgc_hart_instr),
    .hart_dbg_dreg_out  (dbgc_hart_dreg_out),
    .hart_dbg_dreg_in   (dbgc_hart_dreg_in),
    .hart_dbg_dreg_wr   (dbgc_hart_dreg_wr),
    .hart_dbg_pcsample  (dbgc_hart_pcsample)
);
`endif // SCR1_DBGC_EN


`ifdef SCR1_CLKCTRL_EN
//-------------------------------------------------------------------------------
// Global clock gating logic
//-------------------------------------------------------------------------------
scr1_clk_ctrl i_clk_ctrl (
    .clk                (clk            ),
    .rst_n              (rst_n          ),
    .test_mode          (test_mode      ),
    // Sleep/wake interface
    .sleep_pipe         (sleep_pipe     ),
    .wake_pipe          (wake_pipe      ),
    // Clocks
    .clkout             (clk_alw_on     ),
    .clkout_pipe        (clk_pipe       ),
    .clk_pipe_en        (clk_pipe_en    ),
    .clkout_dbgc        (clk_dbgc       )
);
`endif // SCR1_CLKCTRL_EN

endmodule : scr1_core_top