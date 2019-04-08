/// Copyright by Syntacore LLC © 2016-2019. See LICENSE for details
/// @file       <scr1_core_top.sv>
/// @brief      SCR1 core top
///

`include "scr1_arch_description.svh"
`include "scr1_arch_types.svh"
`include "scr1_memif.svh"

`ifdef SCR1_DBGC_EN
`include "scr1_tapc.svh"
`include "scr1_dm.svh"
`include "scr1_hdu.svh"
`endif // SCR1_DBGC_EN

`ifdef SCR1_IPIC_EN
`include "scr1_ipic.svh"
`endif // SCR1_IPIC_EN

module scr1_core_top #(
    parameter bit SCR1_RESET_INPUTS_SYNC = 1 // Reset inputs are: 1 - synchronous, 0 -asynchronous
) (
    // Common
    input   logic                                   pwrup_rst_n,
    input   logic                                   rst_n,
    input   logic                                   cpu_rst_n,
    input   logic                                   test_mode,
    input   logic                                   test_rst_n,
    input   logic                                   clk,
    output  logic                                   core_rst_n_out,
`ifdef SCR1_DBGC_EN
    output  logic                                   ndm_rst_n_out,
`endif // SCR1_DBGC_EN
    
    // Fuses
    input   logic [`SCR1_XLEN-1:0]                  fuse_mhartid,
`ifdef SCR1_DBGC_EN
    input   logic [31:0]                            fuse_idcode,
`endif // SCR1_DBGC_EN

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
`else // SCR1_DBGC_EN
logic                                           core_rst_n_sync;
`endif // SCR1_DBGC_EN
logic                                           core_rst_n;
logic                                           core_rst_n_qlfy;
logic                                           pwrup_rst_n_sync;
logic                                           rst_n_sync;
logic                                           cpu_rst_n_sync;

`ifdef SCR1_DBGC_EN
// TAPC-DM Interface
logic                                           tapc_dmi_ch_sel;
logic [SCR1_DBG_DMI_CH_ID_WIDTH-1:0]            tapc_dmi_ch_id;
logic                                           tapc_dmi_ch_capture;
logic                                           tapc_dmi_ch_shift;
logic                                           tapc_dmi_ch_update;
logic                                           tapc_dmi_ch_tdi;
logic                                           tapc_dmi_ch_tdo;
//
logic                                           tapc_dmi_ch_sel_tapout;
logic [SCR1_DBG_DMI_CH_ID_WIDTH-1:0]            tapc_dmi_ch_id_tapout;
logic                                           tapc_dmi_ch_capture_tapout;
logic                                           tapc_dmi_ch_shift_tapout;
logic                                           tapc_dmi_ch_update_tapout;
logic                                           tapc_dmi_ch_tdi_tapout;
logic                                           tapc_dmi_ch_tdo_tapin;
//
logic                                           dmi_req;
logic                                           dmi_wr;
logic [SCR1_DBG_DMI_ADDR_WIDTH-1:0]             dmi_addr;
logic [SCR1_DBG_DMI_DATA_WIDTH-1:0]             dmi_wdata;
logic                                           dmi_resp;
logic [SCR1_DBG_DMI_DATA_WIDTH-1:0]             dmi_rdata;
// TAPC-SCU Interface
logic                                           tapc_scu_ch_sel;
logic                                           tapc_scu_ch_sel_tapout;
logic                                           tapc_scu_ch_tdo;
logic                                           tapc_ch_tdo;
// SCU nets
logic                                           tapc_rst_n;
logic                                           hdu_rst_n;
logic                                           hdu_rst_n_qlfy;
logic                                           ndm_rst_n;
logic                                           dm_rst_n;
logic                                           hart_rst_n;
`endif // SCR1_DBGC_EN

`ifdef SCR1_DBGC_EN
// DM-Pipeline Interface
// HART Run Control i/f
logic                                           dm_active;
logic                                           dm_cmd_req;
type_scr1_hdu_dbgstates_e                       dm_cmd;
logic                                           dm_cmd_resp;
logic                                           dm_cmd_resp_qlfy;
logic                                           dm_cmd_rcode;
logic                                           dm_cmd_rcode_qlfy;
logic                                           dm_hart_event;
logic                                           dm_hart_event_qlfy;
type_scr1_hdu_hartstatus_s                      dm_hart_status;
type_scr1_hdu_hartstatus_s                      dm_hart_status_qlfy;
// Program Buffer - HART instruction execution i/f
logic [SCR1_HDU_PBUF_ADDR_WIDTH-1:0]            dm_pbuf_addr;
logic [SCR1_HDU_PBUF_ADDR_WIDTH-1:0]            dm_pbuf_addr_qlfy;
logic [SCR1_HDU_CORE_INSTR_WIDTH-1:0]           dm_pbuf_instr;
// HART Abstract Data regs i/f
logic                                           dm_dreg_req;
logic                                           dm_dreg_req_qlfy;
logic                                           dm_dreg_wr;
logic                                           dm_dreg_wr_qlfy;
logic [SCR1_HDU_DATA_REG_WIDTH-1:0]             dm_dreg_wdata;
logic [SCR1_HDU_DATA_REG_WIDTH-1:0]             dm_dreg_wdata_qlfy;
logic                                           dm_dreg_resp;
logic                                           dm_dreg_fail;
logic [SCR1_HDU_DATA_REG_WIDTH-1:0]             dm_dreg_rdata;

logic [`SCR1_XLEN-1 : 0]                        dm_pc_sample;
logic [`SCR1_XLEN-1 : 0]                        dm_pc_sample_qlfy;
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

//-------------------------------------------------------------------------------
// Reset Logic
//-------------------------------------------------------------------------------
`ifdef SCR1_DBGC_EN
scr1_scu #(
    .SCR1_SCU_CFG_RESET_INPUTS_SYNC     (SCR1_RESET_INPUTS_SYNC)
) i_scu(
    // Global signals
    .pwrup_rst_n                (pwrup_rst_n),
    .rst_n                      (rst_n),
    .cpu_rst_n                  (cpu_rst_n),
    .test_mode                  (test_mode),
    .test_rst_n                 (test_rst_n),
    .clk                        (clk),
    // TAPC scan-chains
    .tapc_ch_sel                (tapc_scu_ch_sel),
    .tapc_ch_id                 ('0),
    .tapc_ch_capture            (tapc_dmi_ch_capture),
    .tapc_ch_shift              (tapc_dmi_ch_shift),
    .tapc_ch_update             (tapc_dmi_ch_update),
    .tapc_ch_tdi                (tapc_dmi_ch_tdi),
    .tapc_ch_tdo                (tapc_scu_ch_tdo),
    // Input sync resets:
    .ndm_rst_n                  (ndm_rst_n),
    .hart_rst_n                 (hart_rst_n),
    // Generated resets and their attributes (qualifiers etc):
    .core_rst_n                 (core_rst_n),
    .core_rst_n_qlfy            (core_rst_n_qlfy),
    .dm_rst_n                   (dm_rst_n),
    .hdu_rst_n                  (hdu_rst_n),
    .hdu_rst_n_qlfy             (hdu_rst_n_qlfy)
);

// TAPC reset
scr1_reset_and2_cell i_tapc_rstn_and2_cell (
    .rst_n_in       ({trst_n, pwrup_rst_n}),
    .test_rst_n     (test_rst_n),
    .test_mode      (test_mode),
    .rst_n_out      (tapc_rst_n)
);
assign ndm_rst_n_out  = ndm_rst_n;

generate

if (SCR1_RESET_INPUTS_SYNC)
// reset inputs are synchronous

begin : gen_rst_inputs_sync
    assign pwrup_rst_n_sync = pwrup_rst_n;
end : gen_rst_inputs_sync

else // SCR1_RESET_INPUTS_SYNC == 0, - reset inputs are asynchronous

begin : gen_rst_inputs_async
// Power-Up Reset synchronizer
scr1_reset_sync_cell i_pwrup_rstn_reset_sync (
    .rst_n          (pwrup_rst_n),
    .clk            (clk),
    .test_rst_n     (test_rst_n),
    .test_mode      (test_mode),
    .rst_n_out      (pwrup_rst_n_sync)
);
end : gen_rst_inputs_async

// end of  SCR1_RESET_INPUTS_SYNC

endgenerate

`else // SCR1_DBGC_EN

generate

if (SCR1_RESET_INPUTS_SYNC)
// reset inputs are synchronous

begin : gen_rst_inputs_sync
    assign pwrup_rst_n_sync = pwrup_rst_n;
    assign rst_n_sync       = rst_n;
    assign cpu_rst_n_sync   = cpu_rst_n;
end : gen_rst_inputs_sync

else // SCR1_RESET_INPUTS_SYNC == 0, - reset inputs are asynchronous

begin : gen_rst_inputs_async
// Power-Up Reset synchronizer
scr1_reset_sync_cell i_pwrup_rstn_reset_sync (
    .rst_n          (pwrup_rst_n),
    .clk            (clk),
    .test_rst_n     (test_rst_n),
    .test_mode      (test_mode),
    .rst_n_out      (pwrup_rst_n_sync)
);

// Regular Reset synchronizer
scr1_reset_sync_cell i_rstn_reset_sync (
    .rst_n          (rst_n),
    .clk            (clk),
    .test_rst_n     (test_rst_n),
    .test_mode      (test_mode),
    .rst_n_out      (rst_n_sync)
);

// CPU Reset synchronizer
scr1_reset_sync_cell i_cpu_rstn_reset_sync (
    .rst_n          (cpu_rst_n),
    .clk            (clk),
    .test_rst_n     (test_rst_n),
    .test_mode      (test_mode),
    .rst_n_out      (cpu_rst_n_sync)
);
end : gen_rst_inputs_async

// end of  SCR1_RESET_INPUTS_SYNC

endgenerate

// Core Reset: core_rst_n
scr1_reset_buf_qlfy_cell i_core_rstn_buf_qlfy_cell (
    .rst_n              (pwrup_rst_n_sync),
    .clk                (clk),
    .test_rst_n         (test_rst_n),
    .test_mode          (test_mode),
    .reset_n_in         (core_rst_n_sync),
    .reset_n_out_qlfy   (core_rst_n_qlfy),
    .reset_n_out        (core_rst_n),
    .reset_n_status     ()
);
assign core_rst_n_sync      = rst_n_sync & cpu_rst_n_sync;
`endif // SCR1_DBGC_EN
assign core_rst_n_out       = core_rst_n;

//-------------------------------------------------------------------------------
// SCR1 pipeline
//-------------------------------------------------------------------------------
scr1_pipe_top i_pipe_top (
    // Control
    .pipe_rst_n             (core_rst_n         ),
`ifdef SCR1_DBGC_EN
    .pipe_rst_n_qlfy        (core_rst_n_qlfy    ),
    .dbg_rst_n              (hdu_rst_n          ),
`endif // SCR1_DBGC_EN
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
    // Debug interface:
    // DM <-> Pipeline: HART Run Control i/f
    .dm_active              (dm_active          ),
    .dm_cmd_req             (dm_cmd_req         ),
    .dm_cmd                 (dm_cmd             ),
    .dm_cmd_resp            (dm_cmd_resp        ),
    .dm_cmd_rcode           (dm_cmd_rcode       ),
    .dm_hart_event          (dm_hart_event      ),
    .dm_hart_status         (dm_hart_status     ),
    // DM <-> Pipeline: Program Buffer - HART instruction execution i/f
    .dm_pbuf_addr           (dm_pbuf_addr       ),
    .dm_pbuf_instr          (dm_pbuf_instr      ),
    // DM <-> Pipeline: HART Abstract Data regs i/f
    .dm_dreg_req            (dm_dreg_req        ),
    .dm_dreg_wr             (dm_dreg_wr         ),
    .dm_dreg_wdata          (dm_dreg_wdata      ),
    .dm_dreg_resp           (dm_dreg_resp       ),
    .dm_dreg_fail           (dm_dreg_fail       ),
    .dm_dreg_rdata          (dm_dreg_rdata      ),
    //
    .dm_pc_sample           (dm_pc_sample       ),
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

    // Fuse
    .fuse_mhartid           (fuse_mhartid       )
);


`ifdef SCR1_DBGC_EN
//-------------------------------------------------------------------------------
// TAP Controller (TAPC)
//-------------------------------------------------------------------------------
scr1_tapc i_tapc (
    // JTAG signals
    .trst_n                 (tapc_rst_n),
    .tck                    (tck),
    .tms                    (tms),
    .tdi                    (tdi),
    .tdo                    (tdo),
    .tdo_en                 (tdo_en),
    // Fuses:
    .fuse_idcode            (fuse_idcode),
    // System Control/Status signals
    .scu_ch_sel             (tapc_scu_ch_sel_tapout),
    // DMI scan-chains
    .dmi_ch_sel             (tapc_dmi_ch_sel_tapout),
    .dmi_ch_id              (tapc_dmi_ch_id_tapout),
    .dmi_ch_capture         (tapc_dmi_ch_capture_tapout),
    .dmi_ch_shift           (tapc_dmi_ch_shift_tapout),
    .dmi_ch_update          (tapc_dmi_ch_update_tapout),
    .dmi_ch_tdi             (tapc_dmi_ch_tdi_tapout),
    .dmi_ch_tdo             (tapc_dmi_ch_tdo_tapin)
);

scr1_tapc_synchronizer i_tapc_synchronizer (
    // System common signals
    .pwrup_rst_n            (pwrup_rst_n_sync),
    .dm_rst_n               (dm_rst_n),
    .clk                    (clk),

    // JTAG common signals
    .trst_n                 (tapc_rst_n),
    .tck                    (tck),

    // System Control/Status signals
    .scu_ch_sel             (tapc_scu_ch_sel_tapout),
    .scu_ch_sel_core        (tapc_scu_ch_sel),

    // DMI scan-chains
    .dmi_ch_sel             (tapc_dmi_ch_sel_tapout),
    .dmi_ch_sel_core        (tapc_dmi_ch_sel),
    .dmi_ch_id              (tapc_dmi_ch_id_tapout),
    .dmi_ch_id_core         (tapc_dmi_ch_id),
    .dmi_ch_capture         (tapc_dmi_ch_capture_tapout),
    .dmi_ch_capture_core    (tapc_dmi_ch_capture),
    .dmi_ch_shift           (tapc_dmi_ch_shift_tapout),
    .dmi_ch_shift_core      (tapc_dmi_ch_shift),
    .dmi_ch_update          (tapc_dmi_ch_update_tapout),
    .dmi_ch_update_core     (tapc_dmi_ch_update),
    .dmi_ch_tdi             (tapc_dmi_ch_tdi_tapout),
    .dmi_ch_tdi_core        (tapc_dmi_ch_tdi),
    .dmi_ch_tdo             (tapc_dmi_ch_tdo_tapin),
    .dmi_ch_tdo_core        (tapc_ch_tdo)
);
assign tapc_ch_tdo = (tapc_scu_ch_tdo & tapc_scu_ch_sel) | (tapc_dmi_ch_tdo & tapc_dmi_ch_sel);

scr1_dmi i_dmi (
    .rst_n                  (dm_rst_n),
    .clk                    (clk),

    // TAP scan-chains
    .dtm_ch_sel             (tapc_dmi_ch_sel),
    .dtm_ch_id              (tapc_dmi_ch_id),
    .dtm_ch_capture         (tapc_dmi_ch_capture),
    .dtm_ch_shift           (tapc_dmi_ch_shift),
    .dtm_ch_update          (tapc_dmi_ch_update),
    .dtm_ch_tdi             (tapc_dmi_ch_tdi),
    .dtm_ch_tdo             (tapc_dmi_ch_tdo),

    // DMI
    .dmi_resp               (dmi_resp),
    .dmi_rdata              (dmi_rdata),
    .dmi_req                (dmi_req),
    .dmi_wr                 (dmi_wr),
    .dmi_addr               (dmi_addr),
    .dmi_wdata              (dmi_wdata)
);
`endif // SCR1_DBGC_EN


`ifdef SCR1_DBGC_EN

//-------------------------------------------------------------------------------
// Debug Module (DM)
//-------------------------------------------------------------------------------
assign dm_cmd_resp_qlfy    = dm_cmd_resp   & {$bits(dm_cmd_resp){hdu_rst_n_qlfy}};
assign dm_cmd_rcode_qlfy   = dm_cmd_rcode  & {$bits(dm_cmd_rcode){hdu_rst_n_qlfy}};
assign dm_hart_event_qlfy  = dm_hart_event & {$bits(dm_hart_event){hdu_rst_n_qlfy}};
assign dm_hart_status_qlfy = hdu_rst_n_qlfy ? dm_hart_status : '0;
assign dm_pbuf_addr_qlfy   = dm_pbuf_addr  & {$bits(dm_pbuf_addr){hdu_rst_n_qlfy}};
assign dm_dreg_req_qlfy    = dm_dreg_req   & {$bits(dm_dreg_req){hdu_rst_n_qlfy}};
assign dm_dreg_wr_qlfy     = dm_dreg_wr    & {$bits(dm_dreg_wr){hdu_rst_n_qlfy}};
assign dm_dreg_wdata_qlfy  = dm_dreg_wdata & {$bits(dm_dreg_wdata){hdu_rst_n_qlfy}};
assign dm_pc_sample_qlfy   = dm_pc_sample  & {$bits(dm_pc_sample){core_rst_n_qlfy}};

scr1_dm i_dm (
    // Common signals
    .rst_n                  (dm_rst_n),
    .clk                    (clk),
    // DM internal interface
    .dmi_req                (dmi_req),
    .dmi_wr                 (dmi_wr),
    .dmi_addr               (dmi_addr),
    .dmi_wdata              (dmi_wdata),
    .dmi_resp               (dmi_resp),
    .dmi_rdata              (dmi_rdata),
    // DM <-> Pipeline: HART Run Control i/f
    .ndm_rst_n              (ndm_rst_n),
    .hart_rst_n             (hart_rst_n),
    .hart_dmactive          (dm_active),
    .hart_cmd_req           (dm_cmd_req),
    .hart_cmd               (dm_cmd),
    .hart_cmd_resp          (dm_cmd_resp_qlfy),
    .hart_cmd_rcode         (dm_cmd_rcode_qlfy),
    .hart_event             (dm_hart_event_qlfy),
    .hart_status            (dm_hart_status_qlfy),
    .ro_fuse_mhartid        (fuse_mhartid),
    .ro_pc                  (dm_pc_sample_qlfy),

    // DM <-> Pipeline: HART Abstract Command / Program Buffer i/f
    .hart_pbuf_addr         (dm_pbuf_addr_qlfy),
    .hart_pbuf_instr        (dm_pbuf_instr),

    // DM <-> Pipeline: HART Abstract Data regs i/f
    .hart_dreg_req          (dm_dreg_req_qlfy),
    .hart_dreg_wr           (dm_dreg_wr_qlfy),
    .hart_dreg_wdata        (dm_dreg_wdata_qlfy),
    .hart_dreg_resp         (dm_dreg_resp),
    .hart_dreg_fail         (dm_dreg_fail),
    .hart_dreg_rdata        (dm_dreg_rdata)
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