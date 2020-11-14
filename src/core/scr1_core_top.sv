/// Copyright by Syntacore LLC © 2016-2020. See LICENSE for details
/// @file       <scr1_core_top.sv>
/// @brief      SCR1 core top
///

`include "scr1_arch_description.svh"
`include "scr1_arch_types.svh"
`include "scr1_memif.svh"

`ifdef SCR1_DBG_EN
`include "scr1_tapc.svh"
`include "scr1_dm.svh"
`include "scr1_hdu.svh"
`endif // SCR1_DBG_EN

`ifdef SCR1_IPIC_EN
`include "scr1_ipic.svh"
`endif // SCR1_IPIC_EN

module scr1_core_top (
    // Common
    input   logic                                   pwrup_rst_n,                // Power-Up reset
    input   logic                                   rst_n,                      // Regular reset
    input   logic                                   cpu_rst_n,                  // CPU reset
    input   logic                                   test_mode,                  // DFT Test Mode
    input   logic                                   test_rst_n,                 // DFT Test Reset
    input   logic                                   clk,                        // Core clock
    output  logic                                   core_rst_n_o,               // Core reset
    output  logic                                   core_rdc_qlfy_o,            // Core RDC qualifier
`ifdef SCR1_DBG_EN
    output  logic                                   sys_rst_n_o,                // System reset
    output  logic                                   sys_rdc_qlfy_o,             // System RDC qualifier
`endif // SCR1_DBG_EN

    // Fuses
    input   logic [`SCR1_XLEN-1:0]                  core_fuse_mhartid_i,        // Fuse MHARTID value
`ifdef SCR1_DBG_EN
    input   logic [31:0]                            tapc_fuse_idcode_i,         // Fuse IDCODE value
`endif // SCR1_DBG_EN

    // IRQ
`ifdef SCR1_IPIC_EN
    input   logic [SCR1_IRQ_LINES_NUM-1:0]          core_irq_lines_i,           // External interrupt request lines
`else
    input   logic                                   core_irq_ext_i,             // External interrupt request
`endif // SCR1_IPIC_EN
    input   logic                                   core_irq_soft_i,            // Software generated interrupt request
    input   logic                                   core_irq_mtimer_i,          // Machine timer interrupt request

    // Memory-mapped external timer
    input   logic [63:0]                            core_mtimer_val_i,          // Machine timer value

`ifdef SCR1_DBG_EN
    // Debug Interface
    input   logic                                   tapc_trst_n,                // Test Reset (TRSTn)
    input   logic                                   tapc_tck,                   // Test Clock (TCK)
    input   logic                                   tapc_tms,                   // Test Mode Select (TMS)
    input   logic                                   tapc_tdi,                   // Test Data Input (TDI)
    output  logic                                   tapc_tdo,                   // Test Data Output (TDO)
    output  logic                                   tapc_tdo_en,                // TDO Enable, signal for TDO buffer control
`endif // SCR1_DBG_EN

    // Instruction Memory Interface
    input   logic                                   imem2core_req_ack_i,        // IMEM request acknowledge
    output  logic                                   core2imem_req_o,            // IMEM request
    output  type_scr1_mem_cmd_e                     core2imem_cmd_o,            // IMEM command
    output  logic [`SCR1_IMEM_AWIDTH-1:0]           core2imem_addr_o,           // IMEM address
    input   logic [`SCR1_IMEM_DWIDTH-1:0]           imem2core_rdata_i,          // IMEM read data
    input   type_scr1_mem_resp_e                    imem2core_resp_i,           // IMEM response

    // Data Memory Interface
    input   logic                                   dmem2core_req_ack_i,        // DMEM request acknowledge
    output  logic                                   core2dmem_req_o,            // DMEM request
    output  type_scr1_mem_cmd_e                     core2dmem_cmd_o,            // DMEM command
    output  type_scr1_mem_width_e                   core2dmem_width_o,          // DMEM data width
    output  logic [`SCR1_DMEM_AWIDTH-1:0]           core2dmem_addr_o,           // DMEM address
    output  logic [`SCR1_DMEM_DWIDTH-1:0]           core2dmem_wdata_o,          // DMEM write data
    input   logic [`SCR1_DMEM_DWIDTH-1:0]           dmem2core_rdata_i,          // DMEM read data
    input   type_scr1_mem_resp_e                    dmem2core_resp_i            // DMEM response
);

//-------------------------------------------------------------------------------
// Local parameters
//-------------------------------------------------------------------------------
localparam int unsigned SCR1_CORE_TOP_RST_SYNC_STAGES_NUM               = 2;

//-------------------------------------------------------------------------------
// Local signals declaration
//-------------------------------------------------------------------------------

// Reset Logic
`ifdef SCR1_DBG_EN
`else // SCR1_DBG_EN
logic                                           core_rst_n_in_sync;
logic                                           core_rst_n_qlfy;
logic                                           core_rst_n_status;
`endif // SCR1_DBG_EN
logic                                           core_rst_n;
logic                                           core_rst_n_status_sync;
logic                                           core_rst_status;
logic                                           core2hdu_rdc_qlfy;
logic                                           core2dm_rdc_qlfy;
logic                                           pwrup_rst_n_sync;
logic                                           rst_n_sync;
logic                                           cpu_rst_n_sync;

`ifdef SCR1_DBG_EN
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
logic                                           sys_rst_n;
logic                                           sys_rst_status;
logic                                           tapc_rst_n;
logic                                           hdu_rst_n;
logic                                           hdu2dm_rdc_qlfy;
logic                                           ndm_rst_n;
logic                                           dm_rst_n;
logic                                           hart_rst_n;
`endif // SCR1_DBG_EN

`ifdef SCR1_DBG_EN
// DM-Pipeline Interface
// HART Run Control i/f
logic                                           dm_active;
logic                                           dm_cmd_req;
type_scr1_hdu_dbgstates_e                       dm_cmd;
logic                                           dm_cmd_resp;
logic                                           dm_cmd_resp_qlfy;
logic                                           dm_cmd_rcode;
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
logic [SCR1_HDU_DATA_REG_WIDTH-1:0]             dm_dreg_wdata;
logic                                           dm_dreg_resp;
logic                                           dm_dreg_fail;
logic [SCR1_HDU_DATA_REG_WIDTH-1:0]             dm_dreg_rdata;

logic [`SCR1_XLEN-1 : 0]                        dm_pc_sample;
logic [`SCR1_XLEN-1 : 0]                        dm_pc_sample_qlfy;
`endif // SCR1_DBG_EN

`ifdef SCR1_CLKCTRL_EN
// Global clock gating logic
logic                                           sleep_pipe;
logic                                           wake_pipe;
logic                                           clk_pipe;
logic                                           clk_pipe_en;
logic                                           clk_dbgc;
logic                                           clk_alw_on;
`endif // SCR1_CLKCTRL_EN


//-------------------------------------------------------------------------------
// Reset Logic
//-------------------------------------------------------------------------------
`ifdef SCR1_DBG_EN
scr1_scu    i_scu (
    // Global signals
    .pwrup_rst_n                (pwrup_rst_n        ),
    .rst_n                      (rst_n              ),
    .cpu_rst_n                  (cpu_rst_n          ),
    .test_mode                  (test_mode          ),
    .test_rst_n                 (test_rst_n         ),
    .clk                        (clk                ),

    // TAPC scan-chains
    .tapcsync2scu_ch_sel_i      (tapc_scu_ch_sel    ),
    .tapcsync2scu_ch_id_i       ('0                 ),
    .tapcsync2scu_ch_capture_i  (tapc_dmi_ch_capture),
    .tapcsync2scu_ch_shift_i    (tapc_dmi_ch_shift  ),
    .tapcsync2scu_ch_update_i   (tapc_dmi_ch_update ),
    .tapcsync2scu_ch_tdi_i      (tapc_dmi_ch_tdi    ),
    .scu2tapcsync_ch_tdo_o      (tapc_scu_ch_tdo    ),

    // Input sync resets:
    .ndm_rst_n_i                (ndm_rst_n          ),
    .hart_rst_n_i               (hart_rst_n         ),

    // Generated resets
    .sys_rst_n_o                (sys_rst_n          ),
    .core_rst_n_o               (core_rst_n         ),
    .dm_rst_n_o                 (dm_rst_n           ),
    .hdu_rst_n_o                (hdu_rst_n          ),

    // Resets statuses
    .sys_rst_status_o           (sys_rst_status     ),
    .core_rst_status_o          (core_rst_status    ),

    // Reset Domain Crossing (RDC) qualifiers
    .sys_rdc_qlfy_o             (sys_rdc_qlfy_o     ),
    .core_rdc_qlfy_o            (core_rdc_qlfy_o    ),
    .core2hdu_rdc_qlfy_o        (core2hdu_rdc_qlfy  ),
    .core2dm_rdc_qlfy_o         (core2dm_rdc_qlfy   ),
    .hdu2dm_rdc_qlfy_o          (hdu2dm_rdc_qlfy    )
);

// TAPC reset
scr1_reset_and2_cell i_tapc_rstn_and2_cell (
    .rst_n_in       ({tapc_trst_n, pwrup_rst_n}),
    .test_rst_n     (test_rst_n                ),
    .test_mode      (test_mode                 ),
    .rst_n_out      (tapc_rst_n                )
);

assign sys_rst_n_o      = sys_rst_n;

// Reset inputs are assumed synchronous
assign pwrup_rst_n_sync = pwrup_rst_n;

`else // SCR1_DBG_EN

// Reset inputs are assumed synchronous
assign pwrup_rst_n_sync   = pwrup_rst_n;
assign rst_n_sync         = rst_n;
assign cpu_rst_n_sync     = cpu_rst_n;
assign core_rst_n_in_sync = rst_n_sync & cpu_rst_n_sync;

// Core Reset: core_rst_n
scr1_reset_qlfy_adapter_cell_sync i_core_rstn_qlfy_adapter_cell_sync (
    .rst_n              (pwrup_rst_n_sync  ),
    .clk                (clk               ),
    .test_rst_n         (test_rst_n        ),
    .test_mode          (test_mode         ),
    .reset_n_in_sync    (core_rst_n_in_sync),
    .reset_n_out_qlfy   (core_rst_n_qlfy   ),
    .reset_n_out        (core_rst_n        ),
    .reset_n_status     (core_rst_n_status )
);

scr1_data_sync_cell #(
    .STAGES_AMOUNT      (SCR1_CORE_TOP_RST_SYNC_STAGES_NUM)
) i_core_rstn_status_sync (
    .rst_n               (pwrup_rst_n_sync      ),
    .clk                 (clk                   ),
    .data_in             (core_rst_n_status     ),
    .data_out            (core_rst_n_status_sync)
);

assign core_rst_status      = ~core_rst_n_status_sync;
assign core_rdc_qlfy_o      = core_rst_n_qlfy;

`endif // SCR1_DBG_EN
assign core_rst_n_o         = core_rst_n;

//-------------------------------------------------------------------------------
// SCR1 pipeline
//-------------------------------------------------------------------------------
scr1_pipe_top i_pipe_top (
    // Control
    .pipe_rst_n                     (core_rst_n             ),
`ifdef SCR1_DBG_EN
    .pipe2hdu_rdc_qlfy_i            (core2hdu_rdc_qlfy      ),
    .dbg_rst_n                      (hdu_rst_n              ),
`endif // SCR1_DBG_EN
`ifndef SCR1_CLKCTRL_EN
    .clk                            (clk                    ),
`else // SCR1_CLKCTRL_EN
    .clk                            (clk_pipe               ),
    .pipe2clkctl_sleep_req_o        (sleep_pipe             ),
    .pipe2clkctl_wake_req_o         (wake_pipe              ),
    .clkctl2pipe_clk_alw_on_i       (clk_alw_on             ),
    .clkctl2pipe_clk_dbgc_i         (clk_dbgc               ),
    .clkctl2pipe_clk_en_i           (clk_pipe_en            ),
`endif // SCR1_CLKCTRL_EN

    // Instruction memory interface
    .pipe2imem_req_o                (core2imem_req_o        ),
    .pipe2imem_cmd_o                (core2imem_cmd_o        ),
    .pipe2imem_addr_o               (core2imem_addr_o       ),
    .imem2pipe_req_ack_i            (imem2core_req_ack_i    ),
    .imem2pipe_rdata_i              (imem2core_rdata_i      ),
    .imem2pipe_resp_i               (imem2core_resp_i       ),

    // Data memory interface
    .pipe2dmem_req_o                (core2dmem_req_o        ),
    .pipe2dmem_cmd_o                (core2dmem_cmd_o        ),
    .pipe2dmem_width_o              (core2dmem_width_o      ),
    .pipe2dmem_addr_o               (core2dmem_addr_o       ),
    .pipe2dmem_wdata_o              (core2dmem_wdata_o      ),
    .dmem2pipe_req_ack_i            (dmem2core_req_ack_i    ),
    .dmem2pipe_rdata_i              (dmem2core_rdata_i      ),
    .dmem2pipe_resp_i               (dmem2core_resp_i       ),

`ifdef SCR1_DBG_EN
    // Debug interface:
    .dbg_en                         (1'b1                   ),
    // Debug interface:
    // DM <-> Pipeline: HART Run Control i/f
    .dm2pipe_active_i               (dm_active              ),
    .dm2pipe_cmd_req_i              (dm_cmd_req             ),
    .dm2pipe_cmd_i                  (dm_cmd                 ),
    .pipe2dm_cmd_resp_o             (dm_cmd_resp            ),
    .pipe2dm_cmd_rcode_o            (dm_cmd_rcode           ),
    .pipe2dm_hart_event_o           (dm_hart_event          ),
    .pipe2dm_hart_status_o          (dm_hart_status         ),

    // DM <-> Pipeline: Program Buffer - HART instruction execution i/f
    .pipe2dm_pbuf_addr_o            (dm_pbuf_addr           ),
    .dm2pipe_pbuf_instr_i           (dm_pbuf_instr          ),

    // DM <-> Pipeline: HART Abstract Data regs i/f
    .pipe2dm_dreg_req_o             (dm_dreg_req            ),
    .pipe2dm_dreg_wr_o              (dm_dreg_wr             ),
    .pipe2dm_dreg_wdata_o           (dm_dreg_wdata          ),
    .dm2pipe_dreg_resp_i            (dm_dreg_resp           ),
    .dm2pipe_dreg_fail_i            (dm_dreg_fail           ),
    .dm2pipe_dreg_rdata_i           (dm_dreg_rdata          ),

    // DM <-> Pipeline: PC i/f
    .pipe2dm_pc_sample_o            (dm_pc_sample           ),
`endif // SCR1_DBG_EN

    // IRQ
`ifdef SCR1_IPIC_EN
    .soc2pipe_irq_lines_i           (core_irq_lines_i       ),
`else // SCR1_IPIC_EN
    .soc2pipe_irq_ext_i             (core_irq_ext_i         ),
`endif // SCR1_IPIC_EN
    .soc2pipe_irq_soft_i            (core_irq_soft_i        ),
    .soc2pipe_irq_mtimer_i          (core_irq_mtimer_i      ),

    // Memory-mapped external timer
    .soc2pipe_mtimer_val_i          (core_mtimer_val_i      ),

    // Fuse
    .soc2pipe_fuse_mhartid_i        (core_fuse_mhartid_i    )
);


`ifdef SCR1_DBG_EN
//-------------------------------------------------------------------------------
// TAP Controller (TAPC)
//-------------------------------------------------------------------------------
scr1_tapc i_tapc (
    // JTAG signals
    .tapc_trst_n                    (tapc_rst_n                ),
    .tapc_tck                       (tapc_tck                  ),
    .tapc_tms                       (tapc_tms                  ),
    .tapc_tdi                       (tapc_tdi                  ),
    .tapc_tdo                       (tapc_tdo                  ),
    .tapc_tdo_en                    (tapc_tdo_en               ),

    // Fuses
    .soc2tapc_fuse_idcode_i         (tapc_fuse_idcode_i        ),

    // DMI/SCU scan-chains
    .tapc2tapcsync_scu_ch_sel_o     (tapc_scu_ch_sel_tapout    ),
    .tapc2tapcsync_dmi_ch_sel_o     (tapc_dmi_ch_sel_tapout    ),
    .tapc2tapcsync_ch_id_o          (tapc_dmi_ch_id_tapout     ),
    .tapc2tapcsync_ch_capture_o     (tapc_dmi_ch_capture_tapout),
    .tapc2tapcsync_ch_shift_o       (tapc_dmi_ch_shift_tapout  ),
    .tapc2tapcsync_ch_update_o      (tapc_dmi_ch_update_tapout ),
    .tapc2tapcsync_ch_tdi_o         (tapc_dmi_ch_tdi_tapout    ),
    .tapcsync2tapc_ch_tdo_i         (tapc_dmi_ch_tdo_tapin     )
);

scr1_tapc_synchronizer i_tapc_synchronizer (
    // System common signals
    .pwrup_rst_n                    (pwrup_rst_n_sync          ),
    .dm_rst_n                       (dm_rst_n                  ),
    .clk                            (clk                       ),

    // JTAG common signals
    .tapc_trst_n                    (tapc_rst_n                ),
    .tapc_tck                       (tapc_tck                  ),

    // DMI/SCU scan-chains
    .tapc2tapcsync_scu_ch_sel_i     (tapc_scu_ch_sel_tapout    ),
    .tapcsync2scu_ch_sel_o          (tapc_scu_ch_sel           ),
    .tapc2tapcsync_dmi_ch_sel_i     (tapc_dmi_ch_sel_tapout    ),
    .tapcsync2dmi_ch_sel_o          (tapc_dmi_ch_sel           ),

    .tapc2tapcsync_ch_id_i          (tapc_dmi_ch_id_tapout     ),
    .tapcsync2core_ch_id_o          (tapc_dmi_ch_id            ),
    .tapc2tapcsync_ch_capture_i     (tapc_dmi_ch_capture_tapout),
    .tapcsync2core_ch_capture_o     (tapc_dmi_ch_capture       ),
    .tapc2tapcsync_ch_shift_i       (tapc_dmi_ch_shift_tapout  ),
    .tapcsync2core_ch_shift_o       (tapc_dmi_ch_shift         ),
    .tapc2tapcsync_ch_update_i      (tapc_dmi_ch_update_tapout ),
    .tapcsync2core_ch_update_o      (tapc_dmi_ch_update        ),
    .tapc2tapcsync_ch_tdi_i         (tapc_dmi_ch_tdi_tapout    ),
    .tapcsync2core_ch_tdi_o         (tapc_dmi_ch_tdi           ),
    .tapc2tapcsync_ch_tdo_i         (tapc_dmi_ch_tdo_tapin     ),
    .tapcsync2core_ch_tdo_o         (tapc_ch_tdo               )
);
assign tapc_ch_tdo = (tapc_scu_ch_tdo & tapc_scu_ch_sel)
                   | (tapc_dmi_ch_tdo & tapc_dmi_ch_sel);

scr1_dmi i_dmi (
    .rst_n                      (dm_rst_n           ),
    .clk                        (clk                ),

    // TAP scan-chains
    .tapcsync2dmi_ch_sel_i      (tapc_dmi_ch_sel    ),
    .tapcsync2dmi_ch_id_i       (tapc_dmi_ch_id     ),
    .tapcsync2dmi_ch_capture_i  (tapc_dmi_ch_capture),
    .tapcsync2dmi_ch_shift_i    (tapc_dmi_ch_shift  ),
    .tapcsync2dmi_ch_update_i   (tapc_dmi_ch_update ),
    .tapcsync2dmi_ch_tdi_i      (tapc_dmi_ch_tdi    ),
    .dmi2tapcsync_ch_tdo_o      (tapc_dmi_ch_tdo    ),

    // DMI
    .dm2dmi_resp_i              (dmi_resp           ),
    .dm2dmi_rdata_i             (dmi_rdata          ),
    .dmi2dm_req_o               (dmi_req            ),
    .dmi2dm_wr_o                (dmi_wr             ),
    .dmi2dm_addr_o              (dmi_addr           ),
    .dmi2dm_wdata_o             (dmi_wdata          )
);

`endif // SCR1_DBG_EN


`ifdef SCR1_DBG_EN

//-------------------------------------------------------------------------------
// Debug Module (DM)
//-------------------------------------------------------------------------------
assign dm_cmd_resp_qlfy    = dm_cmd_resp   & {$bits(dm_cmd_resp){hdu2dm_rdc_qlfy}};
assign dm_hart_event_qlfy  = dm_hart_event & {$bits(dm_hart_event){hdu2dm_rdc_qlfy}};
assign dm_hart_status_qlfy.dbg_state = hdu2dm_rdc_qlfy ? dm_hart_status.dbg_state
                                                       : SCR1_HDU_DBGSTATE_RESET;
assign dm_hart_status_qlfy.except    = dm_hart_status.except;
assign dm_hart_status_qlfy.ebreak    = dm_hart_status.ebreak;
assign dm_pbuf_addr_qlfy   = dm_pbuf_addr  & {$bits(dm_pbuf_addr){hdu2dm_rdc_qlfy}};
assign dm_dreg_req_qlfy    = dm_dreg_req   & {$bits(dm_dreg_req){hdu2dm_rdc_qlfy}};
assign dm_pc_sample_qlfy   = dm_pc_sample  & {$bits(dm_pc_sample){core2dm_rdc_qlfy}};

scr1_dm i_dm (
    // Common signals
    .rst_n                      (dm_rst_n               ),
    .clk                        (clk                    ),

    // DM internal interface
    .dmi2dm_req_i               (dmi_req                ),
    .dmi2dm_wr_i                (dmi_wr                 ),
    .dmi2dm_addr_i              (dmi_addr               ),
    .dmi2dm_wdata_i             (dmi_wdata              ),
    .dm2dmi_resp_o              (dmi_resp               ),
    .dm2dmi_rdata_o             (dmi_rdata              ),

    // DM <-> Pipeline: HART Run Control i/f
    .ndm_rst_n_o                (ndm_rst_n              ),
    .hart_rst_n_o               (hart_rst_n             ),
    .dm2pipe_active_o           (dm_active              ),
    .dm2pipe_cmd_req_o          (dm_cmd_req             ),
    .dm2pipe_cmd_o              (dm_cmd                 ),
    .pipe2dm_cmd_resp_i         (dm_cmd_resp_qlfy       ),
    .pipe2dm_cmd_rcode_i        (dm_cmd_rcode           ),
    .pipe2dm_hart_event_i       (dm_hart_event_qlfy     ),
    .pipe2dm_hart_status_i      (dm_hart_status_qlfy    ),

    .soc2dm_fuse_mhartid_i      (core_fuse_mhartid_i    ),
    .pipe2dm_pc_sample_i        (dm_pc_sample_qlfy      ),

    // DM <-> Pipeline: HART Abstract Command / Program Buffer i/f
    .pipe2dm_pbuf_addr_i        (dm_pbuf_addr_qlfy      ),
    .dm2pipe_pbuf_instr_o       (dm_pbuf_instr          ),

    // DM <-> Pipeline: HART Abstract Data regs i/f
    .pipe2dm_dreg_req_i         (dm_dreg_req_qlfy       ),
    .pipe2dm_dreg_wr_i          (dm_dreg_wr             ),
    .pipe2dm_dreg_wdata_i       (dm_dreg_wdata          ),
    .dm2pipe_dreg_resp_o        (dm_dreg_resp           ),
    .dm2pipe_dreg_fail_o        (dm_dreg_fail           ),
    .dm2pipe_dreg_rdata_o       (dm_dreg_rdata          )
);
`endif // SCR1_DBG_EN


`ifdef SCR1_CLKCTRL_EN
//-------------------------------------------------------------------------------
// Global clock gating logic
//-------------------------------------------------------------------------------
scr1_clk_ctrl i_clk_ctrl (
    .clk                            (clk        ),
    .rst_n                          (rst_n      ),
    .test_mode                      (test_mode  ),
    .test_rst_n                     (test_rst_n ),

    // Sleep/wake interface
    .pipe2clkctl_sleep_req_i        (sleep_pipe ),
    .pipe2clkctl_wake_req_i         (wake_pipe  ),

    // Clocks
    .clkctl2pipe_clk_alw_on_o       (clk_alw_on ),
    .clkctl2pipe_clk_o              (clk_pipe   ),
    .clkctl2pipe_clk_en_o           (clk_pipe_en),
    .clkctl2pipe_clk_dbgc_o         (clk_dbgc   )
);
`endif // SCR1_CLKCTRL_EN

endmodule : scr1_core_top
