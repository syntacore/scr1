/// Copyright by Syntacore LLC © 2016-2020. See LICENSE for details
/// @file <scr1_scu.sv>
/// @brief System Control Unit (SCU)
///

//------------------------------------------------------------------------------
 //
 // Functionality:
 // - Generates System, Core, HDU and DM resets and their qualifier signals
 // - Provides debugger with software System and Core resets generation functionality
 // - Allows to set the behavior of DM and HDU resets
 // - Shows resets Statuses and Sticky Statuses

 // Structure:
 // - TAPC scan-chain interface
 // - SCU CSRs write/read interface
 // - SCU CSRS:
 //   - CONTROL register
 //   - MODE register
 //   - STATUS register
 //   - STICKY_STATUS register
 // - Reset logic
 //   - System Reset
 //   - Core Reset
 //   - DM Reset
 //   - HDU Reset
//------------------------------------------------------------------------------

`include "scr1_arch_description.svh"
`include "scr1_scu.svh"

`ifdef SCR1_DBG_EN

module scr1_scu (
    // Global signals
    input  logic        pwrup_rst_n,                  // Power-Up Reset
    input  logic        rst_n,                        // Regular Reset
    input  logic        cpu_rst_n,                    // CPU Reset
    input  logic        test_mode,                    // DFT Test Mode
    input  logic        test_rst_n,                   // DFT Test Reset
    input  logic        clk,                          // SCU clock

    // TAPC scan-chains
    input  logic        tapcsync2scu_ch_sel_i,        // TAPC Chain Select
    input  logic        tapcsync2scu_ch_id_i,         // TAPC Chain ID
    input  logic        tapcsync2scu_ch_capture_i,    // TAPC Chain Capture
    input  logic        tapcsync2scu_ch_shift_i,      // TAPC Chain Shift
    input  logic        tapcsync2scu_ch_update_i,     // TAPC Chain Update
    input  logic        tapcsync2scu_ch_tdi_i,        // TAPC Chain TDI
    output logic        scu2tapcsync_ch_tdo_o,        // TAPC Chain TDO

    // Input sync resets:
    input  logic        ndm_rst_n_i,                  // Non-DM Reset input from DM
    input  logic        hart_rst_n_i,                 // HART Reset from DM

    // Generated resets
    output logic        sys_rst_n_o,                  // System/Cluster Reset
    output logic        core_rst_n_o,                 // Core Reset
    output logic        dm_rst_n_o,                   // Debug Module Reset
    output logic        hdu_rst_n_o,                  // HART Debug Unit Reset

    // Resets statuses
    output logic        sys_rst_status_o,             // System Reset Status (sync'ed to POR reset domain)
    output logic        core_rst_status_o,            // Core Reset Status (sync'ed to POR reset domain)

    // Reset Domain Crossing (RDC) qualifiers
    output logic        sys_rdc_qlfy_o,               // System/Cluster-to-ExternalSOC Reset Domain Crossing Qualifier
    output logic        core_rdc_qlfy_o,              // Core-to-ExternalSOC Reset Domain Crossing Qualifier
    output logic        core2hdu_rdc_qlfy_o,          // Core-to-HDU Reset Domain Crossing Qualifier
    output logic        core2dm_rdc_qlfy_o,           // Core-to-DM Reset Domain Crossing Qualifier
    output logic        hdu2dm_rdc_qlfy_o             // HDU-to-DM Reset Domain Crossing Qualifier
);

//------------------------------------------------------------------------------
// Local Parameters
//======================================================================================================================
localparam int unsigned SCR1_SCU_RST_SYNC_STAGES_NUM        = 2;

//------------------------------------------------------------------------------
// Local Signals
//------------------------------------------------------------------------------

// SCU CSR write/read i/f
//------------------------------------------------------------------------------

// TAPC scan-chain control logic
logic                                       scu_csr_req;
logic                                       tapc_dr_cap_req;
logic                                       tapc_dr_shft_req;
logic                                       tapc_dr_upd_req;

// TAPC shift register signals
logic                                       tapc_shift_upd;
type_scr1_scu_sysctrl_dr_s                  tapc_shift_ff;
type_scr1_scu_sysctrl_dr_s                  tapc_shift_next;

// TAPC shadow register signals
type_scr1_scu_sysctrl_dr_s                  tapc_shadow_ff;

// SCU CSR write/read i/f
//------------------------------------------------------------------------------

logic [SCR1_SCU_DR_SYSCTRL_DATA_WIDTH-1:0]  scu_csr_wdata;
logic [SCR1_SCU_DR_SYSCTRL_DATA_WIDTH-1:0]  scu_csr_rdata;

// SCU CSRs signals
//------------------------------------------------------------------------------

// Control register
type_scr1_scu_sysctrl_control_reg_s         scu_control_ff;
logic                                       scu_control_wr_req;

// Mode register
type_scr1_scu_sysctrl_mode_reg_s            scu_mode_ff;
logic                                       scu_mode_wr_req;

// Status register
type_scr1_scu_sysctrl_status_reg_s          scu_status_ff;
type_scr1_scu_sysctrl_status_reg_s          scu_status_ff_dly;
type_scr1_scu_sysctrl_status_reg_s          scu_status_ff_posedge;

// Sticky Status register
type_scr1_scu_sysctrl_status_reg_s          scu_sticky_sts_ff;
logic                                       scu_sticky_sts_wr_req;

// Reset logic signals
//------------------------------------------------------------------------------

// Input resets synchronization signals
logic                                       pwrup_rst_n_sync;
logic                                       rst_n_sync;
logic                                       cpu_rst_n_sync;

// System Reset signals
logic                                       sys_rst_n_in;
logic                                       sys_rst_n_status;
logic                                       sys_rst_n_status_sync;
logic                                       sys_rst_n_qlfy;
logic                                       sys_reset_n;

// Core Reset signals
logic                                       core_rst_n_in_sync;
logic                                       core_rst_n_status;
logic                                       core_rst_n_status_sync;
logic                                       core_rst_n_qlfy;
logic                                       core_reset_n;

// HDU Reset signals
logic                                       hdu_rst_n_in_sync;
logic                                       hdu_rst_n_status;
logic                                       hdu_rst_n_status_sync;
logic                                       hdu_rst_n_qlfy;

// DM Reset signals
logic                                       dm_rst_n_in;
logic                                       dm_rst_n_status;

//------------------------------------------------------------------------------
// TAPC scan-chain i/f
//------------------------------------------------------------------------------
//
 // Consists of the following functional units:
 // - TAPC scan-chain control logic
 // - TAPC shift register
 // - TAPC shadow register
//

// TAPC scan-chain control logic
//------------------------------------------------------------------------------

assign scu_csr_req      = tapcsync2scu_ch_sel_i & (tapcsync2scu_ch_id_i == '0);
assign tapc_dr_cap_req  = scu_csr_req & tapcsync2scu_ch_capture_i;
assign tapc_dr_shft_req = scu_csr_req & tapcsync2scu_ch_shift_i;
assign tapc_dr_upd_req  = scu_csr_req & tapcsync2scu_ch_update_i;

// TAPC shift register
//------------------------------------------------------------------------------

assign tapc_shift_upd = tapc_dr_cap_req | tapc_dr_shft_req;

always_ff @(posedge clk, negedge pwrup_rst_n_sync) begin
    if (~pwrup_rst_n_sync) begin
        tapc_shift_ff <= '0;
    end else if (tapc_shift_upd) begin
        tapc_shift_ff <= tapc_shift_next;
    end
end

assign tapc_shift_next = tapc_dr_cap_req  ? tapc_shadow_ff
                       : tapc_dr_shft_req ? {tapcsync2scu_ch_tdi_i, tapc_shift_ff[$bits(type_scr1_scu_sysctrl_dr_s)-1:1]}
                                          : tapc_shift_ff;

// TAPC shadow register
//------------------------------------------------------------------------------

always_ff @(posedge clk, negedge pwrup_rst_n_sync) begin
    if (~pwrup_rst_n_sync) begin
        tapc_shadow_ff      <= '0;
    end else if (tapc_dr_upd_req) begin
        tapc_shadow_ff.op   <= tapc_shift_ff.op;
        tapc_shadow_ff.addr <= tapc_shift_ff.addr;
        tapc_shadow_ff.data <= scu_csr_wdata;
    end
end

assign scu2tapcsync_ch_tdo_o = tapc_shift_ff[0];

//------------------------------------------------------------------------------
// SCU CSRs write/read interface
//------------------------------------------------------------------------------

// Write interface
//------------------------------------------------------------------------------

// Register selection logic
always_comb begin
    scu_control_wr_req    = 1'b0;
    scu_mode_wr_req       = 1'b0;
    scu_sticky_sts_wr_req = 1'b0;

    if (tapc_dr_upd_req && (tapc_shift_ff.op != SCR1_SCU_SYSCTRL_OP_READ)) begin
        case (tapc_shift_ff.addr)
            SCR1_SCU_SYSCTRL_ADDR_CONTROL: scu_control_wr_req    = 1'b1;
            SCR1_SCU_SYSCTRL_ADDR_MODE   : scu_mode_wr_req       = 1'b1;
            SCR1_SCU_SYSCTRL_ADDR_STICKY : scu_sticky_sts_wr_req = (tapc_shift_ff.op == SCR1_SCU_SYSCTRL_OP_CLRBITS);
            default                      : begin end
        endcase
    end
end

// Write data construction
always_comb begin
    scu_csr_wdata = '0;

    if (tapc_dr_upd_req) begin
        case (tapc_shift_ff.op)
            SCR1_SCU_SYSCTRL_OP_WRITE  : scu_csr_wdata = tapc_shift_ff.data;
            SCR1_SCU_SYSCTRL_OP_READ   : scu_csr_wdata = scu_csr_rdata;
            SCR1_SCU_SYSCTRL_OP_SETBITS: scu_csr_wdata = scu_csr_rdata |   tapc_shift_ff.data;
            SCR1_SCU_SYSCTRL_OP_CLRBITS: scu_csr_wdata = scu_csr_rdata & (~tapc_shift_ff.data);
            default                    : begin end
        endcase
    end
end

// Read interface
//------------------------------------------------------------------------------

// Read data multiplexer
always_comb begin
    scu_csr_rdata = '0;

    if (tapc_dr_upd_req) begin
        case (tapc_shift_ff.addr)
            SCR1_SCU_SYSCTRL_ADDR_CONTROL: scu_csr_rdata = scu_control_ff;
            SCR1_SCU_SYSCTRL_ADDR_MODE   : scu_csr_rdata = scu_mode_ff;
            SCR1_SCU_SYSCTRL_ADDR_STATUS : scu_csr_rdata = scu_status_ff;
            SCR1_SCU_SYSCTRL_ADDR_STICKY : scu_csr_rdata = scu_sticky_sts_ff;
            default                      : scu_csr_rdata = 'x;
        endcase
    end
end

//------------------------------------------------------------------------------
// SCU CSRs
//------------------------------------------------------------------------------
//
 // Registers:
 // - CONTROL register
 // - MODE register
 // - STATUS register
 // - STICKY_STATUS register
//

// CONTROL register
//------------------------------------------------------------------------------
// Allows debugger to generate System and Core resets

always_ff @(posedge clk, negedge pwrup_rst_n_sync) begin
    if (~pwrup_rst_n_sync) begin
        scu_control_ff <= '0;
    end else if (scu_control_wr_req) begin
        scu_control_ff <= scu_csr_wdata;
    end
end

// MODE register
//------------------------------------------------------------------------------
// Sets reset behavior for DM Reset and HDU Reset signals

always_ff @(posedge clk, negedge pwrup_rst_n_sync) begin
    if (~pwrup_rst_n_sync) begin
        scu_mode_ff <= '0;
    end else if (scu_mode_wr_req) begin
        scu_mode_ff <= scu_csr_wdata;
    end
end

// STATUS register
//------------------------------------------------------------------------------
// Holds the status of every output reset signal (System, Core, DM and HDU)

assign scu_status_ff.sys_reset  = sys_rst_status_o ;
assign scu_status_ff.core_reset = core_rst_status_o;
assign scu_status_ff.dm_reset   = ~dm_rst_n_status;
assign scu_status_ff.hdu_reset  = ~hdu_rst_n_status_sync;

// Status Register positive edge detection logic
always_ff @(posedge clk, negedge pwrup_rst_n_sync) begin
    if (~pwrup_rst_n_sync) begin
        scu_status_ff_dly <= '0;
    end else begin
        scu_status_ff_dly <= scu_status_ff;
    end
end

assign scu_status_ff_posedge = scu_status_ff & ~scu_status_ff_dly;

// STICKY_STATUS register
//------------------------------------------------------------------------------
// For every output reset signal shows if it was asserted since the last bit clearing

always_ff @(posedge clk, negedge pwrup_rst_n_sync) begin
    if (~pwrup_rst_n_sync) begin
        scu_sticky_sts_ff <= '0;
    end else begin
        for (int unsigned i = 0; i < $bits(type_scr1_scu_sysctrl_status_reg_s); ++i) begin
            if (scu_status_ff_posedge[i]) begin
                scu_sticky_sts_ff[i] <= 1'b1;
            end else if (scu_sticky_sts_wr_req) begin
                scu_sticky_sts_ff[i] <= scu_csr_wdata[i];
            end
        end
    end
end

//------------------------------------------------------------------------------
// Reset logic
//------------------------------------------------------------------------------
//
 // Consists of the following functional units:
 // - System Reset logic
 // - Core Reset logic
 // - Hart Debug Unit Reset logic
 // - Debug Module Reset logic
//

// Reset inputs are assumed synchronous
assign pwrup_rst_n_sync = pwrup_rst_n;
assign rst_n_sync       = rst_n;
assign cpu_rst_n_sync   = cpu_rst_n;

// Intermediate resets:
assign sys_reset_n  = ~scu_control_ff.sys_reset;
assign core_reset_n = ~scu_control_ff.core_reset;

// System/Cluster Reset: sys_rst_n_o
//------------------------------------------------------------------------------

scr1_reset_qlfy_adapter_cell_sync   i_sys_rstn_qlfy_adapter_cell_sync (
    .rst_n                          (pwrup_rst_n_sync),
    .clk                            (clk             ),
    .test_rst_n                     (test_rst_n      ),
    .test_mode                      (test_mode       ),
    .reset_n_in_sync                (sys_rst_n_in    ),
    .reset_n_out_qlfy               (sys_rst_n_qlfy  ),
    .reset_n_out                    (sys_rst_n_o     ),
    .reset_n_status                 (sys_rst_n_status)
);

assign sys_rst_n_in = sys_reset_n & ndm_rst_n_i & rst_n_sync;

scr1_data_sync_cell #(
    .STAGES_AMOUNT       (SCR1_SCU_RST_SYNC_STAGES_NUM)
) i_sys_rstn_status_sync (
    .rst_n               (pwrup_rst_n_sync     ),
    .clk                 (clk                  ),
    .data_in             (sys_rst_n_status     ),
    .data_out            (sys_rst_n_status_sync)
);

assign sys_rst_status_o = ~sys_rst_n_status_sync;

// System/Cluster-to-ExternalSOC RDC qualifier
assign sys_rdc_qlfy_o = sys_rst_n_qlfy;

// Core Reset: core_rst_n_o
//------------------------------------------------------------------------------

scr1_reset_qlfy_adapter_cell_sync   i_core_rstn_qlfy_adapter_cell_sync (
    .rst_n                          (pwrup_rst_n_sync  ),
    .clk                            (clk               ),
    .test_rst_n                     (test_rst_n        ),
    .test_mode                      (test_mode         ),
    .reset_n_in_sync                (core_rst_n_in_sync),
    .reset_n_out_qlfy               (core_rst_n_qlfy   ),
    .reset_n_out                    (core_rst_n_o      ),
    .reset_n_status                 (core_rst_n_status )
);

assign core_rst_n_in_sync   = sys_rst_n_in & hart_rst_n_i & core_reset_n & cpu_rst_n_sync;

scr1_data_sync_cell #(
    .STAGES_AMOUNT        (SCR1_SCU_RST_SYNC_STAGES_NUM)
) i_core_rstn_status_sync (
    .rst_n                (pwrup_rst_n_sync      ),
    .clk                  (clk                   ),
    .data_in              (core_rst_n_status     ),
    .data_out             (core_rst_n_status_sync)
);

assign core_rst_status_o = ~core_rst_n_status_sync;

// Core Reset RDC Qualifiers:
//  - Core-to-ExternalSOC RDC Qlfy
assign core_rdc_qlfy_o = core_rst_n_qlfy;
//  - Core-to-HDU RDC Qlfy
assign core2hdu_rdc_qlfy_o = core_rst_n_qlfy;
//  - Core-to-DebugModule RDC Qlfy
assign core2dm_rdc_qlfy_o  = core_rst_n_qlfy;

// Hart Debug Unit Reset: hdu_rst_n_o
//------------------------------------------------------------------------------

scr1_reset_qlfy_adapter_cell_sync   i_hdu_rstn_qlfy_adapter_cell_sync (
    .rst_n                          (pwrup_rst_n_sync ),
    .clk                            (clk              ),
    .test_rst_n                     (test_rst_n       ),
    .test_mode                      (test_mode        ),
    .reset_n_in_sync                (hdu_rst_n_in_sync),
    .reset_n_out_qlfy               (hdu_rst_n_qlfy   ),
    .reset_n_out                    (hdu_rst_n_o      ),
    .reset_n_status                 (hdu_rst_n_status )
);

assign hdu_rst_n_in_sync = scu_mode_ff.hdu_rst_bhv | core_rst_n_in_sync;

scr1_data_sync_cell #(
    .STAGES_AMOUNT       (SCR1_SCU_RST_SYNC_STAGES_NUM)
) i_hdu_rstn_status_sync (
    .rst_n               (pwrup_rst_n_sync     ),
    .clk                 (clk                  ),
    .data_in             (hdu_rst_n_status     ),
    .data_out            (hdu_rst_n_status_sync)
);

// Hart Debug Unit Reset RDC Qualifiers:
//  - HDU-to-DebugModule RDC Qlfy
assign hdu2dm_rdc_qlfy_o = hdu_rst_n_qlfy;

// Debug Module Reset: dm_rst_n_o
//------------------------------------------------------------------------------

scr1_reset_buf_cell i_dm_rstn_buf_cell (
    .rst_n              (pwrup_rst_n_sync),
    .clk                (clk             ),
    .test_mode          (test_mode       ),
    .test_rst_n         (test_rst_n      ),
    .reset_n_in         (dm_rst_n_in     ),
    .reset_n_out        (dm_rst_n_o      ),
    .reset_n_status     (dm_rst_n_status )
);

assign dm_rst_n_in  = ~scu_mode_ff.dm_rst_bhv | sys_reset_n;

`ifdef SCR1_TRGT_SIMULATION
//--------------------------------------------------------------------
// Assertions
//--------------------------------------------------------------------

`ifndef VERILATOR
// Preventing some assertions to be raised at 0 sim time or in the first cycle
initial begin
$assertoff(0, scr1_scu);
repeat (2) @(posedge clk);
$asserton(0, scr1_scu);
end
`endif // VERILATOR

// X checks
SCR1_SVA_SCU_RESETS_XCHECK : assert property (
    @(negedge clk)
    !$isunknown({pwrup_rst_n, rst_n, cpu_rst_n, ndm_rst_n_i, hart_rst_n_i})
) else $error("SCU resets error: unknown values of input resets");

// Qualifiers checks
SCR1_SVA_SCU_SYS2SOC_QLFY_CHECK : assert property (
    @(negedge clk) disable iff (~pwrup_rst_n)
    $fell(sys_rst_n_o) |-> $fell($past(sys_rdc_qlfy_o))
) else $error("SCU sys2soc qlfy error: qlfy wasn't raised prior to reset");

SCR1_SVA_SCU_CORE2SOC_QLFY_CHECK : assert property (
    @(negedge clk) disable iff (~pwrup_rst_n)
    $fell(core_rst_n_o) |-> $fell($past(core_rdc_qlfy_o))
) else $error("SCU core2soc qlfy error: qlfy wasn't raised prior to reset");

SCR1_SVA_SCU_CORE2HDU_QLFY_CHECK : assert property (
    @(negedge clk) disable iff (~pwrup_rst_n)
    $fell(core_rst_n_o) |-> $fell($past(core2hdu_rdc_qlfy_o))
) else $error("SCU core2hdu qlfy error: qlfy wasn't raised prior to reset");

SCR1_SVA_SCU_CORE2DM_QLFY_CHECK : assert property (
    @(negedge clk) disable iff (~pwrup_rst_n)
    $fell(core_rst_n_o) |-> $fell($past(core2dm_rdc_qlfy_o))
) else $error("SCU core2dm qlfy error: qlfy wasn't raised prior to reset");

SCR1_SVA_SCU_HDU2DM_QLFY_CHECK : assert property (
    @(negedge clk) disable iff (~pwrup_rst_n)
    $fell(hdu_rst_n_o) |-> $fell($past(hdu2dm_rdc_qlfy_o))
) else $error("SCU hdu2dm qlfy error: qlfy wasn't raised prior to reset");

`endif // SCR1_TRGT_SIMULATION

endmodule : scr1_scu
`endif // SCR1_DBG_EN

