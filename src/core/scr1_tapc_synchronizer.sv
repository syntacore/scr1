/// Copyright by Syntacore LLC © 2016-2018. See LICENSE for details
/// @file       <scr1_tapc_synchronizer.sv>
/// @brief      TAPC clock domain crossing synchronizer
///

`include "scr1_arch_description.svh"

`ifdef SCR1_DBGC_EN
`include "scr1_tapc.svh"
`include "scr1_dbgc.svh"

module scr1_tapc_synchronizer (
    // System common signals
    input   logic                                   async_rst_n,        // Asynchronous Reset
    input   logic                                   sys_rst_n,          // System Reset (generated as synchronous)
    input   logic                                   clk,                // System Clock (SysCLK)
    // JTAG common signals
    input   logic                                   trst_n,             // JTAG Test Reset (TRSTn)
    input   logic                                   tck,                // JTAG Test Clock (TCK)
    // System Control/Status signals
    input   logic                                   sys_rst_ctrl,       // System Reset Control input  (TCK domain)
    output  logic                                   sys_rst_ctrl_core,  // System Reset Control output (SysCLK domain)

    output  logic                                   sys_rst_sts,        // System Reset Status output (TCK domain)
    input   logic                                   sys_rst_sts_core,   // System Reset Status input  (SysCLK domain)

    // DAP scan-chains
    input  logic                                    dap_ch_sel,         // DAP Chain Select input  (TCK domain)
    output logic                                    dap_ch_sel_core,    // DAP Chain Select output (SysCLK domain)

    input  logic [SCR1_DBGC_DAP_CH_ID_WIDTH-1:0]    dap_ch_id,          // DAP Chain Identificator input  (TCK domain)
    output logic [SCR1_DBGC_DAP_CH_ID_WIDTH-1:0]    dap_ch_id_core,     // DAP Chain Identificator output (SysCLK domain)

    input  logic                                    dap_ch_capture,     // DAP Chain Capture input  (TCK domain)
    output logic                                    dap_ch_capture_core,// DAP Chain Capture output (SysCLK domain)

    input  logic                                    dap_ch_shift,       // DAP Chain Shift input  (TCK domain)
    output logic                                    dap_ch_shift_core,  // DAP Chain Shift output (SysCLK domain)

    input  logic                                    dap_ch_update,      // DAP Chain Update input  (TCK domain)
    output logic                                    dap_ch_update_core, // DAP Chain Update output (SysCLK domain)

    input  logic                                    dap_ch_tdi,         // DAP Chain TDI input  (TCK domain)
    output logic                                    dap_ch_tdi_core,    // DAP Chain TDI output (SysCLK domain)

    output logic                                    dap_ch_tdo,         // DAP Chain TDO output (TCK domain)
    input  logic                                    dap_ch_tdo_core     // DAP Chain TDO input  (SysCLK domain)
);

//-------------------------------------------------------------------------------
// Local signals declaration
//-------------------------------------------------------------------------------

logic           tck_divpos;
logic           tck_divneg;
logic           tck_rise_load;
logic           tck_rise_reset;
logic           tck_fall_load;
logic           tck_fall_reset;
logic [3:0]     tck_divpos_sync;
logic [3:0]     tck_divneg_sync;
logic [1:0]     sys_rst_sts_core_sync;
logic [2:0]     sys_rst_ctrl_sync;
logic [2:0]     dap_ch_capture_sync;
logic [2:0]     dap_ch_shift_sync;
logic [2:0]     dap_ch_tdi_sync;

//-------------------------------------------------------------------------------
// Logic
//-------------------------------------------------------------------------------

always_ff @(posedge tck, negedge trst_n) begin
    if (~trst_n) begin
        tck_divpos      <= 1'b0;
    end else begin
        tck_divpos      <= ~tck_divpos;
    end
end

always_ff @(negedge tck, negedge trst_n) begin
    if (~trst_n) begin
        tck_divneg      <= 1'b0;
    end else begin
        tck_divneg      <= ~tck_divneg;
    end
end

always_ff @(posedge clk, negedge sys_rst_n) begin
    if (~sys_rst_n) begin
        tck_divpos_sync <= 4'd0;
        tck_divneg_sync <= 4'd0;
    end else begin
        tck_divpos_sync <= {tck_divpos_sync[2:0], tck_divpos};
        tck_divneg_sync <= {tck_divneg_sync[2:0], tck_divneg};
    end
end

assign tck_rise_load  = tck_divpos_sync[2] ^ tck_divpos_sync[1];
assign tck_rise_reset = tck_divpos_sync[3] ^ tck_divpos_sync[2];
assign tck_fall_load  = tck_divneg_sync[2] ^ tck_divneg_sync[1];
assign tck_fall_reset = tck_divneg_sync[3] ^ tck_divneg_sync[2];

always_ff @(posedge clk, negedge sys_rst_n) begin
    if (~sys_rst_n) begin
            dap_ch_update_core  <= '0;
    end else begin
        if  (tck_fall_load) begin
            dap_ch_update_core  <= dap_ch_update;
        end else if (tck_fall_reset) begin
            dap_ch_update_core  <= '0;
        end
    end
end

always_ff @(negedge tck, negedge trst_n) begin
    if (~trst_n) begin
        dap_ch_capture_sync[0]  <= '0;
        dap_ch_shift_sync[0]    <= '0;
    end else begin
        dap_ch_capture_sync[0]  <= dap_ch_capture;
        dap_ch_shift_sync[0]    <= dap_ch_shift;
    end
end

always_ff @(posedge clk, negedge sys_rst_n) begin
    if (~sys_rst_n) begin
        dap_ch_capture_sync[2:1] <= '0;
        dap_ch_shift_sync[2:1]   <= '0;
    end else begin
        dap_ch_capture_sync[2:1] <= {dap_ch_capture_sync[1], dap_ch_capture_sync[0]};
        dap_ch_shift_sync[2:1]   <= {dap_ch_shift_sync[1], dap_ch_shift_sync[0]};
    end
end

always_ff @(posedge clk, negedge sys_rst_n) begin
    if (~sys_rst_n) begin
        dap_ch_tdi_sync         <= '0;
    end else begin
        dap_ch_tdi_sync         <= {dap_ch_tdi_sync[1:0], dap_ch_tdi};
    end
end

always_ff @(posedge clk, negedge async_rst_n) begin
    if (~async_rst_n) begin
        sys_rst_ctrl_sync       <= '0;
        sys_rst_ctrl_core       <= 1'b0;
    end else begin
        sys_rst_ctrl_sync       <= {sys_rst_ctrl_sync[1:0], sys_rst_ctrl};
        sys_rst_ctrl_core       <= sys_rst_ctrl_sync[2];
    end
end

always_ff @(posedge clk, negedge sys_rst_n) begin
    if (~sys_rst_n) begin
            dap_ch_capture_core <= '0;
            dap_ch_shift_core   <= '0;
            dap_ch_tdi_core     <= '0;
    end else begin
        if (tck_rise_load) begin
            dap_ch_capture_core <= dap_ch_capture_sync[2];
            dap_ch_shift_core   <= dap_ch_shift_sync[2];
            dap_ch_tdi_core     <= dap_ch_tdi_sync[2];
        end else if (tck_rise_reset) begin
            dap_ch_capture_core <= '0;
            dap_ch_shift_core   <= '0;
            dap_ch_tdi_core     <= '0;
        end
    end
end

always_ff @(posedge clk, negedge sys_rst_n) begin
    if (~sys_rst_n) begin
            dap_ch_sel_core     <= '0;
            dap_ch_id_core      <= '0;
    end else begin
        if (tck_rise_load) begin
            dap_ch_sel_core     <= dap_ch_sel;
            dap_ch_id_core      <= dap_ch_id;
        end
    end
end

assign dap_ch_tdo = dap_ch_tdo_core;

always_ff @(posedge tck, negedge trst_n) begin
    if (~trst_n) begin
        sys_rst_sts_core_sync   <= '0;
    end
    else begin
        sys_rst_sts_core_sync   <= {sys_rst_sts_core_sync[0], sys_rst_sts_core};
    end
end

assign sys_rst_sts = sys_rst_sts_core_sync[1];

endmodule : scr1_tapc_synchronizer

`endif // SCR1_DBGC_EN