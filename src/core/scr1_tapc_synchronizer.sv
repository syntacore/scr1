/// Copyright by Syntacore LLC © 2016-2019. See LICENSE for details
/// @file       <scr1_tapc_synchronizer.sv>
/// @brief      TAPC clock domain crossing synchronizer
///

`include "scr1_arch_description.svh"

`ifdef SCR1_DBGC_EN
`include "scr1_tapc.svh"
`include "scr1_dm.svh"

module scr1_tapc_synchronizer (
    // System common signals
    input   logic                                   pwrup_rst_n,        // Power-Up Reset
    input   logic                                   dm_rst_n,           // Debug Module Reset
    input   logic                                   clk,                // System Clock (SysCLK)
    // JTAG common signals
    input   logic                                   trst_n,             // JTAG Test Reset (TRSTn)
    input   logic                                   tck,                // JTAG Test Clock (TCK)
    // System Control/Status signals
    input  logic                                    scu_ch_sel,         // SCU Chain Select input  (TCK domain)
    output logic                                    scu_ch_sel_core,    // SCU Chain Select output (SysCLK domain)

    // DMI scan-chains
    input  logic                                    dmi_ch_sel,         // DMI Chain Select input  (TCK domain)
    output logic                                    dmi_ch_sel_core,    // DMI Chain Select output (SysCLK domain)

    input  logic [SCR1_DBG_DMI_CH_ID_WIDTH-1:0]     dmi_ch_id,          // DMI Chain Identifier input  (TCK domain)
    output logic [SCR1_DBG_DMI_CH_ID_WIDTH-1:0]     dmi_ch_id_core,     // DMI Chain Identifier output (SysCLK domain)

    input  logic                                    dmi_ch_capture,     // DMI Chain Capture input  (TCK domain)
    output logic                                    dmi_ch_capture_core,// DMI Chain Capture output (SysCLK domain)

    input  logic                                    dmi_ch_shift,       // DMI Chain Shift input  (TCK domain)
    output logic                                    dmi_ch_shift_core,  // DMI Chain Shift output (SysCLK domain)

    input  logic                                    dmi_ch_update,      // DMI Chain Update input  (TCK domain)
    output logic                                    dmi_ch_update_core, // DMI Chain Update output (SysCLK domain)

    input  logic                                    dmi_ch_tdi,         // DMI Chain TDI input  (TCK domain)
    output logic                                    dmi_ch_tdi_core,    // DMI Chain TDI output (SysCLK domain)

    output logic                                    dmi_ch_tdo,         // DMI Chain TDO output (TCK domain)
    input  logic                                    dmi_ch_tdo_core     // DMI Chain TDO input  (SysCLK domain)
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
logic [2:0]     dmi_ch_capture_sync;
logic [2:0]     dmi_ch_shift_sync;
logic [2:0]     dmi_ch_tdi_sync;

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

always_ff @(posedge clk, negedge pwrup_rst_n) begin
    if (~pwrup_rst_n) begin
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

always_ff @(posedge clk, negedge pwrup_rst_n) begin
    if (~pwrup_rst_n) begin
            dmi_ch_update_core   <= '0;
    end else begin
        if  (tck_fall_load) begin
            dmi_ch_update_core   <= dmi_ch_update;
        end else if (tck_fall_reset) begin
            dmi_ch_update_core   <= '0;
        end
    end
end

always_ff @(negedge tck, negedge trst_n) begin
    if (~trst_n) begin
        dmi_ch_capture_sync[0] <= '0;
        dmi_ch_shift_sync[0]   <= '0;
    end else begin
        dmi_ch_capture_sync[0] <= dmi_ch_capture;
        dmi_ch_shift_sync[0]   <= dmi_ch_shift;
    end
end

always_ff @(posedge clk, negedge pwrup_rst_n) begin
    if (~pwrup_rst_n) begin
        dmi_ch_capture_sync[2:1] <= '0;
        dmi_ch_shift_sync[2:1]   <= '0;
    end else begin
        dmi_ch_capture_sync[2:1] <= {dmi_ch_capture_sync[1], dmi_ch_capture_sync[0]};
        dmi_ch_shift_sync[2:1]   <= {dmi_ch_shift_sync[1], dmi_ch_shift_sync[0]};
    end
end

always_ff @(posedge clk, negedge pwrup_rst_n) begin
    if (~pwrup_rst_n) begin
        dmi_ch_tdi_sync     <= '0;
    end else begin
        dmi_ch_tdi_sync     <= {dmi_ch_tdi_sync[1:0], dmi_ch_tdi};
    end
end

always_ff @(posedge clk, negedge pwrup_rst_n) begin
    if (~pwrup_rst_n) begin
            dmi_ch_capture_core <= '0;
            dmi_ch_shift_core   <= '0;
            dmi_ch_tdi_core     <= '0;
    end else begin
        if (tck_rise_load) begin
            dmi_ch_capture_core <= dmi_ch_capture_sync[2];
            dmi_ch_shift_core   <= dmi_ch_shift_sync[2];
            dmi_ch_tdi_core     <= dmi_ch_tdi_sync[2];
        end else if (tck_rise_reset) begin
            dmi_ch_capture_core <= '0;
            dmi_ch_shift_core   <= '0;
            dmi_ch_tdi_core     <= '0;
        end
    end
end

always_ff @(posedge clk, negedge dm_rst_n) begin
    if (~dm_rst_n) begin
            dmi_ch_sel_core     <= '0;
            dmi_ch_id_core      <= '0;
    end else begin
        if (tck_rise_load) begin
            dmi_ch_sel_core     <= dmi_ch_sel;
            dmi_ch_id_core      <= dmi_ch_id;
        end
    end
end

always_ff @(posedge clk, negedge pwrup_rst_n) begin
    if (~pwrup_rst_n) begin
            scu_ch_sel_core     <= '0;
    end else begin
        if (tck_rise_load) begin
            scu_ch_sel_core     <= scu_ch_sel;
        end
    end
end

assign dmi_ch_tdo = dmi_ch_tdo_core;

endmodule : scr1_tapc_synchronizer

`endif // SCR1_DBGC_EN