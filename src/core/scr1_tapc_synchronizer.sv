/// Copyright by Syntacore LLC © 2016-2020. See LICENSE for details
/// @file       <scr1_tapc_synchronizer.sv>
/// @brief      TAPC clock domain crossing synchronizer
///

`include "scr1_arch_description.svh"

`ifdef SCR1_DBG_EN
`include "scr1_tapc.svh"
`include "scr1_dm.svh"

module scr1_tapc_synchronizer (
    // System common signals
    input   logic                                   pwrup_rst_n,                // Power-Up Reset
    input   logic                                   dm_rst_n,                   // Debug Module Reset
    input   logic                                   clk,                        // System Clock (SysCLK)

    // JTAG common signals
    input   logic                                   tapc_trst_n,                // JTAG Test Reset (TRSTn)
    input   logic                                   tapc_tck,                   // JTAG Test Clock (TCK)


    // DMI/SCU scan-chains
    input  logic                                    tapc2tapcsync_scu_ch_sel_i, // SCU Chain Select input  (TCK domain)
    output logic                                    tapcsync2scu_ch_sel_o,      // SCU Chain Select output (SysCLK domain)
    input  logic                                    tapc2tapcsync_dmi_ch_sel_i, // DMI Chain Select input  (TCK domain)
    output logic                                    tapcsync2dmi_ch_sel_o,      // DMI Chain Select output (SysCLK domain)

    input  logic [SCR1_DBG_DMI_CH_ID_WIDTH-1:0]     tapc2tapcsync_ch_id_i,      // DMI/SCU Chain Identifier input  (TCK domain)
    output logic [SCR1_DBG_DMI_CH_ID_WIDTH-1:0]     tapcsync2core_ch_id_o,      // DMI/SCU Chain Identifier output (SysCLK domain)

    input  logic                                    tapc2tapcsync_ch_capture_i, // DMI/SCU Chain Capture input  (TCK domain)
    output logic                                    tapcsync2core_ch_capture_o, // DMI/SCU Chain Capture output (SysCLK domain)

    input  logic                                    tapc2tapcsync_ch_shift_i,   // DMI/SCU Chain Shift input  (TCK domain)
    output logic                                    tapcsync2core_ch_shift_o,   // DMI/SCU Chain Shift output (SysCLK domain)

    input  logic                                    tapc2tapcsync_ch_update_i,  // DMI/SCU Chain Update input  (TCK domain)
    output logic                                    tapcsync2core_ch_update_o,  // DMI/SCU Chain Update output (SysCLK domain)

    input  logic                                    tapc2tapcsync_ch_tdi_i,     // DMI/SCU Chain TDI input  (TCK domain)
    output logic                                    tapcsync2core_ch_tdi_o,     // DMI/SCU Chain TDI output (SysCLK domain)

    output logic                                    tapc2tapcsync_ch_tdo_i,     // DMI/SCU Chain TDO output (TCK domain)
    input  logic                                    tapcsync2core_ch_tdo_o      // DMI/SCU Chain TDO input  (SysCLK domain)
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

always_ff @(posedge tapc_tck, negedge tapc_trst_n) begin
    if (~tapc_trst_n) begin
        tck_divpos      <= 1'b0;
    end else begin
        tck_divpos      <= ~tck_divpos;
    end
end

always_ff @(negedge tapc_tck, negedge tapc_trst_n) begin
    if (~tapc_trst_n) begin
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
            tapcsync2core_ch_update_o   <= '0;
    end else begin
        if  (tck_fall_load) begin
            tapcsync2core_ch_update_o   <= tapc2tapcsync_ch_update_i;
        end else if (tck_fall_reset) begin
            tapcsync2core_ch_update_o   <= '0;
        end
    end
end

always_ff @(negedge tapc_tck, negedge tapc_trst_n) begin
    if (~tapc_trst_n) begin
        dmi_ch_capture_sync[0] <= '0;
        dmi_ch_shift_sync[0]   <= '0;
    end else begin
        dmi_ch_capture_sync[0] <= tapc2tapcsync_ch_capture_i;
        dmi_ch_shift_sync[0]   <= tapc2tapcsync_ch_shift_i;
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
        dmi_ch_tdi_sync     <= {dmi_ch_tdi_sync[1:0], tapc2tapcsync_ch_tdi_i};
    end
end

always_ff @(posedge clk, negedge pwrup_rst_n) begin
    if (~pwrup_rst_n) begin
            tapcsync2core_ch_capture_o <= '0;
            tapcsync2core_ch_shift_o   <= '0;
            tapcsync2core_ch_tdi_o     <= '0;
    end else begin
        if (tck_rise_load) begin
            tapcsync2core_ch_capture_o <= dmi_ch_capture_sync[2];
            tapcsync2core_ch_shift_o   <= dmi_ch_shift_sync[2];
            tapcsync2core_ch_tdi_o     <= dmi_ch_tdi_sync[2];
        end else if (tck_rise_reset) begin
            tapcsync2core_ch_capture_o <= '0;
            tapcsync2core_ch_shift_o   <= '0;
            tapcsync2core_ch_tdi_o     <= '0;
        end
    end
end

always_ff @(posedge clk, negedge dm_rst_n) begin
    if (~dm_rst_n) begin
            tapcsync2dmi_ch_sel_o     <= '0;
            tapcsync2core_ch_id_o      <= '0;
    end else begin
        if (tck_rise_load) begin
            tapcsync2dmi_ch_sel_o     <= tapc2tapcsync_dmi_ch_sel_i;
            tapcsync2core_ch_id_o      <= tapc2tapcsync_ch_id_i;
        end
    end
end

always_ff @(posedge clk, negedge pwrup_rst_n) begin
    if (~pwrup_rst_n) begin
            tapcsync2scu_ch_sel_o     <= '0;
    end else begin
        if (tck_rise_load) begin
            tapcsync2scu_ch_sel_o     <= tapc2tapcsync_scu_ch_sel_i;
        end
    end
end

assign tapc2tapcsync_ch_tdo_i = tapcsync2core_ch_tdo_o;

endmodule : scr1_tapc_synchronizer

`endif // SCR1_DBG_EN
