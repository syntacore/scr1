/// Copyright by Syntacore LLC © 2016-2019. See LICENSE for details
/// @file       <scr1_dmi.sv>
/// @brief      Debug Module Interface (DMI)
///

`include "scr1_arch_description.svh"

`ifdef SCR1_DBGC_EN
`include "scr1_dm.svh"

module scr1_dmi (
    // System
    input  logic                                    rst_n,          // DMI unit reset
    input  logic                                    clk,            // DMI unit clock

    // TAP interface
    input  logic                                    dtm_ch_sel,     // Debug Transport Module Chain Select
    input  logic [SCR1_DBG_DMI_CH_ID_WIDTH-1:0]     dtm_ch_id,      // Debug Transport Module Chain ID
    input  logic                                    dtm_ch_capture, // Debug Transport Module Chain Capture
    input  logic                                    dtm_ch_shift,   // Debug Transport Module Chain Shift
    input  logic                                    dtm_ch_update,  // Debug Transport Module Chain Update
    input  logic                                    dtm_ch_tdi,     // Debug Transport Module Chain TDI
    output logic                                    dtm_ch_tdo,     // Debug Transport Module Chain TDO

    // DM interface
    input logic                                     dmi_resp,       // DMI response
    input logic [SCR1_DBG_DMI_DATA_WIDTH-1:0]       dmi_rdata,      // DMI read data

    output logic                                    dmi_req,        // DMI request
    output logic                                    dmi_wr,         // DMI write
    output logic [SCR1_DBG_DMI_ADDR_WIDTH-1:0]      dmi_addr,       // DMI address
    output logic [SCR1_DBG_DMI_DATA_WIDTH-1:0]      dmi_wdata       // DMI write data

);

// DTMS
localparam                                          DTMCS_RESERVEDB_HI = 5'd31;
localparam                                          DTMCS_RESERVEDB_LO = 5'd18;
localparam                                          DTMCS_DMIHARDRESET = 5'd17;
localparam                                          DTMCS_DMIRESET     = 5'd16;
localparam                                          DTMCS_RESERVEDA    = 5'd15;
localparam                                          DTMCS_IDLE_HI      = 5'd14;
localparam                                          DTMCS_IDLE_LO      = 5'd12;
localparam                                          DTMCS_DMISTAT_HI   = 5'd11;
localparam                                          DTMCS_DMISTAT_LO   = 5'd10;
localparam                                          DTMCS_ABITS_HI     = 5'd9;
localparam                                          DTMCS_ABITS_LO     = 5'd4;
localparam                                          DTMCS_VERSION_HI   = 5'd3;
localparam                                          DTMCS_VERSION_LO   = 5'd0;
logic                                               dtmcs_dmihardreset_cmb;
logic                                               dtmcs_dmireset_cmb;

// DMI
localparam                                          DMI_OP_LO   = 5'd0;
localparam                                          DMI_OP_HI   = DMI_OP_LO + SCR1_DBG_DMI_OP_WIDTH - 1;
localparam                                          DMI_DATA_LO = DMI_OP_HI + 1;
localparam                                          DMI_DATA_HI = DMI_DATA_LO + SCR1_DBG_DMI_DATA_WIDTH - 1;
localparam                                          DMI_ADDR_LO = DMI_DATA_HI + 1;
localparam                                          DMI_ADDR_HI = DMI_ADDR_LO + SCR1_DBG_DMI_ADDR_WIDTH - 1;

logic [SCR1_DBG_DMI_DATA_WIDTH-1:0]                 dmi_rdata_ff;

// TAP
logic [SCR1_DBG_DMI_DR_DMI_ACCESS_WIDTH-1:0]        tap_dr_shift_cmb;
logic [SCR1_DBG_DMI_DR_DMI_ACCESS_WIDTH-1:0]        tap_dr_rdata_cmb;
logic [SCR1_DBG_DMI_DR_DMI_ACCESS_WIDTH-1:0]        tap_dr_ff;

// Clock enable
logic                                               clk_en_dmi_rdata_cmb;
logic                                               clk_en_tap_dr_cmb;

// TAP interface
// -------------

always_comb dtm_ch_tdo = tap_dr_ff[0];

always_comb begin
    tap_dr_rdata_cmb = 1'b0;
    tap_dr_shift_cmb = 1'b0;

    if( dtm_ch_id == 1'd1 ) begin
        tap_dr_rdata_cmb[ DTMCS_RESERVEDB_HI : DTMCS_RESERVEDB_LO ] = 1'b0;
        tap_dr_rdata_cmb[ DTMCS_DMIHARDRESET ]                      = 1'b0;
        tap_dr_rdata_cmb[ DTMCS_DMIRESET ]                          = 1'b0;
        tap_dr_rdata_cmb[ DTMCS_RESERVEDA ]                         = 1'b0;
        tap_dr_rdata_cmb[ DTMCS_IDLE_HI    : DTMCS_IDLE_LO ]        = 1'b0;
        // Status of dmi operation is always success because of current DM implementation
        tap_dr_rdata_cmb[ DTMCS_DMISTAT_HI : DTMCS_DMISTAT_LO ]     = 1'b0;
        tap_dr_rdata_cmb[ DTMCS_ABITS_HI   : DTMCS_ABITS_LO ]       = SCR1_DBG_DMI_ADDR_WIDTH;
        tap_dr_rdata_cmb[ DTMCS_VERSION_LO : DTMCS_VERSION_LO ]     = 1'b1;

        tap_dr_shift_cmb =  { dtm_ch_tdi,
                              tap_dr_ff[SCR1_DBG_DMI_DR_DTMCS_WIDTH-1:1] };
    end else begin
        tap_dr_rdata_cmb[ DMI_ADDR_HI : DMI_ADDR_LO ] = 1'b0;
        tap_dr_rdata_cmb[ DMI_DATA_HI : DMI_DATA_LO ] = dmi_rdata_ff;
        // Status of dmi operation is always success because of current DM implementation
        tap_dr_rdata_cmb[ DMI_OP_HI   : DMI_OP_LO ]   = 1'b0;

        tap_dr_shift_cmb =  { dtm_ch_tdi,
                              tap_dr_ff[SCR1_DBG_DMI_DR_DMI_ACCESS_WIDTH-1:1] };
    end
end

// Clock enable logic
always_comb begin
    clk_en_tap_dr_cmb = dtm_ch_capture | dtm_ch_shift;
end

// TAP data register
always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        tap_dr_ff <= '0;
    end
    else begin
        if( clk_en_tap_dr_cmb ) begin
            if( dtm_ch_capture ) begin
                tap_dr_ff <= tap_dr_rdata_cmb;
            end else if( dtm_ch_shift ) begin
                tap_dr_ff <= tap_dr_shift_cmb;
            end
        end
    end
end

// DM interface
// ------------

always_comb begin
    dmi_req           = 1'b0;
    dmi_wr            = 1'b0;
    dmi_addr          = 1'b0;
    dmi_wdata         = 1'b0;
    
    if( dtm_ch_update & dtm_ch_sel  &  dtm_ch_id == 2'd2 ) begin
        dmi_req           = tap_dr_ff[ DMI_OP_HI   : DMI_OP_LO ] != 2'b00;
        dmi_wr            = tap_dr_ff[ DMI_OP_HI   : DMI_OP_LO ] == 2'b10;
        dmi_addr          = tap_dr_ff[DMI_ADDR_HI : DMI_ADDR_LO];
        dmi_wdata         = tap_dr_ff[DMI_DATA_HI : DMI_DATA_LO];
    end
end

// Clock enable logic
always_comb begin
    clk_en_dmi_rdata_cmb = dmi_req & dmi_resp & ~dmi_wr;
end

// DMI readed data storage
always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        dmi_rdata_ff <= '0;
    end
    else begin
        if( clk_en_dmi_rdata_cmb ) begin
            dmi_rdata_ff <= dmi_rdata;
        end
    end
end

endmodule : scr1_dmi

`endif // SCR1_DBGC_EN