/// Copyright by Syntacore LLC © 2016-2018. See LICENSE for details
/// @file       <scr1_tapc_data_reg.sv>
/// @brief      TAPC data register. Parameterized implementation of JTAG TAPC's Data Register (DR)
///

`include "scr1_arch_description.svh"

`ifdef SCR1_DBGC_EN
module scr1_tapc_data_reg #(
    parameter   int unsigned            SCR1_WIDTH       = 8,   // Register width, bits
    parameter   logic [SCR1_WIDTH-1:0]  SCR1_RESET_VALUE = '0   // Register's value after reset
) (
    input  logic                    clk,            // Clock
    input  logic                    rst_n,          // Async reset
    input  logic                    rst_n_sync,     // Sync reset
                                                    // TAP FSM's control signals:
    input  logic                    fsm_dr_select,  //   - for this DR selection (operation enabling);
    input  logic                    fsm_dr_capture, //   - to capture parallel input's data into shift register;
    input  logic                    fsm_dr_shift,   //   - to enable data shifting;
    input  logic                    fsm_dr_update,  //   - to update shadow register with the shift register's data.
                                                    // Inputs:
    input  logic                    din_serial,     //   - serial (shift_reg[msb/SCR1_WIDTH]);
    input  logic [SCR1_WIDTH-1:0]   din_parallel,   //   - parallel (shift register's input).
                                                    // Outputs:
    output logic                    dout_serial,    //   - serial (shift_reg[0]);
    output logic [SCR1_WIDTH-1:0]   dout_parallel   //   - parallel (shadow register's output).
);

//-------------------------------------------------------------------------------
// Local signals declaration
//-------------------------------------------------------------------------------
logic [SCR1_WIDTH-1:0]   shift_reg;

//-------------------------------------------------------------------------------
// Shift register
//-------------------------------------------------------------------------------
generate
    if (SCR1_WIDTH > 1)
    begin : dr_shift_reg

        always_ff @(posedge clk, negedge rst_n) begin
            if (~rst_n) begin
                shift_reg <= SCR1_RESET_VALUE;
            end
            else if (~rst_n_sync) begin
                shift_reg <= SCR1_RESET_VALUE;
            end
            else if (fsm_dr_select & fsm_dr_capture) begin
                shift_reg <= din_parallel;
            end
            else if (fsm_dr_select & fsm_dr_shift) begin
                shift_reg <= {din_serial, shift_reg[SCR1_WIDTH-1:1]};
            end
        end

    end
    else begin : dr_shift_reg

        always_ff @(posedge clk, negedge rst_n) begin
            if (~rst_n) begin
                shift_reg <= SCR1_RESET_VALUE;
            end
            else if (~rst_n_sync) begin
                shift_reg <= SCR1_RESET_VALUE;
            end
            else if (fsm_dr_select & fsm_dr_capture) begin
                shift_reg <= din_parallel;
            end
            else if (fsm_dr_select & fsm_dr_shift) begin
                shift_reg <= din_serial;
            end
        end

    end
endgenerate

//-------------------------------------------------------------------------------
// Shadow  register
//-------------------------------------------------------------------------------
always_ff @(negedge clk, negedge rst_n) begin
    if (~rst_n) begin
        dout_parallel <= SCR1_RESET_VALUE;
    end
    else if (~rst_n_sync) begin
        dout_parallel <= SCR1_RESET_VALUE;
    end
    else if (fsm_dr_select & fsm_dr_update) begin
        dout_parallel <= shift_reg;
    end
end

//-------------------------------------------------------------------------------
// Serial output
//-------------------------------------------------------------------------------
assign dout_serial = shift_reg[0];


`ifdef SCR1_SIM_ENV
//-------------------------------------------------------------------------------
// Assertion
//-------------------------------------------------------------------------------

// X checks
SCR1_SVA_TAPC_DATAREG_XCHECK : assert property (
    @(negedge clk) disable iff (~rst_n)
    !$isunknown({
        rst_n_sync,
        fsm_dr_select,
        fsm_dr_capture,
        fsm_dr_shift,
        din_serial,
        din_parallel
    })
) else begin
    $error("TAPC Data Reg error: unknown values");
end

SCR1_SVA_TAPC_DATAREG_XCHECK_NEGCLK : assert property (
    @(negedge clk) disable iff (~rst_n)
    !$isunknown({
        rst_n_sync,
        fsm_dr_select,
        fsm_dr_update
    })
) else begin
    $error("TAPC Data Reg @negedge error: unknown values");
end

`endif // SCR1_SIM_ENV

endmodule : scr1_tapc_data_reg

`endif // SCR1_DBGC_EN