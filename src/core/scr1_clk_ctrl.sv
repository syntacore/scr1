/// Copyright by Syntacore LLC © 2016-2018. See LICENSE for details
/// @file       <scr1_clk_ctrl.sv>
/// @brief      SCR1 clock control
///

`include "scr1_arch_description.svh"

`ifdef SCR1_CLKCTRL_EN
module scr1_clk_ctrl (
    input   logic   clk,
    input   logic   rst_n,
    input   logic   test_mode,

    input   logic   sleep_pipe,
    input   logic   wake_pipe,

    output  logic   clkout,         // always on
    output  logic   clkout_pipe,
    output  logic   clk_pipe_en,
    output  logic   clkout_dbgc     // always on (for now)
);

assign clkout       = clk;
assign clkout_dbgc  = clk;

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        clk_pipe_en <= 1'b1;
    end else begin
        if (clk_pipe_en) begin
            if (sleep_pipe & ~wake_pipe) begin
                clk_pipe_en <= 1'b0;
            end
        end else begin // ~clk_pipe_en
            if (wake_pipe) begin
                clk_pipe_en <= 1'b1;
            end
        end // pipeline
    end
end

scr1_cg i_scr1_cg_pipe (
    .clk        (clk        ),
    .clk_en     (clk_pipe_en),
    .test_mode  (test_mode  ),
    .clk_out    (clkout_pipe)
);

endmodule : scr1_clk_ctrl

`endif // SCR1_CLKCTRL_EN