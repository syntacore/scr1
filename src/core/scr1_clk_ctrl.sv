/// Copyright by Syntacore LLC © 2016-2021. See LICENSE for details
/// @file       <scr1_clk_ctrl.sv>
/// @brief      SCR1 clock control
///

`include "scr1_arch_description.svh"

`ifdef SCR1_CLKCTRL_EN
module scr1_clk_ctrl (
    input   logic   clk,                            // Clock control module clock
    input   logic   rst_n,                          // Clock control module reset
    input   logic   test_mode,                      // DFT Test Mode
    input   logic   test_rst_n,                     // DFT Test reset

    input   logic   pipe2clkctl_sleep_req_i,        // CLK disable request from pipe
    input   logic   pipe2clkctl_wake_req_i,         // CLK enable request from pipe

    output  logic   clkctl2pipe_clk_alw_on_o,       // Not gated pipe CLK
    output  logic   clkctl2pipe_clk_o,              // Gated pipe
    output  logic   clkctl2pipe_clk_en_o,           // CLK enabled flag
    output  logic   clkctl2pipe_clk_dbgc_o          // CLK for pipe debug subsystem
);

logic ctrl_rst_n;

assign clkctl2pipe_clk_alw_on_o = clk;
assign clkctl2pipe_clk_dbgc_o   = clk;
assign ctrl_rst_n   = (test_mode) ? test_rst_n : rst_n;

always_ff @(posedge clk, negedge ctrl_rst_n) begin
    if (~ctrl_rst_n) begin
        clkctl2pipe_clk_en_o <= 1'b1;
    end else begin
        if (clkctl2pipe_clk_en_o) begin
            if (pipe2clkctl_sleep_req_i & ~pipe2clkctl_wake_req_i) begin
                clkctl2pipe_clk_en_o <= 1'b0;
            end
        end else begin // ~clkctl2pipe_clk_en_o
            if (pipe2clkctl_wake_req_i) begin
                clkctl2pipe_clk_en_o <= 1'b1;
            end
        end // pipeline
    end
end

scr1_cg i_scr1_cg_pipe (
    .clk        (clk                 ),
    .clk_en     (clkctl2pipe_clk_en_o),
    .test_mode  (test_mode           ),
    .clk_out    (clkctl2pipe_clk_o   )
);

endmodule : scr1_clk_ctrl

`endif // SCR1_CLKCTRL_EN
