/// Copyright by Syntacore LLC © 2016, 2017. See LICENSE for details
/// @file       <scr1_cg.sv>
/// @brief      SCR1 clock gate primitive
///

module scr1_cg (
    input   logic   clk,
    input   logic   clk_en,
    input   logic   test_mode,
    output  logic   clk_out
);

`ifdef SYNTHESIS
    // Instantiate library clock gate primitive here
`else   // SYNTHESIS
logic latch_en;

always_latch begin
    if (~clk) begin
        latch_en <= test_mode | clk_en;
    end
end

assign clk_out  = latch_en & clk;
`endif  // SYNTHESIS

endmodule : scr1_cg