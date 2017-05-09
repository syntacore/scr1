/// Copyright by Syntacore LLC © 2016, 2017. See LICENSE for details
/// @file       <scr1_dp_memory.sv>
/// @brief      Dual-port synchronous memory with byte enable inputs
///
`include "scr1_arch_description.svh"

module scr1_dp_memory
#(
    parameter SCR1_WIDTH  = 32,
    parameter SCR1_SIZE   = `SCR1_IMEM_AWIDTH'h00010000,
    parameter SCR1_NBYTES = SCR1_WIDTH / 8
)
(
    input   logic                           clk,
    // Port A
    input   logic                           rena,
    input   logic [$clog2(SCR1_SIZE)-1:0]   addra,
    output  logic [SCR1_WIDTH-1:0]          qa,
    // Port B
    input   logic                           renb,
    input   logic                           wenb,
    input   logic [SCR1_NBYTES-1:0]         webb,
    input   logic [$clog2(SCR1_SIZE)-1:0]   addrb,
    input   logic [SCR1_WIDTH-1:0]          datab,
    output  logic [SCR1_WIDTH-1:0]          qb
);

//-------------------------------------------------------------------------------
// Local signal declaration
//-------------------------------------------------------------------------------
logic [SCR1_NBYTES-1:0][7:0] memory_array [0:(SCR1_SIZE/SCR1_NBYTES)-1];
logic [3:0] wenbb;
//-------------------------------------------------------------------------------
// Port B memory behavioral description
//-------------------------------------------------------------------------------
assign wenbb = {4{wenb}} & webb;
always_ff @(posedge clk) begin
    if (wenb) begin
        if (wenbb[0]) begin
            memory_array[addrb[$clog2(SCR1_SIZE)-1:2]][0] <= datab[0+:8];
        end
        if (wenbb[1]) begin
            memory_array[addrb[$clog2(SCR1_SIZE)-1:2]][1] <= datab[8+:8];
        end
        if (wenbb[2]) begin
            memory_array[addrb[$clog2(SCR1_SIZE)-1:2]][2] <= datab[16+:8];
        end
        if (wenbb[3]) begin
            memory_array[addrb[$clog2(SCR1_SIZE)-1:2]][3] <= datab[24+:8];
        end
    end
    if (renb) begin
        qb <= memory_array[addrb[$clog2(SCR1_SIZE)-1:2]];
    end
end
//-------------------------------------------------------------------------------
// Port A memory behavioral description
//-------------------------------------------------------------------------------
always_ff @(posedge clk) begin
    if (rena) begin
        qa <= memory_array[addra[$clog2(SCR1_SIZE)-1:2]];
    end
end

endmodule : scr1_dp_memory