/// Copyright by Syntacore LLC © 2016, 2017. See LICENSE for details
/// @file       <scr1_dp_memory.sv>
/// @brief      Dual-port synchronous memory with byte enable inputs
///

`include "scr1_arch_description.svh"

module scr1_dp_memory
#(
    parameter SCR1_WIDTH    = 32,
    parameter SCR1_SIZE     = `SCR1_IMEM_AWIDTH'h00010000,
    parameter SCR1_NBYTES   = SCR1_WIDTH / 8
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

localparam int unsigned RAM_SIZE_WORDS = SCR1_SIZE/SCR1_NBYTES;

//-------------------------------------------------------------------------------
// Local signal declaration
//-------------------------------------------------------------------------------
reg [SCR1_WIDTH-1:0]                ram_block [RAM_SIZE_WORDS-1:0];
integer                             i;
reg [$clog2(RAM_SIZE_WORDS)-1:0]    addra_word;
reg [$clog2(RAM_SIZE_WORDS)-1:0]    addrb_word;

//-------------------------------------------------------------------------------
// Port A memory behavioral description
//-------------------------------------------------------------------------------
assign addra_word = addra[$clog2(SCR1_SIZE)-1 : $clog2(SCR1_SIZE)-$clog2(RAM_SIZE_WORDS)];
always @(posedge clk) begin
    if (rena) begin
        qa <= ram_block[addra_word];
    end
end

//-------------------------------------------------------------------------------
// Port B memory behavioral description
//-------------------------------------------------------------------------------
assign addrb_word = addrb[$clog2(SCR1_SIZE)-1 : $clog2(SCR1_SIZE)-$clog2(RAM_SIZE_WORDS)];
always @(posedge clk) begin
    if (wenb) begin
        for (i=0; i<SCR1_NBYTES; i=i+1) begin
            if (webb[i]) begin
                ram_block[addrb_word][i*8 +: 8] <= datab[i*8 +: 8];
            end
        end
    end
    if (renb) begin
        qb <= ram_block[addrb_word];
    end
end

endmodule : scr1_dp_memory