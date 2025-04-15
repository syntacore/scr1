/// Copyright by Syntacore LLC © 2016-2020. See LICENSE for details
/// @file       <scr1_dp_memory.sv>
/// @brief      Dual-port synchronous memory with byte enable inputs
///

`include "scr1_arch_description.svh"

`ifdef SCR1_TCM_EN
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
    input   logic [$clog2(SCR1_SIZE)-1:2]   addra,
    output  logic [SCR1_WIDTH-1:0]          qa,
    // Port B
    input   logic                           renb,
    input   logic                           wenb,
    input   logic [SCR1_NBYTES-1:0]         webb,
    input   logic [$clog2(SCR1_SIZE)-1:2]   addrb,
    input   logic [SCR1_WIDTH-1:0]          datab,
    output  logic [SCR1_WIDTH-1:0]          qb
);

`ifdef SCR1_TRGT_FPGA_INTEL
//-------------------------------------------------------------------------------
// Local signal declaration
//-------------------------------------------------------------------------------
 `ifdef SCR1_TRGT_FPGA_INTEL_MAX10
(* ramstyle = "M9K" *)    logic [SCR1_NBYTES-1:0][7:0]  memory_array  [0:(SCR1_SIZE/SCR1_NBYTES)-1];
 `elsif SCR1_TRGT_FPGA_INTEL_ARRIAV
(* ramstyle = "M10K" *)   logic [SCR1_NBYTES-1:0][7:0]  memory_array  [0:(SCR1_SIZE/SCR1_NBYTES)-1];
 `endif
logic [3:0] wenbb;
//-------------------------------------------------------------------------------
// Port B memory behavioral description
//-------------------------------------------------------------------------------
assign wenbb = {4{wenb}} & webb;
always_ff @(posedge clk) begin
    if (wenb) begin
        if (wenbb[0]) begin
            memory_array[addrb][0] <= datab[0+:8];
        end
        if (wenbb[1]) begin
            memory_array[addrb][1] <= datab[8+:8];
        end
        if (wenbb[2]) begin
            memory_array[addrb][2] <= datab[16+:8];
        end
        if (wenbb[3]) begin
            memory_array[addrb][3] <= datab[24+:8];
        end
    end
    qb <= memory_array[addrb];
end
//-------------------------------------------------------------------------------
// Port A memory behavioral description
//-------------------------------------------------------------------------------
always_ff @(posedge clk) begin
    qa <= memory_array[addra];
end

`elsif SCR1_TRGT_FPGA_GOWIN

`include "gowin_dpb.v"
localparam int unsigned RAM_SIZE_WORDS = SCR1_SIZE/SCR1_NBYTES;
logic [3:0] wenbb;
assign wenbb = {4{wenb}} & webb;

logic [7:0] douta1;
logic [7:0] douta2;
logic [7:0] douta3;
logic [7:0] douta4;

logic [7:0] doutb1;
logic [7:0] doutb2;
logic [7:0] doutb3;
logic [7:0] doutb4;

assign qa = {douta4, douta3, douta2, douta1};
assign qb = {doutb4, doutb3, doutb2, doutb1};

Gowin_DPB dpb1(
        .douta(douta1), //output [7:0] douta
        .doutb(doutb1), //output [7:0] doutb
        .clka(clk), //input clka
        .ocea(), //input ocea
        .cea('1), //input cea
        .reseta(), //input reseta
        .wrea(), //input wrea
        .clkb(clk), //input clkb
        .oceb(), //input oceb
        .ceb('1), //input ceb
        .resetb(), //input resetb
        .wreb(wenbb[0]), //input wreb
        .ada(addra), //input [15:0] ada
        .dina(), //input [7:0] dina
        .adb(addrb), //input [15:0] adb
        .dinb(datab[0+:8]) //input [7:0] dinb
    );

Gowin_DPB dpb2(
        .douta(douta2), //output [7:0] douta
        .doutb(doutb2), //output [7:0] doutb
        .clka(clk), //input clka
        .ocea(), //input ocea
        .cea('1), //input cea
        .reseta(), //input reseta
        .wrea(), //input wrea
        .clkb(clk), //input clkb
        .oceb(), //input oceb
        .ceb('1), //input ceb
        .resetb(), //input resetb
        .wreb(wenbb[1]), //input wreb
        .ada(addra), //input [15:0] ada
        .dina(), //input [7:0] dina
        .adb(addrb), //input [15:0] adb
        .dinb(datab[8+:8]) //input [7:0] dinb
    );

Gowin_DPB dpb3(
        .douta(douta3), //output [7:0] douta
        .doutb(doutb3), //output [7:0] doutb
        .clka(clk), //input clka
        .ocea(), //input ocea
        .cea('1), //input cea
        .reseta(), //input reseta
        .wrea(), //input wrea
        .clkb(clk), //input clkb
        .oceb(), //input oceb
        .ceb('1), //input ceb
        .resetb(), //input resetb
        .wreb(wenbb[2]), //input wreb
        .ada(addra), //input [15:0] ada
        .dina(), //input [7:0] dina
        .adb(addrb), //input [15:0] adb
        .dinb(datab[16+:8]) //input [7:0] dinb
    );

Gowin_DPB dpb4(
        .douta(douta4), //output [7:0] douta
        .doutb(doutb4), //output [7:0] doutb
        .clka(clk), //input clka
        .ocea(), //input ocea
        .cea('1), //input cea
        .reseta(), //input reseta
        .wrea(), //input wrea
        .clkb(clk), //input clkb
        .oceb(), //input oceb
        .ceb('1), //input ceb
        .resetb(), //input resetb
        .wreb(wenbb[3]), //input wreb
        .ada(addra), //input [15:0] ada
        .dina(), //input [7:0] dina
        .adb(addrb), //input [15:0] adb
        .dinb(datab[24+:8]) //input [7:0] dinb
    );

`else // SCR1_TRGT_FPGA_INTEL

// CASE: OTHERS - SCR1_TRGT_FPGA_XILINX, SIMULATION, ASIC etc

localparam int unsigned RAM_SIZE_WORDS = SCR1_SIZE/SCR1_NBYTES;

//-------------------------------------------------------------------------------
// Local signal declaration
//-------------------------------------------------------------------------------
 `ifdef SCR1_TRGT_FPGA_XILINX
(* ram_style = "block" *)  logic  [SCR1_WIDTH-1:0]  ram_block  [RAM_SIZE_WORDS-1:0];
 `else  // ASIC or SIMULATION
logic  [SCR1_WIDTH-1:0]  ram_block  [RAM_SIZE_WORDS-1:0];
 `endif
//-------------------------------------------------------------------------------
// Port A memory behavioral description
//-------------------------------------------------------------------------------
always_ff @(posedge clk) begin
    if (rena) begin
        qa <= ram_block[addra];
    end
end

//-------------------------------------------------------------------------------
// Port B memory behavioral description
//-------------------------------------------------------------------------------
always_ff @(posedge clk) begin
    if (wenb) begin
        for (int i=0; i<SCR1_NBYTES; i++) begin
            if (webb[i]) begin
                ram_block[addrb][i*8 +: 8] <= datab[i*8 +: 8];
            end
        end
    end
    if (renb) begin
        qb <= ram_block[addrb];
    end
end

`endif // SCR1_TRGT_FPGA_INTEL

endmodule : scr1_dp_memory

`endif // SCR1_TCM_EN
