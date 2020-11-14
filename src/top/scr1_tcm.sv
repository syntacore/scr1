/// Copyright by Syntacore LLC © 2016-2020. See LICENSE for details
/// @file       <scr1_tcm.sv>
/// @brief      Tightly-Coupled Memory (TCM)
///

`include "scr1_memif.svh"
`include "scr1_arch_description.svh"

`ifdef SCR1_TCM_EN
module scr1_tcm
#(
    parameter SCR1_TCM_SIZE = `SCR1_IMEM_AWIDTH'h00010000
)
(
    // Control signals
    input   logic                           clk,
    input   logic                           rst_n,

    // Core instruction interface
    output  logic                           imem_req_ack,
    input   logic                           imem_req,
    input   logic [`SCR1_IMEM_AWIDTH-1:0]   imem_addr,
    output  logic [`SCR1_IMEM_DWIDTH-1:0]   imem_rdata,
    output  type_scr1_mem_resp_e            imem_resp,

    // Core data interface
    output  logic                           dmem_req_ack,
    input   logic                           dmem_req,
    input   type_scr1_mem_cmd_e             dmem_cmd,
    input   type_scr1_mem_width_e           dmem_width,
    input   logic [`SCR1_DMEM_AWIDTH-1:0]   dmem_addr,
    input   logic [`SCR1_DMEM_DWIDTH-1:0]   dmem_wdata,
    output  logic [`SCR1_DMEM_DWIDTH-1:0]   dmem_rdata,
    output  type_scr1_mem_resp_e            dmem_resp
);

//-------------------------------------------------------------------------------
// Local signal declaration
//-------------------------------------------------------------------------------
logic                               imem_req_en;
logic                               dmem_req_en;
logic                               imem_rd;
logic                               dmem_rd;
logic                               dmem_wr;
logic [`SCR1_DMEM_DWIDTH-1:0]       dmem_writedata;
logic [`SCR1_DMEM_DWIDTH-1:0]       dmem_rdata_local;
logic [3:0]                         dmem_byteen;
logic [1:0]                         dmem_rdata_shift_reg;
//-------------------------------------------------------------------------------
// Core interface
//-------------------------------------------------------------------------------
assign imem_req_en = (imem_resp == SCR1_MEM_RESP_RDY_OK) ^ imem_req;
assign dmem_req_en = (dmem_resp == SCR1_MEM_RESP_RDY_OK) ^ dmem_req;

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        imem_resp <= SCR1_MEM_RESP_NOTRDY;
    end else if (imem_req_en) begin
        imem_resp <= imem_req ? SCR1_MEM_RESP_RDY_OK : SCR1_MEM_RESP_NOTRDY;
    end
end

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        dmem_resp <= SCR1_MEM_RESP_NOTRDY;
    end else if (dmem_req_en) begin
        dmem_resp <= dmem_req ? SCR1_MEM_RESP_RDY_OK : SCR1_MEM_RESP_NOTRDY;
    end
end

assign imem_req_ack = 1'b1;
assign dmem_req_ack = 1'b1;
//-------------------------------------------------------------------------------
// Memory data composing
//-------------------------------------------------------------------------------
assign imem_rd  = imem_req;
assign dmem_rd  = dmem_req & (dmem_cmd == SCR1_MEM_CMD_RD);
assign dmem_wr  = dmem_req & (dmem_cmd == SCR1_MEM_CMD_WR);

always_comb begin
    dmem_writedata = dmem_wdata;
    dmem_byteen    = 4'b1111;
    case ( dmem_width )
        SCR1_MEM_WIDTH_BYTE : begin
            dmem_writedata  = {(`SCR1_DMEM_DWIDTH /  8){dmem_wdata[7:0]}};
            dmem_byteen     = 4'b0001 << dmem_addr[1:0];
        end
        SCR1_MEM_WIDTH_HWORD : begin
            dmem_writedata  = {(`SCR1_DMEM_DWIDTH / 16){dmem_wdata[15:0]}};
            dmem_byteen     = 4'b0011 << {dmem_addr[1], 1'b0};
        end
        default : begin
        end
    endcase
end
//-------------------------------------------------------------------------------
// Memory instantiation
//-------------------------------------------------------------------------------
scr1_dp_memory #(
    .SCR1_WIDTH ( 32            ),
    .SCR1_SIZE  ( SCR1_TCM_SIZE )
) i_dp_memory (
    .clk    ( clk                                   ),
    // Instruction port
    // Port A
    .rena   ( imem_rd                               ),
    .addra  ( imem_addr[$clog2(SCR1_TCM_SIZE)-1:2]  ),
    .qa     ( imem_rdata                            ),
    // Data port
    // Port B
    .renb   ( dmem_rd                               ),
    .wenb   ( dmem_wr                               ),
    .webb   ( dmem_byteen                           ),
    .addrb  ( dmem_addr[$clog2(SCR1_TCM_SIZE)-1:2]  ),
    .qb     ( dmem_rdata_local                      ),
    .datab  ( dmem_writedata                        )
);
//-------------------------------------------------------------------------------
// Data memory output generation
//-------------------------------------------------------------------------------
always_ff @(posedge clk) begin
    if (dmem_rd) begin
        dmem_rdata_shift_reg <= dmem_addr[1:0];
    end
end

assign dmem_rdata = dmem_rdata_local >> ( 8 * dmem_rdata_shift_reg );

endmodule : scr1_tcm

`endif // SCR1_TCM_EN
