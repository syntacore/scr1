/// Copyright by Marek Pikuła, Trinamic 2019. See LICENSE for details
/// @file       <scr1_mem_pulp.sv>
/// @brief      Memory PULP bridge
///
/// Based on <scr1_dmem_ahb.sv>
///

`include "scr1_memif.svh"
`include "scr1_arch_description.svh"

module scr1_mem_pulp
#(
    parameter SCR1_ADDR_WIDTH = 32
)
(
    // Core Interface
    output  logic                       core_req_ack,
    input   logic                       core_req,
    input   type_scr1_mem_cmd_e         core_cmd,
    input   type_scr1_mem_width_e       core_width,
    input   logic [SCR1_ADDR_WIDTH-1:0] core_addr,
    input   logic [31:0]                core_wdata,
    output  logic [31:0]                core_rdata,
    output  type_scr1_mem_resp_e        core_resp,

    // PULP
    output  logic [SCR1_ADDR_WIDTH-1:0] data_addr_o,
    output  logic                       data_req_o,
    output  logic [3:0]                 data_be_o,
    input   logic [31:0]                data_rdata_i,
    output  logic                       data_we_o,
    input   logic                       data_gnt_i,
    output  logic [31:0]                data_wdata_o,
    input   logic                       data_rvalid_i,
    input   logic                       data_err_i
);

assign core_req_ack = data_gnt_i;
assign data_req_o   = core_req;
assign data_addr_o  = {core_addr[SCR1_ADDR_WIDTH-1:2], 2'b0};

always_comb begin : assign_wdata
    data_wdata_o = 'x;
    unique case (core_width)
        SCR1_MEM_WIDTH_BYTE : begin
            unique case (core_addr[1:0])
                2'b00: data_wdata_o[7:0]   = core_wdata[7:0];
                2'b01: data_wdata_o[15:8]  = core_wdata[7:0];
                2'b10: data_wdata_o[23:16] = core_wdata[7:0];
                2'b11: data_wdata_o[31:24] = core_wdata[7:0];
            endcase
        end
        SCR1_MEM_WIDTH_HWORD : begin
            unique case (core_addr[1])
                1'b0: data_wdata_o[15:0]  = core_wdata[15:0];
                1'b1: data_wdata_o[31:16] = core_wdata[15:0];
            endcase
        end
        SCR1_MEM_WIDTH_WORD : data_wdata_o = core_wdata;
        default :             data_wdata_o = 'x;
    endcase
end

always_comb begin : assign_rdata
    core_rdata = 'x;
    unique case (core_width)
        SCR1_MEM_WIDTH_BYTE : begin
            unique case (core_addr[1:0])
                2'b00 : core_rdata[7:0] = data_rdata_i[7:0];
                2'b01 : core_rdata[7:0] = data_rdata_i[15:8];
                2'b10 : core_rdata[7:0] = data_rdata_i[23:16];
                2'b11 : core_rdata[7:0] = data_rdata_i[31:24];
            endcase
        end
        SCR1_MEM_WIDTH_HWORD : begin
            unique case (core_addr[1])
                1'b0 : core_rdata[15:0] = data_rdata_i[15:0];
                1'b1 : core_rdata[15:0] = data_rdata_i[31:16];
            endcase
        end
        SCR1_MEM_WIDTH_WORD : core_rdata = data_rdata_i;
        default :             core_rdata = 'x;
    endcase
end

always_comb begin : handle_core_cmd
    unique case (core_cmd)
        SCR1_MEM_CMD_RD : data_we_o = 1'b0;
        SCR1_MEM_CMD_WR : data_we_o = 1'b1;
        default :         data_we_o = 1'bx;
    endcase
end

always_comb begin : handle_core_width
    unique case (core_width)
        SCR1_MEM_WIDTH_BYTE : begin
            unique case (core_addr[1:0])
                2'b00 : data_be_o = 4'h1;
                2'b01 : data_be_o = 4'h2;
                2'b10 : data_be_o = 4'h4;
                2'b11 : data_be_o = 4'h8;
            endcase
        end
        SCR1_MEM_WIDTH_HWORD : begin
            unique case (core_addr[1])
                1'b0 : data_be_o = 4'h3;
                1'b1 : data_be_o = 4'hc;
            endcase
        end
        SCR1_MEM_WIDTH_WORD : data_be_o = 4'hf;
        default :             data_be_o = 'x;
    endcase
end

always_comb begin : assign_core_resp
    if (data_rvalid_i) begin
        if (data_err_i) begin
            core_resp = SCR1_MEM_RESP_RDY_ER;
        end else begin
            core_resp = SCR1_MEM_RESP_RDY_OK;
        end
    end else begin
        core_resp = SCR1_MEM_RESP_NOTRDY;
    end
end

endmodule : scr1_mem_pulp
