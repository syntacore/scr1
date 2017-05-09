/// Copyright by Syntacore LLC © 2016, 2017. See LICENSE for details
/// @file       <scr1_dmem_router.sv>
/// @brief      Data memory router
///
`include "scr1_memif.svh"
`include "scr1_arch_description.svh"

module scr1_dmem_router
#(
    parameter SCR1_ADDR_MASK    = `SCR1_DMEM_AWIDTH'hFFFF0000,
    parameter SCR1_ADDR_PATTERN = `SCR1_DMEM_AWIDTH'h00010000
)
(
    // Control signals
    input   logic                           rst_n,
    input   logic                           clk,

    // Core interface
    output  logic                           dmem_req_ack,
    input   logic                           dmem_req,
    input   type_scr1_mem_cmd_e             dmem_cmd,
    input   type_scr1_mem_width_e           dmem_width,
    input   logic [`SCR1_DMEM_AWIDTH-1:0]   dmem_addr,
    input   logic [`SCR1_DMEM_DWIDTH-1:0]   dmem_wdata,
    output  logic [`SCR1_DMEM_DWIDTH-1:0]   dmem_rdata,
    output  type_scr1_mem_resp_e            dmem_resp,

    // PORT0 interface
    input   logic                           port0_req_ack,
    output  logic                           port0_req,
    output  type_scr1_mem_cmd_e             port0_cmd,
    output  type_scr1_mem_width_e           port0_width,
    output  logic [`SCR1_DMEM_AWIDTH-1:0]   port0_addr,
    output  logic [`SCR1_DMEM_DWIDTH-1:0]   port0_wdata,
    input   logic [`SCR1_DMEM_DWIDTH-1:0]   port0_rdata,
    input   type_scr1_mem_resp_e            port0_resp,

    // PORT1 interface
    input   logic                           port1_req_ack,
    output  logic                           port1_req,
    output  type_scr1_mem_cmd_e             port1_cmd,
    output  type_scr1_mem_width_e           port1_width,
    output  logic [`SCR1_DMEM_AWIDTH-1:0]   port1_addr,
    output  logic [`SCR1_DMEM_DWIDTH-1:0]   port1_wdata,
    input   logic [`SCR1_DMEM_DWIDTH-1:0]   port1_rdata,
    input   type_scr1_mem_resp_e            port1_resp
);

//-------------------------------------------------------------------------------
// Local types declaration
//-------------------------------------------------------------------------------
typedef enum logic {
    SCR1_FSM_ADDR,
    SCR1_FSM_DATA
} type_scr1_fsm_e;

//-------------------------------------------------------------------------------
// Local signal declaration
//-------------------------------------------------------------------------------
type_scr1_fsm_e                 fsm;
logic                           port_sel;
logic                           port_sel_r;
logic [`SCR1_DMEM_DWIDTH-1:0]   sel_rdata;
type_scr1_mem_resp_e            sel_resp;
logic                           sel_req_ack;

//-------------------------------------------------------------------------------
// FSM
//-------------------------------------------------------------------------------
assign port_sel = ((dmem_addr & SCR1_ADDR_MASK) == SCR1_ADDR_PATTERN);

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        fsm        <= SCR1_FSM_ADDR;
        port_sel_r <= 1'b0;
    end else begin
        case (fsm)
            SCR1_FSM_ADDR : begin
                if (dmem_req & sel_req_ack) begin
                    fsm <= SCR1_FSM_DATA;
                    port_sel_r <= port_sel;
                end
            end
            SCR1_FSM_DATA : begin
                case (sel_resp)
                    SCR1_MEM_RESP_RDY_OK : begin
                        if (dmem_req & sel_req_ack) begin
                            fsm <= SCR1_FSM_DATA;
                            port_sel_r <= port_sel;
                        end else begin
                            fsm <= SCR1_FSM_ADDR;
                        end
                    end
                    SCR1_MEM_RESP_RDY_ER : begin
                        fsm <= SCR1_FSM_ADDR;
                    end
                    default : begin
                    end
                endcase
            end
            default : begin
            end
        endcase
    end
end

always_comb begin
    if ((fsm == SCR1_FSM_ADDR) | ((fsm == SCR1_FSM_DATA) & (sel_resp == SCR1_MEM_RESP_RDY_OK))) begin
        sel_req_ack = (port_sel) ? port1_req_ack : port0_req_ack;
    end else begin
        sel_req_ack = 1'b0;
    end
end

assign sel_rdata = (port_sel_r) ? port1_rdata : port0_rdata;
assign sel_resp  = (port_sel_r) ? port1_resp  : port0_resp;

//-------------------------------------------------------------------------------
// Interface to core
//-------------------------------------------------------------------------------
assign dmem_req_ack = sel_req_ack;
assign dmem_rdata   = sel_rdata;
assign dmem_resp    = sel_resp;

//-------------------------------------------------------------------------------
// Interface to PORT0
//-------------------------------------------------------------------------------
always_comb begin
    port0_req = 1'b0;
    case (fsm)
        SCR1_FSM_ADDR : begin
            port0_req = dmem_req & ~port_sel;
        end
        SCR1_FSM_DATA : begin
            if (sel_resp == SCR1_MEM_RESP_RDY_OK) begin
                port0_req = dmem_req & ~port_sel;
            end
        end
        default : begin
        end
    endcase
end

assign port0_cmd   = (~port_sel) ? dmem_cmd   : SCR1_MEM_CMD_ERROR;
assign port0_width = (~port_sel) ? dmem_width : SCR1_MEM_WIDTH_ERROR;
assign port0_addr  = (~port_sel) ? dmem_addr  : 'x;
assign port0_wdata = (~port_sel) ? dmem_wdata : 'x;

//-------------------------------------------------------------------------------
// Interface to PORT1
//-------------------------------------------------------------------------------
always_comb begin
    port1_req = 1'b0;
    case (fsm)
        SCR1_FSM_ADDR : begin
            port1_req = dmem_req & port_sel;
        end
        SCR1_FSM_DATA : begin
            if (sel_resp == SCR1_MEM_RESP_RDY_OK) begin
                port1_req = dmem_req & port_sel;
            end
        end
        default : begin
        end
    endcase
end

assign port1_cmd   = (port_sel) ? dmem_cmd   : SCR1_MEM_CMD_ERROR;
assign port1_width = (port_sel) ? dmem_width : SCR1_MEM_WIDTH_ERROR;
assign port1_addr  = (port_sel) ? dmem_addr  : 'x;
assign port1_wdata = (port_sel) ? dmem_wdata : 'x;

`ifdef SCR1_SYN_OFF_EN
// pragma synthesis_off
//-------------------------------------------------------------------------------
// Assertion
//-------------------------------------------------------------------------------

SCR1_SVA_DMEM_RT_XCHECK : assert property (
    @(posedge clk) disable iff (~rst_n)
    dmem_req |-> !$isunknown({port_sel, dmem_cmd, dmem_width})
    ) else $error("DMEM router Error: unknown values");

// pragma synthesis_on
`endif // SCR1_SYN_OFF_EN

endmodule : scr1_dmem_router
