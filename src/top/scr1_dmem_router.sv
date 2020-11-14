/// Copyright by Syntacore LLC © 2016-2020. See LICENSE for details
/// @file       <scr1_dmem_router.sv>
/// @brief      Data memory router
///
`include "scr1_memif.svh"
`include "scr1_arch_description.svh"

module scr1_dmem_router
#(
    parameter SCR1_PORT1_ADDR_MASK      = `SCR1_DMEM_AWIDTH'hFFFF0000,
    parameter SCR1_PORT1_ADDR_PATTERN   = `SCR1_DMEM_AWIDTH'h00010000,
    parameter SCR1_PORT2_ADDR_MASK      = `SCR1_DMEM_AWIDTH'hFFFF0000,
    parameter SCR1_PORT2_ADDR_PATTERN   = `SCR1_DMEM_AWIDTH'h00020000
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
    input   type_scr1_mem_resp_e            port1_resp,

    // PORT2 interface
    input   logic                           port2_req_ack,
    output  logic                           port2_req,
    output  type_scr1_mem_cmd_e             port2_cmd,
    output  type_scr1_mem_width_e           port2_width,
    output  logic [`SCR1_DMEM_AWIDTH-1:0]   port2_addr,
    output  logic [`SCR1_DMEM_DWIDTH-1:0]   port2_wdata,
    input   logic [`SCR1_DMEM_DWIDTH-1:0]   port2_rdata,
    input   type_scr1_mem_resp_e            port2_resp
);

//-------------------------------------------------------------------------------
// Local types declaration
//-------------------------------------------------------------------------------
typedef enum logic {
    SCR1_FSM_ADDR,
    SCR1_FSM_DATA
} type_scr1_fsm_e;

typedef enum logic [1:0] {
    SCR1_SEL_PORT0,
    SCR1_SEL_PORT1,
    SCR1_SEL_PORT2
} type_scr1_sel_e;

//-------------------------------------------------------------------------------
// Local signal declaration
//-------------------------------------------------------------------------------
type_scr1_fsm_e                 fsm;
type_scr1_sel_e                 port_sel;
type_scr1_sel_e                 port_sel_r;
logic [`SCR1_DMEM_DWIDTH-1:0]   sel_rdata;
type_scr1_mem_resp_e            sel_resp;
logic                           sel_req_ack;

//-------------------------------------------------------------------------------
// FSM
//-------------------------------------------------------------------------------
always_comb begin
    port_sel    = SCR1_SEL_PORT0;
    if ((dmem_addr & SCR1_PORT1_ADDR_MASK) == SCR1_PORT1_ADDR_PATTERN) begin
        port_sel    = SCR1_SEL_PORT1;
    end else if ((dmem_addr & SCR1_PORT2_ADDR_MASK) == SCR1_PORT2_ADDR_PATTERN) begin
        port_sel    = SCR1_SEL_PORT2;
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        fsm         <= SCR1_FSM_ADDR;
        port_sel_r  <= SCR1_SEL_PORT0;
    end else begin
        case (fsm)
            SCR1_FSM_ADDR : begin
                if (dmem_req & sel_req_ack) begin
                    fsm         <= SCR1_FSM_DATA;
                    port_sel_r  <= port_sel;
                end
            end
            SCR1_FSM_DATA : begin
                case (sel_resp)
                    SCR1_MEM_RESP_RDY_OK : begin
                        if (dmem_req & sel_req_ack) begin
                            fsm         <= SCR1_FSM_DATA;
                            port_sel_r  <= port_sel;
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
        case (port_sel)
            SCR1_SEL_PORT0  : sel_req_ack   = port0_req_ack;
            SCR1_SEL_PORT1  : sel_req_ack   = port1_req_ack;
            SCR1_SEL_PORT2  : sel_req_ack   = port2_req_ack;
            default         : sel_req_ack   = 1'b0;
        endcase
    end else begin
        sel_req_ack = 1'b0;
    end
end

always_comb begin
    case (port_sel_r)
        SCR1_SEL_PORT0  : begin
            sel_rdata   = port0_rdata;
            sel_resp    = port0_resp;
        end
        SCR1_SEL_PORT1  : begin
            sel_rdata   = port1_rdata;
            sel_resp    = port1_resp;
        end
        SCR1_SEL_PORT2  : begin
            sel_rdata   = port2_rdata;
            sel_resp    = port2_resp;
        end
        default         : begin
            sel_rdata   = '0;
            sel_resp    = SCR1_MEM_RESP_RDY_ER;
        end
    endcase
end

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
            port0_req = dmem_req & (port_sel == SCR1_SEL_PORT0);
        end
        SCR1_FSM_DATA : begin
            if (sel_resp == SCR1_MEM_RESP_RDY_OK) begin
                port0_req = dmem_req & (port_sel == SCR1_SEL_PORT0);
            end
        end
        default : begin
        end
    endcase
end

assign port0_cmd    = (port_sel == SCR1_SEL_PORT0) ? dmem_cmd   : SCR1_MEM_CMD_ERROR;
assign port0_width  = (port_sel == SCR1_SEL_PORT0) ? dmem_width : SCR1_MEM_WIDTH_ERROR;
assign port0_addr   = (port_sel == SCR1_SEL_PORT0) ? dmem_addr  : 'x;
assign port0_wdata  = (port_sel == SCR1_SEL_PORT0) ? dmem_wdata : 'x;

//-------------------------------------------------------------------------------
// Interface to PORT1
//-------------------------------------------------------------------------------
always_comb begin
    port1_req = 1'b0;
    case (fsm)
        SCR1_FSM_ADDR : begin
            port1_req = dmem_req & (port_sel == SCR1_SEL_PORT1);
        end
        SCR1_FSM_DATA : begin
            if (sel_resp == SCR1_MEM_RESP_RDY_OK) begin
                port1_req = dmem_req & (port_sel == SCR1_SEL_PORT1);
            end
        end
        default : begin
        end
    endcase
end

assign port1_cmd    = (port_sel == SCR1_SEL_PORT1) ? dmem_cmd   : SCR1_MEM_CMD_ERROR;
assign port1_width  = (port_sel == SCR1_SEL_PORT1) ? dmem_width : SCR1_MEM_WIDTH_ERROR;
assign port1_addr   = (port_sel == SCR1_SEL_PORT1) ? dmem_addr  : 'x;
assign port1_wdata  = (port_sel == SCR1_SEL_PORT1) ? dmem_wdata : 'x;

//-------------------------------------------------------------------------------
// Interface to PORT2
//-------------------------------------------------------------------------------
always_comb begin
    port2_req = 1'b0;
    case (fsm)
        SCR1_FSM_ADDR : begin
            port2_req = dmem_req & (port_sel == SCR1_SEL_PORT2);
        end
        SCR1_FSM_DATA : begin
            if (sel_resp == SCR1_MEM_RESP_RDY_OK) begin
                port2_req = dmem_req & (port_sel == SCR1_SEL_PORT2);
            end
        end
        default : begin
        end
    endcase
end

assign port2_cmd    = (port_sel == SCR1_SEL_PORT2) ? dmem_cmd   : SCR1_MEM_CMD_ERROR;
assign port2_width  = (port_sel == SCR1_SEL_PORT2) ? dmem_width : SCR1_MEM_WIDTH_ERROR;
assign port2_addr   = (port_sel == SCR1_SEL_PORT2) ? dmem_addr  : 'x;
assign port2_wdata  = (port_sel == SCR1_SEL_PORT2) ? dmem_wdata : 'x;

`ifdef SCR1_TRGT_SIMULATION
//-------------------------------------------------------------------------------
// Assertion
//-------------------------------------------------------------------------------

SCR1_SVA_DMEM_RT_XCHECK : assert property (
    @(negedge clk) disable iff (~rst_n)
    dmem_req |-> !$isunknown({port_sel, dmem_cmd, dmem_width})
    ) else $error("DMEM router Error: unknown values");

`endif // SCR1_TRGT_SIMULATION

endmodule : scr1_dmem_router
