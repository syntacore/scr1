/// Copyright by Syntacore LLC © 2016-2020. See LICENSE for details
/// @file       <scr1_mem_axi.sv>
/// @brief      Memory AXI bridge
///

`include "scr1_memif.svh"
`include "scr1_arch_description.svh"

module scr1_mem_axi
#(
    parameter SCR1_REQ_BUF_SIZE     = 2,                    // Power of 2 value
    parameter SCR1_AXI_IDWIDTH      = 4,
    parameter SCR1_ADDR_WIDTH       = 32,
    parameter SCR1_AXI_REQ_BP       = 1,
    parameter SCR1_AXI_RESP_BP      = 1
)
(
    // Clock and Reset
    input   logic                           clk,
    input   logic                           rst_n,
    input   logic                           axi_reinit,
    // Core Interface
    output  logic                           core_idle,
    output  logic                           core_req_ack,
    input   logic                           core_req,
    input   type_scr1_mem_cmd_e             core_cmd,
    input   type_scr1_mem_width_e           core_width,
    input   logic [SCR1_ADDR_WIDTH-1:0]     core_addr,
    input   logic [31:0]                    core_wdata,
    output  logic [31:0]                    core_rdata,
    output  type_scr1_mem_resp_e            core_resp,

    // AXI
    output  logic [SCR1_AXI_IDWIDTH-1:0]    awid,
    output  logic [SCR1_ADDR_WIDTH-1:0]     awaddr,
    output  logic [ 7:0]                    awlen,
    output  logic [ 2:0]                    awsize,
    output  logic [ 1:0]                    awburst,
    output  logic                           awlock,
    output  logic [ 3:0]                    awcache,
    output  logic [ 2:0]                    awprot,
    output  logic [ 3:0]                    awregion,
    output  logic [ 3:0]                    awuser,
    output  logic [ 3:0]                    awqos,
    output  logic                           awvalid,
    input   logic                           awready,
    output  logic [31:0]                    wdata,
    output  logic [3:0]                     wstrb,
    output  logic                           wlast,
    output  logic [3:0]                     wuser,
    output  logic                           wvalid,
    input   logic                           wready,
    input   logic [SCR1_AXI_IDWIDTH-1:0]    bid,
    input   logic [ 1:0]                    bresp,
    input   logic                           bvalid,
    input   logic [ 3:0]                    buser,
    output  logic                           bready,
    output  logic [SCR1_AXI_IDWIDTH-1:0]    arid,
    output  logic [SCR1_ADDR_WIDTH-1:0]     araddr,
    output  logic [ 7:0]                    arlen,
    output  logic [ 2:0]                    arsize,
    output  logic [ 1:0]                    arburst,
    output  logic                           arlock,
    output  logic [ 3:0]                    arcache,
    output  logic [ 2:0]                    arprot,
    output  logic [ 3:0]                    arregion,
    output  logic [ 3:0]                    aruser,
    output  logic [ 3:0]                    arqos,
    output  logic                           arvalid,
    input   logic                           arready,
    input   logic [SCR1_AXI_IDWIDTH-1:0]    rid,
    input   logic [31:0]                    rdata,
    input   logic [ 1:0]                    rresp,
    input   logic                           rlast,
    input   logic [ 3:0]                    ruser,
    input   logic                           rvalid,
    output  logic                           rready
);


// Local functions
function automatic logic [2:0] width2axsize (
    input   type_scr1_mem_width_e    width );
    logic [2:0] axsize;
begin
    case (width)
        SCR1_MEM_WIDTH_BYTE :  axsize = 3'b000;
        SCR1_MEM_WIDTH_HWORD:  axsize = 3'b001;
        SCR1_MEM_WIDTH_WORD :  axsize = 3'b010;
                     default:  axsize = 'x;
    endcase

    return axsize;
end
endfunction: width2axsize

typedef struct packed {
    type_scr1_mem_width_e                               axi_width;
    logic                    [SCR1_ADDR_WIDTH-1:0]      axi_addr;
    logic                                   [31:0]      axi_wdata;
} type_scr1_request_s;

typedef struct packed {
    logic                                               req_write;
    logic                                               req_addr;
    logic                                               req_data;
    logic                                               req_resp;
} type_scr1_req_status_s;


type_scr1_request_s         [SCR1_REQ_BUF_SIZE-1:0]     req_fifo;
type_scr1_req_status_s      [SCR1_REQ_BUF_SIZE-1:0]     req_status;
type_scr1_req_status_s      [SCR1_REQ_BUF_SIZE-1:0]     req_status_new;
logic                       [SCR1_REQ_BUF_SIZE-1:0]     req_status_en;
logic               [$clog2(SCR1_REQ_BUF_SIZE)-1:0]     req_aval_ptr;
logic               [$clog2(SCR1_REQ_BUF_SIZE)-1:0]     req_proc_ptr;
logic               [$clog2(SCR1_REQ_BUF_SIZE)-1:0]     req_done_ptr;
logic                                                   rresp_err;
logic                                       [31:0]      rcvd_rdata;
type_scr1_mem_resp_e                                    rcvd_resp;
logic                                                   force_read;
logic                                                   force_write;



assign core_req_ack =   ~axi_reinit                        &
                        ~req_status[req_aval_ptr].req_resp &
                         core_resp!=SCR1_MEM_RESP_RDY_ER;


assign rready      = ~req_status[req_done_ptr].req_write;
assign bready      =  req_status[req_done_ptr].req_write;


assign force_read  = bit'(SCR1_AXI_REQ_BP) & core_req & core_req_ack & req_aval_ptr==req_proc_ptr & core_cmd==SCR1_MEM_CMD_RD;
assign force_write = bit'(SCR1_AXI_REQ_BP) & core_req & core_req_ack & req_aval_ptr==req_proc_ptr & core_cmd==SCR1_MEM_CMD_WR;


always_comb begin: idle_status
    core_idle = 1'b1;
    for (int unsigned i=0; i<SCR1_REQ_BUF_SIZE; ++i) begin
        core_idle &= req_status[i].req_resp==1'b0;
    end
end

always_ff @(posedge clk) begin
    if (core_req & core_req_ack) begin
        req_fifo[req_aval_ptr].axi_width <= core_width;
        req_fifo[req_aval_ptr].axi_addr  <= core_addr;
        req_fifo[req_aval_ptr].axi_wdata <= core_wdata;
    end
end

// Request Status Queue
// It is used for holding control info of processing requests

// Combinational logic of Request Status Queue
always_comb begin
    // Default
    req_status_en  = '0; // No update
    req_status_new = req_status; // Hold request info

    // Update status on new core request
    if( core_req & core_req_ack ) begin
        req_status_en[req_aval_ptr]            = 1'd1;

        req_status_new[req_aval_ptr].req_resp  = 1'd1;
        req_status_new[req_aval_ptr].req_write = core_cmd == SCR1_MEM_CMD_WR;

        req_status_new[req_aval_ptr].req_addr  = ~( (force_read & arready) |
                                                    (force_write & awready) );

        req_status_new[req_aval_ptr].req_data  = ~( (force_write & wready & awlen == 8'd0) |
                                                    (~force_write & core_cmd == SCR1_MEM_CMD_RD) );
    end

    // Update status on AXI address phase
    if ( (awvalid & awready) | (arvalid & arready) ) begin
        req_status_en[req_proc_ptr]           = 1'd1;
        req_status_new[req_proc_ptr].req_addr = 1'd0;
    end

    // Update status on AXI data phase
    if ( wvalid & wready & wlast ) begin
        req_status_en[req_proc_ptr]           = 1'd1;
        req_status_new[req_proc_ptr].req_data = 1'd0;
    end

    // Update status when AXI finish transaction
    if ( (bvalid & bready) | (rvalid & rready & rlast) ) begin
        req_status_en[req_done_ptr]           = 1'd1;
        req_status_new[req_done_ptr].req_resp = 1'd0;
    end
end

// Request Status Queue register
always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        req_status <= '0;
    end else begin
        for (int unsigned i = 0; i < SCR1_REQ_BUF_SIZE; ++i) begin
            if ( req_status_en[i] ) begin
                req_status[i] <= req_status_new[i];
            end
        end
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n)                         req_aval_ptr <= '0;
    else if (core_req & core_req_ack)   req_aval_ptr <= req_aval_ptr + 1'b1;
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        req_proc_ptr <= '0;
    end else begin
        if ((                                                    awvalid & awready & wvalid & wready & wlast) |
            (~force_write & ~req_status[req_proc_ptr].req_data & awvalid & awready                          ) |
            (~force_write & ~req_status[req_proc_ptr].req_addr &                     wvalid & wready & wlast) |
            (               ~req_status[req_proc_ptr].req_data & arvalid & arready                          )  ) begin

            req_proc_ptr <= req_proc_ptr + 1'b1;
        end
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        req_done_ptr <= '0;
    end else begin
        if ((bvalid & bready | rvalid & rready & rlast) & req_status[req_done_ptr].req_resp) begin

            req_done_ptr <= req_done_ptr + 1'b1;
        end
    end
end



assign arvalid = req_status[req_proc_ptr].req_addr & ~req_status[req_proc_ptr].req_write | force_read;
assign awvalid = req_status[req_proc_ptr].req_addr &  req_status[req_proc_ptr].req_write | force_write;
assign  wvalid = req_status[req_proc_ptr].req_data &  req_status[req_proc_ptr].req_write | force_write;

assign araddr  = (~force_read )? req_fifo[req_proc_ptr].axi_addr : core_addr;
assign awaddr  = (~force_write)? req_fifo[req_proc_ptr].axi_addr : core_addr;

always_comb begin
    if (bvalid & bready & req_status[req_done_ptr].req_resp) begin
        rcvd_resp = (bresp==2'b00)? SCR1_MEM_RESP_RDY_OK :
                                    SCR1_MEM_RESP_RDY_ER;
    end else begin
        if (rvalid & rready & rlast & req_status[req_done_ptr].req_resp) begin
            rcvd_resp = (rresp==2'b00)? SCR1_MEM_RESP_RDY_OK :
                                        SCR1_MEM_RESP_RDY_ER;
        end else begin
            rcvd_resp = SCR1_MEM_RESP_NOTRDY;
        end
    end
end




// Write data signals adaptation
always_comb begin
    if (force_write)
        case (core_width)
            SCR1_MEM_WIDTH_BYTE :  wstrb = 4'h1 << core_addr[1:0];
            SCR1_MEM_WIDTH_HWORD:  wstrb = 4'h3 << core_addr[1:0];
            SCR1_MEM_WIDTH_WORD :  wstrb = 4'hf << core_addr[1:0];
                         default:  wstrb = 'x;
        endcase
    else
        case (req_fifo[req_proc_ptr].axi_width)
            SCR1_MEM_WIDTH_BYTE :  wstrb = 4'h1 << req_fifo[req_proc_ptr].axi_addr[1:0];
            SCR1_MEM_WIDTH_HWORD:  wstrb = 4'h3 << req_fifo[req_proc_ptr].axi_addr[1:0];
            SCR1_MEM_WIDTH_WORD :  wstrb = 4'hf << req_fifo[req_proc_ptr].axi_addr[1:0];
                         default:  wstrb = 'x;
        endcase
end



assign wdata = (force_write)?                       core_wdata << (8*                       core_addr[1:0]) :
                              req_fifo[req_proc_ptr].axi_wdata << (8* req_fifo[req_proc_ptr].axi_addr[1:0]);


// Read data adaptation
always_comb begin
    case (req_fifo[req_done_ptr].axi_width)
        SCR1_MEM_WIDTH_BYTE :  rcvd_rdata = rdata >> (8*req_fifo[req_done_ptr].axi_addr[1:0]);
        SCR1_MEM_WIDTH_HWORD:  rcvd_rdata = rdata >> (8*req_fifo[req_done_ptr].axi_addr[1:0]);
        SCR1_MEM_WIDTH_WORD :  rcvd_rdata = rdata >> (8*req_fifo[req_done_ptr].axi_addr[1:0]);
                     default:  rcvd_rdata = 'x;
    endcase
end


generate
    if (SCR1_AXI_RESP_BP == 1) begin : axi_resp_bp
        assign core_rdata = (rvalid & rready & rlast) ? rcvd_rdata : '0;
        assign core_resp  = (axi_reinit) ? SCR1_MEM_RESP_NOTRDY : rcvd_resp;
    end else begin : axi_resp_no_bp
        always_ff @(negedge rst_n, posedge clk) begin
            if (~rst_n)              core_resp  <= SCR1_MEM_RESP_NOTRDY;
            else                     core_resp  <= (axi_reinit) ? SCR1_MEM_RESP_NOTRDY : rcvd_resp;
        end
        always_ff @(posedge clk) begin
            if (rvalid & rready & rlast) core_rdata <= rcvd_rdata;
        end
    end
endgenerate



// AXI interface assignments
assign awid     = SCR1_AXI_IDWIDTH'(1);
assign awlen    = 8'd0;
assign awsize   = (force_write) ? width2axsize(core_width) : width2axsize(req_fifo[req_proc_ptr].axi_width);
assign awburst  = 2'd1;
assign awcache  = 4'd2;
assign awlock   = '0;
assign awprot   = '0;
assign awregion = '0;
assign awuser   = '0;
assign awqos    = '0;

assign arid     = SCR1_AXI_IDWIDTH'(0);
assign arlen    = 8'd0;
assign arsize   = (force_read) ? width2axsize(core_width) : width2axsize(req_fifo[req_proc_ptr].axi_width);
assign arburst  = 2'd1;
assign arcache  = 4'd2;
assign arprot   = '0;
assign arregion = '0;
assign arlock   = '0;
assign arqos    = '0;
assign aruser   = '0;

assign wlast    = 1'd1;
assign wuser    = '0;


`ifdef SCR1_TRGT_SIMULATION
//-------------------------------------------------------------------------------
// Assertion
//-------------------------------------------------------------------------------

// X checks
SCR1_SVA_AXI_X_CHECK0  : assert property (@(negedge clk) disable iff (~rst_n)   !$isunknown({core_req, awready, wready, bvalid, arready, rvalid}) )
                                                                                                        else $error("AXI bridge: X state on input");
SCR1_SVA_AXI_X_CHECK1  : assert property (@(negedge clk) disable iff (~rst_n)   core_req |->
                                                                                    !$isunknown({core_cmd, core_width, core_addr}) )
                                                                                                        else $error("AXI bridge: X state on input");
SCR1_SVA_AXI_X_CHECK2  : assert property (@(negedge clk) disable iff (~rst_n)   bvalid |->
                                                                                    !$isunknown({bid, bresp}) )
                                                                                                        else $error("AXI bridge: X state on input");
SCR1_SVA_AXI_X_CHECK3  : assert property (@(negedge clk) disable iff (~rst_n)   rvalid |->
                                                                                    !$isunknown({rid, rresp}) )
                                                                                                        else $error("AXI bridge: X state on input");
`endif // SCR1_TRGT_SIMULATION

endmodule : scr1_mem_axi
