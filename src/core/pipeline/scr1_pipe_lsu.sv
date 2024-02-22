/// Copyright by Syntacore LLC © 2016-2021. See LICENSE for details
/// @file       <scr1_pipe_lsu.sv>
/// @brief      Load/Store Unit (LSU)
///

//------------------------------------------------------------------------------
 //
 // Functionality:
 // - Performs load and store operations in Data Memory
 // - Generates DMEM address misalign and access fault exceptions
 // - Passes DMEM operations information to TDU and generates LSU breakpoint exception
 //
 // Structure:
 // - FSM
 // - Exceptions logic
 // - LSU <-> EXU interface
 // - LSU <-> DMEM interface
 // - LSU <-> TDU interface
 //
//------------------------------------------------------------------------------

`include "scr1_arch_description.svh"
`include "scr1_arch_types.svh"
`include "scr1_memif.svh"
`include "scr1_riscv_isa_decoding.svh"
`ifdef SCR1_TDU_EN
`include "scr1_tdu.svh"
`endif // SCR1_TDU_EN

module scr1_pipe_lsu (
    // Common
    input   logic                               rst_n,                      // LSU reset
    input   logic                               clk,                        // LSU clock

    // LSU <-> EXU interface
    input   logic                               exu2lsu_req_i,              // Request to LSU
    input   type_scr1_lsu_cmd_sel_e             exu2lsu_cmd_i,              // LSU command
    input   logic [`SCR1_XLEN-1:0]              exu2lsu_addr_i,             // Address of DMEM
    input   logic [`SCR1_XLEN-1:0]              exu2lsu_sdata_i,            // Data for store
    output  logic                               lsu2exu_rdy_o,              // LSU received DMEM response
    output  logic [`SCR1_XLEN-1:0]              lsu2exu_ldata_o,            // Load data
    output  logic                               lsu2exu_exc_o,              // Exception from LSU
    output  type_scr1_exc_code_e                lsu2exu_exc_code_o,         // Exception code
`ifndef SCR1_IMMUTABLE_ENDIANNES
    input   type_endianness                     exu2lsu_endianness_i,       // Endianness of the data access
`endif // SCR1_IMMUTABLE_ENDIANNES

`ifdef SCR1_TDU_EN
    // LSU <-> TDU interface
    output  type_scr1_brkm_lsu_mon_s            lsu2tdu_dmon_o,             // Data address stream monitoring
    input   logic                               tdu2lsu_ibrkpt_exc_req_i,   // Instruction BP exception request
    input   logic                               tdu2lsu_dbrkpt_exc_req_i,   // Data BP exception request
`endif // SCR1_TDU_EN

    // LSU <-> DMEM interface
    output  logic                               lsu2dmem_req_o,             // Data memory request
    output  type_scr1_mem_cmd_e                 lsu2dmem_cmd_o,             // Data memory command (READ/WRITE)
    output  type_scr1_mem_width_e               lsu2dmem_width_o,           // Data memory data width
    output  logic [`SCR1_DMEM_AWIDTH-1:0]       lsu2dmem_addr_o,            // Data memory address
    output  logic [`SCR1_DMEM_DWIDTH-1:0]       lsu2dmem_wdata_o,           // Data memory write data
    input   logic                               dmem2lsu_req_ack_i,         // Data memory request acknowledge
    input   logic [`SCR1_DMEM_DWIDTH-1:0]       dmem2lsu_rdata_i,           // Data memory read data
    input   type_scr1_mem_resp_e                dmem2lsu_resp_i             // Data memory response
);

//------------------------------------------------------------------------------
// Local types declaration
//------------------------------------------------------------------------------

typedef enum logic {
    SCR1_LSU_FSM_IDLE,
    SCR1_LSU_FSM_BUSY
} type_scr1_lsu_fsm_e;

//------------------------------------------------------------------------------
// Local signals declaration
//------------------------------------------------------------------------------

// LSU FSM signals
type_scr1_lsu_fsm_e         lsu_fsm_curr;       // LSU FSM current state
type_scr1_lsu_fsm_e         lsu_fsm_next;       // LSU FSM next state
logic                       lsu_fsm_idle;       // LSU FSM is in IDLE state

// LSU Command register signals
logic                       lsu_cmd_upd;        // LSU Command register update
type_scr1_lsu_cmd_sel_e     lsu_cmd_ff;         // LSU Command register value
logic                       lsu_cmd_ff_load;    // Registered LSU Command is load
logic                       lsu_cmd_ff_store;   // Registered LSU Command is store

// DMEM command and width flags
logic                       dmem_cmd_load;      // DMEM command is load
logic                       dmem_cmd_store;     // DMEM Command is store
logic                       dmem_wdth_word;     // DMEM data width is WORD
logic                       dmem_wdth_hword;    // DMEM data width is HALFWORD
logic                       dmem_wdth_byte;     // DMEM data width is BYTE

// DMEM response and request control signals
logic                       dmem_resp_ok;       // DMEM response is OK
logic                       dmem_resp_er;       // DMEM response is erroneous
logic                       dmem_resp_received; // DMEM response is received
logic                       dmem_req_vd;        // DMEM request is valid (req_ack received)

// Exceptions signals
logic                       lsu_exc_req;        // LSU exception request
logic                       dmem_addr_mslgn;    // DMEM address is misaligned
logic                       dmem_addr_mslgn_l;  // DMEM load address is misaligned
logic                       dmem_addr_mslgn_s;  // DMEM store address is misaligned
`ifdef SCR1_TDU_EN
logic                       lsu_exc_hwbrk;      // LSU hardware breakpoint exception
`endif // SCR1_TDU_EN

// endianess related signals
logic [`SCR1_DMEM_DWIDTH-1:0] ordered_dmem2lsu_rdata; // Data memory read data
// ordered according to the selected endianness
type_endianness endianness; // selected endianness for the data access
logic [$clog2(`SCR1_XLEN)-4:0] swap_control;
// controls how bytes are swapped are swapped according to the selected endianness:
// If swap_control[0]=1 each even byte is swapped for the following (odd) byte
// If swap_control[1]=1 each even halfword is swapped for the following halfword
// (RV64 only) If swap_control[2]=1 the even word is swapped for the odd word
logic [$clog2(`SCR1_XLEN)-4:0] swap_control_ff;  // swap_control register value

//------------------------------------------------------------------------------
// Control logic
//------------------------------------------------------------------------------

// Byte order control logic

`ifndef SCR1_IMMUTABLE_ENDIANNES
assign   endianness = exu2lsu_endianness_i;
`else
assign   endianness = `SCR1_IMMUTABLE_ENDIANNES;
`endif // SCR1_IMMUTABLE_ENDIANNES

 always_comb begin
   case (1'b1)
       dmem_wdth_byte  : swap_control = 2'b0;
       dmem_wdth_hword : swap_control = {1'b0,endianness};
       dmem_wdth_word  : swap_control = {endianness,endianness};
   endcase
 end

 always_ff @(posedge clk) begin
     if (lsu_cmd_upd) begin
         swap_control_ff <= swap_control;
     end
 end

// DMEM response and request control signals
assign dmem_resp_ok       = (dmem2lsu_resp_i == SCR1_MEM_RESP_RDY_OK);
assign dmem_resp_er       = (dmem2lsu_resp_i == SCR1_MEM_RESP_RDY_ER);
assign dmem_resp_received = dmem_resp_ok | dmem_resp_er;
assign dmem_req_vd        = exu2lsu_req_i & dmem2lsu_req_ack_i & ~lsu_exc_req;

// LSU load and store command flags
assign dmem_cmd_load  = (exu2lsu_cmd_i == SCR1_LSU_CMD_LB )
                      | (exu2lsu_cmd_i == SCR1_LSU_CMD_LBU)
                      | (exu2lsu_cmd_i == SCR1_LSU_CMD_LH )
                      | (exu2lsu_cmd_i == SCR1_LSU_CMD_LHU)
                      | (exu2lsu_cmd_i == SCR1_LSU_CMD_LW );
assign dmem_cmd_store = (exu2lsu_cmd_i == SCR1_LSU_CMD_SB )
                      | (exu2lsu_cmd_i == SCR1_LSU_CMD_SH )
                      | (exu2lsu_cmd_i == SCR1_LSU_CMD_SW );

// LSU data width flags
assign dmem_wdth_word  = (exu2lsu_cmd_i == SCR1_LSU_CMD_LW )
                       | (exu2lsu_cmd_i == SCR1_LSU_CMD_SW );
assign dmem_wdth_hword = (exu2lsu_cmd_i == SCR1_LSU_CMD_LH )
                       | (exu2lsu_cmd_i == SCR1_LSU_CMD_LHU)
                       | (exu2lsu_cmd_i == SCR1_LSU_CMD_SH );
assign dmem_wdth_byte  = (exu2lsu_cmd_i == SCR1_LSU_CMD_LB )
                       | (exu2lsu_cmd_i == SCR1_LSU_CMD_LBU)
                       | (exu2lsu_cmd_i == SCR1_LSU_CMD_SB );

// LSU command register
assign lsu_cmd_upd = lsu_fsm_idle & dmem_req_vd;

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        lsu_cmd_ff <= SCR1_LSU_CMD_NONE;
    end else if (lsu_cmd_upd) begin
        lsu_cmd_ff <= exu2lsu_cmd_i;
    end
end

// LSU registered load and store command flags
assign lsu_cmd_ff_load  = (lsu_cmd_ff == SCR1_LSU_CMD_LB )
                        | (lsu_cmd_ff == SCR1_LSU_CMD_LBU)
                        | (lsu_cmd_ff == SCR1_LSU_CMD_LH )
                        | (lsu_cmd_ff == SCR1_LSU_CMD_LHU)
                        | (lsu_cmd_ff == SCR1_LSU_CMD_LW );
assign lsu_cmd_ff_store = (lsu_cmd_ff == SCR1_LSU_CMD_SB )
                        | (lsu_cmd_ff == SCR1_LSU_CMD_SH )
                        | (lsu_cmd_ff == SCR1_LSU_CMD_SW );

//------------------------------------------------------------------------------
// LSU FSM
//------------------------------------------------------------------------------
 //
 // LSU FSM is used to control the LSU <-> DMEM interface
 //
//

// Updating LSU FSM state
always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        lsu_fsm_curr <= SCR1_LSU_FSM_IDLE;
    end else begin
        lsu_fsm_curr <= lsu_fsm_next;
    end
end

// LSU FSM next state logic
always_comb begin
    case (lsu_fsm_curr)
        SCR1_LSU_FSM_IDLE: begin
            lsu_fsm_next = dmem_req_vd        ? SCR1_LSU_FSM_BUSY
                                              : SCR1_LSU_FSM_IDLE;
        end
        SCR1_LSU_FSM_BUSY: begin
            lsu_fsm_next = dmem_resp_received ? SCR1_LSU_FSM_IDLE
                                              : SCR1_LSU_FSM_BUSY;
        end
    endcase
end

assign lsu_fsm_idle = (lsu_fsm_curr == SCR1_LSU_FSM_IDLE);

//------------------------------------------------------------------------------
// Exceptions logic
//------------------------------------------------------------------------------
 //
 // The following types of exceptions are supported:
 // - Load address misalign
 // - Load access fault
 // - Store address misalign
 // - Store access fault
 // - LSU breakpoint exception
//

// DMEM addr misalign logic
assign dmem_addr_mslgn   = exu2lsu_req_i & ( (dmem_wdth_hword & exu2lsu_addr_i[0])
                                           | (dmem_wdth_word  & |exu2lsu_addr_i[1:0]));
assign dmem_addr_mslgn_l = dmem_addr_mslgn & dmem_cmd_load;
assign dmem_addr_mslgn_s = dmem_addr_mslgn & dmem_cmd_store;

// Exception code logic
always_comb begin
    case (1'b1)
        dmem_resp_er     : lsu2exu_exc_code_o = lsu_cmd_ff_load  ? SCR1_EXC_CODE_LD_ACCESS_FAULT
                                              : lsu_cmd_ff_store ? SCR1_EXC_CODE_ST_ACCESS_FAULT
                                                                 : SCR1_EXC_CODE_INSTR_MISALIGN;
`ifdef SCR1_TDU_EN
        lsu_exc_hwbrk    : lsu2exu_exc_code_o = SCR1_EXC_CODE_BREAKPOINT;
`endif // SCR1_TDU_EN
        dmem_addr_mslgn_l: lsu2exu_exc_code_o = SCR1_EXC_CODE_LD_ADDR_MISALIGN;
        dmem_addr_mslgn_s: lsu2exu_exc_code_o = SCR1_EXC_CODE_ST_ADDR_MISALIGN;
        default          : lsu2exu_exc_code_o = SCR1_EXC_CODE_INSTR_MISALIGN;
    endcase // 1'b1
end

assign lsu_exc_req = dmem_addr_mslgn_l | dmem_addr_mslgn_s
`ifdef SCR1_TDU_EN
                   | lsu_exc_hwbrk
`endif // SCR1_TDU_EN
;

//------------------------------------------------------------------------------
// LSU <-> EXU interface
//------------------------------------------------------------------------------

assign lsu2exu_rdy_o = dmem_resp_received;
assign lsu2exu_exc_o = dmem_resp_er | lsu_exc_req;

// Sign- or zero-extending data received from DMEM
always_comb begin
    case (lsu_cmd_ff)
        SCR1_LSU_CMD_LH : lsu2exu_ldata_o = {{16{ordered_dmem2lsu_rdata[15]}}, ordered_dmem2lsu_rdata[15:0]};
        SCR1_LSU_CMD_LHU: lsu2exu_ldata_o = { 16'b0,                     ordered_dmem2lsu_rdata[15:0]};
        SCR1_LSU_CMD_LB : lsu2exu_ldata_o = {{24{ordered_dmem2lsu_rdata[7]}},  ordered_dmem2lsu_rdata[7:0]};
        SCR1_LSU_CMD_LBU: lsu2exu_ldata_o = { 24'b0,                     ordered_dmem2lsu_rdata[7:0]};
        default         : lsu2exu_ldata_o = ordered_dmem2lsu_rdata;
    endcase // lsu_cmd_ff
end

//------------------------------------------------------------------------------
// LSU <-> DMEM interface
//------------------------------------------------------------------------------

assign lsu2dmem_req_o   = exu2lsu_req_i & ~lsu_exc_req & lsu_fsm_idle;
assign lsu2dmem_addr_o  = exu2lsu_addr_i;
scr1_lsu_byte_swapper lsu2dmem_byte_swapper (
  .control(swap_control),
  .in(exu2lsu_sdata_i),
  .out(lsu2dmem_wdata_o)
);
scr1_lsu_byte_swapper dmem2lsu_byte_swapper (
  .control(swap_control_ff),
  .in(dmem2lsu_rdata_i),
  .out(ordered_dmem2lsu_rdata)
);
assign lsu2dmem_cmd_o   = dmem_cmd_store  ? SCR1_MEM_CMD_WR : SCR1_MEM_CMD_RD;
assign lsu2dmem_width_o = dmem_wdth_byte  ? SCR1_MEM_WIDTH_BYTE
                        : dmem_wdth_hword ? SCR1_MEM_WIDTH_HWORD
                                          : SCR1_MEM_WIDTH_WORD;

`ifdef SCR1_TDU_EN
//------------------------------------------------------------------------------
// LSU <-> TDU interface
//------------------------------------------------------------------------------

assign lsu2tdu_dmon_o.vd    = exu2lsu_req_i & lsu_fsm_idle & ~tdu2lsu_ibrkpt_exc_req_i;
assign lsu2tdu_dmon_o.addr  = exu2lsu_addr_i;
assign lsu2tdu_dmon_o.load  = dmem_cmd_load;
assign lsu2tdu_dmon_o.store = dmem_cmd_store;

assign lsu_exc_hwbrk = (exu2lsu_req_i & tdu2lsu_ibrkpt_exc_req_i)
                     | tdu2lsu_dbrkpt_exc_req_i;

`endif // SCR1_TDU_EN

`ifdef SCR1_TRGT_SIMULATION
//------------------------------------------------------------------------------
// Assertions
//------------------------------------------------------------------------------

// X checks

SCR1_SVA_LSU_XCHECK_CTRL : assert property (
    @(negedge clk) disable iff (~rst_n)
    !$isunknown({exu2lsu_req_i, lsu_fsm_curr
`ifdef SCR1_TDU_EN
        , tdu2lsu_ibrkpt_exc_req_i, tdu2lsu_dbrkpt_exc_req_i
`endif // SCR1_TDU_EN
    })
    ) else $error("LSU Error: unknown control value");

SCR1_SVA_LSU_XCHECK_CMD : assert property (
    @(negedge clk) disable iff (~rst_n)
    exu2lsu_req_i |-> !$isunknown({exu2lsu_cmd_i, exu2lsu_addr_i})
    ) else $error("LSU Error: undefined CMD or address");

SCR1_SVA_LSU_XCHECK_SDATA : assert property (
    @(negedge clk) disable iff (~rst_n)
    (exu2lsu_req_i & (lsu2dmem_cmd_o == SCR1_MEM_CMD_WR)) |-> !$isunknown({exu2lsu_sdata_i})
    ) else $error("LSU Error: undefined store data");

SCR1_SVA_LSU_XCHECK_EXC : assert property (
    @(negedge clk) disable iff (~rst_n)
    lsu2exu_exc_o |-> !$isunknown(lsu2exu_exc_code_o)
    ) else $error("LSU Error: exception code undefined");

SCR1_SVA_LSU_IMEM_CTRL : assert property (
    @(negedge clk) disable iff (~rst_n)
    lsu2dmem_req_o |-> !$isunknown({lsu2dmem_cmd_o, lsu2dmem_width_o, lsu2dmem_addr_o})
    ) else $error("LSU Error: undefined dmem control");

SCR1_SVA_LSU_IMEM_ACK : assert property (
    @(negedge clk) disable iff (~rst_n)
    lsu2dmem_req_o |-> !$isunknown(dmem2lsu_req_ack_i)
    ) else $error("LSU Error: undefined dmem ack");

SCR1_SVA_LSU_IMEM_WDATA : assert property (
    @(negedge clk) disable iff (~rst_n)
    lsu2dmem_req_o & (lsu2dmem_cmd_o == SCR1_MEM_CMD_WR)
    |-> !$isunknown(lsu2dmem_wdata_o[8:0])
    ) else $error("LSU Error: undefined dmem wdata");

// Behavior checks

SCR1_SVA_LSU_EXC_ONEHOT : assert property (
    @(negedge clk) disable iff (~rst_n)
    $onehot0({dmem_resp_er, dmem_addr_mslgn_l, dmem_addr_mslgn_s})
    ) else $error("LSU Error: more than one exception at a time");

SCR1_SVA_LSU_UNEXPECTED_DMEM_RESP : assert property (
    @(negedge clk) disable iff (~rst_n)
    lsu_fsm_idle |-> ~dmem_resp_received
    ) else $error("LSU Error: not expecting memory response");

SCR1_SVA_LSU_REQ_EXC : assert property (
    @(negedge clk) disable iff (~rst_n)
    lsu2exu_exc_o |-> exu2lsu_req_i
    ) else $error("LSU Error: impossible exception");

`ifdef SCR1_TDU_EN

SCR1_COV_LSU_MISALIGN_BRKPT : cover property (
    @(negedge clk) disable iff (~rst_n)
    (dmem_addr_mslgn_l | dmem_addr_mslgn_s) & lsu_exc_hwbrk
);
`endif // SCR1_TDU_EN

`endif // SCR1_TRGT_SIMULATION

endmodule : scr1_pipe_lsu

//------------------------------------------------------------------------------
// Modules only used by scr1_pipe_lsu are written bellow because local module
// declarations within a module are not supported.
//
// Functionality:
// - scr1_lsu_byte_swapper is a combinational module. The with of its data input
//   and is data ouput is XLEN. The data ouput is obtained by permuting the data
//   input in the following way:
//    -if control[0]=1 each even byte is swapped for the following (odd) byte
//    -if control[1]=1 each even halfword is swapped for the following halfword
//    -(RV64 only) if control[2]=1 the even word is swapped for the odd word
//------------------------------------------------------------------------------

module swapper #(parameter stages=0, size=0, type wire_t=logic) (
  input logic [stages-1:0] control,
  input wire_t [size-1:0] in,
  output wire_t [size-1:0] out
);

localparam half_size = size>>1;
wire_t [half_size-1:0] out0,out1; //halves of out
assign out = control[stages-1]? {out0,out1} : {out1,out0};
generate
  if(stages>1)
    begin
      swapper #(.stages(stages-1),
                .size(half_size),
                .wire_t(wire_t))
      swapper0 (.control(control[stages-2:0]),
                .in(in[half_size-1:0]),
                .out(out0));
      swapper #(.stages(stages-1),
                .size(half_size),
                .wire_t(wire_t))
      swapper1 (.control(control[stages-2:0]),
                .in(in[size-1:half_size]),
                .out(out1));
    end
  else
    assign {out1,out0} = in;
endgenerate

endmodule : swapper

module scr1_lsu_byte_swapper
#(localparam controlwidth=$clog2(`SCR1_XLEN)-3) //base2 log of the size in bytes
(
  input logic [controlwidth-1:0] control,
  input logic [`SCR1_XLEN-1:0] in,
  output logic [`SCR1_XLEN-1:0] out
);

swapper #(
    .stages(controlwidth),
    .size(`SCR1_XLEN)
)
swapper(.*);

endmodule : scr1_lsu_byte_swapper
