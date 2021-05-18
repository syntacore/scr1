/// Copyright by Syntacore LLC © 2016-2020. See LICENSE for details
/// @file       <scr1_dm.sv>
/// @brief      Debug Module (DM)
///

//------------------------------------------------------------------------------
 //
 // Functionality:
 // - Allows debugger to perform a system reset (ndm_rst)
 // - Allows debugger to control the HART's state
 // - Provides debugger with information about the current HART's state
 // - Provides debugger with Abstract Command interface that allows to:
 //   - Access MPRF registers
 //   - Access CSR registers
 //   - Access memory with the same view and permission as the hart has
 // - Provides debugger with Abstract Command status information (busy flag and error code)
 // - Provides debugger with Program Buffer functionality that allows to execute
 //   small programs on a halted HART
 //
 // Structure:
 // - DM <-> DMI interface
 // - DM registers:
 //   - DMCONTROL
 //   - DMSTATUS
 // - Abstract Command Control logic
 // - Abstract Command FSM
 // - Abstract Command Status logic
 // - Abstract Instruction logic
 // - Abstract registers:
 //   - COMMAND
 //   - ABSTRACTAUTO
 //   - PROGBUF0..5
 //   - DATA0..1
 // - DHI FSM
 // - HART command registers
 // - DHI interface
 //
//

`include "scr1_arch_description.svh"

`ifdef SCR1_DBG_EN
`include "scr1_csr.svh"
`include "scr1_dm.svh"

module scr1_dm (
    // System
    input  logic                                    rst_n,                      // DM reset
    input  logic                                    clk,                        // DM clock

    // DM internal interface
    input  logic                                    dmi2dm_req_i,               // DMI request
    input  logic                                    dmi2dm_wr_i,                // DMI write
    input  logic [SCR1_DBG_DMI_ADDR_WIDTH-1:0]      dmi2dm_addr_i,              // DMI address
    input  logic [SCR1_DBG_DMI_DATA_WIDTH-1:0]      dmi2dm_wdata_i,             // DMI write data
    output logic                                    dm2dmi_resp_o,              // DMI response
    output logic [SCR1_DBG_DMI_DATA_WIDTH-1:0]      dm2dmi_rdata_o,             // DMI read data

    // DM <-> Pipeline: HART Run Control i/f
    output logic                                    ndm_rst_n_o,                // Non-DM Reset output
    output logic                                    hart_rst_n_o,               // HART reset output
    output logic                                    dm2pipe_active_o,           // Debug Module active flag
    output logic                                    dm2pipe_cmd_req_o,          // Request to pipe
    output type_scr1_hdu_dbgstates_e                dm2pipe_cmd_o,              // Command to pipe
    input  logic                                    pipe2dm_cmd_resp_i,         // Response to Debug Module
    input  logic                                    pipe2dm_cmd_rcode_i,        // HART Command return code: 0 - Ok; 1 - Error
    input  logic                                    pipe2dm_hart_event_i,       // HART event flag
    input  type_scr1_hdu_hartstatus_s               pipe2dm_hart_status_i,      // HART Status

    input  logic [`SCR1_XLEN-1:0]                   soc2dm_fuse_mhartid_i,      // RO MHARTID value
    input  logic [`SCR1_XLEN-1:0]                   pipe2dm_pc_sample_i,        // RO PC value for sampling

    // HART Abstract Command / Program Buffer i/f
    input  logic [SCR1_HDU_PBUF_ADDR_WIDTH-1:0]     pipe2dm_pbuf_addr_i,        // Program Buffer address
    output logic [SCR1_HDU_CORE_INSTR_WIDTH-1:0]    dm2pipe_pbuf_instr_o,       // Program Buffer instruction

    // HART Abstract Data regs i/f
    input  logic                                    pipe2dm_dreg_req_i,         // Abstract Data Register request
    input  logic                                    pipe2dm_dreg_wr_i,          // Abstract Data Register write
    input  logic [`SCR1_XLEN-1:0]                   pipe2dm_dreg_wdata_i,       // Abstract Data Register write data
    output logic                                    dm2pipe_dreg_resp_o,        // Abstract Data Register response
    output logic                                    dm2pipe_dreg_fail_o,        // Abstract Data Register fail - possibly not needed ?
    output logic [`SCR1_XLEN-1:0]                   dm2pipe_dreg_rdata_o        // Abstract Data Register read data
);

//------------------------------------------------------------------------------
// Local types declaration
//------------------------------------------------------------------------------

typedef enum logic [3:0] {
    ABS_STATE_IDLE,
    ABS_STATE_ERR,
    ABS_STATE_EXEC,
    ABS_STATE_XREG_RW,
    ABS_STATE_MEM_SAVE_XREG,
    ABS_STATE_MEM_SAVE_XREG_FORADDR,
    ABS_STATE_MEM_RW,
    ABS_STATE_MEM_RETURN_XREG,
    ABS_STATE_MEM_RETURN_XREG_FORADDR,
    ABS_STATE_CSR_RO,
    ABS_STATE_CSR_SAVE_XREG,
    ABS_STATE_CSR_RW,
    ABS_STATE_CSR_RETURN_XREG
} type_scr1_abs_fsm_e;

typedef enum logic [2:0] {
    DHI_STATE_IDLE,
    DHI_STATE_EXEC,
    DHI_STATE_EXEC_RUN,
    DHI_STATE_EXEC_HALT,
    DHI_STATE_HALT_REQ,
    DHI_STATE_RESUME_REQ,
    DHI_STATE_RESUME_RUN
} type_scr1_dhi_fsm_e;

typedef enum logic [SCR1_DBG_ABSTRACTCS_CMDERR_WDTH:0] {
    ABS_ERR_NONE      = (SCR1_DBG_ABSTRACTCS_CMDERR_WDTH+1)'('d0),
    ABS_ERR_BUSY      = (SCR1_DBG_ABSTRACTCS_CMDERR_WDTH+1)'('d1),
    ABS_ERR_CMD       = (SCR1_DBG_ABSTRACTCS_CMDERR_WDTH+1)'('d2),
    ABS_ERR_EXCEPTION = (SCR1_DBG_ABSTRACTCS_CMDERR_WDTH+1)'('d3),
    ABS_ERR_NOHALT    = (SCR1_DBG_ABSTRACTCS_CMDERR_WDTH+1)'('d4)
} type_scr1_abs_err_e;


//------------------------------------------------------------------------------
// Local parameters declaration
//------------------------------------------------------------------------------

// Abstract instruction opcode parameters
localparam      SCR1_OP_SYSTEM      = 7'b111_0011;
localparam      SCR1_OP_LOAD        = 7'b000_0011;
localparam      SCR1_OP_STORE       = 7'b010_0011;

// Abstract instruction funct3 parameters
localparam      SCR1_FUNCT3_CSRRW       = 3'b001;
localparam      SCR1_FUNCT3_CSRRS       = 3'b010;
localparam      SCR1_FUNCT3_SB          = 3'b000;
localparam      SCR1_FUNCT3_SH          = 3'b001;
localparam      SCR1_FUNCT3_SW          = 3'b010;
localparam      SCR1_FUNCT3_LW          = 3'b010;
localparam      SCR1_FUNCT3_LBU         = 3'b100;
localparam      SCR1_FUNCT3_LHU         = 3'b101;

// DMCONTROL parameters
//------------------------------------------------------------------------------
localparam      DMCONTROL_HARTRESET     = 1'd0;
localparam      DMCONTROL_RESERVEDB     = 1'd0;
localparam      DMCONTROL_HASEL         = 1'd0;
localparam      DMCONTROL_HARTSELLO     = 1'd0;
localparam      DMCONTROL_HARTSELHI     = 1'd0;
localparam      DMCONTROL_RESERVEDA     = 1'd0;

// DMSTATUS parameters
//------------------------------------------------------------------------------
localparam      DMSTATUS_RESERVEDC      = 1'd0;
localparam      DMSTATUS_IMPEBREAK      = 1'd1;
localparam      DMSTATUS_RESERVEDB      = 1'd0;
localparam      DMSTATUS_ALLUNAVAIL     = 1'd0;
localparam      DMSTATUS_ANYUNAVAIL     = 1'd0;
localparam      DMSTATUS_ALLANYUNAVAIL  = 1'd0;
localparam      DMSTATUS_ALLANYNONEXIST = 1'b0;
localparam      DMSTATUS_AUTHENTICATED  = 1'd1;
localparam      DMSTATUS_AUTHBUSY       = 1'd0;
localparam      DMSTATUS_RESERVEDA      = 1'd0;
localparam      DMSTATUS_DEVTREEVALID   = 1'd0;
localparam      DMSTATUS_VERSION        = 2'd2;

// HARTINFO parameters
//------------------------------------------------------------------------------
localparam      HARTINFO_RESERVEDB      = 1'd0;
localparam      HARTINFO_NSCRATCH       = 4'd1;
localparam      HARTINFO_RESERVEDA      = 1'd0;
localparam      HARTINFO_DATAACCESS     = 1'd0;
localparam      HARTINFO_DATASIZE       = 4'd1;
localparam      HARTINFO_DATAADDR       = 12'h7b2;

// ABSTRACTCS parameters
//------------------------------------------------------------------------------
localparam      ABSTRACTCS_RESERVEDD    = 1'd0;
localparam      ABSTRACTCS_PROGBUFSIZE  = 5'd6;
localparam      ABSTRACTCS_RESERVEDC    = 1'd0;
localparam      ABSTRACTCS_RESERVEDB    = 1'd0;
localparam      ABSTRACTCS_RESERVEDA    = 1'd0;
localparam      ABSTRACTCS_DATACOUNT    = 4'd2;

localparam      ABS_CMD_HARTREG         = 1'd0;
localparam      ABS_CMD_HARTMEM         = 2'd2;
localparam      ABS_CMD_HARTREG_CSR     = 4'b0000;
localparam      ABS_CMD_HARTREG_INTFPU  = 4'b0001;
localparam      ABS_CMD_HARTREG_INT     = 7'b000_0000;
localparam      ABS_CMD_HARTREG_FPU     = 7'b000_0001;
localparam      ABS_EXEC_EBREAK         = 32'b000000000001_00000_000_00000_1110011;

//------------------------------------------------------------------------------
// Local signals declaration
//------------------------------------------------------------------------------

// DM <-> DMI interface internal signals
//------------------------------------------------------------------------------

// Register selection signals
logic                                             dmi_req_dmcontrol;
logic                                             dmi_req_abstractcs;
logic                                             dmi_req_abstractauto;
logic                                             dmi_req_command;
logic                                             dmi_rpt_command;
logic                                             dmi_req_data0;
logic                                             dmi_req_data1;
logic                                             dmi_req_progbuf0;
logic                                             dmi_req_progbuf1;
logic                                             dmi_req_progbuf2;
logic                                             dmi_req_progbuf3;
logic                                             dmi_req_progbuf4;
logic                                             dmi_req_progbuf5;

logic                                             dmi_req_any;

// Registers write request signals
logic                                             dmcontrol_wr_req;
logic                                             abstractcs_wr_req;
logic                                             data0_wr_req;
logic                                             data1_wr_req;
logic                                             dreg_wr_req;
logic                                             command_wr_req;
logic                                             autoexec_wr_req;
logic                                             progbuf0_wr_req;
logic                                             progbuf1_wr_req;
logic                                             progbuf2_wr_req;
logic                                             progbuf3_wr_req;
logic                                             progbuf4_wr_req;
logic                                             progbuf5_wr_req;

// DM registers
//------------------------------------------------------------------------------

// DM clock enable signals
logic                                             clk_en_dm;
logic                                             clk_en_dm_ff;

// DMCONTROL register signals
logic                                             dmcontrol_haltreq_ff;
logic                                             dmcontrol_haltreq_next;
logic                                             dmcontrol_resumereq_ff;
logic                                             dmcontrol_resumereq_next;
logic                                             dmcontrol_ackhavereset_ff;
logic                                             dmcontrol_ackhavereset_next;
logic                                             dmcontrol_ndmreset_ff;
logic                                             dmcontrol_ndmreset_next;
logic                                             dmcontrol_dmactive_ff;
logic                                             dmcontrol_dmactive_next;

// Auxilary Skip Reset On Powerup register
logic                                             havereset_skip_pwrup_ff;
logic                                             havereset_skip_pwrup_next;

// DMSTATUS register signals
logic                                             dmstatus_allany_havereset_ff;
logic                                             dmstatus_allany_havereset_next;
logic                                             dmstatus_allany_resumeack_ff;
logic                                             dmstatus_allany_resumeack_next;
logic                                             dmstatus_allany_halted_ff;
logic                                             dmstatus_allany_halted_next;

// Abstract command control logic signals
//------------------------------------------------------------------------------

logic [SCR1_DBG_DMI_DATA_WIDTH-1:0]               abs_cmd;

logic                                             abs_cmd_csr_ro;
logic [SCR1_DBG_COMMAND_TYPE_WDTH:0]              abs_cmd_type;
logic                                             abs_cmd_regacs;
logic [SCR1_DBG_COMMAND_ACCESSREG_REGNO_HI-12:0]  abs_cmd_regtype;
logic [6:0]                                       abs_cmd_regfile;
logic                                             abs_cmd_regwr;
logic [SCR1_DBG_COMMAND_ACCESSREG_SIZE_WDTH:0]    abs_cmd_regsize;
logic                                             abs_cmd_execprogbuf;
logic                                             abs_cmd_regvalid;
logic [2:0]                                       abs_cmd_memsize;
logic                                             abs_cmd_memwr;
logic                                             abs_cmd_memvalid;

logic                                             abs_cmd_regsize_vd;
logic                                             abs_cmd_memsize_vd;

logic                                             abs_cmd_wr_ff;
logic                                             abs_cmd_wr_next;
logic                                             abs_cmd_postexec_ff;
logic                                             abs_cmd_postexec_next;
logic [11:0]                                      abs_cmd_regno;
logic [11:0]                                      abs_cmd_regno_ff;
logic [1:0]                                       abs_cmd_size_ff;
logic [1:0]                                       abs_cmd_size_next;

logic                                             abs_reg_access_csr;
logic                                             abs_reg_access_mprf;

logic                                             abs_cmd_hartreg_vd;
logic                                             abs_cmd_hartmem_vd;

logic                                             abs_cmd_reg_access_req;
logic                                             abs_cmd_csr_access_req;
logic                                             abs_cmd_mprf_access_req;
logic                                             abs_cmd_execprogbuf_req;

logic                                             abs_cmd_csr_ro_access_vd;
logic                                             abs_cmd_csr_rw_access_vd;
logic                                             abs_cmd_mprf_access_vd;
logic                                             abs_cmd_mem_access_vd;

// Abstract FSM signals
//------------------------------------------------------------------------------

type_scr1_abs_fsm_e                               abs_fsm_ff;
type_scr1_abs_fsm_e                               abs_fsm_next;
logic                                             abs_fsm_idle;
logic                                             abs_fsm_exec;
logic                                             abs_fsm_csr_ro;
logic                                             abs_fsm_err;
logic                                             abs_fsm_use_addr;

// Abstract registers
//------------------------------------------------------------------------------

logic                                             clk_en_abs;

// ABSTRACTCS register signals
logic                                             abstractcs_busy;
logic                                             abstractcs_ro_en;

// COMMAND register signals
logic [`SCR1_XLEN-1:0]                            abs_command_ff;
logic [`SCR1_XLEN-1:0]                            abs_command_next;

// ABSTRACTAUTO register signals
logic                                             abs_autoexec_ff;
logic                                             abs_autoexec_next;

// Program buffer registers
logic [`SCR1_XLEN-1:0]                            abs_progbuf0_ff;
logic [`SCR1_XLEN-1:0]                            abs_progbuf1_ff;
logic [`SCR1_XLEN-1:0]                            abs_progbuf2_ff;
logic [`SCR1_XLEN-1:0]                            abs_progbuf3_ff;
logic [`SCR1_XLEN-1:0]                            abs_progbuf4_ff;
logic [`SCR1_XLEN-1:0]                            abs_progbuf5_ff;

// Data 0/1 registers
logic                                             data0_xreg_save;
logic [`SCR1_XLEN-1:0]                            abs_data0_ff;
logic [`SCR1_XLEN-1:0]                            abs_data0_next;
logic [`SCR1_XLEN-1:0]                            abs_data1_ff;
logic [`SCR1_XLEN-1:0]                            abs_data1_next;

// Abstract command status logic signals
//------------------------------------------------------------------------------

// Abstract error exception flag register
logic                                             abs_err_exc_upd;
logic                                             abs_err_exc_ff;
logic                                             abs_err_exc_next;

logic                                             abs_err_acc_busy_upd;
logic                                             abs_err_acc_busy_ff;
logic                                             abs_err_acc_busy_next;

type_scr1_abs_err_e                               abstractcs_cmderr_ff;
type_scr1_abs_err_e                               abstractcs_cmderr_next;

// Abstract instruction signals
//------------------------------------------------------------------------------

// Abstract instruction execution request register
logic                                             abs_exec_req_next;
logic                                             abs_exec_req_ff;

// Abstract instruction register
logic [4:0]                                       abs_instr_rd;
logic [4:0]                                       abs_instr_rs1;
logic [4:0]                                       abs_instr_rs2;
logic [2:0]                                       abs_instr_mem_funct3;
logic [`SCR1_XLEN-1:0]                            abs_exec_instr_next;
logic [`SCR1_XLEN-1:0]                            abs_exec_instr_ff;

// DHI FSM signals
//------------------------------------------------------------------------------

type_scr1_dhi_fsm_e                               dhi_fsm_next;
type_scr1_dhi_fsm_e                               dhi_fsm_ff;
type_scr1_dhi_fsm_e                               dhi_req;

logic                                             dhi_fsm_idle;
logic                                             dhi_fsm_exec;
logic                                             dhi_fsm_exec_halt;
logic                                             dhi_fsm_halt_req;
logic                                             dhi_fsm_resume_req;

// DHI interface signals
//------------------------------------------------------------------------------

logic                                             cmd_resp_ok;
logic                                             hart_rst_unexp;
logic                                             halt_req_vd;
logic                                             resume_req_vd;

logic                                             dhi_resp;
logic                                             dhi_resp_exc;

logic                                             hart_pbuf_ebreak_ff;
logic                                             hart_pbuf_ebreak_next;

// HART command registers
//------------------------------------------------------------------------------

logic                                             hart_cmd_req_ff;
logic                                             hart_cmd_req_next;

type_scr1_hdu_dbgstates_e                         hart_cmd_ff;
type_scr1_hdu_dbgstates_e                         hart_cmd_next;

// HART state signals
//------------------------------------------------------------------------------

logic                                             hart_state_reset;
logic                                             hart_state_run;
logic                                             hart_state_drun;
logic                                             hart_state_dhalt;

//------------------------------------------------------------------------------
// DM <-> DMI interface
//------------------------------------------------------------------------------

// Register selection logic
//------------------------------------------------------------------------------

always_comb begin
    dmi_req_dmcontrol    = dmi2dm_req_i & (dmi2dm_addr_i == SCR1_DBG_DMCONTROL);
    dmi_req_abstractcs   = dmi2dm_req_i & (dmi2dm_addr_i == SCR1_DBG_ABSTRACTCS);
    dmi_req_abstractauto = dmi2dm_req_i & (dmi2dm_addr_i == SCR1_DBG_ABSTRACTAUTO);
    dmi_req_data0        = dmi2dm_req_i & (dmi2dm_addr_i == SCR1_DBG_DATA0);
    dmi_req_data1        = dmi2dm_req_i & (dmi2dm_addr_i == SCR1_DBG_DATA1);
    dmi_req_command      = dmi2dm_req_i & (dmi2dm_addr_i == SCR1_DBG_COMMAND);
    dmi_rpt_command      = (abs_autoexec_ff & dmi_req_data0);
    dmi_req_progbuf0     = dmi2dm_req_i & (dmi2dm_addr_i == SCR1_DBG_PROGBUF0);
    dmi_req_progbuf1     = dmi2dm_req_i & (dmi2dm_addr_i == SCR1_DBG_PROGBUF1);
    dmi_req_progbuf2     = dmi2dm_req_i & (dmi2dm_addr_i == SCR1_DBG_PROGBUF2);
    dmi_req_progbuf3     = dmi2dm_req_i & (dmi2dm_addr_i == SCR1_DBG_PROGBUF3);
    dmi_req_progbuf4     = dmi2dm_req_i & (dmi2dm_addr_i == SCR1_DBG_PROGBUF4);
    dmi_req_progbuf5     = dmi2dm_req_i & (dmi2dm_addr_i == SCR1_DBG_PROGBUF5);
end

assign dmi_req_any = dmi_req_command  | dmi_rpt_command  | dmi_req_abstractauto
                   | dmi_req_data0    | dmi_req_data1    | dmi_req_progbuf0
                   | dmi_req_progbuf1 | dmi_req_progbuf2 | dmi_req_progbuf3
                   | dmi_req_progbuf4 | dmi_req_progbuf5;


// Read data multiplexer
//------------------------------------------------------------------------------

always_comb begin
    dm2dmi_rdata_o = '0;

    case (dmi2dm_addr_i)
        SCR1_DBG_DMSTATUS: begin
            dm2dmi_rdata_o[SCR1_DBG_DMSTATUS_RESERVEDC_HI:
                           SCR1_DBG_DMSTATUS_RESERVEDC_LO]     = DMSTATUS_RESERVEDC;
            dm2dmi_rdata_o[SCR1_DBG_DMSTATUS_IMPEBREAK]        = DMSTATUS_IMPEBREAK;
            dm2dmi_rdata_o[SCR1_DBG_DMSTATUS_RESERVEDB_HI:
                           SCR1_DBG_DMSTATUS_RESERVEDB_LO]     = DMSTATUS_RESERVEDB;
            dm2dmi_rdata_o[SCR1_DBG_DMSTATUS_ALLHAVERESET]     = dmstatus_allany_havereset_ff;
            dm2dmi_rdata_o[SCR1_DBG_DMSTATUS_ANYHAVERESET]     = dmstatus_allany_havereset_ff;
            dm2dmi_rdata_o[SCR1_DBG_DMSTATUS_ALLRESUMEACK]     = dmstatus_allany_resumeack_ff;
            dm2dmi_rdata_o[SCR1_DBG_DMSTATUS_ANYRESUMEACK]     = dmstatus_allany_resumeack_ff;
            dm2dmi_rdata_o[SCR1_DBG_DMSTATUS_ALLNONEXISTENT]   = DMSTATUS_ALLANYNONEXIST;
            dm2dmi_rdata_o[SCR1_DBG_DMSTATUS_ANYNONEXISTENT]   = DMSTATUS_ALLANYNONEXIST;
            dm2dmi_rdata_o[SCR1_DBG_DMSTATUS_ALLUNAVAIL]       = DMSTATUS_ALLANYUNAVAIL;
            dm2dmi_rdata_o[SCR1_DBG_DMSTATUS_ANYUNAVAIL]       = DMSTATUS_ALLANYUNAVAIL;
            dm2dmi_rdata_o[SCR1_DBG_DMSTATUS_ALLRUNNING]       = ~dmstatus_allany_halted_ff;
            dm2dmi_rdata_o[SCR1_DBG_DMSTATUS_ANYRUNNING]       = ~dmstatus_allany_halted_ff;
            dm2dmi_rdata_o[SCR1_DBG_DMSTATUS_ALLHALTED]        = dmstatus_allany_halted_ff;
            dm2dmi_rdata_o[SCR1_DBG_DMSTATUS_ANYHALTED]        = dmstatus_allany_halted_ff;
            dm2dmi_rdata_o[SCR1_DBG_DMSTATUS_AUTHENTICATED]    = DMSTATUS_AUTHENTICATED;
            dm2dmi_rdata_o[SCR1_DBG_DMSTATUS_AUTHBUSY]         = DMSTATUS_AUTHBUSY;
            dm2dmi_rdata_o[SCR1_DBG_DMSTATUS_RESERVEDA]        = DMSTATUS_RESERVEDA;
            dm2dmi_rdata_o[SCR1_DBG_DMSTATUS_DEVTREEVALID]     = DMSTATUS_DEVTREEVALID;
            dm2dmi_rdata_o[SCR1_DBG_DMSTATUS_VERSION_HI:
                           SCR1_DBG_DMSTATUS_VERSION_LO]       = DMSTATUS_VERSION;;
        end

        SCR1_DBG_DMCONTROL: begin
            dm2dmi_rdata_o[SCR1_DBG_DMCONTROL_HALTREQ]         = dmcontrol_haltreq_ff;
            dm2dmi_rdata_o[SCR1_DBG_DMCONTROL_RESUMEREQ]       = dmcontrol_resumereq_ff;
            dm2dmi_rdata_o[SCR1_DBG_DMCONTROL_HARTRESET]       = DMCONTROL_HARTRESET;
            dm2dmi_rdata_o[SCR1_DBG_DMCONTROL_ACKHAVERESET]    = dmcontrol_ackhavereset_ff;
            dm2dmi_rdata_o[SCR1_DBG_DMCONTROL_RESERVEDB]       = DMCONTROL_RESERVEDB;
            dm2dmi_rdata_o[SCR1_DBG_DMCONTROL_HASEL]           = DMCONTROL_HASEL;
            dm2dmi_rdata_o[SCR1_DBG_DMCONTROL_HARTSELLO_HI:
                           SCR1_DBG_DMCONTROL_HARTSELLO_LO]    = DMCONTROL_HARTSELLO;
            dm2dmi_rdata_o[SCR1_DBG_DMCONTROL_HARTSELHI_HI:
                           SCR1_DBG_DMCONTROL_HARTSELHI_LO]    = DMCONTROL_HARTSELHI;
            dm2dmi_rdata_o[SCR1_DBG_DMCONTROL_RESERVEDA_HI:
                           SCR1_DBG_DMCONTROL_RESERVEDA_LO]    = DMCONTROL_RESERVEDA;
            dm2dmi_rdata_o[SCR1_DBG_DMCONTROL_NDMRESET]        = dmcontrol_ndmreset_ff;
            dm2dmi_rdata_o[SCR1_DBG_DMCONTROL_DMACTIVE]        = dmcontrol_dmactive_ff;
        end

        SCR1_DBG_ABSTRACTCS: begin
            dm2dmi_rdata_o[SCR1_DBG_ABSTRACTCS_RESERVEDD_HI:
                           SCR1_DBG_ABSTRACTCS_RESERVEDD_LO]   = ABSTRACTCS_RESERVEDD;
            dm2dmi_rdata_o[SCR1_DBG_ABSTRACTCS_PROGBUFSIZE_HI:
                           SCR1_DBG_ABSTRACTCS_PROGBUFSIZE_LO] = ABSTRACTCS_PROGBUFSIZE;
            dm2dmi_rdata_o[SCR1_DBG_ABSTRACTCS_RESERVEDC_HI:
                           SCR1_DBG_ABSTRACTCS_RESERVEDC_LO]   = ABSTRACTCS_RESERVEDC;
            dm2dmi_rdata_o[SCR1_DBG_ABSTRACTCS_BUSY]           = abstractcs_busy;
            dm2dmi_rdata_o[SCR1_DBG_ABSTRACTCS_RESERVEDB]      = ABSTRACTCS_RESERVEDB;
            dm2dmi_rdata_o[SCR1_DBG_ABSTRACTCS_CMDERR_HI:
                           SCR1_DBG_ABSTRACTCS_CMDERR_LO]      = abstractcs_cmderr_ff;
            dm2dmi_rdata_o[SCR1_DBG_ABSTRACTCS_RESERVEDA_HI:
                           SCR1_DBG_ABSTRACTCS_RESERVEDA_LO]   = ABSTRACTCS_RESERVEDA;
            dm2dmi_rdata_o[SCR1_DBG_ABSTRACTCS_DATACOUNT_HI:
                           SCR1_DBG_ABSTRACTCS_DATACOUNT_LO]   = ABSTRACTCS_DATACOUNT;
        end

        SCR1_DBG_HARTINFO: begin
            dm2dmi_rdata_o[SCR1_DBG_HARTINFO_RESERVEDB_HI:
                           SCR1_DBG_HARTINFO_RESERVEDB_LO]     = HARTINFO_RESERVEDB;
            dm2dmi_rdata_o[SCR1_DBG_HARTINFO_NSCRATCH_HI:
                           SCR1_DBG_HARTINFO_NSCRATCH_LO]      = HARTINFO_NSCRATCH;
            dm2dmi_rdata_o[SCR1_DBG_HARTINFO_RESERVEDA_HI:
                           SCR1_DBG_HARTINFO_RESERVEDA_LO]     = HARTINFO_RESERVEDA;
            dm2dmi_rdata_o[SCR1_DBG_HARTINFO_DATAACCESS]       = HARTINFO_DATAACCESS;
            dm2dmi_rdata_o[SCR1_DBG_HARTINFO_DATASIZE_HI:
                           SCR1_DBG_HARTINFO_DATASIZE_LO]      = HARTINFO_DATASIZE;
            dm2dmi_rdata_o[SCR1_DBG_HARTINFO_DATAADDR_HI:
                           SCR1_DBG_HARTINFO_DATAADDR_LO]      = HARTINFO_DATAADDR;
        end

        SCR1_DBG_ABSTRACTAUTO: dm2dmi_rdata_o[0] = abs_autoexec_ff;
        SCR1_DBG_DATA0       : dm2dmi_rdata_o    = abs_data0_ff;
        SCR1_DBG_DATA1       : dm2dmi_rdata_o    = abs_data1_ff;
        SCR1_DBG_PROGBUF0    : dm2dmi_rdata_o    = abs_progbuf0_ff;
        SCR1_DBG_PROGBUF1    : dm2dmi_rdata_o    = abs_progbuf1_ff;
        SCR1_DBG_PROGBUF2    : dm2dmi_rdata_o    = abs_progbuf2_ff;
        SCR1_DBG_PROGBUF3    : dm2dmi_rdata_o    = abs_progbuf3_ff;
        SCR1_DBG_PROGBUF4    : dm2dmi_rdata_o    = abs_progbuf4_ff;
        SCR1_DBG_PROGBUF5    : dm2dmi_rdata_o    = abs_progbuf5_ff;
        SCR1_DBG_HALTSUM0    : dm2dmi_rdata_o[0] = dmstatus_allany_halted_ff;

        default: begin
            dm2dmi_rdata_o = '0;
        end
    endcase
end

// Response
assign dm2dmi_resp_o = 1'b1;

// Write requests signals
//------------------------------------------------------------------------------

assign dmcontrol_wr_req  = dmi_req_dmcontrol    & dmi2dm_wr_i;
assign data0_wr_req      = dmi_req_data0        & dmi2dm_wr_i;
assign data1_wr_req      = dmi_req_data1        & dmi2dm_wr_i;
assign dreg_wr_req       = pipe2dm_dreg_req_i   & pipe2dm_dreg_wr_i;
assign command_wr_req    = dmi_req_command      & dmi2dm_wr_i;
assign autoexec_wr_req   = dmi_req_abstractauto & dmi2dm_wr_i;
assign progbuf0_wr_req   = dmi_req_progbuf0     & dmi2dm_wr_i;
assign progbuf1_wr_req   = dmi_req_progbuf1     & dmi2dm_wr_i;
assign progbuf2_wr_req   = dmi_req_progbuf2     & dmi2dm_wr_i;
assign progbuf3_wr_req   = dmi_req_progbuf3     & dmi2dm_wr_i;
assign progbuf4_wr_req   = dmi_req_progbuf4     & dmi2dm_wr_i;
assign progbuf5_wr_req   = dmi_req_progbuf5     & dmi2dm_wr_i;
assign abstractcs_wr_req = dmi_req_abstractcs   & dmi2dm_wr_i;

// HART state signals
//------------------------------------------------------------------------------

assign hart_state_reset = (pipe2dm_hart_status_i.dbg_state == SCR1_HDU_DBGSTATE_RESET);
assign hart_state_run   = (pipe2dm_hart_status_i.dbg_state == SCR1_HDU_DBGSTATE_RUN);
assign hart_state_dhalt = (pipe2dm_hart_status_i.dbg_state == SCR1_HDU_DBGSTATE_DHALTED);
assign hart_state_drun  = (pipe2dm_hart_status_i.dbg_state == SCR1_HDU_DBGSTATE_DRUN);

//------------------------------------------------------------------------------
// DM registers
//------------------------------------------------------------------------------
//
 // Registers:
 // - DM clock enable register
 // - Auxilary Skip Reset On Powerup register
 // - DMCONTROL register
 // - DMSTATUS register

// DM clock enable logic
//------------------------------------------------------------------------------

assign clk_en_dm = dmcontrol_wr_req | dmcontrol_dmactive_ff | clk_en_dm_ff;

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        clk_en_dm_ff <= 1'b0;
    end else if (clk_en_dm) begin
        clk_en_dm_ff <= dmcontrol_dmactive_ff;
    end
end

assign dm2pipe_active_o = clk_en_dm_ff;

// DMCONTROL register
//------------------------------------------------------------------------------

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        dmcontrol_dmactive_ff     <= 1'b0;
        dmcontrol_ndmreset_ff     <= 1'b0;
        dmcontrol_ackhavereset_ff <= 1'b0;
        dmcontrol_haltreq_ff      <= 1'b0;
        dmcontrol_resumereq_ff    <= 1'b0;
    end else if (clk_en_dm) begin
        dmcontrol_dmactive_ff     <= dmcontrol_dmactive_next;
        dmcontrol_ndmreset_ff     <= dmcontrol_ndmreset_next;
        dmcontrol_ackhavereset_ff <= dmcontrol_ackhavereset_next;
        dmcontrol_haltreq_ff      <= dmcontrol_haltreq_next;
        dmcontrol_resumereq_ff    <= dmcontrol_resumereq_next;
    end
end

assign dmcontrol_dmactive_next = dmcontrol_wr_req
                               ? dmi2dm_wdata_i[SCR1_DBG_DMCONTROL_DMACTIVE]
                               : dmcontrol_dmactive_ff;

always_comb begin
    dmcontrol_ndmreset_next     = dmcontrol_ndmreset_ff;
    dmcontrol_ackhavereset_next = dmcontrol_ackhavereset_ff;
    dmcontrol_haltreq_next      = dmcontrol_haltreq_ff;
    dmcontrol_resumereq_next    = dmcontrol_resumereq_ff;
    if (~dmcontrol_dmactive_ff) begin
        dmcontrol_ndmreset_next     = 1'b0;
        dmcontrol_ackhavereset_next = 1'b0;
        dmcontrol_haltreq_next      = 1'b0;
        dmcontrol_resumereq_next    = 1'b0;
    end else if (dmcontrol_wr_req) begin
        dmcontrol_ndmreset_next     = dmi2dm_wdata_i[SCR1_DBG_DMCONTROL_NDMRESET];
        dmcontrol_ackhavereset_next = dmi2dm_wdata_i[SCR1_DBG_DMCONTROL_ACKHAVERESET];
        dmcontrol_haltreq_next      = dmi2dm_wdata_i[SCR1_DBG_DMCONTROL_HALTREQ];
        dmcontrol_resumereq_next    = dmi2dm_wdata_i[SCR1_DBG_DMCONTROL_RESUMEREQ];
    end
end

// Reset signal for system controlled by Debug Module
assign hart_rst_n_o = ~dmcontrol_ndmreset_ff;
assign ndm_rst_n_o  = ~dmcontrol_ndmreset_ff;

// Skip reset on powerup register
//------------------------------------------------------------------------------

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        havereset_skip_pwrup_ff <= 1'b1;
    end else if (clk_en_dm) begin
        havereset_skip_pwrup_ff <= havereset_skip_pwrup_next;
    end
end

assign havereset_skip_pwrup_next = ~dmcontrol_dmactive_ff  ? 1'b1
                                 : havereset_skip_pwrup_ff ? hart_state_reset & ndm_rst_n_o & hart_rst_n_o
                                                           : havereset_skip_pwrup_ff;

// DMSTATUS register
//------------------------------------------------------------------------------

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        dmstatus_allany_havereset_ff <= 1'b0;
        dmstatus_allany_resumeack_ff <= 1'b0;
        dmstatus_allany_halted_ff    <= 1'b0;
    end else if (clk_en_dm) begin
        dmstatus_allany_havereset_ff <= dmstatus_allany_havereset_next;
        dmstatus_allany_resumeack_ff <= dmstatus_allany_resumeack_next;
        dmstatus_allany_halted_ff    <= dmstatus_allany_halted_next;
    end
end

assign dmstatus_allany_havereset_next = ~dmcontrol_dmactive_ff                      ? 1'b0
                                      : ~havereset_skip_pwrup_ff & hart_state_reset ? 1'b1
                                      : dmcontrol_ackhavereset_ff                   ? 1'b0
                                                                                    : dmstatus_allany_havereset_ff;
assign dmstatus_allany_resumeack_next = ~dmcontrol_dmactive_ff  ? 1'b0
                                      : ~dmcontrol_resumereq_ff ? 1'b0
                                      : hart_state_run          ? 1'b1
                                                                : dmstatus_allany_resumeack_ff;

assign dmstatus_allany_halted_next    = ~dmcontrol_dmactive_ff ? 1'b0
                                      : hart_state_dhalt       ? 1'b1
                                      : hart_state_run         ? 1'b0
                                                               : dmstatus_allany_halted_ff;

//------------------------------------------------------------------------------
// Abstract Command control logic
//------------------------------------------------------------------------------
//
 // Consists of the following functional units:
 // - Abstract command decoder
 // - Abstract command access valid flags
 // - Abstract command control registers

assign clk_en_abs = clk_en_dm & dmcontrol_dmactive_ff;

// Abstract command decoder
//------------------------------------------------------------------------------

assign abs_cmd = dmi_req_command ? dmi2dm_wdata_i : abs_command_ff;

always_comb begin
    abs_cmd_regno       = abs_cmd[SCR1_DBG_COMMAND_ACCESSREG_REGNO_LO +: 12];

    abs_cmd_csr_ro      = (abs_cmd_regno == SCR1_CSR_ADDR_MISA)
                        | (abs_cmd_regno == SCR1_CSR_ADDR_MVENDORID)
                        | (abs_cmd_regno == SCR1_CSR_ADDR_MARCHID)
                        | (abs_cmd_regno == SCR1_CSR_ADDR_MIMPID)
                        | (abs_cmd_regno == SCR1_CSR_ADDR_MHARTID)
                        | (abs_cmd_regno == SCR1_HDU_DBGCSR_ADDR_DPC);

    abs_cmd_type        = abs_cmd[SCR1_DBG_COMMAND_TYPE_HI:SCR1_DBG_COMMAND_TYPE_LO];
    abs_cmd_regacs      = abs_cmd[SCR1_DBG_COMMAND_ACCESSREG_TRANSFER];
    abs_cmd_regtype     = abs_cmd[SCR1_DBG_COMMAND_ACCESSREG_REGNO_HI:12];
    abs_cmd_regfile     = abs_cmd[11:5];
    abs_cmd_regsize     = abs_cmd[SCR1_DBG_COMMAND_ACCESSREG_SIZE_HI:
                                  SCR1_DBG_COMMAND_ACCESSREG_SIZE_LO];
    abs_cmd_regwr       = abs_cmd[SCR1_DBG_COMMAND_ACCESSREG_WRITE];
    abs_cmd_execprogbuf = abs_cmd[SCR1_DBG_COMMAND_ACCESSREG_POSTEXEC];

    abs_cmd_regvalid    = ~(|{abs_cmd[SCR1_DBG_COMMAND_ACCESSREG_RESERVEDB],
                              abs_cmd[SCR1_DBG_COMMAND_ACCESSREG_RESERVEDA]});

    abs_cmd_memsize     = abs_cmd[SCR1_DBG_COMMAND_ACCESSMEM_AAMSIZE_HI:
                                  SCR1_DBG_COMMAND_ACCESSMEM_AAMSIZE_LO];
    abs_cmd_memwr       = abs_cmd[SCR1_DBG_COMMAND_ACCESSMEM_WRITE];

    abs_cmd_memvalid    = ~(|{abs_cmd[SCR1_DBG_COMMAND_ACCESSMEM_AAMVIRTUAL],
                              abs_cmd[SCR1_DBG_COMMAND_ACCESSMEM_AAMPOSTINC],
                              abs_cmd[SCR1_DBG_COMMAND_ACCESSMEM_RESERVEDB_HI:
                                      SCR1_DBG_COMMAND_ACCESSMEM_RESERVEDB_HI],
                              abs_cmd[SCR1_DBG_COMMAND_ACCESSMEM_RESERVEDA_HI:
                                      SCR1_DBG_COMMAND_ACCESSMEM_RESERVEDA_HI]});
end

assign abs_reg_access_csr  = (abs_cmd_regtype == ABS_CMD_HARTREG_CSR);
assign abs_reg_access_mprf = (abs_cmd_regtype == ABS_CMD_HARTREG_INTFPU)
                           & (abs_cmd_regfile == ABS_CMD_HARTREG_INT);

// Abstract command access request and valid flags
//------------------------------------------------------------------------------

assign abs_cmd_regsize_vd       = (abs_cmd_regsize == 3'h2);
assign abs_cmd_memsize_vd       = (abs_cmd_memsize < 3'h3);

assign abs_cmd_hartreg_vd       = (abs_cmd_type == ABS_CMD_HARTREG) & abs_cmd_regvalid;
assign abs_cmd_hartmem_vd       = (abs_cmd_type == ABS_CMD_HARTMEM) & abs_cmd_memvalid;

// Abstract command requests
assign abs_cmd_reg_access_req   = abs_cmd_hartreg_vd     & abs_cmd_regacs;
assign abs_cmd_csr_access_req   = abs_cmd_reg_access_req & abs_reg_access_csr;
assign abs_cmd_mprf_access_req  = abs_cmd_reg_access_req & abs_reg_access_mprf;
assign abs_cmd_execprogbuf_req  = abs_cmd_hartreg_vd     & abs_cmd_execprogbuf;

// Abstract command access valid flags
assign abs_cmd_csr_ro_access_vd = abs_cmd_csr_access_req  & abs_cmd_regsize_vd & ~abs_cmd_regwr
                                & ~abs_cmd_execprogbuf    & abs_cmd_csr_ro     & hart_state_run;
assign abs_cmd_csr_rw_access_vd = abs_cmd_csr_access_req  & abs_cmd_regsize_vd
                                & (abs_cmd_regwr | ~abs_cmd_csr_ro_access_vd);
assign abs_cmd_mprf_access_vd   = abs_cmd_mprf_access_req & abs_cmd_regsize_vd;
assign abs_cmd_mem_access_vd    = abs_cmd_hartmem_vd & abs_cmd_memsize_vd;

// Abstract command control registers
//------------------------------------------------------------------------------

always_ff @(posedge clk) begin
    if (clk_en_abs & abs_fsm_idle) begin
        abs_cmd_postexec_ff <= abs_cmd_postexec_next;
        abs_cmd_wr_ff       <= abs_cmd_wr_next;
        abs_cmd_regno_ff    <= abs_cmd_regno;
        abs_cmd_size_ff     <= abs_cmd_size_next;
    end
end

always_comb begin
    abs_cmd_wr_next       = 1'b0;
    abs_cmd_postexec_next = 1'b0;
    abs_cmd_size_next     = abs_cmd_size_ff;
    if ((command_wr_req | dmi_rpt_command) & hart_state_dhalt & abs_fsm_idle) begin
        if (abs_cmd_csr_rw_access_vd) begin
            abs_cmd_wr_next       = abs_cmd_regwr;
            abs_cmd_postexec_next = abs_cmd_execprogbuf;
        end else if (abs_cmd_mprf_access_vd) begin
            abs_cmd_wr_next       = abs_cmd_regwr;
            abs_cmd_size_next     = abs_cmd_regsize[1:0];
            abs_cmd_postexec_next = abs_cmd_execprogbuf;
        end else if (abs_cmd_mem_access_vd) begin
            abs_cmd_wr_next       = abs_cmd_memwr;
            abs_cmd_size_next     = abs_cmd_memsize[1:0];
        end
    end
end

//------------------------------------------------------------------------------
// Abstract command FSM
//------------------------------------------------------------------------------

always_ff @(posedge clk) begin
    if (clk_en_dm) begin
        if (~dmcontrol_dmactive_ff) begin
            abs_fsm_ff <= ABS_STATE_IDLE;
        end else begin
            abs_fsm_ff <= abs_fsm_next;
        end
    end
end

always_comb begin
    abs_fsm_next = abs_fsm_ff;

    case (abs_fsm_ff)
        ABS_STATE_IDLE: begin
            if (command_wr_req | dmi_rpt_command) begin
                case (1'b1)
                    abs_cmd_csr_ro_access_vd: abs_fsm_next = ABS_STATE_CSR_RO;
                    abs_cmd_csr_rw_access_vd: abs_fsm_next = hart_state_dhalt ? ABS_STATE_CSR_SAVE_XREG : ABS_STATE_ERR;
                    abs_cmd_mprf_access_vd  : abs_fsm_next = hart_state_dhalt ? ABS_STATE_XREG_RW       : ABS_STATE_ERR;
                    abs_cmd_execprogbuf_req : abs_fsm_next = ABS_STATE_EXEC;
                    abs_cmd_mem_access_vd   : abs_fsm_next = hart_state_dhalt ? ABS_STATE_MEM_SAVE_XREG : ABS_STATE_ERR;
                    default                 : abs_fsm_next = ABS_STATE_ERR;
                endcase
            end
        end

        ABS_STATE_EXEC: begin
            if (dhi_resp) begin
                if (dhi_resp_exc | abs_err_acc_busy_ff) begin
                    abs_fsm_next = ABS_STATE_ERR;
                end else begin
                    abs_fsm_next = ABS_STATE_IDLE;
                end
            end
        end

        ABS_STATE_XREG_RW: begin
            if (dhi_resp) begin
                case (1'b1)
                    abs_err_acc_busy_ff: abs_fsm_next = ABS_STATE_ERR;
                    abs_cmd_postexec_ff: abs_fsm_next = ABS_STATE_EXEC;
                    default            : abs_fsm_next = ABS_STATE_IDLE;
                endcase
            end
        end

        ABS_STATE_CSR_RO       : abs_fsm_next = abs_err_acc_busy_ff ? ABS_STATE_ERR             : ABS_STATE_IDLE;
        ABS_STATE_CSR_SAVE_XREG: abs_fsm_next = dhi_resp            ? ABS_STATE_CSR_RW          : ABS_STATE_CSR_SAVE_XREG;
        ABS_STATE_CSR_RW       : abs_fsm_next = dhi_resp            ? ABS_STATE_CSR_RETURN_XREG : ABS_STATE_CSR_RW;

        ABS_STATE_CSR_RETURN_XREG: begin
            if (dhi_resp) begin
                case (1'b1)
                    abs_err_exc_ff      : abs_fsm_next = ABS_STATE_ERR;
                    abs_err_acc_busy_ff : abs_fsm_next = ABS_STATE_ERR;
                    abs_cmd_postexec_ff : abs_fsm_next = ABS_STATE_EXEC;
                    default             : abs_fsm_next = ABS_STATE_IDLE;
                endcase
            end
        end

        ABS_STATE_MEM_SAVE_XREG         : abs_fsm_next = dhi_resp ? ABS_STATE_MEM_SAVE_XREG_FORADDR   : ABS_STATE_MEM_SAVE_XREG;
        ABS_STATE_MEM_SAVE_XREG_FORADDR : abs_fsm_next = dhi_resp ? ABS_STATE_MEM_RW                  : ABS_STATE_MEM_SAVE_XREG_FORADDR;
        ABS_STATE_MEM_RW                : abs_fsm_next = dhi_resp ? ABS_STATE_MEM_RETURN_XREG         : ABS_STATE_MEM_RW;
        ABS_STATE_MEM_RETURN_XREG       : abs_fsm_next = dhi_resp ? ABS_STATE_MEM_RETURN_XREG_FORADDR : ABS_STATE_MEM_RETURN_XREG;

        ABS_STATE_MEM_RETURN_XREG_FORADDR: begin
            if (dhi_resp) begin
                case (1'b1)
                    abs_err_exc_ff: abs_fsm_next = ABS_STATE_ERR;
                    abs_err_acc_busy_ff : abs_fsm_next = ABS_STATE_ERR;
                    abs_cmd_postexec_ff : abs_fsm_next = ABS_STATE_EXEC;
                    default             : abs_fsm_next = ABS_STATE_IDLE;
                endcase
            end
        end

        ABS_STATE_ERR: begin
            if (abstractcs_wr_req & (abstractcs_cmderr_next == 3'b0)) begin
                abs_fsm_next = ABS_STATE_IDLE;
            end
        end
    endcase

    if (~abs_fsm_idle & hart_state_reset) begin
        abs_fsm_next    = ABS_STATE_ERR;
    end
end

assign abs_fsm_idle     = (abs_fsm_ff == ABS_STATE_IDLE);
assign abs_fsm_exec     = (abs_fsm_ff == ABS_STATE_EXEC);
assign abs_fsm_csr_ro   = (abs_fsm_ff == ABS_STATE_CSR_RO);
assign abs_fsm_err      = (abs_fsm_ff == ABS_STATE_ERR);
assign abs_fsm_use_addr = (abs_fsm_ff == ABS_STATE_MEM_SAVE_XREG_FORADDR)
                        | (abs_fsm_ff == ABS_STATE_MEM_RETURN_XREG_FORADDR);

//------------------------------------------------------------------------------
// Abstract command status logic
//------------------------------------------------------------------------------

// Abstract command access busy error register
//------------------------------------------------------------------------------

assign abs_err_acc_busy_upd = clk_en_abs & (abs_fsm_idle | dmi_req_any);

always_ff @(posedge clk) begin
    if (abs_err_acc_busy_upd) abs_err_acc_busy_ff <= abs_err_acc_busy_next;
end

assign abs_err_acc_busy_next = ~abs_fsm_idle & dmi_req_any;

// Abstract command access exception error register
//------------------------------------------------------------------------------

assign abs_err_exc_upd = clk_en_abs & (abs_fsm_idle | (dhi_resp & dhi_resp_exc));

always_ff @(posedge clk) begin
    if (abs_err_exc_upd) abs_err_exc_ff <= abs_err_exc_next;
end

assign abs_err_exc_next = ~abs_fsm_idle & dhi_resp & dhi_resp_exc;

//------------------------------------------------------------------------------
// Abstract Instruction logic
//------------------------------------------------------------------------------
//
 // Cosists of the following functional units:
 // - Instruction execution request register
 // - Instruction memory FUNCT3 field multiplexer
 // - Instruction RS1 multiplexer
 // - Instruction RD multiplexer
 // - Abstract Instruction register

// Abstract instruction execution request register
//------------------------------------------------------------------------------

assign abs_exec_req_next = ~(abs_fsm_idle | abs_fsm_csr_ro | abs_fsm_err) & ~dhi_resp;

always_ff @(posedge clk) begin
    if (clk_en_dm) begin
        if (~dmcontrol_dmactive_ff) begin
            abs_exec_req_ff <= 1'b0;
        end else begin
            abs_exec_req_ff <= abs_exec_req_next;
        end
    end
end

// Abstract instruction memory FUNCT3 field multiplexer
//------------------------------------------------------------------------------

always_comb begin
    case (abs_cmd_size_ff)
        2'b00  : abs_instr_mem_funct3 = abs_cmd_wr_ff ? SCR1_FUNCT3_SB : SCR1_FUNCT3_LBU;
        2'b01  : abs_instr_mem_funct3 = abs_cmd_wr_ff ? SCR1_FUNCT3_SH : SCR1_FUNCT3_LHU;
        2'b10  : abs_instr_mem_funct3 = abs_cmd_wr_ff ? SCR1_FUNCT3_SW : SCR1_FUNCT3_LW;
        default: abs_instr_mem_funct3 = SCR1_FUNCT3_SB;
    endcase
end

// Abstract instruction RS1 multiplexer
//------------------------------------------------------------------------------

always_comb begin
    abs_instr_rs1 = 5'h0;
    case (abs_fsm_ff)
        ABS_STATE_XREG_RW                : abs_instr_rs1 = abs_cmd_wr_ff ? 5'h0 : abs_cmd_regno_ff[4:0];
        ABS_STATE_CSR_SAVE_XREG          : abs_instr_rs1 = 5'h5;
        ABS_STATE_MEM_SAVE_XREG          : abs_instr_rs1 = 5'h5;
        ABS_STATE_CSR_RETURN_XREG        : abs_instr_rs1 = 5'h5;
        ABS_STATE_MEM_RETURN_XREG        : abs_instr_rs1 = 5'h5;
        ABS_STATE_CSR_RW                 : abs_instr_rs1 = abs_cmd_wr_ff ? 5'h5 : 5'h0;
        ABS_STATE_MEM_SAVE_XREG_FORADDR  : abs_instr_rs1 = 5'h6;
        ABS_STATE_MEM_RETURN_XREG_FORADDR: abs_instr_rs1 = 5'h6;
        ABS_STATE_MEM_RW                 : abs_instr_rs1 = 5'h6;
        default                          : begin end
    endcase
end

assign abs_instr_rs2 = 5'h5;

// Abstract instruction RD multiplexer
//------------------------------------------------------------------------------

always_comb begin
    abs_instr_rd  = 5'h0;
    case (abs_fsm_ff)
        ABS_STATE_XREG_RW                : abs_instr_rd = abs_cmd_wr_ff ? abs_cmd_regno_ff[4:0] : 5'h0;
        ABS_STATE_CSR_SAVE_XREG          : abs_instr_rd = abs_cmd_wr_ff ? 5'h5 : 5'h0;
        ABS_STATE_MEM_SAVE_XREG          : abs_instr_rd = abs_cmd_wr_ff ? 5'h5 : 5'h0;
        ABS_STATE_CSR_RW                 : abs_instr_rd = abs_cmd_wr_ff ? 5'h0 : 5'h5;
        ABS_STATE_MEM_RW                 : abs_instr_rd = abs_cmd_wr_ff ? 5'h0 : 5'h5;
        ABS_STATE_CSR_RETURN_XREG        : abs_instr_rd = 5'h5;
        ABS_STATE_MEM_RETURN_XREG        : abs_instr_rd = 5'h5;
        ABS_STATE_MEM_SAVE_XREG_FORADDR  : abs_instr_rd = 5'h6;
        ABS_STATE_MEM_RETURN_XREG_FORADDR: abs_instr_rd = 5'h6;
        default                          : begin end
    endcase
end

// Abstract instruction register
//------------------------------------------------------------------------------

always_ff @(posedge clk) begin
    if (clk_en_abs) begin
        abs_exec_instr_ff <= abs_exec_instr_next;
    end
end

always_comb begin
    abs_exec_instr_next = abs_exec_instr_ff;
    case (abs_fsm_ff)
        ABS_STATE_XREG_RW,
        ABS_STATE_CSR_SAVE_XREG,
        ABS_STATE_CSR_RETURN_XREG,
        ABS_STATE_MEM_SAVE_XREG,
        ABS_STATE_MEM_SAVE_XREG_FORADDR,
        ABS_STATE_MEM_RETURN_XREG,
        ABS_STATE_MEM_RETURN_XREG_FORADDR: begin
            abs_exec_instr_next = {SCR1_HDU_DBGCSR_ADDR_DSCRATCH0, abs_instr_rs1, SCR1_FUNCT3_CSRRW, abs_instr_rd, SCR1_OP_SYSTEM};
        end

        ABS_STATE_CSR_RW: begin
            abs_exec_instr_next = abs_cmd_wr_ff
                                ? {abs_cmd_regno_ff[11:0], abs_instr_rs1, SCR1_FUNCT3_CSRRW, abs_instr_rd, SCR1_OP_SYSTEM}
                                : {abs_cmd_regno_ff[11:0], abs_instr_rs1, SCR1_FUNCT3_CSRRS, abs_instr_rd, SCR1_OP_SYSTEM};
        end

        ABS_STATE_MEM_RW: begin
            abs_exec_instr_next = abs_cmd_wr_ff
                                ? {7'h0,  abs_instr_rs2, abs_instr_rs1, abs_instr_mem_funct3, 5'h0,         SCR1_OP_STORE}
                                : {12'h0,                abs_instr_rs1, abs_instr_mem_funct3, abs_instr_rd, SCR1_OP_LOAD};
        end

        default: begin end
    endcase
end

//------------------------------------------------------------------------------
// Abstract registers
//------------------------------------------------------------------------------
//
 // Registers:
 // - ABSTRACTCS register
 // - COMMAND register
 // - ABSTRACTAUTO register
 // - PROGBUF0..5 registers
 // - DATA0..1 registers

// ABSTRACTCS register
//------------------------------------------------------------------------------

always_ff @(posedge clk) begin
    if (clk_en_dm) begin
        if (~dmcontrol_dmactive_ff) begin
            abstractcs_cmderr_ff <= ABS_ERR_NONE;
        end else begin
            abstractcs_cmderr_ff <= abstractcs_cmderr_next;
        end
    end
end

always_comb begin
    abstractcs_cmderr_next = abstractcs_cmderr_ff;

    case (abs_fsm_ff)
        ABS_STATE_IDLE: begin
            if (command_wr_req | dmi_rpt_command) begin
                if (abs_cmd_hartreg_vd) begin
                    case (1'b1)
                        abs_cmd_reg_access_req : begin
                            case (1'b1)
                                abs_cmd_csr_rw_access_vd: abstractcs_cmderr_next = hart_state_dhalt
                                                                                 ? abstractcs_cmderr_ff
                                                                                 : ABS_ERR_NOHALT;
                                abs_cmd_mprf_access_vd  : abstractcs_cmderr_next = hart_state_dhalt
                                                                                 ? abstractcs_cmderr_ff
                                                                                 : ABS_ERR_NOHALT;
                                abs_cmd_csr_ro_access_vd: abstractcs_cmderr_next = abstractcs_cmderr_ff;
                                default                 : abstractcs_cmderr_next = ABS_ERR_CMD;
                            endcase
                        end
                        abs_cmd_execprogbuf_req         : abstractcs_cmderr_next = abstractcs_cmderr_ff;
                        default                         : abstractcs_cmderr_next = ABS_ERR_CMD;
                    endcase
                end else if (abs_cmd_hartmem_vd) begin
                    abstractcs_cmderr_next = ~abs_cmd_memsize_vd ? ABS_ERR_CMD
                                           : ~hart_state_dhalt   ? ABS_ERR_NOHALT
                                                                 : abstractcs_cmderr_ff;
                end else begin
                    abstractcs_cmderr_next = ABS_ERR_CMD;
                end
            end
        end

        ABS_STATE_EXEC: begin
            if (dhi_resp) begin
                if (dhi_resp_exc) begin
                    abstractcs_cmderr_next = ABS_ERR_EXCEPTION;
                end else if (abs_err_acc_busy_ff) begin
                    abstractcs_cmderr_next = ABS_ERR_BUSY;
                end
            end
        end

        ABS_STATE_XREG_RW,
        ABS_STATE_CSR_RO: begin
            if (abs_err_acc_busy_ff) begin
                abstractcs_cmderr_next = ABS_ERR_BUSY;
            end
        end

        ABS_STATE_CSR_RETURN_XREG,
        ABS_STATE_MEM_RETURN_XREG_FORADDR: begin
            if (dhi_resp) begin
                case (1'b1)
                    abs_err_exc_ff     : abstractcs_cmderr_next = ABS_ERR_EXCEPTION;
                    abs_err_acc_busy_ff: abstractcs_cmderr_next = ABS_ERR_BUSY;
                    default:             abstractcs_cmderr_next = abstractcs_cmderr_ff;
                endcase
            end
        end

        ABS_STATE_ERR: begin
            if (dmi_req_abstractcs & dmi2dm_wr_i) begin
                abstractcs_cmderr_next = type_scr1_abs_err_e'(logic'(abstractcs_cmderr_ff)
                                       & (~dmi2dm_wdata_i[SCR1_DBG_ABSTRACTCS_CMDERR_HI:
                                                          SCR1_DBG_ABSTRACTCS_CMDERR_LO]));
            end
        end

        default: begin
        end
    endcase

    if (~abs_fsm_idle & hart_state_reset) begin
        abstractcs_cmderr_next = ABS_ERR_EXCEPTION;
    end
end

assign abstractcs_busy = ~abs_fsm_idle & ~abs_fsm_err;

// Abstract COMMAND register
//------------------------------------------------------------------------------

always_ff @(posedge clk) begin
    if (clk_en_dm) abs_command_ff <= abs_command_next;
end

assign abs_command_next = ~dmcontrol_dmactive_ff          ? '0
                        : (command_wr_req & abs_fsm_idle) ? dmi2dm_wdata_i
                                                          : abs_command_ff;

// Abstract ABSTRACTAUTO register
//------------------------------------------------------------------------------

always_ff @(posedge clk) begin
    if (clk_en_dm) abs_autoexec_ff <= abs_autoexec_next;
end

assign abs_autoexec_next = ~dmcontrol_dmactive_ff           ? 1'b0
                         : (autoexec_wr_req & abs_fsm_idle) ? dmi2dm_wdata_i[0]
                                                            : abs_autoexec_ff;

// Program Buffer registers
//------------------------------------------------------------------------------

always_ff @(posedge clk) begin
    if (clk_en_abs & abs_fsm_idle) begin
        if (progbuf0_wr_req) abs_progbuf0_ff <= dmi2dm_wdata_i;
        if (progbuf1_wr_req) abs_progbuf1_ff <= dmi2dm_wdata_i;
        if (progbuf2_wr_req) abs_progbuf2_ff <= dmi2dm_wdata_i;
        if (progbuf3_wr_req) abs_progbuf3_ff <= dmi2dm_wdata_i;
        if (progbuf4_wr_req) abs_progbuf4_ff <= dmi2dm_wdata_i;
        if (progbuf5_wr_req) abs_progbuf5_ff <= dmi2dm_wdata_i;
    end
end

// Data 0 register
//------------------------------------------------------------------------------

always_ff @(posedge clk) begin
    if (clk_en_abs) begin
        abs_data0_ff <= abs_data0_next;
    end
end

assign data0_xreg_save = dreg_wr_req & ~abs_cmd_wr_ff;

always_comb begin
    abs_data0_next = abs_data0_ff;

    case (abs_fsm_ff)
        ABS_STATE_IDLE           : abs_data0_next = data0_wr_req    ? dmi2dm_wdata_i       : abs_data0_ff;
        ABS_STATE_EXEC           : abs_data0_next = dreg_wr_req     ? pipe2dm_dreg_wdata_i : abs_data0_ff;
        ABS_STATE_CSR_SAVE_XREG  : abs_data0_next = dreg_wr_req     ? pipe2dm_dreg_wdata_i : abs_data0_ff;
        ABS_STATE_CSR_RETURN_XREG: abs_data0_next = dreg_wr_req     ? pipe2dm_dreg_wdata_i : abs_data0_ff;
        ABS_STATE_MEM_SAVE_XREG  : abs_data0_next = dreg_wr_req     ? pipe2dm_dreg_wdata_i : abs_data0_ff;
        ABS_STATE_MEM_RETURN_XREG: abs_data0_next = dreg_wr_req     ? pipe2dm_dreg_wdata_i : abs_data0_ff;
        ABS_STATE_XREG_RW        : abs_data0_next = data0_xreg_save ? pipe2dm_dreg_wdata_i : abs_data0_ff;

        ABS_STATE_CSR_RO: begin
            case (abs_cmd_regno_ff[11:0])
                SCR1_CSR_ADDR_MISA     : abs_data0_next = SCR1_CSR_MISA;
                SCR1_CSR_ADDR_MVENDORID: abs_data0_next = SCR1_CSR_MVENDORID;
                SCR1_CSR_ADDR_MARCHID  : abs_data0_next = SCR1_CSR_MARCHID;
                SCR1_CSR_ADDR_MIMPID   : abs_data0_next = SCR1_CSR_MIMPID;
                SCR1_CSR_ADDR_MHARTID  : abs_data0_next = soc2dm_fuse_mhartid_i;
                default                : abs_data0_next = pipe2dm_pc_sample_i;
            endcase
        end

        default : begin end
    endcase
end

// Data 1 register
//------------------------------------------------------------------------------

always_ff @(posedge clk) begin
    if (clk_en_abs) begin
        abs_data1_ff <= abs_data1_next;
    end
end

always_comb begin
    abs_data1_next = abs_data1_ff;
    case (abs_fsm_ff)
        ABS_STATE_IDLE                   : abs_data1_next = data1_wr_req ? dmi2dm_wdata_i       : abs_data1_ff;
        ABS_STATE_MEM_SAVE_XREG_FORADDR  : abs_data1_next = dreg_wr_req  ? pipe2dm_dreg_wdata_i : abs_data1_ff;
        ABS_STATE_MEM_RETURN_XREG_FORADDR: abs_data1_next = dreg_wr_req  ? pipe2dm_dreg_wdata_i : abs_data1_ff;
        default                          : begin end
    endcase
end

//------------------------------------------------------------------------------
// Debug Hart Interface : control
//------------------------------------------------------------------------------

assign cmd_resp_ok    = pipe2dm_cmd_resp_i & ~pipe2dm_cmd_rcode_i;
assign hart_rst_unexp = ~dhi_fsm_idle      & ~dhi_fsm_halt_req & hart_state_reset;

assign halt_req_vd    = dmcontrol_haltreq_ff   & ~hart_state_dhalt;
assign resume_req_vd  = dmcontrol_resumereq_ff & ~dmstatus_allany_resumeack_ff
                      & hart_state_dhalt;

// DHI fsm
//------------------------------------------------------------------------------

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        dhi_fsm_ff   <= DHI_STATE_IDLE;
    end else if (clk_en_dm) begin
        dhi_fsm_ff <= dhi_fsm_next;
    end
end

always_comb begin
    dhi_fsm_next = dhi_fsm_ff;
    if (~hart_rst_unexp & dmcontrol_dmactive_ff) begin
        // Normal work
        case (dhi_fsm_ff)
            DHI_STATE_IDLE      : dhi_fsm_next = dhi_req;
            DHI_STATE_EXEC      : dhi_fsm_next = cmd_resp_ok      ? DHI_STATE_EXEC_RUN   : DHI_STATE_EXEC;
            DHI_STATE_EXEC_RUN  : dhi_fsm_next = hart_state_drun  ? DHI_STATE_EXEC_HALT  : DHI_STATE_EXEC_RUN;
            DHI_STATE_HALT_REQ  : dhi_fsm_next = cmd_resp_ok      ? DHI_STATE_EXEC_HALT  : DHI_STATE_HALT_REQ;
            DHI_STATE_EXEC_HALT : dhi_fsm_next = hart_state_dhalt ? DHI_STATE_IDLE       : DHI_STATE_EXEC_HALT;
            DHI_STATE_RESUME_REQ: dhi_fsm_next = cmd_resp_ok      ? DHI_STATE_RESUME_RUN : DHI_STATE_RESUME_REQ;
            DHI_STATE_RESUME_RUN: dhi_fsm_next = hart_state_run   ? DHI_STATE_IDLE       : DHI_STATE_RESUME_RUN;
            default             : dhi_fsm_next = dhi_fsm_ff;
        endcase
    end else begin
        // In case of DM reset or core unexpected reset
        dhi_fsm_next = DHI_STATE_IDLE;
    end
end

assign dhi_fsm_idle       = (dhi_fsm_ff == DHI_STATE_IDLE);
assign dhi_fsm_halt_req   = (dhi_fsm_ff == DHI_STATE_HALT_REQ);
assign dhi_fsm_exec       = (dhi_fsm_ff == DHI_STATE_EXEC);
assign dhi_fsm_exec_halt  = (dhi_fsm_ff == DHI_STATE_EXEC_HALT);
assign dhi_fsm_resume_req = (dhi_fsm_ff == DHI_STATE_RESUME_REQ);

always_comb begin
    case (1'b1)
        abs_exec_req_ff: dhi_req = DHI_STATE_EXEC;
        halt_req_vd    : dhi_req = DHI_STATE_HALT_REQ;
        resume_req_vd  : dhi_req = DHI_STATE_RESUME_REQ;
        default        : dhi_req = DHI_STATE_IDLE;
    endcase
end

assign dhi_resp     = dhi_fsm_exec_halt    & hart_state_dhalt;
assign dhi_resp_exc = pipe2dm_hart_event_i & pipe2dm_hart_status_i.except
                                           & ~pipe2dm_hart_status_i.ebreak;

// HART command registers
//------------------------------------------------------------------------------

// HART command request register
always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        hart_cmd_req_ff <= 1'b0;
    end else if (clk_en_dm) begin
        hart_cmd_req_ff <= hart_cmd_req_next;
    end
end

assign hart_cmd_req_next = (dhi_fsm_exec | dhi_fsm_halt_req | dhi_fsm_resume_req)
                         & ~cmd_resp_ok & dmcontrol_dmactive_ff;

// HART command register
always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        hart_cmd_ff <= SCR1_HDU_DBGSTATE_RUN;
    end else if (clk_en_dm) begin
        hart_cmd_ff <= hart_cmd_next;
    end
end

always_comb begin
    hart_cmd_next = SCR1_HDU_DBGSTATE_RUN;
    if (dmcontrol_dmactive_ff) begin
        case (dhi_fsm_ff)
            DHI_STATE_EXEC      : hart_cmd_next = SCR1_HDU_DBGSTATE_DRUN;
            DHI_STATE_HALT_REQ  : hart_cmd_next = SCR1_HDU_DBGSTATE_DHALTED;
            DHI_STATE_RESUME_REQ: hart_cmd_next = SCR1_HDU_DBGSTATE_RUN;
            default             : hart_cmd_next = dm2pipe_cmd_o;
        endcase
    end
end

assign dm2pipe_cmd_req_o = hart_cmd_req_ff;
assign dm2pipe_cmd_o     = hart_cmd_ff;

//------------------------------------------------------------------------------
// Debug Hart Interface : program buffer
//------------------------------------------------------------------------------

// Program Buffer execution EBREAK flag
//------------------------------------------------------------------------------

always_ff @(posedge clk) begin
    if (clk_en_dm) hart_pbuf_ebreak_ff <= hart_pbuf_ebreak_next;
end

assign hart_pbuf_ebreak_next = abs_fsm_exec & (dm2pipe_pbuf_instr_o == ABS_EXEC_EBREAK);

// Program Buffer instruction multiplexer
//------------------------------------------------------------------------------

always_comb begin
    dm2pipe_pbuf_instr_o = ABS_EXEC_EBREAK;

    if (abs_fsm_exec & ~hart_pbuf_ebreak_ff) begin
        case (pipe2dm_pbuf_addr_i)
            3'h0: dm2pipe_pbuf_instr_o = abs_progbuf0_ff;
            3'h1: dm2pipe_pbuf_instr_o = abs_progbuf1_ff;
            3'h2: dm2pipe_pbuf_instr_o = abs_progbuf2_ff;
            3'h3: dm2pipe_pbuf_instr_o = abs_progbuf3_ff;
            3'h4: dm2pipe_pbuf_instr_o = abs_progbuf4_ff;
            3'h5: dm2pipe_pbuf_instr_o = abs_progbuf5_ff;
            default: ;
        endcase
    end else if (pipe2dm_pbuf_addr_i == 3'b0) begin
        dm2pipe_pbuf_instr_o = abs_exec_instr_ff;
    end
end

//------------------------------------------------------------------------------
// Debug Hart Interface : abstract command data
//------------------------------------------------------------------------------

assign dm2pipe_dreg_resp_o  = 1'b1;
assign dm2pipe_dreg_fail_o  = 1'b0;
assign dm2pipe_dreg_rdata_o = abs_fsm_use_addr ? abs_data1_ff : abs_data0_ff;

`ifdef SCR1_TRGT_SIMULATION
//------------------------------------------------------------------------------
// Assertions
//------------------------------------------------------------------------------

SVA_DM_X_CONTROL : assert property (
    @(negedge clk) disable iff (~rst_n)
    !$isunknown({dmi2dm_req_i, pipe2dm_dreg_req_i, pipe2dm_cmd_resp_i,
                 pipe2dm_hart_event_i})
) else $error("DM error: control signals is X - %0b", {dmi2dm_req_i,
              pipe2dm_dreg_req_i, pipe2dm_cmd_resp_i, pipe2dm_hart_event_i});

SVA_DM_X_DMI : assert property (
    @(negedge clk) disable iff (~rst_n)
    dmi2dm_req_i |-> !$isunknown({dmi2dm_wr_i, dmi2dm_addr_i, dmi2dm_wdata_i})
) else $error("DM error: data signals is X on dmi");

SVA_DM_X_HART_PBUF : assert property (
    @(negedge clk) disable iff (~rst_n)
    !$isunknown (pipe2dm_pbuf_addr_i)
) else $error("DM error: data signals is X on hart_pbuf");

SVA_DM_X_HART_DREG : assert property (
    @(negedge clk) disable iff (~rst_n)
    pipe2dm_dreg_req_i |-> !$isunknown({pipe2dm_dreg_wr_i, pipe2dm_dreg_wdata_i})
) else $error("DM error: data signals is X on hart_dreg");

SVA_DM_X_HART_CMD : assert property (
    @(negedge clk) disable iff (~rst_n)
    pipe2dm_cmd_resp_i |-> !$isunknown({pipe2dm_cmd_rcode_i})
) else $error("DM error: data signals is X on dm2pipe_cmd_o");

SVA_DM_X_HART_EVENT : assert property (
    @(negedge clk) disable iff (~rst_n)
    pipe2dm_hart_event_i |-> !$isunknown(pipe2dm_hart_status_i)
) else $error("DM error: data signals is X on pipe2dm_hart_event_i");

`endif // SCR1_TRGT_SIMULATION

endmodule : scr1_dm

`endif // SCR1_DBG_EN
