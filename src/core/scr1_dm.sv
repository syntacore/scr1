/// Copyright by Syntacore LLC © 2016-2019. See LICENSE for details
/// @file       <scr1_dm.sv>
/// @brief      Debug Module (DM)
///

`include "scr1_arch_description.svh"

`ifdef SCR1_DBGC_EN
`include "scr1_csr.svh"
`include "scr1_dm.svh"

module scr1_dm (
    // System
    input  logic                                            rst_n,          // DM reset
    input  logic                                            clk,            // DM clock

    // DM internal interface
    input  logic                                            dmi_req,        // DMI request
    input  logic                                            dmi_wr,         // DMI write
    input  logic [SCR1_DBG_DMI_ADDR_WIDTH-1:0]              dmi_addr,       // DMI address
    input  logic [SCR1_DBG_DMI_DATA_WIDTH-1:0]              dmi_wdata,      // DMI write data
    output logic                                            dmi_resp,       // DMI response
    output logic [SCR1_DBG_DMI_DATA_WIDTH-1:0]              dmi_rdata,      // DMI read data

    // HART Run Control i/f
    output logic                                            ndm_rst_n,      // Non-DM Reset output
    output logic                                            hart_rst_n,     // HART reset output
    output logic                                            hart_dmactive,  // HART DM Active
    output logic                                            hart_cmd_req,   // HART Command request
    output type_scr1_hdu_dbgstates_e                        hart_cmd,       // HART Command
    input  logic                                            hart_cmd_resp,  // HART Command response
    input  logic                                            hart_cmd_rcode, // HART Command return code: 0 - Ok; 1 - Error
    input  logic                                            hart_event,     // HART Event: 1 if HART debug state changed
    input  type_scr1_hdu_hartstatus_s                       hart_status,    // HART Status

    input  logic [`SCR1_XLEN-1:0]                           ro_fuse_mhartid,// RO MHARTID value
    input  logic [`SCR1_XLEN-1:0]                           ro_pc,          // RO PC value for sampling

    // HART Abstract Command / Program Buffer i/f
    input  logic [SCR1_HDU_PBUF_ADDR_WIDTH-1:0]             hart_pbuf_addr, // Program Buffer address - so far request only for 1 instruction
    output logic [SCR1_HDU_CORE_INSTR_WIDTH-1:0]            hart_pbuf_instr,// Program Buffer instruction

    // HART Abstract Data regs i/f
    input  logic                                            hart_dreg_req,  // Abstract Data Register request
    input  logic                                            hart_dreg_wr,   // Abstract Data Register write
    input  logic [`SCR1_XLEN-1:0]                           hart_dreg_wdata,// Abstract Data Register write data
    output logic                                            hart_dreg_resp, // Abstract Data Register response
    output logic                                            hart_dreg_fail, // Abstract Data Register fail - possibly not needed ?
    output logic [`SCR1_XLEN-1:0]                           hart_dreg_rdata // Abstract Data Register read data
);

// DMCONTROL
localparam      DMCONTROL_HARTRESET     = 1'd0;
localparam      DMCONTROL_RESERVEDB     = 1'd0;
localparam      DMCONTROL_HASEL         = 1'd0;
localparam      DMCONTROL_HARTSELLO     = 1'd0;
localparam      DMCONTROL_HARTSELHI     = 1'd0;
localparam      DMCONTROL_RESERVEDA     = 1'd0;
logic           dmcontrol_haltreq_ff;
logic           dmcontrol_resumereq_ff;
logic           dmcontrol_ackhavereset_ff;
logic           dmcontrol_ndmreset_ff;
logic           dmcontrol_dmactive_ff;

// DMSTATUS
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
logic           dmstatus_allany_havereset_ff;
logic           havereset_skip_pwrup_ff;
logic           dmstatus_allany_resumeack_ff;
logic           dmstatus_allany_running;
logic           dmstatus_allany_halted_ff;

// HARTINFO
localparam      HARTINFO_RESERVEDB      = 1'd0;
localparam      HARTINFO_NSCRATCH       = 4'd1;
localparam      HARTINFO_RESERVEDA      = 1'd0;
localparam      HARTINFO_DATAACCESS     = 1'd0;
localparam      HARTINFO_DATASIZE       = 4'd1;
localparam      HARTINFO_DATAADDR       = 12'h7b2;

// ABSTRACTCS
localparam      ABSTRACTCS_RESERVEDD    = 1'd0;
localparam      ABSTRACTCS_PROGBUFSIZE  = 5'd6;
localparam      ABSTRACTCS_RESERVEDC    = 1'd0;
localparam      ABSTRACTCS_RESERVEDB    = 1'd0;
localparam      ABSTRACTCS_RESERVEDA    = 1'd0;
localparam      ABSTRACTCS_DATACOUNT    = 4'd2;

logic           abstractcs_busy;

logic[SCR1_DBG_ABSTRACTCS_CMDERR_HI-
      SCR1_DBG_ABSTRACTCS_CMDERR_LO:0]
                abstractcs_cmderr_ff;

logic           abstractcs_ro_en;

// ABSTRACTAUTO
logic           abstractauto_execdata0_ff;

logic [31:0]    data0_ff;
logic [31:0]    data1_ff;

logic [31:0]    command_ff;
logic [31:0]    progbuf0_ff;
logic [31:0]    progbuf1_ff;
logic [31:0]    progbuf2_ff;
logic [31:0]    progbuf3_ff;
logic [31:0]    progbuf4_ff;
logic [31:0]    progbuf5_ff;

localparam      ABS_CMD_HARTREG         = 1'd0;
localparam      ABS_CMD_HARTMEM         = 2'd2;
localparam      ABS_CMD_HARTREG_CSR     = 4'b0000;
localparam      ABS_CMD_HARTREG_INTFPU  = 4'b0001;
localparam      ABS_CMD_HARTREG_INT     = 7'b000_0000;
localparam      ABS_CMD_HARTREG_FPU     = 7'b000_0001;
localparam      ABS_EXEC_EBREAK         = 32'b000000000001_00000_000_00000_1110011;

localparam      ABS_ERR_BUSY            = 1'd1,
                ABS_ERR_CMD             = 2'd2,
                ABS_ERR_EXCEPTION       = 2'd3,
                ABS_ERR_NOHALT          = 3'd4;

logic           dmi_req_dmcontrol_cmb;
logic           dmi_req_abstractcs_cmb;
logic           dmi_req_abstractauto_cmb;
logic           dmi_req_command_cmb;
logic           dmi_rpt_command_cmb;
logic           dmi_req_data0_cmb;
logic           dmi_req_data1_cmb;

logic           dmi_req_progbuf0_cmb;
logic           dmi_req_progbuf1_cmb;
logic           dmi_req_progbuf2_cmb;
logic           dmi_req_progbuf3_cmb;
logic           dmi_req_progbuf4_cmb;
logic           dmi_req_progbuf5_cmb;

enum logic [3:0] {
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
    }           abs_fsm_cmb, abs_fsm_ff;

logic           abs_exec_req_cmb;
logic           abs_exec_req_ff;
logic [31:0]    abs_exec_instr_cmb;
logic [31:0]    abs_exec_instr_ff;

logic [SCR1_DBG_COMMAND_TYPE_HI - SCR1_DBG_COMMAND_TYPE_LO:0]
                abs_cmd_cmb;

logic           abs_cmd_csr_ro_cmb;
logic           abs_cmd_regacs_cmb;

logic [SCR1_DBG_COMMAND_ACCESSREG_REGNO_HI-12:0]
                abs_cmd_regtype_cmb;

logic [6:0]     abs_cmd_regfile_cmb;
logic           abs_cmd_regwr_cmb;
logic [11:0]    abs_cmd_regno_cmb;

logic [ SCR1_DBG_COMMAND_ACCESSREG_SIZE_HI -
        SCR1_DBG_COMMAND_ACCESSREG_SIZE_LO : 0 ]
                abs_cmd_regsize_cmb;
logic           abs_cmd_regsize_valid_cmb;
logic           abs_cmd_regvalid_cmb;

logic           abs_cmd_execprogbuf_cmb;
logic           abs_cmd_memvalid_cmb;
logic           abs_cmd_memwr_cmb;

logic [2:0]     abs_cmd_memsize_cmb;
logic           abs_cmd_memsize_valid_cmb;

logic           abs_cmd_wr_ff;
logic           abs_cmd_wr_cmb;
logic           abs_cmd_postexec_ff;
logic           abs_cmd_postexec_cmb;
logic [1:0]     abs_cmd_size_ff;
logic [1:0]     abs_cmd_size_cmb;
logic [11:0]    abs_cmd_regno_ff;

logic           abs_err_exception_cmb;
logic           abs_err_exception_ff;
logic           abs_err_acc_busy_cmb;
logic           abs_err_acc_busy_ff;

logic [31:0]    abs_data0_cmb;
logic [31:0]    abs_data1_cmb;

logic [31:0]    abs_command_cmb;
logic           abs_abstractauto_execdata0_cmb;
logic [31:0]    abs_progbuf0_cmb;
logic [31:0]    abs_progbuf1_cmb;
logic [31:0]    abs_progbuf2_cmb;
logic [31:0]    abs_progbuf3_cmb;
logic [31:0]    abs_progbuf4_cmb;
logic [31:0]    abs_progbuf5_cmb;

logic [SCR1_DBG_ABSTRACTCS_CMDERR_HI-SCR1_DBG_ABSTRACTCS_CMDERR_LO:0]
                abs_cmderr_cmb;

// Clock enable
logic           clk_en_dm_cmb;
logic           clk_en_dm_ff;

// DHI
enum logic [2:0] {
    DHI_STATE_IDLE,
    DHI_STATE_EXEC,
    DHI_STATE_EXEC_RUN,
    DHI_STATE_EXEC_HALT,
    DHI_STATE_HALT_REQ,
    DHI_STATE_RESUME_REQ,
    DHI_STATE_RESUME_RUN
    }           dhi_fsm_cmb, dhi_fsm_ff, dhi_req_cmb;

logic                           dhi_resp_cmb;
logic                           dhi_resp_exception_cmb;
logic                           hart_pbuf_ebreak_ff;
logic                           hart_pbuf_ebreak_cmb;
logic                           hart_cmd_req_cmb;
type_scr1_hdu_dbgstates_e   hart_cmd_cmb;

// Debug Module Interface
// ----------------------

// Register access
always_comb begin
    dmi_req_dmcontrol_cmb  = dmi_req  &  dmi_addr == SCR1_DBG_DMCONTROL;
    dmi_req_abstractcs_cmb = dmi_req  &  dmi_addr == SCR1_DBG_ABSTRACTCS;
    dmi_req_abstractauto_cmb = dmi_req  &  dmi_addr == SCR1_DBG_ABSTRACTAUTO;
    dmi_req_data0_cmb      = dmi_req  &  dmi_addr == SCR1_DBG_DATA0;
    dmi_req_data1_cmb      = dmi_req  &  dmi_addr == SCR1_DBG_DATA1;

    dmi_req_command_cmb    = (dmi_req  &  dmi_addr == SCR1_DBG_COMMAND);
    dmi_rpt_command_cmb    = (abstractauto_execdata0_ff & dmi_req_data0_cmb);
    dmi_req_progbuf0_cmb   = dmi_req  &  dmi_addr == SCR1_DBG_PROGBUF0;
    dmi_req_progbuf1_cmb   = dmi_req  &  dmi_addr == SCR1_DBG_PROGBUF1;
    dmi_req_progbuf2_cmb   = dmi_req  &  dmi_addr == SCR1_DBG_PROGBUF2;
    dmi_req_progbuf3_cmb   = dmi_req  &  dmi_addr == SCR1_DBG_PROGBUF3;
    dmi_req_progbuf4_cmb   = dmi_req  &  dmi_addr == SCR1_DBG_PROGBUF4;
    dmi_req_progbuf5_cmb   = dmi_req  &  dmi_addr == SCR1_DBG_PROGBUF5;
end

// Register data multiplexor
always_comb begin
    dmi_rdata = 1'b0;

    if( dmi_addr == SCR1_DBG_DMSTATUS ) begin
        dmi_rdata[SCR1_DBG_DMSTATUS_RESERVEDC_HI:
                  SCR1_DBG_DMSTATUS_RESERVEDC_LO]       = DMSTATUS_RESERVEDC;

        dmi_rdata[SCR1_DBG_DMSTATUS_IMPEBREAK]          = DMSTATUS_IMPEBREAK;

        dmi_rdata[SCR1_DBG_DMSTATUS_RESERVEDB_HI:
                  SCR1_DBG_DMSTATUS_RESERVEDB_LO]       = DMSTATUS_RESERVEDB;

        dmi_rdata[SCR1_DBG_DMSTATUS_ALLHAVERESET]       = dmstatus_allany_havereset_ff;
        dmi_rdata[SCR1_DBG_DMSTATUS_ANYHAVERESET]       = dmstatus_allany_havereset_ff;
        dmi_rdata[SCR1_DBG_DMSTATUS_ALLRESUMEACK]       = dmstatus_allany_resumeack_ff;
        dmi_rdata[SCR1_DBG_DMSTATUS_ANYRESUMEACK]       = dmstatus_allany_resumeack_ff;
        dmi_rdata[SCR1_DBG_DMSTATUS_ALLNONEXISTENT]     = DMSTATUS_ALLANYNONEXIST;
        dmi_rdata[SCR1_DBG_DMSTATUS_ANYNONEXISTENT]     = DMSTATUS_ALLANYNONEXIST;
        dmi_rdata[SCR1_DBG_DMSTATUS_ALLUNAVAIL]         = DMSTATUS_ALLANYUNAVAIL;
        dmi_rdata[SCR1_DBG_DMSTATUS_ANYUNAVAIL]         = DMSTATUS_ALLANYUNAVAIL;
        dmi_rdata[SCR1_DBG_DMSTATUS_ALLRUNNING]         = ~dmstatus_allany_halted_ff;
        dmi_rdata[SCR1_DBG_DMSTATUS_ANYRUNNING]         = ~dmstatus_allany_halted_ff;
        dmi_rdata[SCR1_DBG_DMSTATUS_ALLHALTED]          = dmstatus_allany_halted_ff;
        dmi_rdata[SCR1_DBG_DMSTATUS_ANYHALTED]          = dmstatus_allany_halted_ff;
        dmi_rdata[SCR1_DBG_DMSTATUS_AUTHENTICATED]      = DMSTATUS_AUTHENTICATED;
        dmi_rdata[SCR1_DBG_DMSTATUS_AUTHBUSY]           = DMSTATUS_AUTHBUSY;
        dmi_rdata[SCR1_DBG_DMSTATUS_RESERVEDA]          = DMSTATUS_RESERVEDA;
        dmi_rdata[SCR1_DBG_DMSTATUS_DEVTREEVALID]       = DMSTATUS_DEVTREEVALID;

        dmi_rdata[SCR1_DBG_DMSTATUS_VERSION_HI:
                  SCR1_DBG_DMSTATUS_VERSION_LO]         = DMSTATUS_VERSION;;
    end
    if( dmi_addr == SCR1_DBG_DMCONTROL ) begin
        dmi_rdata[SCR1_DBG_DMCONTROL_HALTREQ]           = dmcontrol_haltreq_ff;
        dmi_rdata[SCR1_DBG_DMCONTROL_RESUMEREQ]         = dmcontrol_resumereq_ff;
        dmi_rdata[SCR1_DBG_DMCONTROL_HARTRESET]         = DMCONTROL_HARTRESET;
        dmi_rdata[SCR1_DBG_DMCONTROL_ACKHAVERESET]      = dmcontrol_ackhavereset_ff;
        dmi_rdata[SCR1_DBG_DMCONTROL_RESERVEDB]         = DMCONTROL_RESERVEDB;
        dmi_rdata[SCR1_DBG_DMCONTROL_HASEL]             = DMCONTROL_HASEL;

        dmi_rdata[SCR1_DBG_DMCONTROL_HARTSELLO_HI:
                  SCR1_DBG_DMCONTROL_HARTSELLO_LO]      = DMCONTROL_HARTSELLO;

        dmi_rdata[SCR1_DBG_DMCONTROL_HARTSELHI_HI:
                  SCR1_DBG_DMCONTROL_HARTSELHI_LO]      = DMCONTROL_HARTSELHI;

        dmi_rdata[SCR1_DBG_DMCONTROL_RESERVEDA_HI:
                  SCR1_DBG_DMCONTROL_RESERVEDA_LO]      = DMCONTROL_RESERVEDA;

        dmi_rdata[SCR1_DBG_DMCONTROL_NDMRESET]          = dmcontrol_ndmreset_ff;
        dmi_rdata[SCR1_DBG_DMCONTROL_DMACTIVE]          = dmcontrol_dmactive_ff;
    end
    if( dmi_addr == SCR1_DBG_ABSTRACTCS ) begin
        dmi_rdata[SCR1_DBG_ABSTRACTCS_RESERVEDD_HI:
                  SCR1_DBG_ABSTRACTCS_RESERVEDD_LO]     = ABSTRACTCS_RESERVEDD;

        dmi_rdata[SCR1_DBG_ABSTRACTCS_PROGBUFSIZE_HI:
                  SCR1_DBG_ABSTRACTCS_PROGBUFSIZE_LO]   = ABSTRACTCS_PROGBUFSIZE;

        dmi_rdata[SCR1_DBG_ABSTRACTCS_RESERVEDC_HI:
                  SCR1_DBG_ABSTRACTCS_RESERVEDC_LO]     = ABSTRACTCS_RESERVEDC;

        dmi_rdata[SCR1_DBG_ABSTRACTCS_BUSY]             = abstractcs_busy;
        dmi_rdata[SCR1_DBG_ABSTRACTCS_RESERVEDB]        = ABSTRACTCS_RESERVEDB;

        dmi_rdata[SCR1_DBG_ABSTRACTCS_CMDERR_HI:
                  SCR1_DBG_ABSTRACTCS_CMDERR_LO]        = abstractcs_cmderr_ff;

        dmi_rdata[SCR1_DBG_ABSTRACTCS_RESERVEDA_HI:
                  SCR1_DBG_ABSTRACTCS_RESERVEDA_LO]     = ABSTRACTCS_RESERVEDA;

        dmi_rdata[SCR1_DBG_ABSTRACTCS_DATACOUNT_HI:
                  SCR1_DBG_ABSTRACTCS_DATACOUNT_LO]     = ABSTRACTCS_DATACOUNT;
        end
    if( dmi_addr == SCR1_DBG_ABSTRACTAUTO ) begin
        dmi_rdata[0] = abstractauto_execdata0_ff;
    end
    if( dmi_addr == SCR1_DBG_DATA0 ) begin
        dmi_rdata = data0_ff;
    end
    if( dmi_addr == SCR1_DBG_DATA1 ) begin
        dmi_rdata = data1_ff;
    end

    if( dmi_addr == SCR1_DBG_PROGBUF0 ) begin
        dmi_rdata = progbuf0_ff;
    end
    if( dmi_addr == SCR1_DBG_PROGBUF1 ) begin
        dmi_rdata = progbuf1_ff;
    end
    if( dmi_addr == SCR1_DBG_PROGBUF2 ) begin
        dmi_rdata = progbuf2_ff;
    end
    if( dmi_addr == SCR1_DBG_PROGBUF3 ) begin
        dmi_rdata = progbuf3_ff;
    end
    if( dmi_addr == SCR1_DBG_PROGBUF4 ) begin
        dmi_rdata = progbuf4_ff;
    end
    if( dmi_addr == SCR1_DBG_PROGBUF5 ) begin
        dmi_rdata = progbuf5_ff;
    end
    if( dmi_addr == SCR1_DBG_HARTINFO ) begin
        dmi_rdata[SCR1_DBG_HARTINFO_RESERVEDB_HI:
                  SCR1_DBG_HARTINFO_RESERVEDB_LO]       = HARTINFO_RESERVEDB;

        dmi_rdata[SCR1_DBG_HARTINFO_NSCRATCH_HI:
                  SCR1_DBG_HARTINFO_NSCRATCH_LO]        = HARTINFO_NSCRATCH;

        dmi_rdata[SCR1_DBG_HARTINFO_RESERVEDA_HI:
                  SCR1_DBG_HARTINFO_RESERVEDA_LO]       = HARTINFO_RESERVEDA;

        dmi_rdata[SCR1_DBG_HARTINFO_DATAACCESS]         = HARTINFO_DATAACCESS;

        dmi_rdata[SCR1_DBG_HARTINFO_DATASIZE_HI:
                  SCR1_DBG_HARTINFO_DATASIZE_LO]        = HARTINFO_DATASIZE;

        dmi_rdata[SCR1_DBG_HARTINFO_DATAADDR_HI:
                  SCR1_DBG_HARTINFO_DATAADDR_LO]        = HARTINFO_DATAADDR;
    end
    if( dmi_addr == SCR1_DBG_HALTSUM0 ) begin
        dmi_rdata[0] = dmstatus_allany_halted_ff;
    end
end

// Response
always_comb dmi_resp = 1'b1;

// Clock enable and reset of Debug Module
// --------------------------------------
always_comb clk_en_dm_cmb = (dmi_req_dmcontrol_cmb & dmi_wr) |
                             dmcontrol_dmactive_ff | clk_en_dm_ff;

assign      hart_dmactive = clk_en_dm_ff;

always_ff @(posedge clk, negedge rst_n) begin
    if( ~rst_n ) begin
        dmcontrol_dmactive_ff <= 1'b0;
        clk_en_dm_ff          <= 1'b0;
    end else if( clk_en_dm_cmb ) begin
        if( dmi_req_dmcontrol_cmb & dmi_wr ) begin
            dmcontrol_dmactive_ff <= dmi_wdata[SCR1_DBG_DMCONTROL_DMACTIVE];
        end
        clk_en_dm_ff <= dmcontrol_dmactive_ff;
    end
end

// Reset
// -----

// NotDM reset request
always_ff @(posedge clk, negedge rst_n) begin
    if( ~rst_n ) begin
        dmcontrol_ndmreset_ff        <= 1'b0;
        dmcontrol_ackhavereset_ff    <= 1'b0;
    end else if( clk_en_dm_cmb ) begin
        if( ~dmcontrol_dmactive_ff ) begin
            dmcontrol_ndmreset_ff        <= 1'b0;
            dmcontrol_ackhavereset_ff    <= 1'b0;
        end else begin
            if( dmi_req_dmcontrol_cmb & dmi_wr ) begin
                dmcontrol_ndmreset_ff <= dmi_wdata[SCR1_DBG_DMCONTROL_NDMRESET];

                // Clear sticky NotDM reset status
                dmcontrol_ackhavereset_ff <= dmi_wdata[SCR1_DBG_DMCONTROL_ACKHAVERESET];
            end
        end
    end
end

// NotDM reset status
always_ff @(posedge clk, negedge rst_n) begin
    if( ~rst_n ) begin
        havereset_skip_pwrup_ff      <= 1'b1;
        dmstatus_allany_havereset_ff <= 1'b0;
    end else if( clk_en_dm_cmb ) begin
        if( ~dmcontrol_dmactive_ff ) begin
            havereset_skip_pwrup_ff      <= 1'b1;
            dmstatus_allany_havereset_ff <= 1'b0;
        end else begin
            if( havereset_skip_pwrup_ff ) begin
                havereset_skip_pwrup_ff <= hart_status.dbg_state == SCR1_HDU_DBGSTATE_RESET &
                                           ndm_rst_n & hart_rst_n;
            end

            if( ~havereset_skip_pwrup_ff &
                hart_status.dbg_state == SCR1_HDU_DBGSTATE_RESET ) begin

                dmstatus_allany_havereset_ff <= 1'b1;
            end else if( dmcontrol_ackhavereset_ff ) begin
                dmstatus_allany_havereset_ff <= 1'b0;
            end
        end
    end
end

// Reset signal for system controlled by Debug Module
assign hart_rst_n  = ~dmcontrol_ndmreset_ff;
assign ndm_rst_n   = ~dmcontrol_ndmreset_ff;

// Hart select
// -----------
// Only one hart (index 0) is currently supported

// Halt/Resume
// -----------

// Halt/Resume request
always_ff @(posedge clk, negedge rst_n) begin
    if( ~rst_n ) begin
        dmcontrol_haltreq_ff         <= 1'd0;
        dmcontrol_resumereq_ff       <= 1'd0;
    end else if( clk_en_dm_cmb ) begin
        if( ~dmcontrol_dmactive_ff ) begin
            dmcontrol_haltreq_ff         <= 1'd0;
            dmcontrol_resumereq_ff       <= 1'd0;
        end else begin
            if( dmi_req_dmcontrol_cmb & dmi_wr ) begin
                dmcontrol_haltreq_ff   <= dmi_wdata[SCR1_DBG_DMCONTROL_HALTREQ];
                dmcontrol_resumereq_ff <= dmi_wdata[SCR1_DBG_DMCONTROL_RESUMEREQ];
            end
        end
    end
end

// Halt status
always_ff @(posedge clk, negedge rst_n) begin
    if( ~rst_n ) begin
        dmstatus_allany_halted_ff <= 1'd0;
    end else if( clk_en_dm_cmb ) begin
        if( ~dmcontrol_dmactive_ff ) begin
            dmstatus_allany_halted_ff <= 1'd0;
        end else begin
            if( hart_status.dbg_state == SCR1_HDU_DBGSTATE_DHALTED ) begin
                dmstatus_allany_halted_ff <= 1'b1;
            end else if( hart_status.dbg_state == SCR1_HDU_DBGSTATE_RUN ) begin
                dmstatus_allany_halted_ff <= 1'b0;
            end
        end
    end
end

// Resume status
always_ff @(posedge clk, negedge rst_n) begin
    if( ~rst_n ) begin
        dmstatus_allany_resumeack_ff <= 1'd0;
    end else if( clk_en_dm_cmb ) begin
        if( ~dmcontrol_dmactive_ff ) begin
            dmstatus_allany_resumeack_ff <= 1'd0;
        end else begin
            if( ~dmcontrol_resumereq_ff ) begin
                dmstatus_allany_resumeack_ff <= 1'b0;
            end else if( hart_status.dbg_state == SCR1_HDU_DBGSTATE_RUN ) begin
                dmstatus_allany_resumeack_ff <= 1'b1;
            end
        end
    end
end

// Abstract Command
// ----------------

// Decode abstract command
always_comb begin
    if( dmi_req_command_cmb ) begin
       abs_cmd_regno_cmb        =  dmi_wdata[SCR1_DBG_COMMAND_ACCESSREG_REGNO_LO +: 12];

       abs_cmd_csr_ro_cmb       =  abs_cmd_regno_cmb == SCR1_CSR_ADDR_MISA |
                                   abs_cmd_regno_cmb == SCR1_CSR_ADDR_MVENDORID |
                                   abs_cmd_regno_cmb == SCR1_CSR_ADDR_MARCHID |
                                   abs_cmd_regno_cmb == SCR1_CSR_ADDR_MIMPID |
                                   abs_cmd_regno_cmb == SCR1_CSR_ADDR_MHARTID |
                                   abs_cmd_regno_cmb == SCR1_HDU_DBGCSR_ADDR_DPC;

        abs_cmd_cmb             = dmi_wdata[SCR1_DBG_COMMAND_TYPE_HI : SCR1_DBG_COMMAND_TYPE_LO];
        abs_cmd_regacs_cmb      = dmi_wdata[SCR1_DBG_COMMAND_ACCESSREG_TRANSFER];
        abs_cmd_regtype_cmb     = dmi_wdata[SCR1_DBG_COMMAND_ACCESSREG_REGNO_HI:12];
        abs_cmd_regfile_cmb     = dmi_wdata[11:5];
        abs_cmd_regsize_cmb     = dmi_wdata[SCR1_DBG_COMMAND_ACCESSREG_SIZE_HI : SCR1_DBG_COMMAND_ACCESSREG_SIZE_LO];
        abs_cmd_regwr_cmb       = dmi_wdata[SCR1_DBG_COMMAND_ACCESSREG_WRITE];
        abs_cmd_execprogbuf_cmb = dmi_wdata[SCR1_DBG_COMMAND_ACCESSREG_POSTEXEC];

        abs_cmd_regvalid_cmb    = dmi_wdata[SCR1_DBG_COMMAND_ACCESSREG_RESERVEDB] == 1'd0 &
                                  dmi_wdata[SCR1_DBG_COMMAND_ACCESSREG_RESERVEDA] == 1'd0;

        abs_cmd_memsize_cmb     = dmi_wdata[SCR1_DBG_COMMAND_ACCESSMEM_AAMSIZE_HI : SCR1_DBG_COMMAND_ACCESSMEM_AAMSIZE_LO];
        abs_cmd_memwr_cmb       = dmi_wdata[SCR1_DBG_COMMAND_ACCESSMEM_WRITE];

        abs_cmd_memvalid_cmb    = dmi_wdata[SCR1_DBG_COMMAND_ACCESSMEM_AAMVIRTUAL] == 1'd0 &
                                  dmi_wdata[SCR1_DBG_COMMAND_ACCESSMEM_AAMPOSTINC] == 1'd0 &
                                  dmi_wdata[SCR1_DBG_COMMAND_ACCESSMEM_RESERVEDB_HI:SCR1_DBG_COMMAND_ACCESSMEM_RESERVEDB_HI] == 1'd0 &
                                  dmi_wdata[SCR1_DBG_COMMAND_ACCESSMEM_RESERVEDA_HI:SCR1_DBG_COMMAND_ACCESSMEM_RESERVEDA_HI] == 1'd0;
    end else begin
       abs_cmd_regno_cmb        =  command_ff[SCR1_DBG_COMMAND_ACCESSREG_REGNO_LO +: 12];

       abs_cmd_csr_ro_cmb       =  abs_cmd_regno_cmb == SCR1_CSR_ADDR_MISA |
                                   abs_cmd_regno_cmb == SCR1_CSR_ADDR_MVENDORID |
                                   abs_cmd_regno_cmb == SCR1_CSR_ADDR_MARCHID |
                                   abs_cmd_regno_cmb == SCR1_CSR_ADDR_MIMPID |
                                   abs_cmd_regno_cmb == SCR1_CSR_ADDR_MHARTID |
                                   abs_cmd_regno_cmb == SCR1_HDU_DBGCSR_ADDR_DPC;

        abs_cmd_cmb             = command_ff[SCR1_DBG_COMMAND_TYPE_HI : SCR1_DBG_COMMAND_TYPE_LO];
        abs_cmd_regacs_cmb      = command_ff[SCR1_DBG_COMMAND_ACCESSREG_TRANSFER];
        abs_cmd_regtype_cmb     = command_ff[SCR1_DBG_COMMAND_ACCESSREG_REGNO_HI:12];
        abs_cmd_regfile_cmb     = command_ff[11:5];
        abs_cmd_regsize_cmb     = command_ff[SCR1_DBG_COMMAND_ACCESSREG_SIZE_HI : SCR1_DBG_COMMAND_ACCESSREG_SIZE_LO];
        abs_cmd_regwr_cmb       = command_ff[SCR1_DBG_COMMAND_ACCESSREG_WRITE];
        abs_cmd_execprogbuf_cmb = command_ff[SCR1_DBG_COMMAND_ACCESSREG_POSTEXEC];

        abs_cmd_regvalid_cmb    = command_ff[SCR1_DBG_COMMAND_ACCESSREG_RESERVEDB] == 1'd0 &
                                  command_ff[SCR1_DBG_COMMAND_ACCESSREG_RESERVEDA] == 1'd0;

        abs_cmd_memsize_cmb     = command_ff[SCR1_DBG_COMMAND_ACCESSMEM_AAMSIZE_HI : SCR1_DBG_COMMAND_ACCESSMEM_AAMSIZE_LO];
        abs_cmd_memwr_cmb       = command_ff[SCR1_DBG_COMMAND_ACCESSMEM_WRITE];

        abs_cmd_memvalid_cmb    = command_ff[SCR1_DBG_COMMAND_ACCESSMEM_AAMVIRTUAL] == 1'd0 &
                                  command_ff[SCR1_DBG_COMMAND_ACCESSMEM_AAMPOSTINC] == 1'd0 &
                                  command_ff[SCR1_DBG_COMMAND_ACCESSMEM_RESERVEDB_HI:SCR1_DBG_COMMAND_ACCESSMEM_RESERVEDB_HI] == 1'd0 &
                                  command_ff[SCR1_DBG_COMMAND_ACCESSMEM_RESERVEDA_HI:SCR1_DBG_COMMAND_ACCESSMEM_RESERVEDA_HI] == 1'd0;
    end
end

assign abs_cmd_regsize_valid_cmb =  abs_cmd_regsize_cmb == 2'd2;
assign abs_cmd_memsize_valid_cmb = (abs_cmd_memsize_cmb <  3'd3) ? 1'b1 : 1'b0;


// Detect error while abstract command processing
always_comb begin
    abs_err_exception_cmb = abs_fsm_ff != ABS_STATE_IDLE &
                            dhi_resp_cmb & dhi_resp_exception_cmb ? 1'b1 :
                            abs_fsm_ff == ABS_STATE_IDLE          ? 1'b0 :
                                                                    abs_err_exception_ff;

    abs_err_acc_busy_cmb = abs_fsm_ff != ABS_STATE_IDLE &
                           ( dmi_req_command_cmb |
                             dmi_rpt_command_cmb |
                             dmi_req_abstractauto_cmb |
                             dmi_req_data0_cmb   |
                             dmi_req_data1_cmb   |
                             dmi_req_progbuf0_cmb |
                             dmi_req_progbuf1_cmb |
                             dmi_req_progbuf2_cmb |
                             dmi_req_progbuf3_cmb |
                             dmi_req_progbuf4_cmb |
                             dmi_req_progbuf5_cmb ) ? 1'b1 :
                             abs_fsm_ff == ABS_STATE_IDLE ? 1'b0 :
                                                            abs_err_acc_busy_ff;
end

// Abstract command fsm
always_comb begin
    abs_data0_cmb      = data0_ff;
    abs_data1_cmb      = data1_ff;
    abs_command_cmb    = command_ff;
    abs_abstractauto_execdata0_cmb = abstractauto_execdata0_ff;
    abs_progbuf0_cmb   = progbuf0_ff;
    abs_progbuf1_cmb   = progbuf1_ff;
    abs_progbuf2_cmb   = progbuf2_ff;
    abs_progbuf3_cmb   = progbuf3_ff;
    abs_progbuf4_cmb   = progbuf4_ff;
    abs_progbuf5_cmb   = progbuf5_ff;
    abs_cmderr_cmb     = abstractcs_cmderr_ff;
    abs_cmd_wr_cmb     = 1'b0;
    abs_cmd_postexec_cmb = 1'b0;
    abs_cmd_size_cmb   = abs_cmd_size_ff;
    abs_exec_req_cmb   = 1'b0;
    abs_exec_instr_cmb = abs_exec_instr_ff;
    abs_fsm_cmb        = abs_fsm_ff;
    abstractcs_busy    = abs_fsm_ff != ABS_STATE_IDLE  &  abs_fsm_ff != ABS_STATE_ERR;

    // Wait for command request
    if( abs_fsm_ff == ABS_STATE_IDLE ) begin
        if( dmi_req_data0_cmb & dmi_wr ) begin
            abs_data0_cmb = dmi_wdata;
        end
        if( dmi_req_data1_cmb & dmi_wr ) begin
            abs_data1_cmb = dmi_wdata;
        end
        if( dmi_req_command_cmb & dmi_wr ) begin
            abs_command_cmb = dmi_wdata;
        end
        if( dmi_req_abstractauto_cmb & dmi_wr ) begin
            abs_abstractauto_execdata0_cmb = dmi_wdata[0];
        end
        if( dmi_req_progbuf0_cmb & dmi_wr ) begin
            abs_progbuf0_cmb = dmi_wdata;
        end
        if( dmi_req_progbuf1_cmb & dmi_wr ) begin
            abs_progbuf1_cmb = dmi_wdata;
        end
        if( dmi_req_progbuf2_cmb & dmi_wr ) begin
            abs_progbuf2_cmb = dmi_wdata;
        end
        if( dmi_req_progbuf3_cmb & dmi_wr ) begin
            abs_progbuf3_cmb = dmi_wdata;
        end
        if( dmi_req_progbuf4_cmb & dmi_wr ) begin
            abs_progbuf4_cmb = dmi_wdata;
        end
        if( dmi_req_progbuf5_cmb & dmi_wr ) begin
            abs_progbuf5_cmb = dmi_wdata;
        end

        if( (dmi_req_command_cmb & dmi_wr) | dmi_rpt_command_cmb ) begin
            // HART int/csr access or Program Buffer execute
            if ( (abs_cmd_cmb == ABS_CMD_HARTREG) & abs_cmd_regvalid_cmb ) begin
                // HART int/csr access
                if( abs_cmd_regacs_cmb ) begin
                    // HART csr access
                    if( abs_cmd_regtype_cmb == ABS_CMD_HARTREG_CSR ) begin
                        if( abs_cmd_regsize_valid_cmb ) begin
                            if( abs_cmd_regwr_cmb ) begin
                                if( hart_status.dbg_state == SCR1_HDU_DBGSTATE_DHALTED ) begin
                                    abs_cmd_wr_cmb       = 1'b1;
                                    abs_cmd_postexec_cmb = abs_cmd_execprogbuf_cmb;
                                    abs_fsm_cmb       = ABS_STATE_CSR_SAVE_XREG;
                                end else begin
                                    abs_cmderr_cmb = ABS_ERR_NOHALT;
                                    abs_fsm_cmb    = ABS_STATE_ERR;
                                end
                            end else begin
                                if( hart_status.dbg_state == SCR1_HDU_DBGSTATE_RUN &
                                    abs_cmd_csr_ro_cmb & ~abs_cmd_execprogbuf_cmb ) begin
                                    abs_fsm_cmb  = ABS_STATE_CSR_RO;
                                end else if( hart_status.dbg_state == SCR1_HDU_DBGSTATE_DHALTED ) begin
                                    abs_cmd_postexec_cmb = abs_cmd_execprogbuf_cmb;
                                    abs_fsm_cmb = ABS_STATE_CSR_SAVE_XREG;
                                end else begin
                                    abs_cmderr_cmb = ABS_ERR_NOHALT;
                                    abs_fsm_cmb    = ABS_STATE_ERR;
                                end
                            end
                        end else begin
                            abs_cmderr_cmb = ABS_ERR_CMD;
                            abs_fsm_cmb    = ABS_STATE_ERR;
                        end
                    end
                    // HART int/fpu regfile access
                    else if( abs_cmd_regtype_cmb == ABS_CMD_HARTREG_INTFPU ) begin
                        // HART int regfile access
                        if( abs_cmd_regfile_cmb == ABS_CMD_HARTREG_INT ) begin
                            if( abs_cmd_regsize_valid_cmb ) begin
                                if( hart_status.dbg_state == SCR1_HDU_DBGSTATE_DHALTED ) begin
                                    abs_cmd_wr_cmb    = abs_cmd_regwr_cmb;
                                    abs_cmd_size_cmb     = abs_cmd_regsize_cmb[1:0];
                                    abs_cmd_postexec_cmb = abs_cmd_execprogbuf_cmb;
                                    abs_fsm_cmb       = ABS_STATE_XREG_RW;
                                end else begin
                                    abs_cmderr_cmb = ABS_ERR_NOHALT;
                                    abs_fsm_cmb    = ABS_STATE_ERR;
                                end
                            end else begin
                                abs_cmderr_cmb = ABS_ERR_CMD;
                                abs_fsm_cmb    = ABS_STATE_ERR;
                            end
                        end
                        // Error command
                        else begin
                            abs_cmderr_cmb = ABS_ERR_CMD;
                            abs_fsm_cmb    = ABS_STATE_ERR;
                        end
                    end
                    // Error command
                    else begin
                        abs_cmderr_cmb = ABS_ERR_CMD;
                        abs_fsm_cmb    = ABS_STATE_ERR;
                    end
                end
                // Program buffer execute
                else if( abs_cmd_execprogbuf_cmb ) begin
                    abs_fsm_cmb = ABS_STATE_EXEC;
                end
                // Error command
                else begin
                    abs_cmderr_cmb = ABS_ERR_CMD;
                    abs_fsm_cmb    = ABS_STATE_ERR;
                end
            end
            // HART memory access
            else if ( (abs_cmd_cmb == ABS_CMD_HARTMEM) & abs_cmd_memvalid_cmb ) begin
                if( abs_cmd_memsize_valid_cmb ) begin
                    if( hart_status.dbg_state == SCR1_HDU_DBGSTATE_DHALTED ) begin
                        abs_cmd_wr_cmb    = abs_cmd_memwr_cmb;
                        abs_cmd_size_cmb  = abs_cmd_memsize_cmb[1:0];
                        abs_fsm_cmb       = ABS_STATE_MEM_SAVE_XREG;
                    end else begin
                        abs_cmderr_cmb    = ABS_ERR_NOHALT;
                        abs_fsm_cmb       = ABS_STATE_ERR;
                    end
                end else begin
                    abs_cmderr_cmb = ABS_ERR_CMD;
                    abs_fsm_cmb    = ABS_STATE_ERR;
                end
            end
            // Error command
            else begin
                abs_cmderr_cmb = ABS_ERR_CMD;
                abs_fsm_cmb    = ABS_STATE_ERR;
            end
        end
    end

    // Execute Program Buffer
    else if( abs_fsm_ff == ABS_STATE_EXEC ) begin
        abs_exec_req_cmb   = ~dhi_resp_cmb;

        if( hart_dreg_req & hart_dreg_wr ) begin
            abs_data0_cmb = hart_dreg_wdata;
        end

        if( dhi_resp_cmb ) begin
            if( dhi_resp_exception_cmb ) begin
                abs_cmderr_cmb = ABS_ERR_EXCEPTION;
                abs_fsm_cmb    = ABS_STATE_ERR;
            end else if( abs_err_acc_busy_ff ) begin
                abs_cmderr_cmb = ABS_ERR_BUSY;
                abs_fsm_cmb    = ABS_STATE_ERR;
            end else begin
                abs_fsm_cmb    = ABS_STATE_IDLE;
            end
        end
    end

    // Access to int regfile
    else if( abs_fsm_ff == ABS_STATE_XREG_RW ) begin
        abs_exec_req_cmb   = ~dhi_resp_cmb;
        abs_exec_instr_cmb = { SCR1_HDU_DBGCSR_ADDR_DSCRATCH0,
                               abs_cmd_wr_ff ? 5'd0 : abs_cmd_regno_ff[4:0],
                               3'b001,
                               abs_cmd_wr_ff ? abs_cmd_regno_ff[4:0] : 5'd0,
                               7'b111_0011 };

        if( hart_dreg_req & hart_dreg_wr & ~abs_cmd_wr_ff ) begin
            abs_data0_cmb = hart_dreg_wdata;
        end

        if( dhi_resp_cmb ) begin
            if( abs_err_acc_busy_ff ) begin
                abs_cmderr_cmb = ABS_ERR_BUSY;
                abs_fsm_cmb    = ABS_STATE_ERR;
            end else if( abs_cmd_postexec_ff ) begin
                abs_fsm_cmb    = ABS_STATE_EXEC;
            end else begin
                abs_fsm_cmb    = ABS_STATE_IDLE;
            end
        end
    end

    // Access to CSR
    else if( abs_fsm_ff == ABS_STATE_CSR_RO ) begin
        abs_data0_cmb = abs_cmd_regno_ff[11:0] == SCR1_CSR_ADDR_MISA       ? SCR1_CSR_MISA :
                        abs_cmd_regno_ff[11:0] == SCR1_CSR_ADDR_MVENDORID  ? SCR1_CSR_MVENDORID :
                        abs_cmd_regno_ff[11:0] == SCR1_CSR_ADDR_MARCHID    ? SCR1_CSR_MARCHID :
                        abs_cmd_regno_ff[11:0] == SCR1_CSR_ADDR_MIMPID     ? SCR1_CSR_MIMPID :
                        abs_cmd_regno_ff[11:0] == SCR1_CSR_ADDR_MHARTID    ? ro_fuse_mhartid :
                                                                                 ro_pc;

        if( abs_err_acc_busy_ff ) begin
            abs_cmderr_cmb = ABS_ERR_BUSY;
            abs_fsm_cmb    = ABS_STATE_ERR;
        end else begin
            abs_fsm_cmb    = ABS_STATE_IDLE;
        end
    end
    else if( abs_fsm_ff == ABS_STATE_CSR_SAVE_XREG ) begin
        abs_exec_req_cmb   = ~dhi_resp_cmb;
        abs_exec_instr_cmb = { SCR1_HDU_DBGCSR_ADDR_DSCRATCH0,
                               5'd5,
                               3'b001,
                               abs_cmd_wr_ff ? 5'd5 : 5'd0,
                               7'b111_0011 };

        if( hart_dreg_req & hart_dreg_wr ) begin
            abs_data0_cmb = hart_dreg_wdata;
        end

        if( dhi_resp_cmb ) begin
            abs_fsm_cmb    = ABS_STATE_CSR_RW;
        end
    end
    else if( abs_fsm_ff == ABS_STATE_CSR_RW ) begin
        abs_exec_req_cmb   = ~dhi_resp_cmb;
        abs_exec_instr_cmb = { abs_cmd_regno_ff[11:0],
                               abs_cmd_wr_ff ? 5'd5 : 5'd0,
                               abs_cmd_wr_ff ? 3'b001 : 3'b010,
                               abs_cmd_wr_ff ? 5'd0 : 5'd5,
                               7'b111_0011 };

        if( dhi_resp_cmb ) begin
            abs_fsm_cmb    = ABS_STATE_CSR_RETURN_XREG;
        end
    end
    else if( abs_fsm_ff == ABS_STATE_CSR_RETURN_XREG ) begin
        abs_exec_req_cmb   = ~dhi_resp_cmb;
        abs_exec_instr_cmb = { SCR1_HDU_DBGCSR_ADDR_DSCRATCH0,
    //                           abs_cmd_wr_ff ? 5'd0 : 5'd5,
                               5'd5,
                               3'b001,
                               5'd5,
                               7'b111_0011 };

        if( hart_dreg_req & hart_dreg_wr ) begin
            abs_data0_cmb = hart_dreg_wdata;
        end

        if( dhi_resp_cmb ) begin
            if( abs_err_exception_ff ) begin
                abs_cmderr_cmb = ABS_ERR_EXCEPTION;
                abs_fsm_cmb    = ABS_STATE_ERR;
            end else if( abs_err_acc_busy_ff ) begin
                abs_cmderr_cmb = ABS_ERR_BUSY;
                abs_fsm_cmb    = ABS_STATE_ERR;
            end else if( abs_cmd_postexec_ff ) begin
                abs_fsm_cmb    = ABS_STATE_EXEC;
            end else begin
                abs_fsm_cmb    = ABS_STATE_IDLE;
            end
        end
    end

    // Access to memory
    else if( abs_fsm_ff == ABS_STATE_MEM_SAVE_XREG ) begin
        abs_exec_req_cmb   = ~dhi_resp_cmb;
        abs_exec_instr_cmb = { SCR1_HDU_DBGCSR_ADDR_DSCRATCH0,
                               5'd5,
                               3'b001,
                               abs_cmd_wr_ff ? 5'd5 : 5'd0,
                               7'b111_0011 };

        if( hart_dreg_req & hart_dreg_wr ) begin
            abs_data0_cmb = hart_dreg_wdata;
        end

        if( dhi_resp_cmb ) begin
            abs_fsm_cmb = ABS_STATE_MEM_SAVE_XREG_FORADDR;
        end
    end
    else if( abs_fsm_ff == ABS_STATE_MEM_SAVE_XREG_FORADDR ) begin
        abs_exec_req_cmb   = ~dhi_resp_cmb;
        abs_exec_instr_cmb = { SCR1_HDU_DBGCSR_ADDR_DSCRATCH0,
                               5'd6,
                               3'b001,
                               5'd6,
                               7'b111_0011 };

        if( hart_dreg_req & hart_dreg_wr ) begin
            abs_data1_cmb = hart_dreg_wdata;
        end

        if( dhi_resp_cmb ) begin
            abs_fsm_cmb = ABS_STATE_MEM_RW;
        end
    end
    else if( abs_fsm_ff == ABS_STATE_MEM_RW ) begin
        abs_exec_req_cmb   = ~dhi_resp_cmb;
        if( abs_cmd_wr_ff ) begin
            abs_exec_instr_cmb = { 7'd0,
                                   5'd5,
                                   5'd6,
                                   {1'b0,abs_cmd_size_ff},
                                   5'd0,
                                   7'b010_0011 };
        end else begin
            abs_exec_instr_cmb = { 12'd0,
                                   5'd6,
                                   {abs_cmd_size_ff == 2'b10 ? 1'b0 : 1'b1,
                                   abs_cmd_size_ff},
                                   5'd5,
                                   7'b000_0011 };
        end

        if( dhi_resp_cmb ) begin
            abs_fsm_cmb = ABS_STATE_MEM_RETURN_XREG;
        end
    end
    else if( abs_fsm_ff == ABS_STATE_MEM_RETURN_XREG ) begin
        abs_exec_req_cmb   = ~dhi_resp_cmb;
        abs_exec_instr_cmb = { SCR1_HDU_DBGCSR_ADDR_DSCRATCH0,
                               5'd5,
                               3'b001,
                               5'd5,
                               7'b111_0011 };

        if( hart_dreg_req & hart_dreg_wr ) begin
            abs_data0_cmb = hart_dreg_wdata;
        end

        if( dhi_resp_cmb ) begin
            abs_fsm_cmb = ABS_STATE_MEM_RETURN_XREG_FORADDR;
        end
    end
    else if( abs_fsm_ff == ABS_STATE_MEM_RETURN_XREG_FORADDR ) begin
        abs_exec_req_cmb   = ~dhi_resp_cmb;
        abs_exec_instr_cmb = { SCR1_HDU_DBGCSR_ADDR_DSCRATCH0,
                               5'd6,
                               3'b001,
                               5'd6,
                               7'b111_0011 };

        if( hart_dreg_req & hart_dreg_wr ) begin
            abs_data1_cmb = hart_dreg_wdata;
        end

        if( dhi_resp_cmb ) begin
            if( abs_err_exception_ff ) begin
                abs_cmderr_cmb = ABS_ERR_EXCEPTION;
                abs_fsm_cmb    = ABS_STATE_ERR;
            end else if( abs_err_acc_busy_ff ) begin
                abs_cmderr_cmb = ABS_ERR_BUSY;
                abs_fsm_cmb    = ABS_STATE_ERR;
            end else if( abs_cmd_postexec_ff ) begin
                abs_fsm_cmb    = ABS_STATE_EXEC;
            end else begin
                abs_fsm_cmb    = ABS_STATE_IDLE;
            end
        end
    end

    // Wait for error state will be resolved
    else if( abs_fsm_ff == ABS_STATE_ERR ) begin
        if( dmi_req_abstractcs_cmb & dmi_wr ) begin

            abs_cmderr_cmb  = abstractcs_cmderr_ff &
                              (~dmi_wdata[SCR1_DBG_ABSTRACTCS_CMDERR_HI:
                                          SCR1_DBG_ABSTRACTCS_CMDERR_LO]);

            if( abs_cmderr_cmb == 1'b0 ) begin
                abs_fsm_cmb = ABS_STATE_IDLE;
            end
        end
    end

    // Unexpected hart reset processing like exception
    if( abs_fsm_ff != ABS_STATE_IDLE &
        hart_status.dbg_state == SCR1_HDU_DBGSTATE_RESET ) begin

        abs_cmderr_cmb = ABS_ERR_EXCEPTION;
        abs_fsm_cmb    = ABS_STATE_ERR;
    end
end

// Regs with init with dmcontrol_dmactive_ff=0
always_ff @(posedge clk) begin
    if( clk_en_dm_cmb ) begin
        if( ~dmcontrol_dmactive_ff ) begin
            abs_exec_req_ff      <= 1'd0;
            abs_fsm_ff           <= ABS_STATE_IDLE;
            abstractcs_cmderr_ff <= 1'd0;
            abstractauto_execdata0_ff <= 1'b0;
            command_ff           <= 1'b0;
        end else begin
            abs_exec_req_ff      <= abs_exec_req_cmb;
            abs_fsm_ff           <= abs_fsm_cmb;
            abstractcs_cmderr_ff <= abs_cmderr_cmb;
            abstractauto_execdata0_ff <= abs_abstractauto_execdata0_cmb;
            command_ff           <= abs_command_cmb;
        end
    end
end

// Regs without init when dmcontrol_dmactive_ff=0
always_ff @(posedge clk) begin
    if( clk_en_dm_cmb ) begin
        if( dmcontrol_dmactive_ff ) begin
            if( abs_fsm_ff == ABS_STATE_IDLE ) begin
                abs_cmd_postexec_ff <= abs_cmd_postexec_cmb;
                abs_cmd_wr_ff     <= abs_cmd_wr_cmb;
                abs_cmd_regno_ff  <= abs_cmd_regno_cmb;
                abs_cmd_size_ff   <= abs_cmd_size_cmb;
            end
            abs_err_exception_ff  <= abs_err_exception_cmb;
            abs_err_acc_busy_ff   <= abs_err_acc_busy_cmb;

            abs_exec_instr_ff     <= abs_exec_instr_cmb;
            data0_ff              <= abs_data0_cmb;
            data1_ff              <= abs_data1_cmb;

            progbuf0_ff           <= abs_progbuf0_cmb;
            progbuf1_ff           <= abs_progbuf1_cmb;
            progbuf2_ff           <= abs_progbuf2_cmb;
            progbuf3_ff           <= abs_progbuf3_cmb;
            progbuf4_ff           <= abs_progbuf4_cmb;
            progbuf5_ff           <= abs_progbuf5_cmb;
        end
    end
end

// Debug Hart Interface : control
// ------------------------------

// DHI fsm internal interface
always_comb begin
    // Request
    dhi_req_cmb  = DHI_STATE_IDLE;
    if( abs_exec_req_ff ) begin
        dhi_req_cmb = DHI_STATE_EXEC;
    end
    if( dmcontrol_haltreq_ff &
        hart_status.dbg_state != SCR1_HDU_DBGSTATE_DHALTED ) begin

        dhi_req_cmb = DHI_STATE_HALT_REQ;
    end
    if( dmcontrol_resumereq_ff & ~dmstatus_allany_resumeack_ff &
        hart_status.dbg_state == SCR1_HDU_DBGSTATE_DHALTED ) begin

        dhi_req_cmb = DHI_STATE_RESUME_REQ;
    end

    // Response
    dhi_resp_cmb           = dhi_fsm_ff == DHI_STATE_EXEC_HALT  &
                             hart_status.dbg_state == SCR1_HDU_DBGSTATE_DHALTED;

    dhi_resp_exception_cmb = hart_event & hart_status.except & ~hart_status.ebreak;
end

// DHI fsm
always_comb begin
    hart_cmd_req_cmb = 1'b0;
    hart_cmd_cmb     = hart_cmd;
    dhi_fsm_cmb      = dhi_fsm_ff;

    // Wait for debug requests
    if( dhi_fsm_ff == DHI_STATE_IDLE ) begin
        dhi_fsm_cmb = dhi_req_cmb;
    end

    // Execute instruction in debug run
    else if( dhi_fsm_ff == DHI_STATE_EXEC ) begin // Request for debug run
            hart_cmd_req_cmb = ~(hart_cmd_resp & ~hart_cmd_rcode);
            hart_cmd_cmb     = SCR1_HDU_DBGSTATE_DRUN;
            if( hart_cmd_resp & ~hart_cmd_rcode ) begin
                dhi_fsm_cmb = DHI_STATE_EXEC_RUN;
            end
        end
    else if( dhi_fsm_ff == DHI_STATE_EXEC_RUN ) begin // Wait for debug run
        if( hart_status.dbg_state == SCR1_HDU_DBGSTATE_DRUN ) begin
            dhi_fsm_cmb = DHI_STATE_EXEC_HALT;
        end
    end

    // Halt
    else if( dhi_fsm_ff == DHI_STATE_HALT_REQ ) begin // Request for halt hart
            hart_cmd_req_cmb = ~(hart_cmd_resp & ~hart_cmd_rcode);
            hart_cmd_cmb     = SCR1_HDU_DBGSTATE_DHALTED;

            if( hart_cmd_resp & ~hart_cmd_rcode ) begin
                dhi_fsm_cmb = DHI_STATE_EXEC_HALT;
            end
        end

    // Wait for HART halt
    else if( dhi_fsm_ff == DHI_STATE_EXEC_HALT ) begin
        if( hart_status.dbg_state == SCR1_HDU_DBGSTATE_DHALTED ) begin
            dhi_fsm_cmb = DHI_STATE_IDLE;
        end
    end

    // Resume
    else if( dhi_fsm_ff == DHI_STATE_RESUME_REQ ) begin // Request for hart run
            hart_cmd_req_cmb = ~(hart_cmd_resp & ~hart_cmd_rcode);
            hart_cmd_cmb     = SCR1_HDU_DBGSTATE_RUN;

            if( hart_cmd_resp & ~hart_cmd_rcode ) begin
                dhi_fsm_cmb = DHI_STATE_RESUME_RUN;
            end
        end
    else if( dhi_fsm_ff == DHI_STATE_RESUME_RUN ) begin // Wait for hart run
        if( hart_status.dbg_state == SCR1_HDU_DBGSTATE_RUN ) begin
            dhi_fsm_cmb = DHI_STATE_IDLE;
        end
    end

    // Unexpected hart reset
    if( dhi_fsm_ff != DHI_STATE_IDLE &
        dhi_fsm_ff != DHI_STATE_HALT_REQ &
        hart_status.dbg_state == SCR1_HDU_DBGSTATE_RESET ) begin

        dhi_fsm_cmb = DHI_STATE_IDLE;
    end
end

always_ff @(posedge clk, negedge rst_n) begin
    if( ~rst_n ) begin
        hart_cmd_req <= 1'd0;
        hart_cmd     <= SCR1_HDU_DBGSTATE_RUN;

        dhi_fsm_ff   <= DHI_STATE_IDLE;
    end else if( clk_en_dm_cmb ) begin
        if( ~dmcontrol_dmactive_ff ) begin
            hart_cmd_req <= 1'd0;
            hart_cmd     <= SCR1_HDU_DBGSTATE_RUN;

            dhi_fsm_ff   <= DHI_STATE_IDLE;
        end else begin
            hart_cmd_req <= hart_cmd_req_cmb;
            hart_cmd     <= hart_cmd_cmb;

            dhi_fsm_ff   <= dhi_fsm_cmb;
        end
    end
end

// Debug Hart Interface : program buffer
// -------------------------------------

always_comb begin
    hart_pbuf_instr = ABS_EXEC_EBREAK;

    if( abs_fsm_ff == ABS_STATE_EXEC & ~hart_pbuf_ebreak_ff ) begin
        if( hart_pbuf_addr == 1'd0 ) hart_pbuf_instr = progbuf0_ff;
        if( hart_pbuf_addr == 1'd1 ) hart_pbuf_instr = progbuf1_ff;
        if( hart_pbuf_addr == 2'd2 ) hart_pbuf_instr = progbuf2_ff;
        if( hart_pbuf_addr == 2'd3 ) hart_pbuf_instr = progbuf3_ff;
        if( hart_pbuf_addr == 3'd4 ) hart_pbuf_instr = progbuf4_ff;
        if( hart_pbuf_addr == 3'd5 ) hart_pbuf_instr = progbuf5_ff;
    end else if( hart_pbuf_addr == 1'b0 ) hart_pbuf_instr = abs_exec_instr_ff;
end

// Latch EBREAK condition when program buffer execution
always_ff @(posedge clk) begin
    if( clk_en_dm_cmb ) begin
        hart_pbuf_ebreak_ff <= abs_fsm_ff == ABS_STATE_EXEC &
                               hart_pbuf_instr == ABS_EXEC_EBREAK;
    end
end

// Debug Hart Interface : abstract command data
// --------------------------------------------

always_comb hart_dreg_resp     = 1'b1;
always_comb hart_dreg_fail     = 1'b0;
always_comb hart_dreg_rdata    = abs_fsm_ff == ABS_STATE_MEM_SAVE_XREG_FORADDR |
                                 abs_fsm_ff == ABS_STATE_MEM_RETURN_XREG_FORADDR ? data1_ff : data0_ff;

// pragma synthesis_off
// synopsys translate_off

// Assertions
// ----------
`ifndef VERILATOR
SVA_DM_X_CONTROL :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        !$isunknown( {rst_n,clk,dmi_req,hart_dreg_req,hart_cmd_resp,hart_event} )
    )
    else $error("DM error: control signals is X - %0b",{rst_n,clk,dmi_req,hart_dreg_req,hart_cmd_resp,hart_event});

SVA_DM_X_DMI :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        dmi_req |-> !$isunknown( {dmi_wr,dmi_addr,dmi_wdata} )
    )
    else $error("DM error: data signals is X on dmi");

SVA_DM_X_HART_PBUF :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        !$isunknown( hart_pbuf_addr )
    )
    else $error("DM error: data signals is X on hart_pbuf");

SVA_DM_X_HART_DREG :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        hart_dreg_req |-> !$isunknown( {hart_dreg_wr,hart_dreg_wdata} )
    )
    else $error("DM error: data signals is X on hart_dreg");

SVA_DM_X_HART_CMD :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        hart_cmd_resp |-> !$isunknown( {hart_cmd_rcode} )
    )
    else $error("DM error: data signals is X on hart_cmd");

SVA_DM_X_HART_EVENT :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        hart_event |-> !$isunknown( hart_status )
    )
    else $error("DM error: data signals is X on hart_event");
`endif // ! VERILATOR
// synopsys translate_on
// pragma synthesis_on

endmodule : scr1_dm

`endif // SCR1_DBGC_EN