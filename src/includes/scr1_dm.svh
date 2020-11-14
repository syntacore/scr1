/// Copyright by Syntacore LLC © 2016-2020. See LICENSE for details
/// @file       <scr1_dm.svh>
/// @brief      Debug Module header file
///

`ifndef SCR1_INCLUDE_DM_DEFS
`define SCR1_INCLUDE_DM_DEFS

`include "scr1_arch_description.svh"
`include "scr1_hdu.svh"
`include "scr1_csr.svh"

parameter SCR1_DBG_DMI_ADDR_WIDTH                  = 6'd7;
parameter SCR1_DBG_DMI_DATA_WIDTH                  = 6'd32;
parameter SCR1_DBG_DMI_OP_WIDTH                    = 2'd2;

parameter SCR1_DBG_DMI_CH_ID_WIDTH                 = 2'd2;
parameter SCR1_DBG_DMI_DR_DTMCS_WIDTH              = 6'd32;
parameter SCR1_DBG_DMI_DR_DMI_ACCESS_WIDTH         = SCR1_DBG_DMI_OP_WIDTH +
                                                     SCR1_DBG_DMI_DATA_WIDTH +
                                                     SCR1_DBG_DMI_ADDR_WIDTH;

// Debug Module addresses
parameter SCR1_DBG_DATA0                           = 7'h4;
parameter SCR1_DBG_DATA1                           = 7'h5;
parameter SCR1_DBG_DMCONTROL                       = 7'h10;
parameter SCR1_DBG_DMSTATUS                        = 7'h11;
parameter SCR1_DBG_HARTINFO                        = 7'h12;
parameter SCR1_DBG_ABSTRACTCS                      = 7'h16;
parameter SCR1_DBG_COMMAND                         = 7'h17;
parameter SCR1_DBG_ABSTRACTAUTO                    = 7'h18;
parameter SCR1_DBG_PROGBUF0                        = 7'h20;
parameter SCR1_DBG_PROGBUF1                        = 7'h21;
parameter SCR1_DBG_PROGBUF2                        = 7'h22;
parameter SCR1_DBG_PROGBUF3                        = 7'h23;
parameter SCR1_DBG_PROGBUF4                        = 7'h24;
parameter SCR1_DBG_PROGBUF5                        = 7'h25;
parameter SCR1_DBG_HALTSUM0                        = 7'h40;

// DMCONTROL
parameter SCR1_DBG_DMCONTROL_HALTREQ               = 5'd31;
parameter SCR1_DBG_DMCONTROL_RESUMEREQ             = 5'd30;
parameter SCR1_DBG_DMCONTROL_HARTRESET             = 5'd29;
parameter SCR1_DBG_DMCONTROL_ACKHAVERESET          = 5'd28;
parameter SCR1_DBG_DMCONTROL_RESERVEDB             = 5'd27;
parameter SCR1_DBG_DMCONTROL_HASEL                 = 5'd26;
parameter SCR1_DBG_DMCONTROL_HARTSELLO_HI          = 5'd25;
parameter SCR1_DBG_DMCONTROL_HARTSELLO_LO          = 5'd16;
parameter SCR1_DBG_DMCONTROL_HARTSELHI_HI          = 5'd15;
parameter SCR1_DBG_DMCONTROL_HARTSELHI_LO          = 5'd6;
parameter SCR1_DBG_DMCONTROL_RESERVEDA_HI          = 5'd5;
parameter SCR1_DBG_DMCONTROL_RESERVEDA_LO          = 5'd2;
parameter SCR1_DBG_DMCONTROL_NDMRESET              = 5'd1;
parameter SCR1_DBG_DMCONTROL_DMACTIVE              = 5'd0;

// DMSTATUS
parameter SCR1_DBG_DMSTATUS_RESERVEDC_HI           = 5'd31;
parameter SCR1_DBG_DMSTATUS_RESERVEDC_LO           = 5'd23;
parameter SCR1_DBG_DMSTATUS_IMPEBREAK              = 5'd22;
parameter SCR1_DBG_DMSTATUS_RESERVEDB_HI           = 5'd21;
parameter SCR1_DBG_DMSTATUS_RESERVEDB_LO           = 5'd20;
parameter SCR1_DBG_DMSTATUS_ALLHAVERESET           = 5'd19;
parameter SCR1_DBG_DMSTATUS_ANYHAVERESET           = 5'd18;
parameter SCR1_DBG_DMSTATUS_ALLRESUMEACK           = 5'd17;
parameter SCR1_DBG_DMSTATUS_ANYRESUMEACK           = 5'd16;
parameter SCR1_DBG_DMSTATUS_ALLNONEXISTENT         = 5'd15;
parameter SCR1_DBG_DMSTATUS_ANYNONEXISTENT         = 5'd14;
parameter SCR1_DBG_DMSTATUS_ALLUNAVAIL             = 5'd13;
parameter SCR1_DBG_DMSTATUS_ANYUNAVAIL             = 5'd12;
parameter SCR1_DBG_DMSTATUS_ALLRUNNING             = 5'd11;
parameter SCR1_DBG_DMSTATUS_ANYRUNNING             = 5'd10;
parameter SCR1_DBG_DMSTATUS_ALLHALTED              = 5'd9;
parameter SCR1_DBG_DMSTATUS_ANYHALTED              = 5'd8;
parameter SCR1_DBG_DMSTATUS_AUTHENTICATED          = 5'd7;
parameter SCR1_DBG_DMSTATUS_AUTHBUSY               = 5'd6;
parameter SCR1_DBG_DMSTATUS_RESERVEDA              = 5'd5;
parameter SCR1_DBG_DMSTATUS_DEVTREEVALID           = 5'd4;
parameter SCR1_DBG_DMSTATUS_VERSION_HI             = 5'd3;
parameter SCR1_DBG_DMSTATUS_VERSION_LO             = 5'd0;

// COMMANDS
parameter SCR1_DBG_COMMAND_TYPE_HI                 = 5'd31;
parameter SCR1_DBG_COMMAND_TYPE_LO                 = 5'd24;
parameter SCR1_DBG_COMMAND_TYPE_WDTH               = SCR1_DBG_COMMAND_TYPE_HI
                                                   - SCR1_DBG_COMMAND_TYPE_LO;

parameter SCR1_DBG_COMMAND_ACCESSREG_RESERVEDB     = 5'd23;
parameter SCR1_DBG_COMMAND_ACCESSREG_SIZE_HI       = 5'd22;
parameter SCR1_DBG_COMMAND_ACCESSREG_SIZE_LO       = 5'd20;
parameter SCR1_DBG_COMMAND_ACCESSREG_SIZE_WDTH     = SCR1_DBG_COMMAND_ACCESSREG_SIZE_HI
                                                   - SCR1_DBG_COMMAND_ACCESSREG_SIZE_LO;
parameter SCR1_DBG_COMMAND_ACCESSREG_RESERVEDA     = 5'd19;
parameter SCR1_DBG_COMMAND_ACCESSREG_POSTEXEC      = 5'd18;
parameter SCR1_DBG_COMMAND_ACCESSREG_TRANSFER      = 5'd17;
parameter SCR1_DBG_COMMAND_ACCESSREG_WRITE         = 5'd16;
parameter SCR1_DBG_COMMAND_ACCESSREG_REGNO_HI      = 5'd15;
parameter SCR1_DBG_COMMAND_ACCESSREG_REGNO_LO      = 5'd0;

parameter SCR1_DBG_COMMAND_ACCESSMEM_AAMVIRTUAL    = 5'd23;
parameter SCR1_DBG_COMMAND_ACCESSMEM_AAMSIZE_HI    = 5'd22;
parameter SCR1_DBG_COMMAND_ACCESSMEM_AAMSIZE_LO    = 5'd20;
parameter SCR1_DBG_COMMAND_ACCESSMEM_AAMPOSTINC    = 5'd19;
parameter SCR1_DBG_COMMAND_ACCESSMEM_RESERVEDB_HI  = 5'd18;
parameter SCR1_DBG_COMMAND_ACCESSMEM_RESERVEDB_LO  = 5'd17;
parameter SCR1_DBG_COMMAND_ACCESSMEM_WRITE         = 5'd16;
parameter SCR1_DBG_COMMAND_ACCESSMEM_RESERVEDA_HI  = 5'd13;
parameter SCR1_DBG_COMMAND_ACCESSMEM_RESERVEDA_LO  = 5'd0;

// ABSTRACTCS
parameter SCR1_DBG_ABSTRACTCS_RESERVEDD_HI         = 5'd31;
parameter SCR1_DBG_ABSTRACTCS_RESERVEDD_LO         = 5'd29;
parameter SCR1_DBG_ABSTRACTCS_PROGBUFSIZE_HI       = 5'd28;
parameter SCR1_DBG_ABSTRACTCS_PROGBUFSIZE_LO       = 5'd24;
parameter SCR1_DBG_ABSTRACTCS_RESERVEDC_HI         = 5'd23;
parameter SCR1_DBG_ABSTRACTCS_RESERVEDC_LO         = 5'd13;
parameter SCR1_DBG_ABSTRACTCS_BUSY                 = 5'd12;
parameter SCR1_DBG_ABSTRACTCS_RESERVEDB            = 5'd11;
parameter SCR1_DBG_ABSTRACTCS_CMDERR_HI            = 5'd10;
parameter SCR1_DBG_ABSTRACTCS_CMDERR_LO            = 5'd8;
parameter SCR1_DBG_ABSTRACTCS_CMDERR_WDTH          = SCR1_DBG_ABSTRACTCS_CMDERR_HI
                                                   - SCR1_DBG_ABSTRACTCS_CMDERR_LO;
parameter SCR1_DBG_ABSTRACTCS_RESERVEDA_HI         = 5'd7;
parameter SCR1_DBG_ABSTRACTCS_RESERVEDA_LO         = 5'd4;
parameter SCR1_DBG_ABSTRACTCS_DATACOUNT_HI         = 5'd3;
parameter SCR1_DBG_ABSTRACTCS_DATACOUNT_LO         = 5'd0;

// HARTINFO
parameter SCR1_DBG_HARTINFO_RESERVEDB_HI           = 5'd31;
parameter SCR1_DBG_HARTINFO_RESERVEDB_LO           = 5'd24;
parameter SCR1_DBG_HARTINFO_NSCRATCH_HI            = 5'd23;
parameter SCR1_DBG_HARTINFO_NSCRATCH_LO            = 5'd20;
parameter SCR1_DBG_HARTINFO_RESERVEDA_HI           = 5'd19;
parameter SCR1_DBG_HARTINFO_RESERVEDA_LO           = 5'd17;
parameter SCR1_DBG_HARTINFO_DATAACCESS             = 5'd16;
parameter SCR1_DBG_HARTINFO_DATASIZE_HI            = 5'd15;
parameter SCR1_DBG_HARTINFO_DATASIZE_LO            = 5'd12;
parameter SCR1_DBG_HARTINFO_DATAADDR_HI            = 5'd11;
parameter SCR1_DBG_HARTINFO_DATAADDR_LO            = 5'd0;


`endif // SCR1_INCLUDE_DM_DEFS
