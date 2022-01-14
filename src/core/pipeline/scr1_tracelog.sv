/// Copyright by Syntacore LLC © 2016-2021. See LICENSE for details
/// @file       <scr1_tracelog.sv>
/// @brief      Core tracelog module
///

`include "scr1_arch_description.svh"
`include "scr1_arch_types.svh"
`include "scr1_csr.svh"

`ifdef SCR1_TRGT_SIMULATION

module scr1_tracelog (
    input   logic                                 rst_n,                        // Tracelog reset
    input   logic                                 clk                           // Tracelog clock
`ifdef SCR1_TRACE_LOG_EN
    ,
    input   logic [`SCR1_XLEN-1:0]                soc2pipe_fuse_mhartid_i,      // Fuse MHARTID

    // MPRF
`ifdef  SCR1_MPRF_RAM
    input   logic   [`SCR1_XLEN-1:0]            mprf2trace_int_i   [1:`SCR1_MPRF_SIZE-1], // MPRF registers content
`else // SCR1_MPRF_RAM
    input   type_scr1_mprf_v [1:`SCR1_MPRF_SIZE-1] mprf2trace_int_i,             // MPRF registers content
`endif // SCR1_MPRF_RAM
    input   logic                                 mprf2trace_wr_en_i,           // MPRF write enable
    input   logic [`SCR1_MPRF_AWIDTH-1:0]         mprf2trace_wr_addr_i,         // MPRF write address
    input   logic [`SCR1_XLEN-1:0]                mprf2trace_wr_data_i,         // MPRF write data

    // EXU
    input   logic                                 exu2trace_update_pc_en_i,     // PC updated flag
    input   logic [`SCR1_XLEN-1:0]                exu2trace_update_pc_i,        // Next PC value

    // IFU
    input   logic [`SCR1_IMEM_DWIDTH-1:0]         ifu2trace_instr_i,            // Current instruction from IFU stage

    // CSR
    input   logic                                 csr2trace_mstatus_mie_i,      // CSR MSTATUS.mie bit
    input   logic                                 csr2trace_mstatus_mpie_i,     // CSR MSTATUS.mpie bit
    input   logic [`SCR1_XLEN-1:6]                csr2trace_mtvec_base_i,       // CSR MTVEC.
    input   logic                                 csr2trace_mtvec_mode_i,       // CSR MTVEC.
    input   logic                                 csr2trace_mie_meie_i,         // CSR MIE.meie bit
    input   logic                                 csr2trace_mie_mtie_i,         // CSR MIE.mtie bit
    input   logic                                 csr2trace_mie_msie_i,         // CSR MIE.msie bit
    input   logic                                 csr2trace_mip_meip_i,         // CSR MIP.meip bit
    input   logic                                 csr2trace_mip_mtip_i,         // CSR MIP.mtip bit
    input   logic                                 csr2trace_mip_msip_i,         // CSR MIP.msip bit
 `ifdef SCR1_RVC_EXT
    input   logic [`SCR1_XLEN-1:1]                csr2trace_mepc_i,             // CSR MEPC register
 `else // SCR1_RVC_EXT
    input   logic [`SCR1_XLEN-1:2]                csr2trace_mepc_i,             // CSR MEPC register
 `endif // SCR1_RVC_EXT
    input   logic                                 csr2trace_mcause_irq_i,       // CSR MCAUSE.interrupt bit
    input   type_scr1_exc_code_e                  csr2trace_mcause_ec_i,        // CSR MCAUSE.exception_code bit
    input   logic [`SCR1_XLEN-1:0]                csr2trace_mtval_i,            // CSR MTVAL register

    // Events
    input   logic                                 csr2trace_e_exc_i,            // exception event
    input   logic                                 csr2trace_e_irq_i,            // interrupt event
    input   logic                                 pipe2trace_e_wake_i           // pipe wakeup event
`endif // SCR1_TRACE_LOG_EN
);

//-------------------------------------------------------------------------------
// Local types declaration
//-------------------------------------------------------------------------------
`ifdef SCR1_TRACE_LOG_EN
typedef struct {
    logic [`SCR1_XLEN-1:0]      INT_00_ZERO ;
    logic [`SCR1_XLEN-1:0]      INT_01_RA   ;
    logic [`SCR1_XLEN-1:0]      INT_02_SP   ;
    logic [`SCR1_XLEN-1:0]      INT_03_GP   ;
    logic [`SCR1_XLEN-1:0]      INT_04_TP   ;
    logic [`SCR1_XLEN-1:0]      INT_05_T0   ;
    logic [`SCR1_XLEN-1:0]      INT_06_T1   ;
    logic [`SCR1_XLEN-1:0]      INT_07_T2   ;
    logic [`SCR1_XLEN-1:0]      INT_08_S0   ;
    logic [`SCR1_XLEN-1:0]      INT_09_S1   ;
    logic [`SCR1_XLEN-1:0]      INT_10_A0   ;
    logic [`SCR1_XLEN-1:0]      INT_11_A1   ;
    logic [`SCR1_XLEN-1:0]      INT_12_A2   ;
    logic [`SCR1_XLEN-1:0]      INT_13_A3   ;
    logic [`SCR1_XLEN-1:0]      INT_14_A4   ;
    logic [`SCR1_XLEN-1:0]      INT_15_A5   ;
`ifndef SCR1_RVE_EXT
    logic [`SCR1_XLEN-1:0]      INT_16_A6   ;
    logic [`SCR1_XLEN-1:0]      INT_17_A7   ;
    logic [`SCR1_XLEN-1:0]      INT_18_S2   ;
    logic [`SCR1_XLEN-1:0]      INT_19_S3   ;
    logic [`SCR1_XLEN-1:0]      INT_20_S4   ;
    logic [`SCR1_XLEN-1:0]      INT_21_S5   ;
    logic [`SCR1_XLEN-1:0]      INT_22_S6   ;
    logic [`SCR1_XLEN-1:0]      INT_23_S7   ;
    logic [`SCR1_XLEN-1:0]      INT_24_S8   ;
    logic [`SCR1_XLEN-1:0]      INT_25_S9   ;
    logic [`SCR1_XLEN-1:0]      INT_26_S10  ;
    logic [`SCR1_XLEN-1:0]      INT_27_S11  ;
    logic [`SCR1_XLEN-1:0]      INT_28_T3   ;
    logic [`SCR1_XLEN-1:0]      INT_29_T4   ;
    logic [`SCR1_XLEN-1:0]      INT_30_T5   ;
    logic [`SCR1_XLEN-1:0]      INT_31_T6   ;
`endif // SCR1_RVE_EXT
} type_scr1_ireg_name_s;

typedef struct packed {
    logic [`SCR1_XLEN-1:0]  mstatus;
    logic [`SCR1_XLEN-1:0]  mtvec;
    logic [`SCR1_XLEN-1:0]  mie;
    logic [`SCR1_XLEN-1:0]  mip;
    logic [`SCR1_XLEN-1:0]  mepc;
    logic [`SCR1_XLEN-1:0]  mcause;
    logic [`SCR1_XLEN-1:0]  mtval;
} type_scr1_csr_trace_s;
`endif // SCR1_TRACE_LOG_EN

//-------------------------------------------------------------------------------
// Local Signal Declaration
//-------------------------------------------------------------------------------
`ifdef SCR1_TRACE_LOG_EN

type_scr1_ireg_name_s               mprf_int_alias;


time                                current_time;

// Tracelog control signals
logic                               trace_flag;
logic                               trace_update;
logic                               trace_update_r;
byte                                event_type;

logic [`SCR1_XLEN-1:0]              trace_pc;
logic [`SCR1_XLEN-1:0]              trace_npc;
logic [`SCR1_IMEM_DWIDTH-1:0]       trace_instr;

type_scr1_csr_trace_s               csr_trace1;

// File handlers
int unsigned                        trace_fhandler_core;

// MPRF signals
logic                               mprf_up;
logic [`SCR1_MPRF_AWIDTH-1:0]       mprf_addr;
logic [`SCR1_XLEN-1:0]              mprf_wdata;

string                              hart;
string                              test_name;

`endif // SCR1_TRACE_LOG_EN

//-------------------------------------------------------------------------------
// Local tasks
//-------------------------------------------------------------------------------

`ifdef SCR1_TRACE_LOG_EN

task trace_write_common;
    $fwrite(trace_fhandler_core, "%16d  ", current_time);
    // $fwrite(trace_fhandler_core, " 0  ");
    $fwrite(trace_fhandler_core, " %s  ",  event_type);
    $fwrite(trace_fhandler_core, " %8x  ", trace_pc);
    $fwrite(trace_fhandler_core, " %8x  ", trace_instr);
    $fwrite(trace_fhandler_core, " %8x  ", trace_npc);
endtask // trace_write_common

task trace_write_int_walias;
    case (mprf_addr)
        0  :  $fwrite(trace_fhandler_core, " x00_zero  ");
        1  :  $fwrite(trace_fhandler_core, " x01_ra    ");
        2  :  $fwrite(trace_fhandler_core, " x02_sp    ");
        3  :  $fwrite(trace_fhandler_core, " x03_gp    ");
        4  :  $fwrite(trace_fhandler_core, " x04_tp    ");
        5  :  $fwrite(trace_fhandler_core, " x05_t0    ");
        6  :  $fwrite(trace_fhandler_core, " x06_t1    ");
        7  :  $fwrite(trace_fhandler_core, " x07_t2    ");
        8  :  $fwrite(trace_fhandler_core, " x08_s0    ");
        9  :  $fwrite(trace_fhandler_core, " x09_s1    ");
        10 :  $fwrite(trace_fhandler_core, " x10_a0    ");
        11 :  $fwrite(trace_fhandler_core, " x11_a1    ");
        12 :  $fwrite(trace_fhandler_core, " x12_a2    ");
        13 :  $fwrite(trace_fhandler_core, " x13_a3    ");
        14 :  $fwrite(trace_fhandler_core, " x14_a4    ");
        15 :  $fwrite(trace_fhandler_core, " x15_a5    ");
`ifndef SCR1_RVE_EXT
        16 :  $fwrite(trace_fhandler_core, " x16_a6    ");
        17 :  $fwrite(trace_fhandler_core, " x17_a7    ");
        18 :  $fwrite(trace_fhandler_core, " x18_s2    ");
        19 :  $fwrite(trace_fhandler_core, " x19_s3    ");
        20 :  $fwrite(trace_fhandler_core, " x20_s4    ");
        21 :  $fwrite(trace_fhandler_core, " x21_s5    ");
        22 :  $fwrite(trace_fhandler_core, " x22_s6    ");
        23 :  $fwrite(trace_fhandler_core, " x23_s7    ");
        24 :  $fwrite(trace_fhandler_core, " x24_s8    ");
        25 :  $fwrite(trace_fhandler_core, " x25_s9    ");
        26 :  $fwrite(trace_fhandler_core, " x26_s10   ");
        27 :  $fwrite(trace_fhandler_core, " x27_s11   ");
        28 :  $fwrite(trace_fhandler_core, " x28_t3    ");
        29 :  $fwrite(trace_fhandler_core, " x29_t4    ");
        30 :  $fwrite(trace_fhandler_core, " x30_t5    ");
        31 :  $fwrite(trace_fhandler_core, " x31_t6    ");
`endif // SCR1_RVE_EXT
        default: begin
              $fwrite(trace_fhandler_core, " xxx       ");
        end
    endcase
endtask

//-------------------------------------------------------------------------------
// MPRF Registers assignment
//-------------------------------------------------------------------------------
assign mprf_int_alias.INT_00_ZERO   = '0;
assign mprf_int_alias.INT_01_RA     = mprf2trace_int_i[1];
assign mprf_int_alias.INT_02_SP     = mprf2trace_int_i[2];
assign mprf_int_alias.INT_03_GP     = mprf2trace_int_i[3];
assign mprf_int_alias.INT_04_TP     = mprf2trace_int_i[4];
assign mprf_int_alias.INT_05_T0     = mprf2trace_int_i[5];
assign mprf_int_alias.INT_06_T1     = mprf2trace_int_i[6];
assign mprf_int_alias.INT_07_T2     = mprf2trace_int_i[7];
assign mprf_int_alias.INT_08_S0     = mprf2trace_int_i[8];
assign mprf_int_alias.INT_09_S1     = mprf2trace_int_i[9];
assign mprf_int_alias.INT_10_A0     = mprf2trace_int_i[10];
assign mprf_int_alias.INT_11_A1     = mprf2trace_int_i[11];
assign mprf_int_alias.INT_12_A2     = mprf2trace_int_i[12];
assign mprf_int_alias.INT_13_A3     = mprf2trace_int_i[13];
assign mprf_int_alias.INT_14_A4     = mprf2trace_int_i[14];
assign mprf_int_alias.INT_15_A5     = mprf2trace_int_i[15];
`ifndef SCR1_RVE_EXT
assign mprf_int_alias.INT_16_A6     = mprf2trace_int_i[16];
assign mprf_int_alias.INT_17_A7     = mprf2trace_int_i[17];
assign mprf_int_alias.INT_18_S2     = mprf2trace_int_i[18];
assign mprf_int_alias.INT_19_S3     = mprf2trace_int_i[19];
assign mprf_int_alias.INT_20_S4     = mprf2trace_int_i[20];
assign mprf_int_alias.INT_21_S5     = mprf2trace_int_i[21];
assign mprf_int_alias.INT_22_S6     = mprf2trace_int_i[22];
assign mprf_int_alias.INT_23_S7     = mprf2trace_int_i[23];
assign mprf_int_alias.INT_24_S8     = mprf2trace_int_i[24];
assign mprf_int_alias.INT_25_S9     = mprf2trace_int_i[25];
assign mprf_int_alias.INT_26_S10    = mprf2trace_int_i[26];
assign mprf_int_alias.INT_27_S11    = mprf2trace_int_i[27];
assign mprf_int_alias.INT_28_T3     = mprf2trace_int_i[28];
assign mprf_int_alias.INT_29_T4     = mprf2trace_int_i[29];
assign mprf_int_alias.INT_30_T5     = mprf2trace_int_i[30];
assign mprf_int_alias.INT_31_T6     = mprf2trace_int_i[31];
`endif // SCR1_RVE_EXT
`endif // SCR1_TRACE_LOG_EN

//-------------------------------------------------------------------------------
// Legacy time counter
//-------------------------------------------------------------------------------
// The counter is left for compatibility with the current UVM environment

int     time_cnt;

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        time_cnt    <= 0;
    end else begin
        time_cnt    <= time_cnt + 1;
    end
end

//-------------------------------------------------------------------------------
// Initial part pipeline tracelog
//-------------------------------------------------------------------------------

`ifdef SCR1_TRACE_LOG_EN
// Files opening and writing initial header
initial begin
    $timeformat(-9, 0, " ns", 10);
    #1 hart.hextoa(soc2pipe_fuse_mhartid_i);

    trace_fhandler_core = $fopen({"tracelog_core_", hart, ".log"}, "w");

    // Writing initial header
    $fwrite(trace_fhandler_core,  "# RTL_ID %h\n", SCR1_CSR_MIMPID);
    $fwrite(trace_fhandler_core,  "#\n");
    // $fwrite(trace_fhandler_core,  "# R - return from trap:\n");
    // $fwrite(trace_fhandler_core,  "#    1 - MRET\n");
    // $fwrite(trace_fhandler_core,  "#    0 - no return\n");
    $fwrite(trace_fhandler_core,  "# Events:\n");
    $fwrite(trace_fhandler_core,  "#    N - no event\n");
    $fwrite(trace_fhandler_core,  "#    E - exception\n");
    $fwrite(trace_fhandler_core,  "#    I - interrupt\n");
    $fwrite(trace_fhandler_core,  "#    W - wakeup\n");
end

// Core reset logging and header printing
always @(posedge rst_n) begin
    $fwrite(trace_fhandler_core, "# =====================================================================================\n");
`ifndef VERILATOR
    $fwrite(trace_fhandler_core, "# %16d ns : Core Reset\n", $time());
`else
    $fwrite(trace_fhandler_core, "# : Core Reset\n");
`endif
    $fwrite(trace_fhandler_core, "# =====================================================================================\n");
    $fwrite(trace_fhandler_core,  "# Test: %s\n", test_name);
    $fwrite(trace_fhandler_core,  "#           Time  ");
    // $fwrite(trace_fhandler_core,  " R  ");
    $fwrite(trace_fhandler_core,  " Ev ");
    $fwrite(trace_fhandler_core,  " Curr_PC   ");
    $fwrite(trace_fhandler_core,  " Instr     ");
    $fwrite(trace_fhandler_core,  " Next_PC   ");
    $fwrite(trace_fhandler_core,  " Reg       ");
    $fwrite(trace_fhandler_core,  " Value     ");
    $fwrite(trace_fhandler_core, "\n");
    $fwrite(trace_fhandler_core, "# =====================================================================================\n");
end

//-------------------------------------------------------------------------------
// Common trace part
//-------------------------------------------------------------------------------

assign trace_flag   = 1'b1;
assign trace_update = (exu2trace_update_pc_en_i | mprf2trace_wr_en_i) & trace_flag;

always_ff @(posedge clk) begin
    if (~rst_n) begin
        current_time    <= 0;
        event_type      <= "N";

        trace_pc        <= 'x;
        trace_npc       <= 'x;
        trace_instr     <= 'x;

        trace_update_r  <= 1'b0;

        mprf_up         <= '0;
        mprf_addr       <= '0;
        mprf_wdata      <= '0;
    end else begin
        trace_update_r <= trace_update;
        if (trace_update) begin
`ifdef VERILATOR
            current_time  <= time_cnt;
`else
            current_time  <= $time();
`endif
            trace_pc      <= trace_npc;
            trace_npc     <= exu2trace_update_pc_i;
            trace_instr   <= ifu2trace_instr_i;

            if (csr2trace_e_exc_i) begin
                // Exception
                event_type  <= "E";
            end
            else if (csr2trace_e_irq_i) begin
                // IRQ
                event_type  <= "I";
            end
            else if (pipe2trace_e_wake_i) begin
                // Wake
                event_type <= "W";
            end
            else begin
                // No event
                event_type <= "N";
            end
        end

        // Write log signals
        mprf_up    <= mprf2trace_wr_en_i;
        mprf_addr  <= mprf2trace_wr_en_i ? mprf2trace_wr_addr_i : 'x;
        mprf_wdata <= mprf2trace_wr_en_i ? mprf2trace_wr_data_i : 'x;
    end
end

//-------------------------------------------------------------------------------
// Core MPRF logging
//-------------------------------------------------------------------------------

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
    end else begin
        if (trace_update_r) begin

            trace_write_common();

            case (event_type)
                "W"     : begin
                    // Wakeup
                    if (csr_trace1.mip & csr_trace1.mie) begin
                        $fwrite(trace_fhandler_core, " mip        %08x\n", csr_trace1.mip );
                        trace_write_common();
                        $fwrite(trace_fhandler_core, " mie        %08x", csr_trace1.mie );
                    end
                end
                "N"     : begin
                    // Regular
                    if (mprf_up && mprf_addr != 0) begin
                        // $fwrite(trace_fhandler_core, " x%2d      %08x", mprf_addr, mprf_wdata);
                        trace_write_int_walias();
                        $fwrite(trace_fhandler_core, " %08x", mprf_wdata);
                    end else begin
                        $fwrite(trace_fhandler_core, " ---        --------");
                    end
                end
                "R"     : begin
                    // MRET
                    $fwrite(trace_fhandler_core, " mstatus    %08x", csr_trace1.mstatus);
                end
                "E", "I": begin
                    // IRQ/Exception
                    $fwrite(trace_fhandler_core, " mstatus    %08x\n", csr_trace1.mstatus);
                    trace_write_common();
                    $fwrite(trace_fhandler_core, " mepc       %08x\n", csr_trace1.mepc);
                    trace_write_common();
                    $fwrite(trace_fhandler_core, " mcause     %08x\n", csr_trace1.mcause);
                    trace_write_common();
                    $fwrite(trace_fhandler_core, " mtval      %08x",   csr_trace1.mtval);
                end
                default : begin
                    $fwrite(trace_fhandler_core,  "\n");
                end
            endcase
            $fwrite(trace_fhandler_core,  "\n");
        end
    end
end

//-------------------------------------------------------------------------------
// Core CSR logging
//-------------------------------------------------------------------------------

always_comb begin
    csr_trace1.mtvec        = {csr2trace_mtvec_base_i, 4'd0, 2'(csr2trace_mtvec_mode_i)};
    csr_trace1.mepc         =
`ifdef SCR1_RVC_EXT
                              {csr2trace_mepc_i, 1'b0};
`else // SCR1_RVC_EXT
                              {csr2trace_mepc_i, 2'b00};
`endif // SCR1_RVC_EXT
    csr_trace1.mcause       = {csr2trace_mcause_irq_i, type_scr1_csr_mcause_ec_v'(csr2trace_mcause_ec_i)};
    csr_trace1.mtval        = csr2trace_mtval_i;

    csr_trace1.mstatus      = '0;
    csr_trace1.mie          = '0;
    csr_trace1.mip          = '0;

    csr_trace1.mstatus[SCR1_CSR_MSTATUS_MIE_OFFSET]     = csr2trace_mstatus_mie_i;
    csr_trace1.mstatus[SCR1_CSR_MSTATUS_MPIE_OFFSET]    = csr2trace_mstatus_mpie_i;
    csr_trace1.mstatus[SCR1_CSR_MSTATUS_MPP_OFFSET+1:SCR1_CSR_MSTATUS_MPP_OFFSET]   = SCR1_CSR_MSTATUS_MPP;
    csr_trace1.mie[SCR1_CSR_MIE_MSIE_OFFSET]            = csr2trace_mie_msie_i;
    csr_trace1.mie[SCR1_CSR_MIE_MTIE_OFFSET]            = csr2trace_mie_mtie_i;
    csr_trace1.mie[SCR1_CSR_MIE_MEIE_OFFSET]            = csr2trace_mie_meie_i;
    csr_trace1.mip[SCR1_CSR_MIE_MSIE_OFFSET]            = csr2trace_mip_msip_i;
    csr_trace1.mip[SCR1_CSR_MIE_MTIE_OFFSET]            = csr2trace_mip_mtip_i;
    csr_trace1.mip[SCR1_CSR_MIE_MEIE_OFFSET]            = csr2trace_mip_meip_i;
end

`endif // SCR1_TRACE_LOG_EN

endmodule : scr1_tracelog

`endif // SCR1_TRGT_SIMULATION
