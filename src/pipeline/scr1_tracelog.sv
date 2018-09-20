/// Copyright by Syntacore LLC © 2016-2018. See LICENSE for details
/// @file       <scr1_tracelog.sv>
/// @brief      Core tracelog module
///

`include "scr1_arch_description.svh"
`include "scr1_arch_types.svh"
`include "scr1_csr.svh"

module scr1_tracelog (
    input   logic                                   rst_n,
    input   logic                                   clk,
    input   logic [`SCR1_XLEN-1:0]                  fuse_mhartid,
    // MPRF
`ifndef SCR1_RVE_EXT
    input   type_scr1_mprf_v [1:31]                 mprf_int,
`else // SCR1_RVE_EXT
    input   type_scr1_mprf_v [1:15]                 mprf_int,
`endif // SCR1_RVE_EXT
    input   logic                                   mprf_wr_en,
    input   logic [`SCR1_MPRF_ADDR_WIDTH-1:0]       mprf_wr_addr,
    input   logic [`SCR1_XLEN-1:0]                  mprf_wr_data,
    // EXU
    input   logic                                   update_pc_en,
    input   logic [`SCR1_XLEN-1:0]                  update_pc,
    // CSR
    input   logic                                   mstatus_mie,
    input   logic                                   mstatus_mpie,
    input   logic [`SCR1_XLEN-1:6]                  mtvec_base,
    input   logic                                   mtvec_mode,
    input   logic                                   mie_meie,
    input   logic                                   mie_mtie,
    input   logic                                   mie_msie,
    input   logic                                   mip_meip,
    input   logic                                   mip_mtip,
    input   logic                                   mip_msip,
 `ifdef SCR1_RVC_EXT
    input   logic [`SCR1_XLEN-1:1]                  mepc,
 `else // SCR1_RVC_EXT
    input   logic [`SCR1_XLEN-1:2]                  mepc,
 `endif // SCR1_RVC_EXT
    input   logic                                   mcause_i,
    input   type_scr1_exc_code_e                    mcause_ec,
    input   logic [`SCR1_XLEN-1:0]                  mtval,
    input   logic                                   mstatus_mie_up
);

//-------------------------------------------------------------------------------
// MPRF register aliases
//-------------------------------------------------------------------------------
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

type_scr1_ireg_name_s   mprf_int_alias;

assign mprf_int_alias.INT_00_ZERO   = '0;
assign mprf_int_alias.INT_01_RA     = mprf_int[1];
assign mprf_int_alias.INT_02_SP     = mprf_int[2];
assign mprf_int_alias.INT_03_GP     = mprf_int[3];
assign mprf_int_alias.INT_04_TP     = mprf_int[4];
assign mprf_int_alias.INT_05_T0     = mprf_int[5];
assign mprf_int_alias.INT_06_T1     = mprf_int[6];
assign mprf_int_alias.INT_07_T2     = mprf_int[7];
assign mprf_int_alias.INT_08_S0     = mprf_int[8];
assign mprf_int_alias.INT_09_S1     = mprf_int[9];
assign mprf_int_alias.INT_10_A0     = mprf_int[10];
assign mprf_int_alias.INT_11_A1     = mprf_int[11];
assign mprf_int_alias.INT_12_A2     = mprf_int[12];
assign mprf_int_alias.INT_13_A3     = mprf_int[13];
assign mprf_int_alias.INT_14_A4     = mprf_int[14];
assign mprf_int_alias.INT_15_A5     = mprf_int[15];
`ifndef SCR1_RVE_EXT
assign mprf_int_alias.INT_16_A6     = mprf_int[16];
assign mprf_int_alias.INT_17_A7     = mprf_int[17];
assign mprf_int_alias.INT_18_S2     = mprf_int[18];
assign mprf_int_alias.INT_19_S3     = mprf_int[19];
assign mprf_int_alias.INT_20_S4     = mprf_int[20];
assign mprf_int_alias.INT_21_S5     = mprf_int[21];
assign mprf_int_alias.INT_22_S6     = mprf_int[22];
assign mprf_int_alias.INT_23_S7     = mprf_int[23];
assign mprf_int_alias.INT_24_S8     = mprf_int[24];
assign mprf_int_alias.INT_25_S9     = mprf_int[25];
assign mprf_int_alias.INT_26_S10    = mprf_int[26];
assign mprf_int_alias.INT_27_S11    = mprf_int[27];
assign mprf_int_alias.INT_28_T3     = mprf_int[28];
assign mprf_int_alias.INT_29_T4     = mprf_int[29];
assign mprf_int_alias.INT_30_T5     = mprf_int[30];
assign mprf_int_alias.INT_31_T6     = mprf_int[31];
`endif // SCR1_RVE_EXT

//-------------------------------------------------------------------------------
// Time counter
//-------------------------------------------------------------------------------
int     time_cnt;

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        time_cnt    <= 0;
    end else begin
        time_cnt    <= time_cnt + 1;
    end
end

//-------------------------------------------------------------------------------
// Trace log MPRF
//-------------------------------------------------------------------------------
`ifdef SCR1_TRACE_LOG_EN

logic                               trace_update;
logic                               trace_update_r;
logic [`SCR1_XLEN-1:0]              curr_pc_log;
`ifndef SCR1_RVE_EXT
type_scr1_mprf_v [1:31]             mprf_int_log;
`else // SCR1_RVE_EXT
type_scr1_mprf_v [1:15]             mprf_int_log;
`endif // SCR1_RVE_EXT
logic                               mprf_up;
logic [`SCR1_MPRF_ADDR_WIDTH-1:0]   mprf_addr;
logic                               tracelog_full;
int unsigned                        trace_fhandler;
int unsigned                        trace_fhandler_diff;
int                                 time_cnt2;
string                              hart;
string                              test_name;

task trace_write_mprf;
    $fwrite(trace_fhandler,  "%12d ", time_cnt);
    $fwrite(trace_fhandler,  "%6d ", time_cnt-time_cnt2);
    $fwrite(trace_fhandler,  "%8x ", curr_pc_log);
`ifndef SCR1_RVE_EXT
    for (int i=1; i<32; ++i) begin
`else // SCR1_RVE_EXT
    for (int i=1; i<16; ++i) begin
`endif // SCR1_RVE_EXT
        $fwrite(trace_fhandler,  "%8x ", mprf_int_log[i]);
    end
    $fwrite(trace_fhandler,  "\n");
endtask // trace_write_mprf

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        mprf_int_log    <= '0;
        mprf_up         <= '0;
        mprf_addr       <= '0;
    end else begin
        mprf_up         <= '0;
        mprf_addr       <= '0;

        if (mprf_wr_en) begin
            mprf_up     <= 1'b1;
            mprf_addr   <= mprf_wr_addr;
            if (mprf_wr_addr != 0) begin
                mprf_int_log[$unsigned(mprf_wr_addr)] <= mprf_wr_data;
            end
        end
    end
end

always_ff @(posedge clk) begin
    curr_pc_log <= update_pc;
end

assign trace_update = update_pc_en | (mprf_wr_en & ~mstatus_mie_up);

int unsigned temp_fhandler;

initial begin
`ifndef VERILATOR
    #1 hart.hextoa(fuse_mhartid);
`endif // VERILATOR

`ifdef SCR1_TRACE_LOG_FULL
    tracelog_full   = 1'b1;
`else // SCR1_TRACE_LOG_FULL
    tracelog_full   = 1'b0;
`endif // SCR1_TRACE_LOG_FULL

    // erase old logs
    if (tracelog_full) begin
        temp_fhandler= $fopen({"trace_mprf_", hart, ".log"}, "w");
        $fclose(temp_fhandler);
    end else begin
        temp_fhandler = $fopen({"trace_mprf_diff_", hart, ".log"}, "w");
        $fclose(temp_fhandler);
    end
    temp_fhandler = $fopen({"trace_csr_", hart, ".log"}, "w");
    $fclose(temp_fhandler);
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        if (trace_fhandler) begin
            $fflush(trace_fhandler);
            $fclose(trace_fhandler);
            trace_fhandler  = 0;
        end
        trace_update_r      <= 1'b0;
        time_cnt2           <= 0;
    end else begin
        // open file
        if ((trace_fhandler == 0) & tracelog_full) begin
            trace_fhandler = $fopen({"trace_mprf_", hart, ".log"}, "a+");
            // Write Header
            $fwrite(trace_fhandler,  "# Test: %s\n", test_name);
            $fwrite(trace_fhandler,  "          Clk# ");
            $fwrite(trace_fhandler,  "Delay ");
            $fwrite(trace_fhandler,  " PC     ");
            $fwrite(trace_fhandler,  " X1_RA   ");
            $fwrite(trace_fhandler,  " X2_SP   ");
            $fwrite(trace_fhandler,  " X3_GP   ");
            $fwrite(trace_fhandler,  " X4_TP   ");
            $fwrite(trace_fhandler,  " X5_T0   ");
            $fwrite(trace_fhandler,  " X6_T1   ");
            $fwrite(trace_fhandler,  " X7_T2   ");
            $fwrite(trace_fhandler,  " X8_S0   ");
            $fwrite(trace_fhandler,  " X9_S1   ");
            $fwrite(trace_fhandler,  " X10_A0  ");
            $fwrite(trace_fhandler,  " X11_A1  ");
            $fwrite(trace_fhandler,  " X12_A2  ");
            $fwrite(trace_fhandler,  " X13_A3  ");
            $fwrite(trace_fhandler,  " X14_A4  ");
            $fwrite(trace_fhandler,  " X15_A5  ");
`ifndef SCR1_RVE_EXT
            $fwrite(trace_fhandler,  " X16_A6  ");
            $fwrite(trace_fhandler,  " X17_A7  ");
            $fwrite(trace_fhandler,  " X18_S2  ");
            $fwrite(trace_fhandler,  " X19_S3  ");
            $fwrite(trace_fhandler,  " X20_S4  ");
            $fwrite(trace_fhandler,  " X21_S5  ");
            $fwrite(trace_fhandler,  " X22_S6  ");
            $fwrite(trace_fhandler,  " X23_S7  ");
            $fwrite(trace_fhandler,  " X24_S8  ");
            $fwrite(trace_fhandler,  " X25_S9  ");
            $fwrite(trace_fhandler,  " X26_S10 ");
            $fwrite(trace_fhandler,  " X27_S11 ");
            $fwrite(trace_fhandler,  " X28_T3  ");
            $fwrite(trace_fhandler,  " X29_T4  ");
            $fwrite(trace_fhandler,  " X30_T5  ");
            $fwrite(trace_fhandler,  " X31_T6  ");
`endif // SCR1_RVE_EXT
            $fwrite(trace_fhandler,  "\n");
        end

        trace_update_r      <= trace_update;

        if (trace_update_r & tracelog_full) begin
            time_cnt2       <= time_cnt;
            trace_write_mprf();
        end
    end
end

`ifndef SCR1_TRACE_LOG_FULL
always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        if (trace_fhandler_diff) begin
            $fflush(trace_fhandler_diff);
            $fclose(trace_fhandler_diff);
            trace_fhandler_diff = 0;
        end
    end else begin
        // open file
        if ((trace_fhandler_diff == 0) & ~tracelog_full) begin
            trace_fhandler_diff = $fopen({"trace_mprf_diff_", hart, ".log"}, "a+");
            // Write Header
            $fwrite(trace_fhandler_diff,  "# Test: %s\n", test_name);
            $fwrite(trace_fhandler_diff,  "      Clk# ");
            $fwrite(trace_fhandler_diff,  "  PC ");
            $fwrite(trace_fhandler_diff,  "\n");
        end

        if (trace_update_r & ~tracelog_full) begin
            // write updated registers
            $fwrite(trace_fhandler_diff,  "%10d: ", time_cnt);
            $fwrite(trace_fhandler_diff,  "%8x ", curr_pc_log);

            if (mprf_up) begin
`ifndef SCR1_RVE_EXT
                for (int i=1; i<32; ++i) begin
`else // SCR1_RVE_EXT
                for (int i=1; i<16; ++i) begin
`endif // SCR1_RVE_EXT
                    if (mprf_addr == i) begin
                        $fwrite(trace_fhandler_diff,  "X%2d: %8x", i, mprf_int_log[i]);
                    end
                end
            end
            $fwrite(trace_fhandler_diff,  "\n");
        end
    end
end

`endif // SCR1_TRACE_LOG_FULL

//-------------------------------------------------------------------------------
// Trace log CSR
//-------------------------------------------------------------------------------
int unsigned                trace_csr_fhandler;

typedef struct packed {
    logic [`SCR1_XLEN-1:0]  mstatus;
    logic [`SCR1_XLEN-1:0]  mtvec;
    logic [`SCR1_XLEN-1:0]  mie;
    logic [`SCR1_XLEN-1:0]  mip;
    logic [`SCR1_XLEN-1:0]  mepc;
    logic [`SCR1_XLEN-1:0]  mcause;
    logic [`SCR1_XLEN-1:0]  mtval;
} type_scr1_csr_trace_s;

type_scr1_csr_trace_s       csr_trace1;
type_scr1_csr_trace_s       csr_trace2;

task trace_write_csr;
    $fwrite(trace_csr_fhandler,  "%12d   ", time_cnt);
    $fwrite(trace_csr_fhandler,  "%8x ", csr_trace1.mstatus );
    $fwrite(trace_csr_fhandler,  "%8x ", csr_trace1.mtvec   );
    $fwrite(trace_csr_fhandler,  "%8x ", csr_trace1.mie     );
    $fwrite(trace_csr_fhandler,  "%8x ", csr_trace1.mip     );
    $fwrite(trace_csr_fhandler,  "%8x ", csr_trace1.mepc    );
    $fwrite(trace_csr_fhandler,  "%8x ", csr_trace1.mcause  );
    $fwrite(trace_csr_fhandler,  "%8x ", csr_trace1.mtval   );
    $fwrite(trace_csr_fhandler,  "\n");
endtask // trace_write_csr

always_comb begin
    csr_trace1.mtvec        = {mtvec_base, 4'd0, 2'(mtvec_mode)};
    csr_trace1.mepc         =
`ifdef SCR1_RVC_EXT
                              {mepc, 1'b0};
`else // SCR1_RVC_EXT
                              {mepc, 2'b00};
`endif // SCR1_RVC_EXT
    csr_trace1.mcause       = {mcause_i, type_scr1_csr_mcause_ec_v'(mcause_ec)};
    csr_trace1.mtval        = mtval;

    csr_trace1.mstatus      = '0;
    csr_trace1.mie          = '0;
    csr_trace1.mip          = '0;

    csr_trace1.mstatus[SCR1_CSR_MSTATUS_MIE_OFFSET]     = mstatus_mie;
    csr_trace1.mstatus[SCR1_CSR_MSTATUS_MPIE_OFFSET]    = mstatus_mpie;
    csr_trace1.mstatus[SCR1_CSR_MSTATUS_MPP_OFFSET+1:SCR1_CSR_MSTATUS_MPP_OFFSET]   = SCR1_CSR_MSTATUS_MPP;
    csr_trace1.mie[SCR1_CSR_MIE_MSIE_OFFSET]            = mie_msie;
    csr_trace1.mie[SCR1_CSR_MIE_MTIE_OFFSET]            = mie_mtie;
    csr_trace1.mie[SCR1_CSR_MIE_MEIE_OFFSET]            = mie_meie;
    csr_trace1.mip[SCR1_CSR_MIE_MSIE_OFFSET]            = mip_msip;
    csr_trace1.mip[SCR1_CSR_MIE_MTIE_OFFSET]            = mip_mtip;
    csr_trace1.mip[SCR1_CSR_MIE_MEIE_OFFSET]            = mip_meip;
end


always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        if (trace_csr_fhandler) begin
            $fflush(trace_csr_fhandler);
            $fclose(trace_csr_fhandler);
            trace_csr_fhandler = 0;
        end
        csr_trace2  <= csr_trace1;
    end else begin
        // open file
        if (trace_csr_fhandler == 0) begin
            trace_csr_fhandler = $fopen({"trace_csr_", hart, ".log"}, "a+");

            // Write Header
            $fwrite(trace_csr_fhandler, "# Test: %s\n", test_name);
            $fwrite(trace_csr_fhandler, "        Clk#  ");
            $fwrite(trace_csr_fhandler, "  MSTATUS");
            $fwrite(trace_csr_fhandler, "    MTVEC");
            $fwrite(trace_csr_fhandler, "      MIE");
            $fwrite(trace_csr_fhandler, "      MIP");
            $fwrite(trace_csr_fhandler, "     MEPC");
            $fwrite(trace_csr_fhandler, "   MCAUSE");
            $fwrite(trace_csr_fhandler, " MTVAL"   );
            $fwrite(trace_csr_fhandler,  "\n");

            trace_write_csr();
        end
        csr_trace2   <= csr_trace1;
        if (csr_trace2 != csr_trace1) begin
            trace_write_csr();
        end
    end
end

`endif // SCR1_TRACE_LOG_EN

endmodule : scr1_tracelog