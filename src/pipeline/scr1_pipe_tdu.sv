/// Copyright by Syntacore LLC © 2016-2019. See LICENSE for details
/// @file       <scr1_pipe_tdu.sv>
/// @brief      Trigger Debug Unit (TDU)
///

`include "scr1_arch_description.svh"

`ifdef SCR1_BRKM_EN
`include "scr1_riscv_isa_decoding.svh"
`include "scr1_tdu.svh"

module scr1_pipe_tdu (
    // Common signals
    input  logic                                            rst_n,              // TDU reset
    input  logic                                            clk,                // TDU clock
    input  logic                                            clk_en,             // TDU clock enable
    input  logic                                            dsbl,               // TDU Disable
    // CSR I/F
    input  logic                                            csr2tdu_req,        // CSR-TDU i/f request
    input  type_scr1_csr_cmd_sel_e                          csr2tdu_cmd,        // CSR-TDU i/f command
    input  logic [SCR1_CSR_ADDR_TDU_OFFS_W-1:0]             csr2tdu_addr,       // CSR-TDU i/f address
    input  logic [SCR1_TDU_DATA_W-1:0]                      csr2tdu_wdata,      // CSR-TDU i/f write data
    output logic [SCR1_TDU_DATA_W-1:0]                      csr2tdu_rdata,      // CSR-TDU i/f read data
    output type_scr1_csr_resp_e                             csr2tdu_resp,       // CSR-TDU i/f response
    // ID I/F
    input  type_scr1_brkm_instr_mon_s                       exu2tdu_i_mon,      // Instruction stream monitoring
    // CFU I/F
    output logic [SCR1_TDU_ALLTRIG_NUM-1 : 0]               tdu2exu_i_match,    // Instruction BP match
    output logic                                            tdu2exu_i_x_req,    // Instruction BP exception request
    // LSU I/F
`ifndef SCR1_BRKM_EN
    output logic                                            tdu2lsu_brk_en,     // TDU-LSU Breakpoint enable
`endif // SCR1_BRKM_EN
    output logic                                            tdu2lsu_i_x_req,    // TDU-LSU Instruction BP exception request
    input  type_scr1_brkm_lsu_mon_s                         tdu2lsu_d_mon,      // TDU-LSU Data address stream monitoring
    output logic [SCR1_TDU_MTRIG_NUM-1 : 0]                 tdu2lsu_d_match,    // TDU-LSU Data BP match
    output logic                                            tdu2lsu_d_x_req,    // TDU-LSU Data BP exception request
    // WB I/F
    input  logic [SCR1_TDU_ALLTRIG_NUM-1 : 0]               exu2tdu_bp_retire,  // Map of BPs being retired
    // EPU I/F
    output logic                                            tdu2hdu_dmode_req   // Debug Mode redirection request
);

localparam int unsigned MTRIG_NUM   = SCR1_TDU_MTRIG_NUM;
localparam int unsigned ALLTRIG_NUM = SCR1_TDU_ALLTRIG_NUM;
localparam int unsigned ALLTRIG_W   = $clog2(ALLTRIG_NUM);

logic [ALLTRIG_W-1:0]                           tselect_ff;
logic [MTRIG_NUM-1:0] [SCR1_TDU_DATA_W-1:0]     tdata2;

logic                                           csr_addr_tselect_cmb;
logic [MTRIG_NUM-1:0]                           csr_addr_mcontrol_cmb;
logic [MTRIG_NUM-1:0]                           csr_addr_tdata2_cmb;
logic                                           csr_wr_cmb;
logic [SCR1_TDU_DATA_W-1:0]                     csr_wr_data_cmb;

logic [MTRIG_NUM-1:0]                           clk_en_mcontrol_cmb;
logic [MTRIG_NUM-1:0]                           mcontrol_dmode_ff;
logic [MTRIG_NUM-1:0]                           mcontrol_execution_hit_cmb;
logic [MTRIG_NUM-1:0]                           mcontrol_ldst_hit_cmb;
logic [MTRIG_NUM-1:0]                           mcontrol_action_ff;
logic [MTRIG_NUM-1:0] [1:0]                     mcontrol_match_ff;
logic [MTRIG_NUM-1:0]                           mcontrol_hit_ff;
logic [MTRIG_NUM-1:0]                           mcontrol_m_ff;
logic [MTRIG_NUM-1:0]                           mcontrol_execution_ff;
logic [MTRIG_NUM-1:0]                           mcontrol_load_ff;
logic [MTRIG_NUM-1:0]                           mcontrol_store_ff;
logic [MTRIG_NUM-1:0]                           mcontrol_write_en;

genvar                                          gvar_trig;

`ifdef SCR1_BRKM_BRKPT_ICOUNT_EN
logic                                           csr_addr_icount_cmb;

logic                                           clk_en_icount_cmb;
logic                                           icount_decrement_cmb;
logic                                           icount_hit_cmb;
logic                                           icount_skip_ff;
logic                                           icount_dmode_ff;
logic                                           icount_action_ff;
logic                                           icount_hit_ff;
logic                                           icount_m_ff;
logic [SCR1_TDU_ICOUNT_COUNT_HI-SCR1_TDU_ICOUNT_COUNT_LO:0]
                                                icount_count_ff;

logic                                           icount_write_en;
`endif // SCR1_BRKM_BRKPT_ICOUNT_EN

// CSR interface
// -------------

always_comb begin
    csr_addr_tselect_cmb      = 1'b0;
    csr_addr_tdata2_cmb       = 1'b0;
    csr_addr_mcontrol_cmb     = 1'b0;

`ifdef SCR1_BRKM_BRKPT_ICOUNT_EN
    csr_addr_icount_cmb       = 1'b0;
`endif // SCR1_BRKM_BRKPT_ICOUNT_EN

    csr_wr_cmb            = 1'b0;
    csr_wr_data_cmb       = 1'b0;

    csr2tdu_rdata         = 1'b0;
    csr2tdu_resp          = SCR1_CSR_RESP_ER;

    if( csr2tdu_req ) begin
        csr2tdu_resp = SCR1_CSR_RESP_OK;

        // Access enable
        if( csr2tdu_addr == SCR1_CSR_ADDR_TDU_OFFS_TSELECT ) begin
            csr_addr_tselect_cmb = 1'b1;
            // Read data
            csr2tdu_rdata        = tselect_ff;
        end
        if( csr2tdu_addr == SCR1_CSR_ADDR_TDU_OFFS_TDATA2 ) begin
            for( int unsigned i = 0; i < MTRIG_NUM; ++i ) begin
                if( tselect_ff == i ) begin
                    csr_addr_tdata2_cmb[i] = 1'b1;
                    // Read data
                    csr2tdu_rdata          = tdata2[ i ];
                end
            end
        end
        if( csr2tdu_addr == SCR1_CSR_ADDR_TDU_OFFS_TDATA1 ) begin
            for( int unsigned i = 0; i < MTRIG_NUM; ++i ) begin
                if( tselect_ff == i ) begin
                    csr_addr_mcontrol_cmb[ i ] = 1'b1;
                    // Read data
                    csr2tdu_rdata[ SCR1_TDU_TDATA1_TYPE_HI:
                                   SCR1_TDU_TDATA1_TYPE_LO ]      = SCR1_TDU_MCONTROL_TYPE_VAL;
                    csr2tdu_rdata[ SCR1_TDU_TDATA1_DMODE ]        = mcontrol_dmode_ff[ i ];

                    csr2tdu_rdata[ SCR1_TDU_MCONTROL_MASKMAX_HI:
                                   SCR1_TDU_MCONTROL_MASKMAX_LO ] = SCR1_TDU_MCONTROL_MASKMAX_VAL;
                    csr2tdu_rdata[ SCR1_TDU_MCONTROL_HIT ]        = mcontrol_hit_ff[ i ];
                    csr2tdu_rdata[ SCR1_TDU_MCONTROL_SELECT ]     = SCR1_TDU_MCONTROL_SELECT_VAL;
                    csr2tdu_rdata[ SCR1_TDU_MCONTROL_TIMING ]     = SCR1_TDU_MCONTROL_TIMING_VAL;
                    csr2tdu_rdata[ SCR1_TDU_MCONTROL_ACTION_HI:
                                   SCR1_TDU_MCONTROL_ACTION_LO ]  = mcontrol_action_ff[ i ];
                    csr2tdu_rdata[ SCR1_TDU_MCONTROL_CHAIN ]      = 1'b0;
                    csr2tdu_rdata[ SCR1_TDU_MCONTROL_MATCH_HI:
                                   SCR1_TDU_MCONTROL_MATCH_LO ]   = 1'b0;
                    csr2tdu_rdata[ SCR1_TDU_MCONTROL_M ]          = mcontrol_m_ff[ i ];
                    csr2tdu_rdata[ SCR1_TDU_MCONTROL_RESERVEDA ]  = SCR1_TDU_MCONTROL_RESERVEDA_VAL;
                    csr2tdu_rdata[ SCR1_TDU_MCONTROL_S ]          = 1'b0;
                    csr2tdu_rdata[ SCR1_TDU_MCONTROL_U ]          = 1'b0;
                    csr2tdu_rdata[ SCR1_TDU_MCONTROL_EXECUTE ]    = mcontrol_execution_ff[ i ];
                    csr2tdu_rdata[ SCR1_TDU_MCONTROL_STORE ]      = mcontrol_store_ff[ i ];
                    csr2tdu_rdata[ SCR1_TDU_MCONTROL_LOAD ]       = mcontrol_load_ff[ i ];
                end
            end
`ifdef SCR1_BRKM_BRKPT_ICOUNT_EN
            if( tselect_ff == (SCR1_TDU_ALLTRIG_NUM - 1'b1) ) begin
                csr_addr_icount_cmb = 1'b1;
                // Read data
                csr2tdu_rdata[ SCR1_TDU_TDATA1_TYPE_HI:
                               SCR1_TDU_TDATA1_TYPE_LO ]      = SCR1_TDU_ICOUNT_TYPE_VAL;
                csr2tdu_rdata[ SCR1_TDU_TDATA1_DMODE ]        = icount_dmode_ff;

                csr2tdu_rdata[ SCR1_TDU_ICOUNT_HIT ]          = icount_hit_ff;
                csr2tdu_rdata[ SCR1_TDU_ICOUNT_COUNT_HI:
                               SCR1_TDU_ICOUNT_COUNT_LO ]     = icount_count_ff;
                csr2tdu_rdata[ SCR1_TDU_ICOUNT_U ]            = 1'b0;
                csr2tdu_rdata[ SCR1_TDU_ICOUNT_S ]            = 1'b0;
                csr2tdu_rdata[ SCR1_TDU_ICOUNT_M ]            = icount_m_ff;
                csr2tdu_rdata[ SCR1_TDU_ICOUNT_ACTION_HI:
                               SCR1_TDU_ICOUNT_ACTION_LO ]    = icount_action_ff;
            end
`endif // SCR1_BRKM_BRKPT_ICOUNT_EN
        end
        if( csr2tdu_addr == SCR1_CSR_ADDR_TDU_OFFS_TINFO ) begin
            for( int unsigned i = 0; i < MTRIG_NUM; ++i ) begin
                if( tselect_ff == i ) begin
                    // Read data
                    csr2tdu_rdata[ SCR1_TDU_MCONTROL_TYPE_VAL ] = 1'b1;
                end
            end
`ifdef SCR1_BRKM_BRKPT_ICOUNT_EN
            if( tselect_ff == (SCR1_TDU_ALLTRIG_NUM - 1'b1) ) begin
                // Read data
                csr2tdu_rdata[ SCR1_TDU_ICOUNT_TYPE_VAL ] = 1'b1;
            end
`endif // SCR1_BRKM_BRKPT_ICOUNT_EN
        end

        // Write data
        if( csr2tdu_cmd == SCR1_CSR_CMD_WRITE ) begin
            csr_wr_cmb      = 1'b1;
            csr_wr_data_cmb = csr2tdu_wdata;
        end
        if( csr2tdu_cmd == SCR1_CSR_CMD_SET ) begin
            csr_wr_cmb      = |csr2tdu_wdata;
            csr_wr_data_cmb = csr2tdu_rdata | csr2tdu_wdata;
        end
        if( csr2tdu_cmd == SCR1_CSR_CMD_CLEAR ) begin
            csr_wr_cmb      = |csr2tdu_wdata;
            csr_wr_data_cmb = csr2tdu_rdata & ~csr2tdu_wdata;
        end
    end
end

// Trigger select
// --------------

always_ff @(negedge rst_n, posedge clk) begin
    if( ~rst_n ) begin
        tselect_ff <= 1'b0;
    end else if( clk_en ) begin
        if( csr_addr_tselect_cmb & csr_wr_cmb ) begin
            if( csr_wr_data_cmb[ALLTRIG_W-1:0] < ALLTRIG_NUM ) begin
                tselect_ff <= csr_wr_data_cmb[ALLTRIG_W-1:0];
            end
        end
    end
end

`ifdef SCR1_BRKM_BRKPT_ICOUNT_EN
// Breakpoint on instruction counter
// ---------------------------------

// Hit logic
always_comb begin
    icount_hit_cmb = 1'b0;
    icount_decrement_cmb = 1'b0;

    if( ~dsbl ) begin
        if( icount_m_ff ) begin
            icount_hit_cmb       = exu2tdu_i_mon.vd & (icount_count_ff == 1'b1) & ~icount_skip_ff;
            icount_decrement_cmb = exu2tdu_i_mon.vd & (icount_count_ff != 1'b0);
        end
    end
end

// Clock enable logic
always_comb begin
    clk_en_icount_cmb = (csr_addr_icount_cmb & csr_wr_cmb) | icount_m_ff;
end

// Write enable logic for tdata
always_comb begin
    icount_write_en = icount_dmode_ff ? dsbl : 1'b1;
end

// Trigger enable/hit
always_ff @(negedge rst_n, posedge clk) begin
    if( ~rst_n ) begin
        icount_dmode_ff  <= 1'b0;
        icount_m_ff      <= 1'b0;
        icount_action_ff <= 1'b0;
        icount_hit_ff    <= 1'b0;
        icount_count_ff  <= 1'b0;
        icount_skip_ff   <= 1'b0;
    end else if( clk_en ) begin
        if( clk_en_icount_cmb ) begin
            if( csr_addr_icount_cmb & csr_wr_cmb & icount_write_en ) begin
                icount_dmode_ff <= csr_wr_data_cmb[SCR1_TDU_TDATA1_DMODE];
                icount_m_ff <= csr_wr_data_cmb[ SCR1_TDU_ICOUNT_M ];
                icount_action_ff <= csr_wr_data_cmb[SCR1_TDU_ICOUNT_ACTION_HI:SCR1_TDU_ICOUNT_ACTION_LO] == 1'b1;
            end

            if( csr_addr_icount_cmb & csr_wr_cmb & icount_write_en ) begin
                icount_hit_ff <= csr_wr_data_cmb[SCR1_TDU_ICOUNT_HIT];
            end else if( exu2tdu_bp_retire[ALLTRIG_NUM - 1'b1] ) begin
                icount_hit_ff <= 1'b1;
            end

            if( csr_addr_icount_cmb & csr_wr_cmb & icount_write_en ) begin
                icount_count_ff <= csr_wr_data_cmb[SCR1_TDU_ICOUNT_COUNT_HI:SCR1_TDU_ICOUNT_COUNT_LO];
            end else if( icount_decrement_cmb & exu2tdu_i_mon.req & ~icount_skip_ff ) begin
                icount_count_ff <= icount_count_ff - 1'b1;
            end

             // skip scr write instruction to icount trigger
            if( csr_addr_icount_cmb & csr_wr_cmb ) begin
                icount_skip_ff <= csr_wr_data_cmb[ SCR1_TDU_ICOUNT_M ];
            end else if( icount_skip_ff & icount_decrement_cmb & exu2tdu_i_mon.req ) begin
                icount_skip_ff <= 1'b0;
            end
        end
    end
end
`endif // SCR1_BRKM_BRKPT_ICOUNT_EN

// Breakpoint/watchpoint on matching address
// -----------------------------------------

generate for( gvar_trig = 0; $unsigned(gvar_trig) < MTRIG_NUM; ++gvar_trig ) begin : gblock_mtrig

// Breakpoint hit logic
always_comb begin
    mcontrol_execution_hit_cmb[gvar_trig] = 1'b0;

    if( ~dsbl ) begin
        if( mcontrol_m_ff[gvar_trig] ) begin
            if(  mcontrol_execution_ff[gvar_trig] ) begin

                mcontrol_execution_hit_cmb[gvar_trig] = exu2tdu_i_mon.vd & exu2tdu_i_mon.addr == tdata2[gvar_trig];
            end
        end
    end
end

// Watchpoint hit logic
always_comb begin
    mcontrol_ldst_hit_cmb[gvar_trig] = 1'b0;

    if( ~dsbl ) begin
        if( mcontrol_m_ff[gvar_trig] ) begin
            mcontrol_ldst_hit_cmb[gvar_trig] =  tdu2lsu_d_mon.vd &
                                                ((mcontrol_load_ff[gvar_trig] & tdu2lsu_d_mon.load) |
                                                    (mcontrol_store_ff[gvar_trig] & tdu2lsu_d_mon.store)) &
                                                tdu2lsu_d_mon.addr == tdata2[gvar_trig];
        end
    end
end

// Clock enable logic
always_comb begin
    clk_en_mcontrol_cmb[gvar_trig] = (csr_addr_mcontrol_cmb[gvar_trig] & csr_wr_cmb) |
                                      mcontrol_m_ff[gvar_trig];
end

// Write enable logic for tdata
always_comb begin
    mcontrol_write_en[ gvar_trig ] = mcontrol_dmode_ff[ gvar_trig ] ? dsbl : 1'b1;
end

// Trigger enable/hit
always_ff @(negedge rst_n, posedge clk) begin
    if( ~rst_n ) begin
        mcontrol_dmode_ff[gvar_trig]     <= 1'b0;
        mcontrol_m_ff[gvar_trig]         <= 1'b0;
        mcontrol_execution_ff[gvar_trig] <= 1'b0;
        mcontrol_load_ff[gvar_trig]      <= 1'b0;
        mcontrol_store_ff[gvar_trig]     <= 1'b0;
        mcontrol_action_ff[gvar_trig]    <= 1'b0;
        mcontrol_hit_ff[gvar_trig]       <= 1'b0;
    end else if( clk_en ) begin
        if( clk_en_mcontrol_cmb[gvar_trig] ) begin
            if( csr_addr_mcontrol_cmb[gvar_trig] & csr_wr_cmb & mcontrol_write_en[ gvar_trig ] ) begin
                mcontrol_dmode_ff[gvar_trig] <= csr_wr_data_cmb[SCR1_TDU_TDATA1_DMODE];

                // Select privilege mode
                mcontrol_m_ff[gvar_trig] <= csr_wr_data_cmb[SCR1_TDU_MCONTROL_M];

                // Select type
                mcontrol_execution_ff[gvar_trig] <= csr_wr_data_cmb[SCR1_TDU_MCONTROL_EXECUTE];
                mcontrol_load_ff[gvar_trig]      <= csr_wr_data_cmb[SCR1_TDU_MCONTROL_LOAD];
                mcontrol_store_ff[gvar_trig]     <= csr_wr_data_cmb[SCR1_TDU_MCONTROL_STORE];

                // Select action: dmode/exception
                mcontrol_action_ff[gvar_trig]    <= csr_wr_data_cmb[SCR1_TDU_MCONTROL_ACTION_HI:SCR1_TDU_MCONTROL_ACTION_LO] == 1'b1;

                // Exact equality is supported only for match type of triggers (zero value)
                // Chain is not supported
            end

            // Hit status
            if( csr_addr_mcontrol_cmb[gvar_trig] & csr_wr_cmb & mcontrol_write_en[ gvar_trig ] ) begin
                mcontrol_hit_ff[gvar_trig] <= csr_wr_data_cmb[SCR1_TDU_MCONTROL_HIT];
            end else if( exu2tdu_bp_retire[gvar_trig] ) begin
                mcontrol_hit_ff[gvar_trig] <= 1'b1;
            end
        end
    end
end

// Etalon address/border
always_ff @(posedge clk) begin
    if( clk_en ) begin
        if( csr_addr_tdata2_cmb[gvar_trig] & csr_wr_cmb ) begin
            if( mcontrol_write_en[ gvar_trig ] ) begin
                tdata2[gvar_trig] <= csr_wr_data_cmb;
            end
        end
    end
end

end endgenerate // gblock_mtrig

// Pipeline control
// ----------------

// Breakpoint
always_comb begin
    // Invalidate matching instruction in writeback
    tdu2exu_i_match = mcontrol_execution_hit_cmb;

    // Load/store goes to lsu in parallel with exception
    // request goes to epu because of that this signal
    // invalidate load/store in lsu
    tdu2lsu_i_x_req = |mcontrol_execution_hit_cmb;

    // Generate exception
    tdu2exu_i_x_req = |mcontrol_execution_hit_cmb;

`ifdef SCR1_BRKM_BRKPT_ICOUNT_EN
    tdu2exu_i_match[SCR1_TDU_ALLTRIG_NUM-1] = icount_hit_cmb;
    tdu2lsu_i_x_req = tdu2lsu_i_x_req | icount_hit_cmb;
    tdu2exu_i_x_req = tdu2exu_i_x_req | icount_hit_cmb;
`endif // SCR1_BRKM_BRKPT_ICOUNT_EN
end

// Watchpoint
always_comb begin
    // Invalidate matching instruction in writeback
    tdu2lsu_d_match = mcontrol_ldst_hit_cmb;
    // Invalidate instruction in lsu
    tdu2lsu_d_x_req = |mcontrol_ldst_hit_cmb;
end

// Debug mode request
always_comb begin
    tdu2hdu_dmode_req = 1'b0;

    for( int unsigned i = 0; i < MTRIG_NUM; ++i) begin
        tdu2hdu_dmode_req = tdu2hdu_dmode_req |
                            (mcontrol_action_ff[i] == 1'b1 & exu2tdu_bp_retire[i]);
    end

`ifdef SCR1_BRKM_BRKPT_ICOUNT_EN
    tdu2hdu_dmode_req = tdu2hdu_dmode_req |
                        (icount_action_ff == 1'b1 & exu2tdu_bp_retire[ALLTRIG_NUM-1]);
`endif // SCR1_BRKM_BRKPT_ICOUNT_EN
end

`ifndef SCR1_BRKM_EN
// LSU debug mode enable (2 clocks on each operation)
always_comb tdu2lsu_brk_en = (|mcontrol_m_ff) | icount_m_ff;
`endif // SCR1_BRKM_EN

`ifdef SCR1_SIM_ENV
`ifndef VERILATOR
//-------------------------------------------------------------------------------
// Assertion
//-------------------------------------------------------------------------------

SVA_TDU_X_CONTROL :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        !$isunknown( {rst_n,clk,clk_en,dsbl,csr2tdu_req,exu2tdu_i_mon.vd,tdu2lsu_d_mon.vd,exu2tdu_bp_retire} )
    )
    else $error("TDU Error: control signals is X - %0b",{rst_n,clk,clk_en,dsbl,csr2tdu_req,exu2tdu_i_mon.vd,tdu2lsu_d_mon.vd,exu2tdu_bp_retire});

SVA_TDU_X_CSR :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        csr2tdu_req |-> !$isunknown( {csr2tdu_cmd,csr2tdu_addr} )
    )
    else $error("TDU Error: csr is X");

SVA_TDU_XW_CSR :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        (csr2tdu_req & csr_wr_cmb) |-> !$isunknown( csr2tdu_wdata )
    )
    else $error("TDU Error: csr wdata is X ");

SVA_TDU_X_IMON :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        exu2tdu_i_mon.vd |-> !$isunknown( {exu2tdu_i_mon.req,exu2tdu_i_mon.addr} )
    )
    else $error("TDU Error: imonitor is X");

SVA_TDU_X_DMON :
    assert property (
        @(negedge clk) disable iff (~rst_n)
        tdu2lsu_d_mon.vd |-> !$isunknown( {tdu2lsu_d_mon} )
    )
    else $error("TDU Error: dmonitor is X");

`endif // VERILATOR
`endif // SCR1_SIM_ENV

endmodule : scr1_pipe_tdu

`endif // SCR1_BRKM_EN
