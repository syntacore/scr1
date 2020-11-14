/// Copyright by Syntacore LLC © 2016-2020. See LICENSE for details
/// @file       <scr1_ipic.sv>
/// @brief      Integrated Programmable Interrupt Controller (IPIC)
///

//------------------------------------------------------------------------------
 //
 // Functionality:
 // - Synchronizes IRQ lines (optional)
 // - Detects level and edge (with optional lines inversion) of IRQ lines
 // - Setups interrupts handling (mode, inversion, enable)
 // - Provides information about pending interrupts and interrupts currently in
 //   service
 // - Generates interrupt request to CSR
 //
 // Structure:
 // - IRQ lines handling (synchronization, level and edge detection) logic
 // - IPIC registers:
 //   - CISV
 //   - CICSR
 //   - EOI
 //   - SOI
 //   - IDX
 //   - IPR
 //   - ISVR
 //   - IER
 //   - IMR
 //   - IINVR
 //   - ICSR
 // - Priority interrupt generation logic
 //
//------------------------------------------------------------------------------

`include "scr1_arch_description.svh"

`ifdef SCR1_IPIC_EN

`include "scr1_ipic.svh"

module scr1_ipic
(
    // Common
    input   logic                                   rst_n,                  // IPIC reset
    input   logic                                   clk,                    // IPIC clock

    // External Interrupt lines
    input   logic [SCR1_IRQ_LINES_NUM-1:0]          soc2ipic_irq_lines_i,   // External IRQ lines

    // CSR <-> IPIC interface
    input   logic                                   csr2ipic_r_req_i,       // IPIC read request
    input   logic                                   csr2ipic_w_req_i,       // IPIC write request
    input   logic [2:0]                             csr2ipic_addr_i,        // IPIC address
    input   logic [`SCR1_XLEN-1:0]                  csr2ipic_wdata_i,       // IPIC write data
    output  logic [`SCR1_XLEN-1:0]                  ipic2csr_rdata_o,       // IPIC read data
    output  logic                                   ipic2csr_irq_m_req_o    // IRQ request from IPIC
);

//-------------------------------------------------------------------------------
// Local types declaration
//-------------------------------------------------------------------------------
typedef struct {
    logic                                   vd;
    logic                                   idx;
} type_scr1_search_one_2_s;

typedef struct {
    logic                                   vd;
    logic   [SCR1_IRQ_VECT_WIDTH-1:0]       idx;
} type_scr1_search_one_16_s;

typedef struct packed {
    logic                                   ip;
    logic                                   ie;
    logic                                   im;
    logic                                   inv;
    logic                                   is;
    logic   [SCR1_IRQ_LINES_WIDTH-1:0]      line;
} type_scr1_icsr_m_s;

typedef struct packed {
    logic                                   ip;
    logic                                   ie;
} type_scr1_cicsr_s;

//-------------------------------------------------------------------------------
// Local functions declaration
//-------------------------------------------------------------------------------

function automatic type_scr1_search_one_2_s scr1_search_one_2(
    input   logic   [1:0] din
);
    type_scr1_search_one_2_s tmp;
begin
    tmp.vd  = |din;
    tmp.idx = ~din[0];
    return  tmp;
end
endfunction : scr1_search_one_2

function automatic type_scr1_search_one_16_s scr1_search_one_16(
    input   logic [15:0]    din
);
begin
    logic [7:0]         stage1_vd;
    logic [3:0]         stage2_vd;
    logic [1:0]         stage3_vd;

    logic               stage1_idx [7:0];
    logic [1:0]         stage2_idx [3:0];
    logic [2:0]         stage3_idx [1:0];
    type_scr1_search_one_16_s result;

    // Stage 1
    for (int unsigned i=0; i<8; ++i) begin
        type_scr1_search_one_2_s tmp;
        tmp = scr1_search_one_2(din[(i+1)*2-1-:2]);
        stage1_vd[i]  = tmp.vd;
        stage1_idx[i] = tmp.idx;
    end

    // Stage 2
    for (int unsigned i=0; i<4; ++i) begin
        type_scr1_search_one_2_s tmp;
        tmp = scr1_search_one_2(stage1_vd[(i+1)*2-1-:2]);
        stage2_vd[i]  = tmp.vd;
        stage2_idx[i] = (~tmp.idx) ? {tmp.idx, stage1_idx[2*i]} : {tmp.idx, stage1_idx[2*i+1]};
    end

    // Stage 3
    for (int unsigned i=0; i<2; ++i) begin
        type_scr1_search_one_2_s tmp;
        tmp = scr1_search_one_2(stage2_vd[(i+1)*2-1-:2]);
        stage3_vd[i]  = tmp.vd;
        stage3_idx[i] = (~tmp.idx) ? {tmp.idx, stage2_idx[2*i]} : {tmp.idx, stage2_idx[2*i+1]};
    end

    // Stage 4
    result.vd = |stage3_vd;
    result.idx = (stage3_vd[0]) ? {1'b0, stage3_idx[0]} : {1'b1, stage3_idx[1]};

    return result;
end
endfunction : scr1_search_one_16

//------------------------------------------------------------------------------
// Local signals declaration
//------------------------------------------------------------------------------

// IRQ lines handling signals
//------------------------------------------------------------------------------

logic [SCR1_IRQ_VECT_NUM-1:0]           irq_lines;              // Internal IRQ lines
`ifdef SCR1_IPIC_SYNC_EN
logic [SCR1_IRQ_VECT_NUM-1:0]           irq_lines_sync;
`endif // SCR1_IPIC_SYNC_EN
logic [SCR1_IRQ_VECT_NUM-1:0]           irq_lines_dly;          // Internal IRQ lines delayed for 1 cycle
logic [SCR1_IRQ_VECT_NUM-1:0]           irq_edge_detected;      // IRQ lines edge detected flags
logic [SCR1_IRQ_VECT_NUM-1:0]           irq_lvl;                // IRQ lines level

// IPIC registers
//------------------------------------------------------------------------------

// CISV register
logic                                   ipic_cisv_upd;          // Current Interrupt Vecotr in Service register update
logic [SCR1_IRQ_VECT_WIDTH-1:0]         ipic_cisv_ff;           // Current Interrupt Vector in Service register
logic [SCR1_IRQ_VECT_WIDTH-1:0]         ipic_cisv_next;         // Current Interrupt Vector in Service register next value

// CICS register (CICSR)
logic                                   cicsr_wr_req;           // Write request to Current Interrupt Control Status register
type_scr1_cicsr_s                       ipic_cicsr;             // Current Interrupt Control Status register

// EOI register
logic                                   eoi_wr_req;             // Write request to End of Interrupt register
logic                                   ipic_eoi_req;           // Request to end the interrupt that is currently in service

// SOI register
logic                                   soi_wr_req;             // Write request to Start of Interrupt register
logic                                   ipic_soi_req;           // Request to start the interrupt

// IDX register (IDXR)
logic                                   idxr_wr_req;            // Write request to Index register
logic [SCR1_IRQ_IDX_WIDTH-1:0]          ipic_idxr_ff;           // Index register

// IP register (IPR)
logic                                   ipic_ipr_upd;           // Interrupt pending register update
logic [SCR1_IRQ_VECT_NUM-1:0]           ipic_ipr_ff;            // Interrupt pending register
logic [SCR1_IRQ_VECT_NUM-1:0]           ipic_ipr_next;          // Interrupt pending register next value
logic [SCR1_IRQ_VECT_NUM-1:0]           ipic_ipr_clr_cond;      // Interrupt pending clear condition
logic [SCR1_IRQ_VECT_NUM-1:0]           ipic_ipr_clr_req;       // Interrupt pending clear request
logic [SCR1_IRQ_VECT_NUM-1:0]           ipic_ipr_clr;           // Interrupt pending clear operation

// ISV register (ISVR)
logic                                   ipic_isvr_upd;          // Interrupt Serviced register update
logic [SCR1_IRQ_VECT_NUM-1:0]           ipic_isvr_ff;           // Interrupt Serviced register
logic [SCR1_IRQ_VECT_NUM-1:0]           ipic_isvr_next;         // Interrupt Serviced register next value

// IE register (IER)
logic                                   ipic_ier_upd;           // Interrupt enable register update
logic [SCR1_IRQ_VECT_NUM-1:0]           ipic_ier_ff;            // Interrupt enable register
logic [SCR1_IRQ_VECT_NUM-1:0]           ipic_ier_next;          // Interrupt enable register next value

// IM register (IMR)
logic [SCR1_IRQ_VECT_NUM-1:0]           ipic_imr_ff;            // Interrupt mode register
logic [SCR1_IRQ_VECT_NUM-1:0]           ipic_imr_next;          // Interrupt mode register next value

// IINV register (IINVR)
logic [SCR1_IRQ_VECT_NUM-1:0]           ipic_iinvr_ff;          // Interrupt Inversion register
logic [SCR1_IRQ_VECT_NUM-1:0]           ipic_iinvr_next;        // Interrupt Inversion register next value

// ICS register (ICSR)
logic                                   icsr_wr_req;            // Write request to Interrupt Control Status register
type_scr1_icsr_m_s                      ipic_icsr;              // Interrupt Control Status register

// Priority interrupt generation signals
//------------------------------------------------------------------------------

// Serviced interrupt signals
logic                                   irq_serv_vd;            // There is an interrupt in service
logic [SCR1_IRQ_VECT_WIDTH-1:0]         irq_serv_idx;           // Index of an interrupt that is currently in service

// Requested interrupt signals
logic                                   irq_req_vd;             // There is a requested interrupt
logic [SCR1_IRQ_VECT_WIDTH-1:0]         irq_req_idx;            // Index of a requested interrupt

// Interrupt requested on "end of the previous interrupt" signals
logic                                   irq_eoi_req_vd;         // There is a requested interrupt when the previous one has ended
logic [SCR1_IRQ_VECT_WIDTH-1:0]         irq_eoi_req_idx;        // Index of an interrupt requested when the previous one has ended

logic [SCR1_IRQ_VECT_NUM-1:0]           irq_req_v;              // Vector of interrupts that are pending and enabled

logic                                   irq_start_vd;           // Request to start an interrupt is valid
logic                                   irq_hi_prior_pnd;       // There is a pending IRQ with a priority higher than of the interrupt that is currently in service

type_scr1_search_one_16_s               irr_priority;           // Structure for vd and idx of the requested interrupt
type_scr1_search_one_16_s               isvr_priority_eoi;      // Structure for vd and idx of the interrupt requested when the previous interrupt has ended
logic [SCR1_IRQ_VECT_NUM-1:0]           ipic_isvr_eoi;          // Interrupt Serviced register when the previous interrupt has ended

//------------------------------------------------------------------------------
// IRQ lines handling
//------------------------------------------------------------------------------

`ifdef SCR1_IPIC_SYNC_EN
// IRQ lines synchronization
//------------------------------------------------------------------------------

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        irq_lines_sync <= '0;
        irq_lines      <= '0;
    end else begin
        irq_lines_sync <= soc2ipic_irq_lines_i;
        irq_lines      <= irq_lines_sync;
    end
end
`else // SCR1_IPIC_SYNC_EN
assign irq_lines = soc2ipic_irq_lines_i;
`endif // SCR1_IPIC_SYNC_EN

// IRQ lines level detection
//------------------------------------------------------------------------------

assign irq_lvl = irq_lines ^ ipic_iinvr_next;

// IRQ lines edge detection
//------------------------------------------------------------------------------

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        irq_lines_dly <= '0;
    end else begin
        irq_lines_dly <= irq_lines;
    end
end

assign irq_edge_detected = (irq_lines_dly ^ irq_lines) & irq_lvl;

//------------------------------------------------------------------------------
// IPIC registers read/write interface
//------------------------------------------------------------------------------

// Read Logic
//------------------------------------------------------------------------------

// Read data multiplexer
always_comb begin
    ipic2csr_rdata_o  = '0;

    if (csr2ipic_r_req_i) begin
        case (csr2ipic_addr_i)
            SCR1_IPIC_CISV : begin
                ipic2csr_rdata_o[SCR1_IRQ_VECT_WIDTH-1:0] = irq_serv_vd
                                                          ? ipic_cisv_ff
                                                          : SCR1_IRQ_VOID_VECT_NUM;
            end
            SCR1_IPIC_CICSR : begin
                ipic2csr_rdata_o[SCR1_IPIC_ICSR_IP]  = ipic_cicsr.ip;
                ipic2csr_rdata_o[SCR1_IPIC_ICSR_IE]  = ipic_cicsr.ie;
            end
            SCR1_IPIC_IPR : begin
                ipic2csr_rdata_o = `SCR1_XLEN'(ipic_ipr_ff);
            end
            SCR1_IPIC_ISVR : begin
                ipic2csr_rdata_o = `SCR1_XLEN'(ipic_isvr_ff);
            end
            SCR1_IPIC_EOI,
            SCR1_IPIC_SOI : begin
                ipic2csr_rdata_o = '0;
            end
            SCR1_IPIC_IDX : begin
                ipic2csr_rdata_o = `SCR1_XLEN'(ipic_idxr_ff);
            end
            SCR1_IPIC_ICSR : begin
                ipic2csr_rdata_o[SCR1_IPIC_ICSR_IP]      = ipic_icsr.ip;
                ipic2csr_rdata_o[SCR1_IPIC_ICSR_IE]      = ipic_icsr.ie;
                ipic2csr_rdata_o[SCR1_IPIC_ICSR_IM]      = ipic_icsr.im;
                ipic2csr_rdata_o[SCR1_IPIC_ICSR_INV]     = ipic_icsr.inv;
                ipic2csr_rdata_o[SCR1_IPIC_ICSR_PRV_MSB:
                                 SCR1_IPIC_ICSR_PRV_LSB] = SCR1_IPIC_PRV_M;
                ipic2csr_rdata_o[SCR1_IPIC_ICSR_IS]      = ipic_icsr.is;
                ipic2csr_rdata_o[SCR1_IPIC_ICSR_LN_MSB-1:
                                 SCR1_IPIC_ICSR_LN_LSB]  = ipic_icsr.line;
            end
            default : begin
                ipic2csr_rdata_o = 'x;
            end
        endcase
    end
end

// Write logic
//------------------------------------------------------------------------------

// Register selection
always_comb begin
    cicsr_wr_req = 1'b0;
    eoi_wr_req   = 1'b0;
    soi_wr_req   = 1'b0;
    idxr_wr_req  = 1'b0;
    icsr_wr_req  = 1'b0;
    if (csr2ipic_w_req_i) begin
        case (csr2ipic_addr_i)
            SCR1_IPIC_CISV : begin end // Quiet Read-Only
            SCR1_IPIC_CICSR: cicsr_wr_req = 1'b1;
            SCR1_IPIC_IPR  : begin end
            SCR1_IPIC_ISVR : begin end // Quiet Read-Only
            SCR1_IPIC_EOI  : eoi_wr_req   = 1'b1;
            SCR1_IPIC_SOI  : soi_wr_req   = 1'b1;
            SCR1_IPIC_IDX  : idxr_wr_req  = 1'b1;
            SCR1_IPIC_ICSR : icsr_wr_req  = 1'b1;
            default : begin // Illegal IPIC register address
                cicsr_wr_req = 'x;
                eoi_wr_req   = 'x;
                soi_wr_req   = 'x;
                idxr_wr_req  = 'x;
                icsr_wr_req  = 'x;
            end
        endcase
    end
end

//------------------------------------------------------------------------------
// IPIC registers
//------------------------------------------------------------------------------
//
 // Registers:
 // - Current Interrupt Vector in Service (CISV) register
 // - Current Interrupt Control Status (CICSR) register
 // - End of Interrupt (EOI) register
 // - Start of Interrupt (SOI) register
 // - Index (IDX) register
 // - Interrupt Pending Register (IPR)
 // - Interrupt Serviced Register (ISVR)
 // - Interrupt Enable Register (IER)
 // - Interrupt Mode Register (IMR)
 // - Interrupt Inversion Register (IINVR)
 // - Interrupt Control Status Register (ICSR)
//

// CISV register
//------------------------------------------------------------------------------
// Contains number of the interrupt vector currently in service. When no
// interrupts are in service, contains number of the void interrupt vector (0x10).
// The register cannot contain all 0's

assign ipic_cisv_upd = irq_start_vd | ipic_eoi_req;

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        ipic_cisv_ff <= SCR1_IRQ_VOID_VECT_NUM;
    end else if (ipic_cisv_upd) begin
        ipic_cisv_ff <= ipic_cisv_next;
    end
end

assign ipic_cisv_next = irq_start_vd ? irq_req_idx
                      : ipic_eoi_req ? irq_eoi_req_vd ? irq_eoi_req_idx
                                                      : SCR1_IRQ_VOID_VECT_NUM
                                     : 1'b0;

assign irq_serv_idx = ipic_cisv_ff[SCR1_IRQ_VECT_WIDTH-2:0];
assign irq_serv_vd  = ~ipic_cisv_ff[SCR1_IRQ_VECT_WIDTH-1];

// CICSR register
//------------------------------------------------------------------------------
// Shows whether the interrupt currently in service is pending and enabled

assign ipic_cicsr.ip = ipic_ipr_ff[irq_serv_idx] & irq_serv_vd;
assign ipic_cicsr.ie = ipic_ier_ff[irq_serv_idx] & irq_serv_vd;

// EOI register
//------------------------------------------------------------------------------
// Writing any value to EOI register ends the interrupt which is currently in service

assign ipic_eoi_req = eoi_wr_req & irq_serv_vd;

// SOI register
//------------------------------------------------------------------------------
// Writing any value to SOI activates start of interrupt if one of the following
// conditions is true:
// - There is at least one pending interrupt with IE and ISR is zero
// - There is at least one pending interrupt with IE and higher priority than the
// interrupts currently in service

assign ipic_soi_req = soi_wr_req & irq_req_vd;

// IDX register
//------------------------------------------------------------------------------
// Defines the number of interrupt vector which is accessed through the IPIC_ICSR
// register

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        ipic_idxr_ff <= '0;
    end else if (idxr_wr_req) begin
        ipic_idxr_ff <= csr2ipic_wdata_i[SCR1_IRQ_IDX_WIDTH-1:0];
    end
end

// IPR
//------------------------------------------------------------------------------
// For every IRQ line shows whether there is a pending interrupt

assign ipic_ipr_upd = (ipic_ipr_next != ipic_ipr_ff);

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        ipic_ipr_ff <= '0;
    end else if (ipic_ipr_upd) begin
        ipic_ipr_ff <= ipic_ipr_next;
    end
end

always_comb begin
    ipic_ipr_clr_req = '0;
    if (csr2ipic_w_req_i) begin
        case (csr2ipic_addr_i)
            SCR1_IPIC_CICSR: ipic_ipr_clr_req[irq_serv_idx] = csr2ipic_wdata_i[SCR1_IPIC_ICSR_IP]
                                                            & irq_serv_vd;
            SCR1_IPIC_IPR  : ipic_ipr_clr_req               = csr2ipic_wdata_i[SCR1_IRQ_VECT_NUM-1:0];
            SCR1_IPIC_SOI  : ipic_ipr_clr_req[irq_req_idx]  = irq_req_vd;
            SCR1_IPIC_ICSR : ipic_ipr_clr_req[ipic_idxr_ff] = csr2ipic_wdata_i[SCR1_IPIC_ICSR_IP];
            default        : begin end
        endcase
    end
end

assign ipic_ipr_clr_cond = ~irq_lvl | ipic_imr_next;
assign ipic_ipr_clr      = ipic_ipr_clr_req & ipic_ipr_clr_cond;

always_comb begin
    ipic_ipr_next = '0;
    for (int unsigned i=0; i<SCR1_IRQ_VECT_NUM; ++i) begin
        ipic_ipr_next[i] = ipic_ipr_clr[i] ? 1'b0
                         : ~ipic_imr_ff[i] ? irq_lvl[i]
                                           : ipic_ipr_ff[i] | irq_edge_detected[i];
    end
end

// ISVR
//------------------------------------------------------------------------------
// For every IRQ line shows whether the interrupt is in service or not

assign ipic_isvr_upd = irq_start_vd | ipic_eoi_req;

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        ipic_isvr_ff <= '0;
    end else if (ipic_isvr_upd) begin
        ipic_isvr_ff <= ipic_isvr_next;
    end
end

always_comb begin
    ipic_isvr_eoi = ipic_isvr_ff;
    if (irq_serv_vd) begin
        ipic_isvr_eoi[irq_serv_idx] = 1'b0;
    end
end

always_comb begin
    ipic_isvr_next = ipic_isvr_ff;
    if (irq_start_vd) begin
        ipic_isvr_next[irq_req_idx] = 1'b1;
    end else if (ipic_eoi_req) begin
        ipic_isvr_next = ipic_isvr_eoi;
    end
end

// IER
//------------------------------------------------------------------------------
// Enables/disables interrupt for every IRQ line

assign ipic_ier_upd = cicsr_wr_req | icsr_wr_req;

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        ipic_ier_ff <= '0;
    end else if (ipic_ier_upd) begin
        ipic_ier_ff <= ipic_ier_next;
    end
end

always_comb begin
    ipic_ier_next = ipic_ier_ff;
    if (cicsr_wr_req) begin
        ipic_ier_next[irq_serv_idx] = irq_serv_vd
                                    ? csr2ipic_wdata_i[SCR1_IPIC_ICSR_IE]
                                    : ipic_ier_ff;
    end else if (icsr_wr_req) begin
        ipic_ier_next[ipic_idxr_ff] = csr2ipic_wdata_i[SCR1_IPIC_ICSR_IE];
    end
end

// IMR
//------------------------------------------------------------------------------
// For every IRQ line sets either Level (0) or Edge (1) detection

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        ipic_imr_ff <= '0;
    end else if (icsr_wr_req) begin
        ipic_imr_ff <= ipic_imr_next;
    end
end

always_comb begin
    ipic_imr_next = ipic_imr_ff;
    if (icsr_wr_req) begin
        ipic_imr_next[ipic_idxr_ff] = csr2ipic_wdata_i[SCR1_IPIC_ICSR_IM];
    end
end

// IINVR
//------------------------------------------------------------------------------
// For every IRQ line defines whether it should be inverted or not

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        ipic_iinvr_ff <= '0;
    end else if (icsr_wr_req) begin
        ipic_iinvr_ff <= ipic_iinvr_next;
    end
end

always_comb begin
    ipic_iinvr_next = ipic_iinvr_ff;
    if (icsr_wr_req) begin
        ipic_iinvr_next[ipic_idxr_ff] = csr2ipic_wdata_i[SCR1_IPIC_ICSR_INV];
    end
end

// ICSR
//------------------------------------------------------------------------------
// Holds control and status information about the interrupt defined by Index Register

assign ipic_icsr.ip    = ipic_ipr_ff  [ipic_idxr_ff];
assign ipic_icsr.ie    = ipic_ier_ff  [ipic_idxr_ff];
assign ipic_icsr.im    = ipic_imr_ff  [ipic_idxr_ff];
assign ipic_icsr.inv   = ipic_iinvr_ff[ipic_idxr_ff];
assign ipic_icsr.is    = ipic_isvr_ff [ipic_idxr_ff];
assign ipic_icsr.line  = SCR1_IRQ_LINES_WIDTH'(ipic_idxr_ff);

//------------------------------------------------------------------------------
// Priority IRQ generation logic
//------------------------------------------------------------------------------

assign irq_req_v = ipic_ipr_ff & ipic_ier_ff;

assign irr_priority        = scr1_search_one_16(irq_req_v);
assign irq_req_vd          = irr_priority.vd;
assign irq_req_idx         = irr_priority.idx;

assign isvr_priority_eoi   = scr1_search_one_16(ipic_isvr_eoi);
assign irq_eoi_req_vd      = isvr_priority_eoi.vd;
assign irq_eoi_req_idx     = isvr_priority_eoi.idx;

assign irq_hi_prior_pnd     = irq_req_idx < irq_serv_idx;

assign ipic2csr_irq_m_req_o = irq_req_vd & (~irq_serv_vd | irq_hi_prior_pnd);

assign irq_start_vd         = ipic2csr_irq_m_req_o & ipic_soi_req;

endmodule : scr1_ipic

`endif // SCR1_IPIC_EN