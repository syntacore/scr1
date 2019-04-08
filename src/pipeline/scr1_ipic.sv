/// Copyright by Syntacore LLC © 2016-2019. See LICENSE for details
/// @file       <scr1_ipic.sv>
/// @brief      Integrated Programmable Interrupt Controller (IPIC)
///

`include "scr1_arch_description.svh"

`ifdef SCR1_IPIC_EN

`include "scr1_ipic.svh"

module scr1_ipic
(
    // Common
    input   logic                                   rst_n,
    input   logic                                   clk,

    // External Interrupt lines
    input   logic [SCR1_IRQ_LINES_NUM-1:0]          irq_lines,

    // CSR <-> IPIC interface
    input   logic                                   csr2ipic_r_req,     // IPIC read request
    input   logic                                   csr2ipic_w_req,     // IPIC write request
    input   logic [2:0]                             csr2ipic_addr,      // IPIC address
    input   logic [`SCR1_XLEN-1:0]                  csr2ipic_wdata,     // IPIC write data
    output  logic [`SCR1_XLEN-1:0]                  ipic2csr_rdata,     // IPIC read data

    // Interface to Core
    output  logic                                   irq_m_req           // IRQ request from IPIC
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


//-------------------------------------------------------------------------------
// Local signals declaration
//-------------------------------------------------------------------------------
logic [SCR1_IRQ_VECT_NUM-1:0]           irq_lines_i;            // Internal IRQ lines
logic [SCR1_IRQ_VECT_NUM-1:0]           irq_edge_det;           // IRQ edge
logic [SCR1_IRQ_VECT_NUM-1:0]           irq_lvl;                // IRQ level
logic [SCR1_IRQ_VECT_NUM-1:0]           invr;                   // Inversion register
logic [SCR1_IRQ_VECT_NUM-1:0]           invr_new;               // Inversion register new value
logic [SCR1_IRQ_VECT_NUM-1:0]           irq_vect;               // Inversion IRQ mapped vector
logic [SCR1_IRQ_VECT_NUM-1:0]           imr;                    // Interrupt mode register
logic [SCR1_IRQ_VECT_NUM-1:0]           imr_new;                // Interrupt mode register new value

logic [SCR1_IRQ_VECT_NUM-1:0]           ipr;                    // Interrupt pending register;
                                                                    //  for level IRQ just translate the irq_vect,
                                                                    //  for edge IRQ - latch edge detection
logic [SCR1_IRQ_VECT_NUM-1:0]           ipr_new;                // New value for IPR
logic [SCR1_IRQ_VECT_NUM-1:0]           ipr_m;                  // Interrupt pending register for M-mode IRQ(IPIC_IPR_M)
logic [SCR1_IRQ_VECT_NUM-1:0]           ipr_clr;                // Interrupt pending clr

logic [SCR1_IRQ_VECT_NUM-1:0]           ier;                    // Interrupt enable register(IPIC_IER)
logic [SCR1_IRQ_VECT_NUM-1:0]           irr_m;                  // Interrupt register register(IPIC_IPR & IPIC_IER & PRV==M)


logic [SCR1_IRQ_VECT_WIDTH-1:0]         cisv_m;                 // Number of the current M-mode interrupt in service register(IPIC_CISV_M)
logic [SCR1_IRQ_IDX_WIDTH-1:0]          idxr_m;                 // M-mode index register(IPIC_IDX_M)
logic [SCR1_IRQ_VECT_NUM-1:0]           isvr_m;                 // M-mode in service register(IPIC_ISVR_M)
logic                                   soi_wr_m;               // Start of M-mode interrupt
logic                                   eoi_wr_m;               // End of M-mode current in service interrupt

type_scr1_icsr_m_s                      icsr_m;
type_scr1_cicsr_s                       cicsr_m;

type_scr1_search_one_16_s               irr_priority_m;
type_scr1_search_one_16_s               isvr_priority_eoi_m;
logic [SCR1_IRQ_VECT_NUM-1:0]           isvr_eoi_m;


genvar gen_i;

//-------------------------------------------------------------------------------
// Read Logic
//-------------------------------------------------------------------------------
always_comb begin
    logic cisv_found;

    cisv_found      = 1'b0;
    ipic2csr_rdata  = '0;
    if (csr2ipic_r_req) begin
        case (csr2ipic_addr)

            SCR1_IPIC_CISV : begin
                // Vector number for currently serviced interrupt
                for (int unsigned i=0; i<SCR1_IRQ_VECT_NUM; ++i) begin
                    if (cisv_m == i) begin
                        cisv_found |= 1'b1;
                        ipic2csr_rdata[SCR1_IRQ_VECT_WIDTH-1:0] |= cisv_m;
                    end
                end
                if (~cisv_found) begin
                    ipic2csr_rdata[SCR1_IRQ_VECT_WIDTH-1:0] = SCR1_IRQ_VOID_VECT_NUM;
                end
            end

            SCR1_IPIC_CICSR : begin
                // CSR for the currently serviced interrupts
                ipic2csr_rdata[SCR1_IPIC_ICSR_IP]  = cicsr_m.ip;
                ipic2csr_rdata[SCR1_IPIC_ICSR_IE]  = cicsr_m.ie;
            end

            SCR1_IPIC_IPR : begin
                // Aggregated pending interrupts
                ipic2csr_rdata = ipr_m;
            end

            SCR1_IPIC_ISVR : begin
                // Aggregated serviced interrupts
                ipic2csr_rdata = isvr_m;
            end

            SCR1_IPIC_EOI,
            SCR1_IPIC_SOI : begin
                ipic2csr_rdata = '0;
            end

            SCR1_IPIC_IDX : begin
                // Index register for access to interrupt CSRs
                ipic2csr_rdata = idxr_m;
            end

            SCR1_IPIC_ICSR : begin
                // Interrupt CSR pointed by IDX
                ipic2csr_rdata[SCR1_IPIC_ICSR_IP]  = icsr_m.ip;
                ipic2csr_rdata[SCR1_IPIC_ICSR_IE]  = icsr_m.ie;
                ipic2csr_rdata[SCR1_IPIC_ICSR_IM]  = icsr_m.im;
                ipic2csr_rdata[SCR1_IPIC_ICSR_INV] = icsr_m.inv;
                ipic2csr_rdata[SCR1_IPIC_ICSR_PRV_MSB:SCR1_IPIC_ICSR_PRV_LSB]   = SCR1_IPIC_PRV_M;
                ipic2csr_rdata[SCR1_IPIC_ICSR_IS]  = icsr_m.is;
                ipic2csr_rdata[SCR1_IPIC_ICSR_LN_LSB+SCR1_IRQ_LINES_WIDTH-1:SCR1_IPIC_ICSR_LN_LSB]  = icsr_m.line;
            end

            default : begin
                ipic2csr_rdata = 'x;
            end
        endcase
    end
end

assign icsr_m.ip    = ipr[idxr_m];
assign icsr_m.ie    = ier[idxr_m];
assign icsr_m.im    = imr[idxr_m];
assign icsr_m.inv   = invr[idxr_m];
assign icsr_m.is    = isvr_m[idxr_m];
assign icsr_m.line  = SCR1_IRQ_LINES_WIDTH'(idxr_m);

assign cicsr_m.ip   = ipr[cisv_m[SCR1_IRQ_VECT_WIDTH-2:0]] & ~cisv_m[SCR1_IRQ_VECT_WIDTH-1];
assign cicsr_m.ie   = ier[cisv_m[SCR1_IRQ_VECT_WIDTH-2:0]] & ~cisv_m[SCR1_IRQ_VECT_WIDTH-1];

//-------------------------------------------------------------------------------
// Write logic
//-------------------------------------------------------------------------------
always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        ier     <= '0;
        imr     <= '0;
        invr    <= '0;
        idxr_m  <= '0;
    end else if (csr2ipic_w_req) begin
        case (csr2ipic_addr)
            SCR1_IPIC_CICSR : begin
                // CSR for the currently serviced interrupt
                if (~cisv_m[SCR1_IRQ_VECT_WIDTH-1]) begin
                    ier[cisv_m[SCR1_IRQ_VECT_WIDTH-2:0]] <= csr2ipic_wdata[SCR1_IPIC_ICSR_IE];
                end
            end

            SCR1_IPIC_IDX : begin
                idxr_m      <= csr2ipic_wdata[SCR1_IRQ_IDX_WIDTH-1:0];
            end

            SCR1_IPIC_ICSR : begin
                ier[idxr_m]     <= csr2ipic_wdata[SCR1_IPIC_ICSR_IE];
                imr[idxr_m]     <= csr2ipic_wdata[SCR1_IPIC_ICSR_IM];
                invr[idxr_m]    <= csr2ipic_wdata[SCR1_IPIC_ICSR_INV];
            end

            default : begin
            end
        endcase
    end
end

//-------------------------------------------------------------------------------
// IPR clear generation
//-------------------------------------------------------------------------------
always_comb begin
    ipr_clr = '0;
    eoi_wr_m  = 1'b0;
    soi_wr_m  = 1'b0;
    if (csr2ipic_w_req) begin
        case (csr2ipic_addr)
            SCR1_IPIC_CICSR : begin
                // CSR for the currently serviced interrupt
                ipr_clr[cisv_m[SCR1_IRQ_VECT_WIDTH-2:0]] |= (csr2ipic_wdata[SCR1_IPIC_ICSR_IP] & ~cisv_m[SCR1_IRQ_VECT_WIDTH-1]);
            end

            SCR1_IPIC_IPR : begin
                // Aggregated pending interrupts
                ipr_clr = csr2ipic_wdata[SCR1_IRQ_VECT_NUM-1:0];
            end

            SCR1_IPIC_EOI : begin
                // End Of Interrupt
                eoi_wr_m |= (~cisv_m[SCR1_IRQ_VECT_WIDTH-1]);
            end

            SCR1_IPIC_SOI : begin
                // Start Of Interrupt
                if (irr_priority_m.vd) begin
                    for (int unsigned i=0; i<SCR1_IRQ_VECT_NUM; ++i) begin
                        if (irr_priority_m.idx == i) begin
                            soi_wr_m   |= 1'b1;
                            ipr_clr[i] |= 1'b1;
                        end
                    end
                end
            end


            SCR1_IPIC_ICSR : begin
                ipr_clr[idxr_m] |= csr2ipic_wdata[SCR1_IPIC_ICSR_IP];
            end

            default : begin
            end

        endcase
    end
end

//-------------------------------------------------------------------------------
// Synchronizer (optional), interrupt vector edge detect
//-------------------------------------------------------------------------------
`ifdef SCR1_IPIC_SYNC_EN
logic [SCR1_IRQ_VECT_NUM-1:0]   irq_lines_sync0;

always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
        irq_lines_sync0 <= '0;
        irq_lines_i     <= '0;
    end else begin
        irq_lines_sync0 <= irq_lines;
        irq_lines_i     <= irq_lines_sync0;
    end
end
`else // SCR1_IPIC_SYNC_EN
assign irq_lines_i  = irq_lines;
`endif // SCR1_IPIC_SYNC_EN

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        irq_edge_det    <= '0;
    end else begin
        irq_edge_det    <= irq_lines_i;
    end
end


//-------------------------------------------------------------------------------
// IMR / INVR new values
//-------------------------------------------------------------------------------
always_comb begin
    invr_new    = invr;
    imr_new     = imr;
    if (csr2ipic_w_req & (csr2ipic_addr == SCR1_IPIC_ICSR)) begin
        invr_new[idxr_m]    = csr2ipic_wdata[SCR1_IPIC_ICSR_INV];
        imr_new[idxr_m]     = csr2ipic_wdata[SCR1_IPIC_ICSR_IM];
    end
end

// Level and edge IRQ
assign irq_lvl  = irq_lines_i ^ invr_new;

//-------------------------------------------------------------------------------
// Interrupt Pending register
//-------------------------------------------------------------------------------
// IP bit should not be cleared if the condition for interrupt triggering is true,
// even if a ipr_clr request is present
always_comb begin
    ipr_new = '0;
    for (int unsigned i=0; i<SCR1_IRQ_VECT_NUM; ++i) begin
        if (ipr_clr[i] & (~irq_lvl[i] | imr_new[i])) begin
            ipr_new[i] = 1'b0;
        end else begin
            if (~imr[i]) begin          // Level IRQ
                ipr_new[i] = irq_lvl[i];
            end else begin              // Edge IRQ
                ipr_new[i] = ipr[i] | ((irq_edge_det[i] ^ irq_lines_i[i]) & irq_lvl[i]);
            end
        end
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        ipr <= '0;
    end else begin
        if (ipr != ipr_new) begin
            ipr <= ipr_new;
        end
    end
end

assign ipr_m = ipr;

//-------------------------------------------------------------------------------
// Interrupt Requested Register
//-------------------------------------------------------------------------------
assign irr_m    = ipr_m & ier;

//-------------------------------------------------------------------------------
// IRQ generation for M-mode IRQ
//-------------------------------------------------------------------------------
assign irr_priority_m      = scr1_search_one_16(irr_m);
assign isvr_priority_eoi_m = scr1_search_one_16(isvr_eoi_m);

always_comb begin
    isvr_eoi_m = isvr_m;
    for (int unsigned i=0; i<SCR1_IRQ_VECT_NUM; ++i) begin
        if (i == cisv_m) begin
            isvr_eoi_m[i] = 1'b0;
        end
    end
end

always_comb begin

    irq_m_req = 1'b0;

    if (irr_priority_m.vd) begin            // There is a new interrupt
        if (~|isvr_m) begin                 // No serviced interrupts
            irq_m_req = 1'b1;
        end else begin                      // There are serviced interrupts
            if (irr_priority_m.idx < cisv_m) begin
                irq_m_req = 1'b1;
            end
        end
    end
end

always_ff @(negedge rst_n, posedge clk) begin
    if (~rst_n) begin
        isvr_m  <= '0;
        cisv_m  <= SCR1_IRQ_VOID_VECT_NUM;
    end else begin
        if ((irq_m_req) & (soi_wr_m)) begin
            for (int unsigned i=0; i<SCR1_IRQ_VECT_NUM; ++i) begin
                if (i == irr_priority_m.idx) begin
                    isvr_m[i] <= 1'b1;
                end
            end
            cisv_m <= irr_priority_m.idx;
        end else if (eoi_wr_m) begin
            isvr_m <= isvr_eoi_m;
            if (isvr_priority_eoi_m.vd) begin
                cisv_m <= isvr_priority_eoi_m.idx;
            end else begin
                cisv_m <= SCR1_IRQ_VOID_VECT_NUM;
            end

        end
    end
end

endmodule : scr1_ipic

`endif // SCR1_IPIC_EN