/// Copyright by Syntacore LLC © 2016-2018. See LICENSE for details
/// @file       <scr1_brkm_matcher.sv>
/// @brief      Matcher of the BRKM
///

`include "scr1_arch_description.svh"

`ifdef SCR1_BRKM_EN
`include "scr1_arch_types.svh"
`include "scr1_brkm.svh"

module scr1_brkm_matcher #(
    parameter type_scr1_op_width_e  BRKM_MATCH_OPWIDTH_MAX      = SCR1_OP_WIDTH_BYTE,   // Maximal operation width
    parameter bit                   BRKM_MATCH_ADDR_EXACT       = 0,                    // Address Exact Matching feature support
    parameter bit                   BRKM_MATCH_ADDR_MASK        = 0,                    // Address Mask Matching feature support
    parameter bit                   BRKM_MATCH_ADDR_MASK_EXT    = 0,                    // Address Mask Matching Extension feature support
    parameter int                   BRKM_MATCH_ADDR_WIDTH       = 0                     // Width of address bus for matching
) (
    // Common signals
    input   logic                                               valid,                  // Input signals are valid
    input   type_scr1_op_width_e                                width,                  // Width of operation being monitored
    // Address Channel
    input   logic                                               addr_exact_en,          // Address Exact Matching Enable
    input   logic                                               addr_mask_en,           // Address Mask Matching Enable
    input   logic                                               addr_mask_ext_en,       // Address Mask Matching Extention Enable
    input   logic [BRKM_MATCH_ADDR_WIDTH-1:0]                   addr,                   // Address bus under monitoring
    input   logic [BRKM_MATCH_ADDR_WIDTH-1:0]                   addr_lo,                // Content of a bploaddr register
    input   logic [BRKM_MATCH_ADDR_WIDTH-1:0]                   addr_hi,                // Content of a bphiaddr register
    // Result
    output  logic                                               match                   // Matching result: 0/1
);

//-------------------------------------------------------------------------------
// Local parameters declaration
//-------------------------------------------------------------------------------
localparam int unsigned L_BRKM_OP_WIDTH_ID_POW  = ((BRKM_MATCH_OPWIDTH_MAX == SCR1_OP_WIDTH_WORD)
                                                ? 2
                                                : ((BRKM_MATCH_OPWIDTH_MAX == SCR1_OP_WIDTH_HALF)
                                                    ? 1
                                                    : ((BRKM_MATCH_OPWIDTH_MAX == SCR1_OP_WIDTH_BYTE)
                                                        ? 0
                                                        : 0 )));

//-------------------------------------------------------------------------------
// Local signals declaration
//-------------------------------------------------------------------------------
logic                                   match_addr_exact;
logic                                   match_addr_range;
logic                                   match_addr_mask;
logic                                   match_addr_channel;

//-------------------------------------------------------------------------------
// Address Exact Matcher
//-------------------------------------------------------------------------------
generate
if (BRKM_MATCH_ADDR_EXACT)
begin : gen_match_addr_exact
    always_comb begin
        match_addr_exact        = 1'b0;

        if ((addr_exact_en) & (addr == addr_lo)) begin
            match_addr_exact    = 1'b1;
        end
    end
end : gen_match_addr_exact
else begin : gen_match_addr_exact
    assign match_addr_exact     = 1'b0;
end : gen_match_addr_exact
endgenerate


//-------------------------------------------------------------------------------
// Address Mask Matcher
//-------------------------------------------------------------------------------
generate
if (BRKM_MATCH_ADDR_MASK)
begin : gen_match_addr_mask
    if (BRKM_MATCH_ADDR_MASK_EXT)
    begin : gen_match_addr_mask_ext
        logic [L_BRKM_OP_WIDTH_ID_POW-1:0]      addr_lsb_mask;

        if (BRKM_MATCH_OPWIDTH_MAX == SCR1_OP_WIDTH_WORD)
        begin : gen_match_width_max
            always_comb begin
                addr_lsb_mask = '0;
                case (width)
                    SCR1_OP_WIDTH_BYTE : begin
                        addr_lsb_mask = L_BRKM_OP_WIDTH_ID_POW'(0);
                    end
                    SCR1_OP_WIDTH_HALF : begin
                        addr_lsb_mask = L_BRKM_OP_WIDTH_ID_POW'(1);
                    end
                    SCR1_OP_WIDTH_WORD : begin
                        addr_lsb_mask = $unsigned(L_BRKM_OP_WIDTH_ID_POW'(3));
                    end
                    default : begin
                        addr_lsb_mask = '0;
                    end
                endcase
            end
        end : gen_match_width_max
        else
        begin : gen_match_width_max
            always_comb begin
                addr_lsb_mask = '0;
            end
        end : gen_match_width_max

        always_comb begin
            logic [BRKM_MATCH_ADDR_WIDTH-1:0]   temp;

            match_addr_mask = 1'b0;
            temp            = '0;
            for (int unsigned i = 0; i < BRKM_MATCH_ADDR_WIDTH; ++i) begin
                if (i < L_BRKM_OP_WIDTH_ID_POW) begin
                    temp[i] = (addr_mask_ext_en & addr_lsb_mask[i])
                            ? 1'b0
                            : (addr[i] & addr_hi[i]) ^ addr_lo[i];
                end
                else begin
                    temp[i] = (addr[i] & addr_hi[i]) ^ addr_lo[i];
                end
            end
            match_addr_mask = addr_mask_en & ~(|temp);
        end
    end : gen_match_addr_mask_ext
    else
    begin : gen_match_addr_mask_ext
        always_comb begin
            match_addr_mask        = 1'b0;

            if ((addr_mask_en) & ((addr & addr_hi) == addr_lo)) begin
                match_addr_mask    = 1'b1;
            end
        end
    end : gen_match_addr_mask_ext
end : gen_match_addr_mask
else
begin : gen_match_addr_mask
    assign match_addr_mask     = 1'b0;
end : gen_match_addr_mask
endgenerate

//-------------------------------------------------------------------------------
// Address Channel Matcher output
//-------------------------------------------------------------------------------
assign match_addr_channel   = ((~addr_exact_en) & (~addr_mask_en))
                            | match_addr_exact
                            | match_addr_mask;

//-------------------------------------------------------------------------------
// Matcher output
//-------------------------------------------------------------------------------
assign match = valid & match_addr_channel;

endmodule : scr1_brkm_matcher

`endif // SCR1_BRKM_EN