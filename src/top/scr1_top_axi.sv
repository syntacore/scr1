/// Copyright by Syntacore LLC © 2016-2020. See LICENSE for details
/// @file       <scr1_top_axi.sv>
/// @brief      SCR1 AXI top
///

`include "scr1_arch_description.svh"
`include "scr1_memif.svh"
`ifdef SCR1_IPIC_EN
`include "scr1_ipic.svh"
`endif // SCR1_IPIC_EN

`ifdef SCR1_TCM_EN
 `define SCR1_IMEM_ROUTER_EN
`endif // SCR1_TCM_EN

module scr1_top_axi (
    // Control
    input   logic                                   pwrup_rst_n,            // Power-Up Reset
    input   logic                                   rst_n,                  // Regular Reset signal
    input   logic                                   cpu_rst_n,              // CPU Reset (Core Reset)
    input   logic                                   test_mode,              // Test mode
    input   logic                                   test_rst_n,             // Test mode's reset
    input   logic                                   clk,                    // System clock
    input   logic                                   rtc_clk,                // Real-time clock
`ifdef SCR1_DBG_EN
    output  logic                                   sys_rst_n_o,            // External System Reset output
                                                                            //   (for the processor cluster's components or
                                                                            //    external SOC (could be useful in small
                                                                            //    SCR-core-centric SOCs))
    output  logic                                   sys_rdc_qlfy_o,         // System-to-External SOC Reset Domain Crossing Qualifier
`endif // SCR1_DBG_EN

    // Fuses
    input   logic [`SCR1_XLEN-1:0]                  fuse_mhartid,           // Hart ID
`ifdef SCR1_DBG_EN
    input   logic [31:0]                            fuse_idcode,            // TAPC IDCODE
`endif // SCR1_DBG_EN

    // IRQ
`ifdef SCR1_IPIC_EN
    input   logic [SCR1_IRQ_LINES_NUM-1:0]          irq_lines,              // IRQ lines to IPIC
`else // SCR1_IPIC_EN
    input   logic                                   ext_irq,                // External IRQ input
`endif // SCR1_IPIC_EN
    input   logic                                   soft_irq,               // Software IRQ input

`ifdef SCR1_DBG_EN
    // -- JTAG I/F
    input   logic                                   trst_n,
    input   logic                                   tck,
    input   logic                                   tms,
    input   logic                                   tdi,
    output  logic                                   tdo,
    output  logic                                   tdo_en,
`endif // SCR1_DBG_EN

    // Instruction Memory Interface
    output  logic [3:0]                             io_axi_imem_awid,
    output  logic [31:0]                            io_axi_imem_awaddr,
    output  logic [7:0]                             io_axi_imem_awlen,
    output  logic [2:0]                             io_axi_imem_awsize,
    output  logic [1:0]                             io_axi_imem_awburst,
    output  logic                                   io_axi_imem_awlock,
    output  logic [3:0]                             io_axi_imem_awcache,
    output  logic [2:0]                             io_axi_imem_awprot,
    output  logic [3:0]                             io_axi_imem_awregion,
    output  logic [3:0]                             io_axi_imem_awuser,
    output  logic [3:0]                             io_axi_imem_awqos,
    output  logic                                   io_axi_imem_awvalid,
    input   logic                                   io_axi_imem_awready,
    output  logic [31:0]                            io_axi_imem_wdata,
    output  logic [3:0]                             io_axi_imem_wstrb,
    output  logic                                   io_axi_imem_wlast,
    output  logic [3:0]                             io_axi_imem_wuser,
    output  logic                                   io_axi_imem_wvalid,
    input   logic                                   io_axi_imem_wready,
    input   logic [3:0]                             io_axi_imem_bid,
    input   logic [1:0]                             io_axi_imem_bresp,
    input   logic                                   io_axi_imem_bvalid,
    input   logic [3:0]                             io_axi_imem_buser,
    output  logic                                   io_axi_imem_bready,
    output  logic [3:0]                             io_axi_imem_arid,
    output  logic [31:0]                            io_axi_imem_araddr,
    output  logic [7:0]                             io_axi_imem_arlen,
    output  logic [2:0]                             io_axi_imem_arsize,
    output  logic [1:0]                             io_axi_imem_arburst,
    output  logic                                   io_axi_imem_arlock,
    output  logic [3:0]                             io_axi_imem_arcache,
    output  logic [2:0]                             io_axi_imem_arprot,
    output  logic [3:0]                             io_axi_imem_arregion,
    output  logic [3:0]                             io_axi_imem_aruser,
    output  logic [3:0]                             io_axi_imem_arqos,
    output  logic                                   io_axi_imem_arvalid,
    input   logic                                   io_axi_imem_arready,
    input   logic [3:0]                             io_axi_imem_rid,
    input   logic [31:0]                            io_axi_imem_rdata,
    input   logic [1:0]                             io_axi_imem_rresp,
    input   logic                                   io_axi_imem_rlast,
    input   logic [3:0]                             io_axi_imem_ruser,
    input   logic                                   io_axi_imem_rvalid,
    output  logic                                   io_axi_imem_rready,

    // Data Memory Interface
    output  logic [3:0]                             io_axi_dmem_awid,
    output  logic [31:0]                            io_axi_dmem_awaddr,
    output  logic [7:0]                             io_axi_dmem_awlen,
    output  logic [2:0]                             io_axi_dmem_awsize,
    output  logic [1:0]                             io_axi_dmem_awburst,
    output  logic                                   io_axi_dmem_awlock,
    output  logic [3:0]                             io_axi_dmem_awcache,
    output  logic [2:0]                             io_axi_dmem_awprot,
    output  logic [3:0]                             io_axi_dmem_awregion,
    output  logic [3:0]                             io_axi_dmem_awuser,
    output  logic [3:0]                             io_axi_dmem_awqos,
    output  logic                                   io_axi_dmem_awvalid,
    input   logic                                   io_axi_dmem_awready,
    output  logic [31:0]                            io_axi_dmem_wdata,
    output  logic [3:0]                             io_axi_dmem_wstrb,
    output  logic                                   io_axi_dmem_wlast,
    output  logic [3:0]                             io_axi_dmem_wuser,
    output  logic                                   io_axi_dmem_wvalid,
    input   logic                                   io_axi_dmem_wready,
    input   logic [3:0]                             io_axi_dmem_bid,
    input   logic [1:0]                             io_axi_dmem_bresp,
    input   logic                                   io_axi_dmem_bvalid,
    input   logic [3:0]                             io_axi_dmem_buser,
    output  logic                                   io_axi_dmem_bready,
    output  logic [3:0]                             io_axi_dmem_arid,
    output  logic [31:0]                            io_axi_dmem_araddr,
    output  logic [7:0]                             io_axi_dmem_arlen,
    output  logic [2:0]                             io_axi_dmem_arsize,
    output  logic [1:0]                             io_axi_dmem_arburst,
    output  logic                                   io_axi_dmem_arlock,
    output  logic [3:0]                             io_axi_dmem_arcache,
    output  logic [2:0]                             io_axi_dmem_arprot,
    output  logic [3:0]                             io_axi_dmem_arregion,
    output  logic [3:0]                             io_axi_dmem_aruser,
    output  logic [3:0]                             io_axi_dmem_arqos,
    output  logic                                   io_axi_dmem_arvalid,
    input   logic                                   io_axi_dmem_arready,
    input   logic [3:0]                             io_axi_dmem_rid,
    input   logic [31:0]                            io_axi_dmem_rdata,
    input   logic [1:0]                             io_axi_dmem_rresp,
    input   logic                                   io_axi_dmem_rlast,
    input   logic [3:0]                             io_axi_dmem_ruser,
    input   logic                                   io_axi_dmem_rvalid,
    output  logic                                   io_axi_dmem_rready
);

//-------------------------------------------------------------------------------
// Local signal declaration
//-------------------------------------------------------------------------------
// Reset logic
logic                                               pwrup_rst_n_sync;
logic                                               rst_n_sync;
logic                                               cpu_rst_n_sync;
logic                                               reset_n_sync;
logic                                               reset_n;
logic                                               core_rst_n_local;

// Instruction memory interface from core to router
logic                                               core_imem_req_ack;
logic                                               core_imem_req;
type_scr1_mem_cmd_e                                 core_imem_cmd;
logic [`SCR1_IMEM_AWIDTH-1:0]                       core_imem_addr;
logic [`SCR1_IMEM_DWIDTH-1:0]                       core_imem_rdata;
type_scr1_mem_resp_e                                core_imem_resp;

// Data memory interface from core to router
logic                                               core_dmem_req_ack;
logic                                               core_dmem_req;
type_scr1_mem_cmd_e                                 core_dmem_cmd;
type_scr1_mem_width_e                               core_dmem_width;
logic [`SCR1_DMEM_AWIDTH-1:0]                       core_dmem_addr;
logic [`SCR1_DMEM_DWIDTH-1:0]                       core_dmem_wdata;
logic [`SCR1_DMEM_DWIDTH-1:0]                       core_dmem_rdata;
type_scr1_mem_resp_e                                core_dmem_resp;

// Instruction memory interface from router to AXI bridge
logic                                               axi_imem_req_ack;
logic                                               axi_imem_req;
type_scr1_mem_cmd_e                                 axi_imem_cmd;
logic [`SCR1_IMEM_AWIDTH-1:0]                       axi_imem_addr;
logic [`SCR1_IMEM_DWIDTH-1:0]                       axi_imem_rdata;
type_scr1_mem_resp_e                                axi_imem_resp;

// Data memory interface from router to AXI bridge
logic                                               axi_dmem_req_ack;
logic                                               axi_dmem_req;
type_scr1_mem_cmd_e                                 axi_dmem_cmd;
type_scr1_mem_width_e                               axi_dmem_width;
logic [`SCR1_DMEM_AWIDTH-1:0]                       axi_dmem_addr;
logic [`SCR1_DMEM_DWIDTH-1:0]                       axi_dmem_wdata;
logic [`SCR1_DMEM_DWIDTH-1:0]                       axi_dmem_rdata;
type_scr1_mem_resp_e                                axi_dmem_resp;

`ifdef SCR1_TCM_EN
// Instruction memory interface from router to TCM
logic                                               tcm_imem_req_ack;
logic                                               tcm_imem_req;
type_scr1_mem_cmd_e                                 tcm_imem_cmd;
logic [`SCR1_IMEM_AWIDTH-1:0]                       tcm_imem_addr;
logic [`SCR1_IMEM_DWIDTH-1:0]                       tcm_imem_rdata;
type_scr1_mem_resp_e                                tcm_imem_resp;

// Data memory interface from router to TCM
logic                                               tcm_dmem_req_ack;
logic                                               tcm_dmem_req;
type_scr1_mem_cmd_e                                 tcm_dmem_cmd;
type_scr1_mem_width_e                               tcm_dmem_width;
logic [`SCR1_DMEM_AWIDTH-1:0]                       tcm_dmem_addr;
logic [`SCR1_DMEM_DWIDTH-1:0]                       tcm_dmem_wdata;
logic [`SCR1_DMEM_DWIDTH-1:0]                       tcm_dmem_rdata;
type_scr1_mem_resp_e                                tcm_dmem_resp;
`endif // SCR1_TCM_EN

// Data memory interface from router to memory-mapped timer
logic                                               timer_dmem_req_ack;
logic                                               timer_dmem_req;
type_scr1_mem_cmd_e                                 timer_dmem_cmd;
type_scr1_mem_width_e                               timer_dmem_width;
logic [`SCR1_DMEM_AWIDTH-1:0]                       timer_dmem_addr;
logic [`SCR1_DMEM_DWIDTH-1:0]                       timer_dmem_wdata;
logic [`SCR1_DMEM_DWIDTH-1:0]                       timer_dmem_rdata;
type_scr1_mem_resp_e                                timer_dmem_resp;

// Misc
logic                                               timer_irq;
logic [63:0]                                        timer_val;
logic                                               axi_reinit;
logic                                               axi_imem_idle;
logic                                               axi_dmem_idle;

//-------------------------------------------------------------------------------
// Reset logic
//-------------------------------------------------------------------------------
// Power-Up Reset synchronizer
scr1_reset_sync_cell i_pwrup_rstn_reset_sync (
    .rst_n          (pwrup_rst_n     ),
    .clk            (clk             ),
    .test_rst_n     (test_rst_n      ),
    .test_mode      (test_mode       ),
    .rst_n_out      (pwrup_rst_n_sync)
);

// Regular Reset synchronizer
scr1_reset_sync_cell i_rstn_reset_sync (
    .rst_n          (rst_n     ),
    .clk            (clk       ),
    .test_rst_n     (test_rst_n),
    .test_mode      (test_mode ),
    .rst_n_out      (rst_n_sync)
);

// CPU Reset synchronizer
scr1_reset_sync_cell i_cpu_rstn_reset_sync (
    .rst_n          (cpu_rst_n     ),
    .clk            (clk           ),
    .test_rst_n     (test_rst_n    ),
    .test_mode      (test_mode     ),
    .rst_n_out      (cpu_rst_n_sync)
);

// Combo Reset (Power-Up and Regular Resets): reset_n
scr1_reset_buf_cell i_reset_buf_cell (
    .rst_n              (reset_n_sync),
    .clk                (clk         ),
    .test_mode          (test_mode   ),
    .test_rst_n         (test_rst_n  ),
    .reset_n_in         (1'b1        ),
    .reset_n_out        (reset_n     ),
    .reset_n_status     (            )
);
assign reset_n_sync = rst_n_sync & pwrup_rst_n_sync;

//-------------------------------------------------------------------------------
// SCR1 core instance
//-------------------------------------------------------------------------------
scr1_core_top i_core_top (
    // Common
    .pwrup_rst_n                (pwrup_rst_n_sync ),
    .rst_n                      (rst_n_sync       ),
    .cpu_rst_n                  (cpu_rst_n_sync   ),
    .test_mode                  (test_mode        ),
    .test_rst_n                 (test_rst_n       ),
    .clk                        (clk              ),
    .core_rst_n_o               (core_rst_n_local ),
    .core_rdc_qlfy_o            (                 ),
`ifdef SCR1_DBG_EN
    .sys_rst_n_o                (sys_rst_n_o      ),
    .sys_rdc_qlfy_o             (sys_rdc_qlfy_o   ),
`endif // SCR1_DBG_EN

    // Fuses
    .core_fuse_mhartid_i        (fuse_mhartid     ),
`ifdef SCR1_DBG_EN
    .tapc_fuse_idcode_i         (fuse_idcode      ),
`endif // SCR1_DBG_EN

    // IRQ
`ifdef SCR1_IPIC_EN
    .core_irq_lines_i           (irq_lines        ),
`else // SCR1_IPIC_EN
    .core_irq_ext_i             (ext_irq          ),
`endif // SCR1_IPIC_EN
    .core_irq_soft_i            (soft_irq         ),
    .core_irq_mtimer_i          (timer_irq        ),

    // Memory-mapped external timer
    .core_mtimer_val_i          (timer_val        ),

`ifdef SCR1_DBG_EN
    // Debug interface
    .tapc_trst_n                (trst_n           ),
    .tapc_tck                   (tck              ),
    .tapc_tms                   (tms              ),
    .tapc_tdi                   (tdi              ),
    .tapc_tdo                   (tdo              ),
    .tapc_tdo_en                (tdo_en           ),
`endif // SCR1_DBG_EN

    // Instruction memory interface
    .imem2core_req_ack_i        (core_imem_req_ack),
    .core2imem_req_o            (core_imem_req    ),
    .core2imem_cmd_o            (core_imem_cmd    ),
    .core2imem_addr_o           (core_imem_addr   ),
    .imem2core_rdata_i          (core_imem_rdata  ),
    .imem2core_resp_i           (core_imem_resp   ),

    // Data memory interface
    .dmem2core_req_ack_i        (core_dmem_req_ack),
    .core2dmem_req_o            (core_dmem_req    ),
    .core2dmem_cmd_o            (core_dmem_cmd    ),
    .core2dmem_width_o          (core_dmem_width  ),
    .core2dmem_addr_o           (core_dmem_addr   ),
    .core2dmem_wdata_o          (core_dmem_wdata  ),
    .dmem2core_rdata_i          (core_dmem_rdata  ),
    .dmem2core_resp_i           (core_dmem_resp   )
);


`ifdef SCR1_TCM_EN
//-------------------------------------------------------------------------------
// TCM instance
//-------------------------------------------------------------------------------
scr1_tcm #(
    .SCR1_TCM_SIZE  (`SCR1_DMEM_AWIDTH'(~SCR1_TCM_ADDR_MASK + 1'b1))
) i_tcm (
    .clk            (clk             ),
    .rst_n          (core_rst_n_local),

    // Instruction interface to TCM
    .imem_req_ack   (tcm_imem_req_ack),
    .imem_req       (tcm_imem_req    ),
    .imem_addr      (tcm_imem_addr   ),
    .imem_rdata     (tcm_imem_rdata  ),
    .imem_resp      (tcm_imem_resp   ),

    // Data interface to TCM
    .dmem_req_ack   (tcm_dmem_req_ack),
    .dmem_req       (tcm_dmem_req    ),
    .dmem_cmd       (tcm_dmem_cmd    ),
    .dmem_width     (tcm_dmem_width  ),
    .dmem_addr      (tcm_dmem_addr   ),
    .dmem_wdata     (tcm_dmem_wdata  ),
    .dmem_rdata     (tcm_dmem_rdata  ),
    .dmem_resp      (tcm_dmem_resp   )
);
`endif // SCR1_TCM_EN


//-------------------------------------------------------------------------------
// Memory-mapped timer instance
//-------------------------------------------------------------------------------
scr1_timer i_timer (
    // Common
    .rst_n          (core_rst_n_local  ),
    .clk            (clk               ),
    .rtc_clk        (rtc_clk           ),

    // Memory interface
    .dmem_req       (timer_dmem_req    ),
    .dmem_cmd       (timer_dmem_cmd    ),
    .dmem_width     (timer_dmem_width  ),
    .dmem_addr      (timer_dmem_addr   ),
    .dmem_wdata     (timer_dmem_wdata  ),
    .dmem_req_ack   (timer_dmem_req_ack),
    .dmem_rdata     (timer_dmem_rdata  ),
    .dmem_resp      (timer_dmem_resp   ),

    // Timer interface
    .timer_val      (timer_val         ),
    .timer_irq      (timer_irq         )
);


`ifdef SCR1_IMEM_ROUTER_EN
//-------------------------------------------------------------------------------
// Instruction memory router
//-------------------------------------------------------------------------------
scr1_imem_router #(
    .SCR1_ADDR_MASK     (SCR1_TCM_ADDR_MASK),
    .SCR1_ADDR_PATTERN  (SCR1_TCM_ADDR_PATTERN)
) i_imem_router (
    .rst_n          (core_rst_n_local ),
    .clk            (clk              ),

    // Interface to core
    .imem_req_ack   (core_imem_req_ack),
    .imem_req       (core_imem_req    ),
    .imem_cmd       (core_imem_cmd    ),
    .imem_addr      (core_imem_addr   ),
    .imem_rdata     (core_imem_rdata  ),
    .imem_resp      (core_imem_resp   ),

    // Interface to AXI bridge
    .port0_req_ack  (axi_imem_req_ack ),
    .port0_req      (axi_imem_req     ),
    .port0_cmd      (axi_imem_cmd     ),
    .port0_addr     (axi_imem_addr    ),
    .port0_rdata    (axi_imem_rdata   ),
    .port0_resp     (axi_imem_resp    ),

    // Interface to TCM
    .port1_req_ack  (tcm_imem_req_ack ),
    .port1_req      (tcm_imem_req     ),
    .port1_cmd      (tcm_imem_cmd     ),
    .port1_addr     (tcm_imem_addr    ),
    .port1_rdata    (tcm_imem_rdata   ),
    .port1_resp     (tcm_imem_resp    )
);

`else // SCR1_IMEM_ROUTER_EN

assign axi_imem_req         = core_imem_req;
assign axi_imem_cmd         = core_imem_cmd;
assign axi_imem_addr        = core_imem_addr;
assign core_imem_req_ack    = axi_imem_req_ack;
assign core_imem_resp       = axi_imem_resp;
assign core_imem_rdata      = axi_imem_rdata;

`endif // SCR1_IMEM_ROUTER_EN


//-------------------------------------------------------------------------------
// Data memory router
//-------------------------------------------------------------------------------
scr1_dmem_router #(

`ifdef SCR1_TCM_EN
    .SCR1_PORT1_ADDR_MASK       (SCR1_TCM_ADDR_MASK),
    .SCR1_PORT1_ADDR_PATTERN    (SCR1_TCM_ADDR_PATTERN),
`else // SCR1_TCM_EN
    .SCR1_PORT1_ADDR_MASK       (32'h00000000),
    .SCR1_PORT1_ADDR_PATTERN    (32'hFFFFFFFF),
`endif // SCR1_TCM_EN

    .SCR1_PORT2_ADDR_MASK       (SCR1_TIMER_ADDR_MASK),
    .SCR1_PORT2_ADDR_PATTERN    (SCR1_TIMER_ADDR_PATTERN)

) i_dmem_router (
    .rst_n          (core_rst_n_local    ),
    .clk            (clk                 ),

    // Interface to core
    .dmem_req_ack   (core_dmem_req_ack   ),
    .dmem_req       (core_dmem_req       ),
    .dmem_cmd       (core_dmem_cmd       ),
    .dmem_width     (core_dmem_width     ),
    .dmem_addr      (core_dmem_addr      ),
    .dmem_wdata     (core_dmem_wdata     ),
    .dmem_rdata     (core_dmem_rdata     ),
    .dmem_resp      (core_dmem_resp      ),

`ifdef SCR1_TCM_EN
    // Interface to TCM
    .port1_req_ack  (tcm_dmem_req_ack    ),
    .port1_req      (tcm_dmem_req        ),
    .port1_cmd      (tcm_dmem_cmd        ),
    .port1_width    (tcm_dmem_width      ),
    .port1_addr     (tcm_dmem_addr       ),
    .port1_wdata    (tcm_dmem_wdata      ),
    .port1_rdata    (tcm_dmem_rdata      ),
    .port1_resp     (tcm_dmem_resp       ),
`else // SCR1_TCM_EN
    .port1_req_ack  (1'b0                ),
    .port1_req      (                    ),
    .port1_cmd      (                    ),
    .port1_width    (                    ),
    .port1_addr     (                    ),
    .port1_wdata    (                    ),
    .port1_rdata    ('0                  ),
    .port1_resp     (SCR1_MEM_RESP_RDY_ER),
`endif // SCR1_TCM_EN

    // Interface to memory-mapped timer
    .port2_req_ack  (timer_dmem_req_ack  ),
    .port2_req      (timer_dmem_req      ),
    .port2_cmd      (timer_dmem_cmd      ),
    .port2_width    (timer_dmem_width    ),
    .port2_addr     (timer_dmem_addr     ),
    .port2_wdata    (timer_dmem_wdata    ),
    .port2_rdata    (timer_dmem_rdata    ),
    .port2_resp     (timer_dmem_resp     ),

    // Interface to AXI bridge
    .port0_req_ack  (axi_dmem_req_ack    ),
    .port0_req      (axi_dmem_req        ),
    .port0_cmd      (axi_dmem_cmd        ),
    .port0_width    (axi_dmem_width      ),
    .port0_addr     (axi_dmem_addr       ),
    .port0_wdata    (axi_dmem_wdata      ),
    .port0_rdata    (axi_dmem_rdata      ),
    .port0_resp     (axi_dmem_resp       )
);


//-------------------------------------------------------------------------------
// Instruction memory AXI bridge
//-------------------------------------------------------------------------------
scr1_mem_axi #(
`ifdef SCR1_IMEM_AXI_REQ_BP
    .SCR1_AXI_REQ_BP    (1),
`else // SCR1_IMEM_AXI_REQ_BP
    .SCR1_AXI_REQ_BP    (0),
`endif // SCR1_IMEM_AXI_REQ_BP
`ifdef SCR1_IMEM_AXI_RESP_BP
    .SCR1_AXI_RESP_BP   (1)
`else // SCR1_IMEM_AXI_RESP_BP
    .SCR1_AXI_RESP_BP   (0)
`endif // SCR1_IMEM_AXI_RESP_BP
) i_imem_axi (
    .clk            (clk                    ),
    .rst_n          (reset_n                ),
    .axi_reinit     (axi_reinit             ),

    // Interface to core
    .core_idle      (axi_imem_idle          ),
    .core_req_ack   (axi_imem_req_ack       ),
    .core_req       (axi_imem_req           ),
    .core_cmd       (axi_imem_cmd           ),
    .core_width     (SCR1_MEM_WIDTH_WORD    ),
    .core_addr      (axi_imem_addr          ),
    .core_wdata     ('0                     ),
    .core_rdata     (axi_imem_rdata         ),
    .core_resp      (axi_imem_resp          ),

    // AXI I/O
    .awid           (io_axi_imem_awid       ),
    .awaddr         (io_axi_imem_awaddr     ),
    .awlen          (io_axi_imem_awlen      ),
    .awsize         (io_axi_imem_awsize     ),
    .awburst        (io_axi_imem_awburst    ),
    .awlock         (io_axi_imem_awlock     ),
    .awcache        (io_axi_imem_awcache    ),
    .awprot         (io_axi_imem_awprot     ),
    .awregion       (io_axi_imem_awregion   ),
    .awuser         (io_axi_imem_awuser     ),
    .awqos          (io_axi_imem_awqos      ),
    .awvalid        (io_axi_imem_awvalid    ),
    .awready        (io_axi_imem_awready    ),
    .wdata          (io_axi_imem_wdata      ),
    .wstrb          (io_axi_imem_wstrb      ),
    .wlast          (io_axi_imem_wlast      ),
    .wuser          (io_axi_imem_wuser      ),
    .wvalid         (io_axi_imem_wvalid     ),
    .wready         (io_axi_imem_wready     ),
    .bid            (io_axi_imem_bid        ),
    .bresp          (io_axi_imem_bresp      ),
    .bvalid         (io_axi_imem_bvalid     ),
    .buser          (io_axi_imem_buser      ),
    .bready         (io_axi_imem_bready     ),
    .arid           (io_axi_imem_arid       ),
    .araddr         (io_axi_imem_araddr     ),
    .arlen          (io_axi_imem_arlen      ),
    .arsize         (io_axi_imem_arsize     ),
    .arburst        (io_axi_imem_arburst    ),
    .arlock         (io_axi_imem_arlock     ),
    .arcache        (io_axi_imem_arcache    ),
    .arprot         (io_axi_imem_arprot     ),
    .arregion       (io_axi_imem_arregion   ),
    .aruser         (io_axi_imem_aruser     ),
    .arqos          (io_axi_imem_arqos      ),
    .arvalid        (io_axi_imem_arvalid    ),
    .arready        (io_axi_imem_arready    ),
    .rid            (io_axi_imem_rid        ),
    .rdata          (io_axi_imem_rdata      ),
    .rresp          (io_axi_imem_rresp      ),
    .rlast          (io_axi_imem_rlast      ),
    .ruser          (io_axi_imem_ruser      ),
    .rvalid         (io_axi_imem_rvalid     ),
    .rready         (io_axi_imem_rready     )
);


//-------------------------------------------------------------------------------
// Data memory AXI bridge
//-------------------------------------------------------------------------------
scr1_mem_axi #(
`ifdef SCR1_DMEM_AXI_REQ_BP
    .SCR1_AXI_REQ_BP    (1),
`else // SCR1_DMEM_AXI_REQ_BP
    .SCR1_AXI_REQ_BP    (0),
`endif // SCR1_DMEM_AXI_REQ_BP
`ifdef SCR1_DMEM_AXI_RESP_BP
    .SCR1_AXI_RESP_BP   (1)
`else // SCR1_DMEM_AXI_RESP_BP
    .SCR1_AXI_RESP_BP   (0)
`endif // SCR1_DMEM_AXI_RESP_BP
) i_dmem_axi (
    .clk            (clk                    ),
    .rst_n          (reset_n                ),
    .axi_reinit     (axi_reinit             ),

    // Interface to core
    .core_idle      (axi_dmem_idle          ),
    .core_req_ack   (axi_dmem_req_ack       ),
    .core_req       (axi_dmem_req           ),
    .core_cmd       (axi_dmem_cmd           ),
    .core_width     (axi_dmem_width         ),
    .core_addr      (axi_dmem_addr          ),
    .core_wdata     (axi_dmem_wdata         ),
    .core_rdata     (axi_dmem_rdata         ),
    .core_resp      (axi_dmem_resp          ),

    // AXI I/O
    .awid           (io_axi_dmem_awid       ),
    .awaddr         (io_axi_dmem_awaddr     ),
    .awlen          (io_axi_dmem_awlen      ),
    .awsize         (io_axi_dmem_awsize     ),
    .awburst        (io_axi_dmem_awburst    ),
    .awlock         (io_axi_dmem_awlock     ),
    .awcache        (io_axi_dmem_awcache    ),
    .awprot         (io_axi_dmem_awprot     ),
    .awregion       (io_axi_dmem_awregion   ),
    .awuser         (io_axi_dmem_awuser     ),
    .awqos          (io_axi_dmem_awqos      ),
    .awvalid        (io_axi_dmem_awvalid    ),
    .awready        (io_axi_dmem_awready    ),
    .wdata          (io_axi_dmem_wdata      ),
    .wstrb          (io_axi_dmem_wstrb      ),
    .wlast          (io_axi_dmem_wlast      ),
    .wuser          (io_axi_dmem_wuser      ),
    .wvalid         (io_axi_dmem_wvalid     ),
    .wready         (io_axi_dmem_wready     ),
    .bid            (io_axi_dmem_bid        ),
    .bresp          (io_axi_dmem_bresp      ),
    .bvalid         (io_axi_dmem_bvalid     ),
    .buser          (io_axi_dmem_buser      ),
    .bready         (io_axi_dmem_bready     ),
    .arid           (io_axi_dmem_arid       ),
    .araddr         (io_axi_dmem_araddr     ),
    .arlen          (io_axi_dmem_arlen      ),
    .arsize         (io_axi_dmem_arsize     ),
    .arburst        (io_axi_dmem_arburst    ),
    .arlock         (io_axi_dmem_arlock     ),
    .arcache        (io_axi_dmem_arcache    ),
    .arprot         (io_axi_dmem_arprot     ),
    .arregion       (io_axi_dmem_arregion   ),
    .aruser         (io_axi_dmem_aruser     ),
    .arqos          (io_axi_dmem_arqos      ),
    .arvalid        (io_axi_dmem_arvalid    ),
    .arready        (io_axi_dmem_arready    ),
    .rid            (io_axi_dmem_rid        ),
    .rdata          (io_axi_dmem_rdata      ),
    .rresp          (io_axi_dmem_rresp      ),
    .rlast          (io_axi_dmem_rlast      ),
    .ruser          (io_axi_dmem_ruser      ),
    .rvalid         (io_axi_dmem_rvalid     ),
    .rready         (io_axi_dmem_rready     )
);

//-------------------------------------------------------------------------------
// AXI reinit logic
//-------------------------------------------------------------------------------
always_ff @(negedge core_rst_n_local, posedge clk) begin
    if (~core_rst_n_local)                      axi_reinit <= 1'b1;
    else if (axi_imem_idle & axi_dmem_idle)     axi_reinit <= 1'b0;
end

endmodule : scr1_top_axi
