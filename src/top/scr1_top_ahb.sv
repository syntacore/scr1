/// Copyright by Syntacore LLC © 2016-2020. See LICENSE for details
/// @file       <scr1_top_ahb.sv>
/// @brief      SCR1 AHB top
///

`include "scr1_arch_description.svh"
`include "scr1_memif.svh"
`include "scr1_ahb.svh"
`ifdef SCR1_IPIC_EN
`include "scr1_ipic.svh"
`endif // SCR1_IPIC_EN

`ifdef SCR1_TCM_EN
 `define SCR1_IMEM_ROUTER_EN
`endif // SCR1_TCM_EN

module scr1_top_ahb (
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
    output  logic [3:0]                             imem_hprot,
    output  logic [2:0]                             imem_hburst,
    output  logic [2:0]                             imem_hsize,
    output  logic [1:0]                             imem_htrans,
    output  logic                                   imem_hmastlock,
    output  logic [SCR1_AHB_WIDTH-1:0]              imem_haddr,
    input   logic                                   imem_hready,
    input   logic [SCR1_AHB_WIDTH-1:0]              imem_hrdata,
    input   logic                                   imem_hresp,

    // Data Memory Interface
    output  logic [3:0]                             dmem_hprot,
    output  logic [2:0]                             dmem_hburst,
    output  logic [2:0]                             dmem_hsize,
    output  logic [1:0]                             dmem_htrans,
    output  logic                                   dmem_hmastlock,
    output  logic [SCR1_AHB_WIDTH-1:0]              dmem_haddr,
    output  logic                                   dmem_hwrite,
    output  logic [SCR1_AHB_WIDTH-1:0]              dmem_hwdata,
    input   logic                                   dmem_hready,
    input   logic [SCR1_AHB_WIDTH-1:0]              dmem_hrdata,
    input   logic                                   dmem_hresp
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

// Instruction memory interface from router to AHB bridge
logic                                               ahb_imem_req_ack;
logic                                               ahb_imem_req;
type_scr1_mem_cmd_e                                 ahb_imem_cmd;
logic [`SCR1_IMEM_AWIDTH-1:0]                       ahb_imem_addr;
logic [`SCR1_IMEM_DWIDTH-1:0]                       ahb_imem_rdata;
type_scr1_mem_resp_e                                ahb_imem_resp;

// Data memory interface from router to AHB bridge
logic                                               ahb_dmem_req_ack;
logic                                               ahb_dmem_req;
type_scr1_mem_cmd_e                                 ahb_dmem_cmd;
type_scr1_mem_width_e                               ahb_dmem_width;
logic [`SCR1_DMEM_AWIDTH-1:0]                       ahb_dmem_addr;
logic [`SCR1_DMEM_DWIDTH-1:0]                       ahb_dmem_wdata;
logic [`SCR1_DMEM_DWIDTH-1:0]                       ahb_dmem_rdata;
type_scr1_mem_resp_e                                ahb_dmem_resp;

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

logic                                               timer_irq;
logic [63:0]                                        timer_val;


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
    // Interface to AHB bridge
    .port0_req_ack  (ahb_imem_req_ack ),
    .port0_req      (ahb_imem_req     ),
    .port0_cmd      (ahb_imem_cmd     ),
    .port0_addr     (ahb_imem_addr    ),
    .port0_rdata    (ahb_imem_rdata   ),
    .port0_resp     (ahb_imem_resp    ),
    // Interface to TCM
    .port1_req_ack  (tcm_imem_req_ack ),
    .port1_req      (tcm_imem_req     ),
    .port1_cmd      (tcm_imem_cmd     ),
    .port1_addr     (tcm_imem_addr    ),
    .port1_rdata    (tcm_imem_rdata   ),
    .port1_resp     (tcm_imem_resp    )
);

`else // SCR1_IMEM_ROUTER_EN

assign ahb_imem_req         = core_imem_req;
assign ahb_imem_cmd         = core_imem_cmd;
assign ahb_imem_addr        = core_imem_addr;
assign core_imem_req_ack    = ahb_imem_req_ack;
assign core_imem_resp       = ahb_imem_resp;
assign core_imem_rdata      = ahb_imem_rdata;

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
    .port1_req_ack  (1'b0),
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
    // Interface to AHB bridge
    .port0_req_ack  (ahb_dmem_req_ack    ),
    .port0_req      (ahb_dmem_req        ),
    .port0_cmd      (ahb_dmem_cmd        ),
    .port0_width    (ahb_dmem_width      ),
    .port0_addr     (ahb_dmem_addr       ),
    .port0_wdata    (ahb_dmem_wdata      ),
    .port0_rdata    (ahb_dmem_rdata      ),
    .port0_resp     (ahb_dmem_resp       )
);


//-------------------------------------------------------------------------------
// Instruction memory AHB bridge
//-------------------------------------------------------------------------------
scr1_imem_ahb i_imem_ahb (
    .rst_n          (core_rst_n_local   ),
    .clk            (clk                ),
    // Interface to imem router
    .imem_req_ack   (ahb_imem_req_ack   ),
    .imem_req       (ahb_imem_req       ),
    .imem_addr      (ahb_imem_addr      ),
    .imem_rdata     (ahb_imem_rdata     ),
    .imem_resp      (ahb_imem_resp      ),
    // AHB interface
    .hprot          (imem_hprot         ),
    .hburst         (imem_hburst        ),
    .hsize          (imem_hsize         ),
    .htrans         (imem_htrans        ),
    .hmastlock      (imem_hmastlock     ),
    .haddr          (imem_haddr         ),
    .hready         (imem_hready        ),
    .hrdata         (imem_hrdata        ),
    .hresp          (imem_hresp         )
);


//-------------------------------------------------------------------------------
// Data memory AHB bridge
//-------------------------------------------------------------------------------
scr1_dmem_ahb i_dmem_ahb (
    .rst_n          (core_rst_n_local   ),
    .clk            (clk                ),
    // Interface to dmem router
    .dmem_req_ack   (ahb_dmem_req_ack   ),
    .dmem_req       (ahb_dmem_req       ),
    .dmem_cmd       (ahb_dmem_cmd       ),
    .dmem_width     (ahb_dmem_width     ),
    .dmem_addr      (ahb_dmem_addr      ),
    .dmem_wdata     (ahb_dmem_wdata     ),
    .dmem_rdata     (ahb_dmem_rdata     ),
    .dmem_resp      (ahb_dmem_resp      ),
    // AHB interface
    .hprot          (dmem_hprot         ),
    .hburst         (dmem_hburst        ),
    .hsize          (dmem_hsize         ),
    .htrans         (dmem_htrans        ),
    .hmastlock      (dmem_hmastlock     ),
    .haddr          (dmem_haddr         ),
    .hwrite         (dmem_hwrite        ),
    .hwdata         (dmem_hwdata        ),
    .hready         (dmem_hready        ),
    .hrdata         (dmem_hrdata        ),
    .hresp          (dmem_hresp         )
);

endmodule : scr1_top_ahb


