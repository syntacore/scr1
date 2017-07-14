#ifndef __SCR1__SPECIFIC
#define __SCR1__SPECIFIC

#define mcounten        0x7E0

// Memory-mapped registers
#define mtime           0x00490000
#define mtimeh          0x00490004
#define mtimecmp        0x00490008
#define mtimecmph       0x0049000C
#define mtimeclkset     0x00490010

#define SCR1_MTIMECLKSET_DIV        15
#define SCR1_MTIMECLKSET_CLKSEL     16
#define SCR1_MTIMECLKSET_EN         17
#define SCR1_MTIMECLKSET_WR_MASK    0x3FFFF

#endif // _SCR1__SPECIFIC
