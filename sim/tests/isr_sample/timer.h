#ifndef __TIMER__H
#define __TIMER__H

#define MEM_MTIME_MASK  0xF0000000
#define MEM_MTIME_CTRL  0x00490000
#define MEM_MTIME_DIV   0x00490004
#define MEM_MTIME       0x00490008
#define MEM_MTIMEH      0x0049000C
#define MEM_MTIMECMP    0x00490010
#define MEM_MTIMECMPH   0x00490014

#define TMP   t0
#define TMP2  t1
#define TMP3  t2

#if defined(__ASSEMBLER__)

// Reset
.macro _reset_mtime
    li          TMP, MEM_MTIME
    sw          zero, 0(TMP)
    sw          zero, 4(TMP)
.endm

.macro _reset_mtimecmp
    li          TMP, MEM_MTIMECMP
    not         TMP2, zero
    sw          TMP2, 0(TMP)
    sw          TMP2, 4(TMP)
.endm

// Write
.macro _write_mtime_ctrl reg
    li          TMP, MEM_MTIME_CTRL
    sw          \reg, 0(TMP)
.endm

.macro _write_mtime_div reg
    li          TMP, MEM_MTIME_DIV
    sw          \reg, 0(TMP)
.endm

.macro _write_mtimecmp_32 reg
    li          TMP, MEM_MTIMECMP
    li          TMP2, -1
    sw          TMP2, 0(TMP)
    sw          zero, 4(TMP)
    sw          \reg, 0(TMP)
.endm

.macro _write_mtime reg
    li          TMP, MEM_MTIME
    sw          \reg, 0(TMP)
.endm

.macro _read_mtime reg
    li          TMP, MEM_MTIME
    lw          \reg, 0(TMP)
.endm

// Read
.macro _read_mtimecmp reg
    li          TMP, MEM_MTIMECMP
    lw          \reg, 0(TMP)
.endm

.macro _read_mtime_ctrl reg
    li          TMP, MEM_MTIME_CTRL
    lw          \reg, 0(TMP)
.endm

.macro _read_mtime_div reg
    li          TMP, MEM_MTIME_DIV
    lw          \reg, 0(TMP)
.endm

// Misc
.macro _run_timer
    li          TMP, MEM_MTIME_CTRL
    lw          TMP2, 0(TMP)
    li          TMP3, (1 << SCR1_MTIME_CTRL_EN)
    or          TMP2, TMP2, TMP3
    sw          TMP2, 0(TMP)
.endm

.macro _stop_timer
    li          TMP, MEM_MTIME_CTRL
    lw          TMP2, 0(TMP)
    li          TMP3, (1 << SCR1_MTIME_CTRL_EN)
    not         TMP3, TMP3
    and         TMP2, TMP2, TMP3
    sw          TMP2, 0(TMP)
.endm

#else  /// #if defined(__ASSEMBLER__)

#include <stdint.h>
#include "scr1_specific.h"

static inline void reset_mtime(void)
{
    volatile uint32_t *mem_mtime = (volatile uint32_t *)MEM_MTIME;
    mem_mtime[0] = 0;
    mem_mtime[1] = 0;
}

static inline void reset_mtimecmp(void)
{
    volatile uint32_t *reset_mtimecmp = (volatile uint32_t *)MEM_MTIMECMP;
    reset_mtimecmp[0] = -1;
    reset_mtimecmp[1] = -1;
}

static inline void write_mtime_ctrl(uint32_t val)
{
    volatile uint32_t *mem_mtime_ctrl = (volatile uint32_t *)MEM_MTIME_CTRL;
    *mem_mtime_ctrl = val;
}

static inline void write_mtime_div(uint32_t val)
{
    volatile uint32_t *mem_mtime_div = (volatile uint32_t *)MEM_MTIME_DIV;
    *mem_mtime_div = val;
}


static inline void write_mtimecmp_32(uint32_t val)
{
    volatile uint32_t *mem_mtime_cmp = (volatile uint32_t *)MEM_MTIMECMP;
    mem_mtime_cmp[0] = -1;
    mem_mtime_cmp[1] = 0;
    mem_mtime_cmp[0] = val;
}

static inline void write_mtime(uint32_t val)
{
    volatile uint32_t *mem_mtime = (volatile uint32_t *)MEM_MTIME;
    *mem_mtime = val;
}

static inline uint32_t read_mtime(void)
{
    volatile uint32_t *mem_mtime = (volatile uint32_t *)MEM_MTIME;
    return *mem_mtime;
}

static inline uint32_t read_mtimecmp(void)
{
    volatile uint32_t *mem_mtime_cmp = (volatile uint32_t *)MEM_MTIMECMP;
    return *mem_mtime_cmp;
}

static inline uint32_t read_mtime_ctrl(void)
{
    volatile uint32_t *mem_mtime_ctrl = (volatile uint32_t *)MEM_MTIME_CTRL;
    return *mem_mtime_ctrl;
}

static inline uint32_t read_mtime_div(void)
{
    volatile uint32_t *mem_mtime_div = (volatile uint32_t *)MEM_MTIME_DIV;
    return *mem_mtime_div;
}

static inline void run_timer(void)
{
    volatile uint32_t *mem_mtime_ctrl = (volatile uint32_t *)MEM_MTIME_CTRL;
    *mem_mtime_ctrl |= 1 << SCR1_MTIME_CTRL_EN;
}


static inline void stop_timer(void)
{
    volatile uint32_t *mem_mtime_ctrl = (volatile uint32_t *)MEM_MTIME_CTRL;
    *mem_mtime_ctrl &= ~(1 << SCR1_MTIME_CTRL_EN);
}

#endif  /// #else #if defined(__ASSEMBLER__)

#endif // #ifndef __TIMER__H
