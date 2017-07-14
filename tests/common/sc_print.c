/// Copyright by Syntacore LLC © 2016, 2017. See LICENSE for details
/// @file       <sc_print.c>
///

#include <string.h>
#include <stdarg.h>
#include "sc_print.h"

#define SC_SIM_OUTPORT (0xf0000000)
#define CHAR_BIT (8)

static void
sc_puts(long str, long strlen) {
	volatile char *out_ptr = (volatile char*)SC_SIM_OUTPORT;
	const char *in_ptr = (const char*)str;
	for (long len = strlen; len > 0; --len)
	  *out_ptr = *in_ptr++;
}

#undef putchar
int
putchar(int ch) {
	static __thread char buf[64] __attribute__((aligned(64)));
    static __thread int buflen = 0;

    buf[buflen++] = ch;

	if ( ch == '\n' || buflen == sizeof(buf) ) {
        sc_puts((long)buf, buflen);
        buflen = 0;
    }

    return 0;
}

static void
printf_putch(int ch, void** data)
{
    putchar(ch);
}

static void
print(const char *str)
{
  sc_puts((long)str, strlen(str));
}


static long long
getint(va_list *ap, int lflag)
{
    if ( lflag >= 2 )
        return va_arg(*ap, long long);
    else if ( lflag )
        return va_arg(*ap, long);
    else
        return va_arg(*ap, int);
}


static unsigned long long
getuint(va_list *ap, int lflag)
{
    if ( lflag >= 2 )
        return va_arg(*ap, unsigned long long);
    else if ( lflag )
        return va_arg(*ap, unsigned long);
    else
        return va_arg(*ap, unsigned int);
}

static inline void
printnum(void(*putch)(int, void**),
void **putdat,
unsigned long long num,
unsigned base,
int width,
int padc,
int hex_A)
{
    unsigned digs[sizeof(num) * CHAR_BIT];
    int pos = 0;

    for ( ;; ) {
        digs[pos++] = num % base;
        if ( num < base )
            break;
        num /= base;
    }

    while ( width-- > pos )
        putch(padc, putdat);

    while ( pos-- > 0 )
        putch(digs[pos] + (digs[pos] >= 10 ? hex_A - 10 : '0'), putdat);
}

static void
vprintfmt(void(*putch)(int, void**), void **putdat, const char *fmt, va_list ap)
{
    register const char* p;
    const char* last_fmt;
    register int ch;
    int err;
    unsigned long long num;
    int base;
    int lflag;
    int width;
    int precision;
    int altflag;
    char padc;
    int hex_A = 'a';
    for ( ;; ) {
        while ( (ch = *(unsigned char *)fmt) != '%' ) {
            if ( ch == '\0' )
                return;
            ++fmt;
            putch(ch, putdat);
        }
        ++fmt;

        // Process a %-escape sequence
        last_fmt = fmt;
        padc = ' ';
        width = -1;
        precision = -1;
        lflag = 0;
        altflag = 0;

reswitch:
        switch ( ch = *(unsigned char *)fmt++ ) {
            // flag to pad on the right
            case '-':
                padc = '-';
                goto reswitch;

                // flag to pad with 0's instead of spaces
            case '0':
                padc = '0';
                goto reswitch;

                // width field
            case '1':
            case '2':
            case '3':
            case '4':
            case '5':
            case '6':
            case '7':
            case '8':
            case '9':
                for ( precision = 0;; ++fmt ) {
                    precision = precision * 10 + ch - '0';
                    ch = *fmt;
                    if ( ch < '0' || ch > '9' )
                        break;
                }
                goto process_precision;

            case '*':
                precision = va_arg(ap, int);
                goto process_precision;

            case '.':
                if ( width < 0 )
                    width = 0;
                goto reswitch;

            case '#':
                altflag = 1;
                goto reswitch;

process_precision:
                if ( width < 0 ) {
                    width = precision;
                    precision = -1;
                }
                goto reswitch;

                // long flag (doubled for long long)
            case 'l':
                lflag++;
                goto reswitch;

                // character
            case 'c':
                putch(va_arg(ap, int), putdat);
                break;

                // string
            case 's':
                if ( (p = va_arg(ap, char *)) == NULL )
                    p = "(null)";
                if ( width > 0 && padc != '-' )
                    for ( width -= strnlen(p, precision); width > 0; width-- )
                        putch(padc, putdat);
                for ( ; (ch = *p) != '\0' && (precision < 0 || --precision >= 0); width-- ) {
                    putch(ch, putdat);
                    p++;
                }
                for ( ; width > 0; width-- )
                    putch(' ', putdat);
                break;

                // (signed) decimal
            case 'd':
                num = getint(&ap, lflag);
                if ( (long long)num < 0 ) {
                    putch('-', putdat);
                    num = -(long long)num;
                }
                base = 10;
                goto signed_number;

            case 'f':
                {
                    // #ifndef nopfloat
                    // double num = getdouble(&ap, lflag);
                    // printdoubleF(putch, putdat, num, width, precision, padc);
                    // #endif
                }
                break;

                // unsigned decimal
            case 'u':
                base = 10;
                goto unsigned_number;

                // (unsigned) octal
            case 'o':
                // should do something with padding so it's always 3 octits
                base = 8;
                goto unsigned_number;

                // pointer
            case 'p':
                // static_assert(sizeof(long) == sizeof(void*));
                lflag = 1;
                putch('0', putdat);
                putch('x', putdat);
                /* fall through to 'x' */

                // (unsigned) hexadecimal
            case 'x':
                hex_A = 'a';
                base = 16;
                goto unsigned_number;

            case 'X':
                hex_A = 'A';
                base = 16;
unsigned_number:
                num = getuint(&ap, lflag);
signed_number:
                printnum(putch, putdat, num, base, width, padc, hex_A);
                break;

                // escaped '%' character
            case '%':
                putch(ch, putdat);
                break;

                // unrecognized escape sequence - just print it literally
            default:
                putch('%', putdat);
                fmt = last_fmt;
                break;
        }
    }
}

int
sc_printf(const char* fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);

    vprintfmt(printf_putch, NULL, fmt, ap);

    va_end(ap);
    return 0; // incorrect return value, but who cares, anyway?
}
