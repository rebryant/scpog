/*========================================================================
  Copyright (c) 2025 Randal E. Bryant, Carnegie Mellon University
  
  Permission is hereby granted, free of
  charge, to any person obtaining a copy of this software and
  associated documentation files (the "Software"), to deal in the
  Software without restriction, including without limitation the
  rights to use, copy, modify, merge, publish, distribute, sublicense,
  and/or sell copies of the Software, and to permit persons to whom
  the Software is furnished to do so, subject to the following
  conditions:
  
  The above copyright notice and this permission notice shall be
  included in all copies or substantial portions of the Software.
  
  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
  ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
  CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.
========================================================================*/

#pragma once

#include <stdio.h>
#include <iostream>

#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <ctype.h>
#include <limits.h>
#include <math.h>
#include <gmp.h>
#include "gmpxx.h"

/*
  Representation of floating-point numbers based on double,
  but with additional exponent field to support extended range
 */
typedef struct {
    double dbl; 
    int64_t exp; 
} erd_t;



/********************* Defines **********************/ 

/* 
   Use library code to manipulate numbers? 
   Functionally correct, but runs a bit slower than what can get with bit manipulation
*/

#define ERD_LIBRARY 0

/* 
   Support two versions: 
   DEFAULT:     0.0 has exp = INT64_MIN
   ERDZ:        0.0 has exp = 0
   Must be ERDZ for library
*/
#define ERDZ 1

#if ERDZ
#define ZEXP 0
#else
#define ZEXP INT64_MIN
#endif

/* Two ways of implementing normalization: standard and one that reduces need for conditional control */
/*   Must be standardfor library */
#define ERD_NORM_STD 1

/* Max number of times fractions can be multiplied without overflowing exponent */
#define MAX_MUL 1000

/* Required size of buffer from printing ERD */
#define ERD_BUF 40
/* Number of significant digits when printing ERD */
#define ERD_NSIG 16

/********************* Double **********************/

#define DBL_MAX_PREC 54
#define DBL_EXP_OFFSET 52
#define DBL_SIGN_OFFSET 63
#define DBL_EXP_MASK ((uint64_t) 0x7ff)
#define DBL_BIAS ((int64_t) 0x3ff)

#if ERD_LIBRARY

static uint64_t dbl_get_bits(double x) {
    union {
	double   d;
	uint64_t b;
    } u;
    u.d = x;
    return u.b;
}

/* Get exponent as unsigned integer */
static uint64_t dbl_get_biased_exponent(double x) {
    uint64_t bx = dbl_get_bits(x);
    return (bx >> DBL_EXP_OFFSET) & DBL_EXP_MASK;
}

/* Get exponent as signed integer */
static int64_t dbl_get_exponent(double x) {
    int64_t bexp = (int64_t) dbl_get_biased_exponent(x);
    return bexp - DBL_BIAS;
}

/* Signed exponent too small */
static bool dbl_exponent_below(int64_t exp) {
    return exp <= -(int64_t) DBL_BIAS;
}

/* Signed exponent too large */
static bool dbl_exponent_above(int64_t exp) {
    return exp >= (int64_t) DBL_EXP_MASK - DBL_BIAS;
}

#else /* !ERD_LIBRARY */

static uint64_t dbl_get_bits(double x) {
    union {
	double   d;
	uint64_t b;
    } u;
    u.d = x;
    return u.b;
}

static double dbl_from_bits(uint64_t bx) {
    union {
	double   d;
	uint64_t b;
    } u;
    u.b = bx;
    return u.d;
}

/* Get exponent as unsigned integer */
static uint64_t dbl_get_biased_exponent(double x) {
    uint64_t bx = dbl_get_bits(x);
    return (bx >> DBL_EXP_OFFSET) & DBL_EXP_MASK;
}

/* Get exponent as signed integer */
static int64_t dbl_get_exponent(double x) {
    int64_t bexp = (int64_t) dbl_get_biased_exponent(x);
    return bexp - DBL_BIAS;
}

static uint64_t dbl_get_sign(double x) {
    uint64_t bx = dbl_get_bits(x);
    return (bx >> DBL_SIGN_OFFSET) & 0x1;
}

static uint64_t dbl_get_fraction(double x) {
    uint64_t bx = dbl_get_bits(x);
    uint64_t umask = ((int64_t) 1 << DBL_EXP_OFFSET) - 1;
    return bx & umask;
}

/* Signed exponent too small */
static bool dbl_exponent_below(int64_t exp) {
    return exp <= -(int64_t) DBL_BIAS;
}

/* Signed exponent too large */
static bool dbl_exponent_above(int64_t exp) {
    return exp >= (int64_t) DBL_EXP_MASK - DBL_BIAS;
}

static double dbl_assemble(uint64_t sign, int64_t exp, uint64_t frac) {
    int64_t bexp = exp + DBL_BIAS;
    uint64_t bx = frac;
    bx += bexp << DBL_EXP_OFFSET;
    bx += sign << DBL_SIGN_OFFSET;
    return dbl_from_bits(bx);
}

static double dbl_replace_exponent(double x, int64_t exp) {
    uint64_t bexp = (uint64_t) (exp + DBL_BIAS);
#if !ERDZ
    bexp &= DBL_EXP_MASK;
#endif
    bexp = bexp << DBL_EXP_OFFSET;
    uint64_t bx = dbl_get_bits(x);
    uint64_t mask = ~(DBL_EXP_MASK << DBL_EXP_OFFSET);
    bx &= mask;
    bx += bexp;
    return dbl_from_bits(bx);
}

static double dbl_zero_exponent(double x) {
    uint64_t bexp = (uint64_t) DBL_BIAS << DBL_EXP_OFFSET;
    uint64_t bx = dbl_get_bits(x);
    uint64_t mask = ~(DBL_EXP_MASK << DBL_EXP_OFFSET);
    bx &= mask;
    bx += bexp;
    return dbl_from_bits(bx);
}


static double dbl_infinity(int sign) {
    return dbl_assemble(sign, DBL_EXP_MASK - DBL_BIAS, 0);
}
#endif


/********************* ERD *************************/

static bool erd_is_zero(erd_t a) {
    return a.dbl == 0.0;
}

static erd_t erd_zero() {
    erd_t nval;
    nval.dbl = 0.0;
    nval.exp = ZEXP;
    return nval;
}

static erd_t erd_normalize_standard(erd_t a) {
    if (erd_is_zero(a))
	return erd_zero();
    erd_t nval;
#if ERD_LIBRARY
    int dexp;
    nval.dbl = frexp(a.dbl, &dexp);
    nval.exp = a.exp + dexp;
#else
    nval.exp = a.exp + dbl_get_exponent(a.dbl);
    nval.dbl = dbl_zero_exponent(a.dbl);
#endif
    return nval;
}

#if !ERD_LIBRARY
// Variant that avoids testing double
static erd_t erd_normalize_nocond(erd_t a) {
    uint64_t ba = dbl_get_bits(a.dbl);
    uint64_t bx = (ba >> DBL_EXP_OFFSET) & DBL_EXP_MASK;
    uint64_t nx = ba ? DBL_BIAS: 0;
    uint64_t mask = ~(DBL_EXP_MASK << DBL_EXP_OFFSET);
    uint64_t na = (ba & mask) + (nx << DBL_EXP_OFFSET);
    erd_t nval;
    nval.dbl = dbl_from_bits(na);
    nval.exp = ba ? a.exp + ((int64_t) bx - DBL_BIAS) : ZEXP;
    return nval;
}
#endif

static erd_t erd_normalize(erd_t a) {
#if ERD_NORM_STD || ERD_LIBRARY
    return erd_normalize_standard(a);
#else
    return erd_normalize_nocond(a);
#endif    
}

static erd_t erd_from_double(double dval) {
    erd_t nval;
#if ERDZ || ERD_LIBRARY
    nval.exp = 0;
#else
    nval.exp = dval == 0 ? ZEXP : 0;
#endif
    nval.dbl = dval;
    return erd_normalize(nval);
}

static erd_t erd_from_mpf(mpf_srcptr fval) {
    erd_t nval;
    long int exp;
    nval.dbl = mpf_get_d_2exp(&exp, fval);
#if !ERDZ
    if (nval.dbl == 0)
	return erd_zero();
#endif
    nval.exp = (int64_t) exp;
    return erd_normalize(nval);
}

/* Generate integral power of 10 */
static long long p10(int exp) {
    if (exp < 0)
	return 0;
    long long result = 1;
    long long power = 10;
    while (exp != 0) {
	if (exp & 0x1)
	    result *= power;
	power *= power;
	exp = exp >> 1;
    }
    return result;
}

static void erd_to_mpf(mpf_ptr dest, erd_t eval) {
    mpf_set_d(dest, eval.dbl);
#if !ERDZ
    if (erd_is_zero(eval))
	return;
#endif
    if (eval.exp < 0)
	mpf_div_2exp(dest, dest, -eval.exp);
    else if (eval.exp > 0)
	mpf_mul_2exp(dest, dest, eval.exp);
}

static double erd_to_double(erd_t eval) {
    if (erd_is_zero(eval))
	return 0.0;
#if ERD_LIBRARY
    if (eval.exp > INT_MAX)
	return eval.dbl < 0 ? -INFINITY : INFINITY;
    if (eval.exp < INT_MIN)
	return 0.0;
    return ldexp(eval.dbl, eval.exp);
#else
    if (dbl_exponent_below(eval.exp))
	return 0.0;
    if (dbl_exponent_above(eval.exp)) {
	int sign = dbl_get_sign(eval.dbl);
	return dbl_infinity(sign);
    }
    return dbl_replace_exponent(eval.dbl, eval.exp);
#endif
}

static bool erd_is_equal(erd_t a, erd_t b) {
    if (erd_is_zero(a))
	return erd_is_zero(b);
    return a.dbl == b.dbl && a.exp == b.exp;
}

static erd_t erd_negate(erd_t a) {
    erd_t nval;
    if (erd_is_zero(a))
	return a;
    nval.exp = a.exp;
    nval.dbl = -a.dbl;
    return nval;
}

static erd_t erd_add(erd_t a, erd_t b) {
#if ERDZ
    if (erd_is_zero(a))
	return b;
    if (erd_is_zero(b))
	return a;
#endif
    if (a.exp > b.exp + DBL_MAX_PREC)
	return a;
    if (b.exp > a.exp + DBL_MAX_PREC)
	return b;
    erd_t nval;
    int64_t ediff = a.exp - b.exp;
#if ERD_LIBRARY
    double ad = ldexp(a.dbl, ediff);
#else
    double ad = dbl_replace_exponent(a.dbl, ediff);
#endif
    nval.dbl = ad + b.dbl;
    nval.exp = b.exp;
    return erd_normalize(nval);
}

static erd_t erd_quick_mul(erd_t a, erd_t b) {
    erd_t nval;
    nval.exp = a.exp + b.exp;
    nval.dbl = a.dbl * b.dbl;
    return nval;
}


static erd_t erd_mul(erd_t a, erd_t b) {
    return erd_normalize(erd_quick_mul(a, b));
}

static erd_t erd_mul_seq_slow(erd_t *val, int len) {
    erd_t result = erd_from_double(1.0);
    int i;
    for (i = 0; i < len; i++)
	result = erd_mul(result, val[i]);
    return result;
}

static erd_t erd_mul_seq_x1(erd_t *val, int len) {
    if (len == 0)
	return erd_from_double(1.0);
    erd_t result = val[0];
    int i;
    int count = 1;
    for (i = 1; i < len; i++) {
	erd_t arg = val[i];
	result = erd_quick_mul(result, arg);
	if (++count > MAX_MUL) {
	    count = 0;
	    result = erd_normalize(result);
	}
    }
    return erd_normalize(result);
}

static erd_t erd_mul_seq_x4(erd_t *val, int len) {
    // Assume len >= 4
    erd_t prod[4];
    int i, j;
    for (j = 0; j < 4; j++) 
	prod[j] = val[j];
    int count = 0;
    for (i = 4; i <= len-4; i+= 4) {
	for (j = 0; j < 4; j++)
	    prod[j] = erd_quick_mul(prod[j], val[i+j]);
	if (++count > MAX_MUL) {
	    count = 0;
	    for (j = 0; j < 4; j++)
		prod[j] = erd_normalize(prod[j]);
	}
    }
    if (count * 4 > MAX_MUL) {
	for (j = 0; j < 4; j++)
	    prod[j] = erd_normalize(prod[j]);
    }

    erd_t result = prod[0];
    for (j = 1; j < 4; j++)
	result = erd_quick_mul(result, prod[j]);
    for (; i < len; i++)
	result = erd_quick_mul(result, val[i]);
    return erd_normalize(result);
}

/* Compute product of sequence of values */
static erd_t erd_mul_seq(erd_t *val, int len) {
    if (len < 8)
	return erd_mul_seq_x1(val, len);
    return erd_mul_seq_x4(val, len);
}

static erd_t erd_div(erd_t a, erd_t b) {
    erd_t nval;
    nval.dbl = a.dbl / b.dbl;
    nval.exp = a.exp - b.exp;
    return erd_normalize(nval);
}

static int erd_cmp(erd_t a, erd_t b) {
    int rval = 0;
    if (!erd_is_equal(a, b)) {
	int sa = a.dbl < 0;
	int sb = b.dbl < 0;
	int za = a.dbl == 0;
	int zb = b.dbl == 0;
	if (!sa && sb)
	    rval = 1;
	else if (sa && !sb)
	    rval = -1;
	else if (za) {
	    if (zb)
		rval = 0;
	    else
		/* Must have b > 0 */
		rval = -1;
	} else if (zb) {
	    /* Must have a > 0 */
	    rval = 1;
	} else {
	    int flip = sa ? -1 : 1;
	    if (a.exp > b.exp)
		rval = flip;
	    if (a.exp < b.exp)
		rval = -flip;
	    if (a.dbl < b.dbl)
		rval = flip;
	}
    }
    return rval;
}

static erd_t erd_sqrt(erd_t a) {
    if (erd_is_zero(a) || a.dbl < 0)
	return erd_zero();
    double da = a.dbl;
    int64_t ea = a.exp;
    if (ea % 2) {
	da *= 2;
	ea--;
    }
    erd_t nval;
    nval.dbl = sqrt(da);
    nval.exp = ea/2;
    return erd_normalize(nval);
}


/* Create right-justified string representation of nonnegative number */
static void rj_string(char *sbuf, long long val, int len) {
    int i;
    for (i = 0; i < len; i++)
	sbuf[i] = '0';
    sbuf[len] = 0;
    if (val <= 0)
	return;
    i = len-1;
    while(val) {
	sbuf[i--] = '0' + (val % 10);
	val = val / 10;
    }
}

/* Buf must point to buffer with at least ERD_BUF character capacity */
static void erd_string(erd_t a, char *buf, int nsig) {
    char sbuf[25];
    if (nsig <= 0)
	nsig = 1;
    if (nsig > 20)
	nsig = 20;
    if (erd_is_zero(a)) {
	snprintf(buf, ERD_BUF, "0.0");
	return;
    }
    const char *sgn = "";
    double da = a.dbl;
    int64_t de = a.exp;
    if (da < 0) {
	da = -da;
	sgn = "-";
    }
    // Convert exponent to base 10
    double dlog = ((double) de) * log10(2.0);
    // Get integer part of exponent
    long long dec = (long long) floor(dlog);
    // Incorporate the fractional part of the exponent into da
    da *= __exp10(dlog-floor(dlog));
    // Get decimal exponent for da
    long long dexp = (long long) floor(log10(da));
    // Add to decimal exponent
    dec += dexp;
    // Scale da to become integer representation of final fraction
    da *= p10(nsig-1-dexp);
    // Round it
    long long dfrac = llround(da);
    // Get digits to the left and right of the decimal point
    long long sep = p10(nsig-1);
    long long lfrac = dfrac / sep;
    long long rfrac = dfrac % sep;
    rj_string(sbuf, rfrac, nsig-1);
    if (dec == 0) 
	snprintf(buf, ERD_BUF, "%s%lld.%s", sgn, lfrac, sbuf);
    else
	snprintf(buf, ERD_BUF, "%s%lld.%se%lld", sgn, lfrac, sbuf, dec);
}

/* Logarithms */
static double erd_log2d(erd_t a) {
    if (a.dbl <= 0)
	return 0.0;
    return log2(a.dbl) + (double) a.exp;
}

static erd_t erd_log2(erd_t a) {
    return erd_from_double(erd_log2d(a));
}

static double erd_log10d(erd_t a) {
    return erd_log2d(a) * log10(2.0);
}

static erd_t erd_log10(erd_t a) {
    return erd_from_double(erd_log10d(a));
}

static unsigned erd_to_unsigned(erd_t a) {
  if (a.dbl <= 0)
      return 0U;
  if (a.exp > 1000)
      return UINT_MAX;
  double d = erd_to_double(a);
  if (d > UINT_MAX)
    return UINT_MAX;
  return (unsigned) d;
}


/* Generate erd power of 10 */
static erd_t ep10(int exp) {
    double dp = 10.0;
    if (exp < 0) {
	exp = -exp;
	dp = 0.1;
    }
    erd_t power = erd_from_double(dp);
    erd_t result = erd_from_double(1.0);
    while (exp != 0) {
	if (exp & 0x1)
	    result = erd_mul(result, power);
	power = erd_mul(power, power);
	exp = exp >> 1;
    }
    return result;
}

static int erd_sscanf(const char *s, erd_t *result) {
    char buf[50];
    erd_t nval = erd_zero();
    int i = 0;
    while (i < sizeof(buf) && *s != 0 && *s != 'e' && *s != 'E')
	buf[i++] = *s++;
    buf[i++] = 0;
    bool ok = sscanf(buf, "%lf", &nval.dbl) > 0;
    if (ok && *s != 0) {
	long long lexp = 0;
	ok = sscanf(s+1, "%lld", &lexp) > 0;
	erd_t p10 = ep10(lexp);
	nval = erd_mul(nval, p10);
    }
    if (ok) 
	*result = erd_normalize(nval);
    else
	*result = erd_zero();
    return (int) ok;
}

static int erd_fscanf(FILE *infile, erd_t *result) {
    char buf[100];
    int c;
    while ((c = fgetc(infile)) != EOF && isspace(c))
	;
    int i = 0;
    while ((c = fgetc(infile)) != EOF && i < sizeof(buf) &&
	   !isspace(c) && (isdigit(c) || c == 'e' || c == 'E' || c == '.'))
	buf[i++] = c;
    buf[i] = 0;
    return erd_sscanf((const char *) buf, result);
}

class Erd {
private:
    erd_t eval;

    Erd(erd_t val) { eval = val; }

    erd_t& get_erd_t() { return eval; }

public:

    Erd() { eval = erd_zero(); }

    Erd(double d) { eval = erd_from_double(d); }

    Erd(int i) { eval = erd_from_double((double) i); }

    Erd(mpf_srcptr mval) { eval = erd_from_mpf(mval); }

    bool is_zero() { return erd_is_zero(eval); }

    void get_mpf(mpf_ptr dest) { return erd_to_mpf(dest, eval); }
    mpf_class get_mpf() { mpf_class val; erd_to_mpf(val.get_mpf_t(), eval); return val; }

    double get_double() { return erd_to_double(eval); }

    Erd add(const Erd &other) const { return Erd(erd_add(eval, other.eval)); }

    Erd mul(const Erd &other) const { return Erd(erd_mul(eval, other.eval)); }

    Erd log2() const { return erd_log2(eval); }

    Erd log10() const { return erd_log10(eval); }

    Erd& operator=(const Erd &v) { eval = v.eval; return *this; }
    Erd& operator=(const mpf_t v) { eval = erd_from_mpf(v); return *this; }
    Erd& operator=(const double v) { eval = erd_from_double(v); return *this; }
    Erd& operator=(const unsigned long int v) { eval = erd_from_double((double) v); return *this; }
    Erd& operator=(const unsigned long long int v) { eval = erd_from_double((double) v); return *this; }
    Erd& operator=(const long long int v)  { eval = erd_from_double((double) v); return *this; }
    Erd& operator=(const unsigned int v)  { eval = erd_from_double((double) v); return *this; }
    Erd& operator=(const long int v)  { eval = erd_from_double((double) v); return *this; }
    Erd& operator=(const int v)  { eval = erd_from_double((double) v); return *this; }

    bool operator==(const Erd &other) const { return erd_is_equal(eval, other.eval); }
    bool operator!=(const Erd &other) const { return !erd_is_equal(eval, other.eval); }
    Erd operator+(const Erd &other) const { return Erd(erd_add(eval, other.eval)); }
    Erd operator*(const Erd &other) const { return Erd(erd_mul(eval, other.eval)); }
    Erd operator*(double &other) const { return Erd(erd_mul(eval, erd_from_double(other))); }
    Erd operator/(const Erd &other) const { return Erd(erd_div(eval, other.eval)); }
    Erd operator-() const { return Erd(erd_negate(eval)); }
    Erd operator-(const Erd &other) const { return Erd(erd_add(eval, erd_negate(other.eval))); }
    Erd& operator*=(const Erd &other) { eval = erd_mul(eval, other.eval); return *this; }
    Erd& operator*=(double &other) { eval = erd_mul(eval, erd_from_double(other)); return *this; }
    Erd& operator+=(const Erd &other) { eval = erd_add(eval, other.eval); return *this; }
    Erd& operator/=(const Erd &other) { eval = erd_div(eval, other.eval); return *this; }
    bool operator<(const Erd &other) const { return erd_cmp(eval, other.eval) < 0; }
    bool operator<=(const Erd &other) const { return erd_cmp(eval, other.eval) <= 0; }
    bool operator>(const Erd &other) const { return erd_cmp(eval, other.eval) > 0; }
    bool operator>=(const Erd &other) const { return erd_cmp(eval, other.eval) >= 0; }

    explicit operator unsigned() const { return erd_to_unsigned(eval); }
    explicit operator double() const { return erd_to_double(eval); }

    friend Erd product_reduce_x1(Erd *data, int len) {
	erd_t prod = erd_from_double(1.0);
	int rcount = 0;
	for (int i = 0; i < len; i++) {
	    prod = erd_quick_mul(prod, data[i].get_erd_t());
	    if (++rcount >= MAX_MUL) {
		erd_normalize(prod);
		rcount = 0;
	    }
	}
	erd_normalize(prod);
	return Erd(prod);
    }

    friend Erd product_reduce_x4(Erd *data, int len) {
	// Assume len >= 4
	erd_t prod[4];
	int i, j;
	for (j = 0; j < 4; j++) 
	    prod[j] = data[j].get_erd_t();
	int count = 0;
	for (i = 4; i <= len-4; i+= 4) {
	    for (j = 0; j < 4; j++)
		prod[j] = erd_quick_mul(prod[j], data[i+j].get_erd_t());
	    if (++count > MAX_MUL) {
		count = 0;
		for (j = 0; j < 4; j++)
		    prod[j] = erd_normalize(prod[j]);
	    }
	}
	if (count * 4 > MAX_MUL) {
	    for (j = 0; j < 4; j++)
		prod[j] = erd_normalize(prod[j]);
	}
	erd_t result = prod[0];
	for (j = 1; j < 4; j++)
	    result = erd_quick_mul(result, prod[j]);
	for (; i < len; i++)
	    result = erd_quick_mul(result, data[i].get_erd_t());
	return Erd(erd_normalize(result));
    }


    friend Erd product_reduce(Erd *data, int len) {
	if (len >= 8)
	    return product_reduce_x4(data, len);
	else
	    return product_reduce_x1(data, len);
    }

    friend Erd product_reduce(std::vector<Erd> data) { return product_reduce(data.data(), (int) data.size()); }

    friend std::ostream& operator<<(std::ostream& os, const Erd &a) {
	char buf[ERD_BUF];
	erd_string(a.eval, buf, ERD_NSIG);
	os << (const char *) buf;
	return os;
    }

    friend std::istream& operator>>(std::istream& is, Erd &a) {
	std::string s;
	is >> s;
	if (erd_sscanf(s.data(), &a.eval) == 0)
	    is.setstate(std::ios::failbit);
	return is;
    }
};

