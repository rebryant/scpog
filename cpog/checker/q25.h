/*========================================================================
  Copyright (c) 2023 Randal E. Bryant, Carnegie Mellon University
  
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
#include <stdbool.h>
#include <stdint.h>

/* Allow this headerfile to define C++ constructs if requested */
#ifdef __cplusplus
#define CPLUSPLUS
#endif

#ifdef CPLUSPLUS
extern "C" {
#endif


/* Representation of a number of form -1^(sign) * d * 2^p2 * 5 ^p5
   where:
       d is arbitrary integer, represented as set of digits
          with (RADIX = 10**k for some k)
       p2 and p5 encode positive or negative powers of 2.

   Values are assumed to be immutable.
   All externally visible values stored in canonical form:
       If invalid, then d=0, p2=0, p5=0
       If zero then not negative and d=0, p2=0, p5=0
       If nonzero then not divisible by power of 2 or 5
*/
typedef struct {
    bool valid : 1;    // Is this a valid number
    bool negative: 1;  // Is it negative
    unsigned dcount : 30; // How many digits does it have (must be at least 1)
    int32_t pwr2;         // Power of 2
    int32_t pwr5;         // Power of 5
    uint32_t digit[1];    // Sequence of digits, each between 0 and RADIX-1
} q25_t, *q25_ptr;

void q25_free(q25_ptr q);

/* Make a fresh copy of number */
q25_ptr q25_copy(q25_ptr q);

/* Convert numbers to q25 form */
q25_ptr q25_from_64(int64_t x);
q25_ptr q25_from_32(int32_t x);
q25_ptr q25_invalid();

/* Scale by powers of 2 & 5 */
q25_ptr q25_scale(q25_ptr q, int32_t p2, int32_t p5);

/* Negative value */
q25_ptr q25_negate(q25_ptr q);

/* 
   Compute reciprocal 
   Can only compute reciprocal when d == 1
   Otherwise invalid
*/
q25_ptr q25_recip(q25_ptr q);

/* Is it valid */
bool q25_is_valid(q25_ptr q);

/* Is it zero */
bool q25_is_zero(q25_ptr q);

/* Is it one */
bool q25_is_one(q25_ptr q);

/* 
   Compare two numbers.  Return -1 (q1<q2), 0 (q1=q2), or +1 (q1>q2)
   Return -2 if either invalid
*/
int q25_compare(q25_ptr q1, q25_ptr q2);

/* Addition */
q25_ptr q25_add(q25_ptr q1, q25_ptr q2);

/* Compute 1-x */
q25_ptr q25_one_minus(q25_ptr q);

/* Multiplication */
q25_ptr q25_mul(q25_ptr q1, q25_ptr q2);

/* Read from file */
q25_ptr q25_read(FILE *infile);

/* Write to file */
void q25_write(q25_ptr q, FILE *outfile);

/* Generate dynamically allocated string.  Should free() when done */
char *q25_string(q25_ptr q);


/* Show value in terms of its representation */
void q25_show(q25_ptr q, FILE *outfile);

/* Try converting to int64_t.  Indicate success / failure */
/* Fails if number out of range, or nonintegral */
bool get_int64(q25_ptr q, int64_t *ip);

/* Count of number of non-trivial operations since initialization */
long q25_operation_count();

#ifdef CPLUSPLUS
}
#endif
