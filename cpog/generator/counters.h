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

// Count all the interesting stuff

typedef enum { 
    COUNT_VAR, COUNT_DATA_VAR, COUNT_CLAUSE, COUNT_POG_AND, COUNT_POG_DECISION_OR, COUNT_POG_OR, COUNT_POG_SKOLEM, COUNT_DEFINING_CLAUSE, COUNT_DEFINING_AUX_CLAUSE,
    COUNT_VISIT_AND, COUNT_VISIT_OR, COUNT_VISIT_SKOLEM, COUNT_VISIT_AND_SAT,
    COUNT_LEMMA_DEFINITION,  COUNT_LEMMA_APPLICATION, COUNT_LEMMA_ARGUMENT_MERGE, COUNT_LEMMA_DUPLICATES,
    COUNT_SAT_CALL, COUNT_AUX_AND,
    COUNT_OR_JUSTIFICATION_CLAUSE, COUNT_AND_JUSTIFICATION_CLAUSE, COUNT_LITERAL_JUSTIFICATION_CLAUSE,
    COUNT_SKOLEM_JUSTIFICATION_CLAUSE,
    COUNT_MONOLITHIC_CLAUSE, COUNT_MUTEX_CLAUSE, COUNT_UNSAT_CLAUSE,
    COUNT_LEMMA_APPLICATION_CLAUSE,
    COUNT_VIRTUAL_CLAUSE,
    COUNT_MUTEX_HINT, COUNT_ADDITION_HINT, COUNT_DELETION_HINT,
    COUNT_NUM
} counter_t;

typedef enum { TIME_TOTAL, TIME_SETUP, TIME_SAT_SETUP, TIME_SAT_TOTAL, TIME_DELETE, TIME_OPTIMIZE, TIME_NUM } etimer_t;

typedef enum { HISTO_PROBLEM, HISTO_PROOF, HISTO_PRODUCT_DEGREE, HISTO_SKOLEM_DEGREE, HISTO_NUM } histogram_t;

/* Allow this headerfile to define C++ constructs if requested */
#ifdef __cplusplus
#define CPLUSPLUS
#endif

#ifdef CPLUSPLUS
extern "C" {
#endif

void clear_count(counter_t counter);
void incr_count(counter_t counter);
void incr_count_by(counter_t counter, int val);
int get_count(counter_t counter);
 long get_long_count(counter_t counter);

void incr_timer(etimer_t timer, double secs);
double get_timer(etimer_t timer);

void incr_histo(histogram_t h, int datum);
int get_histo_min(histogram_t h);
int get_histo_max(histogram_t h);    
long get_histo_count(histogram_t h);
double get_histo_avg(histogram_t h);

#ifdef CPLUSPLUS
}
#endif


/* EOF */
    
