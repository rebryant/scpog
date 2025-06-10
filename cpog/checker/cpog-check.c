/*========================================================================
  Copyright (c) 2022, 2024 Randal E. Bryant, Carnegie Mellon University

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

#ifndef THREADING
#define THREADING 0
#endif

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include <stdbool.h>
#include <sys/time.h>
#include <limits.h>
#include <stdarg.h>

#if THREADING
#include <pthread.h>
#endif

#include "q25.h"


#define VLEVEL 2

void usage(char *name) {
    printf("Usage: %s [-h] [-v VERB] [-L LOGFILE] [-A] [-D] [-n THREADS] FILE.cnf [FILE.cpog]\n", name);
    printf(" -h           Print this message\n");
    //    printf(" -d           Use explicit input clause deletion\n");
    //    printf(" -l           Lenient mode.  Allow non-propagating RUP steps, and allow duplicates in lists of literals\n");
    printf(" -v VERB      Set verbosity level\n");
    printf(" -L LOGFILE   Record results in LOGFILE\n");
    printf(" -A           Don't check clause additions\n");
    printf(" -D           Don't check clause deletions\n");
    //    printf(" -w           Check weak projected compilation: Don't require mutex sum nodes, and don't attempt to count models\n");
    printf(" -n THREADS   Use multithreading with specified number of threads\n");
    printf("    FILE.cnf  Input CNF file\n");
    printf("    FILE.cpog Input CPOG (or SCPOG) file\n");
    exit(0);
}

/*============================================
  Macro parameters
============================================*/

#define ERROUT stdout
#define MIN_SIZE 10
#define MAX_GAP 10
#define GROW_RATIO 1.45
#define DPREFIX "CHECK"
#define __cfunc__ (char *) __func__

/* How many ints fit into a single chunk (2^20 = 4MB) */
#define CHUNK_SIZE (1L << 20)
/* What is assumed limit of VM (128 GB) */
#define VM_LIMIT (1L << 37)
/* What is the maximum number of chunks (32K) */
#define CHUNK_MAX (VM_LIMIT/(CHUNK_SIZE * sizeof(int)))

/* Parameters for tracking progress on deletions */
#define REPORT_MIN_INTERVAL 1000
#define REPORT_MAX_INTERVAL 100000
#define REPORT_MAX_COUNT 10
/* How many input clauses should be deleted in one pass by a thread */
#define CLAUSE_DELETION_BLOCK 250
//#define CLAUSE_DELETION_BLOCK 10

/* Reporting */
double start_time = 0.0;

/* Optional log file */
const char *logfile_name = NULL;

/*============================================
  Global variables.  Others are later in file.
============================================*/

/* Options */
int verb_level = 3;

bool check_add = true;
bool check_delete = true;
bool weak_mode = false;
bool use_explicit_deletion = false;

/* Maximum number of threads */
int thread_limit = 0;

/* Allow multiple copies of same literal in Skolem node arguments */
bool repeated_literal_ok = false;

/* Parameters related to projecting knowledge compilation */
bool is_pkc = false;

/* Set of data (show) variables.  Indexed by v-1 */
bool *show_variables = NULL;
int show_variables_size = 0;

/* Allow RUP proofs that encounter conflict before final hint */
bool early_rup = true;
/* Allow RUP proofs that don't have unit propagation for each hint */
bool skipping_rup = false;

/* Information for error reporting */
char *current_file = "";
int line_count = 0;

int input_clause_count = 0;
int input_variable_count = 0;
long virtual_clause_count = 0;
int variable_limit = 0;

/* Global properties */

/* Allow declaration of root node.  Must match literal in root clause */
int declared_root = 0;
bool root_clause_added = false;

bool declared_unsatisfiable = false;
bool proved_unsatisfiable = false;

/* Informational counters */

/* Count number of explicit and implicit deletions */
int explicit_deletion_count = 0;
int implicit_deletion_count = 0;

/* Count number of events processed during reverse implication */
long event_count = 0;

/* POG counters */
int cpog_operation_count = 0;
int cpog_forward_count = 0;
int cpog_structural_count = 0;
int cpog_input_deletion_count = 0;
int cpog_noninput_deletion_count = 0;
int cpog_tseitin_clause_count = 0;
int cpog_skolem_clause_count = 0;
int cpog_disable_clause_count = 0;

#if THREADING
/* Mutexes */
pthread_mutex_t print_lock;
pthread_mutex_t queue_lock;

void init_threading() {
    pthread_mutex_init(&print_lock, NULL);
    pthread_mutex_init(&queue_lock, NULL);
}
#endif /* THREADING */

/*============================================
  Prototypes
============================================*/

void clause_show(FILE *out, int cid, bool endline);

/*============================================
  Utility functions
============================================*/

double tod() {
    struct timeval tv;
    if (gettimeofday(&tv, NULL) == 0)
	return (double) tv.tv_sec + 1e-6 * tv.tv_usec;
    else
	return 0.0;
}

double elapsed() {
    return tod() - start_time;
}


void err_printf(char *fun, char *fmt, ...) {
#if THREADING
    if (thread_limit > 1)
	pthread_mutex_lock(&print_lock);
#endif /* THREADING */
    va_list ap;
    fprintf(ERROUT, "ERROR. File %s. Line %d. Function %s. ", current_file, line_count+1, fun);
    va_start(ap, fmt);
    vfprintf(ERROUT, fmt, ap);
    va_end(ap);
    if (logfile_name) {
	FILE *logfile = fopen(logfile_name, "a");
	if (logfile) {
	    fprintf(logfile, "ERROR. File %s. Line %d. Function %s. ", current_file, line_count+1, fun);
	    va_start(ap, fmt);
	    vfprintf(logfile, fmt, ap);
	    va_end(ap);
	    fclose(logfile);
	}
    }
#if THREADING
    if (thread_limit > 1)
	pthread_mutex_unlock(&print_lock);
#endif
    exit(1);
}

void info_printf(int vlevel, char *fmt, ...) {
    if (vlevel > verb_level)
	return;
#if THREADING
    if (thread_limit > 1)
	pthread_mutex_lock(&print_lock);
#endif /* THREADING */
    va_list ap;
    fprintf(stdout, "File %s. Line %d:", current_file, line_count+1);
    va_start(ap, fmt);
    vfprintf(stdout, fmt, ap);
    va_end(ap);
    if (logfile_name) {
	FILE *logfile = fopen(logfile_name, "a");
	if (logfile) {
	    fprintf(logfile, "File %s. Line %d:", current_file, line_count+1);
	    va_start(ap, fmt);
	    vfprintf(logfile, fmt, ap);
	    va_end(ap);
	    fclose(logfile);
	}
    }
#if THREADING
    if (thread_limit > 1)
	pthread_mutex_unlock(&print_lock);
#endif
}

void data_printf(int vlevel, char *fmt, ...) {
    if (vlevel > verb_level)
	return;
#if THREADING
    if (thread_limit > 1)
	pthread_mutex_lock(&print_lock);
#endif /* THREADING */
    va_list ap;
    fprintf(stdout, "%s: ", DPREFIX);
    va_start(ap, fmt);
    vfprintf(stdout, fmt, ap);
    va_end(ap);
    if (logfile_name) {
	FILE *logfile = fopen(logfile_name, "a");
	if (logfile) {
	    fprintf(logfile, "%s: ", DPREFIX);
	    va_start(ap, fmt);
	    vfprintf(logfile, fmt, ap);
	    va_end(ap);
	    fclose(logfile);
	}
    }
#if THREADING
    if (thread_limit > 1)
	pthread_mutex_unlock(&print_lock);
#endif
}

/*============================================
   Integer lists
============================================*/

/*
  Data type ilist is used to represent clauses and clause id lists.
  These are simply lists of integers, where the value at position -1
  indicates the list length and the value at position -2 indicates the
  maximum list length.  The value at position -2 is positive for
  statically-allocated ilists and negative for ones that can be
  dynamically resized.
*/
typedef int *ilist;
  
/* Macros */
/*
  Difference between ilist maximum length and number of allocated
  integers
 */
#define ILIST_OVHD 2

#define ILIST_BASE(ils) ((ils)-ILIST_OVHD)
#define ILIST_LENGTH(ils) ((ils)[-1])
#define IABS(x) ((x)<0?(-x):(x))
#define ILIST_MAXLENGTHFIELD(ils) ((ils)[-2])
#define ILIST_MAXLENGTH(ils) (IABS(ILIST_MAXLENGTHFIELD(ils)))

/* Allocate a new ilist. */
ilist ilist_new(int max_length) {
    if (max_length == 0)
	max_length++;
    int *p = calloc(max_length + ILIST_OVHD, sizeof(int));
    if (p == NULL)
	err_printf("ilist_new", "Failed to allocate ilist of length %d\n", max_length);
    ilist result = p+ILIST_OVHD;
    ILIST_LENGTH(result) = 0;
    ILIST_MAXLENGTHFIELD(result) = -max_length;
    return result;
}

/* Free allocated ilist.  Will only free ones allocated via ilist_new */
void ilist_free(ilist ils) {
    if (!ils)
	return;
    if (ILIST_MAXLENGTHFIELD(ils) < 0) {
	int *p = ILIST_BASE(ils);
	free(p);
    }
}

/* Return number of elements in ilist */
int ilist_length(ilist ils) {
    return ILIST_LENGTH(ils);
}

/*
  Change size of ilist.  Can be shorter or longer than current.
  When lengthening, new contents are undefined
*/
ilist ilist_resize(ilist ils, int nlength) {
    int list_max_length = ILIST_MAXLENGTHFIELD(ils);
    int true_max_length = IABS(list_max_length);
    if (nlength > true_max_length) {
	if (list_max_length < 0) {
	    int *p = ILIST_BASE(ils);
	    int old_tml = true_max_length;
	    /* Dynamically resize */
	    true_max_length = (int) (true_max_length * GROW_RATIO);
	    if (nlength > true_max_length)
		true_max_length = nlength;
	    p = realloc(p, (true_max_length + ILIST_OVHD) * sizeof(int));
	    if (p == NULL)
		err_printf(__cfunc__, "Failed to grow ilist allocation from %d to %d\n",
			old_tml, true_max_length);
	    ils = p+ILIST_OVHD;
	    ILIST_MAXLENGTHFIELD(ils) = -true_max_length;
	} else 
	    /* Need to throw an error here */
	    err_printf(__cfunc__, "Cannot resize static ilist beyond initial allocation %d", true_max_length);
    }
    ILIST_LENGTH(ils) = nlength;
    return ils;
}

/*
  Add new value(s) to end of ilist.
  For dynamic ilists, the value of the pointer may change
*/
ilist ilist_push(ilist ils, int val) {
    int length = ILIST_LENGTH(ils);
    int nlength = length+1;
    ils = ilist_resize(ils, nlength);
    if (!ils)
	/* Want to throw an exception here */
	err_printf(__cfunc__, "Couldn't allocate space for list of length %d", nlength);
    ils[length] = val;
    ILIST_LENGTH(ils) = nlength;
    return ils;
}

/*
  Sort integers in ascending order
 */
int int_compare_ilist(const void *i1p, const void *i2p) {
    int i1 = *(int *) i1p;
    int i2 = *(int *) i2p;
    if (i1 < i2)
	return -1;
    if (i1 > i2)
	return 1;
    return 0;
}

/*
  Put elements of ilist into ascending order
 */
void ilist_sort(ilist ils) {
    qsort((void *) ils, ilist_length(ils), sizeof(int), int_compare_ilist);
}

/*
  Print elements of an ilist separated by sep
 */
int ilist_print(ilist ils, FILE *out, const char *sep) {
    int i;
    int rval = 0;
    const char *space = "";
    if (ils == NULL) {
	rval = fprintf(out, "NULL");
	return rval;
    }
    for (i = 0; i < ilist_length(ils); i++) {
	int pval = fprintf(out, "%s%d", space, ils[i]);
	if (pval < 0)
	    return pval;
	rval += pval;
	space = sep;
    }
    return rval;
}

/*
  Print elements of an ilist separated by sep.  Return number of characters written
 */
int ilist_format(ilist ils, char *out, const char *sep, int maxlen) {
    int i;
    const char *space = "";
    int len = 0;
    for (i = 0; i < ilist_length(ils); i++) {
	if (len >= maxlen)
	    break;
	int xlen = snprintf(out+len, maxlen-len, "%s%d", space, ils[i]);
	len += xlen;
	space = sep;
    }
    out[len] = '\0';
    return len;
}



/* Check for duplicates from sorted ilist */
/* If duplicate found, set *dup_valp */
bool ilist_find_duplicate(ilist ils, int *dup_valp) {
    if (ilist_length(ils) <= 1)
	return false;
    int len = ilist_length(ils);
    int i;
    for (i = 1; i < len; i++) {
	if (ils[i-1] == ils[i]) {
	    *dup_valp = ils[i];
	    return true;
	}
    }
    return false;
}

/* Remove duplicates from sorted ilist */
/* May or may not create copy */
ilist ilist_deduplicate(ilist ils) {
    if (ilist_length(ils) <= 1)
	return ils;
    int next_pos = 1;
    int last_val = ils[0];
    int i;
    int len = ilist_length(ils);
    for (i = 1; i < len; i++) {
	int val = ils[i];
	if (val != last_val)
	    last_val = ils[next_pos++] = val;
    }
    return ilist_resize(ils, next_pos);
}

/****************************
Integer Sets.  Extend ilist by listing all members in ascending order
*****************************/
/*
  Test whether value is member of list
*/

#if 0
// Deprecate
bool ilist_is_member(ilist ils, int val) {
    int i;
    int len = ilist_length(ils);
    for (i = 0; i < len; i++) {
	int lval = ils[i];
	if (val == lval)
	    return true;
	if (val < lval)
	    return false;
    }
    return false;
}

bool ilist_is_member_sorted(ilist ils, int val) {
    /* Binary search */
    /* Invariant: value between left and right */
    int left = 0;
    int right = ilist_length(ils)-1;
    while (left <= right) {
	int mid = (left+right)/2;
	int vm = ils[mid];
	if (vm == val)
	    return true;
	if (if val < vm)
	    right = mid-1;
	else
	    left = mid+1;
    }
    return false;
}
#endif

/* Test whether disjoint.  If find common element, then set *dup_val */
bool ilist_is_disjoint(ilist ils1, ilist ils2, int *dup_val) {
    int i1 = 0;
    int i2 = 0;
    int n1 = ilist_length(ils1);
    int n2 = ilist_length(ils2);
    while (i1 < n1 && i2 < n2) {
	int v1 = ils1[i1];
	int v2 = ils2[i2];
	if (v1 == v2) {
	    *dup_val = v1;
	    return false;
	}
	if (v1 < v2) 
	    i1++;
	else
	    i2++;
    }
    return true;
}

#if 0
// Deprecate
/* First list may not be sorted */
bool ilist_is_disjoint_unsorted(ilist ils1, ilist ils2) {
    int i;
    int len1 = ilist_length(ils1);
    for (i = 0; i < len1; i++)
	if (ilist_is_member(ils2, ils1[i]))
	    return false;
    return true;
}
#endif


ilist ilist_union(ilist ils1, ilist ils2) {
    int i1 = 0;
    int i2 = 0;
    int n1 = ilist_length(ils1);
    int n2 = ilist_length(ils2);
    ilist rls = ilist_new(n1 < n2 ? n2 : n1);
    while (i1 < n1 && i2 < n2) {
	int v1 = ils1[i1];
	int v2 = ils2[i2];
	if (v1 < v2) {
	    rls = ilist_push(rls, v1);
	    i1++;
	} else if (v2 < v1) {
	    rls = ilist_push(rls, v2);
	    i2++;
	} else {
	    rls = ilist_push(rls, v1);
	    i1++; i2++;
	}
    }
    while (i1 < n1) {
	int v1 = ils1[i1++];
	rls = ilist_push(rls, v1);
    }
    while (i2 < n2) {
	int v2 = ils2[i2++];
	rls = ilist_push(rls, v2);
    }
    return rls;
}

/*============================================
  Set of literals for performing unit propagation
============================================*/

/*
  Represent set of literals as array indexed by variable.
  Maintain counter "lset_generation"
  Entry +lset_generation indicates positive literal
  Entry -lset_generation indicates negative literal
  Any entry with value < |lset_generation| indicates neither literal in set
 */

int lset_generation = 0;
int *lset_array = NULL;
size_t lset_asize = 0;

void lset_init(int var) {
    lset_asize = MIN_SIZE;
    if (var > lset_asize)
	lset_asize = var;
    lset_array = calloc(lset_asize, sizeof(int));
    if (lset_array == NULL)
	err_printf(__cfunc__, "Couldn't allocate initial literal array of size %zd\n", lset_asize);
    lset_generation = 1;
}

void lset_clear() {
    lset_generation++;
    if (lset_generation < 0) {
	int var;
	for (var = 1; var <= lset_asize; var++) 
	    lset_array[var-1] = 0;
	lset_generation = 1;
    }
}

void lset_check_size(int var) {
    if (var <= lset_asize)
	return;
    if (lset_asize == 0) {
	lset_init(var);
	return;
    }
    size_t nasize = (size_t) (lset_asize * GROW_RATIO);
    if (nasize < var)
	nasize = var;
    lset_array = realloc(lset_array, nasize * sizeof(int));
    info_printf(3, "Resizing lset array %zd --> %zd\n", lset_asize, nasize);
    if (lset_array == NULL)
	err_printf(__cfunc__, "Couldn't grow literal array size to %zd\n", nasize);
    int nvar;
    for (nvar = lset_asize+1; nvar <= nasize; nvar++)
	lset_array[nvar-1] = 0;
    lset_asize = nasize;
}

int lset_get_lit(int var) {
    if (var <= 0 || var > lset_asize)
	return 0;
    int g = lset_array[var-1];
    if (g == lset_generation)
	return var;
    if (g == -lset_generation)
	return -var;
    return 0;
}

/* Attempt to add literal to set.  Return false if already have opposite literal */
bool lset_add_lit(int lit) {
    int var = IABS(lit);
    lset_check_size(var);
    int olit = lset_get_lit(var);
    if (olit != 0 && olit != lit)
	return false;
    int val = lit > 0 ? lset_generation : -lset_generation;
    lset_array[var-1] = val;
    return true;
}

void lset_show(FILE *out) {
    int var;
    fprintf(out, "[");
    bool first = true;
    for (var = 1; var <= lset_asize; var++) {
	int lit = lset_get_lit(var);
	if (lit == 0)
	    continue;
	if (first)
	    fprintf(out, "%d", lit);
	else
	    fprintf(out, ", %d", lit);
	first = false;
    }
    fprintf(out, "]");
}

/*============================================
  Clause types
============================================*/

typedef enum {CLAUSE_INPUT, CLAUSE_TSEITIN, CLAUSE_DISABLE, CLAUSE_SKOLEM, CLAUSE_STRUCTURAL,
	      CLAUSE_ROOT, CLAUSE_FORWARD, CLAUSE_UNKNOWN, CLAUSE_INVALID, CLAUSE_COUNT } clause_type_t;

char *clause_type_names[CLAUSE_COUNT] = { "input", "tseitin", "disable", "skolem", "structural",
					 "root", "forward", "unknown", "invalid" };

static const char* clause_type_name(clause_type_t type) {
    if (type < 0 || type > CLAUSE_UNKNOWN)
	return clause_type_names[(int) CLAUSE_INVALID];
    return clause_type_names[(int) type];
}


/*============================================
  Processing Input
============================================*/

typedef enum {TOK_INT, TOK_STRING, TOK_STAR, TOK_EOF, TOK_EOL, TOK_NONE, TOK_UNKNOWN} token_t;

char *token_name[7] = { "integer", "string", "star", "EOF", "EOL", "NONE", "UNKNOWN" };

#define TOKEN_MAX 100
char token_last[TOKEN_MAX];
int token_value = 0;
FILE *token_file = NULL;
int token_pos = 0;

void token_setup(char *fname) {
    token_file = fopen(fname, "r");
    current_file = strdup(fname);
    if (token_file == NULL)
	err_printf(__cfunc__, "Couldn't open file '%s'\n", fname);
    line_count = 0;
}

void token_finish() {
    fclose(token_file);
    token_file = NULL;
}

bool skip_space() {
    int c;
    do
	c = fgetc(token_file);
    while (c != '\n' && c != EOF && isspace(c));
    if (c == EOF || c == '\n')
	return false;
    ungetc(c, token_file);
    return true;
}

token_t token_next() {
    int sign = 1;
    int mag = 0;
    token_t ttype = TOK_NONE;
    token_pos = 0;
    token_last[token_pos] = '\0';
    token_value = 0;
    int c;
    bool done = false;
    while (!done) {
	c = fgetc(token_file);
	if (c == EOF) {
	    ttype = TOK_EOF;
	    done = true;
	} else  if (c == '\n') {
	    line_count ++;
	    ttype = TOK_EOL;
	    done = true;
	} else if (!isspace(c)) {
	    ungetc(c, token_file);
	    break;
	}
    }

    while (!done) {
	if (token_pos >= TOKEN_MAX-1) {
	    ttype = TOK_UNKNOWN;
	    done = true;
	}
	c = fgetc(token_file);
	if (c == '-') {
	    if (ttype != TOK_NONE) {
		ttype = TOK_UNKNOWN;
		done = true;
	    } else {
		sign = -sign;
		ttype = TOK_INT;
		token_last[token_pos++] = c;
		token_last[token_pos] = '\0';
	    }
	} else if (isdigit(c)) {
	    if (ttype != TOK_NONE && ttype != TOK_INT) {
		ttype =  TOK_UNKNOWN;
		done = true;
	    } else {
		ttype = TOK_INT;
		mag = 10 * mag + (c - '0');
		token_last[token_pos++] = c;
		token_last[token_pos] = '\0';
		token_value = sign * mag;
	    }
	} else if (isspace(c) || c == EOF) {
	    if (c == '\n') {
		ungetc(c, token_file);
	    }
	    done = true;
	} else if (c == '*') {
	    if (ttype != TOK_NONE) {
		ttype = TOK_UNKNOWN;
		done = true;
	    } else {
		token_last[token_pos++] = c;
		token_last[token_pos] = '\0';
		ttype = TOK_STAR;
	    }
	} else {
	    if (ttype != TOK_NONE && ttype != TOK_STRING) {
		ttype = TOK_UNKNOWN;
		done = true;
	    } else {
		ttype = TOK_STRING;
		token_last[token_pos++] = c;
		token_last[token_pos] = '\0';
	    }
	}
    }
    info_printf(4, "Read token.  Token = '%s'.  Type = %s\n", token_last, token_name[ttype]);
    return ttype;
}

void token_confirm_eol() {
    /* Done */
    token_t token = token_next();
    if (token != TOK_EOL)
	err_printf(__cfunc__, "Expected end of line.  Got %s ('%s') instead\n", token_name[token], token_last);
}

void token_find_eol() {
    int c;
    while (true) {
	c = fgetc(token_file);
	if (c == EOF)
	    return;
	if (c == '\n') {
	    line_count ++;
	    return;
	}
    }
}

/*============================================
  Core data structures
============================================*/

/* 
   Maintain set of all clauses as set of chunks.  Within a chunk,
   clauses are organized as zero-terminated sequences of int's.  A
   clause does not break across chunks
*/

/*
  Fixed array containing pointers to all chunks.  Individual chunks
  are allocated dynamically.
*/
int *chunk_set[CHUNK_MAX];

/* How many chunks have been allocated? */
int chunk_count = 0;

/* How much of the current chunk has been used */
int chunk_used = 0;

/* Tracking clauses */
int clause_count = 0;
int clause_last_id = 0;

// Working area for creating a new clause
ilist current_clause = NULL;

/*
  Assume that clauses come in consecutively numbered blocks, but with gaps between them
  Maintain as array of blocks
 */

typedef struct {
    int start_id;  // Clause ID of initial entry
    int length;    // Number of (possibly null) clauses in block
    ilist chunk;   // Sequence of chunk IDs (numbered from 0)
    ilist offset;  // Sequence of clause offsets within chunk
    ilist type;    // Sequence of clause types
} clause_block_t;

clause_block_t *clause_blocks = NULL;
int clause_block_alloc = 0;
int clause_block_count = 0;

/* Operations */
void clause_init() {
    /* Allocate a single starting chunk */
    chunk_set[chunk_count] = calloc(CHUNK_SIZE, sizeof(int));
    if (chunk_set[chunk_count] == NULL)
	err_printf(__cfunc__, "Couldn't allocate space for clause chunk %d\n", chunk_count);	
    chunk_count++;
    current_clause = ilist_new(0);
    clause_block_alloc = 10;
    clause_blocks = calloc(clause_block_alloc, sizeof(clause_block_t));
    if (clause_blocks == NULL)
	err_printf(__cfunc__, "Couldn't allocate space for clause blocks\n");	
    clause_block_count = 1;
    clause_blocks[clause_block_count-1].start_id = 1;
    clause_blocks[clause_block_count-1].length = 0;
    clause_blocks[clause_block_count-1].chunk = ilist_new(MIN_SIZE);
    clause_blocks[clause_block_count-1].offset = ilist_new(MIN_SIZE);
    clause_blocks[clause_block_count-1].type = ilist_new(MIN_SIZE);
}

/* Info to quickly locate clause */
typedef struct {
    int bid;
    int pos;
} clause_location_t;

/* Identify location of clause */
bool find_clause(int cid, clause_location_t *loc) {
    int bid = -1;
    int pos = 0;
    /* Ensure that lid <= bid <= rid */
    int lid = 0;
    int rid = clause_block_count - 1;
    while (lid <= rid) {
	bid = (lid + rid)/2;
	pos = cid - clause_blocks[bid].start_id;
	if (pos < 0)
	    rid = bid-1;
	else if (pos >= clause_blocks[bid].length)
	    lid = bid+1;
	else {
	    loc->bid = bid;
	    loc->pos = pos;
	    return true;
	}
    }
    return false;
}

bool goto_next_clause(clause_location_t *loc) {
    int bid = loc->bid;
    int pos = loc->pos;
    if (pos+1 < clause_blocks[bid].length) {
	loc->pos = pos+1;
	return true;
    }
    if (bid+1 < clause_block_count) {
	loc->bid = bid+1;
	loc->pos = 0;
	return true;
    }
    return false;
}

int generate_clause_id(clause_location_t *loc) {
    return clause_blocks[loc->bid].start_id + loc->pos;
}

/* Return pointer to beginning of any existing clause */
int *clause_locate(clause_location_t *loc) {
    int bid = loc->bid;
    int pos = loc->pos;
    int chunk = clause_blocks[bid].chunk[pos];
    if (chunk < 0)
	return NULL;
    int offset = clause_blocks[bid].offset[pos];
    if (offset < 0)
	return NULL;
    return chunk_set[chunk] + offset;
}

/* Return clause type */
clause_type_t clause_type(clause_location_t *loc) {
    int bid = loc->bid;
    int pos = loc->pos;
    return (clause_type_t) clause_blocks[bid].type[pos];
}

/* Deallocate clause data structures */
void clause_free_noninput() {
    int bid, chunk;
    clause_location_t location;
    if (!find_clause(input_clause_count, &location))
	return;
    int last_input_chunk = clause_blocks[location.bid].chunk[location.pos];
    /* Deallocate chunks beyond those used for input clauses */
    for (chunk = last_input_chunk + 1; chunk < chunk_count; chunk++)
	free(chunk_set[chunk]);
    /* Deallocate blocks beyond those used for input */
    for (bid = location.bid+1; bid < clause_block_count; bid++) {
	ilist_free(clause_blocks[bid].chunk);
	ilist_free(clause_blocks[bid].offset);
	ilist_free(clause_blocks[bid].type);
    }
    ilist_free(current_clause);
    data_printf(1, "Freed %d/%d chunks and %d/%d blocks\n", 
		chunk_count-last_input_chunk-1, chunk_count,
		clause_block_count-location.bid-1, clause_block_count);
}

bool clause_delete(clause_location_t *loc) {
    int bid = loc->bid;
    int pos = loc->pos;
    int chunk = clause_blocks[bid].chunk[pos];
    int offset = clause_blocks[bid].offset[pos];
    bool deleting = offset >= 0;
    if (deleting) {
	int *litp = chunk_set[chunk] + offset;
	int lit;
	while ((lit = *litp++) != 0) {
	    int var = IABS(lit);
	    if (var > input_variable_count) {
		if (var > variable_limit)
		    err_printf(__cfunc__, "Deleting clause with literal %d.  Exceeds variable limit of %d\n", lit, variable_limit);
	    }
	}
	clause_blocks[bid].type[pos] = CLAUSE_UNKNOWN;
    } else {
	int cid = generate_clause_id(loc);
	err_printf(__cfunc__, "Can't delete clause %d.  bid = %d, pos = %d, chunk = %d, offset = %d\n",
		   cid, bid, pos, chunk, offset);
    }
    return deleting;
}

void start_clause(int cid) {
    clause_location_t location;
    if (cid <= clause_last_id)
	err_printf(__cfunc__, "Can't add clause %d.  Already added same or higher-numbered clause %d\n", cid, clause_last_id);
    if (cid > clause_last_id + MAX_GAP || clause_block_count == 1 && cid > input_clause_count) {
	/* Start new block */
	if (clause_block_count == clause_block_alloc) {
	    /* Need more blocks */
	    clause_block_alloc = (int) (clause_block_alloc * GROW_RATIO);
	    clause_blocks = realloc(clause_blocks, clause_block_alloc * sizeof(clause_block_t));
	    if (clause_blocks == NULL)
		err_printf(__cfunc__, "Failed to add enough clause blocks for %d blocks\n", clause_block_alloc);
	}
	clause_block_count++;
	info_printf(2, "Starting clause block %d\n", clause_block_count);
	clause_blocks[clause_block_count-1].start_id = cid;
	clause_blocks[clause_block_count-1].length = 0;
	clause_blocks[clause_block_count-1].chunk = ilist_new(MIN_SIZE);
	clause_blocks[clause_block_count-1].offset = ilist_new(MIN_SIZE);
	clause_blocks[clause_block_count-1].type = ilist_new(MIN_SIZE);
    } else {
	/* Fill in with null clauses */
	int ncid;
	for (ncid = clause_last_id+1; ncid < cid; ncid++) {
	    clause_blocks[clause_block_count-1].chunk = ilist_push(clause_blocks[clause_block_count-1].chunk, -1);
	    clause_blocks[clause_block_count-1].offset = ilist_push(clause_blocks[clause_block_count-1].offset, -1);
	    clause_blocks[clause_block_count-1].type = ilist_push(clause_blocks[clause_block_count-1].type, (int) CLAUSE_UNKNOWN);
	    clause_blocks[clause_block_count-1].length ++;
	}
    }
    clause_last_id = cid;
    clause_count ++;
    current_clause = ilist_resize(current_clause, 0);
    info_printf(3, "Starting clause %d\n", cid);
}

/* Save the current clause */
void finish_clause(int cid, clause_type_t type) {
    long int need = ilist_length(current_clause);
    if (need > CHUNK_SIZE) {
	err_printf("finish_clause", "Attempt to save clause of length %d.  Max allowed length = %d\n", ilist_length(current_clause), CHUNK_SIZE);
	exit(1);
    }
    if (need + chunk_used > CHUNK_SIZE) {
	// Must start new chunk
	if (chunk_count >= CHUNK_MAX-1)
	    err_printf(__cfunc__, "Reached maximum of %d chunks\n", CHUNK_MAX);	
	chunk_set[chunk_count] = calloc(CHUNK_SIZE, sizeof(int));
	if (chunk_set[chunk_count] == NULL)
	    err_printf(__cfunc__, "Couldn't allocate space for clause chunk %d\n", chunk_count);	
	chunk_count++;
	chunk_used = 0;
    }
    int pos = chunk_used;
    memcpy(chunk_set[chunk_count-1] + chunk_used, current_clause, ilist_length(current_clause) * sizeof(int));
    chunk_used += ilist_length(current_clause);
    // Record clause position
    clause_blocks[clause_block_count-1].chunk = ilist_push(clause_blocks[clause_block_count-1].chunk, chunk_count-1);
    clause_blocks[clause_block_count-1].offset = ilist_push(clause_blocks[clause_block_count-1].offset, pos);
    clause_blocks[clause_block_count-1].type = ilist_push(clause_blocks[clause_block_count-1].type, type);
    clause_blocks[clause_block_count-1].length ++;
    info_printf(3, "Finished clause.  Full length %d.  Chunk ID %d.  Offset %d. ", need, chunk_count-1, pos, clause_type_name(type));
    if (verb_level >= 3) 
	clause_show(stdout, cid, true);
}

/* Add either literal or terminating 0 to current clause */
void clause_add_literal(int lit) { 
    current_clause = ilist_push(current_clause, lit);
    int var = IABS(lit);
    if (var > input_variable_count) {
	if (var > variable_limit)
	    err_printf(__cfunc__, "Adding clause with literal %d.  Exceeds variable limit of %d\n", lit, variable_limit);
    }
}

bool clause_is_unit(int *lits) {
    /* Can have multiple repetitions of single literal */
    if (lits == NULL || lits[0] == 0)
	return false;
    int lit = lits[0];
    int i;
    for (i = 1; lits[i] == lit; i++)
	;
    return lits[i] == 0;
}

void clause_show(FILE *out, int cid, bool endline) {
    clause_location_t location;
    if (!find_clause(cid, &location))
	fprintf(out, "** Cannot locate clause #%d **", cid);
    clause_type_t type = clause_type(&location);
    fprintf(out, "%d(%s):", cid, clause_type_name(type));
    if (type != CLAUSE_UNKNOWN) {
	int *litp = clause_locate(&location);
	while (*litp != 0) {
	    fprintf(out, " %d", *litp);
	    litp++;
	}
    }
    if (endline)
	fprintf(out, "\n");
}

void clause_show_all(FILE *out) {
    clause_location_t location;
    bool ok = find_clause(1, &location);
    while (ok) {
	int cid = generate_clause_id(&location);
	clause_show(out, cid, true);
	ok = goto_next_clause(&location);
    }
}

/*============================================
  RUP
============================================*/

#define RUP_CONFLICT INT_MAX
#define RUP_STALL 0

/* Initialize lset to complement of literals */
/* Return false if encounter conflict */
bool rup_setup(int *lits) {
    lset_clear();
    int lit;
    while ((lit = *lits) != 0) {
	if (!lset_add_lit(-lit))
	    return false;
	lits++;
    }
    return true;
}

bool rup_add_unit(int lit) {
    return lset_add_lit(lit);
}

int rup_unit_prop(clause_location_t *loc) {
    int *lits = clause_locate(loc);
    int unit = RUP_CONFLICT;
    int lit;
    while ((lit = *lits) != 0) {
	lits++;
	if (lit == unit) 
	    /* Repeated unit literal */
	    continue;
	int var = IABS(lit);
	int rlit = lset_get_lit(var);
	if (rlit == lit)
	    return RUP_STALL;
	else if (rlit == -lit)
	    continue;
	else if (unit == RUP_CONFLICT)
	    unit = lit;
	else
	    return RUP_STALL;
    }
    return unit;
}

/* 
   Run RUP on hints from file.
   Assume already set up.
   Checks whether hints suitable for target clause type
 */
void rup_run(int tcid, clause_type_t target_type) {
    bool conflict = false;
    bool ok = true;
    int steps = 0;
    while (true) {
	token_t token = token_next();
	if (token == TOK_STAR)
	    err_printf(__cfunc__, "This checker requires explicit hints\n");
	else if (token != TOK_INT)
	    err_printf(__cfunc__, "RUP for clause %d.  Expecting integer hint.  Got %s ('%s') instead\n", tcid, token_name[token], token_last);
	else if (token_value == 0) {
	    if (!conflict) {
		fprintf(ERROUT, "FAILURE: RUP failure for clause %d.  Didn't have conflict on final clause\n", tcid);
		if (verb_level >= 2) {
		    fprintf(ERROUT, "    Added literals: ");
		    lset_show(ERROUT);
		    fprintf(ERROUT, "\n");
		}
		err_printf(__cfunc__, "RUP failure for clause %d\n", tcid);
	    }
	    if (!ok)
		err_printf(__cfunc__, "RUP failure for clause %d.  Combination of target type and hint types not allowed\n", tcid);
	    else if (target_type == CLAUSE_STRUCTURAL) 
		info_printf(3, "RUP for mutex.  Succeeded in %d steps\n", steps);
	    else
		info_printf(3, "RUP for clause %d.  Succeeded in %d steps\n", tcid, steps);
	    return;
	} else {
	    if (conflict) {
		if (early_rup) {
		    while (token_value != 0) {
			token = token_next();
			if (token != TOK_INT)
			    err_printf(__cfunc__, "RUP for clause %d.  Expecting integer hint.  Got %s ('%s') instead\n", tcid, token_name[token], token_last);
		    }
		    if (!ok)
			err_printf(__cfunc__, "RUP failure for clause %d.  Combination of target type and hint types not allowed\n", tcid);
		    else
			info_printf(3, "RUP for clause %d.  Succeeded in %d steps\n", tcid, steps);
		    return;
		} else
		    err_printf(__cfunc__, 
			       "RUP failure for clause %d.  Encountered conflict after processing %d hints.  Not at end of hint list\n", tcid, steps);
	    }
	    int cid = token_value;
	    clause_location_t location;
	    if (!find_clause(cid, &location))
		err_printf(__cfunc__,
			   "RUP failure for clause %d.  Encountered invalid hint clause %d\n", tcid, cid);
	    clause_type_t htype = clause_type(&location);
	    info_printf(4, "Target clause %d (type %s) Hint clause %d, type = %s, last  ok = %s .. ",
			tcid, clause_type_name(target_type), cid, clause_type_name(htype), ok ? "true" : "false");
	    switch (htype) {
	    case CLAUSE_TSEITIN:
		break;
	    case CLAUSE_FORWARD:
		ok = ok && (target_type == CLAUSE_FORWARD || target_type == CLAUSE_ROOT);
		break;
	    case CLAUSE_INPUT:
		ok = ok && (target_type == CLAUSE_FORWARD || target_type == CLAUSE_ROOT || target_type == CLAUSE_INPUT);
		break;
	    case CLAUSE_SKOLEM:
	    case CLAUSE_ROOT:
		ok = ok && target_type == CLAUSE_INPUT;
		break;
	    case CLAUSE_STRUCTURAL:
	    case CLAUSE_DISABLE:
		ok = ok && (target_type == CLAUSE_FORWARD || target_type == CLAUSE_ROOT || target_type == CLAUSE_STRUCTURAL);
		break;
	    default:
		ok = false;
		break;
	    }
	    info_printf(4, "New  ok = %s\n", ok ? "true" : "false");
	    int unit = rup_unit_prop(&location);
	    steps ++;
	    if (unit == RUP_CONFLICT)
		conflict = true;
	    else if (unit == RUP_STALL) {
		if (skipping_rup)
			info_printf(2, "Warning.  No unit propagation by hint clause %d in RUP for clause %d\n", cid, tcid);
		else {
		    fprintf(ERROUT, "RUP failure for clause %d. Hint clause %d did not cause unit propagation\n", tcid, cid);
		    if (verb_level >= 2) {
			fprintf(ERROUT, "    Added literals: ");
			lset_show(ERROUT);
			fprintf(ERROUT, "\n    Hint Clause ");
			clause_show(ERROUT, cid, true);
		    }
		    err_printf(__cfunc__, "RUP failure for clause %d\n", tcid);
		}
	    } else
		lset_add_lit(unit);
	}
    }
    if (!ok)
	err_printf(__cfunc__, "RUP failure for clause %d.  Combination of target type and hint types not allowed\n", tcid);
    return;
}

/* Skip over RUP hints in file.  Assume already set up  */
void rup_skip(int tcid) {
    while (true) {
	token_t token = token_next();
	if (token == TOK_STAR)
	    continue;
	else if (token != TOK_INT)
	    continue;
	else if (token_value == 0)
	    return;
    }
}

/*============================================
  Processing files
============================================*/

/* Look for pmc or pwmc declaration.  Parse list of show variables */
void process_comment() {
    token_t token = token_next();
    if (token != TOK_STRING)
	goto done;
    if (strcmp(token_last, "t") == 0) {
	token = token_next();
	if (token != TOK_STRING)
	    goto done;
	if (strcmp(token_last, "pmc") == 0 || strcmp(token_last, "pwmc") == 0) {
	    data_printf(3, "Performing projected knowledge compilation\n");
	    is_pkc = true;
	}
	goto done;
    } else if (is_pkc && strcmp(token_last, "p") == 0) {
	token = token_next();
	if (token != TOK_STRING || strcmp(token_last, "show") != 0)
	    goto done;
	show_variables = calloc(input_variable_count, sizeof(bool));
	show_variables_size = input_variable_count;
	if (show_variables == NULL)
	    err_printf("process_comment", "Failed to allocate space for show variables\n");
	/* Parse show variables */
	while (true) {
	    token = token_next();
	    if (token == TOK_EOL)
		err_printf("process_comment", "List of show variables not terminated by '0'\n");
	    if (token != TOK_INT)
		err_printf("process_comment", "Couldn't parse list of show variables\n");
	    int v = token_value;
	    if (v == 0) {
		data_printf(3, "Found show variables\n");
		goto done;
	    }
	    if (v <= 0)
		err_printf("process_comment", "Invalid variable ID %d\n", v);
	    if (v > show_variables_size) {
		if (input_variable_count > 0)
		    err_printf("process_comment", "Invalid variable ID %d.  Have declare total of %d input variables\n",
			       v, input_variable_count);
		show_variables_size = v;
		show_variables = realloc(show_variables, show_variables_size * sizeof(bool));
		if (!show_variables)
		    err_printf("process_comment", "Couldn't allocate memory for %d show variables\n", show_variables_size);
	    }
	    show_variables[v-1] = true;
	}
    }
 done:
    if (token != TOK_EOL)
	token_find_eol();
}

void cnf_read(char *fname) {
    token_setup(fname);
    clause_init();
    /* Find and parse header */
    while (true) {
	token_t token = token_next();
	if (token == TOK_EOL)
	    continue;
	if (token != TOK_STRING)
	    err_printf(__cfunc__, "Unexpected token %s ('%s') while looking for CNF header\n", token_name[token], token_last);
	if (token_last[0] == 'c')
	    process_comment();
	else if (token_last[0] == 'p') {
	    if (token_last[1] != '\0')
		err_printf(__cfunc__, "Invalid CNF field %s ('%s')\n", token_name[token], token_last);
	    token = token_next();
	    if (strcmp(token_last, "cnf") != 0)
		err_printf(__cfunc__, "Expected field 'cnf'.  Got %s ('%s')\n", token_name[token], token_last);
	    token = token_next();
	    if (token != TOK_INT)
		err_printf(__cfunc__, "Invalid CNF variable count %s ('%s')\n", token_name[token], token_last);
	    input_variable_count = token_value;
	    variable_limit = input_variable_count;
	    if (show_variables_size > input_variable_count)
		err_printf(__cfunc__, "Invalid CNF variable count %d.  Have already declared %d as show variable\n", input_variable_count, show_variables_size);
	    if (show_variables_size < input_variable_count) {
		show_variables_size = input_variable_count;
		show_variables = realloc(show_variables, show_variables_size * sizeof(bool));
		if (!show_variables)
		    err_printf("process_comment", "Couldn't allocate memory for %d show variables\n", show_variables_size);
	    }
	    token = token_next();
	    if (token != TOK_INT)
		err_printf(__cfunc__, "Invalid CNF clause count %s ('%s')\n", token_name[token], token_last);
	    input_clause_count = token_value;
	    token = token_next();
	    if (token != TOK_EOL)
		err_printf(__cfunc__, "Invalid field in CNF header %s ('%s')\n", token_name[token], token_last);
	    break;
	} else
	    err_printf(__cfunc__, "Unexpected token %s ('%s') while reading CNF header\n", token_name[token], token_last);
    }
    /* Read clauses */
    int found_clause_count = 0;
    bool within_clause = false;
    int last_literal = INT_MAX;
    while (true) {
	token_t token = token_next();
	if (token == TOK_EOF)
	    break;
	else if (token == TOK_EOL)
	    continue;
	else if (token == TOK_STRING && token_last[0] == 'c')
	    process_comment();
	else if (token == TOK_EOL)
	    continue;
	else if (token == TOK_INT) {
	    if (!within_clause) {
		start_clause(found_clause_count+1);
		within_clause = true;
		last_literal = INT_MAX;
	    }
	    clause_add_literal(token_value);
	    last_literal = token_value;
	    if (token_value == 0) {
		found_clause_count ++;
		within_clause = false;
		finish_clause(found_clause_count, CLAUSE_INPUT);
	    }
	}
	else
	    err_printf(__cfunc__, "Unexpected token %s ('%s') found in CNF file\n", token_name[token], token_last);
    }
    if (found_clause_count != input_clause_count)
	err_printf(__cfunc__, "Invalid CNF.  Expected %d clauses.  Found %d\n", input_clause_count, found_clause_count);
    token_finish();
    /* When no show variables included, then default is that they all are */
    if (is_pkc) {
	if (show_variables == NULL) {
	    show_variables = calloc(input_variable_count, sizeof(bool));
	    if (show_variables == NULL)
		err_printf("process_comment", "Failed to allocate space for show variables\n");
	    for (int v = 1; v <= input_variable_count; v++)
		show_variables[v-1] = true;
	    data_printf(2, "No show variables declared.  Declaring all input variables to be show variables");
	}
    }
    data_printf(1, "Read CNF file with %d variables and %d clauses\n", input_variable_count, input_clause_count);
}

void cnf_show(FILE *out) {
    int cid;
    if (verb_level < 1)
	return;
    printf("CNF File.  %d clauses\n", input_clause_count);
    clause_show_all(out);
}

/*============================================
  POG data structures
============================================*/

typedef enum {NODE_PRODUCT, NODE_SKOLEM, NODE_SUM, NODE_NONE} node_type_t;

const char node_type_char[4] = {'P', 'T', 'S', 'N' };

/* Representation of POG node */
typedef struct {
    node_type_t type;
    int id;                 /* Node ID */
    int cid;                /* First defining clause ID */
    ilist dependency_list;  /* All variables in subgraph */
    ilist children;         /* Node IDs of children */
    q25_ptr ring_value;     /* For counting */
} node_t;

node_t *node_list = NULL;
int node_asize = 0;
int node_count = 0;

node_t *node_find(int id) {
    int idx = id - input_variable_count - 1;
    if (idx < 0 || idx >= node_asize)
	return NULL;
    return &node_list[idx];
}

node_t *node_new(node_type_t type, int id, int cid) {
    if (id <= input_variable_count)
	err_printf(__cfunc__, "Invalid operation id %d\n", id);
    if (id-input_variable_count > node_asize) {
	int nasize = id-input_variable_count;
	if (nasize < MIN_SIZE)
	    nasize = MIN_SIZE;
	if (nasize < (int) (GROW_RATIO * node_asize))
	    nasize = (int) (GROW_RATIO * node_asize);
	if (node_list == NULL)
	    node_list = calloc(nasize, sizeof(node_t));
	else
	    node_list = realloc(node_list, nasize * sizeof(node_t));
	if (node_list == NULL)
	    err_printf(__cfunc__, "Couldn't allocate space for node list of size %d\n", nasize);
	int idx;
	for (idx = node_asize; idx < nasize; idx++) {
	    int nid = idx + input_variable_count + 1;
	    node_list[idx].type = NODE_NONE;
	    node_list[idx].id = nid;
	    node_list[idx].cid = 0;
	    node_list[idx].dependency_list = NULL;
	    node_list[idx].children = NULL;
	}
	info_printf(3, "Resized node array %d --> %d\n", node_asize, nasize);
	node_asize = nasize;
	variable_limit = node_asize + input_variable_count;
    }
    node_t *node = node_find(id);
    if (node && node->type != NODE_NONE)
	err_printf(__cfunc__, "Cannot create new node with id %d.  Id already in use\n", id);
    node->type = type;
    node->cid = cid;
    node->ring_value = NULL;
    node_count ++;
    return node;
}

void cpog_show(FILE *out) {
    int cid;
    int idx, nid;
    printf("CPOG Operations\n");
    for (idx = 0; idx < node_asize; idx++) {
	nid = input_variable_count + 1 + idx;
	node_t *node = node_find(nid);
	if (node == NULL || node->type == NODE_NONE)
	    continue;
	fprintf(out, "%c%d: (", node_type_char[node->type], nid);
	ilist_print(node->children, out, ", ");
	fprintf(out, ")\n");
	int n = ilist_length(node->children);
	int i;
	for (i = 0; i <= n; i++) {
	    fprintf(out, "  ");
	    clause_show(out, node->cid + i, true);
	}
    }
}

/* Handlers for different command types.  Each starts after parsing command token */
void cpog_read_root() {
    token_t token = token_next();
    if (token != TOK_INT)
	err_printf(__cfunc__, "Unexpected token %s ('%s')\n", token_name[token], token_last);
    declared_root = token_value;
    if (token_value == 0) {
	declared_unsatisfiable = true;
	info_printf(3, "Formula declared to be unsatisfiable\n");
    } else
	info_printf(3, "Root literal declared as %d\n", declared_root);
}

void cpog_add_clause(int cid, bool is_structural) {
    lset_clear();
    start_clause(cid);
    int clen = 0;
    int last_literal = 0;
    while (true) {
	token_t token = token_next();
	if (token != TOK_INT)
	    err_printf(__cfunc__, "Unexpected token %s ('%s')\n", token_name[token], token_last);
	int lit = token_value;
	clause_add_literal(lit);
	if (lit == 0)
	    break;
	last_literal = lit;
	lset_add_lit(-lit);
	clen++;
    }
    clause_type_t ctype = CLAUSE_FORWARD;
    if (is_structural)
	ctype = CLAUSE_STRUCTURAL;
    else if (clen == 0)
	proved_unsatisfiable = true;
    else if (clen == 1 && last_literal == declared_root) {
	ctype = CLAUSE_ROOT;
	root_clause_added = true;
    }
    if (!check_add)
	rup_skip(cid);
    else
	rup_run(cid, ctype);
    token_confirm_eol();
    finish_clause(cid, ctype);
    if (ctype == CLAUSE_FORWARD)
	cpog_forward_count++;
    else if (ctype == CLAUSE_STRUCTURAL)
	cpog_structural_count++;
    info_printf(3, "Processed clause %d addition.  Type = %s\n", cid, clause_type_name(ctype));
}

void cpog_delete_clause() {
    token_t token = token_next();
    if (token != TOK_INT)
	err_printf(__cfunc__, "Unexpected token %s ('%s')\n", token_name[token], token_last);
    int cid = token_value;
    if (cid > input_clause_count)
	err_printf(__cfunc__, "Cannot delete clause #%d.  Can only delete input clauses\n", cid);
    clause_location_t location;
    if (!find_clause(cid, &location))
	err_printf(__cfunc__, "Could not delete clause %d.  Never defined\n", cid);
    int *lits = clause_locate(&location);
    bool tautology = !rup_setup(lits);
    bool deleted = clause_delete(&location);
    if (!deleted) 
	err_printf(__cfunc__, "Could not delete clause %d.  Never defined or already deleted\n", cid);
    if (!tautology) {
	if (!check_delete)
	    rup_skip(cid);
	else
	    rup_run(cid, CLAUSE_INPUT);
    }
    token_find_eol();
    explicit_deletion_count++;
    info_printf(3, "Processed input clause %d deletion\n", cid);
}

/*============================================
  Support for reverse implication
============================================*/

/* Event processing data structures */

/* Map from negated literals to all POG node IDs for which they are arguments */
ilist *neg_fanouts = NULL;
/* Map from positive literals to all POG node IDs for which they are arguments */
ilist *pos_fanouts = NULL;

/* Data structures used for unit propagation */
typedef struct {
    // Counter for each node.  Max value = 2
    unsigned char *node_event_count;
    // Queue structured as heap
    int *priority_queue;
    // size of queue
    int priority_count;
    // Counters
    int implicit_deletion_count;
    long event_count;
} propagate_t;

propagate_t *new_propagator() {
    propagate_t *prop = malloc(sizeof(propagate_t));
    if (!prop) {
	err_printf(__cfunc__, "Couldn't allocate propagator\n");
    }
    prop->priority_count = 0;
    prop->implicit_deletion_count = 0;
    prop->event_count = 0;
    prop->priority_queue = calloc(node_count, sizeof(int));
    prop->node_event_count = calloc(node_count, sizeof(unsigned char));
    if (!prop->priority_queue || !prop->node_event_count)
	err_printf(__cfunc__, "Couldn't allocate propagator\n");
    return prop;
}

void free_propagator(propagate_t *prop) {
    free(prop->priority_queue);
    free(prop->node_event_count); 
    free(prop);
}

void reset_propagator(propagate_t *prop) {
    /* Keep counters, but clear priority queue */
    prop->priority_count = 0;
}

/* Counter can saturate at 2 */
int plusplus_max2(unsigned char *p) {
    int rval = *p;
    if (rval < 2)
	(*p)++;
    return rval;
}

int var_to_index(int var) {
    return var - input_variable_count;
}

int index_to_var(int index) {
    return index + input_variable_count;
}

void  build_deletion_structures() {
    neg_fanouts = (ilist *) calloc(input_variable_count, sizeof(ilist));
    pos_fanouts = (ilist *) calloc(declared_root, sizeof(ilist));
    int i;
    for (i = 0; i < input_variable_count; i++)
	neg_fanouts[i] = ilist_new(0);
    for (i = 0; i < declared_root; i++)
	pos_fanouts[i] = ilist_new(0);
    int idx;
    for (idx = 0; idx < node_count; idx++) {
	node_type_t type = node_list[idx].type;
	if (type == NODE_NONE)
	    continue;
	ilist children = node_list[idx].children;
	int id = node_list[idx].id;
	int len = ilist_length(children);

	if (type == NODE_NONE)
	    continue;
	for (i = 0; i < len; i++) {
	    int clit = children[i];
	    int var = IABS(clit);
	    if (clit < 0)
		neg_fanouts[var-1] = ilist_push(neg_fanouts[var-1], id);
	    else 
		pos_fanouts[var-1] = ilist_push(pos_fanouts[var-1], id);
	}
    }
    if (repeated_literal_ok) {
	/* Remove any duplicates from fanout lists */
	int var;
	for (var = 1; var <= input_variable_count; var++) {
	    ilist old_fanouts = neg_fanouts[var-1];
	    neg_fanouts[var-1] = ilist_deduplicate(old_fanouts);
	    if (old_fanouts != neg_fanouts[var-1])
		ilist_free(old_fanouts);
	}
	/* Can only be for literal. */
	for (var = 1; var <= input_variable_count; var++) {
	    ilist old_fanouts = pos_fanouts[var-1];
	    pos_fanouts[var-1] = ilist_deduplicate(old_fanouts);
	    if (old_fanouts != pos_fanouts[var-1])
		ilist_free(old_fanouts);
	}
    }
}

/* Sift down into heap */
void sift_down(propagate_t *prop, int idx) {
    int *priority_queue = prop->priority_queue;
    int left = 2 * idx + 1;
    while (left < prop->priority_count) {
	int right = left + 1;
	int min = idx;
	if (priority_queue[left] < priority_queue[min])
	    min = left;
	if (right < prop->priority_count && priority_queue[right] < priority_queue[min])
	    min = right;
	if (min == idx) 
	    return;
	else {
	    int tmp = priority_queue[min];
	    priority_queue[min] = priority_queue[idx];
	    priority_queue[idx] = tmp;
	    idx = min;
	    left = 2 * idx + 1;
	}
    }
}

/* Sift up into heap */
void sift_up(propagate_t *prop, int idx) {
    int *priority_queue = prop->priority_queue;
    while (idx > 0) {
	int parent = (idx - 1)/2;
	if (priority_queue[idx] < priority_queue[parent]) {
	    int tmp = priority_queue[idx];
	    priority_queue[idx] = priority_queue[parent];
	    priority_queue[parent] = tmp;
	    idx = parent;
	} else
	    return;
    }
}

void priority_add(propagate_t *prop, int var) {
    int *priority_queue = prop->priority_queue;
    int index = var_to_index(var);
    if (!plusplus_max2(&(prop->node_event_count[index-1]))) {
	priority_queue[prop->priority_count++] = var;
	sift_up(prop, prop->priority_count-1);
#if VLEVEL >= 3
	info_printf(3, "     Added %d to priority queue\n", var);
#endif
    }
}

int priority_next(propagate_t *prop) {
    int *priority_queue = prop->priority_queue;
    if (prop->priority_count == 0)
	return -1;
    int var = priority_queue[0];
    int index = var_to_index(var);
    priority_queue[0] = priority_queue[--prop->priority_count];
    sift_down(prop, 0);
#if VLEVEL >= 3
    info_printf(3, "   Removed %d from priority queue\n", var);
#endif
    prop->event_count++;
    return var;
}

/* Propagate effect of adding unit literal */
void process_fanout(propagate_t *prop, int lit) {
    int var = IABS(lit);
    ilist fanouts = lit < 0 ? pos_fanouts[var-1] : neg_fanouts[var-1];
    int i;
    int len = ilist_length(fanouts);
#if VLEVEL >= 3
    if (verb_level >= 3) {
	info_printf(3, "   Adding fanouts of literal %d:", lit);
	ilist_print(fanouts, stdout, ", ");
	printf("\n");
    }
#endif    
    for (i = 0; i < len; i++)
	priority_add(prop, fanouts[i]);
}

void rup_run_input(propagate_t *prop, int tcid, int *lits) {
    int lit;
    /* Set up event list with fanouts of negated clause literals */
#if VLEVEL >= 3
    info_printf(3, "Running rup_run_input on input clause #%d\n", tcid);
#endif
    while ((lit = *lits++) != 0)
	process_fanout(prop, -lit);
    int var;
    bool conflict = false;
    while (!conflict && (var = priority_next(prop)) > 0) {
	event_count++;
	int idx = var_to_index(var);
	node_type_t type = node_list[idx-1].type;
	ilist children = node_list[idx-1].children;
	int id = node_list[idx-1].id;
	int i;
	int len = ilist_length(children);
	int ecount = prop->node_event_count[idx-1];
	prop->node_event_count[idx-1] = 0;
	int propagate_threshold = 1;
	if (type == NODE_SUM)
	    propagate_threshold = len;
	if (ecount >= propagate_threshold) {
	    conflict = var == declared_root;
	    process_fanout(prop, -id);
	}
#if VLEVEL >= 3
	info_printf(3, "  Node %d.  Event count = %d, Threshold = %d\n", id, ecount, propagate_threshold);
#endif
    }
    reset_propagator(prop);
    if (!conflict)
	err_printf(__cfunc__, "RUP failure for input clause %d.  No conflict detected\n", tcid);
    return;
}

/*============================================
  Support for CPOG file commands
============================================*/

void cpog_batch_delete_clauses() {
    int dcount = 0;
    while (true) {
	token_t token = token_next();
	if (token == TOK_EOL)
	    err_printf(__cfunc__, "Unexpected end-of-line.  List of clauses must be terminated by 0\n");
	else if (token != TOK_INT)
	    err_printf(__cfunc__, "Unexpected token %s ('%s')\n", token_name[token], token_last);
	int cid = token_value;
	if (token_value == 0)
	    break;
	clause_location_t location;
	if (!find_clause(cid, &location))
	    err_printf(__cfunc__, "Cannot delete clause #%d.  Not defined\n", cid);
	clause_type_t ctype = clause_type(&location);
	if (!(ctype == CLAUSE_FORWARD || ctype == CLAUSE_STRUCTURAL))
	    err_printf(__cfunc__, "Cannot delete clause #%d  (type %s) with 'D' command.\n", cid, clause_type_name(ctype));
	bool deleted = clause_delete(&location);
	dcount++;
	if (!deleted) 
	    err_printf(__cfunc__, "Could not delete clause %d.  Never defined or already deleted\n", cid);
    }
    token_find_eol();
    cpog_noninput_deletion_count += dcount;
    info_printf(3, "Deleted %d non-input clauses\n", dcount);
}

void cpog_add_product(int cid) {
    token_t token = token_next();
    if (token != TOK_INT)
	err_printf(__cfunc__, "Expected operation number.  Got %s ('%s') instead\n", token_name[token], token_last);
    int nid = token_value;
    node_t *node = node_new(NODE_PRODUCT, nid, cid);
    node->children = ilist_new(2);
    node->dependency_list = ilist_new(1);
    ilist local_dependency_list = ilist_new(0);
    /* Get children */
    while (true) {
	token = token_next();
	if (token != TOK_INT)
	    err_printf(__cfunc__, "Expected product operation argument.  Got %s ('%s') instead\n", token_name[token], token_last);
	if (token_value == 0)
	    break;
	int lit = token_value;
	int var = IABS(lit);
	node->children = ilist_push(node->children, lit);
	if (var <= input_variable_count) {
	    if (is_pkc && !show_variables[var-1] && nid <= declared_root) 
		err_printf(__cfunc__, "Can't add literal %d to node %d children.  Not a data variable\n", lit, nid);
	    local_dependency_list = ilist_push(local_dependency_list, var);
	} else {
	    if (var != lit)
		err_printf(__cfunc__, "Can't add negative literal %d to node %d children.  Violates NNF\n", lit, nid);
	    node_t *cnode = node_find(var);
	    if (cnode == NULL || cnode->type == NODE_NONE) 
		err_printf(__cfunc__, "Can't add literal %d to node %d children.  Invalid node Id %d\n", lit, nid, var);
	    int dvar = 0;
	    if (!ilist_is_disjoint(node->dependency_list, cnode->dependency_list, &dvar))
		err_printf(__cfunc__, "Can't add node %d to node %d children.  Both dependency sets include variable %d\n", lit, nid, dvar);
	    ilist save = node->dependency_list;
	    node->dependency_list = ilist_union(node->dependency_list, cnode->dependency_list);
	    ilist_free(save);
	}
    }
    if (ilist_length(local_dependency_list) > 0) {
	int dvar = 0;
	ilist_sort(local_dependency_list);
	if (repeated_literal_ok) {
	    ilist save = local_dependency_list;
	    local_dependency_list = ilist_deduplicate(local_dependency_list);
	    if (save != local_dependency_list)
		ilist_free(save);
	} else {
	    if (ilist_find_duplicate(local_dependency_list, &dvar))
		err_printf(__cfunc__, "Can't add variable %d to node %d children.  Same or opposite literals in argument\n", dvar, nid);
	}
	if (!ilist_is_disjoint(node->dependency_list, local_dependency_list, &dvar))
	    err_printf(__cfunc__, "Can't add variable %d to node %d children.  Already in dependency set\n", dvar, nid);			       
	ilist save = node->dependency_list;
	node->dependency_list = ilist_union(node->dependency_list, local_dependency_list);
	ilist_free(save);
    }
    ilist_free(local_dependency_list);
    /* Done */
    token = token_next();
    if (token != TOK_EOL) 
	err_printf(__cfunc__, "Expected end of line.  Got %s ('%s') instead\n", token_name[token], token_last);

    /* Add clauses */
    start_clause(cid);
    clause_add_literal(nid);
    int i;
    int n = ilist_length(node->children);
    clause_type_t ctype = n == 0 && nid == declared_root ? CLAUSE_ROOT : CLAUSE_TSEITIN;
    for (i = 0; i < n; i++)
	clause_add_literal(-node->children[i]);
    clause_add_literal(0);
    finish_clause(cid, ctype);
    for (i = 0; i < n; i++) {
	start_clause(cid+i+1);
	clause_add_literal(-nid);
	clause_add_literal(node->children[i]);
	clause_add_literal(0);
	finish_clause(cid+i+1, CLAUSE_TSEITIN);
    }
    if (n == 0 && nid == declared_root)
	root_clause_added = true;
    cpog_operation_count ++;
    cpog_tseitin_clause_count += (n+1);
    info_printf(3, "Processed product %d addition\n", nid);
}

void cpog_add_skolem(int cid) {
    token_t token = token_next();
    if (token != TOK_INT)
	err_printf(__cfunc__, "Expected operation number.  Got %s ('%s') instead\n", token_name[token], token_last);
    int nid = token_value;
    if (!is_pkc)
	err_printf(__cfunc__, "Cannot add Skolem node %d.  Not performing projected compilation\n", nid);
    node_t *node = node_new(NODE_SKOLEM, nid, cid);
    node->children = ilist_new(2);
    node->dependency_list = ilist_new(1);
    /* Get children */
    while (true) {
	token = token_next();
	if (token != TOK_INT)
	    err_printf(__cfunc__, "Expected skolem operation argument.  Got %s ('%s') instead\n", token_name[token], token_last);
	if (token_value == 0)
	    break;
	int lit = token_value;
	int var = IABS(lit);
	node->children = ilist_push(node->children, lit);
	if (var <= input_variable_count) {
	    if (show_variables[var-1])
		err_printf(__cfunc__, "Can't add literal %d to skolem node %d children.  Not a projection variable\n", lit, nid);
	    else
		node->dependency_list = ilist_push(node->dependency_list, var);
	} else
	    err_printf(__cfunc__, "Can't add literal %d to node %d children.  Child must be literal of projection variable\n", lit, nid);
    }
    ilist_sort(node->dependency_list);
    /* Check for duplicates */
    if (repeated_literal_ok) {
	ilist save = node->dependency_list;
	node->dependency_list = ilist_deduplicate(node->dependency_list);
	if (save != node->dependency_list)
	    ilist_free(save);
    } else {
	int dvar = 0;
	if (ilist_find_duplicate(node->dependency_list, &dvar))
	    err_printf(__cfunc__, "Can't add variable %d to Skolem node %d children.  Same or opposite literals in argument\n", dvar, nid);
    }
    /* Done */
    token = token_next();
    if (token != TOK_EOL) 
	err_printf(__cfunc__, "Expected end of line.  Got %s ('%s') instead\n", token_name[token], token_last);

    /* Add clauses */
    start_clause(cid);
    clause_add_literal(nid);
    clause_add_literal(0);
    finish_clause(cid, CLAUSE_DISABLE);
    int n = ilist_length(node->children);
    if (use_explicit_deletion) {
	int i;
	for (i = 0; i < n; i++) {
	    start_clause(cid+i+1);
	    clause_add_literal(-nid);
	    clause_add_literal(node->children[i]);
	    clause_add_literal(0);
	    finish_clause(cid+i+1, CLAUSE_SKOLEM);
	}
	cpog_skolem_clause_count += n;
    } else
	virtual_clause_count += n;
    cpog_operation_count ++;
    cpog_disable_clause_count++;
    info_printf(3, "Processed skolem %d addition\n", nid);
}

void cpog_add_sum(int cid, bool weak) {
    token_t token = token_next();
    if (token != TOK_INT)
	err_printf(__cfunc__, "Expected operation number.  Got %s ('%s') instead\n", token_name[token], token_last);
    int nid = token_value;
    node_t *node = node_new(NODE_SUM, nid, cid);
    node->children = ilist_new(2);
    node->dependency_list = ilist_new(1);
    ilist local_dependency_list = ilist_new(0);
    /* Get children */
    while (true) {
	token = token_next();
	if (token != TOK_INT) 
	    err_printf(__cfunc__, "Expected sum operation argument.  Got %s ('%s') instead\n", token_name[token], token_last);
	int lit = token_value;
	int var = IABS(lit);
	if (weak && var == 0)
	    break;
	node->children = ilist_push(node->children, lit);
	if (var <= input_variable_count) {
	    if (is_pkc && !show_variables[var-1])
		err_printf(__cfunc__, "Can't add literal %d to node %d children.  Not a data variable\n", lit, nid);
	    local_dependency_list = ilist_push(local_dependency_list, var);
	} else {
	    if (var != lit)
		err_printf(__cfunc__, "Can't add negative literal %d to node %d children.  Not NNF\n", lit, nid);
	    node_t *cnode = node_find(var);
	    if (cnode == NULL || cnode->type == NODE_NONE)
		err_printf(__cfunc__, "Can't add literal %d to node %d children.  Invalid node Id %d\n", lit, nid, var);
	    ilist save = node->dependency_list;
	    node->dependency_list = ilist_union(node->dependency_list, cnode->dependency_list);
	    ilist_free(save);
	}
	if (!weak && ilist_length(node->children) == 2)
	    break;
    }
    if (ilist_length(local_dependency_list) > 0) {
	ilist_sort(local_dependency_list);
	ilist save = node->dependency_list;
	node->dependency_list = ilist_union(node->dependency_list, local_dependency_list);
	ilist_free(save);
    }
    ilist_free(local_dependency_list);
    
    if (!weak) {
	/* Prove mutual exclusion */
	lset_clear();
	lset_add_lit(node->children[0]);
	lset_add_lit(node->children[1]);
	rup_run(cid, CLAUSE_STRUCTURAL);
    }

    token_confirm_eol();
    /* Add sum clause */
    start_clause(cid);
    clause_add_literal(-nid);
    int i;
    int n = ilist_length(node->children);
    for (i = 0; i < n; i++)
	clause_add_literal(node->children[i]);
    clause_add_literal(0);
    finish_clause(cid, CLAUSE_TSEITIN);
    for (i = 0; i < n; i++) {
	start_clause(cid+i+1);
	clause_add_literal(nid);
	clause_add_literal(-node->children[i]);
	clause_add_literal(0);
	finish_clause(cid+i+1, CLAUSE_TSEITIN);
    }
    cpog_operation_count ++;
    cpog_tseitin_clause_count += (n+1);
    info_printf(3, "Processed %ssum %d addition\n", weak ? "weak " : "", nid);
}


/*============================================
  Support for multithreaded input deletion
============================================*/

/* Queue of clause ranges */
typedef struct {
    int cid_min;
    int cid_max;
} clause_range_t;

int clause_queue_count = 0;
clause_range_t *clause_queue = NULL;
int processed_count = 0;

/* Forward pointer */
int cpog_delete_range(propagate_t *prop, int cid_min, int cid_max);

void setup_deletion_queue() {
    int block_size = (input_clause_count+thread_limit-1) / thread_limit;
    if (block_size > CLAUSE_DELETION_BLOCK)
	block_size = CLAUSE_DELETION_BLOCK;
    clause_queue_count = (input_clause_count + block_size - 1)/block_size;
    clause_queue = calloc(clause_queue_count, sizeof(clause_range_t));
    int cid_min;
    int qi = 0;
    for (cid_min = 1; cid_min <= input_clause_count; cid_min += block_size) {
	int cid_max = cid_min + block_size-1;
	if (cid_max > input_clause_count)
	    cid_max = input_clause_count;
	clause_queue[qi].cid_min = cid_min;
	clause_queue[qi++].cid_max = cid_max;
    }
    processed_count = 0;
}

/* This should be protected by a mutex */
bool next_deletion(propagate_t *prop, int *dcountp) {
#if THREADING
    if (thread_limit > 1)
	pthread_mutex_lock(&queue_lock);
#endif /* THREADING */
    if (processed_count >= clause_queue_count) {
#if THREADING
	if (thread_limit > 1)
	    pthread_mutex_unlock(&queue_lock);
#endif /* THREADING */
	return false;
    }
    int cid_min = clause_queue[processed_count].cid_min;
    int cid_max = clause_queue[processed_count++].cid_max;
    *dcountp = cpog_delete_range(prop, cid_min, cid_max);
#if THREADING
    if (thread_limit > 1)
	pthread_mutex_unlock(&queue_lock);
#endif /* THREADING */
    return true;
}

void *deletion_thread(void *vargp) {
    size_t t = (size_t) vargp;
    int bcount = 0;
    int dcount = 0;
    int ndcount = 0;
    propagate_t *prop = new_propagator();
    while (next_deletion(prop, &ndcount)) {
	bcount++;
	dcount += ndcount;
    }
    data_printf(2, "Thread %d processed %d clauses in %d segments\n", (int) t, dcount, bcount);
    return NULL;
}

void run_deletion() {
    setup_deletion_queue();
#if THREADING
    if (thread_limit > 1) {
	data_printf(1, "Running deletion with %d threads\n", thread_limit);
	pthread_t tid[thread_limit-1];
	size_t t;
	for (t = 0; t < thread_limit-1; t++)
	    pthread_create(&tid[t], NULL, deletion_thread, (void *) t);
	/* Let main thread execute thread routine */
	deletion_thread((void *) t);
	for (t = 0; t < thread_limit-1; t++)
	    pthread_join(tid[t], NULL);
    } else {
	propagate_t *prop = new_propagator();
	int dcount = 0;
	int ndcount = 0;
	while (next_deletion(prop, &ndcount))
	    dcount += ndcount;
	data_printf(2, "Program deleted %d clauses\n", dcount);
    }
#else /* !THREADING */
    propagate_t *prop = new_propagator();
    int dcount = 0;
    int ndcount = 0;
    while (next_deletion(prop, &ndcount))
	dcount += ndcount;
    data_printf(2, "Program deleted %d clauses\n", dcount);
#endif /* THREADING */
}

/* Report intermediate status information.  Must be able to manage information from multiple threads */

/* Number of deleted clauses that will trigger report */
int report_interval;
/* Time since deletion started */
double start_deletion = 0.0;
/* Time of last report */
double last_deletion = 0.0;
/* How many clauses had been previously deleted */
int implicit_last;
/* How many events had previously occurred */
int event_last;

void clear_tautologies() {
    int cid;
    int tcount = 0;
    clause_location_t location;
    bool ok = find_clause(1, &location);
    while (ok) {
	int cid = generate_clause_id(&location);
	if (cid > input_clause_count)
	    break;
	int *lits = clause_locate(&location);
	if (!rup_setup(lits)) {
	    tcount++;
	    implicit_deletion_count++;
	    bool deleted = clause_delete(&location);
	    if (deleted)
		data_printf(2, "Clause #%d.  Tautology (deleted)\n", cid);
	    else
		err_printf(__cfunc__, "Could not delete clause %d.  Never defined or already deleted\n", cid);
	}
	ok = goto_next_clause(&location);
    }
    if (tcount > 0)
	data_printf(1, "%d input clause tautologies deleted\n", tcount);
}

void implicit_delete_input_clause(propagate_t *prop, int cid, clause_location_t *loc) {
    int *lits = clause_locate(loc);
    bool deleted = clause_delete(loc);
    if (!deleted) 
	err_printf(__cfunc__, "Could not delete clause %d.  Never defined or already deleted\n", cid);
    rup_run_input(prop, cid, lits);
    info_printf(3, "Processed implicit input clause %d deletion\n", cid);
    prop->implicit_deletion_count++;
}

void init_report(int interval) {
    report_interval = interval;
    start_deletion = last_deletion = tod();
    implicit_last = 0;
    event_last = 0;
}


/** This needs to be protected by mutex **/
void update_report(propagate_t *prop) {
    implicit_deletion_count += prop->implicit_deletion_count;
    event_count += prop->event_count;
    prop->implicit_deletion_count = 0;
    prop->event_count = 0;
    if (implicit_deletion_count >= implicit_last + report_interval) {
	double this_deletion = tod();
	int this_deletion_count = implicit_deletion_count-implicit_last;
	long this_event = event_count - event_last;
	double this_deletion_time = this_deletion-last_deletion;
	data_printf(1, "Elapsed = %.3f.  Deleted %d clauses in %.3f seconds %ld events.  Total deletions = %d.  Events/us = %.2f Deletions/s = %.2f\n", 
		    elapsed(), this_deletion_count, this_deletion_time, this_event, implicit_deletion_count + explicit_deletion_count,
		    1e-6 * this_event/this_deletion_time, this_deletion_count/this_deletion_time);
	implicit_last = implicit_deletion_count;
	event_last = event_count;
	last_deletion = this_deletion;
    }
}

/* Input deletion check for range of clauses */
int cpog_delete_range(propagate_t *prop, int cid_min, int cid_max) {
    clause_location_t location;
    bool ok = find_clause(cid_min, &location);
    int cid = cid_min;
    int dcount = 0;
    while (ok) {
	int cid = generate_clause_id(&location);
	if (cid > cid_max)
	    break;
	if (clause_type(&location) == CLAUSE_INPUT) {
	    implicit_delete_input_clause(prop, cid, &location);
	    dcount++;
	}
	ok = goto_next_clause(&location);
    }
    update_report(prop);
    return dcount;
}

/* Check end condition.  Return literal representation of root node */
int cpog_final_root() {
    if (declared_unsatisfiable) {
	data_printf(1, "Elapsed = %.3f.  Completed processing of SCPOG file\n", elapsed());
	return 0;
    }
    if (!root_clause_added)
	err_printf(__cfunc__, "Unit clause for root %d not added\n", declared_root);
    data_printf(1, "Elapsed = %.3f.  Completed processing of SCPOG file\n", elapsed());
    if (check_delete && explicit_deletion_count < input_clause_count) {
	implicit_deletion_count = 0;
	clear_tautologies();
	int report_interval = (input_clause_count-explicit_deletion_count) / REPORT_MAX_COUNT;
	if (report_interval < REPORT_MIN_INTERVAL)
	    report_interval = REPORT_MIN_INTERVAL;
	if (report_interval > REPORT_MAX_INTERVAL)
	    report_interval = REPORT_MAX_INTERVAL;
	init_report(report_interval);
	clause_free_noninput();
	double start_deletion = tod();
	build_deletion_structures();
	run_deletion();
	if (implicit_deletion_count > 0) {
	    double deletion_time = tod() - start_deletion;
	    data_printf(1, "Elapsed = %.3f.  Implicitly deleted %d input clauses.  %ld events.  Events/us = %.2f Deletions/s = %.2f\n", elapsed(),
			implicit_deletion_count, event_count,
			1e-6 * event_count/deletion_time, implicit_deletion_count/deletion_time);
	}
    }
    return declared_root;
}

void cpog_read(char *fname) {
    token_setup(fname);
    /* Find and parse each command */
    while (true) {
	int cid = 0;
	token_t token = token_next();
	if (token == TOK_EOF)
	    break;
	if (token == TOK_EOL)
	    continue;
	if (token == TOK_STRING && token_last[0] == 'c') {
	    token_find_eol();
	    continue;
	} else if (token == TOK_INT) {
	    cid = token_value;
	    token = token_next();
	}
	if (token != TOK_STRING) 
	    err_printf(__cfunc__, "Expecting CPOG command.  Got %s ('%s') instead\n", token_name[token], token_last);
	else if (strcmp(token_last, "a") == 0)
	    cpog_add_clause(cid, false);
	else if (strcmp(token_last, "as") == 0)
	    cpog_add_clause(cid, true);
	else if (strcmp(token_last, "r") == 0)
	    cpog_read_root();
	else if (strcmp(token_last, "d") == 0)
	    cpog_delete_clause();
	else if (strcmp(token_last, "D") == 0)
	    cpog_batch_delete_clauses();
 	else if (strcmp(token_last, "p") == 0)
	    cpog_add_product(cid);
	else if (strcmp(token_last, "t") == 0)
	    cpog_add_skolem(cid);
	else if (strcmp(token_last, "s") == 0)
	    cpog_add_sum(cid, false);
	else if (strcmp(token_last, "S") == 0) {
	    if (!weak_mode) 
		err_printf(__cfunc__, "Encountered weak sum node, but not in weak mode\n");
	    cpog_add_sum(cid, true);
	} else 
	    err_printf(__cfunc__, "Invalid CPOG command '%s'\n", token_last);
    }
    token_finish();
    int root_count = root_clause_added ? 1 : 0;
    int all_clause_count =  cpog_tseitin_clause_count + cpog_disable_clause_count + cpog_skolem_clause_count + cpog_structural_count + cpog_forward_count + root_count;
    if (use_explicit_deletion) {
	data_printf(1, "Read CPOG file with %d operations,  %d Tseitin + %d Disable + %d Skolem + %d Structural + %d Forward + %d root = %d clauses\n",
		    cpog_operation_count,
		    cpog_tseitin_clause_count, cpog_disable_clause_count, cpog_skolem_clause_count, cpog_structural_count, cpog_forward_count, root_count,
		    all_clause_count);
    } else {
	data_printf(1, "Read CPOG file with %d operations,  %d Tseitin + %d Disable + %d Structural + %d Forward + %d root = %d real + %ld virtual clauses\n",
		    cpog_operation_count,
		    cpog_tseitin_clause_count, cpog_disable_clause_count, cpog_structural_count, cpog_forward_count, root_count,
		    all_clause_count, virtual_clause_count);
    }
    data_printf(3, "Clauses divided into %d blocks\n", clause_block_count);
    data_printf(1, "Explicitly deleted %d input and %d non-input clauses\n", explicit_deletion_count, cpog_noninput_deletion_count);
}

/*============================================
  Counting
============================================*/

q25_ptr *input_weights = NULL;
q25_ptr rescale = NULL;

/* Perform ring evalation.
   Given array of weights for input variables
*/
q25_ptr ring_evaluate(q25_ptr *input_weights) {
    int id;
    q25_ptr val;
    if (declared_unsatisfiable)
	return q25_from_32(0);
    for (id = input_variable_count+1; id <= declared_root; id++) {
	node_t *np = node_find(id);
	bool is_skolem = np->type == NODE_SKOLEM;
	switch (np->type) {
	case NODE_PRODUCT:
	case NODE_SKOLEM:
	    val = q25_from_32(1);
	    break;
	case NODE_SUM:
	    val = q25_from_32(0);
	    break;
	default:
	    err_printf(__cfunc__, "Invalid type %d for node %d\n", (int) np->type, id);
	}
	int i;
	for (i = 0; !is_skolem && i < ilist_length(np->children); i++) {
	    int clit = np->children[i];
	    int cid = IABS(clit);
	    q25_ptr cval;
	    if (cid <= input_variable_count) 
		cval = input_weights[cid-1];
	    else {
		node_t *cnp = node_find(cid);
		cval = cnp->ring_value;
	    }
	    if (clit < 0) {
		cval = q25_one_minus(cval);
	    }
	    q25_ptr nval = np->type == NODE_PRODUCT ? q25_mul(val, cval) : q25_add(val, cval);
	    q25_free(val);
	    if (clit < 0)
		q25_free(cval);
	    val = nval;
	}
	np->ring_value = val;
	if (verb_level >= 3) {
	    info_printf(3, "Ring value for node %d: ", np->id);
	    q25_write(val, stdout);
	    printf("\n");
	}
    }
    val = q25_copy(val);
    for (id = input_variable_count+1; id <= declared_root; id++) {
	node_t *np = node_find(id);
	q25_free(np->ring_value);
	np->ring_value = NULL;
    }
    return val;
}

q25_ptr count_regular() {
    int nvar = 0;
    if (is_pkc) {
	nvar = 0;
	int v;
	for (v = 1; v <= input_variable_count; v++)
	    if (show_variables[v-1])
		nvar++;
	data_printf(2, "%d data variables\n", nvar);
    } else
	  nvar = input_variable_count;
    q25_ptr *input_weights = calloc(input_variable_count, sizeof(q25_ptr));
    if (input_weights == NULL) {
	err_printf(__cfunc__, "count_regular", "Couldn't allocate memory for weights\n");
	return NULL;
    }
    q25_ptr qone = q25_from_32(1);
    q25_ptr half = q25_scale(qone, -1, 0);
    q25_free(qone);
    int v;
    for (v = 1; v <= input_variable_count; v++)
	input_weights[v-1] = half;
    q25_ptr density = ring_evaluate(input_weights);
    q25_ptr result = q25_scale(density, nvar, 0);
    q25_free(half);
    q25_free(density);
    free(input_weights);
    return result;
}


bool cnf_read_weights(char *fname) {
    bool found_wmc = false;
    token_setup(fname);
    /* Find and parse wmc header */
    while (true) {
	token_t token = token_next();
	if (token == TOK_EOL)
	    continue;
	if (token != TOK_STRING)
	    err_printf(__cfunc__, "Unexpected token %s ('%s') while looking for WMC header\n", token_name[token], token_last);
	if (token_last[0] == 'c') {
	    if (!found_wmc) {
		bool ok = true;
		token = token_next();
		ok = token == TOK_STRING && strcmp(token_last, "t") == 0;
		if (ok)
		    token = token_next();
		ok = ok && token == TOK_STRING && 
		    (strcmp(token_last, "wmc") == 0 || strcmp(token_last, "pwmc") == 0);
		if (ok)
		    found_wmc = true;
	    }
	    if (token != TOK_EOL)
		token_find_eol();
	} else if (token_last[0] == 'p') {
	    if (found_wmc) {
		token_find_eol();
		break;
	    }
	    else {
		/* Not weighted model counting problem */
		token_finish();
		return false;
	    }
	}
    }
    input_weights = calloc(input_variable_count, sizeof(q25_ptr));
    q25_ptr *positive_weights = calloc(input_variable_count, sizeof(q25_ptr));
    q25_ptr *negative_weights = calloc(input_variable_count, sizeof(q25_ptr));
    if (!input_weights || !positive_weights || !negative_weights) 
	err_printf(__cfunc__, "Couldn't allocate memory for weights\n");
    rescale = q25_from_32(1);
    while (true) {
	token_t token = token_next();
	if (token == TOK_EOF)
	    break;
	else if (token == TOK_EOL)
	    continue;
	else if (token == TOK_STRING && token_last[0] == 'c') {
	    bool ok = true;
	    token = token_next();
	    ok = token == TOK_STRING && strcmp(token_last, "p") == 0;
	    if (ok)
		token = token_next();
	    ok = ok && token == TOK_STRING && strcmp(token_last, "weight") == 0;
	    if (ok)
		token = token_next();
	    ok = ok && token == TOK_INT;
	    ok = ok && skip_space();
	    if (!ok) {
		if (token != TOK_EOL)
		    token_find_eol();
		continue;
	    }
	    int lit = token_value;
	    int var = IABS(lit);

	    if (var > input_variable_count)
		err_printf(__cfunc__, "Invalid literal %d for weight\n", lit);
	    q25_ptr cur_val = lit < 0 ? negative_weights[var-1] : positive_weights[var-1];
	    if (cur_val != NULL)
		err_printf(__cfunc__, "Already have weight for literal %d\n", lit);
	    q25_ptr val = q25_read(token_file);
	    ok = q25_is_valid(val);
	    if (ok)
		token = token_next();
	    ok = ok && token == TOK_INT && token_value == 0;
	    if (!ok)
		err_printf(__cfunc__, "Couldn't read weight for literal %d\n", lit);
	    token_find_eol();
	    if (lit < 0)
		negative_weights[var-1] = val;
	    else
		positive_weights[var-1] = val;
	    info_printf(3, "Found weight for literal %d\n", lit);
	} else
	    token_find_eol();
    }
    token_finish();
    /* Fix up weights */
    int var;
    for (var = 1; var <= input_variable_count; var++) {
	q25_ptr pwt = positive_weights[var-1];
	q25_ptr nwt = negative_weights[var-1];
	if (nwt == NULL) {
	    if (pwt == NULL) {
		q25_ptr sum = q25_from_32(2);
		input_weights[var-1] = q25_recip(sum);
		q25_ptr nrescale = q25_mul(rescale, sum);
		q25_free(rescale);
		q25_free(sum);
		rescale = nrescale;
	    } else
		input_weights[var-1] = pwt;
	} else if (pwt == NULL) {
	    input_weights[var-1] = q25_one_minus(nwt);
	    q25_free(nwt);
	} else {
	    q25_ptr sum = q25_add(nwt, pwt);
	    if (q25_is_one(sum)) {
		input_weights[var-1] = pwt;
		q25_free(nwt); q25_free(sum);
	    } else {
		q25_ptr recip = q25_recip(sum);
		if (!q25_is_valid(recip))
		    err_printf(__cfunc__, "Could not get reciprocal of summed weights for variable %d\n", var);
		q25_ptr nrescale = q25_mul(rescale, sum);
		q25_free(rescale);
		rescale = nrescale;
		input_weights[var-1] = q25_mul(pwt, recip);
		q25_free(nwt); q25_free(pwt);
		q25_free(sum); q25_free(recip);
	    }
	}
    }
    free(positive_weights);
    free(negative_weights);
    data_printf(3, "Read weights from CNF file\n");
    return true;
}

q25_ptr count_weighted(char *fname) {
    if (!cnf_read_weights(fname))
	return NULL;
    q25_ptr val = ring_evaluate(input_weights);
    q25_ptr rval = q25_mul(val, rescale);
    q25_free(val);
    q25_free(rescale);
    int v;
    for (v = 1; v < input_variable_count; v++) {
	q25_free(input_weights[v-1]);
    }
    free(input_weights);
    return rval;
}

void run(char *cnf_name, char *cpog_name) {
    start_time = tod();
    double secs;
    cnf_read(cnf_name);
    if (verb_level >= 3)
	cnf_show(stdout);
    if (cpog_name != NULL) {
	cpog_read(cpog_name);
	if (verb_level >= 3) {
	    cpog_show(stdout);
	    printf("All clauses:\n");
	    clause_show_all(stdout);
	}
	int root = cpog_final_root();
	if (root == 0) {
	    if (!check_add) 
		data_printf(0, "NOTHING CHECKED.  CPOG representation not verified\n");
	    else if (!proved_unsatisfiable)
		err_printf(__cfunc__, "POG declared as unsatisfiable, but empty clause not added\n");
	    else
 		data_printf(0, "FULL-PROOF SUCCESS.  CPOG representation of unsatisfiable POG verified\n");
	} else {
	    data_printf(2, "Final root literal %d\n", root);
	    if (!check_add && !check_delete) 
		data_printf(0, "NOTHING CHECKED.  CPOG representation not verified\n");
	    else if (!check_add)
		data_printf(0, "CLAUSE DELETIONS VALID.  CPOG representation partially verified\n");
	    else if (!check_delete)
		data_printf(0, "CLAUSE ADDITIONS VALID.  CPOG representation partially verified\n");
	    else
		data_printf(0, "FULL-PROOF SUCCESS.  CPOG representation verified\n");
	}
    }
    if (weak_mode) 
	data_printf(1, "Weak mode equivalence checked\n");
    else {
	double post_check = tod();
	long start_count = q25_operation_count();
	q25_ptr mc = count_regular();
	if (mc && q25_is_valid(mc)) {
	    data_printf(0, "Regular model count = ");
	    q25_write(mc, stdout);
	    printf("\n");
	    data_printf(0, "Regular count required %ld binary operations\n", 
			q25_operation_count() - start_count);
	}
	q25_free(mc);
	start_count = q25_operation_count();
	q25_ptr wmc = count_weighted(cnf_name);
	if (wmc && q25_is_valid(wmc)) {
	    data_printf(0, "Weighted model count = ");
	    q25_write(wmc, stdout);
	    printf("\n");
	    data_printf(0, "Weighted count required %ld binary operations\n", 
			q25_operation_count() - start_count);
	}
	q25_free(wmc);
	secs = tod() - post_check;
	data_printf(1, "Time to compute model counts: %.3f\n", secs);
    }
    data_printf(1, "Elapsed seconds: %.3f\n", elapsed());
}

int main(int argc, char *argv[]) {
    char *cnf_name = NULL;
    char *cpog_name = NULL;
    verb_level = 1;
    if (argc <= 1) 
	usage(argv[0]);
    int argi;
    char *istring;
    FILE *logfile;
    for (argi = 1; argi < argc && argv[argi][0] == '-'; argi++) {
	switch (argv[argi][1]) {
	case 'h':
	    usage(argv[0]);
	    break;
	case 'l':
	    skipping_rup = true;
	    break;
	case 'd':
	    use_explicit_deletion = true;
	    break;
	case 'v':
	    istring = argv[++argi];
	    verb_level = atoi(istring);
	    break;
	case 'L':
	    logfile_name = strndup(argv[++argi], 100);
	    logfile = fopen(logfile_name, "w");
	    if (logfile)
		fclose(logfile);
	    break;
	case 'w':
	    weak_mode = true;
	    break;
	case 'A':
	case '1':
	    check_add = false;
	    break;
	case 'D':
	    check_delete = false;
	    break;
	case 'n':
	    istring = argv[++argi];
	    thread_limit = atoi(istring);
#if !THREADING
	    if (thread_limit > 1)
		data_printf(1, "WARNING: Threading not enabled.  Cannot run %d threads\n", thread_limit);
#endif	 /* !THREADING */
	    break;
	default:
	    printf("Unknown command line option '%s'\n", argv[argi]);
	    usage(argv[0]);
	}
    }
    if (argi == argc) {
	printf("Require CNF file\n");
	usage(argv[0]);
    }
    cnf_name = argv[argi++];
    if (argi < argc) {
	cpog_name = argv[argi++];
    }
    run(cnf_name, cpog_name);
    return 0;
}
