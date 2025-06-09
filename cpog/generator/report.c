#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include "report.h"

int verblevel = 1;

FILE *errfile = NULL;
FILE *verbfile = NULL;

static panic_function_t panic_function = NULL;

static const char *logfile_name = NULL;

static const char *datafile_name = "datafile.csv";

static const char *name_tag = "cpog";
#define SMAX 1024
static char name_buf[SMAX];

static int sequence_number = 1000 * 1000 * 10;

static double start_time = 0.0;

const char *archive_string(const char *tstring) {
    char *rstring = (char *) malloc(strlen(tstring)+1);
    strcpy(rstring, tstring);
    return (const char *) rstring;
}

void init_namer(const char *fname) {
    sequence_number = 1000 * 1000;
    strncpy(name_buf, fname, SMAX-1);
    name_buf[SMAX-1] = 0;
    int len = strlen(name_buf);
    int last_slash = len - 1;
    while (last_slash >= 0 && name_buf[last_slash] != '/')
	last_slash--;
    int first_dot = last_slash+1;
    while (first_dot < len && name_buf[first_dot] != '.')
	first_dot++;
    // Terminate
    name_buf[first_dot] = 0;
    name_tag = archive_string(name_buf+last_slash+1);
}

const char *generate_name(const char *suffix, bool increment) {
    if (increment)
	sequence_number++;
    snprintf(name_buf, SMAX-1, "reduction-%s-%d.%s", name_tag, sequence_number, suffix);
    const char *name = archive_string(name_buf);
    return name;
}



//  Logging information
// Establish a log file
void set_logname(const char *fname) {
    logfile_name = archive_string(fname);
    // Clear out whatever was there
    FILE *logfile = fopen(logfile_name, "w");
    if (logfile)
	fclose(logfile);
}


void set_verblevel(int level) {
    verblevel = level;
}

void set_panic(panic_function_t fun) {
    panic_function = fun;
}

void err(bool fatal, const char *fmt, ...) {
    if (!errfile)
	errfile = stdout;
    va_list ap;
    va_start(ap, fmt);
    if (fatal)
	fprintf(errfile, "c ERROR: ");
    else
	fprintf(errfile, "c WARNING: ");
    vfprintf(errfile, fmt, ap);
    fflush(errfile);
    va_end(ap);
    if (logfile_name) {
	FILE *logfile = fopen(logfile_name, "a");
	if (logfile) {
	    va_start(ap, fmt);
	    if (fatal)
		fprintf(logfile, "c ERROR: ");
	    else
		fprintf(logfile, "c WARNING: ");
	    vfprintf(logfile, fmt, ap);
	    va_end(ap);
	    fclose(logfile);
	}
    }
    if (fatal) {
	if (panic_function)
	    panic_function();
	exit(1);
    }
}

void report(int level, const char *fmt, ...) {
    if (!verbfile)
	verbfile = stdout;
    va_list ap;
    if (level <= verblevel) {
	fprintf(verbfile, "c ");
	va_start(ap, fmt);
	vfprintf(verbfile, fmt, ap);
	fflush(verbfile);
	va_end(ap);
	if (logfile_name) {
	    FILE *logfile = fopen(logfile_name, "a");
	    if (logfile) {
		fprintf(logfile, "c ");
		va_start(ap, fmt);
		vfprintf(logfile, fmt, ap);
		va_end(ap);
		fclose(logfile);
	    }
	}
    }
}

void lprintf(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    vfprintf(stdout, fmt, ap);
    fflush(stdout);
    va_end(ap);
    if (logfile_name) {
	FILE *logfile = fopen(logfile_name, "a");
	if (logfile) {
	    va_start(ap, fmt);
	    vfprintf(logfile, fmt, ap);
	    va_end(ap);
	    fclose(logfile);
	}
    }
}

void log_data(const char *fmt, ...) {
    va_list ap;
    if (datafile_name == NULL)
	return;
    FILE *datafile = fopen(datafile_name, "a");
    if (!datafile)
	return;
    va_start(ap, fmt);
    vfprintf(datafile, fmt, ap);
    va_end(ap);
    fclose(datafile);
}


double tod() {
    struct timeval tv;
    if (gettimeofday(&tv, NULL) == 0)
	return (double) tv.tv_sec + 1e-6 * tv.tv_usec;
    else
	return 0.0;
}

void start_timer() {
    start_time = tod();
}

double get_elapsed() {
    return tod() - start_time;
}

