#include <limits.h>
#include <stdbool.h>
#include "counters.h"
#include "report.h"

typedef struct {
    int min;
    int max;
    long count;
    double total;
} histo_info_t;

static long counters[COUNT_NUM];
static double timers[TIME_NUM];
static histo_info_t histograms[HISTO_NUM];

static bool initialized = false;

static void test_init() {
    if (initialized)
	return;
    for (int c = 0; c < COUNT_NUM; c++)
	counters[c] = 0;
    for (int t = 0; t < TIME_NUM; t++)
	timers[t] = 0.0;
    for (int h = 0; h < HISTO_NUM; h++) {
	histograms[h].min = INT_MAX;
	histograms[h].max = INT_MIN;
	histograms[h].count = 0;
	histograms[h].total = 0.0;
    }
    initialized = true;
}

static bool counter_ok(counter_t counter) {
    test_init();
    bool ok = counter >= 0 && counter < COUNT_NUM;
    if (!ok)
	err(false, "Invalid counter number %d\n", (int) counter);
    return ok;
}

void clear_count(counter_t counter) {
    if (!counter_ok(counter))
	return;
    counters[counter] = 0;
}

void incr_count_by(counter_t counter, int val) {
    if (!counter_ok(counter))
	return;
    counters[counter] += val;
}

void incr_count(counter_t counter) {
    incr_count_by(counter, 1);
}

int get_count(counter_t counter) {
    if (!counter_ok(counter))
	return -1;
    return (int) counters[counter];
}

long get_long_count(counter_t counter) {
    if (!counter_ok(counter))
	return -1;
    return counters[counter];
}


static bool timer_ok(etimer_t timer) {
    test_init();
    bool ok = timer >= 0 && timer < TIME_NUM;
    if (!ok)
	err(false, "Invalid timer number %d\n", (int) timer);
    return ok;
}

void incr_timer(etimer_t timer, double secs) {
    if (!timer_ok(timer))
	return;
    timers[timer] += secs;
}

double get_timer(etimer_t timer) {
    if (!timer_ok(timer))
	return -1;
    return timers[timer];

}

static bool histo_ok(histogram_t histo) {
    test_init();
    bool ok = histo >= 0 && histo < HISTO_NUM;
    if (!ok)
	err(false, "Invalid histo number %d\n", (int) histo);
    return ok;
}

void incr_histo(histogram_t histo, int datum) {
    if (!histo_ok(histo))
	return;
    histograms[histo].count++;
    histograms[histo].total += datum;
    if (datum < histograms[histo].min)
	histograms[histo].min = datum;
    if (datum > histograms[histo].max)
	histograms[histo].max = datum;
}

int get_histo_min(histogram_t histo) {
    if (!histo_ok(histo))
	return INT_MAX;
    return histograms[histo].min;
}

int get_histo_max(histogram_t histo) {
    if (!histo_ok(histo))
	return INT_MAX;
    return histograms[histo].max;
}

long get_histo_count(histogram_t histo) {
    if (!histo_ok(histo))
	return INT_MAX;
    return histograms[histo].count;
}

double get_histo_avg(histogram_t histo) {
    if (!histo_ok(histo))
	return 0.0;
    if (histograms[histo].count == 0)
	return 0;
    return histograms[histo].total / histograms[histo].count;
}
