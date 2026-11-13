#if !defined(_WIN32) && !defined(_POSIX_C_SOURCE)
#define _POSIX_C_SOURCE 200809L
#endif
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "sv_legality_shield.h"

#if defined(_WIN32)
#include <windows.h>
static double now_ns(void) {
  static LARGE_INTEGER freq;
  LARGE_INTEGER t;
  if (!freq.QuadPart) QueryPerformanceFrequency(&freq);
  QueryPerformanceCounter(&t);
  return (double)t.QuadPart * 1e9 / (double)freq.QuadPart;
}
#else
#include <time.h>
static double now_ns(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec * 1e9 + (double)ts.tv_nsec;
}
#endif

#if defined(__x86_64__) || defined(_M_X64)
#if defined(_MSC_VER)
#include <intrin.h>
#else
#include <x86intrin.h>
#endif
#define HAVE_TSC 1
static inline uint64_t ticks(void) {
  unsigned aux;
  return __rdtscp(&aux);
}
#else
#define HAVE_TSC 0
static inline uint64_t ticks(void) { return (uint64_t)now_ns(); }
#endif

#define BATCH 32

static double tick_ns;

static void calibrate(void) {
#if HAVE_TSC
  double t0 = now_ns();
  uint64_t c0 = ticks();
  while (now_ns() - t0 < 200e6) {
  }
  double t1 = now_ns();
  uint64_t c1 = ticks();
  tick_ns = (t1 - t0) / (double)(c1 - c0);
#else
  tick_ns = 1.0;
#endif
}

static int cmp_u64(const void *a, const void *b) {
  uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
  return (x > y) - (x < y);
}

typedef struct {
  double mean, p50, p99, p999, max_single, overhead;
} stats_t;

static volatile uint64_t sink;

static stats_t measure(int which, const shield_u64 *st, const shield_u64 *tx, size_t n, size_t rounds) {
  size_t batches = rounds;
  uint64_t *lat = (uint64_t *)malloc(batches * sizeof(uint64_t));
  uint64_t *single = (uint64_t *)malloc(batches * sizeof(uint64_t));
  uint64_t acc = 0, empty = (uint64_t)-1;
  for (int i = 0; i < 2000; ++i) {
    uint64_t a = ticks(), b = ticks();
    if (b - a < empty) empty = b - a;
  }
  double total_start = now_ns();
  size_t idx = 0;
  for (size_t r = 0; r < batches; ++r) {
    uint64_t t0 = ticks();
    for (int k = 0; k < BATCH; ++k) {
      size_t j = (idx + (size_t)k) % n;
      if (which == 0) {
        acc += (uint64_t)is_action_legal(st[j], tx[j]);
      } else {
        shield_u64 rep, masks[SHIELD_MASK_WORDS];
        acc += (uint64_t)project_or_mask_action(st[j], tx[j], &rep, masks) + rep;
      }
    }
    uint64_t t1 = ticks();
    lat[r] = (t1 - t0) / BATCH;
    size_t j = idx % n;
    uint64_t a = ticks();
    if (which == 0) {
      acc += (uint64_t)is_action_legal(st[j], tx[j]);
    } else {
      shield_u64 rep, masks[SHIELD_MASK_WORDS];
      acc += (uint64_t)project_or_mask_action(st[j], tx[j], &rep, masks) + rep;
    }
    uint64_t b = ticks();
    single[r] = (b - a) > empty ? (b - a) - empty : 0;
    idx += BATCH;
  }
  double total = now_ns() - total_start;
  sink = acc;
  qsort(lat, batches, sizeof(uint64_t), cmp_u64);
  qsort(single, batches, sizeof(uint64_t), cmp_u64);
  stats_t s;
  s.mean = total / (double)(batches * (BATCH + 1));
  s.p50 = lat[batches / 2] * tick_ns;
  s.p99 = lat[(size_t)(batches * 0.99)] * tick_ns;
  s.p999 = lat[(size_t)(batches * 0.999)] * tick_ns;
  s.max_single = single[batches - 1] * tick_ns;
  s.overhead = empty * tick_ns;
  free(lat);
  free(single);
  return s;
}

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr, "usage: shield_bench samples.bin [rounds]\n");
    return 2;
  }
  size_t rounds = argc > 2 ? (size_t)strtoull(argv[2], NULL, 10) : 200000;
  FILE *f = fopen(argv[1], "rb");
  if (!f) {
    fprintf(stderr, "cannot open %s\n", argv[1]);
    return 2;
  }
  fseek(f, 0, SEEK_END);
  long sz = ftell(f);
  fseek(f, 0, SEEK_SET);
  size_t n = (size_t)sz / 16;
  shield_u64 *buf = (shield_u64 *)malloc((size_t)sz);
  if (fread(buf, 16, n, f) != n) return 2;
  fclose(f);
  shield_u64 *st = (shield_u64 *)malloc(n * sizeof(shield_u64));
  shield_u64 *tx = (shield_u64 *)malloc(n * sizeof(shield_u64));
  for (size_t i = 0; i < n; ++i) {
    st[i] = buf[2 * i];
    tx[i] = buf[2 * i + 1];
  }
  calibrate();
  stats_t a = measure(0, st, tx, n, rounds / 10);
  a = measure(0, st, tx, n, rounds);
  stats_t b = measure(1, st, tx, n, rounds);
  printf("{\"samples\": %zu, \"rounds\": %zu, \"batch\": %d, \"tsc\": %d, \"timer_overhead_ns\": %.2f,\n", n, rounds, BATCH, HAVE_TSC, a.overhead);
  printf(" \"is_action_legal\": {\"mean_ns\": %.2f, \"p50_ns\": %.2f, \"p99_ns\": %.2f, \"p999_ns\": %.2f, \"max_single_ns\": %.2f},\n", a.mean, a.p50, a.p99, a.p999, a.max_single);
  printf(" \"project_or_mask_action\": {\"mean_ns\": %.2f, \"p50_ns\": %.2f, \"p99_ns\": %.2f, \"p999_ns\": %.2f, \"max_single_ns\": %.2f}}\n", b.mean, b.p50, b.p99, b.p999, b.max_single);
  free(buf);
  free(st);
  free(tx);
  return 0;
}
