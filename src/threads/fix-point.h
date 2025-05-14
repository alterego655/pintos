#ifndef THREADS_FIXED_POINT_H
#define THREADS_FIXED_POINT_H

#include <stdint.h> // For int64_t

// --- Configuration ---
// Using 'Q' as the number of fractional bits.
// P + Q = 31 for a 32-bit signed integer (1 bit for sign).
// A common choice for Q in Pintos is 14.
#define FP_Q_BITS 14

typedef int fp_t;  /* Fixed-point number type */

// --- Derived Constants ---
// The scaling factor 'f', which is 1 << Q. This represents 1.0 in fixed-point.
#define FP_SCALING_FACTOR (1 << FP_Q_BITS)

// --- Conversion Macros ---

// Convert integer N to fixed-point: N * f
#define INT_TO_FP(n) ((n) * FP_SCALING_FACTOR)

// Convert fixed-point X to integer (rounding toward zero): X / f
#define FP_TO_INT_TRUNC(x) ((x) / FP_SCALING_FACTOR)

// Convert fixed-point X to integer (rounding to nearest):
// (X + f / 2) / f if X >= 0,
// (X - f / 2) / f if X <= 0.
#define FP_TO_INT_NEAREST(x) ((x) >= 0 ? \
                             ((x) + FP_SCALING_FACTOR / 2) / FP_SCALING_FACTOR : \
                             ((x) - FP_SCALING_FACTOR / 2) / FP_SCALING_FACTOR)

// --- Fixed-Point Arithmetic with two Fixed-Point Numbers ---

// Add fixed-point X and fixed-point Y: X + Y
#define ADD_FP_FP(x, y) ((x) + (y))

// Subtract fixed-point Y from fixed-point X: X - Y
#define SUB_FP_FP(x, y) ((x) - (y))

// Multiply fixed-point X by fixed-point Y: ((int64_t) X) * Y / f
// Cast to int64_t for intermediate multiplication to prevent overflow.
#define MUL_FP_FP(x, y) (int)(((int64_t)(x) * (y)) / FP_SCALING_FACTOR)

// Divide fixed-point X by fixed-point Y: ((int64_t) X) * f / Y
// Cast to int64_t for intermediate multiplication (X * f) to prevent overflow
// and preserve precision before division.
#define DIV_FP_FP(x, y) (int)(((int64_t)(x) * FP_SCALING_FACTOR) / (y))

// --- Fixed-Point Arithmetic with a Fixed-Point Number and an Integer ---

// Add fixed-point X and integer N: X + N * f
#define ADD_FP_INT(x, n) ((x) + (n) * FP_SCALING_FACTOR)

// Subtract integer N from fixed-point X: X - N * f
#define SUB_FP_INT(x, n) ((x) - (n) * FP_SCALING_FACTOR)

// Multiply fixed-point X by integer N: X * N
#define MUL_FP_INT(x, n) (int)(((int64_t)(x) * (n)))

// Divide fixed-point X by integer N: X / N
#define DIV_FP_INT(x, n) ((x) / (n))

#endif /* threads/fixed-point.h */
