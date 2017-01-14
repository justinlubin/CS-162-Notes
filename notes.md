---
title: CS 162 Notes (Winter 2017)
author: Justin Lubin
header-includes:
    - \usepackage{inconsolata}
geometry: margin=1.5in
---

# Asymptotic Analysis I

## Analyzing Code (Worst-Case)

### Constant Operations (Approximations)

- Arithmetic (fixed width)
- Assignment
- Access any array element

### Non-Constant Operations

| Control Flow           | Time                                     |
|------------------------|------------------------------------------|
| Consecutive statements | Sum of time of each statement            |
| Conditional            | Time of test + time of the slower branch |
| Loop                   | Number of iterations * time of body      |
| Function call          | Time of function body                    |
| Recursion              | Solve recurrence relation                |

## Reducing Big-O Expressions

### What to Eliminate

- Eliminate low-order terms
- Eliminate coefficients

### Examples

- $4n + 5 \in O(n)$
- $\frac{1}{2} n \log n + 2n + 7 \in O(n\log n)$
- $n^3 + 2^n + 3n \in O(2^n)$
- $n \log (10n^2) + 2n \log n \in O(n\log n)$
    - Note that $n \log (10n^2) = 2n \log(10n)$

## Linear Search

### Code

```c
int find(int[] arr, int arr_length, int k) {
    for (int i = 0; i < arr_length; ++i) {
        if (arr[i] == k) {
            return 1;
        }
    }
    return 0;
}
```

### Analysis

- Best case: approximately six steps
    - $O(1)$
- Worst case: $6 * \text{arr\_length}$ steps
    - $n = \text{arr\_length}$, so $O(n)$

## Binary Search

### Code

```c
int find(int[] arr, int k, int lo, int hi) {
    return help(arr, k, 0, arr_length);
}

int find(int[] arr, int arr_length, int k) {
    int mid = (hi + lo) / 2;
    if (lo == hi) {
        return 0;
    }
    if (arr[mid] == k) {
        return 1;
    }
    if (arr[mid] < k) {
        return help(arr, k, mid + 1, k);
    } else {
        return help(arr, k, lo, mid);
    }
}
```

### Analysis

Let $T(n)$ be the efficiency of \texttt{find}. Then, because each split takes
approximately ten operations, we have that:

\begin{align*}
T(n) &= 10 + T\left(\frac{n}{2}\right) \\
&= 10 + \left(10 + T\left(\frac{n}{4}\right)\right) \\
&= 10 + \left(10 + \left(10 + T\left(\frac{n}{8}\right)\right)\right) \\
&= 10k + T\left(\frac{n}{2^k}\right).
\end{align*}
