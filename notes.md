---
title: CS 162 Notes (Winter 2017)
author: Justin Lubin
header-includes:
    - \usepackage{inconsolata}
geometry: margin=1in
---

# Asymptotic Analysis

## Big-Oh Notation

### Definition

We have that a function $f \in O(g(n))$ if and only if there exists constants
$c$ and $n_0$ such that $f(n) \leq c g(n)$ for all $n \geq n_0$.

We have that a function $f \in \Omega(g(n))$ if and only if there exists
constants $c$ and $n_0$ such that $f(n) \leq c g(n)$ for all $n \leq n_0$.

We have that a function $f \in \Theta(g(n))$ if and only if $f \in O(g(n))$
and $f \in \Omega(g(n))$.

This notation can be used to analyze the best-case, average-case, and
worse-case efficiency of an algorithm, but this class typically concerns the
worst-case efficiency of an algorithm.

Note that efficiency can be a measure of time, space, or even power complexity.

### Assumption: Constant Operations (Approximations)

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
To solve this, there are a couple methods.

## Methods of Asymptotic Analysis

### Method 1

Let $\frac{n}{2^k} = 1$, so then $k = \log n$. Then
\begin{align*}
T(n) &= 10 \log n + T\left(\frac{n}{2^{\log n}}\right) \\
&=  10 \log n + T(1) \\
&= 10 \log n + 10 \\
&\in O(\log n).
\end{align*}
However, this method actually gives you a big-theta approximation for $T$; in
other words, not only is $T \in O(\log n)$, we also have that $T \in
\Theta(\log n)$.

### Method 2 (Substitution Method)

Guess $O(?)$, then check. For example (in this case), guess $\log n$ because we
have something like $\frac{n}{2^n}$ in the formula. Then:
\begin{align*}
T(n) &= 10 + T(n/2) \\
&= 10 + \log (n/2)
\end{align*}
Because we have guessed that $T \in O(\log n)$, we have that $T(n) \leq c \log
n$ for all $n \geq n_0$, for some constants $c, n_0$.
\begin{align*}
T(n) &\leq c \log n \\
10 + \log (n/2) &\leq c \log n \\
10 + \log (n) - \log (2) &\leq c \log n \\
\frac{10 + \log (n) - \log (2)}{\log n} &\leq c \\
\frac{10}{\log n} + 1 - \frac{\log (2)}{\log n} &\leq c \\
\frac{10}{\log n} + 1 - \frac{1}{\log n} &\leq c
\end{align*}
Now take $n_0 = 2$, so $n \geq 2$ and thus $\log n \geq 1$ ($\log$ is base two).
We then have:
\begin{align*}
c \geq \frac{10}{1} + 1 - \frac{1}{1} \\
c \geq 10
\end{align*}
Therefore, $T \in O(\log n)$ because with $c = 10$ and $n_0 = 2$, we have
that $T(n) \leq c \log n$ for all $n \geq n_0$.

Note that the substituion
method is more general than *Method 1*, but it does *not* give you a big-theta
approximation (unlike *Method 1*).

### Examples

*Example 1*: $f(n) = 45 n \log n + 2n^2 + 65$. We will use the substitution
method, with a guess of $f \in O(n^2)$.
\begin{align*}
cn^2 &\geq 45n \log n + 2n^2 + 65 \\
c&\geq \frac{45n \log n + 2n^2 + 65}{n^2} \\
c&\geq \frac{45 \log n}{n} + 2 + \frac{65}{n^2} \\
\end{align*}

TODO

## The Towers of Hanoi

### Gameplay

The goal of the Towers of Hanoi is to move all disks to goal peg, with the
following rules:

- You can only move one disk at a time
- You can only move the top-most disk in a pile
- You cannot put a larger disk on top of a smaller one

### Algorithmic Solution

```
if n = 1:                                => T(1)
    move to goal (base case)                  = 1
else:                                    => T(n)
    move top n-1 disks to temporary peg       = T(n - 1)
    move bottom disk to goal                  + T(1)
    move the n-1 disks to goal                + T(n - 1)
```

Thus, $T(n) = T(n-1) + T(1) + T(n-1)$, with $T(1) = 1$. So:
\begin{align*}
T(n) &= 2T(n-1) + 1 \\
&= 2(2T(n-2) + 1) + 1 \\
&= 4T(n-2) + 3 \\
&= 4(2T(n-3) + 1) + 3 \\
&= 8T(n-3) + 7.
\end{align*}
By inspection, we have:
\begin{align*}
T(n) = 2^{n-1} T(1) + (2^{n-1} - 1),
\end{align*}
but $T(1) = 1$, so we have:
\begin{align*}
T(n) = 2^{n-1} + 2^{n-1} - 1, \\
&= 2^n - 1 \\
&\in \Theta(2^n).
\end{align*}
