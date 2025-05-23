# arithmetic.ml

## Overview

Number of statements: 2

`arithmetic.ml` defines and proves theorems related to arithmetic series. The file focuses on formalizing the concept of the sum of an arithmetic series. It provides definitions and theorems necessary for reasoning about and computing such sums within HOL Light.


## ARITHMETIC_PROGRESSION_LEMMA

### Name of formal statement
ARITHMETIC_PROGRESSION_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ARITHMETIC_PROGRESSION_LEMMA = prove
 (`!n. nsum(0..n) (\i. a + d * i) = ((n + 1) * (2 * a + n * d)) DIV 2`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THEN ARITH_TAC);;
```
### Informal statement
For all natural numbers `n`, the sum of the arithmetic progression with first term `a` and common difference `d`, from `i = 0` to `n`, is equal to `((n + 1) * (2 * a + n * d)) DIV 2`.

### Informal sketch
The proof proceeds by induction on `n`.

- Base case: When `n = 0`, the sum from `0` to `0` is just `a + d * 0 = a`. The right-hand side is `((0 + 1) * (2 * a + 0 * d)) DIV 2 = (1 * 2 * a) DIV 2 = a`.
- Inductive step: Assume the theorem holds for some `n`. We need to show it holds for `n + 1`.  That is, we assume `nsum(0..n) (\i. a + d * i) = ((n + 1) * (2 * a + n * d)) DIV 2`, and we want to prove that `nsum(0..n+1) (\i. a + d * i) = ((n + 2) * (2 * a + (n + 1) * d)) DIV 2`.
  - By the definition of `nsum`, `nsum(0..n+1) (\i. a + d * i) = nsum(0..n) (\i. a + d * i) + (a + d * (n + 1))`.
  - By the inductive hypothesis, this is equal to `((n + 1) * (2 * a + n * d)) DIV 2 + (a + d * (n + 1))`.
  - By arithmetic manipulation, we can show that `((n + 1) * (2 * a + n * d)) DIV 2 + (a + d * (n + 1)) = ((n + 2) * (2 * a + (n + 1) * d)) DIV 2`. This step uses integer division properties.

### Mathematical insight
This theorem provides a formula for the sum of an arithmetic progression. It is a fundamental result in elementary algebra and is essential for many applications in mathematics and computer science.

### Dependencies
- `NSUM_CLAUSES_NUMSEG` provides the recursive definition of `nsum` over a numeric segment.

### Porting notes (optional)
- The proof relies on the definition of `nsum` and basic arithmetic simplification, including integer division. Make sure the target proof assistant has similar definitional rules and arithmetic capabilities.
- The `ARITH_TAC` tactic in HOL Light is a powerful decision procedure for arithmetic. In other proof assistants, you may need to use more specific tactics to discharge the arithmetic goals.


---

## ARITHMETIC_PROGRESSION

### Name of formal statement
ARITHMETIC_PROGRESSION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ARITHMETIC_PROGRESSION = prove
 (`!n. 1 <= n
       ==> nsum(0..n-1) (\i. a + d * i) = (n * (2 * a + (n - 1) * d)) DIV 2`,
  INDUCT_TAC THEN REWRITE_TAC[ARITHMETIC_PROGRESSION_LEMMA; SUC_SUB1] THEN
  ARITH_TAC);;
```

### Informal statement
For all natural numbers `n`, if `n` is greater than or equal to 1, then the sum of the arithmetic progression with initial term `a` and common difference `d`, from `0` to `n-1`, is equal to `(n * (2 * a + (n - 1) * d)) DIV 2`.

### Informal sketch
The proof proceeds by induction on `n`.

- **Base Case:** `n = 1`. The summation `nsum(0..n-1) (\i. a + d * i)` reduces to `a`, and the right-hand side `(n * (2 * a + (n - 1) * d)) DIV 2` becomes `(1 * (2 * a + (1 - 1) * d)) DIV 2` which simplifies to `a`.

- **Inductive Step:** Assume the theorem holds for `n`; we must show it holds for `n+1`.
  The goal is to prove `nsum(0..n) (\i. a + d * i) = ((n+1) * (2 * a + n * d)) DIV 2`. This can be done applying the lemma `ARITHMETIC_PROGRESSION_LEMMA` to split the sum into the sum up to `n-1` plus the `n`th term, so that `nsum(0..n) (\i. a + d * i) = (nsum(0..n-1) (\i. a + d * i)) + (a + d * n)`. Apply the inductive hypothesis to replace `nsum(0..n-1) (\i. a + d * i)` with `(n * (2 * a + (n - 1) * d)) DIV 2`, and `SUC_SUB1` to simplify `n+1-1=n`. The rest is just arithmetic.

### Mathematical insight
This theorem provides a closed-form expression for the sum of an arithmetic progression. This is a fundamental result in number theory and is widely used in various mathematical contexts.

### Dependencies
- `ARITHMETIC_PROGRESSION_LEMMA`
- `SUC_SUB1`

### Porting notes (optional)
The `nsum` iterator, and the `DIV` operator will likely have different names or notations in other proof assistants. Pay close attention to the definition of `nsum` to ensure correctness. The `ARITH_TAC` is a powerful tactic in HOL Light, its behavior may needs to be mimicked by other methods or libraries in other proof assistants.


---

