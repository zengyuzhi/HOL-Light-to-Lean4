# perfect.ml

## Overview

Number of statements: 18

The file `perfect.ml` formalizes the theory of perfect numbers within HOL Light. It builds upon the primality theory defined in `prime.ml` to define perfect numbers and prove related theorems. The file likely contains definitions related to divisors and theorems characterizing or relating to perfect numbers.


## sigma

### Name of formal statement
sigma

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let sigma = new_definition
 `sigma(n) = if n = 0 then 0 else nsum {d | d divides n} (\i. i)`;;
```

### Informal statement
The function `sigma` of `n` is defined as follows: if `n` is equal to 0, then `sigma(n)` is 0; otherwise, `sigma(n)` is the sum, over all `d` that divide `n`, of the function that maps `i` to `i`. In other words, `sigma(n)` is the sum of all divisors of `n` when `n` is not 0, and 0 when `n` is 0.

### Informal sketch
The definition of the `sigma` function is straightforward:

- If the input `n` is 0, return 0.
- Otherwise, compute the set of divisors of `n`.
- Calculate the sum of the elements in the divisor set, which is the sum of the divisors of `n`.

### Mathematical insight
The `sigma` function computes the sum of the divisors of a given integer. It is a fundamental function in number theory, especially in the study of perfect numbers, amicable numbers, and other related concepts. It is often denoted as σ(n) in mathematical literature.

### Dependencies
- Requires `Library/prime.ml`, as indicated by `needs "Library/prime.ml";;`
- Definition: `divides` (used in the set comprehension `{d | d divides n}`)
- Definition: `nsum` (used to sum over the set of divisors)


---

## perfect

### Name of formal statement
perfect

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let perfect = new_definition
 `perfect n <=> ~(n = 0) /\ sigma(n) = 2 * n`;;
```

### Informal statement
For any natural number *n*, `perfect n` is true if and only if *n* is not equal to 0 and the sum of the divisors of *n*, denoted by `sigma(n)`, is equal to 2 times *n*.

### Informal sketch
- The definition introduces the concept of a perfect number.
- It states that a number `n` is perfect if it is a positive number and the sum of its divisors is equal to twice the number itself.
- The definition uses the negation of equality to zero (`~(n = 0)`) to ensure the number is positive.
- The definition relies on the function `sigma(n)` which calculates the sum of divisors of n.

### Mathematical insight
This definition captures the standard mathematical notion of a perfect number. A perfect number is a positive integer that is equal to the sum of its proper divisors (i.e., the sum of its divisors excluding the number itself). The definition given here uses the `sigma` function, which includes the number itself in the sum of divisors, hence the condition `sigma(n) = 2 * n`.

### Dependencies
- Definitions: `sigma`


---

## ODD_POW2_MINUS1

### Name of formal statement
ODD_POW2_MINUS1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ODD_POW2_MINUS1 = prove
 (`!k. ~(k = 0) ==> ODD(2 EXP k - 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `EVEN(2 EXP k) <=> EVEN((2 EXP k - 1) + 1)` MP_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[ARITH_RULE `k = k - 1 + 1 <=> ~(k = 0)`] THEN
    REWRITE_TAC[EXP_EQ_0; ARITH];
    ASM_REWRITE_TAC[GSYM NOT_EVEN; EVEN_ADD; EVEN_EXP; ARITH]]);;
```
### Informal statement
For all natural numbers `k`, if `k` is not equal to `0`, then `2` to the power of `k` minus `1` is odd.

### Informal sketch
The proof proceeds by induction-free, equational reasoning, using standard arithmetic lemmas:
- Start by stripping the goal.
- Reduce the goal to proving `EVEN(2 EXP k)` is equivalent to `EVEN((2 EXP k - 1) + 1)`.
- Consider the case when `k` is not `0`; rewrite `k` as `k - 1 + 1`; simplify `2 EXP k` to `2 EXP (k - 1 + 1)` which is equal to `2 * (2 EXP (k - 1))`.
- Assume `k` is not `0`; rewrite using `NOT_EVEN`; `EVEN_ADD`; `EVEN_EXP`, showing that `2 EXP k - 1` is odd.

### Mathematical insight
This theorem states a basic but useful property of number theory. It's a special case for how powers of 2 relate to odd numbers. Namely, that subtracting 1 from a positive power of 2 always yields an odd number.

### Dependencies
- Arithmetic: `ARITH`
- Theorems: `EXP_EQ_0`, `NOT_EVEN`, `EVEN_ADD`, `EVEN_EXP`
- Tacticals: `REPEAT`, `STRIP_TAC`, `SUBGOAL_THEN`, `MP_TAC`, `AP_TERM_TAC`, `REWRITE_TAC`, `ASM_REWRITE_TAC`, `GSYM`


---

## EVEN_ODD_DECOMP

### Name of formal statement
EVEN_ODD_DECOMP

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EVEN_ODD_DECOMP = prove
 (`!n. ~(n = 0) ==> ?r s. ODD s /\ n = 2 EXP r * s`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  MP_TAC(SPEC `n:num` EVEN_OR_ODD) THEN
  REWRITE_TAC[EVEN_EXISTS; ODD_EXISTS] THEN
  DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `m:num` SUBST_ALL_TAC)) THENL
   [DISCH_THEN(MP_TAC o SPEC `m:num`) THEN
    REWRITE_TAC[MULT_EQ_0; ARITH; ARITH_RULE `m < 2 * m <=> ~(m = 0)`] THEN
    ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `s:num` THEN DISCH_THEN(X_CHOOSE_TAC `r:num`) THEN
    EXISTS_TAC `SUC r` THEN ASM_REWRITE_TAC[EXP; GSYM MULT_ASSOC];
    REPEAT(DISCH_THEN(K ALL_TAC)) THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[EXP; MULT_CLAUSES] THEN MESON_TAC[]]);;
```

### Informal statement
For all natural numbers `n`, if `n` is not equal to 0, then there exist natural numbers `r` and `s` such that `s` is odd and `n` is equal to `2` to the power of `r` times `s`.

### Informal sketch
The proof proceeds by induction on `n`.

- Base case: When `n` is not 0, we apply `EVEN_OR_ODD` to `n`:
  - Case 1: If `n` is even, then there exists an `m` such that `n = 2 * m`. If `m = 0`, then `n = 0`, which contradicts the assumption `~(n = 0)`. Thus, `m` is not 0. We then decompose `m` into `2 EXP r * s` for some `r` and odd `s`. Thus we have `n = 2 * (2 EXP r * s) = 2 EXP (SUC r) * s`.
  - Case 2: If `n` is odd, we can take `r = 0` and `s = n`, thus `n = 2 EXP 0 * n = 1 * n = n`.

### Mathematical insight
This theorem states that every non-zero natural number can be uniquely represented as a power of 2 multiplied by an odd number. This is a fundamental result in number theory.

### Dependencies
- Theorems: `EVEN_OR_ODD`, `EVEN_EXISTS`, `ODD_EXISTS`, `MULT_EQ_0`, `ARITH`, `SWAP_EXISTS_THM`, `MONO_EXISTS`, `EXP`, `MULT_ASSOC`, `MULT_CLAUSES`
- Tactics: `MATCH_MP_TAC`, `X_GEN_TAC`, `MP_TAC`, `SPEC`, `REWRITE_TAC`, `DISCH_THEN`, `DISJ_CASES_THEN`, `X_CHOOSE_THEN`, `SUBST_ALL_TAC`, `ASM_CASES_TAC`, `ASM_REWRITE_TAC`, `ONCE_REWRITE_TAC`, `EXISTS_TAC`, `K`, `ALL_TAC`, `MESON_TAC`

### Porting notes (optional)
This theorem relies heavily on rewriting and arithmetic simplification. Automated tactics like `MESON_TAC` are used. Ensure that the target proof assistant has similar capabilities for automated reasoning about arithmetic. The tactics `X_GEN_TAC` and `X_CHOOSE_TAC` suggest a need for explicit variable naming control during existential quantifier instantiation. You may need to explicitly manage variable names when porting.


---

## FINITE_DIVISORS

### Name of formal statement
FINITE_DIVISORS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FINITE_DIVISORS = prove
 (`!n. ~(n = 0) ==> FINITE {d | d divides n}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{d | d <= n}` THEN REWRITE_TAC[FINITE_NUMSEG_LE] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[DIVIDES_LE]);;
```

### Informal statement
For all `n`, if `n` is not equal to 0, then the set of all `d` such that `d` divides `n` is finite.

### Informal sketch
The proof demonstrates that for any non-zero number `n`, the set of its divisors is finite.
- Start by assuming `n` is not zero.
- Instantiate the theorem `FINITE_SUBSET`, which states that a subset of a finite set is finite, to show the goal.
- Show that all divisors `d` of `n` are contained in the finite set `{d | d <= n}` .
- Establish `{d | d <= n}` is finite by rewriting with `FINITE_NUMSEG_LE`, which states that the segment of natural numbers less than or equal to `n` is finite.
- Prove the subset relation `{d | d divides n} SUBSET {d | d <= n}` by showing that if `d` divides `n` then `d <= n`.
- Use `DIVIDES_LE` to prove that if `d` divides `n`, then `d` must be less than or equal to `n`.

### Mathematical insight
The theorem formalizes the basic mathematical fact that any non-zero integer has a finite number of divisors. This is a fundamental property used in number theory. The proof relies on the fact that any divisor `d` of `n` must be less than or equal to `n`, hence the set of divisors is a subset of the finite set `{1, 2, ..., n}`.

### Dependencies
- Theorems: `FINITE_SUBSET`, `FINITE_NUMSEG_LE`, `IN_ELIM_THM`, `DIVIDES_LE`, `SUBSET`


---

## MULT_EQ_COPRIME

### Name of formal statement
MULT_EQ_COPRIME

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MULT_EQ_COPRIME = prove
 (`!a b x y. a * b = x * y /\ coprime(a,x)
             ==> ?d. y = a * d /\ b = x * d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:num`; `x:num`; `y:num`] COPRIME_DIVPROD) THEN
  MP_TAC(SPECL [`x:num`; `a:num`; `b:num`] COPRIME_DIVPROD) THEN
  REPEAT(ANTS_TAC THENL
   [ASM_MESON_TAC[DIVIDES_REFL; DIVIDES_RMUL; COPRIME_SYM];
    REWRITE_TAC[divides] THEN STRIP_TAC]) THEN
  UNDISCH_TAC `a * b = x * y` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE
    `(a * x * u = x * a * v) <=> (a * x) * u = (a * x) * v`] THEN
  REWRITE_TAC[EQ_MULT_LCANCEL; MULT_EQ_0] THEN ASM_MESON_TAC[]);;
```
### Informal statement
For all natural numbers `a`, `b`, `x`, and `y`, if `a * b = x * y` and `a` and `x` are coprime, then there exists a natural number `d` such that `y = a * d` and `b = x * d`.

### Informal sketch
The proof proceeds as follows:
- Assume `a * b = x * y` and `coprime(a, x)`.
- By `COPRIME_DIVPROD` (twice), `a` divides `y` and `x` divides `b`.
- Thus, there exist `u` and `v` such that `y = a * u` and `b = x * v`. This involves rewriting using the definition of `divides`.
- Substitute `y = a * u` and `b = x * v` into `a * b = x * y` to get `a * (x * v) = x * (a * u)`.
- Rewrite this to `(a * x) * v = (a * x) * u`.
- By `EQ_MULT_LCANCEL` and `MULT_EQ_0`, deduce that `u = v`.
- Thus, there exists a `d` equal to `u` (or `v`) such that `y = a * d` and `b = x * d`.

### Mathematical insight
This theorem states that if `a * b = x * y` and `a` and `x` are coprime, then `a` and `x` are the "coprime parts" of `y` and `b` respectively. It is a useful result in number theory concerning divisibility and coprime numbers.

### Dependencies
- `COPRIME_DIVPROD`
- `DIVIDES_REFL`
- `DIVIDES_RMUL`
- `COPRIME_SYM`
- `divides`
- `EQ_MULT_LCANCEL`
- `MULT_EQ_0`


---

## COPRIME_ODD_POW2

### Name of formal statement
COPRIME_ODD_POW2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COPRIME_ODD_POW2 = prove
 (`!k n. ODD(n) ==> coprime(2 EXP k,n)`,
  SIMP_TAC[coprime; PRIME_2; DIVIDES_PRIMEPOW] THEN REWRITE_TAC[divides] THEN
  REPEAT STRIP_TAC THEN UNDISCH_TAC `ODD n` THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[ODD_MULT; ODD_EXP; ARITH]);;
```

### Informal statement
For all natural numbers `k` and `n`, if `n` is odd, then `2` raised to the power of `k` is coprime to `n`.

### Informal sketch
The proof proceeds as follows:
- Assume `n` is odd.
- By the definition of `coprime`, we need to show that the greatest common divisor of `2 EXP k` and `n` is 1.
- From `PRIME_2` we know that `2` is prime.
- By `DIVIDES_PRIMEPOW`, if some number divides `2 EXP k`, then it must be some power of 2, i.e. `2 EXP i` for some `i <= k`.
- We then show that no power of 2 (except 1) can divide `n` if `n` is odd. This follows by contradiction, assuming that some `2 EXP i` divides `n`.
- We use the properties that the product of odd numbers `ODD_MULT` is odd and that the exponentiation of an odd number `ODD_EXP` is odd.
- Finally, we apply arithmetic reasoning (`ARITH`) to complete the proof.

### Mathematical insight
This theorem states a basic but useful property in number theory: powers of 2 are coprime to odd numbers. It formalizes the intuitive idea that odd numbers, by definition, do not share any prime factors with powers of 2. This result is often used in simplifying expressions and proving other theorems in number theory.

### Dependencies
- Definitions: `coprime`
- Theorems: `PRIME_2`, `DIVIDES_PRIMEPOW`, `ODD_MULT`, `ODD_EXP`
- Basic Rewrites: `divides`


---

## MULT_NSUM

### Name of formal statement
MULT_NSUM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MULT_NSUM = prove
 (`!s t. FINITE s /\ FINITE t
         ==> nsum s f * nsum t g =
             nsum {(x:A,y:B) | x IN s /\ y IN t} (\(x,y). f(x) * g(y))`,
  SIMP_TAC[GSYM NSUM_NSUM_PRODUCT; NSUM_LMUL; NSUM_RMUL]);;
```
### Informal statement
For all sets `s` and `t`, if `s` is a finite set and `t` is a finite set, then the product of the sum over `s` of `f(x)` and the sum over `t` of `g(y)` is equal to the sum over the set of pairs `(x, y)` such that `x` is in `s` and `y` is in `t` of `f(x) * g(y)`.

### Informal sketch
The proof proceeds as follows:
- It uses the theorem `GSYM NSUM_NSUM_PRODUCT` to rewrite the right-hand side.  `NSUM_NSUM_PRODUCT` likely expresses a bi-directional equality related to the product of sums over two sets of pairs, converting a double summation into a product of two summations. Applying `GSYM` reverses the direction of the mentioned rewrite rule.
- It applies `NSUM_LMUL` which states that summing `c * f(x)` is the same as `c * nsum(f(x))`
- It applies `NSUM_RMUL` which states that summing `f(x) * c` is the same as `nsum(f(x)) * c`

### Mathematical insight
The theorem establishes a fundamental relationship between the product of sums and the sum of products over the Cartesian product of two finite sets. This reflects the distributive property linking multiplication and addition, extended to finite summations over sets. It formalizes the straightforward intuition that multiplying two sums is equivalent to summing all possible products of terms from each sum.

### Dependencies
- `GSYM NSUM_NSUM_PRODUCT`
- `NSUM_LMUL`
- `NSUM_RMUL`


---

## SIGMA_0

### Name of formal statement
SIGMA_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SIGMA_0 = prove
 (`sigma 0 = 0`,
  REWRITE_TAC[sigma]);;
```
### Informal statement
The sum of divisors of 0 is equal to 0; that is, `sigma 0 = 0`.

### Informal sketch
The theorem `SIGMA_0` is proved by rewriting the term `sigma 0` using the definition of the `sigma` function.

### Mathematical insight
The `sigma` function calculates the sum of all positive divisors of a given number. Since 0 has no positive divisors, the sum is 0. This is a base case or edge case that needs to be handled correctly when defining or working with the sigma function.

### Dependencies
- Definition: `sigma`


---

## SIGMA_1

### Name of formal statement
SIGMA_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SIGMA_1 = prove
 (`sigma(1) = 1`,
  REWRITE_TAC[sigma; DIVIDES_ONE; SET_RULE `{d | d = 1} = {1}`] THEN
  REWRITE_TAC[ARITH; NSUM_SING]);;
```
### Informal statement
The sum of divisors of 1, denoted by `sigma(1)`, is equal to 1.

### Informal sketch
The proof proceeds as follows:
- By definition of the `sigma` function (sum of divisors) and the fact that the only divisor of 1 is 1 itself (`DIVIDES_ONE`, `SET_RULE `{d | d = 1} = {1}``), we can rewrite `sigma(1)` as the sum of the set containing only 1.
- The sum over a singleton set containing 1 is simply 1 (`ARITH`, `NSUM_SING`).

### Mathematical insight
This theorem captures the base case for the divisor sum function. It states that the only divisor of 1 is 1, hence the sum of all divisors of 1 is 1. This is a fundamental property in number theory.

### Dependencies
- Definitions: `sigma`
- Theorems: `DIVIDES_ONE`, `SET_RULE `{d | d = 1} = {1}`, `ARITH`, `NSUM_SING`


---

## SIGMA_LBOUND

### Name of formal statement
SIGMA_LBOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SIGMA_LBOUND = prove
 (`!n. 1 < n ==> n + 1 <= sigma(n)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `1 < n ==> ~(n = 0)`)) THEN
  ASM_REWRITE_TAC[sigma] THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `nsum {1,n} (\i. i)` THEN CONJ_TAC THENL
   [SIMP_TAC[NSUM_CLAUSES; FINITE_RULES; IN_SING; NOT_IN_EMPTY] THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC NSUM_SUBSET_SIMPLE THEN ASM_SIMP_TAC[FINITE_DIVISORS] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; NOT_IN_EMPTY; IN_INSERT] THEN
    MESON_TAC[DIVIDES_1; DIVIDES_REFL]]);;
```
### Informal statement
For all natural numbers `n`, if `1 < n` then `n + 1` is less than or equal to the sum of the divisors of `n`.

### Informal sketch
The proof proceeds by induction on `n`.

- We assume `1 < n` and aim to prove `n + 1 <= sigma(n)`.
- First, we use the fact that `1 < n` implies `~(n = 0)`.
- We expand `sigma(n)` using its definition.
- We use `LE_TRANS` to reduce the goal to showing that `n+1` is less or equal to the sum of `i` from 1 to `n` over the divisors of `n`.
- We show that `n+1 <= nsum {1,n} (\i. i)` i.e. the sum of the numbers from 1 to n.
- We show that the sets of divisors are in `{1,n}`.
- We simplify using the definition of `nsum` with properties like `NSUM_CLAUSES`, `FINITE_RULES`, `IN_SING`, and `NOT_IN_EMPTY`.
- We use arithmetic to simplify the base case.
- We use `NSUM_SUBSET_SIMPLE` to rewrite the `nsum` over divisors subset and simplify with `FINITE_DIVISORS`.
- We then rewrite the goal in terms of `SUBSET`, `IN_ELIM_THM`, `NOT_IN_EMPTY`, and `IN_INSERT`.
- Finally, we discharge the goal using a decision procedure (`MESON_TAC`) and known facts about divisibility, such as `DIVIDES_1` and `DIVIDES_REFL`.

### Mathematical insight
This theorem establishes a lower bound on the sum of the divisors of a natural number `n` greater than 1. It states that the sum of divisors `sigma(n)` is always at least `n + 1`. The divisors of `n` always includes 1 and n. Thus,`sigma(n)` must be at least `1 + n`.

### Dependencies
- `sigma` (definition of the sum of divisors function)
- `ARITH_RULE !n. 1 < n ==> ~(n = 0)`
- `LE_TRANS`
- `NSUM_CLAUSES`
- `FINITE_RULES`
- `IN_SING`
- `NOT_IN_EMPTY`
- `NSUM_SUBSET_SIMPLE`
- `FINITE_DIVISORS`
- `SUBSET`
- `IN_ELIM_THM`
- `IN_INSERT`
- `DIVIDES_1`
- `DIVIDES_REFL`


---

## SIGMA_MULT

### Name of formal statement
SIGMA_MULT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SIGMA_MULT = prove
 (`!a b. 1 < a /\ 1 < b ==> 1 + b + a * b <= sigma(a * b)`,
  REPEAT STRIP_TAC THEN
  EVERY_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `1 < n ==> ~(n = 0)`)) THEN
  ASM_REWRITE_TAC[sigma] THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `nsum {1,b,a*b} (\i. i)` THEN CONJ_TAC THENL
   [SIMP_TAC[NSUM_CLAUSES; FINITE_RULES; IN_INSERT; NOT_IN_EMPTY] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `x = a * b <=> a * b = 1 * x`] THEN
    ASM_REWRITE_TAC[EQ_MULT_RCANCEL] THEN
    REWRITE_TAC[MULT_CLAUSES; MULT_EQ_1] THEN
    ASM_ARITH_TAC;
    ASM_REWRITE_TAC[MULT_EQ_0] THEN
    MATCH_MP_TAC NSUM_SUBSET_SIMPLE THEN
    ASM_SIMP_TAC[FINITE_DIVISORS; MULT_EQ_0] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; NOT_IN_EMPTY; IN_INSERT] THEN
    MESON_TAC[DIVIDES_1; DIVIDES_REFL; DIVIDES_LMUL]]);;
```

### Informal statement
For all natural numbers `a` and `b`, if `1 < a` and `1 < b`, then `1 + b + a * b` is less than or equal to the sum of all divisors of `a * b`.

### Informal sketch
The proof proceeds by assuming `1 < a` and `1 < b` and aims to show that `1 + b + a * b <= sigma(a * b)`.

- The proof starts by stripping the quantifiers and assumptions using `REPEAT STRIP_TAC`.
- It uses the fact that if `1 < n` then `~(n = 0)`, by applying `EVERY_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE '1 < n ==> ~(n = 0)'))`
- Then we rewrite using the definition of `sigma` function `sigma(n) = nsum divisors(n) (\d. d)` by applying `ASM_REWRITE_TAC[sigma]`
- Show that `1 + b + a * b` is less than or equal to the sum of divisors of `a * b` by providing an explicit enumeration of the divisors: `EXISTS_TAC 'nsum {1,b,a*b} (\i. i)'`
- The goal is then split into two subgoals:
  - Prove that `nsum {1,b,a*b} (\i. i) = 1 + b + a * b` using `SIMP_TAC[NSUM_CLAUSES; FINITE_RULES; IN_INSERT; NOT_IN_EMPTY]`. Further simplification involves rewriting `x = a * b` to `a * b = 1 * x` by applying `ONCE_REWRITE_TAC[ARITH_RULE 'x = a * b <=> a * b = 1 * x']`, then canceling `a * b` using `ASM_REWRITE_TAC[EQ_MULT_RCANCEL]` and simplifying the remaining expression with rewriting rules for multiplication `REWRITE_TAC[MULT_CLAUSES; MULT_EQ_1]` and using arithmetic tactics `ASM_ARITH_TAC`.
  - Prove that the set `{1, b, a * b}` is a subset of the divisors of `a * b`.  This is achieved by rewriting with `MULT_EQ_0`, applying `NSUM_SUBSET_SIMPLE`, simplifying with `FINITE_DIVISORS` and `MULT_EQ_0`. We rewrite the goal with set rewriting rules `REWRITE_TAC[SUBSET; IN_ELIM_THM; NOT_IN_EMPTY; IN_INSERT]` and finally prove it using a MESON proof search, providing the divisibility rules.

### Mathematical insight
The theorem provides a lower bound on the divisor sum function `sigma(n)`. It leverages the fact that 1, `b`, and `a * b` are divisors of `a * b` when `1 < a` and `1 < b`.  The inequality is useful in number theory and other areas where divisor functions are studied.

### Dependencies
- `sigma`
- `NSUM_CLAUSES`
- `FINITE_RULES`
- `IN_INSERT`
- `NOT_IN_EMPTY`
- `EQ_MULT_RCANCEL`
- `MULT_CLAUSES`
- `MULT_EQ_1`
- `MULT_EQ_0`
- `NSUM_SUBSET_SIMPLE`
- `FINITE_DIVISORS`
- `SUBSET`
- `IN_ELIM_THM`
- `DIVIDES_1`
- `DIVIDES_REFL`
- `DIVIDES_LMUL`


---

## SIGMA_PRIME

### Name of formal statement
SIGMA_PRIME

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SIGMA_PRIME = prove
 (`!p. prime(p) ==> sigma(p) = p + 1`,
  GEN_TAC THEN
  ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[PRIME_0; SIGMA_0; ARITH] THEN
  ASM_CASES_TAC `p = 1` THEN ASM_REWRITE_TAC[PRIME_1; SIGMA_1; ARITH] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[sigma] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `nsum {1,p} (\i. i)` THEN
  CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[prime; DIVIDES_1; DIVIDES_REFL];
    ASM_SIMP_TAC[NSUM_CLAUSES; IN_SING; FINITE_RULES; NOT_IN_EMPTY] THEN
    ARITH_TAC]);;
```

### Informal statement
For all `p`, if `p` is prime, then the sum of the divisors of `p` is equal to `p + 1`.

### Informal sketch
The proof proceeds by cases and rewriting.
- First, the cases `p = 0` and `p = 1` are eliminated by rewriting with theorems `PRIME_0`, `SIGMA_0`, `ARITH` and `PRIME_1`, `SIGMA_1`, `ARITH`, respectively.
- Then, assuming `p` is prime and not equal to 0 or 1, the theorem `sigma` is rewritten, and equality transitivity is used to show that the sum of divisors is expressed as the sum of elements in the set `{1, p}`.
- Finally, the proof proceeds by demonstrating that this set is exactly the set of divisors of `p`, and evaluates the sum of divisors using `nsum`.
  - The theorem stating that the set of divisors are `{1, p}` is proven using rewriting with set extensionality, `IN_ELIM_THM`, `IN_INSERT`, `NOT_IN_EMPTY`, and `ASM_MESON_TAC` is used with theorems `prime`, `DIVIDES_1` and `DIVIDES_REFL`.
  - Computing the sum `nsum {1,p} (\i. i)` simplifies to `p + 1` using theorems regarding `NSUM`, `IN_SING`, `FINITE_RULES`, `NOT_IN_EMPTY`.

### Mathematical insight
This theorem states a fundamental property of prime numbers: their only divisors are 1 and themselves. Therefore, the sum of their divisors is simply 1 plus the prime number. This is a basic result in number theory.

### Dependencies
- Definitions: `sigma`, `prime`
- Theorems: `PRIME_0`, `SIGMA_0`, `ARITH`, `PRIME_1`, `SIGMA_1`, `sigma`, `EQ_TRANS`, `EXTENSION`, `IN_ELIM_THM`, `IN_INSERT`, `NOT_IN_EMPTY`, `DIVIDES_1`, `DIVIDES_REFL`, `NSUM_CLAUSES`, `IN_SING`, `FINITE_RULES`


---

## SIGMA_PRIME_EQ

### Name of formal statement
SIGMA_PRIME_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SIGMA_PRIME_EQ = prove
 (`!p. prime(p) <=> sigma(p) = p + 1`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[SIGMA_PRIME] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[prime; DE_MORGAN_THM] THEN
  ASM_CASES_TAC `p = 1` THEN ASM_REWRITE_TAC[SIGMA_1; ARITH] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; divides; DE_MORGAN_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num` SUBST_ALL_TAC) THEN
  MP_TAC(SPECL [`a:num`; `b:num`] SIGMA_MULT) THEN
  ASM_CASES_TAC `a = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; SIGMA_0; ARITH] THEN
  ASM_CASES_TAC `b = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; SIGMA_0; ARITH] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[MULT_EQ_1] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `a = a * b <=> a * b = a * 1`] THEN
  REWRITE_TAC[EQ_MULT_LCANCEL] THEN ARITH_TAC);;
```

### Informal statement
For all natural numbers `p`, `p` is prime if and only if the sum of the divisors of `p` is equal to `p + 1`.

### Informal sketch
The proof proceeds as follows:
- Expand the definition of `sigma` using `SIGMA_PRIME`.
- Show the contrapositive and rewrite the goal to `~(prime p) <=> ~(sigma p = p + 1)`.
- Expand the definition of `prime` and apply De Morgan's law. The goal is now `(p = 1) \/ (EX a. divides a p /\ ~(a = 1) /\ ~(a = p)) <=> ~(sigma p = p + 1)`.
- Case split on `p = 1`.
  - If `p = 1`, then simplify using the definition of `SIGMA_1` to get `sigma(1) = 1`, and then use arithmetic to simplify the equation.
- Assume `~(p = 1)`.
- Rewrite using the definitions of `NOT_FORALL_THM`, `NOT_IMP`, `divides` and `DE_MORGAN_THM`, and discharge assumptions.
- Use the witness `a` such that `divides a p /\ ~(a = 1) /\ ~(a = p)`.
- Similarly, use a witness `b` such that `a * b = p`.
- Instantiate the theorem `SIGMA_MULT` with `a` and `b`.
- Perform case splits on `a = 0` and `b = 0` and simplify using `SIGMA_0`, `MULT_CLAUSES` and arithmetic.
- Eliminate assumptions via `POP_ASSUM`.
- Use `MULT_EQ_1` to show `a = 1 /\ b = 1`.
- Rewrite `a = a * b <=> a * b = a * 1` and use `EQ_MULT_LCANCEL` to cancel `a`.
- Apply arithmetic to complete the proof.

### Mathematical insight
This theorem provides a characterization of prime numbers in terms of the sigma function (sum of divisors). A number is prime if and only if the sum of its divisors is the number itself plus one. This is because a prime number has only two divisors: 1 and itself.

### Dependencies
- `SIGMA_PRIME`
- `CONTRAPOS_THM`
- `prime`
- `DE_MORGAN_THM`
- `SIGMA_1`
- `ARITH`
- `NOT_FORALL_THM`
- `NOT_IMP`
- `divides`
- `SIGMA_MULT`
- `SIGMA_0`
- `MULT_CLAUSES`
- `MULT_EQ_1`
- `EQ_MULT_LCANCEL`


---

## SIGMA_POW2

### Name of formal statement
SIGMA_POW2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SIGMA_POW2 = prove
 (`!k. sigma(2 EXP k) = 2 EXP (k + 1) - 1`,
  GEN_TAC THEN REWRITE_TAC[sigma; EXP_EQ_0; ARITH] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `nsum {2 EXP i | i <= k} (\i. i)` THEN CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC[DIVIDES_PRIMEPOW; PRIME_2; EXTENSION; IN_ELIM_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `x + 1 = y ==> x = y - 1`) THEN
  SPEC_TAC(`k:num`,`k:num`) THEN INDUCT_TAC THEN REWRITE_TAC[LE] THENL
   [REWRITE_TAC[SET_RULE `{2 EXP i | i = 0} = {2 EXP 0}`] THEN
    REWRITE_TAC[ARITH; NSUM_SING];
    ALL_TAC] THEN
  REWRITE_TAC[SET_RULE
   `{2 EXP i | i = SUC k \/ i <= k} =
    (2 EXP (SUC k)) INSERT {2 EXP i | i <= k}`] THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[SET_RULE
   `{2 EXP i | i <= k} = IMAGE (\i. 2 EXP i) {i | i <= k}`] THEN
  SIMP_TAC[NSUM_CLAUSES; FINITE_IMAGE; FINITE_NUMSEG_LE] THEN
  REWRITE_TAC[IN_IMAGE; GSYM LE_ANTISYM; LE_EXP; ARITH] THEN
  REWRITE_TAC[LE_ANTISYM; IN_ELIM_THM; UNWIND_THM1] THEN
  REWRITE_TAC[ARITH_RULE `~(SUC k <= k)`] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[GSYM ADD_ASSOC] THEN
  REWRITE_TAC[EXP; EXP_ADD; ARITH] THEN ARITH_TAC);;
```

### Informal statement
For all natural numbers `k`, the sum of `2` to the power of `i`, where `i` ranges over all elements in the set of natural numbers less than or equal to `k`, is equal to `2` to the power of `k+1`, minus `1`.

### Informal sketch
The proof proceeds by induction on `k`.

- Base Case: `k = 0`. The sum of `2` to the power of `i` for `i` in the set `{0}` (since `i <= 0`) is just `2` to the power of `0`, which is `1`. On the other hand, `2` to the power of `(0 + 1)` minus `1` is `2 - 1 = 1`.

- Inductive Step: Assume that the theorem holds for `k`. We want to prove that it holds for `k+1`. The sum of `2` to the power of `i` for `i` in the set of natural numbers less than or equal to `k+1` is equal to the sum of `2` to the power of `(k+1)` plus the sum of `2` to the power of `i` for `i` in the set of natural numbers less than or equal to `k`. By the inductive hypothesis, the latter is equal to `2` to the power of `(k+1)` minus `1`. Thus, the total sum is `2` to the power of `(k+1)` plus `2` to the power of `(k+1)` minus `1`, which simplifies to `2 * (2` to the power of `(k+1)`) minus `1`, which is `2` to the power of `(k+2)` minus `1`.

The proof uses properties of the `sigma` operator (summation over a set), exponentiation (`EXP`), arithmetic, and set theory.

### Mathematical insight
This theorem gives a closed-form expression for the sum of the first `k+1` powers of 2. It's a fundamental result that's often used in computer science (e.g., binary representation) and mathematics.

### Dependencies
`sigma`, `EXP_EQ_0`, `ARITH`, `DIVIDES_PRIMEPOW`, `PRIME_2`, `EXTENSION`, `IN_ELIM_THM`, `LE`, `NSUM_SING`, `SET_RULE`, `NSUM_CLAUSES`, `FINITE_IMAGE`, `FINITE_NUMSEG_LE`, `IN_IMAGE`, `GSYM LE_ANTISYM`, `LE_EXP`


---

## SIGMA_MULTIPLICATIVE

### Name of formal statement
SIGMA_MULTIPLICATIVE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SIGMA_MULTIPLICATIVE = prove
 (`!a b. coprime(a,b) ==> sigma(a * b) = sigma(a) * sigma(b)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `a = 0` THEN ASM_REWRITE_TAC[SIGMA_0; MULT_CLAUSES] THEN
  ASM_CASES_TAC `b = 0` THEN ASM_REWRITE_TAC[SIGMA_0; MULT_CLAUSES] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[sigma; MULT_EQ_0] THEN
  ASM_SIMP_TAC[FINITE_DIVISORS; MULT_NSUM] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `nsum (IMAGE (\(x,y). x * y)
         {x,y | x divides a /\ y divides b}) (\i. i)` THEN
  CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; EXISTS_PAIR_THM] THEN
    REWRITE_TAC[PAIR_EQ] THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c <=> c /\ a /\ b`] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    X_GEN_TAC `n:num` THEN EQ_TAC THEN REWRITE_TAC[DIVISION_DECOMP] THEN
    REWRITE_TAC[divides] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[MULT_AC];
    ALL_TAC] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhs o rand) NSUM_IMAGE (lhand w))) THEN
  REWRITE_TAC[o_DEF; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`w:num`; `x:num`; `y:num`; `z:num`] THEN
  REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (is_var o rand o concl))) THEN
  REWRITE_TAC[GSYM DIVIDES_ANTISYM] THEN
  ASM_MESON_TAC[COPRIME_DIVISORS; COPRIME_SYM; COPRIME_DIVPROD;
                DIVIDES_RMUL; DIVIDES_REFL; MULT_SYM]);;
```
### Informal statement
For all natural numbers `a` and `b`, if `a` and `b` are coprime, then the sum of divisors of `a * b` equals the product of the sum of divisors of `a` and the sum of divisors of `b`.

### Informal sketch
The proof proceeds as follows:
- Perform case splits on `a = 0` and `b = 0` in order to handle edge cases of zero. If either number is zero, then the result follows from the definition of `sigma` and basic arithmetic.
- Assume that `a` and `b` are coprime and neither is equal to zero. Rewrite the goal using the definition of `sigma` which is the `nsum` of the set of divisors.
- Use the fact that the divisors of `a * b` can be expressed as the image of the set of pairs `(x, y)` where `x` divides `a` and `y` divides `b`, under the mapping `(x, y) -> x * y`. `FINITE_DIVISORS` is used to establish finiteness, required by `NSUM`.
- Prove that the `nsum` over the image of `(x, y)` such that `x` divides `a` and `y` divides `b` under the function `(x,y). x * y` is equal to `sigma(a) * sigma(b)`.
- Apply `NSUM_IMAGE` to transform the sum over the cartesian product into a product of sums.
- Show that if `w * z` divides both `a` and `b`, then `w = z = 1`, since `a` and `b` are coprime. Then, using `COPRIME_DIVISORS` and related theorems about coprime numbers and divisibility, rewrite the divisibility conditions and simplify.
- Finally, use `ASM_MESON_TAC` and related arithmetic facts to complete proof.

### Mathematical insight
This theorem establishes the multiplicative property of the divisor sum function, `sigma`. It states that `sigma(a * b) = sigma(a) * sigma(b)` whenever `a` and `b` are coprime. This is a fundamental property in number theory, allowing us to compute the divisor sum function for composite numbers based on their prime factorization.

### Dependencies
- `sigma`
- `coprime`
- `FINITE_DIVISORS`
- `MULT_NSUM`
- `IN_ELIM_THM`
- `DIVISION_DECOMP`
- `divides`
- `COPRIME_DIVISORS`
- `COPRIME_SYM`
- `COPRIME_DIVPROD`
- `DIVIDES_RMUL`
- `DIVIDES_REFL`
- `MULT_SYM`
- `NSUM_IMAGE`
- `FORALL_PAIR_THM`
- `MULT_CLAUSES`
- `sigma_0`
- `MULT_EQ_0`

### Porting notes (optional)
The proof relies heavily on rewriting with definitions and simplification. The `NSUM_IMAGE` and related theorems concerning sums over finite sets are critical and may require specific adaptations depending on the target proof assistant's library. The automation through `MESON_TAC` depends on the specific first-order logic solver, so the arithmetic facts may have to be provided explicitly in other systems.


---

## PERFECT_EUCLID

### Name of formal statement
PERFECT_EUCLID

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PERFECT_EUCLID = prove
 (`!k. prime(2 EXP k - 1) ==> perfect(2 EXP (k - 1) * (2 EXP k - 1))`,
  GEN_TAC THEN ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[ARITH; PRIME_0] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `coprime(2 EXP (k - 1),2 EXP k - 1)` ASSUME_TAC THENL
   [MATCH_MP_TAC COPRIME_ODD_POW2 THEN ASM_SIMP_TAC[ODD_POW2_MINUS1];
    ALL_TAC] THEN
  ASM_SIMP_TAC[perfect; SIGMA_MULTIPLICATIVE; SIGMA_PRIME; SIGMA_POW2] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> k - 1 + 1 = k`; EXP_EQ_0;
               MULT_EQ_0; ARITH] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  REWRITE_TAC[MULT_ASSOC] THEN GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN
  AP_TERM_TAC THEN UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC);;
```
### Informal statement
For all natural numbers `k`, if `2^k - 1` is prime, then `2^(k-1) * (2^k - 1)` is a perfect number.

### Informal sketch
The proof proceeds by induction on `k`.
- Base case: `k = 0`. We show that if `k = 0`, then `2^0 - 1 = 0` is prime, which is false (by `PRIME_0`). Thus, the statement holds vacuously.
- Inductive step: Assuming `k != 0` and `2^k - 1` is prime, we need to show that `2^(k-1) * (2^k - 1)` is perfect.
  - First, we prove that `2^(k-1)` and `2^k - 1` are coprime using `COPRIME_ODD_POW2`.
  - Then, since `perfect(n)` is defined as `sigma(n) = 2 * n`, and `sigma` is multiplicative for coprime numbers (using `SIGMA_MULTIPLICATIVE`), we can rewrite `sigma(2^(k-1) * (2^k - 1))` as `sigma(2^(k-1)) * sigma(2^k - 1)`.
  - Using `SIGMA_PRIME` and `SIGMA_POW2` we get `(2^(k-1 + 1) - 1) * (2^k - 1 + 1)` which simplifies to `(2^k - 1) * 2^k`.
  - We need to show that `(2^k - 1) * 2^k = 2 * (2^(k-1) * (2^k - 1))`. We rewrite and simplify the right-hand side to `2^k * (2^k - 1)`, showing equality.
  - Finally, we show that `k != 0`.
    - We know that if `k = 0` then `2^k - 1== 0` which is false, therefore `k != 0`.

### Mathematical insight
This theorem states Euclid's theorem on perfect numbers: if `2^k - 1` is a Mersenne prime, then `2^(k-1) * (2^k - 1)` is a perfect number. A perfect number is a positive integer that is equal to the sum of its proper divisors.

### Dependencies
- `ARITH`
- `PRIME_0`
- `COPRIME_ODD_POW2`
- `ODD_POW2_MINUS1`
- `perfect`
- `SIGMA_MULTIPLICATIVE`
- `SIGMA_PRIME`
- `SIGMA_POW2`
- `EXP_EQ_0`
- `MULT_EQ_0`
- `MULT_ASSOC`
- `CONJUNCT2`

### Porting notes (optional)
- The proof relies heavily on rewriting with arithmetic simplification rules. Ensure the target system's arithmetic simplification is similarly powerful.
- The `sigma` function and its properties (`SIGMA_MULTIPLICATIVE`, `SIGMA_PRIME`, `SIGMA_POW2`) will need to be defined or imported.


---

## PERFECT_EULER

### Name of formal statement
PERFECT_EULER

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PERFECT_EULER = prove
 (`!n. EVEN(n) /\ perfect(n)
       ==> ?k. prime(2 EXP k - 1) /\ n = 2 EXP (k - 1) * (2 EXP k - 1)`,
  GEN_TAC THEN MP_TAC(SPEC `n:num` EVEN_ODD_DECOMP) THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[perfect]; ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; GSYM NOT_EVEN] THEN
  MAP_EVERY X_GEN_TAC [`r:num`; `s:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
  ASM_REWRITE_TAC[EVEN_EXP; EVEN_MULT; ARITH] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[perfect] THEN
  ASM_SIMP_TAC[SIGMA_MULTIPLICATIVE; SIGMA_POW2;
               COPRIME_ODD_POW2; GSYM NOT_EVEN] THEN
  DISCH_TAC THEN EXISTS_TAC `r + 1` THEN
  REWRITE_TAC[ADD_SUB; EQ_MULT_LCANCEL] THEN REWRITE_TAC[EXP_EQ_0; ARITH] THEN
  FIRST_X_ASSUM(MP_TAC o check(is_eq o concl)) THEN
  REWRITE_TAC[MULT_ASSOC; GSYM(CONJUNCT2 EXP); ADD1] THEN
  DISCH_THEN(MP_TAC o MATCH_MP
    (REWRITE_RULE[IMP_CONJ] MULT_EQ_COPRIME)) THEN
  ANTS_TAC THENL
   [ONCE_REWRITE_TAC[COPRIME_SYM] THEN MATCH_MP_TAC COPRIME_ODD_POW2 THEN
    SIMP_TAC[ODD_POW2_MINUS1; ADD_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` MP_TAC) THEN
  ASM_CASES_TAC `d = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THENL
   [ASM_MESON_TAC[EVEN]; ALL_TAC] THEN
  ASM_CASES_TAC `d = 1` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; SIGMA_PRIME_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "s" THEN
    MATCH_MP_TAC(GSYM SUB_ADD) THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0; ARITH];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  MP_TAC(SPECL [`2 EXP (r + 1) - 1`; `d:num`] SIGMA_MULT) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `a /\ ~b ==> (a ==> b) ==> c`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `2 EXP 1 < a ==> 1 < a - 1`) THEN
    REWRITE_TAC[LT_EXP; ARITH] THEN
    UNDISCH_TAC `~(r = 0)` THEN ARITH_TAC;
    MAP_EVERY UNDISCH_TAC [`~(d = 0)`; `~(d = 1)`] THEN ARITH_TAC;
    REWRITE_TAC[NOT_LE] THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[RIGHT_SUB_DISTRIB; MULT_CLAUSES] THEN
    MATCH_MP_TAC(ARITH_RULE `1 * d < x * d ==> x * d < 1 + d + x * d - d`) THEN
    ASM_REWRITE_TAC[LT_MULT_RCANCEL] THEN
    MATCH_MP_TAC(ARITH_RULE `2 EXP 0 < a ==> 1 < a`) THEN
    REWRITE_TAC[LT_EXP] THEN UNDISCH_TAC `~(r = 0)` THEN ARITH_TAC]);;
```
### Informal statement
For all natural numbers `n`, `n` is even and `n` is perfect if and only if there exists a natural number `k` such that `2^k - 1` is prime and `n` is equal to `2^(k-1) * (2^k - 1)`.

### Informal sketch
The proof proceeds as follows:

- First, decompose `n` into `2^r * s` where `s` is odd.
- Case split on `n = 0`. If `n` is zero, we reach a contradiction because 0 is not perfect.
- Assume `n > 0`, hence `r` and `s` are non-zero. Rewrite the definition of `perfect(n)`.
- Use the fact that `sigma` is multiplicative, `sigma(2^r) = 2^(r+1) - 1`, and `2^r` and `s` are coprime.
- Show that if `d` divides `s`, then `d` must be one otherwise it doesn't satisfy `sigma(n)=2*n`.
- Choose `d` such that `s=1*d`. Case split on `d=0`. Then because `s` is odd, we know that `s` is not zero/even.
- Case split on `d=1`. After simplification, it will be shown that `s=2^(r+1)-1`.
- We have `s = 2^(r+1) - 1`, and we also know that `sigma(s) = s + 1`. This holds if and only if `s` is prime.
- Thus, we have `n = 2^r * (2^(r+1) - 1)`, where `2^(r+1) - 1` is prime. Let `k = r+1`.
- The proof concludes by showing that `2^k - 1` is prime if and only if `sigma(s) = s + 1`.

### Mathematical insight
This theorem characterizes even perfect numbers. It states that every even perfect number can be written in the form `2^(k-1) * (2^k - 1)`, where `2^k - 1` is a Mersenne prime. This is a classical result due to Euler. It is not known whether odd perfect numbers exist.

### Dependencies
- `EVEN`
- `perfect`
- `EVEN_ODD_DECOMP`
- `LEFT_IMP_EXISTS_THM`
- `NOT_EVEN`
- `EVEN_EXP`
- `EVEN_MULT`
- `SIGMA_MULTIPLICATIVE`
- `SIGMA_POW2`
- `COPRIME_ODD_POW2`
- `ADD_SUB`
- `EQ_MULT_LCANCEL`
- `EXP_EQ_0`
- `MULT_ASSOC`
- `CONJUNCT2 EXP`
- `ADD1`
- `IMP_CONJ`
- `MULT_EQ_COPRIME`
- `COPRIME_SYM`
- `ODD_POW2_MINUS1`
- `ADD_EQ_0`
- `SIGMA_MULT`
- `MULT_CLAUSES`
- `SIGMA_PRIME_EQ`
- `SUB_ADD`
- `ARITH_RULE`
- `LT_EXP`
- `TAUT`
- `RIGHT_SUB_DISTRIB`
- `LT_MULT_RCANCEL`
- `NOT_LE`


---

