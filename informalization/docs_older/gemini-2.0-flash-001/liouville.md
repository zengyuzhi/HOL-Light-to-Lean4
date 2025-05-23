# liouville.ml

## Overview

Number of statements: 22

`liouville.ml` formalizes Liouville's approximation theorem, which provides a bound on how well algebraic numbers can be approximated by rational numbers. The file depends on the `floor.ml` and `poly.ml` libraries. The main result is a formal proof of Liouville's theorem.


## algebraic

### Name of formal statement
algebraic

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let algebraic = new_definition
 `algebraic(x) <=> ?p. ALL integer p /\ ~(poly p = poly []) /\ poly p x = &0`;;
```

### Informal statement
A real number *x* is `algebraic` if and only if there exists a polynomial *p* with integer coefficients such that *p* is not the zero polynomial and *p(x)* = 0.

### Informal sketch
The definition introduces the concept of an algebraic number. It asserts that a number `x` is algebraic if and only if it is a root of a non-zero polynomial `p` which has integer coefficients.

### Mathematical insight
This definition is fundamental in number theory and real analysis. It distinguishes between algebraic and transcendental numbers. A transcendental number is simply a number that is not algebraic. The definition formalizes the standard mathematical concept of algebraic numbers, which are solutions to polynomial equations with integer (or, equivalently, rational) coefficients.

### Dependencies
- Requires "Library/floor.ml"
- Requires "Library/poly.ml"
- Definition: `poly`


---

## transcendental

### Name of formal statement
transcendental

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let transcendental = new_definition
 `transcendental(x) <=> ~(algebraic x)`;;
```

### Informal statement
For any `x`, `transcendental x` is true if and only if it is not the case that `algebraic x` is true.

### Informal sketch
The definition introduces the predicate `transcendental` as the negation of the predicate `algebraic`. There is no proof associated with a definition.

### Mathematical insight
This definition introduces the notion of a transcendental number as one that is not algebraic. This is a standard definition in number theory and is used to classify numbers based on whether they are roots of polynomial equations with integer coefficients.

### Dependencies
- `algebraic`


---

## REAL_INTEGER_EQ_0

### Name of formal statement
REAL_INTEGER_EQ_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_INTEGER_EQ_0 = prove
 (`!x. integer x /\ abs(x) < &1 ==> x = &0`,
  MESON_TAC[REAL_ABS_INTEGER_LEMMA; REAL_NOT_LE]);;
```
### Informal statement
For all real numbers `x`, if `x` is an integer and the absolute value of `x` is less than 1, then `x` equals 0.

### Informal sketch
The proof proceeds as follows:
- Assume `x` is an integer and `abs(x) < &1`.
- Apply the lemma `REAL_ABS_INTEGER_LEMMA` which relates the absolute value of an integer to its magnitude: if `x` is an integer then `abs(x)` is a natural number. Thus, `abs(x)` is a natural number less than 1.
- Apply `REAL_NOT_LE` which effectively states that if a real number `r` is less than 1, then it is not greater than or equal to 1. Since `abs(x)` is a nonnegative integer that is not greater than or equal to 1, it must be 0.
- Conclude since `abs(x) = 0`, this implies `x = 0`. 
- MESON_TAC automates these steps using the supplied lemmas.

### Mathematical insight
This theorem establishes a basic property of real numbers and integers, showing that `&0` is the only integer strictly numerically between `-1` and `1`. Although simple, it is a useful fact in real analysis when reasoning about integer values.

### Dependencies
- Theorems: `REAL_ABS_INTEGER_LEMMA`, `REAL_NOT_LE`


---

## FACT_LE_REFL

### Name of formal statement
FACT_LE_REFL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FACT_LE_REFL = prove
 (`!n. n <= FACT n`,
  INDUCT_TAC THEN REWRITE_TAC[FACT; ARITH] THEN
  MATCH_MP_TAC(ARITH_RULE `x * 1 <= a ==> x <= a`) THEN
  REWRITE_TAC[LE_MULT_LCANCEL; NOT_SUC; FACT_LT;
              ARITH_RULE `1 <= n <=> 0 < n`]);;
```
### Informal statement
For all natural numbers `n`, `n` is less than or equal to `FACT n`, where `FACT` is the factorial function.

### Informal sketch
The proof is by induction on `n`.

- Base case: `n = 0`. We need to show `0 <= FACT 0`. Since `FACT 0 = 1`, we need to show `0 <= 1`, which is true by arithmetic.
- Inductive step: Assume `n <= FACT n`. We must show that `SUC n <= FACT (SUC n)`.
  - By definition of `FACT`, `FACT (SUC n) = SUC n * FACT n`. Thus, we need to show `SUC n <= SUC n * FACT n`.
  - Since we know `n <= FACT n` and `NOT(SUC n = 0)`, we know `0 < SUC n` and therefore `1 <= SUC n` (by `ARITH_RULE \`1 <= n <=> 0 < n\``).
  - We have `1 <= FACT n` and `1 <= SUC n`. Multiplying `SUC n <= SUC n * FACT n` on both sides by the positive number `SUC n` gives us our goal.
  - We can conclude `SUC n <= SUC n * FACT n`.

### Mathematical insight
This theorem establishes a fundamental property of the factorial function: that `n` is always less than or equal to its factorial, for natural numbers `n`. This is a crucial fact when dealing with inequalities involving factorials.

### Dependencies
- `FACT` (factorial definition)
- `ARITH` (arithmetic facts and tactics)
- `LE_MULT_LCANCEL`
- `NOT_SUC`
- `FACT_LT`
- `ARITH_RULE \`1 <= n <=> 0 < n\``


---

## EXP_LE_REFL

### Name of formal statement
EXP_LE_REFL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EXP_LE_REFL = prove
 (`!a. 1 < a ==> !n. n <= a EXP n`,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC[EXP; ARITH] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
   `n <= x ==> 1 * x < y ==> SUC n <= y`)) THEN
  REWRITE_TAC[LT_MULT_RCANCEL; EXP_EQ_0] THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;
```

### Informal statement
For all `a`, if 1 is less than `a`, then for all `n`, `n` is less than or equal to `a` raised to the power of `n`.

### Informal sketch
The theorem is proved by induction on `n`.
- Base case: `n = 0`. We need to show that 0 <= `a EXP 0`. Since `a EXP 0 = 1` and 0 <= 1, the base case holds.
- Inductive step: Assume `n <= a EXP n`. We need to show that `SUC n <= a EXP (SUC n)`.
    - We know that `1 < a`. We have `n <= a EXP n`.
    - Multiplying both sides of `1 < a` by `a EXP n` yields `a EXP n < a * (a EXP n)`, i.e., `a EXP n < a EXP (SUC n)`.
    - We want to prove `SUC n <= a EXP (SUC n)`. Since `n <= a EXP n` and `a EXP n < a EXP (SUC n)`, implies `SUC n <= a EXP(SUC n)` using `n <= x ==> 1 * x < y ==> SUC n <= y`.

### Mathematical insight
The theorem states that for any number `a` greater than 1, `a^n` grows faster than `n`. This is a fundamental property used in many analyses involving exponential growth.

### Dependencies
- `EXP`
- `ARITH`
- `LT_MULT_RCANCEL`
- `EXP_EQ_0`


---

## MVT_INEQ

### Name of formal statement
MVT_INEQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MVT_INEQ = prove
 (`!f f' a d M.
        &0 < M /\ &0 < d /\
        (!x. abs(x - a) <= d ==> (f diffl f'(x)) x /\ abs(f' x) < M)
        ==> !x. abs(x - a) <= d ==> abs(f x - f a) < M * d`,
  REWRITE_TAC[TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  REPEAT STRIP_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (REAL_ARITH `x = a \/ x < a \/ a < x`)
  THENL
   [ASM_SIMP_TAC[REAL_SUB_REFL; REAL_ABS_NUM; REAL_LT_MUL];
    MP_TAC(SPECL [`f:real->real`; `f':real->real`; `x:real`; `a:real`]
                 MVT_ALT);
    MP_TAC(SPECL [`f:real->real`; `f':real->real`; `a:real`; `x:real`]
                 MVT_ALT)] THEN
  (ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC;
     ALL_TAC]) THEN
  STRIP_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ABS_SUB]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `d * abs(f'(z:real))` THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_RMUL;
     MATCH_MP_TAC REAL_LT_LMUL THEN
     ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC]) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC);;
```

### Informal statement
For all real-valued functions `f` and `f'`, and for all real numbers `a`, `d`, and `M`, if `0 < M` and `0 < d`, and for all `x`, if the absolute value of `x - a` is less than or equal to `d`, then `f` is differentiable at `x` with derivative `f'(x)` and the absolute value of `f'(x)` is less than `M`; then, for all `x`, if the absolute value of `x - a` is less than or equal to `d`, then the absolute value of `f(x) - f(a)` is less than `M * d`.

### Informal sketch
The theorem proves an inequality form of the mean value theorem using the following steps:

- Start by expanding the universal quantifiers and splitting the conjunctions.
- Perform case analysis based on the ordering of `x` and `a` (`x = a`, `x < a`, `a < x`).
- In the case where `x = a`, simplify the goal using `REAL_SUB_REFL`, `REAL_ABS_NUM`, and `REAL_LT_MUL`.
- In the case where `x < a` or `a < x`, apply the alternative version of the mean value theorem (`MVT_ALT`). These MVT alternatives each gives an intermediate point `z` between `a` and `x`.
- Use assumptions about differentiability and bound of derivative `abs(f' x) < M`.
- Apply real arithmetic (`REAL_ARITH_TAC`) to obtain the desired inequality.
- After applying the mean value theorem, the proof involves rewriting the goal using `REAL_ABS_SUB` and `REAL_MUL_SYM`. Further simplifications are performed using absolute value properties.
- Finally, the conclusion follows by demonstrating the existence of a value which allows the target inequality to be bounded based on the properties of the mean value theorem; this involves discharging the intermediate value `d * abs(f'(z:real))`. This relies on further real arithmetic.

### Mathematical insight
This is an inequality version of the Mean Value Theorem, providing a bound on the change of a function's value based on a bound on its derivative. It is particularly useful when you don't need the exact value provided by the standard MVT, but only a guaranteed error bound.

### Dependencies
- `MVT_ALT`
- `REAL_ARITH`
- `REAL_ABS_NUM`
- `REAL_SUB_REFL`
- `REAL_LT_MUL`
- `REAL_ABS_SUB`
- `REAL_MUL_SYM`
- `REAL_ABS_MUL`
- `REAL_LET_TRANS`
- `REAL_LE_RMUL`
- `REAL_LT_LMUL`


---

## POLY_MULTIPLE_INTEGER

### Name of formal statement
POLY_MULTIPLE_INTEGER

### Type of the formal statement
theorem

### Formal Content
```ocaml
let POLY_MULTIPLE_INTEGER = prove
 (`!p q l. ALL integer l ==> integer(&q pow (LENGTH l) * poly l (&p / &q))`,
  GEN_TAC THEN GEN_TAC THEN ASM_CASES_TAC `q = 0` THENL
   [LIST_INDUCT_TAC THEN REWRITE_TAC[poly; REAL_MUL_RZERO; INTEGER_CLOSED] THEN
    ASM_REWRITE_TAC[LENGTH; real_pow; REAL_MUL_LZERO; INTEGER_CLOSED];
    ALL_TAC] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[poly; REAL_MUL_RZERO; INTEGER_CLOSED] THEN
  REWRITE_TAC[LENGTH; real_pow; ALL] THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_ARITH
   `(q * qp) * (h + pq * pol) = q * h * qp + (q * pq) * (qp * pol)`] THEN
  ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ] THEN
  MATCH_MP_TAC(el 1 (CONJUNCTS INTEGER_CLOSED)) THEN
  ASM_SIMP_TAC[INTEGER_CLOSED]);;
```
### Informal statement
For all polynomials `p` and `q`, and for all lists `l`, if all elements of list `l` are integers, then `q` to the power of the length of `l` multiplied by the polynomial `p` evaluated at `p/q` is an integer.

### Informal sketch
The proof proceeds by induction on the list `l`.

- First, the case `q = 0` is considered separately.
  - If `l` is an empty list, the result holds by simplifying using properties of `poly`, `REAL_MUL_RZERO`, and `INTEGER_CLOSED`, along with `LENGTH`, `real_pow`, `REAL_MUL_LZERO`.
  - If `l` is non-empty, the hypothesis `q = 0` leads to a contradiction and the goal is trivially proven.
- The main proof is by induction on the list `l` for the case when `q` is not equal to `0`.
  - Base case: If `l` is an empty list, the result holds by simplifying using properties of `poly`, `REAL_MUL_RZERO`, and `INTEGER_CLOSED`, the definition of `LENGTH`, and the property that anything to the power of zero is one (`real_pow`).
  - Inductive step: Assume the result holds for the list `l`. We need to show it holds for `h::l`. This involves rewriting using `REAL_ARITH` to rearrange the expression `(q * qp) * (h + pq * pol) = q * h * qp + (q * pq) * (qp * pol)`, then simplifying using `REAL_DIV_LMUL` and `REAL_OF_NUM_EQ`. The result then follows from the inductive hypothesis and `INTEGER_CLOSED`.

### Mathematical insight
This theorem states that if we have a polynomial `p` and want to evaluate it at a rational number `p/q`, we can find an integer multiple of that value by multiplying by `q` raised to the power of the degree of the polynomial (which is the same as the length of the list of coefficients). This is a useful result for working with polynomials over integers and rationals.

### Dependencies
- `poly`
- `REAL_MUL_RZERO`
- `INTEGER_CLOSED`
- `LENGTH`
- `real_pow`
- `REAL_MUL_LZERO`
- `REAL_ARITH`
- `REAL_DIV_LMUL`
- `REAL_OF_NUM_EQ`
- `ALL`
- `CONJUNCTS INTEGER_CLOSED`

### Porting notes (optional)
When porting this theorem, ensure that the target proof assistant has similar theorems regarding integer closure under multiplication and addition, as well as properties of real arithmetic. The `INTEGER_CLOSED` theorems and the `REAL_ARITH` tactic play a crucial role in this proof. The handling of real numbers and integer types should be carefully considered. Also the definitions of `poly` and `real_pow` need to be available.


---

## SEPARATE_FINITE_SET

### Name of formal statement
SEPARATE_FINITE_SET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SEPARATE_FINITE_SET = prove
 (`!a s. FINITE s
         ==> ~(a IN s) ==> ?d. &0 < d /\ !x. x IN s ==> d <= abs(x - a)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
  CONJ_TAC THENL [MESON_TAC[REAL_LT_01]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `min d (abs(x - a))` THEN
  ASM_REWRITE_TAC[REAL_MIN_LE; REAL_LT_MIN; GSYM REAL_ABS_NZ; REAL_SUB_0] THEN
  ASM_MESON_TAC[REAL_LE_REFL]);;
```

### Informal statement
For any real number `a` and any set `s`, if `s` is finite and `a` is not an element of `s`, then there exists a positive real number `d` such that for all `x` in `s`, `d` is less than or equal to the absolute value of the difference between `x` and `a`.

### Informal sketch
The proof proceeds by induction on the finiteness of the set `s`.
- Base case: `s` is empty. The theorem holds vacuously because the condition `x IN s` is always false, hence any positive `d` will do.
- Inductive step: Assume the theorem holds for `s`. Need to show the theorem holds for `INSERT x s` assuming `a` is not in `INSERT x s`.
  - The goal is `?d. &0 < d /\ !y. y IN INSERT x s ==> d <= abs(y - a)`.
  - Since `a` is not in `INSERT x s`, we know `a` is not equal to `x` and `a` is not in `s`.
  - By the inductive hypothesis, there exists a `d` such that `&0 < d /\ !y. y IN s ==> d <= abs(y - a)`.
  - We can choose `min d (abs(x - a))` as the new `d`.
  - Show `&0 < min d (abs(x - a))`, which follows from `&0 < d` and `&0 < abs(x - a)` (since `x` and `a` are distinct).
  - Show `!y. y IN INSERT x s ==> min d (abs(x - a)) <= abs(y - a)`.
    - Case 1: `y = x`. Then `min d (abs(x - a)) <= abs(x - a)` holds by the property of `min`.
    - Case 2: `y IN s`. Then `min d (abs(x - a)) <= d <= abs(y - a)` by the inductive hypothesis and the property of `min`.

### Mathematical insight
The theorem states that if a real number `a` is not in a finite set `s` of real numbers, then there exists a positive distance `d` such that all elements in `s` are at least distance `d` away from `a`. This means a finite set is separated from any point not in the set by a positive distance. The separation relies on the finiteness of `s`; an infinite set could accumulate arbitrarily closely to an external point.

### Dependencies
- Theorem: `FINITE_INDUCT_STRONG`
- Theorem: `IN_INSERT`
- Theorem: `NOT_IN_EMPTY`
- Theorem: `DE_MORGAN_THM`
- Theorem: `REAL_LT_01`
- Theorem: `REAL_MIN_LE`
- Theorem: `REAL_LT_MIN`
- Theorem: `GSYM REAL_ABS_NZ`
- Theorem: `REAL_SUB_0`
- Theorem: `REAL_LE_REFL`


---

## POLY_ROOT_SEPARATE_LE

### Name of formal statement
POLY_ROOT_SEPARATE_LE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let POLY_ROOT_SEPARATE_LE = prove
 (`!p x. poly p x = &0 /\ ~(poly p = poly [])
         ==> ?d. &0 < d /\
                 !x'. &0 < abs(x' - x) /\ abs(x' - x) < d
                      ==> ~(poly p x' = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `{x | poly p x = &0} DELETE x`]
    SEPARATE_FINITE_SET) THEN
  ASM_SIMP_TAC[POLY_ROOTS_FINITE_SET; FINITE_DELETE; IN_DELETE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[GSYM REAL_ABS_NZ; REAL_SUB_0] THEN MESON_TAC[REAL_NOT_LT]);;
```
### Informal statement
For any polynomial `p` and any real number `x`, if `poly p x = 0` and `p` is not the zero polynomial, then there exists a real number `d` greater than 0 such that for any real number `x'`, if the absolute value of `x' - x` is greater than 0 and less than `d`, then `poly p x'` is not equal to 0.

### Informal sketch
The proof demonstrates that if `x` is a root of a non-zero polynomial `p`, then there exists a neighborhood around `x` containing no other roots of `p`.
- Assume `poly p x = 0` and `p` is not the zero polynomial.
- Use `SEPARATE_FINITE_SET` to show the existence of a `d` such that `0 < d` and if `x'` is in the set `{x' | 0 < abs(x' - x) /\ abs(x' - x) < d}`, then `x'` is not in `{x' | poly p x' = 0} DELETE x`. This is applicable because `POLY_ROOTS_FINITE_SET` ensures that the set of roots of the polynomial `p` is finite. Moreover, `FINITE_DELETE` establishes that deleting an element from a finite set results in a finite set, and `IN_DELETE` describes the in-set properties after element deletion. Since the set of roots without `x` is finite, we can separate `x` from the remaining roots.
- Use `MONO_EXISTS` to extend the existential quantifier. Rewrite using `IN_ELIM_THM` and `REAL_ABS_NZ`, `REAL_SUB_0`.
- Finally, use `MESON_TAC` with `REAL_NOT_LT` to complete the proof.

### Mathematical insight
This theorem states that the roots of a non-zero polynomial are isolated. This property is crucial in real analysis and algebra because it allows us to reason about the behavior of polynomials locally around their roots.  The condition that `p` is not the zero polynomial is necessary because the zero polynomial has every real number as a root, and thus roots are not isolated.

### Dependencies
- `POLY_ROOTS_FINITE_SET`
- `FINITE_DELETE`
- `IN_DELETE`
- `REAL_ABS_NZ`
- `REAL_SUB_0`
- `REAL_NOT_LT`
- `SEPARATE_FINITE_SET`
- `IN_ELIM_THM`
- `MONO_EXISTS`

### Porting notes (optional)
- The tactic `MESON_TAC` handles most of the logical reasoning. In other proof assistants, it may be necessary to use a combination of simplification and introduction/elimination rules to achieve the same result.
- The `SEPARATE_FINITE_SET` theorem is also a key dependency and will need to be available within the target proof assistant.


---

## POLY_ROOT_SEPARATE_LT

### Name of formal statement
POLY_ROOT_SEPARATE_LT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let POLY_ROOT_SEPARATE_LT = prove
 (`!p x. poly p x = &0 /\ ~(poly p = poly [])
         ==> ?d. &0 < d /\
                 !x'. &0 < abs(x' - x) /\ abs(x' - x) <= d
                      ==> ~(poly p x' = &0)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP POLY_ROOT_SEPARATE_LE) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d / &2` THEN ASM_MESON_TAC[REAL_ARITH
   `&0 < d ==> &0 < d / &2 /\ (x <= d / &2 ==> x < d)`]);;
```

### Informal statement
For any polynomial `p` and any real number `x`, if `x` is a root of `p` (i.e., `poly p x = &0`) and `p` is not the zero polynomial (i.e., `~(poly p = poly [])`), then there exists a real number `d` such that `0 < d` and for all real numbers `x'`, if `0 < abs(x' - x)` and `abs(x' - x) <= d`, then `x'` is not a root of `p` (i.e., `~(poly p x' = &0)`).

### Informal sketch
The proof proceeds as follows:

- Assume `poly p x = &0` and `~(poly p = poly [])`.
- Apply `POLY_ROOT_SEPARATE_LE` (which states that under the same assumptions, there exists a `d` such that `&0 < d` and `!x'. &0 < abs(x' - x) ==> abs(x' - x) <= d ==> ~(poly p x' = &0)`).
- Assume that such a `d` exists.
- Instantiate the existential quantifier with `d / &2`.
- Use `ASM_MESON_TAC` with `REAL_ARITH` (specifically `&0 < d ==> &0 < d / &2 /\ (x <= d / &2 ==> x < d)`) to discharge the goal. This uses the fact that if `0 < abs(x' - x) /\ abs(x' - x) <= d/2` holds, then `0 < abs(x' - x)` and `abs(x' - x) <= d` also holds.

### Mathematical insight
This theorem states that roots of non-zero polynomials are "isolated". It means that for a root `x` of a non-zero polynomial `p`, there exists a neighborhood around `x` such that no other point in that neighborhood (excluding `x` itself) is a root of `p`. This is a crucial property used in real analysis and algebraic geometry. The theorem `POLY_ROOT_SEPARATE_LE` essentially gives you an interval within which no other roots exist. This proof merely shrinks that interval.

### Dependencies
- `POLY_ROOT_SEPARATE_LE`
- `REAL_ARITH`

### Porting notes (optional)
Porting this theorem may require a similar result to `POLY_ROOT_SEPARATE_LE` already present or provable in the target system. Also, a comparable real arithmetic library with similar lemmas (e.g., relating `d` and `d/2` when `d > 0`) would be needed. Handling of the existential quantifier and its instantiation might vary depending on the target proof assistant.


---

## POLY_BOUND_INTERVAL

### Name of formal statement
POLY_BOUND_INTERVAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let POLY_BOUND_INTERVAL = prove
 (`!p d x. ?M. &0 < M /\ !x'. abs(x' - x) <= d ==> abs(poly p x') < M`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`poly p`; `x - d`; `x + d`] CONT_BOUNDED_ABS) THEN
  REWRITE_TAC[REWRITE_RULE[ETA_AX] (SPEC_ALL POLY_CONT)] THEN
  DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN EXISTS_TAC `&1 + abs M` THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `M:real` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN POP_ASSUM MP_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;
```
### Informal statement
For any polynomial `p`, any real number `d`, and any real number `x`, there exists a real number `M` such that `0 < M` and for all real numbers `x'`, if `abs(x' - x) <= d`, then `abs(poly p x') < M`.

### Informal sketch
The proof demonstrates that a polynomial is bounded on a closed interval.
- Start with a general polynomial `p`, a bound `d`, and a point `x`. The objective is to show the existence of a real number `M` that bounds the absolute value of the polynomial `p` within the interval `[x-d, x+d]`.
- Use `CONT_BOUNDED_ABS` to assert that because polynomials are continuous (`POLY_CONT`), they are bounded on closed intervals of the form `[x - d, x + d]`.
- Choose an `M` such that `abs(poly p x') < M` for all `x'` in `[x - d, x + d]`. Specifically, use `X_CHOOSE_TAC` followed by `EXISTS_TAC` to introduce `M'` (called `M` here) such that `abs(poly p x') <= M'` for all `x'` in `[x - d, x + d]`.
- The goal is converted to showing that `0 < M` and `abs(poly p x') < M` whenever `abs(x' - x) <= d`.
- Choose a new `M` in terms of `M'` which is `1 + abs M'` to ensure `0 < M` and `abs(poly p x') < M`.
- The conclusion then follows by real arithmetic.

### Mathematical insight
This theorem formalizes the fact that polynomials are continuous functions and, therefore, are bounded on closed intervals. The continuity of the polynomial is leveraged to ensure that within a given interval around a point `x`, the polynomial's absolute value does not exceed some bound `M`. This is a fundamental property used in real analysis and calculus.

### Dependencies
- `POLY_CONT`
- `CONT_BOUNDED_ABS`
- `REAL_LET_TRANS`


---

## LIOUVILLE_INTERVAL

### Name of formal statement
LIOUVILLE_INTERVAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LIOUVILLE_INTERVAL = prove
 (`!p x. poly p x = &0 /\ ~(poly p = poly [])
         ==> ?c. &0 < c /\
                 (!x'. abs(x' - x) <= c
                       ==> abs(poly(poly_diff p) x') < &1 / c) /\
                 (!x'. &0 < abs(x' - x) /\ abs(x' - x) <= c
                       ==> ~(poly p x' = &0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:real list`; `x:real`] POLY_ROOT_SEPARATE_LT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`poly_diff p`; `d:real`; `x:real`] POLY_BOUND_INTERVAL) THEN
  DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN EXISTS_TAC `min d (inv M)` THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_LE_MIN; REAL_LT_INV_EQ] THEN
  X_GEN_TAC `y:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `M:real` THEN
  ASM_SIMP_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_MIN_LE; REAL_LT_MIN] THEN
  ASM_REWRITE_TAC[REAL_LT_INV_EQ; REAL_LE_REFL]);;
```

### Informal statement
For every polynomial `p` (represented as a list of real coefficients) and every real number `x`, if `poly p x = 0` (that is, x is a root of p) and `p` is not the zero polynomial, then there exists a real number `c` greater than 0 such that:
1. For all real numbers `x'` such that `abs(x' - x) <= c`, it holds that `abs(poly(poly_diff p) x') < 1 / c`.
2. For all real numbers `x'` such that `0 < abs(x' - x) <= c`, it holds that `poly p x' != 0`.

### Informal sketch
The theorem states that for any root `x` of a non-zero polynomial `p`, there exists an interval around `x` where `p` has no other root, and the absolute value of the derivative `poly_diff p` is bounded.

- Start by assuming `poly p x = 0` and `p` is not the zero polynomial. Use `POLY_ROOT_SEPARATE_LT` to obtain a separation distance such that any other root is at some non-zero distance.
- Introduce the separating distance `d` obtained from `POLY_ROOT_SEPARATE_LT`.
- Apply `POLY_BOUND_INTERVAL` to `poly_diff p` to get a bound `M` on the derivative within the interval `[x - d, x + d]`. Thus, for any `x'` in this interval, `abs(poly(poly_diff p) x') <= M`.
- Choose `c` to be `min d (1 / M)`. This choice ensures that `0 < c <= d` and `c <= 1 / M`.  Thus `M <= 1/c` and with  `abs(poly(poly_diff p) x') <= M` we have `abs(poly(poly_diff p) x') <= 1/c`.
- Prove the two conditions for `c` using the properties of `min` and the bound `M` on the derivative, and separate root.

### Mathematical insight
This theorem establishes a local property around the roots of a polynomial. It states that roots of a polynomial are isolated and that the derivative is bounded in a small interval around each root. It combines root separation results (`POLY_ROOT_SEPARATE_LT`) and derivative bounding (`POLY_BOUND_INTERVAL`) to establish a quantitative relationship between the polynomial, its derivative, and the spacing of its roots. The existence of such an interval is crucial for analyzing the behavior of polynomials near their roots and shows that roots are not arbitrarily close to other roots of the same polynomial, unless it's the zero polynomial.

### Dependencies
- `POLY_ROOT_SEPARATE_LT`: states that for a non-zero polynomial `p` and a root `x`, there will be a distance `d` such that there are no roots in `(x-d, x+d)\\{x}`
- `POLY_BOUND_INTERVAL`: states that for any polynomial `p`, any real `x`, and any separation distance `d`, there will be a bound `M` on `poly p` in the interval `[x-d, x+d]`
- `REAL_LT_MIN`, `REAL_LE_MIN`, `REAL_LT_INV_EQ`, `REAL_LTE_TRANS`, `REAL_INV_INV`, `real_div`, `REAL_MUL_LID`, `REAL_LE_INV2`, `REAL_MIN_LE`, `REAL_LT_MIN`, `REAL_LE_REFL` (for reasoning about reals)


---

## LIOUVILLE

### Name of formal statement
LIOUVILLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LIOUVILLE = prove
 (`!x. algebraic x
       ==> ?n c. c > &0 /\
                 !p q. ~(q = 0) ==> &p / &q = x \/
                                    abs(x - &p / &q) > c / &q pow n`,
  GEN_TAC THEN REWRITE_TAC[algebraic; real_gt] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `LENGTH(l:real list)` THEN
  MP_TAC(SPECL [`l:real list`; `x:real`] LIOUVILLE_INTERVAL) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LE] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `&p / &q = x` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN UNDISCH_TAC
   `!x'. &0 < abs(x' - x) /\ abs(x' - x) <= c ==> ~(poly l x' = &0)` THEN
  DISCH_THEN(MP_TAC o SPEC `&p / &q`) THEN REWRITE_TAC[NOT_IMP] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_ABS_NZ; REAL_SUB_0];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `abs(x - y) <= d ==> d <= e ==> abs(y - x) <= e`)) THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; REAL_LE_LDIV_EQ; LT_NZ] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `~(q = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&q pow (LENGTH(l:real list)) * poly l (&p / &q) = &0`
  MP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0; REAL_OF_NUM_EQ]] THEN
  MATCH_MP_TAC REAL_INTEGER_EQ_0 THEN
  ASM_SIMP_TAC[POLY_MULTIPLE_INTEGER] THEN
  MP_TAC(SPECL [`poly l`; `poly(poly_diff l)`; `x:real`;
                `c / &q pow (LENGTH(l:real list))`; `&1 / c`]
               MVT_INEQ) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH; LT_NZ; REAL_POW_LT] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REWRITE_RULE[ETA_AX] (SPEC_ALL POLY_DIFF)] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x <= d ==> d <= e ==> x <= e`)) THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; REAL_LE_LDIV_EQ; LT_NZ] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `~(q = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC; REAL_MUL_LID] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[GSYM real_div] THEN DISCH_THEN(MP_TAC o SPEC `&p / &q`) THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; REAL_LT_RDIV_EQ; LT_NZ] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NUM] THEN
  REWRITE_TAC[REAL_MUL_AC]);;
```

### Informal statement
For all real numbers `x`, if `x` is algebraic, then there exist a natural number `n` and a real number `c` such that `c` is greater than 0, and for all integers `p` and `q`, if `q` is not equal to 0, then either `x` is equal to `p / q` or the absolute value of `x - p / q` is greater than `c / q^n`.

### Informal sketch
The proof proceeds as follows:
- Assume `x` is algebraic.
- By the definition of `algebraic`, there exists a list of real numbers `l` such that `poly l x = 0`.
- Take `n` to be the length of `l`.
- Apply `LIOUVILLE_INTERVAL` to `l` and `x`.
- Introduce `c` such that the conditions of Liouville's interval hold. The goal is now to prove `!p q. ~(q = 0) ==> &p / &q = x \/ abs(x - &p / &q) > c / &q pow n`.
- Assume `p` and `q` are integers and `q` is not zero.
- Perform a case split on whether `&p / &q = x`.
- If `&p / &q = x`, the left disjunct is true.
- Otherwise we need to prove `abs(x - &p / &q) > c / &q pow n`.
- We know that `!x'. &0 < abs(x' - x) /\ abs(x' - x) <= c ==> ~(poly l x' = &0)`.
- Instantiate x' with `&p / &q` to deduce `&0 < abs(&p / &q - x) /\ abs(&p / &q - x) <= c ==> ~(poly l (&p / &q) = &0)`.
- Split this implication into two parts: proving the antecedent, `&0 < abs(&p / &q - x) /\ abs(&p / &q - x) <= c` and using the negation of the consequent.
- Because `poly l x = 0` and `x != &p / &q`,then `abs(&p / &q - x) > 0` follows since `&p/&q` is not a root.  Then show that `abs(&p / &q - x) > 0`.
- Assume for contradiction that `abs(x - &p / &q) <= c`, then it will be shown that `poly l (&p / &q) = 0` to reach a contradiction.
- This splits our main goal into the two conditions given by the instantiated `LIOUVILLE_INTERVAL` theorem combined with our hypothesis.
- Reduce the goal to showing that `&q pow (LENGTH(l:real list)) * poly l (&p / &q) = &0`.
- To show this latter equality, apply `MVT_INEQ` (Mean Value Theorem Inequality) to `poly l`, `poly(poly_diff l)`, `x`, `c / &q pow (LENGTH(l:real list))`, and `&1 / c`.
- Simplify using the assumptions and arithmetic facts.
- Apply the Mean Value Theorem Inequality, which relates `abs(poly l x - poly l (&p / &q))` to `abs(x - &p / &q)`.
- Establish the inequality involving the derivative of the polynomial `poly l`.

### Mathematical insight
This theorem is a key result in number theory. It provides a lower bound on how well algebraic numbers can be approximated by rational numbers. This lower bound depends on the degree of the algebraic number. Specifically, Liouville's theorem implies that algebraic numbers of degree `n` cannot be approximated by rationals to an order greater than `n`. This result is significant because it was among the first results used to construct transcendental numbers. If a number can be approximated by rational numbers to an order *greater* than any `n` then it must be transcendental.

### Dependencies
**Theorems:**
- `algebraic`
- `real_gt`
- `LIOUVILLE_INTERVAL`
- `MONO_EXISTS`
- `REAL_NOT_LE`
- `REAL_ABS_NZ`
- `REAL_SUB_0`
- `REAL_POW_LT`
- `REAL_OF_NUM_LT`
- `REAL_LE_LDIV_EQ`
- `LT_NZ`
- `REAL_MUL_RID`
- `REAL_LE_LMUL`
- `REAL_LT_IMP_LE`
- `REAL_POW_LE_1`
- `REAL_OF_NUM_LE`
- `REAL_ENTIRE`
- `REAL_POW_EQ_0`
- `REAL_OF_NUM_EQ`
- `REAL_INTEGER_EQ_0`
- `POLY_MULTIPLE_INTEGER`
- `MVT_INEQ`
- `ETA_AX`
- `POLY_DIFF`
- `real_div`
- `REAL_MUL_ASSOC`
- `REAL_MUL_LID`
- `REAL_MUL_LINV`
- `REAL_LT_IMP_NZ`
- `REAL_SUB_RZERO`
- `REAL_ABS_SUB`
- `REAL_ABS_MUL`
- `REAL_ABS_POW`
- `REAL_ABS_NUM`
- `REAL_MUL_AC`

### Porting notes (optional)
- The `LIOUVILLE_INTERVAL` theorem is crucial. Without it, porting would have to rebuild a theory about intervals around algebraic numbers.
- The proof relies heavily on real and arithmetic tactics. Other proof assistants will rely heavily on the tactic system available.
- The use of the Mean Value Theorem `MVT_INEQ` is a key mathematical step that must exist in the target proof assistant, or be derived.


---

## LIOUVILLE_IRRATIONAL

### Name of formal statement
LIOUVILLE_IRRATIONAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LIOUVILLE_IRRATIONAL = prove
 (`!x. algebraic x /\ ~rational x
       ==> ?n c. c > &0 /\ !p q. ~(q = 0) ==> abs(x - &p / &q) > c / &q pow n`,
  REWRITE_TAC[RATIONAL_ALT] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LIOUVILLE) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  ASM_MESON_TAC[LIOUVILLE; REAL_ABS_DIV; REAL_ABS_NUM]);;
```

### Informal statement
For all real numbers `x`, if `x` is algebraic and not rational, then there exist a natural number `n` and a real number `c` such that `c` is greater than 0 and for all integers `p` and `q`, if `q` is not equal to 0, then the absolute value of the difference between `x` and `p/q` is greater than `c / q^n`.

### Informal sketch
The proof proceeds as follows:
- Start by rewriting the definition of rationality using `RATIONAL_ALT`.
- Eliminate quantifiers and implications using stripping tactics.
- Apply the Liouville's approximation theorem (`LIOUVILLE`) using `FIRST_X_ASSUM(MP_TAC o MATCH_MP LIOUVILLE)`.
- Introduce the existential quantifiers `n` and `c`.
- Apply monotonicity rules for exists, conjunction and universal quantification.
- Apply the Liouville's approximation theorem (`LIOUVILLE`) and properties of real absolute values and division (`REAL_ABS_DIV`, `REAL_ABS_NUM`) using `ASM_MESON_TAC`.

### Mathematical insight
This theorem is a corollary to Liouville's approximation theorem. It states that algebraic irrational numbers cannot be "too well" approximated by rational numbers. In other words, for any algebraic irrational number, there exists a bound on how closely it can be approximated by rational numbers, relative to the denominator of the rational approximation. This result is a key step in proving the existence of transcendental numbers (numbers that are not algebraic).

### Dependencies
The following theorems and definitions are used in the proof:
- `LIOUVILLE`
- `RATIONAL_ALT`
- `REAL_ABS_DIV`
- `REAL_ABS_NUM`
- `MONO_EXISTS`
- `MONO_AND`
- `MONO_FORALL`


---

## liouville

### Name of formal statement
- liouville

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let liouville = new_definition
 `liouville = suminf (\n. &1 / &10 pow (FACT n))`;;
```
### Informal statement
- The constant `liouville` is defined as the infinite sum, indexed by `n`, of `1 / 10^(FACT n)`.

### Informal sketch
- The definition introduces a new constant `liouville` and equates it to an infinite sum. The summation term is `1 / 10^(FACT n)`, where `FACT` represents the factorial function and `n` is the index of the sum. HOL Light's `suminf` is used to represent the infinite summation.

### Mathematical insight
- This definition introduces Liouville's constant, a transcendental number. The rapid growth of the factorial in the denominator ensures that `liouville` has very good rational approximations, making it a Liouville number. This is a standard example in transcendental number theory.

### Dependencies
- `suminf`
- `FACT`


---

## LIOUVILLE_SUM_BOUND

### Name of formal statement
LIOUVILLE_SUM_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LIOUVILLE_SUM_BOUND = prove
 (`!d n. ~(n = 0)
         ==> sum(n..n+d) (\k. &1 / &10 pow FACT k) <= &2 / &10 pow (FACT n)`,
  INDUCT_TAC THEN GEN_TAC THEN DISCH_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; SUM_SING_NUMSEG; real_div] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_OF_NUM_LE; ARITH];
    ALL_TAC] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_ADD] THEN REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= x ==> &1 * x + y <= &2 * x`) THEN
  REWRITE_TAC[ARITH_RULE `n + SUC d = (n + 1) + d`; GSYM real_div] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n + 1`) THEN REWRITE_TAC[ADD_EQ_0; ARITH] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
  SIMP_TAC[GSYM REAL_POW_SUB; REAL_OF_NUM_EQ; ARITH; FACT_MONO; LE_ADD] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&10 pow 1` THEN
  CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC REAL_POW_MONO] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[GSYM ADD1; FACT] THEN
  MATCH_MP_TAC(ARITH_RULE
   `1 * x <= SUC n * x /\ ~(n * x = 0) ==> 1 <= SUC n * x - x`) THEN
  ASM_SIMP_TAC[LE_MULT_RCANCEL; MULT_EQ_0] THEN
  REWRITE_TAC[GSYM LT_NZ; FACT_LT] THEN ARITH_TAC);;
```

### Informal statement
For all natural numbers `d` and `n`, if `n` is not equal to 0, then the sum of the sequence `&1 / &10 pow FACT k` from `n` to `n + d` is less than or equal to `&2 / &10 pow FACT n`.

### Informal sketch
The proof is by induction on `d`.
- Base case (`d = 0`): show that `&1 / &10 pow FACT n <= &2 / &10 pow FACT n`, which reduces to proving that `1 <= 2`, an arithmetic fact.
- Inductive step: assume that the inequality `sum(n..n+d) (\k. &1 / &10 pow FACT k) <= &2 / &10 pow (FACT n)` holds, and we need to prove `sum(n..n+SUC d) (\k. &1 / &10 pow FACT k) <= &2 / &10 pow (FACT n)`.
  - Expand the sum `sum(n..n+SUC d)` to `sum(n..n+d) + (&1 / &10 pow FACT (n + SUC d))`.
  - By the inductive hypothesis and basic arithmetic, it suffices to show that `&1 / &10 pow FACT (n + 1 + d) <= &1 / &10 pow FACT n`. Furthermore it suffices to prove that `&1 / &10 pow FACT (n + 1) <= &1 / &10 pow FACT n`, which is equivalent to `&1 / &10 pow (FACT (n+1)) <= &1 / (&2 * &10 pow (FACT n))`.
  - Then rewrite `n + SUC d` as `(n + 1) + d` and use the inductive hypothesis.
  - Show that `&1 / (&10 pow FACT (SUC n)) <= &1 / &10 pow FACT n`.
  - Show that `&1 / &10 pow FACT (SUC n) <= &1 / &10 pow (FACT n) * &2`
  - Simplify the real numbers, exponentials and factorials, where one must show that `1 <=  (n+1)! / n! * 2`, which boils down to `1 <= (n+1) n! / n! *2`, so `1 <= (n+1)*2`.

### Mathematical insight
This theorem provides an upper bound for the partial sums of the series `Sum (\k. &1 / &10 pow FACT k)`.  The series converges rapidly, and this result is used to effectively bound the error when approximating the infinite sum by a finite partial sum.  This bound is crucial to showing that a truncated version of the series is accurate to a known number of decimal places.

### Dependencies
- `ADD_CLAUSES`
- `SUM_SING_NUMSEG`
- `real_div`
- `REAL_LE_RMUL`
- `REAL_LE_INV_EQ`
- `REAL_POW_LE`
- `REAL_OF_NUM_LE`
- `ARITH`
- `SUM_CLAUSES_LEFT`
- `LE_ADD`
- `REAL_ARITH `y <= x ==> &1 * x + y <= &2 * x``
- `ARITH_RULE `n + SUC d = (n + 1) + d``
- `GSYM real_div`
- `ADD_EQ_0`
- `REAL_ARITH `a <= b ==> x <= a ==> x <= b``
- `REAL_LE_LDIV_EQ`
- `REAL_POW_LT`
- `REAL_OF_NUM_LT`
- `REAL_MUL_SYM`
- `GSYM REAL_POW_SUB`
- `REAL_OF_NUM_EQ`
- `FACT_MONO`
- `REAL_LE_TRANS`
- `REAL_RAT_REDUCE_CONV`
- `GSYM ADD1`
- `FACT`
- `ARITH_RULE `1 * x <= SUC n * x /\ ~(n * x = 0) ==> 1 <= SUC n * x - x``
- `LE_MULT_RCANCEL`
- `MULT_EQ_0`
- `GSYM LT_NZ`
- `FACT_LT`

### Porting notes (optional)
The heavy use of `REAL_ARITH` and `ARITH_TAC` suggests that a proof assistant with strong arithmetic and real number reasoning capabilities is desirable. The tactic `MATCH_MP_TAC` suggests rewriting with implications, which will need to be handled appropriately. The use of `ONCE_REWRITE_TAC` and `FIRST_X_ASSUM` illustrates some fine-grained control of rewriting. The factorial function `FACT` should be available or definable in the target proof assistant.


---

## LIOUVILLE_PSUM_BOUND

### Name of formal statement
LIOUVILLE_PSUM_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LIOUVILLE_PSUM_BOUND = prove
 (`!n d. ~(n = 0)
         ==> sum(n,d) (\k. &1 / &10 pow FACT k) <= &2 / &10 pow (FACT n)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `d = 0` THEN
  ASM_SIMP_TAC[sum; REAL_LE_DIV; REAL_POW_LE; REAL_POS] THEN
  ASM_SIMP_TAC[PSUM_SUM_NUMSEG] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(d = 0) ==> (n + d) - 1 = n + (d - 1)`] THEN
  ASM_SIMP_TAC[LIOUVILLE_SUM_BOUND]);;
```

### Informal statement
For all natural numbers `n` and `d`, if `n` is not equal to 0, then the sum from `n` to `n + d` of the function that maps `k` to `1 / (10 ^ (k!))` is less than or equal to `2 / (10 ^ (n!))`.

### Informal sketch
The proof proceeds by induction, splitting based on whether `d` equals 0.

- **Base Case (d = 0):**  If `d` is 0, the sum from `n` to `n` reduces to a single term: `1 / (10 ^ (n!))`.  The goal then becomes to show that `1 / (10 ^ (n!)) <= 2 / (10 ^ (n!))`. This follows from the properties `REAL_LE_DIV`, `REAL_POW_LE`, and `REAL_POS` and the definition of `sum`.
- **Inductive Step (d != 0):** The inductive step assumes that the statement holds for `d - 1` and aims to prove it for `d`. The sum from `n` to `n + d` is rewritten as `(1 / (10 ^ ((n + d)!))) +  sum(n, d - 1) (\k. &1 / &10 pow FACT k)`. The inductive hypothesis (`LIOUVILLE_SUM_BOUND`) is then invoked to show that `sum(n, d - 1) (\k. &1 / &10 pow FACT k) <= &2 / &10 pow (FACT n)`. The definition `PSUM_SUM_NUMSEG` is used to split the sum. Finally arithmetic reasoning involving `(n + d) - 1 = n + (d - 1)` and inequalities is applied to complete the proof.

### Mathematical insight
This theorem establishes an upper bound on the partial sum of a specific series. The series has terms of the form `1 / (10 ^ (k!))`, and the theorem shows that the sum from `n` to `n + d` is bounded above by `2 / (10 ^ (n!))`. This suggests that the series converges rapidly. Essentially, the factorial in the exponent makes the terms decrease extremely quickly.

### Dependencies
- Definitions: `sum`, `PSUM_SUM_NUMSEG`
- Theorems: `REAL_LE_DIV`, `REAL_POW_LE`, `REAL_POS`, `LIOUVILLE_SUM_BOUND`
- Rules: `ARITH_RULE`


---

## LIOUVILLE_SUMS

### Name of formal statement
LIOUVILLE_SUMS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LIOUVILLE_SUMS = prove
 (`(\k. &1 / &10 pow FACT k) sums liouville`,
  REWRITE_TAC[liouville] THEN MATCH_MP_TAC SUMMABLE_SUM THEN
  REWRITE_TAC[SER_CAUCHY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `inv(e)` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `2 * N + 1` THEN
  REWRITE_TAC[GE] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `&2 / &10 pow (FACT m)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= a ==> abs x <= a`) THEN
    ASM_SIMP_TAC[SUM_POS; REAL_LE_DIV; REAL_POW_LE; REAL_POS] THEN
    MATCH_MP_TAC LIOUVILLE_PSUM_BOUND THEN
    UNDISCH_TAC `2 * N + 1 <= m` THEN ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `e * &(2 * N + 1)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&1 < (n + &1 / &2) * e ==> &2 < e * (&2 * n + &1)`) THEN
    ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ; real_div; REAL_MUL_LID] THEN
    UNDISCH_TAC `inv(e) <= &N` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `10 EXP m` THEN
  REWRITE_TAC[FACT_LE_REFL; LE_EXP; ARITH] THEN SIMP_TAC[EXP_LE_REFL; ARITH]);;
```
### Informal statement
The infinite sum of `1 / 10^(FACT k)` for `k` ranging from 0 to infinity is a Liouville number.

### Informal sketch
The proof shows that the infinite sum `liouville` of `1 / 10^(FACT k)` is a Liouville number by verifying the following conditions:
- The series `liouville` is summable. This uses the theorem `liouville` (presumably defining `liouville` in terms of a sum), and `SUMMABLE_SUM` to prove summability.
- We demonstrate that for every real number `e > 0`, there exist integers `p` and `q` such that `q > 1` and `abs(liouville - p/q) < e/q`.
  - We introduce an arbitrary positive real number `e`.
  - We pick a natural number `N` such that `1/e <= N`. This is justified by the Archimedean property of real numbers (`REAL_ARCH_SIMPLE`).
  - We choose `m` to be `2 * N + 1` and show that `abs(liouville - p/q) < e/q`, where `q = 10^(FACT m)` and `p` is the partial sum of `liouville` up to `m`. We have `q >= 1`.
  - We then show that `abs(liouville - (sum k. if k <= m then 1 / 10^(FACT k) else 0) ) < 2 / 10^(FACT m)`. This involves bounding the tail of the series using `LIOUVILLE_PSUM_BOUND`. 
  - We need to prove that `2 / 10^(FACT m) < e / 10^(FACT m)`, which simplifies to proving `2 < e`.
  - Then, we show that `2 < e` by using the fact that `inv(e) <= N`, which implies `e * (2 * N + 1) > 2`. This relies on rewriting rules for real number arithmetic such as `REAL_OF_NUM_ADD`, `REAL_OF_NUM_MUL`, `REAL_LT_LDIV_EQ`.
  - Finally we show that `10^(FACT m) > 1` by showing that `FACT m > 0`.

### Mathematical insight
This theorem demonstrates that the Liouville constant, the sum of the series `1 / 10^(FACT k)`, is indeed a Liouville number. A Liouville number is a real number that can be very closely approximated by rational numbers. More formally, for any positive integer `n`, there exist integers `p` and `q` with `q > 1` such that `|x - p/q| < 1/q^n`. This property distinguishes Liouville numbers from algebraic numbers, as the latter cannot be approximated this closely.

### Dependencies
- Definitions:
    - `liouville`
- Theorems:
    - `SUMMABLE_SUM`
    - `SER_CAUCHY`
    - `REAL_ARCH_SIMPLE`
    - `LIOUVILLE_PSUM_BOUND`
    - `REAL_LET_TRANS`
    - `REAL_ARITH` (multiple instances)
    - `REAL_LTE_TRANS`
    - `LE_TRANS`
    - `FACT_LE_REFL`
    - `LE_EXP`
- Other:
    - `SUM_POS`
    - `REAL_LE_DIV`
    - `REAL_POW_LE`
    - `REAL_POS`
    - `REAL_LT_LDIV_EQ`
    - `REAL_POW_LT`
    - `REAL_OF_NUM_LT`
    - `EXP_LE_REFL`
    - `REAL_LE_LMUL_EQ`
    - `REAL_OF_NUM_POW`
    - `REAL_OF_NUM_LE`
    - `FACT_LE_REFL`

### Porting notes (optional)
- Porting this proof to other proof assistants might require careful attention to real number arithmetic and the Archimedean property. The handling of summations and series convergence also needs to be considered. Tactics like `REAL_ARITH_TAC` and `ASM_SIMP_TAC` which automate parts of real number reasoning might need to be replaced with more explicit proof steps depending on the target proof assistant. The `EXISTS_TAC` tactic is essentially existential quantifier instantiation and should be replaced with the appropriate tactic or command to introduce a witness.


---

## LIOUVILLE_PSUM_LE

### Name of formal statement
LIOUVILLE_PSUM_LE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LIOUVILLE_PSUM_LE = prove
 (`!n. sum(0,n) (\k. &1 / &10 pow FACT k) <= liouville`,
  GEN_TAC THEN REWRITE_TAC[suminf] THEN MATCH_MP_TAC SEQ_LE THEN
  EXISTS_TAC `\j:num. sum(0,n) (\k. &1 / &10 pow FACT k)` THEN
  EXISTS_TAC `\n:num. sum(0,n) (\k. &1 / &10 pow FACT k)` THEN
  REWRITE_TAC[SEQ_CONST; GSYM sums; LIOUVILLE_SUMS] THEN
  EXISTS_TAC `n:num` THEN X_GEN_TAC `m:num` THEN SIMP_TAC[GE; LE_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC) THEN
  REWRITE_TAC[GSYM SUM_SPLIT; ADD_CLAUSES; REAL_LE_ADDR] THEN
  SIMP_TAC[SUM_POS; REAL_LE_DIV; REAL_POW_LE; REAL_POS]);;
```

### Informal statement
For all natural numbers `n`, the sum from `k = 0` to `n` of `1 / (10 ^ FACT k)` is less than or equal to Liouville's number (defined as the infinite sum of `1 / (10 ^ FACT k)`).

### Informal sketch
The proof proceeds as follows:

- Start with the goal: `!n. sum(0,n) (\k. &1 / &10 pow FACT k) <= liouville`.
- Rewrite the goal using `suminf` to express `liouville` as an infinite sum: `suminf (\k. &1 / &10 pow FACT k)`.
- Apply `MATCH_MP_TAC SEQ_LE`. This likely uses a theorem about sequences where if a sequence converges and its partial sums are less than or equal to the limit, then the partial sums are less than or equal to the limit for all n.
- Show the existence of `sum(0,n) (\k. &1 / &10 pow FACT k)` and `suminf (\k. &1 / &10 pow FACT k)`.
- Rewrite using `SEQ_CONST` (sequence of constants), `GSYM sums` (symmetric of `sums`), and `LIOUVILLE_SUMS` to relate the partial sums to the infinite sum representing Liouville's number.
- Show that there exists an `n` for which the partial sum is defined, introducing a new variable `m`.
- Use simplification with `GE` (greater than or equal), `LE_EXISTS` (less than or equal exists).
- Introduce a variable `d` and apply substitution. This step likely manipulates the summation index or terms to allow comparison.
- Rewrite using `GSYM SUM_SPLIT` to split the infinite sum into parts, `ADD_CLAUSES` (likely dealing with addition properties), and `REAL_LE_ADDR` (properties of addition and less than or equal on real numbers).
- Simplify using `SUM_POS` (positivity of the sum terms), `REAL_LE_DIV` (properties of division and less than or equal on real numbers), `REAL_POW_LE` (properties of powers and less than or equal on real numbers), and `REAL_POS` (positivity of real numbers). This likely involves showing the remaining terms are positive and contribute to the inequality.

### Mathematical insight
The theorem states that any partial sum of the series defining Liouville's number is less than or equal to Liouville's number itself. This is a fundamental property of convergent series with positive terms. Liouville's number is a transcendental number constructed to have very good approximations by rational numbers, and this theorem establishes a basic bound on its partial sums.

### Dependencies
- `suminf`
- `SEQ_LE`
- `SEQ_CONST`
- `sums`
- `LIOUVILLE_SUMS`
- `GE`
- `LE_EXISTS`
- `SUM_SPLIT`
- `ADD_CLAUSES`
- `REAL_LE_ADDR`
- `SUM_POS`
- `REAL_LE_DIV`
- `REAL_POW_LE`
- `REAL_POS`

### Porting notes (optional)
The proof relies on properties of real numbers, summation, and inequalities. Ensure the target proof assistant has adequate libraries for real analysis and summation. The tactics suggest a focus on rewriting and simplification, which may need to be adapted based on the automation capabilities of the target system. Specifically, `MATCH_MP_TAC` and `X_CHOOSE_THEN` might require more manual translation.


---

## LIOUVILLE_PSUM_LT

### Name of formal statement
LIOUVILLE_PSUM_LT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LIOUVILLE_PSUM_LT = prove
 (`!n. sum(0,n) (\k. &1 / &10 pow FACT k) < liouville`,
  GEN_TAC THEN MP_TAC(SPEC `SUC n` LIOUVILLE_PSUM_LE) THEN SIMP_TAC[sum] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < e ==> x + e <= y ==> x < y`) THEN
  SIMP_TAC[REAL_LT_DIV; REAL_POW_LT; REAL_OF_NUM_LT; ARITH]);;
```
### Informal statement
For all natural numbers `n`, the sum from `k = 0` to `n` of `1 / 10^k!` is strictly less than `liouville`.

### Informal sketch
The proof proceeds by induction.
- First, the goal is to prove `sum(0, n) (\k. &1 / &10 pow FACT k) < liouville` for all `n`.
- The proof uses mathematical induction, by applying `GEN_TAC` then `MP_TAC` with `SPEC SUC n LIOUVILLE_PSUM_LE`.
- Then, simplifies using the definition of `sum`.
- Match the goal with `REAL_ARITH &0 < e ==> x + e <= y ==> x < y`.
- Finally, use some arithmetic simplification tactics namely `REAL_LT_DIV`, `REAL_POW_LT`, `REAL_OF_NUM_LT` and `ARITH`.

### Mathematical insight
The theorem states that the partial sums of the series `sum(0, n) (\k. &1 / &10 pow FACT k)` are strictly less than `liouville`. This provides an upper bound for these partial sums and is probably paving the way to prove the convergence of the series, and that the series converges to `liouville`.

### Dependencies
- `LIOUVILLE_PSUM_LE`
- `sum`
- `REAL_LT_DIV`
- `REAL_POW_LT`
- `REAL_OF_NUM_LT`
- `ARITH`


---

## LIOVILLE_PSUM_DIFF

### Name of formal statement
LIOUVILLE_PSUM_DIFF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LIOVILLE_PSUM_DIFF = prove
 (`!n. ~(n = 0)
       ==> liouville
             <= sum(0,n) (\k. &1 / &10 pow FACT k) + &2 / &10 pow (FACT n)`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SEQ_LE THEN
  EXISTS_TAC `\n. sum(0,n) (\k. &1 / &10 pow FACT k)` THEN
  EXISTS_TAC
    `\j:num. sum (0,n) (\k. &1 / &10 pow FACT k) + &2 / &10 pow FACT n` THEN
  REWRITE_TAC[SEQ_CONST; GSYM sums; LIOUVILLE_SUMS] THEN
  EXISTS_TAC `n:num` THEN X_GEN_TAC `m:num` THEN SIMP_TAC[GE; LE_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC) THEN
  REWRITE_TAC[GSYM SUM_SPLIT; REAL_LE_LADD] THEN
  ASM_SIMP_TAC[ADD_CLAUSES; LIOUVILLE_PSUM_BOUND]);;
```
### Informal statement
For all natural numbers `n`, if `n` is not equal to 0, then Liouville's constant is less than or equal to the sum from 0 to `n` of the function that maps `k` to `1 / 10^(k!)`, plus `2 / 10^(n!)`.

### Informal sketch
The proof demonstrates that for any non-zero natural number `n`, the Liouville constant is bounded above by the partial sum of the series defining it, up to the `n`-th term, plus a correction term.
- Initially, the goal is to prove the stated inequality for all non-zero `n`.
- The proof starts by discharging the assumption that `n` is not zero, introducing it as an assumption.
- It uses `SEQ_LE` to establish the fundamental ordering properties concerning the definition of a sequence's limit.
- It introduces an existential quantifier for the `n`-th partial sum.
- Simultaneously, an existential quantifier for the corrected partial sum (adding `2 / 10^(n!)`) is established.
- The partial sums are rewritten using the definition of `sums` and the theorem `LIOUVILLE_SUMS` to relate Liouville's constant to partial sums of its defining series.
- An existential quantifier is introduced for `n`.
- The goal is generalized w.r.t to a variable `m`.
- Simplification is performed using `GE` (greater than or equal) and `LE_EXISTS` (less than or equal exists) to refine the conditions.
- It eliminates the assumptions about `d` using `X_CHOOSE_THEN` and `SUBST_ALL_TAC`.
- The proof employs a theorem `SUM_SPLIT` (which splits the summation range) and `REAL_LE_LADD` (real less or equal left add) to manipulate the sums.
- Finally, a theorem called `LIOUVILLE_PSUM_BOUND` regarding the bound of partial sums is applied.

### Mathematical insight
This theorem provides an explicit upper bound on the difference between Liouville's constant and its partial sum. The bound is given by `2 / 10^(n!)`. This result is important because it quantifies how well partial sums approximate Liouville's constant, and the rate of convergence. This is important for computational estimates and for proving properties based on approximation.

### Dependencies
- `SEQ_LE` – establishes the fundamental ordering properties for sequence limit definition.
- `sums` – definition of partial sums.
- `LIOUVILLE_SUMS` – relates Liouville's constant to its sums.
- `GE` – greater than or equal relation.
- `LE_EXISTS` – theorem about less than or equals existence.
- `SUM_SPLIT` - Theorem to split summation ranges.
- `REAL_LE_LADD` - Real less or equal left add.
- `LIOUVILLE_PSUM_BOUND` – theorem about Liouville's constant partial sums.


---

## TRANSCENDENTAL_LIOUVILLE

### Name of formal statement
TRANSCENDENTAL_LIOUVILLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TRANSCENDENTAL_LIOUVILLE = prove
 (`transcendental(liouville)`,
  REWRITE_TAC[transcendental] THEN DISCH_THEN(MP_TAC o MATCH_MP LIOUVILLE) THEN
  REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `c:real`] THEN
  REWRITE_TAC[DE_MORGAN_THM; real_gt; REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&10`; `&2 / c`] REAL_ARCH_POW) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  ABBREV_TAC `n = m + k + 1` THEN
  EXISTS_TAC `nsum(0..n-1) (\i. 10 EXP (FACT(n-1) - FACT i))` THEN
  EXISTS_TAC `10 EXP (FACT(n-1))` THEN REWRITE_TAC[EXP_EQ_0; ARITH] THEN
  SUBGOAL_THEN
   `&(nsum(0..n-1) (\i. 10 EXP (FACT(n-1) - FACT i))) / &(10 EXP (FACT(n-1))) =
    sum(0..n-1) (\k. &1 / &10 pow (FACT k))`
  SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_OF_NUM_SUM_NUMSEG; GSYM SUM_LMUL] THEN
    SIMP_TAC[GSYM REAL_OF_NUM_POW; REAL_POW_SUB; REAL_OF_NUM_EQ; ARITH;
             FACT_MONO; real_div; REAL_MUL_ASSOC] THEN
    SIMP_TAC[REAL_MUL_LINV; REAL_OF_NUM_EQ; REAL_POW_EQ_0; ARITH] THEN
    REWRITE_TAC[REAL_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(GEN `f:num->real`
   (SPECL [`f:num->real`; `0`; `m + k + 1`] PSUM_SUM_NUMSEG)) THEN
  REWRITE_TAC[ADD_EQ_0; ARITH; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  SIMP_TAC[LIOUVILLE_PSUM_LT; REAL_LT_IMP_NE] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN
  REWRITE_TAC[REAL_SUB_LE; LIOUVILLE_PSUM_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 / &10 pow (FACT n)` THEN
  REWRITE_TAC[REAL_LE_SUB_RADD] THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LIOVILLE_PSUM_DIFF THEN EXPAND_TAC "n" THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LIOVILLE_PSUM_DIFF] THEN
  REWRITE_TAC[REAL_OF_NUM_POW; GSYM EXP_MULT] THEN
  SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LT_NZ; EXP_EQ_0; ARITH] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&10 pow k` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
  SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; LT_NZ; EXP_EQ_0; ARITH] THEN
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  REWRITE_TAC[GSYM EXP_ADD; LE_EXP; ARITH_EQ] THEN EXPAND_TAC "n" THEN
  REWRITE_TAC[ARITH_RULE `(m + k + 1) - 1 = m + k`] THEN
  REWRITE_TAC[num_CONV `1`; ADD_CLAUSES; FACT] THEN
  REWRITE_TAC[ARITH_RULE
   `k + f * m <= SUC(m + k) * f <=> k <= (k + 1) * f`] THEN
  GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `k = k * 1`] THEN
  MATCH_MP_TAC LE_MULT2 THEN REWRITE_TAC[LE_ADD] THEN
  REWRITE_TAC[FACT_LT; ARITH_RULE `1 <= x <=> 0 < x`]);;
```
### Informal statement
The real number `liouville` is transcendental.

### Informal sketch
The proof shows that `liouville` is transcendental by showing that it does not satisfy the definition of an algebraic number, meaning it is not the root of any non-zero polynomial with integer coefficients.

- Assume for contradiction that `liouville` is algebraic. This implies that for some natural number `m` and real number `c` greater than 0, the inequality `abs(liouville - p / q) < 1 / q pow m` holds for all rationals `p / q`.
- Instantiate `REAL_ARCH_POW` to deduce the existence of a natural number `k` such that `10` is greater than `2 / c` raised to the power of `fact(k)`.
- Define `n` as `m + k + 1`.
- Let `x` be the partial sum from `i = 0` to `n - 1` of `10` to the power of `fact(n - 1) - fact(i)`.
- Show that `x / (10 ^ fact(n - 1))` is equal to the sum from `0` to `n - 1` of `1/ (10 ^ fact(k))`. This involves rewriting the sum of multiples as a multiple of sums.
- Use this fact along with `LIOUVILLE_PSUM_LT` to show that the absolute value of `liouville` minus the partial sum `x / (10 ^ fact(n - 1))` is less than `2 / (10 ^ fact(n))`.
- By contradiction hypothesis, `abs(liouville - x / (10 ^ fact(n - 1)) < 1 / (10 ^ fact(n - 1)) pow m`.
- Apply transitivity on inequality and derive a contradiction by showing that `1/(10 ^ fact(n-1)) pow m` is eventually less than `2/(10 ^ fact(n))`.
- This final stage involves several simplifications using properties of exponents, real numbers, and arithmetic.

### Mathematical insight
The theorem demonstrates that the Liouville constant is a transcendental number. The Liouville constant is a specific example of a Liouville number, which are real numbers that can be very closely approximated by rational numbers. This property makes them transcendental, as algebraic numbers cannot be "too closely" approximated by rationals.

### Dependencies
- `transcendental` (definition of transcendental number)
- `LIOUVILLE` (definition of the Liouville constant)
- `NOT_EXISTS_THM, NOT_FORALL_THM, DE_MORGAN_THM` (theorems about logical negation)
- `real_gt, REAL_NOT_LT` (theorems about real number inequalities)
- `REAL_ARCH_POW` (Real Archimedean property)
- `real_div, REAL_MUL_SYM, REAL_OF_NUM_SUM_NUMSEG, SUM_LMUL` (theorems about real numbers and sums)
- `GSYM REAL_OF_NUM_POW, REAL_POW_SUB, REAL_OF_NUM_EQ, ARITH, FACT_MONO, real_div, REAL_MUL_ASSOC, REAL_MUL_LINV, REAL_POW_EQ_0, REAL_MUL_LID` (real number simplification rules)
- `PSUM_SUM_NUMSEG` (Summation properties)
- `ADD_EQ_0, ADD_CLAUSES` (Arithmetic simplification)
- `LIOUVILLE_PSUM_LT, REAL_LT_IMP_NE` (Properties of the Liouville constant)
- `REAL_ARITH` (Real arithmetic tactics)
- `REAL_SUB_LE, LIOUVILLE_PSUM_LE` (Properties of the Liouville constant)
- `REAL_LE_TRANS` (Transitivity of inequality)
- `REAL_LE_SUB_RADD, REAL_ADD_SYM, LIOVILLE_PSUM_DIFF` (Properties of Liouville Constant and inequality)
- `REAL_OF_NUM_POW, GSYM EXP_MULT` (Properties of exponential and real numbers)
- `REAL_LE_LDIV_EQ, REAL_OF_NUM_LT, LT_NZ, EXP_EQ_0` (Properties of exponential and real numbers)
- `real_div, GSYM REAL_MUL_ASSOC, REAL_LE_RDIV_EQ, REAL_OF_NUM_MUL, REAL_OF_NUM_LE` (Properties of real numbers)
- `GSYM EXP_ADD, LE_EXP` (Properties of exponential and real numbers)
- `num_CONV, FACT` (Number theory)
- `ARITH_RULE` (Arithmetic Simplification)
- `LE_MULT2, LE_ADD` (Inequality properties)
- `FACT_LT` (Factorial properties)

### Porting notes (optional)
- The proof heavily relies on the `REAL_ARITH` tactic for automating inequalities. The target proof assistant will need a similar tactic or a manual proof of each inequality.
- The rewriting steps involving real number arithmetic and simplification are extensive. Ensure that the target system has similar lemmas and automation for real number reasoning.
- The handling of sums may differ. Ensure that the target system has equivalent theorems for manipulating sums over number ranges.


---

