# fourier.ml

## Overview

Number of statements: 145

`fourier.ml` defines square integrable functions from R to R and develops the basic theory of Fourier series. It builds upon the `lpspaces.ml` file from the Multivariate analysis library. The file likely contains definitions related to Fourier coefficients, convergence properties, and related theorems for square integrable functions.


## SUM_NUMBERS

### Name of formal statement
SUM_NUMBERS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_NUMBERS = prove
 (`!n. sum(0..n) (\r. &r) = (&n * (&n + &1)) / &2`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0; GSYM REAL_OF_NUM_SUC] THEN
  REAL_ARITH_TAC);;
```

### Informal statement
For all natural numbers `n`, the sum of the real representations of the numbers from 0 to `n` (inclusive) is equal to `(&n * (&n + &1)) / &2`.

### Informal sketch
The proof proceeds by induction on `n`.

- Base case: `n = 0`. The sum from 0 to 0 is just `&0`, and the right-hand side is `(&0 * (&0 + &1)) / &2 = &0 / &2 = &0`.
- Inductive step: Assume the formula holds for `n`. We need to show that it holds for `n+1`. That is, we must show that the sum from 0 to `n+1` of `&r` is equal to `(&(n+1) * (&(n+1) + &1)) / &2`. The left-hand side can be written as (`sum(0..n) (\r. &r)`) + `&(n+1)`. By the inductive hypothesis, this is equal to `(&n * (&n + &1)) / &2 + &(n+1)`. The goal then simplifies to showing `(&n * (&n + &1)) / &2 + &(n+1) = (&(n+1) * (&(n+1) + &1)) / &2`, which is an arithmetic fact.

The tactic `INDUCT_TAC` performs the induction. `ASM_REWRITE_TAC` simplifies the goal using the clauses for `SUM_CLAUSES_NUMSEG` (likely laws for sums over number segments), `LE_0` (probably `0 <= n` for any natural number n), and `GSYM REAL_OF_NUM_SUC` (rewriting `REAL_OF_NUM (SUC n)` to `&n + &1`). Finally, `REAL_ARITH_TAC` solves the remaining arithmetic goal.

### Mathematical insight
This theorem states the well-known formula for the sum of the first n natural numbers represented as real numbers. It is a fundamental result in arithmetic and is used in many areas of mathematics.

### Dependencies
- `Multivariate/lpspaces.ml` (stated `needs` at the top)
- `SUM_CLAUSES_NUMSEG`
- `LE_0`
- `REAL_OF_NUM_SUC`

### Porting notes (optional)
- The tactic `REAL_ARITH_TAC` represents a significant amount of automation for real arithmetic. Target systems might require explicit invocation of specific arithmetic lemmas or more manual manipulation to achieve the same result.
- The definition of `sum` and number segments may need to be explicitly provided if the target system lacks similar constructs. The behavior of `sum` over empty ranges should be checked for consistency.


---

## REAL_INTEGRABLE_REFLECT_AND_ADD

### Name of formal statement
REAL_INTEGRABLE_REFLECT_AND_ADD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_INTEGRABLE_REFLECT_AND_ADD = prove
 (`!f a. f real_integrable_on real_interval[--a,a]
         ==> f real_integrable_on real_interval[&0,a] /\
             (\x. f(--x)) real_integrable_on real_interval[&0,a] /\
             (\x. f x + f(--x)) real_integrable_on real_interval[&0,a]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ b /\ (a /\ b ==> c) ==> a /\ b /\ c`) THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[GSYM REAL_INTEGRABLE_REFLECT] THEN
    REWRITE_TAC[REAL_NEG_NEG; ETA_AX];
    SIMP_TAC[REAL_INTEGRABLE_ADD]] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] REAL_INTEGRABLE_SUBINTERVAL)) THEN
  REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN REAL_ARITH_TAC);;
```
### Informal statement
For any function `f` and any real number `a`, if `f` is Riemann integrable on the closed real interval from `-a` to `a` (inclusive), then `f` is Riemann integrable on the closed real interval from `0` to `a` (inclusive), the reflection of `f` across the y-axis (i.e., the function defined by mapping `x` to `f(-x)`) is Riemann integrable on the closed real interval from `0` to `a` (inclusive), and the function defined by mapping `x` to `f(x) + f(-x)` is Riemann integrable on the closed real interval from `0` to `a` (inclusive).

### Informal sketch
The proof proceeds as follows:
- Assume that `f` is Riemann integrable on the interval `[--a, a]`.
- Prove that `f` is Riemann integrable on `[0, a]`. This uses the theorem `REAL_INTEGRABLE_SUBINTERVAL`, the fact that the interval `[0, a]` is a subset of `[--a, a]` using `SUBSET_REAL_INTERVAL`, and some real arithmetic.
- Prove that the reflection of `f`, `(\x. f(--x))`, is Riemann integrable on `[0, a]`. First rewrite with `REAL_INTEGRABLE_REFLECT`, `REAL_NEG_NEG`, and `ETA_AX`.
- Prove that the function `(\x. f x + f(--x))` is Riemann integrable on `[0, a]`. This uses the theorem `REAL_INTEGRABLE_ADD`.
- Combine the three integrability arguments into the final conclusion, using a tautology.

### Mathematical insight
This theorem states that if a function `f` is integrable on a symmetric interval `[-a, a]`, then `f` itself, its reflection, and their sum, are integrable on `[0, a]`. This is useful for simplifying integrals over symmetric intervals in integration.

### Dependencies
- `REAL_INTEGRABLE_REFLECT`
- `REAL_NEG_NEG`
- `ETA_AX`
- `REAL_INTEGRABLE_ADD`
- `REAL_INTEGRABLE_SUBINTERVAL`
- `SUBSET_REAL_INTERVAL`
- `IMP_CONJ`


---

## REAL_INTEGRAL_REFLECT_AND_ADD

### Name of formal statement
REAL_INTEGRAL_REFLECT_AND_ADD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_INTEGRAL_REFLECT_AND_ADD = prove
 (`!f a. f real_integrable_on real_interval[--a,a]
         ==> real_integral (real_interval[--a,a]) f =
             real_integral (real_interval[&0,a])
                           (\x. f x + f(--x))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 <= a` THENL
   [MP_TAC(SPECL [`f:real->real`; `--a:real`; `a:real`; `&0:real`]
        REAL_INTEGRAL_COMBINE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_ADD; REAL_INTEGRABLE_REFLECT_AND_ADD] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_INTEGRAL_REFLECT] THEN
    REWRITE_TAC[REAL_NEG_NEG; ETA_AX; REAL_NEG_0; REAL_ADD_AC];
    ASM_SIMP_TAC[REAL_INTEGRAL_NULL;
                 REAL_ARITH `~(&0 <= a) ==> a <= --a /\ a <= &0`]]);;
```
### Informal statement
For all functions `f` and real numbers `a`, if `f` is real integrable on the real interval `--a` to `a`, then the real integral of `f` on the real interval `--a` to `a` is equal to the real integral on the real interval `0` to `a` of the function that maps `x` to `f x + f(--x)`.

### Informal sketch
The proof proceeds as follows:
- Assume `f` is integrable on the interval `[--a, a]`.
- Split the integral `integral[--a, a]`  into `integral[--a, 0]` + `integral[0, a]` using `REAL_INTEGRAL_COMBINE`.
- Apply the change of variable `x` to `--x` on the integral from `--a` to `0`, using `REAL_INTEGRAL_REFLECT`, which transforms `integral[--a, 0] f x` into `integral[0, a] f (--x)`. The integrability of `f (--x)` is justified by `REAL_INTEGRABLE_REFLECT_AND_ADD`.
- Combine the two integrals `integral[0, a] f (--x)` and `integral[0, a] f x` using `REAL_INTEGRAL_ADD` to obtain `integral[0, a] (f x + f (--x))`.
- The case where `~(0 <= a)` i.e. `a < 0` requires showing the integral is zero using `REAL_INTEGRAL_NULL` since in this case `a <= --a`. This uses the fact that when `a < 0`, the interval `[--a, a]` is the empty interval.

### Mathematical insight
This theorem provides a useful symmetry property for real integrals. It states that the integral of a function over a symmetric interval `[-a, a]` can be expressed in terms of the integral over `[0, a]` of the sum of the function and its reflection. This is especially useful when dealing with even or odd functions, as it simplifies the computation of the integral. If f is even, then the integral from -a to a is twice the integral from 0 to a.

### Dependencies
- `REAL_INTEGRAL_COMBINE`
- `REAL_INTEGRAL_ADD`
- `REAL_INTEGRABLE_REFLECT_AND_ADD`
- `REAL_INTEGRAL_REFLECT`
- `REAL_NEG_NEG`
- `ETA_AX`
- `REAL_NEG_0`
- `REAL_ADD_AC`
- `REAL_INTEGRAL_NULL`


---

## l2product

### Name of formal statement
l2product

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let l2product = new_definition
 `l2product s f g = real_integral s (\x. f(x) * g(x))`;;
```

### Informal statement
The `l2product` of a set `s` and two functions `f` and `g` is defined as the real integral of the function that maps `x` to the product of `f(x)` and `g(x)` over the set `s`.

### Informal sketch
The definition directly introduces the `l2product` as the `real_integral` of the pointwise product of two functions. There is nothing to prove here.

### Mathematical insight
This definition introduces the inner product for square-integrable functions, which is a key component in defining the L2 space. It's the integral of the product of two functions over a given set.

### Dependencies
- `real_integral`

---
### Name of formal statement
square_integrable_on

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let square_integrable_on = new_definition
 `f square_integrable_on s <=>
     f real_measurable_on s /\ (\x. f(x) pow 2) real_integrable_on s`;;
```

### Informal statement
A function `f` is `square_integrable_on` a set `s` if and only if `f` is `real_measurable_on` `s`, and the function mapping `x` to `f(x)` raised to the power of 2 is `real_integrable_on` `s`.

### Informal sketch
The definition introduces the notion of square-integrability by conjoining real measurability of the function `f` with the real integrability of its square. There is nothing to prove here.

### Mathematical insight
This definition formally defines what it means for a function to be square-integrable, a critical property for functions in L2 spaces. It ensures that both the function and its square have well-defined integrals.

### Dependencies
- `real_measurable_on`
- `real_integrable_on`

---
### Name of formal statement
SQUARE_INTEGRABLE_IMP_MEASURABLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SQUARE_INTEGRABLE_IMP_MEASURABLE = prove
 (`!f s. f square_integrable_on s ==> f real_measurable_on s`,
  SIMP_TAC[square_integrable_on]);;
```

### Informal statement
For all functions `f` and sets `s`, if `f` is `square_integrable_on` `s`, then `f` is `real_measurable_on` `s`.

### Informal sketch
The proof directly unfolds the definition of `square_integrable_on` using `SIMP_TAC`, revealing that real measurability is a necessary condition.

### Mathematical insight
This theorem highlights a key property of square-integrable functions: they must be measurable. This is a fundamental requirement for defining integrals.

### Dependencies
- `square_integrable_on`
- `real_measurable_on`

---
### Name of formal statement
SQUARE_INTEGRABLE_LSPACE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SQUARE_INTEGRABLE_LSPACE = prove
 (`!f s. f square_integrable_on s <=>
         (lift o f o drop) IN lspace (IMAGE lift s) (&2)`,
  REWRITE_TAC[square_integrable_on; lspace; IN_ELIM_THM] THEN
  REWRITE_TAC[real_measurable_on; REAL_INTEGRABLE_ON; RPOW_POW] THEN
  REWRITE_TAC[o_THM; NORM_REAL; GSYM drop; LIFT_DROP] THEN
  REWRITE_TAC[REAL_POW2_ABS; o_DEF]);;
```

### Informal statement
For all functions `f` and sets `s`, `f` is `square_integrable_on` `s` if and only if the composition `lift o f o drop` is an element of the `lspace` of the image of `lift` over `s` with parameter 2.

### Informal sketch
The proof proceeds by:
- Rewriting with the definitions of `square_integrable_on`, `lspace`, and `IN_ELIM_THM`.
- Expanding `real_measurable_on`, `REAL_INTEGRABLE_ON`, and `RPOW_POW`.
- Simplifying using properties of composition (`o_THM`), `NORM_REAL`, `drop`, `lift`, and `REAL_POW2_ABS`.

### Mathematical insight
This theorem connects the concept of square-integrability on a set `s` to membership in the L2 space constructed using `lift` and `drop` operators. This connection allows reasoning about square-integrability in terms of the more general `lspace` structure.

### Dependencies
- `square_integrable_on`
- `lspace`
- `real_measurable_on`
- `REAL_INTEGRABLE_ON`
- `RPOW_POW`
- `o_THM`
- `NORM_REAL`
- `drop`
- `lift`
- `REAL_POW2_ABS`

---
### Name of formal statement
SQUARE_INTEGRABLE_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SQUARE_INTEGRABLE_0 = prove
 (`!s. (\x. &0) square_integrable_on s`,
  REWRITE_TAC[square_integrable_on; REAL_MEASURABLE_ON_0] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_INTEGRABLE_0]);;
```

### Informal statement
For all sets `s`, the zero function (the function that always returns 0) is `square_integrable_on` `s`.

### Informal sketch
The proof proceeds by:
- Expanding the definition of `square_integrable_on`.
- Using the fact that the zero function is `real_measurable_on` any set (`REAL_MEASURABLE_ON_0`).
- Reducing `0 pow 2` to `0` using arithmetic.
- Using the fact that the zero function is `real_integrable_on` any set (`REAL_INTEGRABLE_0`).

### Mathematical insight
This theorem confirms that the zero function is a member of every L2 space. This is a basic but important property that is often used in proofs involving L2 spaces.

### Dependencies
- `square_integrable_on`
- `REAL_MEASURABLE_ON_0`
- `REAL_INTEGRABLE_0`

---
### Name of formal statement
SQUARE_INTEGRABLE_NEG_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SQUARE_INTEGRABLE_NEG_EQ = prove
 (`!f s. (\x. --(f x)) square_integrable_on s <=> f square_integrable_on s`,
  REWRITE_TAC[square_integrable_on; REAL_MEASURABLE_ON_NEG_EQ;
               REAL_POW_NEG; ARITH]);;
```

### Informal statement
For all functions `f` and sets `s`, the function that maps `x` to the negation of `f(x)` is `square_integrable_on` `s` if and only if `f` is `square_integrable_on` `s`.

### Informal sketch
The proof proceeds by:
- Rewriting with the definition of `square_integrable_on`.
- Using the fact that the negation of a function is measurable if and only if the original function is measurable (`REAL_MEASURABLE_ON_NEG_EQ`).
- Using the property `(-x)^2 = x^2` (`REAL_POW_NEG`) together with arithmetic (`ARITH`).

### Mathematical insight
This theorem demonstrates that square-integrability is preserved under negation. This is due to the fact that squaring a function eliminates the sign, so the integrability of the square is unaffected by negation.

### Dependencies
- `square_integrable_on`
- `REAL_MEASURABLE_ON_NEG_EQ`
- `REAL_POW_NEG`

---
### Name of formal statement
SQUARE_INTEGRABLE_NEG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SQUARE_INTEGRABLE_NEG = prove
 (`!f s. f square_integrable_on s ==> (\x. --(f x)) square_integrable_on s`,
  REWRITE_TAC[SQUARE_INTEGRABLE_NEG_EQ]);;
```

### Informal statement
For all functions `f` and sets `s`, if `f` is `square_integrable_on` `s`, then the function that maps `x` to the negation of `f(x)` is also `square_integrable_on` `s`.

### Informal sketch
The proof follows directly from `SQUARE_INTEGRABLE_NEG_EQ` by rewriting.

### Mathematical insight
This theorem states that negating a square-integrable function results in another square-integrable function. This is a direct consequence of `SQUARE_INTEGRABLE_NEG_EQ`.

### Dependencies
- `SQUARE_INTEGRABLE_NEG_EQ`

---
### Name of formal statement
SQUARE_INTEGRABLE_LMUL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SQUARE_INTEGRABLE_LMUL = prove
 (`!f s c. f square_integrable_on s ==> (\x. c * f(x)) square_integrable_on s`,
  SIMP_TAC[square_integrable_on; REAL_MEASURABLE_ON_LMUL] THEN
  SIMP_TAC[REAL_POW_MUL; REAL_INTEGRABLE_LMUL]);;
```

### Informal statement
For all functions `f`, sets `s`, and constants `c`, if `f` is `square_integrable_on` `s`, then the function that maps `x` to `c * f(x)` is also `square_integrable_on` `s`.

### Informal sketch
The proof involves:
- Expanding the definition of `square_integrable_on`.
- Using the fact that multiplying a measurable function by a constant results in a measurable function (`REAL_MEASURABLE_ON_LMUL`).
- Using the properties of powers and multiplication, as well as the fact that multiplying an integrable function by a constant results in an integrable function (`REAL_INTEGRABLE_LMUL`).

### Mathematical insight
This theorem states that multiplying a square-integrable function by a constant results in another square-integrable function. This demonstrates the closure of the space of square-integrable functions under scalar multiplication, which is crucial for it being a vector space.

### Dependencies
- `square_integrable_on`
- `REAL_MEASURABLE_ON_LMUL`
- `REAL_POW_MUL`
- `REAL_INTEGRABLE_LMUL`

---
### Name of formal statement
SQUARE_INTEGRABLE_RMUL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SQUARE_INTEGRABLE_RMUL = prove
 (`!f s c. f square_integrable_on s ==> (\x. f(x) * c) square_integrable_on s`,
  SIMP_TAC[square_integrable_on; REAL_MEASURABLE_ON_RMUL] THEN
  SIMP_TAC[REAL_POW_MUL; REAL_INTEGRABLE_RMUL]);;
```

### Informal statement
For all functions `f`, sets `s`, and constants `c`, if `f` is `square_integrable_on` `s`, then the function that maps `x` to `f(x) * c` is also `square_integrable_on` `s`.

### Informal sketch
The proof mirrors that of `SQUARE_INTEGRABLE_LMUL`, but uses `REAL_MEASURABLE_ON_RMUL` (right multiplication) and `REAL_INTEGRABLE_RMUL`.

### Mathematical insight
This is analogous to `SQUARE_INTEGRABLE_LMUL`, but for right multiplication.

### Dependencies
- `square_integrable_on`
- `REAL_MEASURABLE_ON_RMUL`
- `REAL_POW_MUL`
- `REAL_INTEGRABLE_RMUL`

---
### Name of formal statement
SQUARE_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE_PRODUCT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SQUARE_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE_PRODUCT = prove
 (`!f g s. f square_integrable_on s /\ g square_integrable_on s
           ==> (\x. f(x) * g(x)) absolutely_real_integrable_on s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_REAL_MEASURABLE] THEN
  ASM_SIMP_TAC[REAL_MEASURABLE_ON_MUL; SQUARE_INTEGRABLE_IMP_MEASURABLE] THEN
  MP_TAC(ISPECL [`IMAGE lift s`; `&2`; `&2`;
                 `lift o f o drop`; `lift o g o drop`]
        LSPACE_INTEGRABLE_PRODUCT) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_REWRITE_TAC[GSYM SQUARE_INTEGRABLE_LSPACE; REAL_INTEGRABLE_ON] THEN
  REWRITE_TAC[o_DEF; NORM_REAL; GSYM drop; LIFT_DROP; REAL_ABS_MUL]);;
```

### Informal statement
For all functions `f` and `g`, and sets `s`, if `f` is `square_integrable_on` `s` and `g` is `square_integrable_on` `s`, then the function that maps `x` to `f(x) * g(x)` is `absolutely_real_integrable_on` `s`.

### Informal sketch
The proof proceeds by:
- Stripping the quantifiers and implication.
- Rewriting with the definition of `absolutely_real_integrable_real_measurable`.
- Using the measurability of the product of measurable functions (`REAL_MEASURABLE_ON_MUL`) and the fact that square-integrable functions are measurable (`SQUARE_INTEGRABLE_IMP_MEASURABLE`).
- Applying the `LSPACE_INTEGRABLE_PRODUCT` theorem.
- Rewriting using connections to `lspace`, lifting and dropping to connect back to `square_integrable_on`.

### Mathematical insight
This theorem shows that the pointwise product of two square-integrable functions is absolutely integrable. This is closely related to the Cauchy-Schwarz inequality.

### Dependencies
- `square_integrable_on`
- `absolutely_real_integrable_on`
- `REAL_MEASURABLE_ON_MUL`
- `SQUARE_INTEGRABLE_IMP_MEASURABLE`
- `LSPACE_INTEGRABLE_PRODUCT`
- `SQUARE_INTEGRABLE_LSPACE`
- `REAL_ABS_MUL`

---
### Name of formal statement
SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT = prove
 (`!f g s. f square_integrable_on s /\ g square_integrable_on s
           ==> (\x. f(x) * g(x)) real_integrable_on s`,
  SIMP_TAC[SQUARE_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE_PRODUCT;
           ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE]);;
```

### Informal statement
For all functions `f` and `g`, and sets `s`, if `f` is `square_integrable_on` `s` and `g` is `square_integrable_on` `s`, then the function that maps `x` to `f(x) * g(x)` is `real_integrable_on` `s`.

### Informal sketch
The proof uses `SQUARE_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE_PRODUCT` to show that the product is absolutely integrable, and then `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE` to conclude that it is integrable.

### Mathematical insight
This theorem is a direct consequence of the previous one and a standard result in integration theory.

### Dependencies
- `square_integrable_on`
- `real_integrable_on`
- `SQUARE_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE_PRODUCT`
- `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE`

---
### Name of formal statement
SQUARE_INTEGRABLE_ADD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SQUARE_INTEGRABLE_ADD = prove
 (`!f g s. f square_integrable_on s /\ g square_integrable_on s
           ==> (\x. f(x) + g(x)) square_integrable_on s`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[square_integrable_on; REAL_MEASURABLE_ON_ADD;
               SQUARE_INTEGRABLE_IMP_MEASURABLE] THEN
  SIMP_TAC[REAL_ARITH `(x + y) pow 2 = (x pow 2 + y pow 2) + &2 * x * y`] THEN
  MATCH_MP_TAC REAL_INTEGRABLE_ADD THEN
  ASM_SIMP_TAC[SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT;
               REAL_INTEGRABLE_LMUL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[square_integrable_on]) THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_ADD]);;
```

### Informal statement
For all functions `f` and `g`, and sets `s`, if `f` is `square_integrable_on` `s` and `g` is `square_integrable_on` `s`, then the function that maps `x` to `f(x) + g(x)` is `square_integrable_on` `s`.

### Informal sketch
The proof proceeds as follows:
- Strip quantifiers and implication.
- Expand `square_integrable_on` and utilize the fact that the sum of measurable functions is measurable (`REAL_MEASURABLE_ON_ADD`), and that square-integrable implies measurable (`SQUARE_INTEGRABLE_IMP_MEASURABLE`).
- Expand `(f(x) + g(x))^2` to `f(x)^2 + g(x)^2 + 2*f(x)*g(x)`.
- Apply the theorem `REAL_INTEGRABLE_ADD`, and the fact that `SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT` and `REAL_INTEGRABLE_LMUL` to show that each term in the sum is integrable.

### Mathematical insight
This theorem asserts that the sum of two square-integrable functions is also square-integrable. This shows the closure of the space of square-integrable functions under addition, which is crucial for it being a vector space.

### Dependencies
- `square_integrable_on`
- `REAL_MEASURABLE_ON_ADD`
- `SQUARE_INTEGRABLE_IMP_MEASURABLE`
- `REAL_INTEGRABLE_ADD`
- `SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT`
- `REAL_INTEGRABLE_LMUL`

---
### Name of formal statement
SQUARE_INTEGRABLE_SUB

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SQUARE_INTEGRABLE_SUB = prove
 (`!f g s. f square_integrable_on s /\ g square_integrable_on s
           ==> (\x. f(x) - g(x)) square_integrable_on s`,
  SIMP_TAC[real_sub; SQUARE_INTEGRABLE_ADD; SQUARE_INTEGRABLE_NEG_EQ]);;
```

### Informal statement
For all functions `f` and `g`, and sets `s`, if `f` is `square_integrable_on` `s` and `g` is `square_integrable_on` `s`, then the function that maps `x` to `f(x) - g(x)` is `square_integrable_on` `s`.

### Informal sketch
The proof rewrites subtraction in terms of addition and negation, and then uses `SQUARE_INTEGRABLE_ADD` and `SQUARE_INTEGRABLE_NEG_EQ`.

### Mathematical insight
This theorem states that the difference of two square-integrable functions is also square-integrable. This mirrors the addition theorem and contributes to the vector space structure.

### Dependencies
- `square_integrable_on`
- `SQUARE_INTEGRABLE_ADD`
- `SQUARE_INTEGRABLE_NEG_EQ`
- `real_sub`

---
### Name of formal statement
SQUARE_INTEGRABLE_ABS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SQUARE_INTEGRABLE_ABS = prove
 (`!f g s. f square_integrable_on s ==> (\x. abs(f x)) square_integrable_on s`,
  SIMP_TAC[square_integrable_on; REAL_MEASURABLE_ON_ABS; REAL_POW2_ABS]);;
```

### Informal statement
For all functions `f` and sets `s`, if `f` is `square_integrable_on` `s`, then the function that maps `x` to the absolute value of `f(x)` is also `square_integrable_on` `s`.

### Informal sketch
The proof is by rewriting with `square_integrable_on`, `REAL_MEASURABLE_ON_ABS` (the absolute value of a measurable function is measurable), and `REAL_POW2_ABS` (`abs(x)^2 = x^2`).

### Mathematical insight
This theorem highlights that taking the absolute value of a square-integrable function preserves square-integrability, owing to `|f(x)|^2 = f(x)^2`.

### Dependencies
- `square_integrable_on`
- `REAL_MEASURABLE_ON_ABS`
- `REAL_POW2_ABS`

---
### Name of formal statement
SQUARE_INTEGRABLE_SUM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SQUARE_INTEGRABLE_SUM = prove
 (`!f s t. FINITE t /\ (!i. i IN t ==> (f i) square_integrable_on s)
           ==> (\x. sum t (\i. f i x)) square_integrable_on s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SQUARE_INTEGRABLE_0; IN_INSERT; SQUARE_INTEGRABLE_ADD; ETA_AX;
           SUM_CLAUSES]);;
```

### Informal statement
For all functions `f`, sets `s`, and finite sets `t`, if `t` is finite and for all `i` in `t`, `f i` is `square_integrable_on` `s`, then the function that maps `x` to the sum over `t` of `f i x` is `square_integrable_on` `s`.

### Informal sketch
The proof proceeds by induction on the finite set `t`. The base case uses `SQUARE_INTEGRABLE_0`, and the inductive step uses `SQUARE_INTEGRABLE_ADD`. The `SUM_CLAUSES` are used to simplify the sum during induction.

### Mathematical insight
This theorem demonstrates that a finite sum of square-integrable functions is itself square-integrable. This is an important generalization of the `SQUARE_INTEGRABLE_ADD` theorem and further supports the vector space structure.

### Dependencies
- `square_integrable_on`
- `FINITE`
- `SQUARE_INTEGRABLE_0`
- `SQUARE_INTEGRABLE_ADD`
- `SUM_CLAUSES`

---
### Name of formal statement
REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE = prove
 (`!f a b. f real_continuous_on real_interval[a,b]
           ==> f square_integrable_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[square_integrable_on] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_IMP_REAL_MEASURABLE THEN
    MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN ASM_REWRITE_TAC[]]);;
```

### Informal statement
For all functions `f` and real numbers `a` and `b`, if `f` is `real_continuous_on` the real interval `[a, b]`, then `f` is `square_integrable_on` the real interval `[a, b]`.

### Informal sketch
The proof proceeds by:
- Expanding the definition of `square_integrable_on`.
- Splitting the goal into proving measurability and integrability of the square.
- Using `INTEGRABLE_IMP_REAL_MEASURABLE` and `REAL_INTEGRABLE_CONTINUOUS` to prove measurability.
- Using `REAL_CONTINUOUS_ON_POW` and `REAL_INTEGRABLE_CONTINUOUS` to prove integrability of the square.

### Mathematical insight
This theorem connects the concepts of continuity and square-integrability. It states that any function that is continuous on a closed interval is also square-integrable on that interval.

### Dependencies
- `square_integrable_on`
- `real_continuous_on`
- `INTEGRABLE_IMP_REAL_MEASURABLE`
- `REAL_INTEGRABLE_CONTINUOUS`
- `REAL_CONTINUOUS_ON_POW`

---
### Name of formal statement
SQUARE_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SQUARE_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE = prove
 (`!f s. f square_integrable_on s /\ real_measurable s
         ==> f absolutely_real_integrable_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_ON] THEN
  REWRITE_TAC[GSYM LSPACE_1] THEN
  MATCH_MP_TAC LSPACE_MONO THEN EXISTS_TAC `&2` THEN
  ASM_REWRITE_TAC[GSYM REAL_MEASURABLE_MEASURABLE;
                  GSYM SQUARE_INTEGRABLE_LSPACE] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;
```

### Informal statement
For all functions `f` and sets `s`, if `f` is `square_integrable_on` `s` and `s` is `real_measurable`, then `f` is `absolutely_real_integrable_on` `s`.

### Informal sketch
The proof involves:
- Expanding the definition of `absolutely_real_integrable_on`.
- Relating the integral bound to the `LSPACE_1` norm.
- Using the monotonicity of `LSPACE` and the fact that square-integrability implies membership in L2 space (`SQUARE_INTEGRABLE_LSPACE`).

### Mathematical insight
This theorem states that if a function is square-integrable on a measurable set, then it is also absolutely integrable on that set.

### Dependencies
- `square_integrable_on`
- `absolutely_real_integrable_on`
- `LSPACE_1`
- `LSPACE_MONO`
- `SQUARE_INTEGRABLE_LSPACE`
- `REAL_MEASURABLE_MEASURABLE`

---
### Name of formal statement
SQUARE_INTEGRABLE_IMP_INTEGRABLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SQUARE_INTEGRABLE_IMP_INTEGRABLE = prove
 (`!f s. f square_integrable_on s /\ real_measurable s
         ==> f real_integrable_on s`,
  SIMP_TAC[SQUARE_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE;
           ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE]);;
```

### Informal statement
For all functions `f` and sets `s`, if `f` is `square_integrable_on` `s` and `s` is `real_measurable`, then `f` is `real_integrable_on` `s`.

### Informal sketch
The proof uses `SQUARE_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE` to show that the function is absolutely integrable, and then `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE` to conclude that it is integrable.

### Mathematical insight
This theorem states that if a function is square-integrable on a measurable set, then it is also integrable on that set.

### Dependencies
- `square_integrable_on`
- `real_integrable_on`
- `SQUARE_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE`
- `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE`


---

## l2norm

### Name of formal statement
l2norm

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let l2norm = new_definition
 `l2norm s f = sqrt(l2product s f f)`;;
```

### Informal statement
The `l2norm` of a function `f` over a set `s` is defined as the square root of the `l2product` of `f` with itself over the set `s`.

### Informal sketch
The definition introduces `l2norm` as a derived concept from `l2product`. It directly applies the square root function (`sqrt`) to the result of `l2product s f f`. No proof is involved since it's a direct definition.

### Mathematical insight
The `l2norm` represents the Euclidean norm (or magnitude) of a function in a given space. It is a standard measure of the "size" of a function. This definition is important because it connects the general concept of an L2 norm with the previously defined `l2product`. By defining it in terms of the `l2product`, the properties of the `l2product` can be leveraged to prove properties about the `l2norm`.

### Dependencies
- Definitions: `l2product`, `sqrt`


---

## L2NORM_LNORM

### Name of formal statement
L2NORM_LNORM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2NORM_LNORM = prove
 (`!f s. f square_integrable_on s
         ==> l2norm s f = lnorm (IMAGE lift s) (&2) (lift o f o drop)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[l2norm; lnorm; l2product] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[square_integrable_on]) THEN
  ASM_SIMP_TAC[GSYM REAL_POW_2; REAL_INTEGRAL] THEN
  REWRITE_TAC[NORM_REAL; o_DEF; GSYM drop; LIFT_DROP; RPOW_POW] THEN
  REWRITE_TAC[REAL_POW2_ABS] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC(GSYM RPOW_SQRT) THEN
  MATCH_MP_TAC INTEGRAL_DROP_POS THEN
  REWRITE_TAC[FORALL_IN_IMAGE; LIFT_DROP; REAL_LE_POW_2] THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[REAL_INTEGRABLE_ON] o CONJUNCT2) THEN
  REWRITE_TAC[o_DEF]);;
```
### Informal statement
For all functions `f` and sets `s`, `f` is square integrable on `s` if and only if the L2 norm of `f` on `s` is equal to the `lnorm` of the image of `lift s` under the function `lift o f o drop` with exponent 2.

### Informal sketch
The proof proceeds by:
- Expanding the definitions of `l2norm`, `lnorm`, and `l2product`.
- Using the definition of `square_integrable_on`.
- Simplifying using `REAL_POW_2`, `REAL_INTEGRAL`.
- Rewriting using `NORM_REAL`, `o_DEF`, `drop`, `LIFT_DROP`, `RPOW_POW`, `REAL_POW2_ABS`.
- Reducing the real rational expression.
- Matching with `RPOW_SQRT`.
- Matching with `INTEGRAL_DROP_POS`.
- Rewriting using `FORALL_IN_IMAGE`, `LIFT_DROP`, `REAL_LE_POW_2`.
- Applying `REAL_INTEGRABLE_ON`.
- Rewriting using `o_DEF`.

### Mathematical insight
This theorem establishes the equivalence between the L2 norm defined using square integrability and the `lnorm` defined using a lifted set and a modified function. It connects two different ways of defining a norm for functions, showing that they are equivalent under suitable conditions.

### Dependencies
- Definitions: `l2norm`, `lnorm`, `l2product`, `square_integrable_on`.
- Theorems: `REAL_POW_2`, `NORM_REAL`, `LIFT_DROP`, `RPOW_POW`, `REAL_POW2_ABS`, `RPOW_SQRT`, `INTEGRAL_DROP_POS`, `FORALL_IN_IMAGE`, `REAL_LE_POW_2`, `REAL_INTEGRABLE_ON`.
- Constants: `REAL_INTEGRAL`, `o_DEF`, `drop`, `lift`


---

## L2PRODUCT_SYM

### Name of formal statement
L2PRODUCT_SYM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2PRODUCT_SYM = prove
 (`!s f g. l2product s f g = l2product s g f`,
  REWRITE_TAC[l2product; REAL_MUL_SYM]);;
```
### Informal statement
For all sets `s` and functions `f` and `g` from `s` to real numbers, the L2 product of `f` and `g` over `s` is equal to the L2 product of `g` and `f` over `s`.

### Informal sketch
The proof demonstrates that the `l2product` is symmetric.
- The proof rewrites the goal using the definition of `l2product`, which involves a sum over the elements of the set `s` of the product of `f(x)` and `g(x)`.
- The proof then applies the symmetry of real number multiplication (`REAL_MUL_SYM`) to swap the order of `f(x)` and `g(x)` within the summation.
- The definition of `l2product` is applied backward which establishes the symmetry of the `l2product`.

### Mathematical insight
The theorem `L2PRODUCT_SYM` establishes a fundamental property of the `l2product`, namely its symmetry with respect to its function arguments. This reflects the commutativity of multiplication in the real numbers, and is a crucial component, for example, in proving that `l2product s f f` is non-negative, i.e. `0 <= l2product s f f`.

### Dependencies
- Definitions: `l2product`
- Theorems: `REAL_MUL_SYM`


---

## L2PRODUCT_POS_LE

### Name of formal statement
L2PRODUCT_POS_LE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2PRODUCT_POS_LE = prove
 (`!s f. f square_integrable_on s ==> &0 <= l2product s f f`,
  REWRITE_TAC[square_integrable_on; l2product] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_POS THEN
  REWRITE_TAC[REAL_LE_SQUARE] THEN ASM_REWRITE_TAC[GSYM REAL_POW_2]);;
```
### Informal statement
For all sets `s` and functions `f`, if `f` is square integrable on `s`, then 0 is less than or equal to the L2 product of `s` with `f` and `f`.

### Informal sketch
The proof proceeds as follows:
- First, rewrite using the definitions of `square_integrable_on` and `l2product`.
- Next, strip the quantifiers and assumptions.
- Then, apply the theorem `REAL_INTEGRAL_POS`, which states that the integral of a non-negative function is non-negative. This requires proving that `f(x) * f(x)` is non-negative, which is implied by the square integrability assumption and the definition of `l2product`.
- Rewrite using `REAL_LE_SQUARE`, which states that `0 <= x * x`.
- Apply assumption rewriting using `GSYM REAL_POW_2`, that is the symmetry of the theorem `REAL_POW_2`, which relates squares and powers of 2.

### Mathematical insight
This theorem establishes a fundamental property of the L2 product: that the L2 product of a function with itself over a set is always non-negative, provided the function is square integrable on that set. This is analogous to the fact that the inner product of a vector with itself is non-negative in linear algebra. This property is crucial for defining norms and distances in function spaces.

### Dependencies
- Definitions: `square_integrable_on`, `l2product`
- Theorems: `REAL_INTEGRAL_POS`, `REAL_LE_SQUARE`, `REAL_POW_2`


---

## L2NORM_POW_2

### Name of formal statement
L2NORM_POW_2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2NORM_POW_2 = prove
 (`!s f. f square_integrable_on s ==> (l2norm s f) pow 2 = l2product s f f`,
  SIMP_TAC[l2norm; SQRT_POW_2; L2PRODUCT_POS_LE]);;
```
### Informal statement
For every set `s` and function `f`, if `f` is square-integrable on `s`, then the square of the `l2norm` of `f` on `s` is equal to the `l2product` of `f` with itself on `s`.

### Informal sketch
The proof proceeds by:
- Expanding the definition of `l2norm` as the square root of the `l2product` of the function with itself, `sqrt(l2product s f f)`.
- Squaring the `l2norm` using `SQRT_POW_2`, which simplifies `(sqrt x) pow 2` to `x`.
- Applying `L2PRODUCT_POS_LE` and `l2norm`.

### Mathematical insight
This theorem establishes a fundamental relationship between the `l2norm` and the `l2product` for square-integrable functions. It shows that the square of the `l2norm` is equal to the `l2product` of the function with itself, effectively linking the concepts of magnitude and inner product in the context of L2 spaces. This is a crucial result when dealing with Hilbert spaces and Fourier analysis, as it allows one to compute norms using inner products and vice versa.

### Dependencies
- Definitions: `l2norm`
- Theorems: `SQRT_POW_2`, `L2PRODUCT_POS_LE`


---

## L2NORM_POS_LE

### Name of formal statement
L2NORM_POS_LE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2NORM_POS_LE = prove
 (`!s f. f square_integrable_on s ==> &0 <= l2norm s f`,
  SIMP_TAC[l2norm; SQRT_POS_LE; L2PRODUCT_POS_LE]);;
```
### Informal statement
For all sets `s` and all functions `f`, if `f` is square integrable on `s`, then 0 is less than or equal to the `l2norm` of `f` on `s`.

### Informal sketch
The proof demonstrates that the L2 norm of a square-integrable function is non-negative.
- The proof relies on the definition of the `l2norm` as the square root of the L2 product of the function with itself: `l2norm s f = sqrt(l2product s f f)`.
- It then uses the theorem `SQRT_POS_LE`, which states that the square root of a non-negative real number is non-negative.
- It also employs the theorem `L2PRODUCT_POS_LE`, stating that the L2 product of a square-integrable function with itself is non-negative if the function is square integrable.
- Combining these facts, the result follows directly.

### Mathematical insight
This theorem is a fundamental property of the L2 norm, showing that it always returns a non-negative value. This ensures it can be used as a distance measure on function spaces. The proof reflects the natural intuition that norms are non-negative by definition..

### Dependencies
- Definitions: `l2norm`
- Theorems: `SQRT_POS_LE`, `L2PRODUCT_POS_LE`


---

## L2NORM_LE

### Name of formal statement
L2NORM_LE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2NORM_LE = prove
 (`!s f g. f square_integrable_on s /\ g square_integrable_on s
           ==> (l2norm s f <= l2norm s g <=>
                l2product s f f <= l2product s g g)`,
  SIMP_TAC[SQRT_MONO_LE_EQ; l2norm; SQRT_MONO_LE_EQ; L2PRODUCT_POS_LE]);;
```
### Informal statement
For all sets `s` and functions `f` and `g`, if `f` is square integrable on `s` and `g` is square integrable on `s`, then the `l2norm` of `f` on `s` is less than or equal to the `l2norm` of `g` on `s` if and only if the `l2product` of `f` with itself on `s` is less than or equal to the `l2product` of `g` with itself on `s`.

### Informal sketch
The proof relies on the following key steps:
- The square root function is monotone increasing for non-negative real numbers. This is formalized in `SQRT_MONO_LE_EQ`.
- Apply the definition of `l2norm`. This reduces the goal to proving that the square root of the `l2product` of `f` with itself is less than or equal to the square root of the `l2product` of `g` with itself if and only if the `l2product` of `f` with itself is less than or equal to the `l2product` of `g` with itself.
- `SQRT_MONO_LE_EQ` is used again to remove the square roots.
- `L2PRODUCT_POS_LE` establishes that the `l2product` of a function with itself is non-negative, ensuring the square root arguments are valid.

### Mathematical insight
The theorem provides a criterion for comparing the `l2norm` of functions by comparing the `l2product` of the functions with themselves. This avoids directly dealing with square roots, which can simplify certain proofs. The condition requires the functions to be square integrable to ensure their l2norms are well-defined.

### Dependencies
- `SQRT_MONO_LE_EQ`
- `l2norm`
- `L2PRODUCT_POS_LE`


---

## L2NORM_EQ

### Name of formal statement
L2NORM_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2NORM_EQ = prove
 (`!s f g. f square_integrable_on s /\ g square_integrable_on s
           ==> (l2norm s f = l2norm s g <=>
                l2product s f f = l2product s g g)`,
  SIMP_TAC[GSYM REAL_LE_ANTISYM; L2NORM_LE]);;
```
### Informal statement
For any set `s` and functions `f` and `g`, if `f` is square integrable on `s` and `g` is square integrable on `s`, then the L2 norm of `f` on `s` is equal to the L2 norm of `g` on `s` if and only if the L2 product of `f` with itself on `s` is equal to the L2 product of `g` with itself on `s`.

### Informal sketch
The proof proceeds as follows:
- Start with the assumption that `f` and `g` are square integrable on `s`.
- Show that `l2norm s f = l2norm s g` is equivalent to `l2product s f f = l2product s g g`.
- The proof relies on the fact that `l2norm s f` is defined as the square root of `l2product s f f`. Therefore, the equivalence follows from the properties of square roots and equality.
- The tactic `GSYM REAL_LE_ANTISYM` is used, indicating manipulation of inequalities concerning real numbers.
- The tactic `L2NORM_LE` is used, meaning the proof utilizes a theorem about the relationship between the L2 norm and inequality. Given that `l2norm` is non-negative, we have `l2norm s f = l2norm s g <=> (l2norm s f)^2 = (l2norm s g)^2`, but `(l2norm s f)^2 = l2product s f f` and `(l2norm s g)^2 = l2product s g g` from definition of L2 norm.

### Mathematical insight
This theorem establishes a direct connection between the equality of L2 norms of two functions and the equality of their L2 products with themselves. This is useful because it allows us to determine whether two functions have the same L2 norm by comparing their L2 products, which can sometimes be easier to compute or reason about. The L2 norm effectively captures the "size" or "energy" of a function in a particular space. This result is fundamental in functional analysis and related fields.

### Dependencies
- `GSYM REAL_LE_ANTISYM`
- `L2NORM_LE`


---

## SCHWARTZ_INEQUALITY_STRONG

### Name of formal statement
SCHWARTZ_INEQUALITY_STRONG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SCHWARTZ_INEQUALITY_STRONG = prove
 (`!f g s. f square_integrable_on s /\
           g square_integrable_on s
           ==> l2product s (\x. abs(f x)) (\x. abs(g x))
               <= l2norm s f * l2norm s g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE lift s`; `&2`; `&2`;
                 `lift o f o drop`; `lift o g o drop`] HOELDER_INEQUALITY) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_SIMP_TAC[GSYM SQUARE_INTEGRABLE_LSPACE; GSYM L2NORM_LNORM] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
  REWRITE_TAC[l2product] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL; SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT;
               SQUARE_INTEGRABLE_ABS] THEN
  REWRITE_TAC[NORM_REAL; o_DEF; GSYM drop; LIFT_DROP; REAL_LE_REFL]);;
```

### Informal statement
For any functions `f` and `g`, and set `s`, if `f` is square integrable on `s` and `g` is square integrable on `s`, then the L2 product of the absolute values of `f` and `g` on `s` is less than or equal to the product of the L2 norms of `f` and `g` on `s`.

### Informal sketch
The proof proceeds as follows:
- Apply the `HOELDER_INEQUALITY` after lifting the functions to the entire space using `lift` and `drop`. This involves specializing `HOELDER_INEQUALITY` with `IMAGE lift s`, `2`, `2`, `lift o f o drop`, and `lift o g o drop`.
- Simplify the resulting expression by reducing real rational expressions related to exponents (using `REAL_RAT_REDUCE_CONV`) and by rewriting using `SQUARE_INTEGRABLE_LSPACE` and `L2NORM_LNORM`.
- Apply transitivity of real inequality (using `REAL_LE_TRANS` combined with `IMP_CONJ` and rewriting) to prepare for introducing the `l2product` definition.
- Rewrite the `l2product` using its definition.
- Simplify the resulting integral expression, using `REAL_INTEGRAL`, `SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT`, and `SQUARE_INTEGRABLE_ABS`.
- Simplify further using `NORM_REAL`, the definition of function composition `o_DEF`, `drop`, `LIFT_DROP` and finally use `REAL_LE_REFL` to complete the proof.

### Mathematical insight
The Schwartz inequality (also known as the Cauchy-Schwarz inequality) is a fundamental inequality in mathematics, particularly in the context of inner product spaces and integration theory. This version states that the integral of absolute value of the product of two functions is less than or equal to the product of their respective norms. It demonstrates a relationship between the "size" of individual functions and the "size" of their product.

### Dependencies
**Theorems/Definitions:**
- `HOELDER_INEQUALITY`
- `SQUARE_INTEGRABLE_LSPACE`
- `L2NORM_LNORM`
- `IMP_CONJ`
- `REAL_LE_TRANS`
- `l2product`
- `REAL_INTEGRAL`
- `SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT`
- `SQUARE_INTEGRABLE_ABS`
- `NORM_REAL`
- `o_DEF`
- `drop`
- `LIFT_DROP`
- `REAL_LE_REFL`

### Porting notes (optional)
- The use of `lift` and `drop` functions might need to be adapted based on how measure spaces and integration are handled in the target proof assistant.
- The tactics used such as `REPEAT STRIP_TAC`, `MP_TAC`, `CONV_TAC`, `ASM_SIMP_TAC`, `MATCH_MP_TAC`, and `REWRITE_TAC` indicate the steps taken in rewriting and simplifying the expressions. The translation of these tactics will depend on the automation capabilities of the target proof assistant.


---

## SCHWARTZ_INEQUALITY_ABS

### Name of formal statement
SCHWARTZ_INEQUALITY_ABS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SCHWARTZ_INEQUALITY_ABS = prove
 (`!f g s. f square_integrable_on s /\
           g square_integrable_on s
           ==> abs(l2product s f g) <= l2norm s f * l2norm s g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `l2product s (\x. abs(f x)) (\x. abs(g x))` THEN
  ASM_SIMP_TAC[SCHWARTZ_INEQUALITY_STRONG] THEN REWRITE_TAC[l2product] THEN
  MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN
  ASM_SIMP_TAC[SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT;
               SQUARE_INTEGRABLE_ABS] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_LE_REFL]);;
```
### Informal statement
For any functions `f` and `g`, and any set `s`, if `f` is square integrable on `s` and `g` is square integrable on `s`, then the absolute value of the L2 product of `f` and `g` on `s` is less than or equal to the product of the L2 norm of `f` on `s` and the L2 norm of `g` on `s`.

### Informal sketch
The proof proceeds as follows:
- Strip the quantifiers and assumption.
- Apply `REAL_LE_TRANS` to transform the goal into proving an upper bound on the absolute value of the L2 product.
- Introduce an existential variable representing the L2 product of the absolute values of `f` and `g` over `s`.
- Apply `SCHWARTZ_INEQUALITY_STRONG` with absolute values.  The theorem `SCHWARTZ_INEQUALITY_STRONG` directly proves that `l2product s (abs o f) (abs o g) <= l2norm s (abs o f) * l2norm s (abs o g)`. As a consequence, it is necessary to prove `abs (l2product s f g) <= l2product s (abs o f) (abs o g)` and `l2norm s (abs o f) * l2norm s (abs o g) <= l2norm s f * l2norm s g`.
- Rewrite using the definition of `l2product`.
- Bound the absolute value of the real integral using `REAL_INTEGRAL_ABS_BOUND_INTEGRAL`.
- Simplify using `SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT` to show that the product of square-integrable functions is integrable and using `SQUARE_INTEGRABLE_ABS` to show that if a function is square integrable, so is its absolute value.
- Rewrite using `REAL_ABS_MUL` and `REAL_LE_REFL`.

### Mathematical insight
The theorem states the Schwarz inequality for the absolute value of the L2 product. This is a variant of the standard Schwarz inequality, which is a fundamental result in functional analysis and has widespread applications in mathematics, physics, and engineering. By taking absolute values, we ensure that the L2 product is non-negative before applying standard Schwartz inequality

### Dependencies
- `SCHWARTZ_INEQUALITY_STRONG`
- `SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT`
- `SQUARE_INTEGRABLE_ABS`
- `REAL_LE_TRANS`
- `REAL_INTEGRAL_ABS_BOUND_INTEGRAL`
- `REAL_ABS_MUL`
- `REAL_LE_REFL`
- Definition: `l2product`
- Definition: `l2norm`

### Porting notes (optional)
- The proof relies on the theorem `SCHWARTZ_INEQUALITY_STRONG`, so the porter should ensure that this theorem (or a suitable equivalent) is available in the target proof assistant.
- The proof uses the tactic `EXISTS_TAC` on the term `l2product s (\x. abs(f x)) (\x. abs(g x))`, so the target proof assistant must support similar existential introduction steps.
- The porter may need to adjust the tactic script to align with the specific proof automation and rewriting capabilities of the target proof assistant.


---

## SCHWARTZ_INEQUALITY

### Name of formal statement
SCHWARTZ_INEQUALITY

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SCHWARTZ_INEQUALITY = prove
 (`!f g s. f square_integrable_on s /\
           g square_integrable_on s
           ==> l2product s f g <= l2norm s f * l2norm s g`,
  MESON_TAC[SCHWARTZ_INEQUALITY_ABS;
            REAL_ARITH `abs x <= a ==> x <= a`]);;
```
### Informal statement
For all functions `f` and `g` and set `s`, if `f` is square integrable on `s` and `g` is square integrable on `s`, then the L2 product of `f` and `g` on `s` is less than or equal to the product of the L2 norm of `f` on `s` and the L2 norm of `g` on `s`.

### Informal sketch
The proof uses the following steps:
- First, the theorem `SCHWARTZ_INEQUALITY_ABS` is probably used, which probably states that `abs (l2product s f g) <= l2norm s f * l2norm s g`.
- Next, a real arithmetic tactic, specifically one using the assumption `abs x <= a ==> x <= a`, is used to remove the absolute value from the left-hand side.
- Finally, use `MESON_TAC` to combine these facts and complete the proof.

### Mathematical insight
The Schwartz inequality is a fundamental inequality in mathematics, particularly in functional analysis, inner product spaces, and probability theory. It relates the inner product of two vectors (here, functions) to the product of their norms. In the context of L2 spaces (square integrable functions), it provides an upper bound on the integral of the product of two functions in terms of the product of their L2 norms. This theorem is essential for proving other results related to convergence, orthogonality, and approximation in function spaces.

### Dependencies
- Theorems: `SCHWARTZ_INEQUALITY_ABS`
- Real arithmetic: `REAL_ARITH abs x <= a ==> x <= a`


---

## L2NORM_TRIANGLE

### Name of formal statement
L2NORM_TRIANGLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2NORM_TRIANGLE = prove
 (`!f g s. f square_integrable_on s /\
           g square_integrable_on s
           ==> l2norm s (\x. f x + g x) <= l2norm s f + l2norm s g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE lift s`; `&2`;
                 `lift o f o drop`; `lift o g o drop`] LNORM_TRIANGLE) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_SIMP_TAC[GSYM SQUARE_INTEGRABLE_LSPACE; L2NORM_LNORM;
               SQUARE_INTEGRABLE_ADD] THEN
  REWRITE_TAC[o_DEF; LIFT_ADD]);;
```
### Informal statement
For any functions `f` and `g`, and set `s`, if `f` is square integrable on `s` and `g` is square integrable on `s`, then the L2 norm of the function `λx. f x + g x` on `s` is less than or equal to the sum of the L2 norms of `f` on `s` and `g` on `s`.

### Informal sketch
The proof demonstrates the triangle inequality for the L2 norm.

- The proof starts by stripping the quantifiers and the implication.
- It then applies the theorem `LNORM_TRIANGLE` after specializing it with `IMAGE lift s`, `&2`, `lift o f o drop` and `lift o g o drop`. This step essentially lifts the problem to a general setting, applying the triangle inequality for norms to the lifted functions within the image of the set `s`.
- A conversion using `REAL_RAT_REDUCE_CONV` is performed.
- Simplification is done using assumptions and the following theorems: `GSYM SQUARE_INTEGRABLE_LSPACE`, `L2NORM_LNORM` and `SQUARE_INTEGRABLE_ADD`. These are used to reduce the goal by rewriting using definitions of key concepts like square integrability and the relationship between the L2 norm and the general norm.
- The definitions `o_DEF` (definition of function composition) and `LIFT_ADD` are rewritten to complete the proof.

### Mathematical insight
This theorem establishes the triangle inequality for the L2 norm, a fundamental property in functional analysis. It states that the norm of the sum of two functions is less than or equal to the sum of their norms. This is a generalization of the familiar triangle inequality for vectors in Euclidean space and is crucial for proving completeness and other properties of L2 spaces.

### Dependencies
- `SQUARE_INTEGRABLE_LSPACE`
- `L2NORM_LNORM`
- `SQUARE_INTEGRABLE_ADD`
- `LNORM_TRIANGLE`
- `o_DEF`
- `LIFT_ADD`


---

## L2PRODUCT_LADD

### Name of formal statement
L2PRODUCT_LADD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2PRODUCT_LADD = prove
 (`!s f g h.
        f square_integrable_on s /\
        g square_integrable_on s /\
        h square_integrable_on s
        ==> l2product s (\x. f x + g x) h =
            l2product s f h + l2product s g h`,
  SIMP_TAC[l2product; REAL_ADD_RDISTRIB; REAL_INTEGRAL_ADD;
           SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT]);;
```
### Informal statement
For any set `s` and functions `f`, `g`, and `h`, if `f` is square integrable on `s`, `g` is square integrable on `s`, and `h` is square integrable on `s`, then the L2 product of `f + g` with `h` over `s` is equal to the sum of the L2 product of `f` with `h` over `s` and the L2 product of `g` with `h` over `s`.

### Informal sketch
The proof establishes the theorem by applying simplification tactics based on several key lemmas and theorems:
- Expand the definition of `l2product`.
- Apply the right distributivity of real addition (`REAL_ADD_RDISTRIB`).
- Apply the theorem that the integral of a sum is the sum of the integrals (`REAL_INTEGRAL_ADD`).
- Use the fact that square integrability implies integrability of the product (`SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT`).

### Mathematical insight
This theorem demonstrates the linearity of the L2 product with respect to addition in the first argument. It's a fundamental property expressing how the L2 product interacts with linear combinations of functions. This is essential for various applications, including Fourier analysis and Hilbert space theory.

### Dependencies
- Definitions: `l2product`
- Theorems: `REAL_ADD_RDISTRIB`, `REAL_INTEGRAL_ADD`, `SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT`


---

## L2PRODUCT_RADD

### Name of formal statement
L2PRODUCT_RADD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2PRODUCT_RADD = prove
 (`!s f g h.
        f square_integrable_on s /\
        g square_integrable_on s /\
        h square_integrable_on s
        ==> l2product s f (\x. g x + h x) =
            l2product s f g + l2product s f h`,
  SIMP_TAC[l2product; REAL_ADD_LDISTRIB; REAL_INTEGRAL_ADD;
           SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT]);;
```
### Informal statement
For any set `s` and any functions `f`, `g`, and `h`, if `f` is square integrable on `s`, `g` is square integrable on `s`, and `h` is square integrable on `s`, then the L2 product of `f` with the function `\x. g x + h x` over the set `s` is equal to the sum of the L2 product of `f` and `g` over `s` and the L2 product of `f` and `h` over `s`.

### Informal sketch
The proof proceeds by showing that the L2 product, defined as the integral of a product, distributes over addition.
- Start with the hypothesis `f square_integrable_on s /\ g square_integrable_on s /\ h square_integrable_on s`.
- Expand the definition of `l2product s f (\x. g x + h x)` to `real_integral s (\x. f x * (g x + h x))`.
- Apply the distributive property of real multiplication over addition (`REAL_ADD_LDISTRIB`) to transform the integrand into `f x * g x + f x * h x`.
- Apply the theorem that the integral of a sum is the sum of the integrals (`REAL_INTEGRAL_ADD`), to rewrite the integral as `real_integral s (\x. f x * g x) + real_integral s (\x. f x * h x)`.
- Finally, use the definition of `l2product` to rewrite the integrals as `l2product s f g + l2product s f h`.
- The assumption `SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT` justifies the application of `REAL_INTEGRAL_ADD`.

### Mathematical insight
This theorem states that the L2 product is a linear operator with respect to addition in its second argument, given that all functions involved are square integrable. This is a fundamental property of inner product spaces, which the L2 space is an instance of.

### Dependencies
- `l2product` (definition of the L2 product)
- `REAL_ADD_LDISTRIB` (distributive property of real multiplication over addition)
- `REAL_INTEGRAL_ADD` (integral of a sum is the sum of the integrals)
- `SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT` (square integrability implies integrability of the product)


---

## L2PRODUCT_LSUB

### Name of formal statement
L2PRODUCT_LSUB

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2PRODUCT_LSUB = prove
 (`!s f g h.
        f square_integrable_on s /\
        g square_integrable_on s /\
        h square_integrable_on s
        ==> l2product s (\x. f x - g x) h =
            l2product s f h - l2product s g h`,
  SIMP_TAC[l2product; REAL_SUB_RDISTRIB; REAL_INTEGRAL_SUB;
           SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT]);;
```
### Informal statement
For all sets `s`, and functions `f`, `g`, and `h`, if `f` is square integrable on `s`, `g` is square integrable on `s`, and `h` is square integrable on `s`, then the L2 product of `s` with the function that maps `x` to `f x - g x` and `h` is equal to the L2 product of `s` with `f` and `h` minus the L2 product of `s` with `g` and `h`.

### Informal sketch
The proof demonstrates the linearity of `l2product` with respect to subtraction in its first argument, given square integrability conditions:
- Start with the goal: `l2product s (\x. f x - g x) h = l2product s f h - l2product s g h`.
- Apply the definition of `l2product` to expand both sides into integrals: `integral s (\x. (f x - g x) * h x) = integral s (f x * h x) - integral s (g x * h x)`.
- Use the fact that `REAL_SUB_RDISTRIB` distributes the multiplication of `h x` over the subtraction `f x - g x`.
- Use `REAL_INTEGRAL_SUB` in the form `integral s (\x. f x - g x) = integral s f - integral s g`. This step requires proving the integrability of `f x * h x` and `g x * h x`.
- This integrability is guaranteed by `SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT` given the initial assumptions of square integrability of `f`, `g`, and `h` on `s`.

### Mathematical insight
This theorem states that the L2 inner product is linear with respect to subtraction in its first argument. This mirrors the linearity property of standard inner products in linear algebra, but in the context of L2 spaces, requires the extra conditions of square integrability to ensure that all integrals are well defined.

### Dependencies
- `l2product`
- `REAL_SUB_RDISTRIB`
- `REAL_INTEGRAL_SUB`
- `SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT`


---

## L2PRODUCT_RSUB

### Name of formal statement
L2PRODUCT_RSUB

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2PRODUCT_RSUB = prove
 (`!s f g h.
        f square_integrable_on s /\
        g square_integrable_on s /\
        h square_integrable_on s
        ==> l2product s f (\x. g x - h x) =
            l2product s f g - l2product s f h`,
  SIMP_TAC[l2product; REAL_SUB_LDISTRIB; REAL_INTEGRAL_SUB;
           SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT]);;
```
### Informal statement
For any set `s` and functions `f`, `g`, and `h`, if `f` is square-integrable on `s`, `g` is square-integrable on `s`, and `h` is square-integrable on `s`, then the L2 inner product of `f` with the function given by pointwise subtraction `g x - h x` on `s` is equal to the L2 inner product of `f` and `g` on `s` minus the L2 inner product of `f` and `h` on `s`.

### Informal sketch
The proof proceeds as follows:
- Start with the definition of `l2product s f (\x. g x - h x)`.
- Apply the distributive property of subtraction over the real numbers using `REAL_SUB_LDISTRIB`.
- Use the linearity of the integral via `REAL_INTEGRAL_SUB` to split the integral of the difference into the difference of integrals.
- Apply the definition of `l2product s f g` and `l2product s f h`.
- Use `SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT` to show that if `f`, `g`, and `h` are square-integrable, then the product of `f` and `(g - h)` is integrable.

### Mathematical insight
The theorem states that the L2 inner product is linear in its second argument. This is a fundamental property of inner products and is crucial in many applications involving Hilbert spaces and functional analysis. The square-integrability conditions ensure that all the L2 inner products and integrals involved are well-defined and finite.

### Dependencies
- Definition: `l2product`
- Theorem: `REAL_SUB_LDISTRIB`
- Theorem: `REAL_INTEGRAL_SUB`
- Theorem: `SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT`


---

## L2PRODUCT_LZERO

### Name of formal statement
L2PRODUCT_LZERO

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2PRODUCT_LZERO = prove
 (`!s f. l2product s (\x. &0) f = &0`,
  REWRITE_TAC[l2product; REAL_MUL_LZERO; REAL_INTEGRAL_0]);;
```

### Informal statement
For any set `s` and any function `f`, the Lebesgue integral of the function that maps every point to 0, with respect to `s`, multiplied by `f`, is equal to 0.

### Informal sketch
The proof proceeds by:
- Rewriting using the definition of `l2product`.
- Applying `REAL_MUL_LZERO` to show that the pointwise multiplication results in 0.
- Applying `REAL_INTEGRAL_0` to demonstrate that the integral of the zero function is zero.

### Mathematical insight
This theorem shows that integrating the zero function (specifically, the function that results from multiplying any function `f` by the constant zero function) will always yield zero. This stems from the fact that the integral represents the area under the curve, and if the function is always zero, the area is zero. This theorem is important for simplifying expressions involving integrals and for reasoning about the properties of integration.

### Dependencies
- Definitions: `l2product`
- Theorems: `REAL_MUL_LZERO`, `REAL_INTEGRAL_0`


---

## L2PRODUCT_RZERO

### Name of formal statement
L2PRODUCT_RZERO

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2PRODUCT_RZERO = prove
 (`!s f. l2product s f (\x. &0) = &0`,
  REWRITE_TAC[l2product; REAL_MUL_RZERO; REAL_INTEGRAL_0]);;
```

### Informal statement
For all sets `s` and functions `f`, the Lebesgue integral of the function that maps every `x` to 0, i.e., `\x. &0`, over the set `s` with respect to the measure induced by `f`  is equal to 0.

### Informal sketch
The proof proceeds by:
- Using the `l2product` definition to expand the Lebesgue integral into a real integral `real_integral`.
- Applying `REAL_MUL_RZERO` to simplify the integrand `f x * &0` to `&0`.
- Applying `REAL_INTEGRAL_0` to conclude that the real integral of `&0` is `&0`.

### Mathematical insight
This theorem states that the integral of the zero function is zero. It is a basic and fundamental property of integration, which is useful for simplifying integrals and proving other properties of integration.

### Dependencies
- Definitions: `l2product`
- Theorems: `REAL_MUL_RZERO`, `REAL_INTEGRAL_0`


---

## L2PRODUCT_LSUM

### Name of formal statement
L2PRODUCT_LSUM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2PRODUCT_LSUM = prove
 (`!s f g t.
        FINITE t /\ (!i. i IN t ==> (f i) square_integrable_on s) /\
        g square_integrable_on s
        ==> l2product s (\x. sum t (\i. f i x)) g =
            sum t (\i. l2product s (f i) g)`,
  REPLICATE_TAC 3 GEN_TAC THEN
  ASM_CASES_TAC `g square_integrable_on s` THEN ASM_REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[L2PRODUCT_LZERO; SUM_CLAUSES; L2PRODUCT_LADD;
               SQUARE_INTEGRABLE_SUM; ETA_AX; IN_INSERT]);;
```

### Informal statement
For any set `s`, function `f`, function `g`, and finite set `t`, if `t` is finite, and for all `i` in `t`, `f i` is square integrable on `s`, and `g` is square integrable on `s`, then the L2 product of `s` with the function that maps `x` to the sum over `t` of `f i x`, and `g`, is equal to the sum over `t` of the L2 product of `s` with `f i` and `g`.

### Informal sketch
The proof proceeds by induction on the finite set `t`.

- First, three assumptions are discharged using `REPLICATE_TAC 3 GEN_TAC`: `FINITE t`, `!i. i IN t ==> (f i) square_integrable_on s`, and `g square_integrable_on s`.
- Then, perform case split on `g square_integrable_on s` using `ASM_CASES_TAC`.
- Then, rewrite the goal using `IMP_CONJ`.
- After this, the main part of the proof is an induction on finite set `t` using `FINITE_INDUCT_STRONG`.
- The base case is proven using the theorem `L2PRODUCT_LZERO` and `SUM_CLAUSES`.
- The inductive step makes use of `L2PRODUCT_LADD` and `SQUARE_INTEGRABLE_SUM` to prove that the property holds for the insertion of elemements `i` into the finite set `t`.

### Mathematical insight
This theorem demonstrates the linearity of the L2 product with respect to finite sums of square integrable functions. It's a generalization of the property that the integral of a sum is the sum of the integrals, but in the context of L2 spaces. This is important for manipulating expressions involving L2 products and sums in Fourier analysis and other applications.

### Dependencies
- `FINITE_INDUCT_STRONG`
- `L2PRODUCT_LZERO`
- `SUM_CLAUSES`
- `L2PRODUCT_LADD`
- `SQUARE_INTEGRABLE_SUM`
- `ETA_AX`
- `IN_INSERT`


---

## L2PRODUCT_RSUM

### Name of formal statement
L2PRODUCT_RSUM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2PRODUCT_RSUM = prove
 (`!s f g t.
        FINITE t /\ (!i. i IN t ==> (f i) square_integrable_on s) /\
        g square_integrable_on s
        ==> l2product s g (\x. sum t (\i. f i x)) =
            sum t (\i. l2product s g (f i))`,
  ONCE_REWRITE_TAC[L2PRODUCT_SYM] THEN REWRITE_TAC[L2PRODUCT_LSUM]);;
```
### Informal statement
For any set `s`, functions `f` and `g`, and finite set `t`, if `t` is finite, every function `f i` for `i` in `t` is square integrable on `s`, and `g` is square integrable on `s`, then the L2 product of `g` with the function mapping `x` to the sum over `t` of `f i x` is equal to the sum over `t` of the L2 product of `g` with `f i`.

### Informal sketch
The proof relies on the following key steps:
- Use `L2PRODUCT_SYM` to switch the order of `g` and the sum of `f i x` in the `l2product`.
- Apply `L2PRODUCT_LSUM` to distribute the `l2product` over the sum, which completes the proof.

### Mathematical insight
This theorem states that the L2 inner product is a linear operator with respect to sums, given appropriate square integrability conditions. This is a fundamental property in functional analysis and is often used when dealing with Hilbert spaces of square integrable functions.

### Dependencies
- Theorems: `L2PRODUCT_SYM`, `L2PRODUCT_LSUM`


---

## L2PRODUCT_LMUL

### Name of formal statement
L2PRODUCT_LMUL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2PRODUCT_LMUL = prove
 (`!s c f g.
        f square_integrable_on s /\ g square_integrable_on s
        ==> l2product s (\x. c * f x) g = c * l2product s f g`,
  SIMP_TAC[l2product; GSYM REAL_MUL_ASSOC; REAL_INTEGRAL_LMUL;
           SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT]);;
```
### Informal statement
For any set `s`, scalar `c`, and functions `f` and `g`, if `f` is square integrable on `s` and `g` is square integrable on `s`, then the L2 product of `s` with the function defined by `λx. c * f x` and `g` is equal to `c` times the L2 product of `s` with `f` and `g`.

### Informal sketch
The proof involves showing that scalar multiplication can be pulled out of the `l2product` integral.
- Assume `f` and `g` are square integrable on `s`.
- Expand `l2product s (\x. c * f x) g` using the definition of `l2product`.
- Apply `REAL_INTEGRAL_LMUL` to pull the constant `c` out of the integral. This step relies on the fact that if `f` is square integrable, then the product `c * f x * g x` is integrable via `SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT`.
- Use `GSYM REAL_MUL_ASSOC` to rearrange the order of multiplication to get `c * l2product s f g`.

### Mathematical insight
This theorem demonstrates the linearity of the L2 product with respect to scalar multiplication in the first argument. It's a fundamental property of inner products and is crucial for many applications in functional analysis and linear algebra in Hilbert spaces.

### Dependencies
- Definitions: `l2product`
- Theorems: `REAL_MUL_ASSOC`, `REAL_INTEGRAL_LMUL`, `SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT`


---

## L2PRODUCT_RMUL

### Name of formal statement
L2PRODUCT_RMUL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2PRODUCT_RMUL = prove
 (`!s c f g.
        f square_integrable_on s /\ g square_integrable_on s
        ==> l2product s f (\x. c * g x) = c * l2product s f g`,
  ONCE_REWRITE_TAC[L2PRODUCT_SYM] THEN SIMP_TAC[L2PRODUCT_LMUL]);;
```
### Informal statement
For any set `s`, complex number `c`, and complex-valued functions `f` and `g`, if `f` is square integrable on `s` and `g` is square integrable on `s`, then the L2 product of `f` with the function defined by `x` mapping to `c * g x` on `s` is equal to `c` times the L2 product of `f` and `g` on `s`.

### Informal sketch
The proof proceeds as follows:
- First, apply `L2PRODUCT_SYM` to swap the arguments of the L2 product.
- Next, simplify using `L2PRODUCT_LMUL` which states that `l2product s (\x. c * f x) g = c * l2product s f g`.

### Mathematical insight
This theorem expresses the linearity of the L2 product with respect to scalar multiplication on the second argument. It shows that multiplying the second function in the L2 product by a constant factor results in the entire L2 product being multiplied by that same factor. This property is crucial in many areas of functional analysis and signal processing.

### Dependencies
- Theorems: `L2PRODUCT_SYM`, `L2PRODUCT_LMUL`


---

## L2NORM_LMUL

### Name of formal statement
L2NORM_LMUL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2NORM_LMUL = prove
 (`!f s c. f square_integrable_on s
           ==> l2norm s (\x. c * f(x)) = abs(c) * l2norm s f`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[l2norm; L2PRODUCT_LMUL; SQUARE_INTEGRABLE_LMUL] THEN
  ASM_SIMP_TAC[L2PRODUCT_RMUL; SQUARE_INTEGRABLE_LMUL] THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_2] THEN
  REWRITE_TAC[SQRT_MUL; POW_2_SQRT_ABS]);;
```
### Informal statement
For any function `f`, set `s`, and real number `c`, if `f` is square integrable on `s`, then the L2 norm of the function defined by `x` mapping to `c * f(x)` on the set `s` is equal to the absolute value of `c` multiplied by the L2 norm of `f` on `s`.

### Informal sketch
The theorem states that scaling a function within an L2 norm scales the result by the absolute value of the scaling factor. The proof proceeds as follows:
- Start by stripping the goal.
- Simplify using the definitions of `l2norm` and `square_integrable_on`, and the theorem `L2PRODUCT_LMUL`, which states `l2product s (\x. c * f x) (\x. g x) = c * (l2product s f g)`.
- Simplify again using `L2PRODUCT_RMUL`, which states `l2product s (\x. f x) (\x. c * g x) = c * (l2product s f g)` and `SQUARE_INTEGRABLE_LMUL`, which is likely a lemma stating that scalar multiples of square-integrable functions are square-integrable, *possibly redundant at this point*.
- Rewrite using the associativity of real multiplication. Additionally, rewrite using `GSYM REAL_POW_2` to transform `c * c` to `c pow 2`.
- Rewrite using `SQRT_MUL`, which states `sqrt (x * y) = sqrt x * sqrt y`, and `POW_2_SQRT_ABS`, which equates `sqrt (x pow 2)` to `abs x`.

### Mathematical insight
The L2 norm represents the "length" of a function. Multiplying the function by a constant `c` scales its length by the absolute value of `c`. This theorem is a fundamental property of the L2 norm and linear operations.

### Dependencies
- `l2norm`
- `L2PRODUCT_LMUL`
- `SQUARE_INTEGRABLE_LMUL`
- `L2PRODUCT_RMUL`
- `REAL_MUL_ASSOC`
- `REAL_POW_2`
- `SQRT_MUL`
- `POW_2_SQRT_ABS`

### Porting notes (optional)
The proof relies on properties of real numbers, such as associativity of multiplication and relationships between square roots, squares, and absolute values. Ensure that the target proof assistant has similar theorems available. The definitions of `l2norm` and `square_integrable_on` must be ported first. The tactics indicate a fairly straightforward equational reasoning style, so porting should be generally smooth.


---

## L2NORM_RMUL

### Name of formal statement
L2NORM_RMUL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2NORM_RMUL = prove
 (`!f s c. f square_integrable_on s
           ==> l2norm s (\x. f(x) * c) = l2norm s f * abs(c)`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[L2NORM_LMUL]);;
```
### Informal statement
For any function `f`, set `s`, and real number `c`, if `f` is square integrable on `s`, then the L2 norm of the function defined by `f(x) * c` on the set `s` is equal to the L2 norm of `f` on `s` multiplied by the absolute value of `c`.

### Informal sketch
The proof proceeds as follows:

- Rewrite the expression `f(x) * c ` as `c * f(x)` using the commutativity of real multiplication (`REAL_MUL_SYM`).
- Apply the theorem `L2NORM_LMUL`, which states that the L2 norm of `c * f` is `abs(c) * l2norm s f`.

### Mathematical insight
This theorem demonstrates a fundamental property of the L2 norm, showing how scalar multiplication interacts with the norm: scaling a function by a constant scales its L2 norm by the absolute value of that constant. This is a crucial property in functional analysis and useful for normalizing functions.

### Dependencies
- `REAL_MUL_SYM`
- `L2NORM_LMUL`


---

## L2NORM_NEG

### Name of formal statement
L2NORM_NEG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2NORM_NEG = prove
 (`!f s. f square_integrable_on s ==> l2norm s (\x. --(f x)) = l2norm s f`,
  ONCE_REWRITE_TAC[REAL_ARITH `--x:real = --(&1) * x`] THEN
  SIMP_TAC[L2NORM_LMUL; REAL_ABS_NEG; REAL_ABS_NUM; REAL_MUL_LID]);;
```

### Informal statement
For any function `f` and set `s`, if `f` is square integrable on `s`, then the L2 norm of the function that maps `x` to the negation of `f x` on `s` is equal to the L2 norm of `f` on `s`.

### Informal sketch
The proof proceeds by showing that the L2 norm of the negated function, `l2norm s (\x. --(f x))`, is equal to the L2 norm of the original function `f`, `l2norm s f`.
- First, rewrite `--x:real = --(&1) * x`.
- Then, simplify using `L2NORM_LMUL`, `REAL_ABS_NEG`, `REAL_ABS_NUM`, and `REAL_MUL_LID` to reduce the expression to the L2 norm of `f`.
    - `L2NORM_LMUL` allows extracting the absolute value of the scalar multiplier from the L2 norm, i.e., `l2norm s (\x. c * f x) = abs c * l2norm s f`.
    - `REAL_ABS_NEG` states that `abs (-x) = abs x` for real numbers.
    - `REAL_ABS_NUM` probably handles `abs (--(&1))` which simplifies to 1.
    - `REAL_MUL_LID` finally simplifies `1 * l2norm s f` to `l2norm s f`.

### Mathematical insight
The L2 norm is defined using the square root of the integral of the square of a function. Since the square of a negated function is the same as the square of the original function, the L2 norm is unaffected by negation. This theorem formalizes this intuition.

### Dependencies
- `square_integrable_on`
- `l2norm`
- `REAL_ARITH`
- `L2NORM_LMUL`
- `REAL_ABS_NEG`
- `REAL_ABS_NUM`
- `REAL_MUL_LID`


---

## L2NORM_SUB

### Name of formal statement
L2NORM_SUB

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2NORM_SUB = prove
 (`!f g s.  f square_integrable_on s /\ g square_integrable_on s
        ==> l2norm s (\x. f x - g x) = l2norm s (\x. g x - f x)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM REAL_NEG_SUB] THEN
  ASM_SIMP_TAC[L2NORM_NEG; SQUARE_INTEGRABLE_SUB; ETA_AX]);;
```
### Informal statement
For all functions `f` and `g`, and for all sets `s`, if `f` is square integrable on `s` and `g` is square integrable on `s`, then the L2 norm of the function `λx. f x - g x` on `s` is equal to the L2 norm of the function `λx. g x - f x` on `s`.

### Informal sketch
The proof demonstrates that the L2 norm of the difference of two functions `f` and `g` on a set `s` is the same regardless of the order in which the functions are subtracted.

- The proof begins by stripping the quantifiers and the assumption.
- It then rewrites `f x - g x` to `g x - f x` using `REAL_NEG_SUB` and `GSYM`. More specifically it exploits the property that `a - b = -(b - a)`.
- It uses the theorem `L2NORM_NEG`, which states that `l2norm s (\x. - f x) = l2norm s f`.
- Finally, it uses transitivity of equality applying `SQUARE_INTEGRABLE_SUB` and `ETA_AX` to complete the proof.

### Mathematical insight
The L2 norm represents a measure of the "size" or "magnitude" of a function. Since the L2 norm involves squaring the function, the sign of the difference `f(x) - g(x)` does not matter, which makes the L2 norm of `f(x) - g(x)` the same as the L2 norm of `g(x) - f(x)`. This result is important in functional analysis and particularly useful when dealing with function spaces and their properties.

### Dependencies
- `REAL_NEG_SUB`
- `L2NORM_NEG`
- `SQUARE_INTEGRABLE_SUB`
- `ETA_AX`


---

## L2_SUMMABLE

### Name of formal statement
L2_SUMMABLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2_SUMMABLE = prove
 (`!f s t.
     (!i. i IN t ==> (f i) square_integrable_on s) /\
     real_summable t (\i. l2norm s (f i))
     ==> ?g. g square_integrable_on s /\
             ((\n. l2norm s (\x. sum (t INTER (0..n)) (\i. f i x) - g x))
              ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n:num. (lift o f n o drop)`;
                 `&2`; `IMAGE lift s`; `t:num->bool`]
        LSPACE_SUMMABLE) THEN
  ASM_REWRITE_TAC[GSYM SQUARE_INTEGRABLE_LSPACE] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ANTS_TAC THENL
   [UNDISCH_TAC `real_summable t (\i. l2norm s (f i))` THEN
    MATCH_MP_TAC EQ_IMP THEN
    REWRITE_TAC[real_summable; real_sums; REALLIM_SEQUENTIALLY] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `x:real` THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `e:real` THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `N:num` THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    ASM_SIMP_TAC[GSYM L2NORM_LNORM; IN_INTER; ETA_AX];
    DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^1` MP_TAC) THEN
    SUBGOAL_THEN `g = (lift o (drop o g o lift) o drop)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_DEF; LIFT_DROP]; ALL_TAC] THEN
    ABBREV_TAC `h = drop o g o lift` THEN
    REWRITE_TAC[GSYM SQUARE_INTEGRABLE_LSPACE] THEN
    DISCH_THEN(fun th -> EXISTS_TAC `h:real->real` THEN MP_TAC th) THEN
    ASM_CASES_TAC `h square_integrable_on s` THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[o_DEF; GSYM LIFT_SUB; REWRITE_RULE[o_DEF] (GSYM LIFT_SUM);
             FINITE_NUMSEG; FINITE_INTER] THEN
    SUBGOAL_THEN `!f. (\x. lift(f(drop x))) = (lift o f o drop)`
     (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    MATCH_MP_TAC(GSYM L2NORM_LNORM) THEN
    MATCH_MP_TAC SQUARE_INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC SQUARE_INTEGRABLE_SUM THEN
    ASM_SIMP_TAC[FINITE_INTER; IN_INTER; FINITE_NUMSEG]]);;
```

### Informal statement
For all functions `f` from natural numbers to functions from real numbers to real numbers, for all sets `s` of real numbers, and for all sets `t` of natural numbers, if the function `λi. f i` is square integrable on `s` for all `i` in `t` and the series `Σ(i ∈ t). l2norm s (f i)` is real summable, then there exists a function `g` from real numbers to real numbers such that `g` is square integrable on `s` and the sequence `λn. l2norm s (λx. Σ(i ∈ t ∩ {0, ..., n}). f i x - g x)` converges sequentially to 0.

### Informal sketch
The proof demonstrates that if a series of functions `f i` is square integrable on a set `s` and the series of their L2 norms is summable, then the partial sums of the functions converge in the L2 norm to a square integrable function `g`.
- Apply `LSPACE_SUMMABLE` after lifting everything to L^2 space.
- Show `g` can be expressed through lifts and drops (`g = (lift o (drop o g o lift) o drop)`).
- The main steps consist of showing the existence of a suitable `g` that is square integrable and demonstrating the convergence of partial sums to it. This involves reasoning about limits (`real_summable`, `REALLIM_SEQUENTIALLY`), sums (`sum`), and L2 norms (`l2norm`). The tactic `L2SPACE_SUMMABLE` is employed. The equivalence between `L2NORM_LNORM` is applied to relate the L2 norm to the integral. Properties of summability (`real_summable`, `real_sums`), sequential limits (`REALLIM_SEQUENTIALLY`), and the definition of the L2 norm (`L2NORM_LNORM`) and square integrability (`SQUARE_INTEGRABLE_LSPACE`) are used extensively. Set operations and finiteness are handled using `FINITE_NUMSEG`, `FINITE_INTER`, and `IN_INTER`. The properties of lifts and drops (`LIFT_DROP`) are leveraged.

### Mathematical insight
The theorem states that if we have a series of square-integrable functions whose L2 norms are summable, the series converges to a limit in the L2 norm, and the function in the L2 space has the same properties as a function in the original space. In essence, the theorem relates the pointwise convergence (implied by the summability of the norms) to convergence in the L2 sense. This sort of result is a basic component of functional analysis allowing one to, for example, switch limits and integrals under appropriate conditions.

### Dependencies
- `LSPACE_SUMMABLE`
- `SQUARE_INTEGRABLE_LSPACE`
- `real_summable`
- `real_sums`
- `REALLIM_SEQUENTIALLY`
- `FUN_EQ_THM`
- `SUM_EQ`
- `L2NORM_LNORM`
- `IN_INTER`
- `ETA_AX`
- `o_DEF`
- `LIFT_DROP`
- `GSYM SQUARE_INTEGRABLE_LSPACE`
- `LIFT_SUB`
- `LIFT_SUM`
- `FINITE_NUMSEG`
- `FINITE_INTER`
- `SQUARE_INTEGRABLE_SUB`
- `SQUARE_INTEGRABLE_SUM`


---

## L2_COMPLETE

### Name of formal statement
L2_COMPLETE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let L2_COMPLETE = prove
 (`!f s. (!i. f i square_integrable_on s) /\
         (!e. &0 < e ==> ?N. !m n. m >= N /\ n >= N
                                   ==> l2norm s (\x. f m x - f n x) < e)
         ==> ?g. g square_integrable_on s /\
                 ((\n. l2norm s (\x. f n x - g x)) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n:num. lift o f n o drop`; `&2`; `IMAGE lift s`]
        RIESZ_FISCHER) THEN
  ASM_SIMP_TAC[GSYM SQUARE_INTEGRABLE_LSPACE] THEN ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV;
    DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^1` MP_TAC) THEN
    SUBGOAL_THEN `g = (lift o (drop o g o lift) o drop)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_DEF; LIFT_DROP]; ALL_TAC] THEN
    ABBREV_TAC `h = drop o g o lift` THEN
    REWRITE_TAC[GSYM SQUARE_INTEGRABLE_LSPACE] THEN
    DISCH_THEN(fun th -> EXISTS_TAC `h:real->real` THEN MP_TAC th) THEN
    ASM_CASES_TAC `h square_integrable_on s` THEN ASM_REWRITE_TAC[]] THEN
  (SUBGOAL_THEN `!f g. (\x. (lift o f o drop) x - (lift o g o drop) x) =
                       (lift o (\y. f y - g y) o drop)`
    (fun th -> REWRITE_TAC[th])
   THENL
    [REWRITE_TAC[o_DEF; LIFT_DROP; LIFT_SUB];
     ASM_SIMP_TAC[GSYM L2NORM_LNORM; SQUARE_INTEGRABLE_SUB; ETA_AX]]) THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs(x - &0) = x`; GE;
               L2NORM_POS_LE; SQUARE_INTEGRABLE_SUB; ETA_AX]);;
```

### Informal statement
For all functions `f` and sets `s`, if the following two conditions hold:
1. For all natural numbers `i`, the function `f i` is square-integrable on `s`.
2. For all real numbers `e` greater than 0, there exists a natural number `N` such that for all natural numbers `m` and `n`, if `m` is greater than or equal to `N` and `n` is greater than or equal to `N`, then the L2 norm over `s` of the function defined by `x` mapping to `f m x - f n x` is less than `e`.
Then there exists a function `g` such that `g` is square-integrable on `s` and the sequence of L2 norms over `s` of the function defined by `x` mapping to `f n x - g x` converges sequentially to 0 as `n` tends to infinity.

### Informal sketch
The proof proceeds as follows:
- Apply `RIESZ_FISCHER` theorem to `lift o f n o drop` and `IMAGE lift s`.
- Simplify using `SQUARE_INTEGRABLE_LSPACE`.
- Reduce the goal to its assumptions.
- Deal with real number arithmetic.
- Choose a function `g` such that `g = (lift o (drop o g o lift) o drop)`.
- Apply the assumption that `h = drop o g o lift` is square integrable.
- Show that `!f g. (\x. (lift o f o drop) x - (lift o g o drop) x) = (lift o (\y. f y - g y) o drop)`.
- Rewrite using the definition of sequential convergence `REALLIM_SEQUENTIALLY`.
- Simplify using real arithmetic and properties of L2 norm.

### Mathematical insight
This theorem states the L2 completeness property: if a sequence of functions `f n` is Cauchy in the L2 norm, meaning that the L2 norm of `f m - f n` goes to zero as `m` and `n` approach infinity, then there exists a limit function `g` that is also square-integrable, and the L2 norm of `f n - g` goes to zero as `n` approaches infinity.  The main idea is to relate the given sequence and the set to the space which the `RIESZ_FISCHER` theorem applies to, and then extract a `g` function by considering the lifted and dropped mapping.

### Dependencies
- `RIESZ_FISCHER`
- `SQUARE_INTEGRABLE_LSPACE`
- `FUN_EQ_THM`
- `o_DEF`
- `LIFT_DROP`
- `L2NORM_LNORM`
- `SQUARE_INTEGRABLE_SUB`
- `REALLIM_SEQUENTIALLY`
- `L2NORM_POS_LE`
- `GE`

### Porting notes (optional)
- The `lift` and `drop` functions suggest that we are mapping from `real` to `real^1` and back again. Ensure that the target proof assistant has similar mapping functionality or that the target is set up with these types.
- The proof uses real analysis concepts (square integrability, L2 norm, limit of sequences) that need to be defined in the target system.
- The `RIESZ_FISCHER` theorem will need to be ported first.


---

## SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS

### Name of formal statement
SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS = prove
 (`!f s e. real_measurable s /\ f square_integrable_on s /\ &0 < e
           ==> ?g. g real_continuous_on (:real) /\
                   g square_integrable_on s /\
                   l2norm s (\x. f x - g x) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `IMAGE lift s`; `&2:real`; `e:real`]
          LSPACE_APPROXIMATE_CONTINUOUS) THEN
  ASM_REWRITE_TAC[GSYM SQUARE_INTEGRABLE_LSPACE; REAL_OF_NUM_LE; ARITH;
                  GSYM REAL_MEASURABLE_MEASURABLE] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^1` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `drop o g o lift` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_CONTINUOUS_ON; o_DEF; LIFT_DROP; ETA_AX;
                    IMAGE_LIFT_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[SQUARE_INTEGRABLE_LSPACE; o_DEF; LIFT_DROP; ETA_AX];
    DISCH_TAC THEN
    ASM_SIMP_TAC[L2NORM_LNORM; SQUARE_INTEGRABLE_SUB; ETA_AX] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < e ==> x = y ==> y < e`)) THEN
    REWRITE_TAC[o_DEF; LIFT_DROP; LIFT_SUB]]);;
```

### Informal statement
For every real-valued function `f` and set `s` of real numbers and positive real number `e`, if `s` is measurable and `f` is square integrable on `s` and `e` is greater than zero, then there exists a real-valued function `g` such that `g` is continuous on the whole real line, `g` is square integrable on `s`, and the L2 norm of the function `lambda x. f x - g x` on the set `s` is less than `e`.

### Informal sketch
The proof demonstrates that a square-integrable function can be approximated by a continuous function in the L2 norm.
- Start with a square integrable function `f` on a measurable set `s` and a positive number `e`.
- Apply `LSPACE_APPROXIMATE_CONTINUOUS` by lifting problem into `real^1 -> real^1`, using `lift`, `IMAGE lift s`, `&2:real` and `e:real`. This theorem provides a continuous function `g` on `real^1` that approximates `f` in the L2 sense.
- Instantiate the existential quantifier with the continuous function on reals `drop o g o lift`, where `g` is a real-valued function defined on `real^1`.
- Show that the constructed function `drop o g o lift` satisfies the necessary conditions.
    - Verify that `drop o g o lift` is continuous via `REAL_CONTINUOUS_ON`, `o_DEF`, `LIFT_DROP`, `ETA_AX`, `IMAGE_LIFT_UNIV`.
    - Prove `drop o g o lift` square integrable on `s` using `SQUARE_INTEGRABLE_LSPACE`, `o_DEF`, `LIFT_DROP`, `ETA_AX`.
    - Demonstrate the L2 norm of the difference between `f` and `drop o g o lift` is less than `e`, using `L2NORM_LNORM`, `SQUARE_INTEGRABLE_SUB`, `ETA_AX`, `o_DEF`, `LIFT_DROP`, `LIFT_SUB`.

### Mathematical insight
This theorem is a fundamental result in real analysis and functional analysis. It states that continuous functions are dense in the space of square-integrable functions `L^2(s)`. This means that any square-integrable function can be approximated arbitrarily closely by a continuous function. This property is crucial for many applications, such as numerical analysis, signal processing, and quantum mechanics.

### Dependencies
- `SQUARE_INTEGRABLE_LSPACE`
- `REAL_OF_NUM_LE`
- `ARITH`
- `REAL_MEASURABLE_MEASURABLE`
- `REAL_CONTINUOUS_ON`
- `o_DEF`
- `LIFT_DROP`
- `ETA_AX`
- `IMAGE_LIFT_UNIV`
- `L2NORM_LNORM`
- `SQUARE_INTEGRABLE_SUB`
- `LSPACE_APPROXIMATE_CONTINUOUS`

### Porting notes (optional)
- The theorem `LSPACE_APPROXIMATE_CONTINUOUS` is used, which is related to approximating a measurable function in `L^2` space with a continuous function.
- The constructs `lift` and `drop` map between the real numbers and one-dimensional real vectors, so corresponding functions may need to be defined in a target theorem prover, especially if it does not have native support for finite-dimensional vector spaces.
- The port should pay attention to how continuity and measurability are defined and proven in the target system.


---

## SCHWARZ_BOUND

### Name of formal statement
SCHWARZ_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SCHWARZ_BOUND = prove
 (`!f s. real_measurable s /\ f square_integrable_on s
         ==> f absolutely_real_integrable_on s /\
             (real_integral s f) pow 2
             <= real_measure s * real_integral s (\x. f x pow 2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
  REWRITE_TAC[SQUARE_INTEGRABLE_LSPACE; REAL_MEASURABLE_MEASURABLE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP
   (ONCE_REWRITE_RULE[IMP_CONJ_ALT] HOELDER_BOUND)) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[GSYM ABSOLUTELY_REAL_INTEGRABLE_ON; RPOW_POW] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [square_integrable_on]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[REAL_INTEGRAL; ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
  REWRITE_TAC[REAL_POW_1; o_DEF; NORM_1; LIFT_DROP; REAL_POW2_ABS] THEN
  REWRITE_TAC[GSYM REAL_MEASURE_MEASURE] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_MEASURE_POS_LE] THEN
  REWRITE_TAC[REAL_ARITH `abs x <= x <=> &0 <= x`] THEN
  MATCH_MP_TAC INTEGRAL_DROP_POS THEN
  REWRITE_TAC[LIFT_DROP; REAL_LE_POW_2] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_INTEGRABLE_ON]) THEN
  REWRITE_TAC[o_DEF]);;
```
### Informal statement
For any function `f` and set `s`, if `s` is real-measurable and `f` is square integrable on `s`, then `f` is absolutely real-integrable on `s` and the square of the real integral of `f` over `s` is less than or equal to the product of the real measure of `s` and the real integral of the square of `f` over `s`.

### Informal sketch
The proof proceeds as follows:
- Assume `f` is square integrable on `s` and `s` is real-measurable.
- Apply `HOELDER_BOUND` theorem.
- Simplify using `REAL_RAT_REDUCE_CONV` and rewrite using `absolute_real_integrable_on` and `RPOW_POW`.
- Further simplification involves rewriting `square_integrable_on` and eliminates redundant assumptions.
- Use transitivity of real less than or equal by `REAL_LE_TRANS`
- `REAL_LE_LMUL` is used to multiply both sides of inequality by `real_measure s`
- Rewrite the powers and use theorems to show `f` is real-integrable.

### Mathematical insight
The `SCHWARZ_BOUND` lemma is the statement of the Cauchy-Schwarz inequality for real integrals. It provides an upper bound for the absolute value of the integral of a function in terms of the integral of its square and the measure of the domain. It is a fundamental result in analysis and has many applications, including establishing convergence results and bounding errors.

### Dependencies
- Definitions: `real_measurable`, `square_integrable_on`, `absolutely_real_integrable_on`, `real_integral`, `real_measure`
- Theorems: `SQUARE_INTEGRABLE_LSPACE`, `REAL_MEASURABLE_MEASURABLE`, `HOELDER_BOUND`, `ABSOLUTELY_REAL_INTEGRABLE_ON`, `RPOW_POW`, `REAL_INTEGRAL`, `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE`, `REAL_POW_1`, `REAL_POW2_ABS`, `REAL_MEASURE_MEASURE`, `REAL_LE_TRANS`, `REAL_LE_LMUL`, `REAL_MEASURE_POS_LE`, `INTEGRAL_DROP_POS`, `REAL_LE_POW_2`, `REAL_INTEGRABLE_ON`


---

## orthonormal_system

### Name of formal statement
- orthonormal_system

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let orthonormal_system = new_definition
 `orthonormal_system s w <=>
        !m n. l2product s (w m) (w n) = if m = n then &1 else &0`;;
```
### Informal statement
- The predicate `orthonormal_system s w` holds if and only if for all `m` and `n`, the L2 inner product of `w m` and `w n` with respect to the measure `s` is equal to 1 if `m` equals `n`, and 0 otherwise.

### Informal sketch
- The definition introduces the concept of an orthonormal system. An orthonormal system `w` with respect to a measure `s` consists of functions such that the inner product of any two distinct functions is zero, and the inner product of any function with itself is one.
- The structure of the definition is a straightforward equivalence, defining `orthonormal_system s w` directly in terms of the L2 inner product `l2product s (w m) (w n)` and the Kronecker delta expressed as `if m = n then &1 else &0`. No complex proof is involved since it is a definition.

### Mathematical insight
- This definition is fundamental in functional analysis, particularly in the study of Hilbert spaces and Fourier analysis. An orthonormal system forms a basis for a Hilbert space, allowing functions to be represented as a linear combination of these orthonormal functions (a Fourier series). The `l2product` represents the inner product with respect to a measure, and the orthogonality condition ensures that the coefficients in the Fourier series can be easily computed.

### Dependencies
- Definitions: `l2product`

### Porting notes (optional)
- In other proof assistants, ensure that the inner product notation and measure theory infrastructure are properly defined or imported before defining `orthonormal_system`. The handling of real numbers (`&1`, `&0`) should also be checked. Also, the conditional expression `if m = n then &1 else &0` resembles the `Kronecker delta`, so be sure that your target proof assistant handles this correctly.


---

## orthonormal_coefficient

### Name of formal statement
- orthonormal_coefficient

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let orthonormal_coefficient = new_definition
 `orthonormal_coefficient s w f (n:num) = l2product s (w n) f`;;
```
### Informal statement
- The orthonormal coefficient of a function `f` with respect to an orthonormal sequence `w` indexed by natural numbers in the L2 space defined by `s` is defined as the L2 inner product of `f` with the `n`-th element of the sequence `w`.

### Informal sketch
- The definition introduces the term `orthonormal_coefficient` as a function that takes a space `s`, an orthonormal sequence `w`, a function `f`, and a natural number `n`.
- It is defined directly as the L2 inner product `l2product s (w n) f` of the `n`-th element of the sequence `w` with the function `f`.
- There is no proof because this is a definition.

### Mathematical insight
- This definition provides the formula for calculating the coefficients in the expansion of a function `f` in terms of an orthonormal basis `w` within a given L2 space. The L2 space provides a notion of inner product and norm, enabling the decomposition of functions into orthogonal components. This is fundamental in Fourier analysis and other areas of applied mathematics.

### Dependencies
- Definitions:
  - `l2product`


---

## ORTHONORMAL_SYSTEM_L2NORM

### Name of formal statement
ORTHONORMAL_SYSTEM_L2NORM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ORTHONORMAL_SYSTEM_L2NORM = prove
 (`!s w. orthonormal_system s w ==> !i. l2norm s (w i) = &1`,
  SIMP_TAC[orthonormal_system; l2norm; SQRT_1]);;
```
### Informal statement
For all sets `s` of functions, and for all functions `w` from a domain type to a codomain type, if `s` is an orthonormal system with respect to the weighting function `w`, then, for all elements `i` in the domain of `w`, the L2 norm of `s` evaluated at `w i` is equal to 1.

### Informal sketch
The proof proceeds by:
- Assuming `orthonormal_system s w`.
- Considering an arbitrary `i`.
- Expanding `l2norm s (w i)` using the definition of `l2norm`.
- Simplifying the expression using the definition of `orthonormal_system` and the theorem `SQRT_1`, which states that the square root of 1 is 1.

### Mathematical insight
This theorem states a fundamental property of orthonormal systems: the L2 norm of an orthonormal system `s` with respect to a weighting function `w`, when evaluated at any element `w i` in the domain of `w`, is always equal to 1. This reflects the normalization condition inherent in the definition of orthonormality. Namely, not only are the elements of `s` orthogonal to each other (i.e., their inner product is 0), each element is also normalized to have unit length / magnitude (i.e., its L2 norm is 1).

### Dependencies
- Definitions: `orthonormal_system`, `l2norm`
- Theorems: `SQRT_1`


---

## ORTHONORMAL_PARTIAL_SUM_DIFF

### Name of formal statement
ORTHONORMAL_PARTIAL_SUM_DIFF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ORTHONORMAL_PARTIAL_SUM_DIFF = prove
 (`!s w a f t.
        orthonormal_system s w /\ (!i. (w i) square_integrable_on s) /\
        f square_integrable_on s /\ FINITE t
        ==> l2norm s (\x. f(x) - sum t (\i. a i * w i x)) pow 2 =
            (l2norm s f) pow 2 + sum t (\i. (a i) pow 2) -
            &2 * sum t (\i. a i * orthonormal_coefficient s w f i)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. sum t (\i:num. a i * w i x)) square_integrable_on s`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQUARE_INTEGRABLE_SUM; ETA_AX; FINITE_NUMSEG;
                 SQUARE_INTEGRABLE_LMUL];
   ALL_TAC] THEN
  ASM_SIMP_TAC[L2NORM_POW_2; SQUARE_INTEGRABLE_SUB; ETA_AX; L2PRODUCT_LSUB] THEN
  ASM_SIMP_TAC[SQUARE_INTEGRABLE_SUB; ETA_AX; L2PRODUCT_RSUB] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x' = x /\ b - &2 * x = c ==> a - x - (x' - b) = a + c`) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[L2PRODUCT_SYM]; ALL_TAC] THEN
  ASM_SIMP_TAC[L2PRODUCT_RSUM; ETA_AX; SQUARE_INTEGRABLE_LMUL; FINITE_NUMSEG;
               SQUARE_INTEGRABLE_SUM] THEN
  ASM_SIMP_TAC[L2PRODUCT_LSUM; SQUARE_INTEGRABLE_LMUL; FINITE_NUMSEG;
               ETA_AX] THEN
  ASM_SIMP_TAC[L2PRODUCT_RMUL; SQUARE_INTEGRABLE_LMUL; ETA_AX] THEN
  ASM_SIMP_TAC[L2PRODUCT_LMUL; SQUARE_INTEGRABLE_LMUL; ETA_AX] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[orthonormal_system]) THEN
  ASM_SIMP_TAC[COND_RAND; REAL_MUL_RZERO; SUM_DELTA] THEN
  REWRITE_TAC[orthonormal_coefficient; REAL_MUL_RID; GSYM REAL_POW_2] THEN
  REWRITE_TAC[L2PRODUCT_SYM]);;
```
### Informal statement
For any set `s`, function `w`, function `a`, function `f`, and finite set `t` of natural numbers, if `w` forms an orthonormal system on `s`, every `w i` is square integrable on `s` for all `i`, `f` is square integrable on `s`, and `t` is a finite set, then the square of the L2 norm of the function that maps `x` to `f(x) - sum t (\i. a i * w i x)` is equal to the square of the L2 norm of `f` plus the sum over `t` of `(a i)` squared, minus 2 times the sum over `t` of `a i * orthonormal_coefficient s w f i`.

### Informal sketch
The proof demonstrates that the L2 norm squared of the difference between a function `f` and a partial sum of an orthonormal system `w` can be expressed in terms of the L2 norm squared of `f`, the sum of squares of coefficients `a i`, and the sum of products of `a i` with orthonormal coefficients.

- First, it is established that the function `sum t (\i. a i * w i x)` is square integrable on `s`.
- The theorem unfolds the definition of the L2 norm using `L2NORM_POW_2`.
- The proof begins by expanding the L2 norm of the difference using the properties of L2 norms and products (`L2PRODUCT_LSUB`, `L2PRODUCT_RSUB`).
- Trigonometric simplification is then applied, utilizing the symmetry of the L2 product (`L2PRODUCT_SYM`).
- The L2 product of a function with a sum is rewritten as the sum of L2 products (`L2PRODUCT_RSUM`, `L2PRODUCT_LSUM`).
- Properties of L2 products with scalar multiplication (`L2PRODUCT_RMUL`, `L2PRODUCT_LMUL`) are applied.
- The orthonormal system property is used to simplify the L2 product of `w i` with `w j` (`orthonormal_system`). Kronecker delta and simplification of sums are used, particularly `SUM_DELTA`.
- The definition of the orthonormal coefficient (`orthonormal_coefficient`), product symmetry (`L2PRODUCT_SYM`), and algebraic simplification are applied to reach the final expression.

### Mathematical insight
This theorem provides a formula for calculating the error when approximating a function `f` by a partial sum of an orthonormal system. The orthonormal coefficients `a i` are chosen to minimize this error in a least-squares sense. The theorem quantifies how much the L2 norm squared of the approximation deviates from the original function `f`. It is a fundamental result in functional analysis and approximation theory.

### Dependencies
- `orthonormal_system`
- `SQUARE_INTEGRABLE_SUM`
- `ETA_AX`
- `FINITE_NUMSEG`
- `SQUARE_INTEGRABLE_LMUL`
- `L2NORM_POW_2`
- `SQUARE_INTEGRABLE_SUB`
- `L2PRODUCT_LSUB`
- `L2PRODUCT_RSUB`
- `L2PRODUCT_SYM`
- `L2PRODUCT_RSUM`
- `L2PRODUCT_LSUM`
- `L2PRODUCT_RMUL`
- `L2PRODUCT_LMUL`
- `COND_RAND`
- `REAL_MUL_RZERO`
- `SUM_DELTA`
- `orthonormal_coefficient`
- `REAL_MUL_RID`
- `REAL_POW_2`

### Porting notes (optional)
- The theorem relies heavily on properties of sums and L2 norms/products. Ensure the target proof assistant has similar lemmas available.
- The HOL Light proof involves rewriting with various properties of square integrability and orthonormal systems. The porter needs to ensure those properties are defined and proved in target system, or reprove them.


---

## ORTHONORMAL_OPTIMAL_PARTIAL_SUM

### Name of formal statement
ORTHONORMAL_OPTIMAL_PARTIAL_SUM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ORTHONORMAL_OPTIMAL_PARTIAL_SUM = prove
 (`!s w a f t.
        orthonormal_system s w /\ (!i. (w i) square_integrable_on s) /\
        f square_integrable_on s /\ FINITE t
        ==>  l2norm s (\x. f(x) -
                           sum t (\i. orthonormal_coefficient s w f i * w i x))
             <= l2norm s (\x. f(x) - sum t (\i. a i * w i x))`,
  REPEAT STRIP_TAC THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
   [L2NORM_LE; SQUARE_INTEGRABLE_SUM; ETA_AX; FINITE_NUMSEG;
    GSYM L2NORM_POW_2; SQUARE_INTEGRABLE_LMUL; SQUARE_INTEGRABLE_SUB] THEN
  ASM_SIMP_TAC[ORTHONORMAL_PARTIAL_SUM_DIFF] THEN
  REWRITE_TAC[REAL_LE_LADD] THEN
  ASM_SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_SUB] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH
   `b pow 2 - &2 * b * b <= a pow 2 - &2 * a * b <=> &0 <= (a - b) pow 2`] THEN
  REWRITE_TAC[REAL_LE_POW_2]);;
```

### Informal statement
For all sets `s`, functions `w`, `a`, and `f`, and sets `t`, if `w` forms an orthonormal system on `s`, every `w i` is square integrable on `s` for all `i`, `f` is square integrable on `s`, and `t` is a finite set, then the L2 norm of the function `x` mapping to `f x` minus the sum over `t` of `(orthonormal_coefficient s w f i)` times `w i x`, is less than or equal to the L2 norm of the function `x` mapping to `f x` minus the sum over `t` of `(a i)` times `w i x`.

### Informal sketch
The proof establishes that the partial sum using orthonormal coefficients provides the best L2 approximation to `f`, compared to any other linear combination of the orthonormal basis.

- The proof starts by stripping the quantifiers and assumptions using `REPEAT STRIP_TAC`.
- A simplification using `GEN_SIMPLIFY_CONV` and basic simplification sets rewrites the L2 norm of the difference, leveraging the square integrability assumptions and properties of norms.
- We use `L2NORM_LE` to prepare for comparison of the squares of the L2 norms. We rewrite the squared L2 norms using the theorem `ORTHONORMAL_PARTIAL_SUM_DIFF` which shows the orthogonality of the error term and the partial sum.
- We rewrite the inequality to be proved using `REAL_LE_LADD` to move terms from one side of the inequality to the other.
- Summation manipulation theorems, such as `SUM_LMUL` and `SUM_SUB` are applied to rearrange and simplify the expressions. `SUM_LE` is used to compare the sums.
- Finally, using `REAL_ARITH`, the goal is reduced to an inequality of the form `0 <= (a - b) pow 2`, which is then proved by `REAL_LE_POW_2`.

### Mathematical insight
The theorem states that the partial sum obtained by projecting a function `f` onto an orthonormal basis provides the best possible approximation in the L2 sense. This is a fundamental result in approximation theory and functional analysis, showing the optimality of the orthonormal projection.

### Dependencies
* `orthonormal_system`
* `square_integrable_on`
* `l2norm`
* `orthonormal_coefficient`
* `FINITE`
* `L2NORM_LE`
* `SQUARE_INTEGRABLE_SUM`
* `ETA_AX`
* `FINITE_NUMSEG`
* `GSYM L2NORM_POW_2`
* `SQUARE_INTEGRABLE_LMUL`
* `SQUARE_INTEGRABLE_SUB`
* `ORTHONORMAL_PARTIAL_SUM_DIFF`
* `REAL_LE_LADD`
* `GSYM SUM_LMUL`
* `GSYM SUM_SUB`
* `SUM_LE`
* `REAL_ARITH`
* `REAL_LE_POW_2`

### Porting notes (optional)
The proof involves manipulation of sums and integrals, and relies heavily on the properties of square integrable functions and orthonormal systems. Ensure that the target proof assistant has adequate support for dealing with such concepts. The rewriting steps, particularly those involving `REAL_ARITH`, might require manual intervention in some systems.


---

## BESSEL_INEQUALITY

### Name of formal statement
BESSEL_INEQUALITY

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BESSEL_INEQUALITY = prove
 (`!s w f t.
        orthonormal_system s w /\ (!i. (w i) square_integrable_on s) /\
        f square_integrable_on s /\ FINITE t
        ==> sum t (\i. (orthonormal_coefficient s w f i) pow 2)
             <= l2norm s f pow 2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ORTHONORMAL_PARTIAL_SUM_DIFF) THEN
  DISCH_THEN(MP_TAC o SPEC `orthonormal_coefficient s w f`) THEN
  REWRITE_TAC[GSYM REAL_POW_2; REAL_ARITH `a + b - &2 * b = a - b`] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= p ==> p = x - y ==> y <= x`) THEN
  REWRITE_TAC[REAL_LE_POW_2]);;
```
### Informal statement
For all sets `s`, functions `w`, and `f`, and sets `t`, if `w` is an orthonormal system on `s`, and for all `i`, `w i` is square integrable on `s`, and `f` is square integrable on `s`, and `t` is a finite set, then the sum over `t` of the squares of the orthonormal coefficients of `f` with respect to `w` is less than or equal to the square of the L2 norm of `f` on `s`.

### Informal sketch
The proof proceeds as follows:
- Assume `s`, `w`, and `f`, and `t` satisfy the premises: `w` is an orthonormal system on `s`, `w i` is square integrable on `s` for all `i`, `f` is square integrable on `s`, and `t` is a finite set.
- Apply `ORTHONORMAL_PARTIAL_SUM_DIFF` to express the difference between the squared L2 norm of `f` and the sum of squared orthonormal coefficients over `t` as the squared L2 norm of the difference between `f` and the partial sum.
- Use the fact that the orthonormal coefficient, `orthonormal_coefficient s w f i`, exists.
- Rearrange terms using `REAL_POW_2` and arithmetic simplification to isolate the difference between squared norms.
- Use the fact that `0 <= p ==> p = x - y ==> y <= x`.
- Rewrite with `REAL_LE_POW_2` to complete the proof.

### Mathematical insight
Bessel's inequality states that the sum of the squares of the projections of a function onto an orthonormal system is less than or equal to the square of the norm of the function. It is a fundamental result in Fourier analysis and Hilbert space theory. It provides an upper bound on how much of the "energy" of a function can be captured by its projections onto an orthonormal basis (or a partial orthonormal system, as is the case in this theorem).

### Dependencies
- `orthonormal_system`
- `square_integrable_on`
- `FINITE`
- `orthonormal_coefficient`
- `l2norm`
- `ORTHONORMAL_PARTIAL_SUM_DIFF`
- `REAL_POW_2`
- `REAL_ARITH`
- `REAL_LE_POW_2`


---

## FOURIER_SERIES_SQUARE_SUMMABLE

### Name of formal statement
FOURIER_SERIES_SQUARE_SUMMABLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_SERIES_SQUARE_SUMMABLE = prove
 (`!s w f t.
        orthonormal_system s w /\ (!i. (w i) square_integrable_on s) /\
        f square_integrable_on s
        ==> real_summable t (\i. (orthonormal_coefficient s w f i) pow 2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[real_summable; real_sums; REALLIM_SEQUENTIALLY] THEN
  MP_TAC(ISPECL
   [`\n. sum(t INTER (0..n)) (\i. (orthonormal_coefficient s w f i) pow 2)`;
    `l2norm s f pow 2`] CONVERGENT_BOUNDED_MONOTONE) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`s:real->bool`; `w:num->real->real`;
                `f:real->real`; `t INTER (0..n)`] BESSEL_INEQUALITY) THEN
    ASM_SIMP_TAC[FINITE_INTER; FINITE_NUMSEG] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs(x) <= y`) THEN
    SIMP_TAC[SUM_POS_LE; FINITE_INTER; FINITE_NUMSEG; REAL_LE_POW_2] THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    SIMP_TAC[FINITE_INTER; SUBSET_REFL; FINITE_NUMSEG; REAL_LE_POW_2];
    DISJ1_TAC THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    SIMP_TAC[INTER_SUBSET; FINITE_NUMSEG; REAL_LE_POW_2; FINITE_INTER] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> u INTER s SUBSET u INTER t`) THEN
    REWRITE_TAC[SUBSET_NUMSEG] THEN ASM_ARITH_TAC]);;
```
### Informal statement
For any set `s` of real numbers, any function `w` from natural numbers to real-valued functions, and any real-valued function `f`, if `w` forms an orthonormal system on `s`, if each `w i` is square-integrable on `s`, and if `f` is square-integrable on `s`, then the series with terms `(orthonormal_coefficient s w f i)^2` (where `i` ranges over the natural numbers) is real-summable with respect to the trivial filter `t`.

### Informal sketch
The proof proceeds as follows:
- Assume `s` is a set, `w` is a function from natural numbers to functions, `f` is a real-valued function, `w` forms an orthonormal system on `s`, each `w i` is square-integrable on `s`, and `f` is square-integrable on `s`.
- Show that the series `\i. (orthonormal_coefficient s w f i) pow 2` is real-summable. This is done by showing that the partial sums are bounded above.
- The `real_summable` is rewritten to `real_sums` and `REALLIM_SEQUENTIALLY` which requires to show that the sequence of partial sums converges.
- Apply `CONVERGENT_BOUNDED_MONOTONE` to show that an increasing sequence that is bounded above converges. The sequence under consideration is `\n. sum(t INTER (0..n)) (\i. (orthonormal_coefficient s w f i) pow 2)` and the upper bound is `l2norm s f pow 2`.
- The proof strategy reduces to showing two things:
  - The sequence of partial sums is bounded above. This uses `BESSEL_INEQUALITY` with specialized arguments `s`, `w`, `f`, and `t INTER (0..n)`. Utilizing `FINITE_INTER` & `FINITE_NUMSEG` and simplifying with `SUM_POS_LE`, `SUM_SUBSET_SIMPLE` and `REAL_LE_POW_2` together with real arithmetic facts gives that the sequence of partial sums is bounded above by the square of the `l2norm` of `f`.
  - The sequence of partial sums is monotonically increasing. This Uses `SUM_SUBSET_SIMPLE` and set manipulations involving `INTER_SUBSET` to show that the sum over `t INTER (0..n)` is less than or equal to the sum over `t INTER (0..SUC n)`.

### Mathematical insight
The theorem states that for a square-integrable function `f`, the sum of the squares of its orthonormal coefficients with respect to an orthonormal system `w` is summable. This is a consequence of Bessel's inequality, which states that the sum of the squares of the magnitudes of the orthonormal coefficients is bounded above by the square of the `L2` norm of the function. The `FOURIER_SERIES_SQUARE_SUMMABLE` theorem is a key step in proving the completeness of the orthonormal system and the convergence of the Fourier series in the `L2` sense.

### Dependencies
- Definitions: `real_summable`, `real_sums`, `square_integrable_on`, `orthonormal_system`, `orthonormal_coefficient`, `l2norm`
- Theorems: `REALLIM_SEQUENTIALLY`, `CONVERGENT_BOUNDED_MONOTONE`, `BESSEL_INEQUALITY`, `FINITE_INTER`, `FINITE_NUMSEG`, `SUM_POS_LE`, `SUM_SUBSET_SIMPLE`, `REAL_LE_POW_2`, `IMP_CONJ`, `REAL_LE_TRANS`, `SET_RULE`, `SUBSET_NUMSEG`.

### Porting notes (optional)
- The proof relies heavily on real analysis results such as the monotone convergence theorem (`CONVERGENT_BOUNDED_MONOTONE`) and properties of summable series. The porter should ensure that these results are available in the target proof assistant.
- The use of `SUM_SUBSET_SIMPLE` suggests that the target proof assistant should have good support for reasoning about sums over subsets of finite sets.
- The target proof assistant needs to have a library for real analysis and measure theory, including definitions and theorems about square-integrable functions and orthonormal systems.


---

## ORTHONORMAL_FOURIER_PARTIAL_SUM_DIFF_SQUARED

### Name of formal statement
ORTHONORMAL_FOURIER_PARTIAL_SUM_DIFF_SQUARED

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ORTHONORMAL_FOURIER_PARTIAL_SUM_DIFF_SQUARED = prove
 (`!s w a f t.
    orthonormal_system s w /\ (!i. (w i) square_integrable_on s) /\
    f square_integrable_on s /\ FINITE t
    ==> l2norm s (\x. f x -
                      sum t (\i. orthonormal_coefficient s w f i * w i x))
        pow 2 =
        l2norm s f pow 2 - sum t (\i. orthonormal_coefficient s w f i pow 2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ORTHONORMAL_PARTIAL_SUM_DIFF) THEN
  DISCH_THEN(MP_TAC o SPEC `orthonormal_coefficient s w f`) THEN
  REWRITE_TAC[GSYM REAL_POW_2; REAL_ARITH `a + b - &2 * b = a - b`]);;
```
### Informal statement
For any set `s`, function `w` (representing an orthonormal system), function `f`, and finite set `t`, if `w` is an orthonormal system on `s`, each `w i` is square integrable on `s` for all `i`, `f` is square integrable on `s`, and `t` is a finite set, then the square of the L2 norm of the difference between `f(x)` and the sum over `t` of the orthonormal coefficients of `f` with respect to `w` multiplied by `w i x` is equal to the square of the L2 norm of `f` minus the sum over `t` of the squares of the orthonormal coefficients of `f` with respect to `w`.

### Informal sketch
- The proof starts by generalizing all variables and discharging the assumptions.
- Apply `ORTHONORMAL_PARTIAL_SUM_DIFF` to rewrite the L2 norm of the functions difference in terms of `orthonormal_coefficient s w f i`.
- Specialize the theorem with `orthonormal_coefficient s w f`.
- Rewrite using `GSYM REAL_POW_2` and `REAL_ARITH `a + b - &2 * b = a - b``.

### Mathematical insight
This theorem states that the squared L2 norm of the error when approximating a function `f` by a partial sum of its orthonormal expansion is equal to the squared L2 norm of `f` minus the sum of the squares of the coefficients in the partial sum. This is a form of Parseval's identity for partial sums. This result quantifies how much energy resides in the components of `f` that are *not* captured by the finite set partial sum representation. The orthonormal property is crucial here to get the simplification on the right hand side.

### Dependencies
- `ORTHONORMAL_PARTIAL_SUM_DIFF`
- `orthonormal_coefficient`
- `GSYM REAL_POW_2`
- `REAL_ARITH `a + b - &2 * b = a - b``


---

## FOURIER_SERIES_L2_SUMMABLE

### Name of formal statement
FOURIER_SERIES_L2_SUMMABLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_SERIES_L2_SUMMABLE = prove
 (`!s w f t.
    orthonormal_system s w /\ (!i. (w i) square_integrable_on s) /\
    f square_integrable_on s
    ==> ?g. g square_integrable_on s /\
            ((\n. l2norm s
                    (\x. sum (t INTER (0..n))
                             (\i. orthonormal_coefficient s w f i * w i x) -
                         g(x))) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC L2_COMPLETE THEN
  ASM_SIMP_TAC[SQUARE_INTEGRABLE_SUM; FINITE_INTER; FINITE_NUMSEG;
               SQUARE_INTEGRABLE_LMUL; ETA_AX] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `t:num->bool` o
   MATCH_MP FOURIER_SERIES_SQUARE_SUMMABLE) THEN
  REWRITE_TAC[REAL_SUMMABLE; summable; sums; CONVERGENT_EQ_CAUCHY] THEN
  REWRITE_TAC[cauchy; GE] THEN
  DISCH_THEN(MP_TAC o SPEC `(e:real) pow 2`) THEN
  ASM_SIMP_TAC[REAL_POW_LT] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `N:num` THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN MATCH_MP_TAC WLOG_LE THEN
  CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THENL
   [ASM_CASES_TAC `N:num <= m` THEN ASM_CASES_TAC `N:num <= n` THEN
    ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC L2NORM_SUB THEN
    ASM_SIMP_TAC[SQUARE_INTEGRABLE_SUM; FINITE_INTER; FINITE_NUMSEG;
               SQUARE_INTEGRABLE_LMUL; ETA_AX];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `m:num`]) THEN
  SIMP_TAC[DIST_REAL; GSYM drop; DROP_VSUM; FINITE_INTER; FINITE_NUMSEG] THEN
  ASM_REWRITE_TAC[o_DEF; LIFT_DROP] THEN
  SUBGOAL_THEN
   `!f. sum (t INTER (0..n)) f - sum (t INTER (0..m)) f =
        sum (t INTER (m+1..n)) f`
   (fun th -> REWRITE_TAC[th])
  THENL
   [X_GEN_TAC `h:num->real` THEN
    REWRITE_TAC[REAL_ARITH `a - b:real = c <=> b + c = a`] THEN
    MATCH_MP_TAC SUM_UNION_EQ THEN
    SIMP_TAC[FINITE_INTER; FINITE_NUMSEG; EXTENSION; IN_INTER; NOT_IN_EMPTY;
             IN_UNION; IN_NUMSEG] THEN
    CONJ_TAC THEN X_GEN_TAC `i:num` THEN
    ASM_CASES_TAC `(i:num) IN t` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> y < e ==> x < e`) THEN
  ASM_SIMP_TAC[L2NORM_POW_2; SQUARE_INTEGRABLE_SUM; FINITE_INTER;
               FINITE_NUMSEG; SQUARE_INTEGRABLE_LMUL; ETA_AX] THEN
  ASM_SIMP_TAC[L2PRODUCT_RSUM; ETA_AX; SQUARE_INTEGRABLE_LMUL; FINITE_NUMSEG;
               FINITE_INTER; SQUARE_INTEGRABLE_SUM] THEN
  ASM_SIMP_TAC[L2PRODUCT_LSUM; SQUARE_INTEGRABLE_LMUL; FINITE_NUMSEG;
               FINITE_INTER; ETA_AX] THEN
  ASM_SIMP_TAC[L2PRODUCT_RMUL; SQUARE_INTEGRABLE_LMUL; ETA_AX] THEN
  ASM_SIMP_TAC[L2PRODUCT_LMUL; SQUARE_INTEGRABLE_LMUL; ETA_AX] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[orthonormal_system]) THEN
  ASM_SIMP_TAC[COND_RAND; REAL_MUL_RZERO; SUM_DELTA] THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_POW_2; REAL_ARITH `x <= abs x`]);;
```
### Informal statement
For any set `s`, function `w` from natural numbers to real-valued functions, real valued function `f`, and boolean function `t` on natural numbers, if
(1) `s` is an `orthonormal_system` with respect to `w`, and
(2) for all natural numbers `i`, the function `w i` is square integrable on `s`, and
(3) the function `f` is square integrable on `s`,
then there exists a function `g` such that
(1) `g` is square integrable on `s`, and
(2) the sequence defined by `n` maps to the L2 norm on `s` of the function 
`x` maps to the sum over the intersection of `{0,...,n}` and `t` of the function `i` maps to `orthonormal_coefficient s w f i * w i x`, minus `g(x)`, converges sequentially to 0.

### Informal sketch
The proof establishes the L2 convergence of the Fourier series of a square-integrable function `f` with respect to an orthonormal system `w`.

- The proof starts by assuming the hypotheses regarding the orthonormal system `s` with the function `w`, the square integrability of `w i` for each `i`, and the square integrability of `f`. It aims to show the existence of a square-integrable function `g` such that the partial sums of the Fourier series converge to `g` in the L2 norm.
- The theorem `FOURIER_SERIES_SQUARE_SUMMABLE` is used to infer that the sum of squares of the Fourier coefficients is convergent. This, along with the completeness of L2 space, suggests that the Fourier series should converge in L2.
- The proof uses the fact that convergence implies the Cauchy criterion. It shows that for any `e > 0`, there exists `N` such that for all `m, n > N`, the distance between the partial sums `sum (t INTER (0..n)) (\i. orthonormal_coefficient s w f i * w i x)` and `sum (t INTER (0..m)) (\i. orthonormal_coefficient s w f i * w i x)` in L2 norm is less than `e`.
- The proof employs `WLOG_LE` to assume without loss of generality that `N <= m` and `N <= n` at some point. Then using `L2NORM_SUB`, the proof reduces the problem to showing the real part of the L2 norm of the difference of the partial sums is less than `e`.
- With the help of `SUM_UNION_EQ`, the difference of sums is converted into a sum over the interval `(m ; n]`.
- The orthonormal property of the system `w` and properties of L2 inner products (`L2PRODUCT_LSUM`, `L2PRODUCT_RSUM`, `L2PRODUCT_LMUL`, `L2PRODUCT_RMUL`) are used to simplify the L2 norm of the difference of partial sums to `sum i. orthonormal_coefficient s w f i pow 2`.
- Finally, using the Cauchy criterion on `sum i. orthonormal_coefficient s w f i pow 2`, convergence is established, which means a `g` with the required properties exists and therefore the goal is achieved.

### Mathematical insight
The theorem demonstrates a fundamental property of Fourier series in the context of L2 spaces: that the Fourier series of a square-integrable function converges to a square-integrable function in the L2 norm. This convergence is a cornerstone of Fourier analysis. It guarantees that the expansion of a function in terms of an orthonormal basis is meaningful and well-behaved in the L2 sense.

### Dependencies
- `SQUARE_INTEGRABLE_SUM`
- `FINITE_INTER`
- `FINITE_NUMSEG`
- `SQUARE_INTEGRABLE_LMUL`
- `ETA_AX`
- `L2_COMPLETE`
- `FOURIER_SERIES_SQUARE_SUMMABLE`
- `REAL_SUMMABLE`
- `summable`
- `sums`
- `CONVERGENT_EQ_CAUCHY`
- `cauchy`
- `GE`
- `REAL_POW_LT`
- `MONO_EXISTS`
- `WLOG_LE`
- `REAL_POW_LT2_REV`
- `DIST_REAL`
- `GSYM drop`
- `DROP_VSUM`
- `o_DEF`
- `LIFT_DROP`
- `REAL_ARITH`
- `SUM_UNION_EQ`
- `EXTENSION`
- `IN_INTER`
- `NOT_IN_EMPTY`
- `IN_UNION`
- `IN_NUMSEG`
- `L2NORM_POW_2`
- `L2PRODUCT_RSUM`
- `L2PRODUCT_LSUM`
- `L2PRODUCT_RMUL`
- `L2PRODUCT_LMUL`
- `orthonormal_system`
- `COND_RAND`
- `REAL_MUL_RZERO`
- `SUM_DELTA`
- `REAL_MUL_RID`
- `REAL_POW_2`
- `REAL_ARITH`

### Porting notes (optional)
- The proof relies heavily on real analysis and properties of sums and L2 spaces. Ensure that the target proof assistant has adequate support for these concepts.
- The tactic `WLOG_LE` may need to be implemented manually in other systems, by explicitly splitting the proof into cases.
- Automation may be needed to discharge some of the real arithmetic and set-theoretic goals.


---

## FOURIER_SERIES_L2_SUMMABLE_STRONG

### Name of formal statement
FOURIER_SERIES_L2_SUMMABLE_STRONG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_SERIES_L2_SUMMABLE_STRONG = prove
 (`!s w f t.
    orthonormal_system s w /\ (!i. (w i) square_integrable_on s) /\
    f square_integrable_on s
    ==> ?g. g square_integrable_on s /\
            (!i. i IN t
                 ==> orthonormal_coefficient s w (\x. f x - g x) i = &0) /\
            ((\n. l2norm s
                   (\x. sum (t INTER (0..n))
                            (\i. orthonormal_coefficient s w f i * w i x) -
                        g(x))) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `t:num->bool` o
    MATCH_MP FOURIER_SERIES_L2_SUMMABLE) THEN
  REWRITE_TAC[orthonormal_coefficient] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real->real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[orthonormal_coefficient] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC
   `\n. l2product s (w i)
     (\x. (f x - sum (t INTER (0..n)) (\i. l2product s (w i) f * w i x)) +
          (sum (t INTER (0..n)) (\i. l2product s (w i) f * w i x) - g x))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_EVENTUALLY THEN
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN GEN_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
   [L2PRODUCT_RADD; SQUARE_INTEGRABLE_SUB;  SQUARE_INTEGRABLE_SUM;
    FINITE_INTER; FINITE_NUMSEG; SQUARE_INTEGRABLE_LMUL; ETA_AX] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ADD_LID] THEN
  MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_EVENTUALLY THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `i:num` THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[L2PRODUCT_RSUB; SQUARE_INTEGRABLE_SUM; L2PRODUCT_RSUM;
           FINITE_INTER; FINITE_NUMSEG; SQUARE_INTEGRABLE_LMUL; ETA_AX] THEN
    ASM_SIMP_TAC[L2PRODUCT_RMUL; ETA_AX] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[orthonormal_system]) THEN
    ASM_SIMP_TAC[COND_RAND; REAL_MUL_RZERO] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    ASM_SIMP_TAC[SUM_DELTA; IN_INTER; IN_NUMSEG; LE_0; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_SUB_REFL];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] REALLIM_NULL_COMPARISON)) THEN
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SCHWARTZ_INEQUALITY_ABS o
        lhand o snd) THEN
    ASM_SIMP_TAC[SQUARE_INTEGRABLE_SUB;  SQUARE_INTEGRABLE_SUM;
      FINITE_INTER; FINITE_NUMSEG; SQUARE_INTEGRABLE_LMUL; ETA_AX] THEN
    ASM_SIMP_TAC[ORTHONORMAL_SYSTEM_L2NORM; REAL_MUL_LID]]);;
```
### Informal statement
For any set `s`, orthonormal system `w` with respect to `s`, and function `f`, if `w i` is square integrable on `s` for all `i`, and `f` is square integrable on `s`, then there exists a function `g` such that `g` is square integrable on `s`; and for all `i`, if `i` is in the set `t`, then the orthonormal coefficient of `f(x) - g(x)` with respect to `s` and `w` at `i` is equal to 0; and the sequence formed by the L2 norm of the difference between the sum from 0 to `n` (restricted to `t`) of the orthonormal coefficient of `f` with respect to `s` and `w` at `i` times `w i x`, and `g(x)`, converges to 0 sequentially as `n` tends to infinity.

### Informal sketch
The proof demonstrates the existence of a square-integrable function `g` that satisfies two conditions related to Fourier series:

- **Condition 1 (Orthonormal Coefficient Condition):** The orthonormal coefficients of the difference between `f` and `g` are zero for indices in the set `t`.
- **Condition 2 (L2 Convergence Condition):** The partial sums of the Fourier series of `f` (restricted to indices in `t`) converge to `g` in the L2 norm.

Here's a breakdown of the proof's main steps:

- Assume `orthonormal_system s w`, `w i` is square integrable on `s` for all `i`, and `f` is square integrable on `s`. Goal is to show existence of `g`.
- Instantiate the theorem `FOURIER_SERIES_L2_SUMMABLE` to specify the set `t`, showing the existence of a square-integrable function `g` such that the Fourier coefficients of `f - g` vanish on `t` and the partial sums converge to `g` in the L2 norm.
- Rewrite using `orthonormal_coefficient` to use `l2product` in the existing assumption
- Use `MONO_EXISTS` to introduce the function `g` in the statement.
- Exploit `REALLIM_UNIQUE` theorem, demonstrating the uniqueness of limits, and then construct a suitable candidate function for `g`.
- The convergence of the sequence is shown by demonstrating that the limit of the difference between the partial sums and `g` is zero.
- Simplify the expression by applying properties of `l2product`, `square_integrable`, `sum`, and other related definitions.
- Decompose sequence limits additively, proving that `l2product s (w i) (\x. f x - g x)` tends to 0 sequentially
- Use `SCHWARTZ_INEQUALITY_ABS` to bound the L2 norm.
- Employ properties of orthonormal systems and square integrable functions and simplify.

### Mathematical insight
This theorem provides a strong convergence result for Fourier series in an L2 setting. Given a square-integrable function `f` and an orthonormal system `w`, it guarantees the existence of a square-integrable function `g` to which the partial sums of the Fourier series of `f` converge in the L2 norm. Furthermore, the Fourier coefficients of the difference `f - g` vanish on the index set `t`, meaning `g` is the best approximation to `f`.

### Dependencies
- Theorem: `FOURIER_SERIES_L2_SUMMABLE`
- Theorem: `REALLIM_UNIQUE`
- Theorem: `TRIVIAL_LIMIT_SEQUENTIALLY`
- Theorem: `REALLIM_EVENTUALLY`
- Theorem: `ALWAYS_EVENTUALLY`
- Theorem: `FUN_EQ_THM`
- Theorem: `REALLIM_ADD`
- Theorem: `EVENTUALLY_SEQUENTIALLY`
- Theorem: `SCHWARTZ_INEQUALITY_ABS`

- Definition: `orthonormal_coefficient`
- Definition: `orthonormal_system`
- Definition: `square_integrable_on`
- Definition: `l2norm`
- Definition: `sequentially`
- Definition: `l2product`

- Other: `L2PRODUCT_RADD`, `SQUARE_INTEGRABLE_SUB`, `SQUARE_INTEGRABLE_SUM`, `FINITE_INTER`, `FINITE_NUMSEG`, `SQUARE_INTEGRABLE_LMUL`, `ETA_AX`, `GSYM REAL_ADD_LID`, `L2PRODUCT_RSUB`, `L2PRODUCT_RSUM`, `L2PRODUCT_RMUL`, `COND_RAND`, `REAL_MUL_RZERO`, `EQ_SYM_EQ`, `SUM_DELTA`, `IN_INTER`, `IN_NUMSEG`, `LE_0`, `REAL_MUL_RID`, `REAL_SUB_REFL`, `IMP_CONJ_ALT`, `REALLIM_NULL_COMPARISON`, `ORTHONORMAL_SYSTEM_L2NORM`, `REAL_MUL_LID`

### Porting notes (optional)
- The use of `sequentially` for limits may require adaptation depending on the target system's limit infrastructure.
- The extensive use of real analysis lemmas like `SCHWARTZ_INEQUALITY_ABS` suggests that a well-developed real analysis library is needed.
- The proof relies heavily on rewriting with various lemmas related to square integrability, orthonormal systems, and L2 products. Ensure that such lemmas can be ported and effectively used for rewriting.


---

## REAL_INTEGRABLE_ON_INTERVAL_TAC

### Name of formal statement
REAL_INTEGRABLE_ON_INTERVAL_TAC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_INTEGRABLE_ON_INTERVAL_TAC =
  MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
  REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
  GEN_TAC THEN DISCH_TAC THEN REAL_DIFFERENTIABLE_TAC;;
```

### Informal statement
The tactic `REAL_INTEGRABLE_ON_INTERVAL_TAC` proves that if a function is differentiable on an interval, then it is integrable on that interval, given that it is continuous.

### Informal sketch
The tactic proceeds by:
- Apply `MATCH_MP_TAC` with `REAL_INTEGRABLE_CONTINUOUS`: This step aims to prove integrability by showing continuity. It focuses the goal on proving the function is continuous.
- Apply `MATCH_MP_TAC` with `REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON`: This step uses the theorem that if a function is differentiable on an interval, then it is continuous on that interval.
- Apply `REWRITE_TAC` with `REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE`: This rewrites the goal using the definition of differentiability on an interval, expanding the concept to its epsilon-delta definition.
- Apply `GEN_TAC`: This tactic universally quantifies any remaining free variables in the goal.
- Apply `DISCH_TAC`: This tactic discharges the assumptions of the current goal, turning them into hypotheses.
- Apply `REAL_DIFFERENTIABLE_TAC`: This tactic attempts to prove the differentiability of the function using standard rules and definitions of real differentiability.

### Mathematical insight
This tactic implements a standard approach to proving that a function is integrable over an interval, by showing it is differentiable and then using the fact that differentiability implies continuity, and continuity implies integrability on bounded intervals.

### Dependencies
- `REAL_INTEGRABLE_CONTINUOUS`
- `REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON`
- `REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE`
- `REAL_DIFFERENTIABLE_TAC`


---

## HAS_REAL_INTEGRAL_SIN_NX

### Name of formal statement
HAS_REAL_INTEGRAL_SIN_NX

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HAS_REAL_INTEGRAL_SIN_NX = prove
 (`!n. ((\x. sin(&n * x)) has_real_integral &0) (real_interval[--pi,pi])`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[HAS_REAL_INTEGRAL_0; REAL_MUL_LZERO; SIN_0] THEN
  MP_TAC(ISPECL
   [`\x. --(inv(&n) * cos(&n * x))`; `\x. sin(&n * x)`; `--pi`; `pi`]
        REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  SIMP_TAC[REAL_ARITH `&0 <= pi ==> --pi <= pi`; PI_POS_LE] THEN
  REWRITE_TAC[REAL_MUL_RNEG; SIN_NPI; COS_NPI; SIN_NEG; COS_NEG] THEN
  REWRITE_TAC[REAL_SUB_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN REAL_DIFF_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM REAL_OF_NUM_EQ]) THEN
  CONV_TAC REAL_FIELD);;
```
### Informal statement
For all real numbers `n`, the function defined by lambda abstraction `\x. sin(&n * x)` has a real integral equal to `&0` on the real interval from `--pi` to `pi` (inclusive).

### Informal sketch
The theorem states that the integral of `sin(n*x)` from `-pi` to `pi` is 0 for any real number `n`. The proof proceeds as follows:

- Case split on whether `n = 0`.
  - If `n = 0`, then `sin(&n * x)` becomes `sin(0)`, which simplifies to `0`. The integral of `0` is `0`.
  - Otherwise, use the fundamental theorem of calculus: `REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS` is applied to the function `\x. sin(&n * x)` with antiderivative `\x. --(inv(&n) * cos(&n * x))`, considering the limits `--pi` and `pi`.
  - Simplify the expression obtained from the fundamental theorem of calculus: `--(inv(&n) * cos(&n * pi)) - --(inv(&n) * cos(&n * --pi))`.
  - Use trigonometric identities `SIN_NPI`, `COS_NPI`, `SIN_NEG`, `COS_NEG` to simplify the expressions `cos(&n * pi)` and `cos(&n * --pi)`. Since cosine is an even function, `cos(&n * --pi)` is equal to `cos(&n * pi)`.
  - After simplification, we have `--(inv(&n) * cos(&n * pi)) - --(inv(&n) * cos(&n * pi))`, which is equal to zero due to `REAL_SUB_REFL`.
  - Verify the needed differentiability results by discharging assumptions.

### Mathematical insight
The integral of `sin(n*x)` from `-pi` to `pi` is 0 due to the symmetry of the sine function around the y-axis, which results in the areas above and below the x-axis cancelling each other out in the definite integral.

### Dependencies
- `HAS_REAL_INTEGRAL_0`
- `REAL_MUL_LZERO`
- `SIN_0`
- `REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS`
- `PI_POS_LE`
- `REAL_MUL_RNEG`
- `SIN_NPI`
- `COS_NPI`
- `SIN_NEG`
- `COS_NEG`
- `REAL_SUB_REFL`
- `REAL_OF_NUM_EQ`

### Porting notes (optional)
The proof relies on the fundamental theorem of calculus. Ensure that the target proof assistant has a similar theorem available or can be derived. The use of `REAL_ARITH` and `REAL_FIELD` suggests the proof may benefit from an automated real arithmetic decision procedure.


---

## REAL_INTEGRABLE_SIN_CX

### Name of formal statement
REAL_INTEGRABLE_SIN_CX

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_INTEGRABLE_SIN_CX = prove
 (`!c. (\x. sin(c * x)) real_integrable_on real_interval[--pi,pi]`,
  GEN_TAC THEN REAL_INTEGRABLE_ON_INTERVAL_TAC);;
```
### Informal statement
For any real number `c`, the function defined by `\x. sin(c * x)` is real integrable on the real interval from `-pi` to `pi`.

### Informal sketch
The proof proceeds by using `REAL_INTEGRABLE_ON_INTERVAL_TAC`. The tactic likely expands the definition of `real_integrable_on` and `real_interval[--pi,pi]`. It probably leverages the fact that `sin` is continuous, and any continuous function on a closed and bounded interval is integrable.

### Mathematical insight
This theorem states that the function `sin(c * x)` is integrable on the interval `[-pi, pi]` for any real number `c`. This is a standard result in real analysis, useful for Fourier analysis and other applications.

### Dependencies
- `GEN_TAC`
- `REAL_INTEGRABLE_ON_INTERVAL_TAC`


---

## REAL_INTEGRAL_SIN_NX

### Name of formal statement
REAL_INTEGRAL_SIN_NX

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_INTEGRAL_SIN_NX = prove
 (`!n. real_integral (real_interval[--pi,pi]) (\x. sin(&n * x)) = &0`,
  GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_SIN_NX]);;
```

### Informal statement
For all natural numbers `n`, the real integral of the function `sin(&n * x)` over the closed real interval from `-pi` to `pi` is equal to `0`.

### Informal sketch
The proof proceeds as follows:
- First, apply `GEN_TAC` to discharge the universal quantifier for `n`.
- Then, apply `MATCH_MP_TAC` with the theorem `REAL_INTEGRAL_UNIQUE`. This likely establishes that if a function has a real integral and there exists another value that satisfies the integral condition, then the integral must be unique and equal to that value.
- Finally, rewrite using the theorem `HAS_REAL_INTEGRAL_SIN_NX`. This theorem should provide the actual value (0) of the integral and prove that `sin(&n * x)` has a real integral on the interval `[--pi, pi]`.

### Mathematical insight
The theorem states that the integral of `sin(n*x)` from `-pi` to `pi` is 0 for any natural number `n`. This reflects the symmetry of the sine function about the origin.  Integrating over an interval centered at the origin cancels out the positive and negative portions of the function. This property is important in Fourier analysis and understanding the orthogonality of trigonometric functions.

### Dependencies
- Theorems: `REAL_INTEGRAL_UNIQUE`, `HAS_REAL_INTEGRAL_SIN_NX`


---

## HAS_REAL_INTEGRAL_COS_NX

### Name of formal statement
HAS_REAL_INTEGRAL_COS_NX

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HAS_REAL_INTEGRAL_COS_NX = prove
 (`!n. ((\x. cos(&n * x)) has_real_integral (if n = 0 then &2 * pi else &0))
       (real_interval[--pi,pi])`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[COS_0; REAL_MUL_LZERO] THEN
    REWRITE_TAC[REAL_ARITH `&2 * pi = &1 * (pi - --pi)`] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_CONST THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL
     [`\x. inv(&n) * sin(&n * x)`; `\x. cos(&n * x)`; `--pi`; `pi`]
          REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
    SIMP_TAC[REAL_ARITH `&0 <= pi ==> --pi <= pi`; PI_POS_LE] THEN
    REWRITE_TAC[REAL_MUL_RNEG; SIN_NPI; COS_NPI; SIN_NEG; COS_NEG] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_NEG_0; REAL_SUB_REFL] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN REAL_DIFF_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
     [GSYM REAL_OF_NUM_EQ]) THEN
    CONV_TAC REAL_FIELD]);;
```
### Informal statement
For all real numbers `n`, the function `λx. cos(n * x)` has a real integral equal to if `n = 0` then `2 * pi` else `0` on the real interval `[-pi, pi]`.

### Informal sketch
The proof proceeds by cases on whether `n = 0`.

- Case `n = 0`:
    - Simplify `cos(0 * x)` to `1`.
    - Rewrite `2 * pi` as `1 * (pi - --pi)`.
    - Apply the theorem `HAS_REAL_INTEGRAL_CONST` that the integral of a constant function `c` on the interval `[a, b]` is `c * (b - a)`. This depends on the fact `pi > 0`.
- Case `n != 0`:
    - Apply the real fundamental theorem of calculus (`REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS`) with the antiderivative `inv(n) * sin(n * x)`.
    - Show that `0 <= pi ==> --pi <= pi` and `pi > 0`.
    - Rewrite `inv(n) * sin(n * pi) - inv(n) * sin(n* --pi)` and use identities for sine and cosine, namely, `sin(n * pi)`, `cos(n * pi)`, `sin(-x) = - sin(x)`, and `cos(-x) = cos(x)`.
    - Simplify using `REAL_MUL_RZERO`, `REAL_NEG_0`, and `REAL_SUB_REFL`, which are real arithmetic rules.
    - Show that the derivative of `inv(n) * sin(n * x)` is `cos(n * x)` using `REAL_DIFF_TAC` and `REAL_FIELD`, and rewriting using `REAL_OF_NUM_EQ`.

### Mathematical insight
This theorem calculates the definite integral of `cos(n * x)` from `-pi` to `pi`, a standard result in Fourier analysis related to the orthogonality of trigonometric functions. Specifically, the integral is `2*pi` when `n = 0` and `0` otherwise. This result is crucial in defining Fourier series.

### Dependencies
- `HAS_REAL_INTEGRAL_CONST`
- `REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS`
- `PI_POS`
- `PI_POS_LE`
- `COS_0`
- `REAL_MUL_LZERO`
- `REAL_ARITH`
- `REAL_MUL_RNEG`
- `SIN_NPI`
- `COS_NPI`
- `SIN_NEG`
- `COS_NEG`
- `REAL_MUL_RZERO`
- `REAL_NEG_0`
- `REAL_SUB_REFL`
- `REAL_DIFF_TAC`
- `REAL_OF_NUM_EQ`
- `REAL_FIELD`

### Porting notes (optional)
The `HAS_REAL_INTEGRAL` predicate and related theorems about integration will need to be defined or imported. The tactic `REAL_ARITH_TAC` handles linear arithmetic reasoning in HOL Light, and may require a different approach in other systems. The tactic `REAL_FIELD` is used for simplifying expressions in the real field. The port should seek an equivalent tactic or convert to a more primitive rule based proof.


---

## REAL_INTEGRABLE_COS_CX

### Name of formal statement
REAL_INTEGRABLE_COS_CX

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_INTEGRABLE_COS_CX = prove
 (`!c. (\x. cos(c * x)) real_integrable_on real_interval[--pi,pi]`,
  GEN_TAC THEN REAL_INTEGRABLE_ON_INTERVAL_TAC);;
```
### Informal statement
For all real numbers `c`, the function defined by `\x. cos(c * x)` is real integrable on the real interval `[--pi, pi]`.

### Informal sketch
The proof proceeds by applying the tactic `REAL_INTEGRABLE_ON_INTERVAL_TAC` to the goal `!c. (\x. cos(c * x)) real_integrable_on real_interval[--pi,pi]`. This tactic likely uses standard results about the integrability of continuous functions on closed intervals and the properties of cosine to establish the result. It would involve showing that `cos(c * x)` is continuous on the interval `[--pi, pi]`, and then applying a theorem that states continuous functions on closed bounded intervals are integrable.

### Mathematical insight
This theorem establishes that the cosine function, scaled by a constant, is integrable on the interval from `-pi` to `pi`. This is a fundamental result in real analysis and is often used in Fourier analysis and other areas of mathematics and physics. It justifies the computation of integrals involving cosine functions over this standard interval.

### Dependencies
- `real_integrable_on`
- `real_interval`
- `cos`


---

## REAL_INTEGRAL_COS_NX

### Name of formal statement
REAL_INTEGRAL_COS_NX

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_INTEGRAL_COS_NX = prove
 (`!n. real_integral (real_interval[--pi,pi]) (\x. cos(&n * x)) =
       if n = 0 then &2 * pi else &0`,
  GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_COS_NX]);;
```
### Informal statement
For all natural numbers `n`, the definite real integral of the function `cos(&n * x)` over the real interval `[-pi, pi]` is equal to `&2 * pi` if `n` is `0`, and equal to `&0` otherwise.

### Informal sketch
The proof proceeds as follows:
- The goal is to prove the integral of `cos(&n * x)` from `-pi` to `pi` is `2*pi` if `n = 0` and `0` otherwise.
- Use `GEN_TAC` to discharge the quantifier `!n`.
- Apply `MATCH_MP_TAC` with `REAL_INTEGRAL_UNIQUE` to reduce the problem to showing that the right-hand side satisfies the `HAS_REAL_INTEGRAL` relation with the integrand on the given interval. This requires showing that the given expression is `a` real integral.
- Use `REWRITE_TAC` with the theorem `HAS_REAL_INTEGRAL_COS_NX` to complete the proof. The theorem `HAS_REAL_INTEGRAL_COS_NX` states that the derivative of `sin(&n * x) / &n` is `cos(&n * x)` given `n` is not zero and the antiderivative of `cos(&0 * x)` which simplifies to `cos(&0)` which equals `1` is `x`.

### Mathematical insight
This theorem demonstrates a fundamental property of cosine functions: their orthogonality over the interval `[-pi, pi]`. Specifically, the integral of `cos(n*x)` over this interval vanishes for all non-zero integers `n`. This property is a cornerstone of Fourier analysis.

### Dependencies
- `REAL_INTEGRAL_UNIQUE`
- `HAS_REAL_INTEGRAL_COS_NX`


---

## REAL_INTEGRAL_SIN_AND_COS

### Name of formal statement
REAL_INTEGRAL_SIN_AND_COS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_INTEGRAL_SIN_AND_COS = prove
 (`!m n. real_integral (real_interval[--pi,pi])
           (\x. cos(&m * x) * cos(&n * x)) =
                (if m = n then if n = 0 then &2 * pi else pi else &0) /\
         real_integral (real_interval[--pi,pi])
           (\x. cos(&m * x) * sin(&n * x)) = &0 /\
         real_integral (real_interval[--pi,pi])
           (\x. sin(&m * x) * cos(&n * x)) = &0 /\
         real_integral (real_interval[--pi,pi])
           (\x. sin(&m * x) * sin(&n * x)) =
              (if m = n /\ ~(n = 0) then pi else &0)`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN
  MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_SYM] THEN MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `m:num`] THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_MUL_SIN_COS; REAL_MUL_COS_SIN;
              REAL_MUL_COS_COS; REAL_MUL_SIN_SIN] THEN
  REWRITE_TAC[GSYM REAL_ADD_RDISTRIB; GSYM REAL_SUB_RDISTRIB] THEN
  SIMP_TAC[REAL_INTEGRAL_ADD; REAL_INTEGRAL_SUB; real_div;
           REAL_INTEGRABLE_SIN_CX; REAL_INTEGRABLE_COS_CX;
           REAL_INTEGRAL_RMUL; REAL_INTEGRABLE_SUB; REAL_INTEGRABLE_ADD] THEN
  ASM_SIMP_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_SUB] THEN
  REWRITE_TAC[REAL_INTEGRAL_SIN_NX; REAL_INTEGRAL_COS_NX] THEN
  REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO; REAL_ADD_LID] THEN
  ASM_SIMP_TAC[ARITH_RULE `n:num <= m ==> (m - n = 0 <=> m = n)`] THEN
  REWRITE_TAC[ADD_EQ_0] THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ARITH `(a + a) * inv(&2) = a`;
                  REAL_MUL_LZERO] THEN
  REAL_ARITH_TAC);;  
```

### Informal statement
For all natural numbers `m` and `n`, the following hold:
1. The definite integral of `cos(m * x) * cos(n * x)` from `-pi` to `pi` is equal to `2 * pi` if `m = n = 0`, is equal to `pi` if `m = n` and `n != 0`, and is equal to `0` otherwise.
2. The definite integral of `cos(m * x) * sin(n * x)` from `-pi` to `pi` is equal to `0`.
3. The definite integral of `sin(m * x) * cos(n * x)` from `-pi` to `pi` is equal to `0`.
4. The definite integral of `sin(m * x) * sin(n * x)` from `-pi` to `pi` is equal to `pi` if `m = n` and `n != 0`, and is equal to `0` otherwise.

### Informal sketch
The proof proceeds as follows:
- Generalize the goal by swapping universal quantifiers.
- Assume without loss of generality that `m >= n`.
- Split the goal into four subgoals, each corresponding to one of the integral equations.
- For the cosine * cosine case, use symmetry of multiplication of real numbers to simplify the goal.
- Introduce the natural numbers `n` and `m` into the assumptions.
- Apply trigonometric identities to express products of trigonometric functions as sums and differences:
  - `cos(m * x) * cos(n * x) = (cos((m + n) * x) + cos((m - n) * x)) / 2`
  - `cos(m * x) * sin(n * x) = (sin((m + n) * x) - sin((m - n) * x)) / 2`
  - `sin(m * x) * cos(n * x) = (sin((m + n) * x) + sin((m - n) * x)) / 2`
  - `sin(m * x) * sin(n * x) = (cos((m - n) * x) - cos((m + n) * x)) / 2`
- Distribute real division over addition and subtraction.
- Simplify using the properties of integrals, including linearity (`REAL_INTEGRAL_ADD`, `REAL_INTEGRAL_SUB`, `REAL_INTEGRAL_RMUL`), the integrability of sine and cosine functions (`REAL_INTEGRABLE_SIN_CX`, `REAL_INTEGRABLE_COS_CX`), and the properties of addition and subtraction.
- Simplify using the definitions of real numbers from numerals with `REAL_OF_NUM_ADD` and `REAL_OF_NUM_SUB`.
- Evaluate the integrals of `sin(n * x)` and `cos(n * x)` via `REAL_INTEGRAL_SIN_NX` and `REAL_INTEGRAL_COS_NX`.
- Further simplify by rewriting using `REAL_SUB_REFL`, `REAL_MUL_LZERO`, and `REAL_ADD_LID` and simplifications depending on `ARITH_RULE \`n:num <= m ==> (m - n = 0 <=> m = n)\``
- Rewrite using `ADD_EQ_0`.
- Perform case splitting on `n = 0`.
- Simplify using arithmetic reasoning.

### Mathematical insight
This theorem establishes the orthogonality of sine and cosine functions with integer multiples of `x` over the interval `[-pi, pi]`. These are fundamental results in Fourier analysis and are crucial for representing periodic functions as sums of sines and cosines. The orthogonality relations form the basis for computing Fourier coefficients.

### Dependencies
- `SWAP_FORALL_THM`
- `REAL_MUL_SYM`
- `REAL_MUL_SIN_COS`
- `REAL_MUL_COS_SIN`
- `REAL_MUL_COS_COS`
- `REAL_MUL_SIN_SIN`
- `REAL_ADD_RDISTRIB`
- `REAL_SUB_RDISTRIB`
- `REAL_INTEGRAL_ADD`
- `REAL_INTEGRAL_SUB`
- `real_div`
- `REAL_INTEGRABLE_SIN_CX`
- `REAL_INTEGRABLE_COS_CX`
- `REAL_INTEGRAL_RMUL`
- `REAL_INTEGRABLE_SUB`
- `REAL_INTEGRABLE_ADD`
- `REAL_OF_NUM_ADD`
- `REAL_OF_NUM_SUB`
- `REAL_INTEGRAL_SIN_NX`
- `REAL_INTEGRAL_COS_NX`
- `REAL_SUB_REFL`
- `REAL_MUL_LZERO`
- `REAL_ADD_LID`
- `ADD_EQ_0`

### Porting notes (optional)
- The proof relies heavily on the predefined integration tactics and simplification rules of HOL Light. In other proof assistants, one may need to provide the integration rules and trigonometric identities explicitly or use corresponding automation tools.
- The arithmetic reasoning (e.g., `ARITH_RULE`) may require adaptation to the specific arithmetic capabilities of the target proof assistant.
- The use of `ASM_CASES_TAC` suggests a case split based on an assumption in the context. This might need to be translated into explicit case distinctions in other systems.


---

## REAL_INTEGRABLE_SIN_AND_COS

### Name of formal statement
REAL_INTEGRABLE_SIN_AND_COS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_INTEGRABLE_SIN_AND_COS = prove
 (`!m n a b.
      (\x. cos(&m * x) * cos(&n * x)) real_integrable_on real_interval[a,b] /\
      (\x. cos(&m * x) * sin(&n * x)) real_integrable_on real_interval[a,b] /\
      (\x. sin(&m * x) * cos(&n * x)) real_integrable_on real_interval[a,b] /\
      (\x. sin(&m * x) * sin(&n * x)) real_integrable_on real_interval[a,b]`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN
  REAL_INTEGRABLE_ON_INTERVAL_TAC);;
```
### Informal statement
For all real numbers `m`, `n`, `a`, and `b`, the following functions are Riemann integrable on the closed real interval `[a, b]`:
1. The function mapping `x` to `cos(m * x) * cos(n * x)`.
2. The function mapping `x` to `cos(m * x) * sin(n * x)`.
3. The function mapping `x` to `sin(m * x) * cos(n * x)`.
4. The function mapping `x` to `sin(m * x) * sin(n * x)`.

### Informal sketch
The proof proceeds by:
- Universally generalizing over `m`, `n`, `a`, and `b`.
- Splitting the goal into four subgoals (using `REPEAT CONJ_TAC`), corresponding to the integrability of the four functions.
- Applying `REAL_INTEGRABLE_ON_INTERVAL_TAC` to each subgoal. This tactic likely relies on the fact that continuous functions are Riemann integrable on closed intervals, and the given functions are continuous since they are products and compositions of continuous sine and cosine functions, and scalar multiplication.

### Mathematical insight
This theorem establishes the Riemann integrability of products of sine and cosine functions, scaled by constants, over closed intervals.  This is a foundational result for computing Fourier series and related integrals.  It is essential to verify that these functions satisfy the prerequisites for integration before attempting to calculate their definite integrals. The `REAL_INTEGRABLE_ON_INTERVAL_TAC` likely encapsulates some already proven theorems regarding continuity and integrability.

### Dependencies
- `real_integrable_on`
- `real_interval`
- `REAL_INTEGRABLE_ON_INTERVAL_TAC`


---

## trigonometric_set_def

### Name of formal statement
trigonometric_set_def

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let trigonometric_set_def = new_definition
 `trigonometric_set n =
    if n = 0 then \x. &1 / sqrt(&2 * pi)
    else if ODD n then \x. sin(&(n DIV 2 + 1) * x) / sqrt(pi)
    else \x. cos(&(n DIV 2) * x) / sqrt(pi)`;;
```
### Informal statement
The `trigonometric_set` is defined as a function that takes a natural number `n` and returns a function mapping a real number `x` to a real number. If `n` is zero, it returns the function that maps `x` to `1 / sqrt(2 * pi)`. Otherwise, if `n` is odd, it returns the function that maps `x` to `sin((n DIV 2 + 1) * x) / sqrt(pi)`. Otherwise, if `n` is even and non-zero, it returns the function that maps `x` to `cos((n DIV 2) * x) / sqrt(pi)`.

### Informal sketch
The definition introduces the trigonometric functions used to construct an orthonormal basis for functions on an interval.

- The definition uses primitive recursion (if-then-else construct) to partition cases based on `n`.
- When `n=0`, the constant function `1/sqrt(2*pi)` is returned. This will be the constant term in the Fourier series.
- When `n` is odd, we define sine functions. `sin(&(n DIV 2 + 1) * x) / sqrt(pi)` where `n DIV 2 + 1` yields the harmonic.
- When `n` is even and non-zero, we define cosine functions. `cos(&(n DIV 2) * x) / sqrt(pi)` where `n DIV 2` yields the harmonic.
- The factors of `sqrt(pi)` and `sqrt(2*pi)` guarantee that the family is orthonormal.

### Mathematical insight
The `trigonometric_set` definition introduces a set of trigonometric functions (sines and cosines) that form an orthonormal basis when considered alongside an appropriate inner product. This basis is fundamental in Fourier analysis for representing periodic functions as a sum of sines and cosines. The normalization factors `1/sqrt(2*pi)` and `1/sqrt(pi)` are chosen to ensure that the functions have unit norm.

### Dependencies
None

### Porting notes (optional)
- The `ODD` and `DIV` operators may need to be defined or imported from standard libraries, depending on the target proof assistant.
- Ensure proper handling of real numbers and square roots.
- Pay close attention to type coercions between natural numbers and real numbers (using `&`).


---

## trigonometric_set

### Name of formal statement
trigonometric_set

### Type of the formal statement
theorem

### Formal Content
```ocaml
let trigonometric_set = prove
 (`trigonometric_set 0 = (\x. cos(&0 * x) / sqrt(&2 * pi)) /\
   trigonometric_set (2 * n + 1) = (\x. sin(&(n + 1) * x) / sqrt(pi)) /\
   trigonometric_set (2 * n + 2) = (\x. cos(&(n + 1) * x) / sqrt(pi))`,
  REWRITE_TAC[trigonometric_set_def; EVEN_ADD; EVEN_MULT; ARITH; ADD_EQ_0;
              GSYM NOT_EVEN] THEN
  REWRITE_TAC[ARITH_RULE `(2 * n + 1) DIV 2 = n`] THEN
  REWRITE_TAC[ARITH_RULE `(2 * n + 2) DIV 2 = n + 1`] THEN
  REWRITE_TAC[REAL_MUL_LZERO; COS_0]);;
```

### Informal statement
The theorem states that the function `trigonometric_set`, when applied to 0, equals the function that maps `x` to `cos(0 * x) / sqrt(2 * pi)`. Also, when applied to `2 * n + 1`, it equals the function mapping `x` to `sin((n + 1) * x) / sqrt(pi)`, and when applied to `2 * n + 2`, it equals the function mapping `x` to `cos((n + 1) * x) / sqrt(pi)`.

### Informal sketch
The proof involves:
- Rewriting the goal using the definition of `trigonometric_set_def`, simplifying even numbers, arithmetic, and the property `0 + 0 = 0`.
- Simplifying `not_even` numbers. Apply arithmetic simplification rules to simplify the expressions `(2 * n + 1) DIV 2` and `(2 * n + 2) DIV 2`.
- Finally, simplify terms using `REAL_MUL_LZERO`  and `COS_0`.

### Mathematical insight
This theorem defines the values of the `trigonometric_set` function for arguments of the form 0, `2 * n + 1`, and `2 * n + 2`. It essentially constructs a set of trigonometric functions (sine and cosine) that are normalized. These functions are important in Fourier analysis and orthonormal bases.

### Dependencies
- Definitions: `trigonometric_set_def`
- Theorems: `EVEN_ADD`, `EVEN_MULT`, `ARITH`, `ADD_EQ_0`, `NOT_EVEN`, `REAL_MUL_LZERO`, `COS_0`
- Arithmetic rules: `ARITH_RULE `(2 * n + 1) DIV 2 = n``, `ARITH_RULE `(2 * n + 2) DIV 2 = n + 1``


---

## TRIGONOMETRIC_SET_EVEN

### Name of formal statement
TRIGONOMETRIC_SET_EVEN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TRIGONOMETRIC_SET_EVEN = prove
 (`!k. trigonometric_set(2 * k) =
        if k = 0 then \x. &1 / sqrt(&2 * pi)
        else \x. cos(&k * x) / sqrt pi`,
  INDUCT_TAC THEN
  REWRITE_TAC[ARITH; trigonometric_set; REAL_MUL_LZERO; COS_0] THEN
  REWRITE_TAC[NOT_SUC; ARITH_RULE `2 * SUC k = 2 * k + 2`] THEN
  REWRITE_TAC[trigonometric_set; GSYM ADD1]);;
```
### Informal statement
For all natural numbers `k`, `trigonometric_set(2 * k)` is equal to a function that maps `x` to `1 / sqrt(2 * pi)` if `k` is `0`, and to `cos(k * x) / sqrt pi` otherwise.

### Informal sketch
The proof proceeds by induction on `k`.

- **Base Case (k = 0):** The left-hand side is `trigonometric_set(2 * 0)` which simplifies to `trigonometric_set(0)`. The right-hand side is `cos(0 * x) / sqrt pi`, which simplifies to `1 / sqrt pi`. Using the definition of `trigonometric_set` and `cos(0)`, the base case is proven, reducing `cos(0)` to `1`.
- **Inductive Step:** Assume the statement holds for `k`. We need to prove it for `SUC k`. Thus, we want to show `trigonometric_set(2 * SUC k) = cos(SUC k * x) / sqrt pi`. We rewrite `2 * SUC k` as `2 * k + 2`. By utilizing the definition of `trigonometric_set`, we reduce the expression of `trigonometric_set(2 * k + 2)` to `cos((k + 1) * x) / sqrt pi`. This completes the inductive step.

### Mathematical insight
This theorem defines the even-indexed elements of the `trigonometric_set`. These are shown to correspond to cosine functions with appropriate scaling. This is a key step in defining the orthonormal basis used in Fourier analysis.

### Dependencies
- `ARITH`
- `trigonometric_set`
- `REAL_MUL_LZERO`
- `COS_0`
- `NOT_SUC`
- `ARITH_RULE`
- `ADD1`


---

## ODD_EVEN_INDUCT_LEMMA

### Name of formal statement
ODD_EVEN_INDUCT_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ODD_EVEN_INDUCT_LEMMA = prove
 (`(!n:num. P 0) /\ (!n. P(2 * n + 1)) /\ (!n. P(2 * n + 2)) ==> !n. P n`,
  REWRITE_TAC[FORALL_SIMP] THEN STRIP_TAC THEN
  MATCH_MP_TAC num_INDUCTION THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN
  MP_TAC(ISPEC `n:num` EVEN_OR_ODD) THEN
  REWRITE_TAC[EVEN_EXISTS; ODD_EXISTS] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE
    `SUC(2 * n) = 2 * n + 1 /\ SUC(2 * n + 1) = 2 * n + 2`]);;
```

### Informal statement
For any property `P` on natural numbers, if `P` holds for 0, and for all `n`, `P` holds for `2 * n + 1` and `P` holds for `2 * n + 2`, then `P` holds for all natural numbers `n`.

### Informal sketch
The proof proceeds by induction on the natural numbers.
- First, strip the forall quantifier on `n:num` from the goal and apply mathematical induction on `n` using `num_INDUCTION`.
- This results in two subgoals:
  - Base case: `P 0` - This is immediate from the assumption.
  - Inductive step: `P n ==> P (SUC n)`.
- To prove the inductive step `P n ==> P (SUC n)`, we first discharge the assumption `P n` with a universal quantifier.
- Then, we use the theorem `EVEN_OR_ODD` which states that every number is either even or odd. Specifically, instantiate `EVEN_OR_ODD` with `n`.
- This produces two cases:
  - `n` is even, meaning there exists an `m` such that `n = 2 * m`. Then `SUC n = SUC (2 * m) = 2 * m + 1`. The goal becomes `P (2 * m + 1)` which is in the assumption.
  - `n` is odd, meaning there exists an `m` such that `n = 2 * m + 1`. Then `SUC n = SUC (2 * m + 1) = 2 * m + 2`. The goal becomes `P (2 * m + 2)` which is in the assumption.
- The goal is then solved using rewriting with the arithmetic simplification rule `SUC(2 * n) = 2 * n + 1 /\ SUC(2 * n + 1) = 2 * n + 2`.

### Mathematical insight
This theorem provides an alternative induction principle for natural numbers. Instead of showing `P(n)` implies `P(n+1)`, it is sufficient to show `P(0)`, and that `P(2n+1)` and `P(2n+2)` both hold. The usefulness of this induction scheme comes when `P` is more naturally defined in terms of the odd and even cases, and one might want to do simultaneous induction on the even and odd natural numbers.

### Dependencies
- `num_INDUCTION`
- `EVEN_OR_ODD`
- `EVEN_EXISTS`
- `ODD_EXISTS`
- `ARITH_RULE`
- `FORALL_SIMP`

### Porting notes (optional)
- A similar induction scheme exists in Coq under the name `even_odd_ind`.
- Most proof assistants will have similar theorems regarding even and odd numbers and induction principles.


---

## ORTHONORMAL_SYSTEM_TRIGONOMETRIC_SET

### Name of formal statement
ORTHONORMAL_SYSTEM_TRIGONOMETRIC_SET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ORTHONORMAL_SYSTEM_TRIGONOMETRIC_SET = prove
 (`orthonormal_system (real_interval[--pi,pi]) trigonometric_set`,
  REWRITE_TAC[orthonormal_system; l2product] THEN
  MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `m:num` THEN
  MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[trigonometric_set] THEN
  REWRITE_TAC[REAL_ARITH `a / k * b / l:real = (inv(k) * inv(l)) * a * b`] THEN
  SIMP_TAC[REAL_INTEGRAL_LMUL; REAL_INTEGRABLE_SIN_AND_COS] THEN
  REWRITE_TAC[REAL_INTEGRAL_SIN_AND_COS] THEN
  REWRITE_TAC[ADD_EQ_0; ARITH_EQ; REAL_MUL_RZERO] THEN
  ASM_CASES_TAC `m:num = n` THEN
  TRY (COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  TRY (MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC) THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 = a + b <=> a = 0 /\ b = 0`;
                  EQ_ADD_RCANCEL; EQ_MULT_LCANCEL] THEN
  REWRITE_TAC[ARITH; REAL_MUL_RZERO] THEN
  REWRITE_TAC[GSYM REAL_INV_MUL; GSYM REAL_POW_2] THEN
  SIMP_TAC[SQRT_POW_2; REAL_LE_MUL; REAL_POS; PI_POS_LE] THEN
  MATCH_MP_TAC REAL_MUL_LINV THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;
```

### Informal statement
The trigonometric set is an orthonormal system on the real interval from -π to π.

### Informal sketch
The proof demonstrates that the `trigonometric_set` is an orthonormal system on the interval `real_interval[--pi,pi]`. This is achieved by proving that the L2 inner product of any two distinct elements in `trigonometric_set` over the interval `real_interval[--pi,pi]` is zero, and the L2 inner product of each element with itself is 1.
- The definition of `orthonormal_system` and `l2product` are expanded using `REWRITE_TAC`.
- Induction is used to decompose the trigonometric set into its constituent sine and cosine functions using `ODD_EVEN_INDUCT_LEMMA` and `REPEAT CONJ_TAC`.
- Two natural number variables, `m` and `n`, are introduced representing the frequencies of the trigonometric functions, where `m` is the index of the cosine term and `n` is the index of a sine term.
- The definition of `trigonometric_set` is expanded.
- Basic real arithmetic simplifications are applied using `REAL_ARITH`, `REAL_INTEGRAL_LMUL`, and `REAL_INTEGRABLE_SIN_AND_COS`.
- The definite integrals of the sine and cosine functions are computed using `REAL_INTEGRAL_SIN_AND_COS` and simplified using `ADD_EQ_0`, `ARITH_EQ`, and `REAL_MUL_RZERO`.
- The proof proceeds by case distinction of `m:num = n`:
  - If `m` is equal to `n`, further conditional cases are considered based on trigonometric identities and simplified with arithmetic rules.
  - If `m` is not equal to `n`, the goal is simplified via arithmetic and real number properties such as `REAL_INV_MUL`, `REAL_POW_2`, `SQRT_POW_2`, `REAL_LE_MUL`, `REAL_POS`, and `PI_POS_LE`.
- Finally, algebraic manipulation and cancellation steps utilizing `REAL_MUL_LINV` and `PI_POS` lead to the desired result of 1, completing the proof that the trigonometric set forms an orthonormal system.

### Mathematical insight
This theorem is a cornerstone result in Fourier analysis. It formalizes the notion that the trigonometric functions (sines and cosines of integer multiples of a fundamental frequency) are orthogonal over the interval [-π, π]. This orthogonality is crucial for decomposing functions into a sum of trigonometric functions – the basis for Fourier series and related transforms.

### Dependencies
- Definitions:
  - `orthonormal_system`
  - `l2product`
  - `trigonometric_set`
- Theorems/Lemmas:
  - `ODD_EVEN_INDUCT_LEMMA`
  - `REAL_ARITH`
  - `REAL_INTEGRAL_LMUL`
  - `REAL_INTEGRABLE_SIN_AND_COS`
  - `REAL_INTEGRAL_SIN_AND_COS`
  - `ADD_EQ_0`, `ARITH_EQ`, `REAL_MUL_RZERO`
  - `ARITH_RULE 0 = a + b <=> a = 0 /\ b = 0`
  - `EQ_ADD_RCANCEL`, `EQ_MULT_LCANCEL`
  - `ARITH`
  - `GSYM REAL_INV_MUL`, `GSYM REAL_POW_2`
  - `SQRT_POW_2`, `REAL_LE_MUL`, `REAL_POS`, `PI_POS_LE`
  - `REAL_MUL_LINV`
  - `PI_POS`

### Porting notes (optional)
- The theorem relies heavily on real analysis and integral calculus. Ensure the target proof assistant has adequate support for these.
- The decomposition of `trigonometric_set` and the handling of indices `m` and `n` need to be reproduced carefully.
- Pay attention to how the target system handles real number arithmetic and simplification.


---

## SQUARE_INTEGRABLE_TRIGONOMETRIC_SET

### Name of formal statement
SQUARE_INTEGRABLE_TRIGONOMETRIC_SET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SQUARE_INTEGRABLE_TRIGONOMETRIC_SET = prove
 (`!i. (trigonometric_set i) square_integrable_on real_interval[--pi,pi]`,
  MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
  REWRITE_TAC[trigonometric_set] THEN
  REWRITE_TAC[real_div] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE THEN
  MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
  REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
  GEN_TAC THEN DISCH_TAC THEN REAL_DIFFERENTIABLE_TAC);;
```
### Informal statement
For all `i`, the `trigonometric_set` `i` is square integrable on the real interval `[--pi,pi]`.

### Informal sketch
The proof proceeds by induction using `ODD_EVEN_INDUCT_LEMMA`.
- The base cases and inductive steps involve showing square integrability of trigonometric functions like sine and cosine.
- The tactic `REWRITE_TAC[trigonometric_set]` expands the definition of `trigonometric_set`.
- The `real_div` is then rewritten.
- The goal is stripped to expose the quantifiers and assumptions.
- `REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE` is applied to reduce the problem to showing that the trigonometric functions are continuous.
- `REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON` is then applied to reduce the problem to showing that the trigonometric functions are differentiable.
- `REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE` is used to show that the functions are differentiable.
- Finally, the goal is discharged using `GEN_TAC`, `DISCH_TAC` and `REAL_DIFFERENTIABLE_TAC`.

### Mathematical insight
This theorem establishes that the functions in the `trigonometric_set` are square integrable over the interval `[--pi, pi]`. This property is essential in Fourier analysis, specifically when demonstrating the convergence and completeness of Fourier series. Square integrability ensures that the integrals required to compute Fourier coefficients exist and are well-defined.

### Dependencies
* Theorems:
    * `ODD_EVEN_INDUCT_LEMMA`
    * `REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE`
    * `REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON`
    * `REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE`
* Definitions:
    * `trigonometric_set`
    * `square_integrable_on`
    * `real_interval`
    * `real_div`


---

## WEIERSTRASS_TRIG_POLYNOMIAL

### Name of formal statement
WEIERSTRASS_TRIG_POLYNOMIAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WEIERSTRASS_TRIG_POLYNOMIAL = prove
 (`!f e. f real_continuous_on real_interval[--pi,pi] /\
         f(--pi) = f pi /\ &0 < e
         ==> ?n a b.
                !x. x IN real_interval[--pi,pi]
                    ==> abs(f x - sum(0..n) (\k. a k * sin(&k * x) +
                                                 b k * cos(&k * x))) < e`,
  let lemma1 = prove
   (`!f. f real_continuous_on (:real) /\ (!x. f(x + &2 * pi) = f x)
         ==> !z. norm z = &1
                 ==> (f o Im o clog) real_continuous
                     at z within {w | norm w = &1}`,
    REPEAT STRIP_TAC THEN
    DISJ_CASES_TAC(REAL_ARITH `&0 <= Re z \/ Re z < &0`) THENL
     [ALL_TAC;
      REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS] THEN
      MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN THEN
      EXISTS_TAC `Cx o f o (\x. x + pi) o Im o clog o (--)` THEN
      EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01; IN_ELIM_THM] THEN
      CONJ_TAC THENL
       [X_GEN_TAC `w:complex` THEN ASM_CASES_TAC `w = Cx(&0)` THEN
        ASM_REWRITE_TAC[COMPLEX_NORM_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN
        STRIP_TAC THEN ASM_SIMP_TAC[CLOG_NEG; o_THM] THEN
        COND_CASES_TAC THEN
        ASM_REWRITE_TAC[IM_ADD; IM_SUB; IM_MUL_II; RE_CX; REAL_SUB_ADD] THEN
        ASM_REWRITE_TAC[REAL_ARITH `(x + pi) + pi = x + &2 * pi`];
        REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC CONTINUOUS_WITHIN_COMPOSE THEN
        CONJ_TAC THENL
         [GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN CONTINUOUS_TAC;
          REWRITE_TAC[GSYM o_ASSOC; GSYM REAL_CONTINUOUS_CONTINUOUS]]]] THEN
    REWRITE_TAC[o_ASSOC] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_WITHIN_COMPOSE THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC CONTINUOUS_WITHIN_CLOG THEN
       REWRITE_TAC[GSYM real] THEN DISCH_TAC THEN
       UNDISCH_TAC `norm(z:complex) = &1` THEN
       ASM_SIMP_TAC[REAL_NORM; RE_NEG; REAL_NEG_GT0] THEN
       ASM_REAL_ARITH_TAC;
       ALL_TAC]) THEN
    MATCH_MP_TAC REAL_CONTINUOUS_WITHIN_COMPOSE THEN
    REWRITE_TAC[REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN] THEN
    TRY(MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_COMPOSE THEN
        SIMP_TAC[REAL_CONTINUOUS_ADD; REAL_CONTINUOUS_CONST;
                 REAL_CONTINUOUS_WITHIN_ID]) THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]) THEN
    SIMP_TAC[IN_UNIV; WITHINREAL_UNIV]) in
  let lemma2 = prove
   (`!f. f real_continuous_on real_interval[--pi,pi] /\ f(--pi) = f pi
         ==> !z. norm z = &1
                 ==> (f o Im o clog) real_continuous
                     at z within {w | norm w = &1}`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL
     [`f:real->real`; `--pi`; `pi`] REAL_TIETZE_PERIODIC_INTERVAL) THEN
    ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real->real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `g:real->real` lemma1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
    ASM_REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS] THEN
    MATCH_MP_TAC(REWRITE_RULE
     [TAUT `a /\ b /\ c /\ d ==> e <=> a /\ b /\ c ==> d ==> e`]
      CONTINUOUS_TRANSFORM_WITHIN) THEN
    EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LT_01] THEN
    X_GEN_TAC `w:complex` THEN ASM_CASES_TAC `w = Cx(&0)` THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN
    STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[IN_REAL_INTERVAL; CLOG_WORKS; REAL_LT_IMP_LE]) in
  REPEAT STRIP_TAC THEN
  (CHOOSE_THEN MP_TAC o prove_inductive_relations_exist)
   `(!c. poly2 (\x. c)) /\
    (!p q. poly2 p /\ poly2 q ==> poly2 (\x. p x + q x)) /\
    (!p q. poly2 p /\ poly2 q ==> poly2 (\x. p x * q x)) /\
    poly2 Re /\ poly2 Im` THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (ASSUME_TAC o CONJUNCT1)) THEN
  MP_TAC(ISPECL [`poly2:(complex->real)->bool`; `{z:complex | norm z = &1}`]
        STONE_WEIERSTRASS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_CLOSED_IMP_COMPACT THEN CONJ_TAC THENL
       [REWRITE_TAC[bounded; IN_ELIM_THM] THEN MESON_TAC[REAL_LE_REFL];
        ONCE_REWRITE_TAC[SET_RULE `{x | p x} = {x | x IN UNIV /\ p x}`] THEN
        REWRITE_TAC[GSYM LIFT_EQ] THEN
        MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_CONSTANT THEN
        REWRITE_TAC[CONTINUOUS_ON_LIFT_NORM; GSYM o_DEF; CLOSED_UNIV]];
      MATCH_MP_TAC(MESON[]
       `(!x f. P f ==> R f x) ==> (!f. P f ==> !x. Q x ==> R f x)`) THEN
      GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[REAL_CONTINUOUS_ADD; REAL_CONTINUOUS_MUL] THEN
      REWRITE_TAC[REAL_CONTINUOUS_CONST;
                  REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN];
      MAP_EVERY X_GEN_TAC [`w:complex`; `z:complex`] THEN
      REWRITE_TAC[IN_ELIM_THM; COMPLEX_EQ; DE_MORGAN_THM] THEN STRIP_TAC THENL
       [EXISTS_TAC `Re` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `Im` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`(f:real->real) o Im o clog`; `e:real`]) THEN
  ASM_SIMP_TAC[IN_ELIM_THM; lemma2] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:complex->real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `trigpoly =
     \f. ?n a b.
         f = \x. sum(0..n) (\k. a k * sin(&k * x) +  b k * cos(&k * x))` THEN
  SUBGOAL_THEN `!c:real. trigpoly(\x:real. c)` ASSUME_TAC THENL
   [X_GEN_TAC `c:real` THEN EXPAND_TAC "trigpoly" THEN REWRITE_TAC[] THEN
    EXISTS_TAC `0` THEN
    REWRITE_TAC[SUM_SING_NUMSEG; REAL_MUL_LZERO; SIN_0; COS_0] THEN
    MAP_EVERY EXISTS_TAC [`(\n. &0):num->real`; `(\n. c):num->real`] THEN
    REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f g:real->real. trigpoly f /\ trigpoly g ==> trigpoly(\x. f x + g x)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "trigpoly" THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`n1:num`; `a1:num->real`; `b1:num->real`;
      `n2:num`; `a2:num->real`; `b2:num->real`] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
    MAP_EVERY EXISTS_TAC
     [`MAX n1 n2`;
      `(\n. (if n <= n1 then a1 n else &0) +
             (if n <= n2 then a2 n else &0)):num->real`;
      `(\n. (if n <= n1 then b1 n else &0) +
            (if n <= n2 then b2 n else &0)):num->real`] THEN
    REWRITE_TAC[SUM_ADD_NUMSEG; FUN_EQ_THM; REAL_ADD_RDISTRIB] THEN
    GEN_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `a:real = e /\ b = g /\ c = f /\ d = h
      ==> (a + b) + (c + d) = (e + f) + (g + h)`) THEN
    REPEAT CONJ_TAC THEN
    REWRITE_TAC[COND_RATOR; COND_RAND; REAL_MUL_LZERO] THEN
    REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
    MATCH_MP_TAC(MESON[] `s = t ==> sum s f = sum t f`) THEN
    REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_ELIM_THM] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f s:num->bool. FINITE s /\ (!i. i IN s ==> trigpoly(f i))
                    ==> trigpoly(\x:real. sum s (\i. f i x))`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC[SUM_CLAUSES; IN_INSERT; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f:real->real c. trigpoly f ==> trigpoly (\x. c * f x)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "trigpoly" THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `a:num->real`; `b:num->real`] THEN
    DISCH_THEN SUBST1_TAC THEN MAP_EVERY EXISTS_TAC
     [`n:num`; `\i. c * (a:num->real) i`; `\i. c * (b:num->real) i`] THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB; GSYM SUM_LMUL; GSYM REAL_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. trigpoly(\x. sin(&i * x))` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN EXPAND_TAC "trigpoly" THEN MAP_EVERY EXISTS_TAC
     [`k:num`; `\i:num. if i = k then &1 else &0`; `\i:num. &0`] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID; COND_RAND; COND_RATOR] THEN
    SIMP_TAC[SUM_DELTA; REAL_MUL_LID; IN_NUMSEG; LE_0; LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. trigpoly(\x. cos(&i * x))` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN EXPAND_TAC "trigpoly" THEN MAP_EVERY EXISTS_TAC
     [`k:num`; `\i:num. &0`; `\i:num. if i = k then &1 else &0`] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID; COND_RAND; COND_RATOR] THEN
    SIMP_TAC[SUM_DELTA; REAL_MUL_LID; IN_NUMSEG; LE_0; LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. trigpoly(\x. sin(&i * x) * sin(&j * x)) /\
          trigpoly(\x. sin(&i * x) * cos(&j * x)) /\
          trigpoly(\x. cos(&i * x) * sin(&j * x)) /\
          trigpoly(\x. cos(&i * x) * cos(&j * x))`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_MP_TAC WLOG_LE THEN
    CONJ_TAC THENL [REWRITE_TAC[CONJ_ACI; REAL_MUL_AC]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_SIN_SIN; REAL_MUL_SIN_COS; REAL_MUL_COS_SIN;
                REAL_MUL_COS_COS] THEN
    REWRITE_TAC[GSYM REAL_ADD_RDISTRIB; GSYM REAL_SUB_RDISTRIB] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[REAL_ARITH `x / &2 = inv(&2) * x`;
                REAL_ARITH `x - y:real = x + --(&1) * y`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f g:real->real. trigpoly f /\ trigpoly g ==> trigpoly(\x. f x * g x)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM
         th]) THEN
    REWRITE_TAC[] THEN
    DISCH_THEN(REPEAT_TCL STRIP_THM_THEN SUBST1_TAC) THEN
    REWRITE_TAC[REAL_MUL_SUM_NUMSEG] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH
    `(ai * si + bi * ci) * (aj * sj + bj * cj):real =
     ((ai * aj) * (si * sj) + (bi * bj) * (ci * cj)) +
     ((ai * bj) * (si * cj) + (aj * bi) * (ci * sj))`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f:complex->real. poly2 f ==> trigpoly(\x.  f(cexp(ii * Cx x)))`
  (MP_TAC o SPEC `g:complex->real`) THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[RE_CEXP; IM_CEXP; RE_MUL_II; IM_CX; IM_MUL_II; RE_CX] THEN
    ONCE_REWRITE_TAC[MESON[REAL_MUL_LID]
     `cos x = cos(&1 * x) /\ sin x = sin(&1 * x)`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "trigpoly" THEN
  MAP_EVERY (fun t -> MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC t)
   [`n:num`; `a:num->real`; `b:num->real`] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `cexp(ii * Cx r)`) THEN
  REWRITE_TAC[NORM_CEXP_II] THEN MATCH_MP_TAC(REAL_ARITH
   `x = x' ==> abs(x - y) < e ==> abs(x' - y) < e`) THEN
  REWRITE_TAC[o_DEF] THEN
  ASM_CASES_TAC `r = --pi` THENL
   [UNDISCH_THEN `r = --pi` SUBST_ALL_TAC THEN
    REWRITE_TAC[CEXP_EULER; GSYM CX_COS; GSYM CX_SIN] THEN
    REWRITE_TAC[COS_NEG; SIN_NEG; SIN_PI; COS_PI] THEN
    REWRITE_TAC[CX_NEG; COMPLEX_MUL_RZERO; COMPLEX_NEG_0] THEN
    ASM_REWRITE_TAC[CLOG_NEG_1; COMPLEX_ADD_RID; IM_MUL_II; RE_CX];
    ASM_SIMP_TAC[CLOG_CEXP; IM_MUL_II; RE_CX; REAL_LT_LE]]);;
```

### Informal statement
For every real-valued function `f` that is continuous on the closed real interval from `-pi` to `pi` and satisfies `f(-pi) = f(pi)`, and for every real number `e` greater than 0, there exist a natural number `n` and real-valued functions `a` and `b` from natural numbers to real numbers, such that for all `x` in the closed real interval from `-pi` to `pi`, the absolute value of the difference between `f(x)` and the sum from 0 to `n` of `a(k) * sin(k * x) + b(k) * cos(k * x)` is less than `e`.

### Informal sketch
The proof establishes the Weierstrass approximation theorem for trigonometric polynomials.
- First, two lemmas are proven.
  - `lemma1` states that given a real-valued function `f` continuous on the real line and periodic with a period of `2 * pi`, then for any complex number `z` with norm 1, the function `f o Im o clog` is real continuous at `z` within the set of complex numbers `w` with norm 1. This is shown by splitting the proof into two cases: `Re z >= 0` and `Re z < 0`.
  - `lemma2` extends `lemma1`. It shows that if `f` is real continuous on the closed interval `[--pi, pi]` and `f(--pi) = f pi`, then for any complex number `z` with norm 1, `(f o Im o clog)` is real continuous at `z` within the set `{w | norm w = &1}`. This lemma uses `REAL_TIETZE_PERIODIC_INTERVAL` and `lemma1`.
- The main proof proceeds by using the Stone-Weierstrass theorem.
  - It defines a predicate `poly2` to identify functions that are polynomials of two variables.
  - It establishes that constant functions are in `poly2`, the sum and product of functions in `poly2` are in `poly2`, and the real and imaginary part functions are in `poly2`. These establish closure properties needed for Stone-Weierstrass.
  - It then applies the Stone-Weierstrass theorem to the function `f o Im o clog` (where `f` is the given function) on the set `{z:complex | norm z = &1}`.
  - The conditions for Stone-Weierstrass (compactness, continuity, and separation) are verified.
  - A `trigpoly` abbreviation is introduced to represent trigonometric polynomials.
  - Several subgoals are then proven, showing closure properties: constant functions are trigonometric polynomials, sums of trig polynomials are trig polynomials, scalar multiples are trig polynomials. Then it is shown that `sin(k*x)` and `cos(k*x)` are trig polynomials. Products of these functions are also shown to be trig polynomials.
  - It is then shown that `poly2 f` implies that `trigpoly (\x. f(cexp(ii * Cx x)))`.
  - Finally, the theorem is proven by instantiating Stone-Weierstrass
  - Finally the main goal is proven.

### Mathematical insight
This theorem provides a cornerstone for approximating periodic continuous functions with trigonometric polynomials. It's a specific instance of the Stone-Weierstrass theorem when applied to the circle, bridging continuous functions with simpler, computable trigonometric polynomials. The theorem is crucial in Fourier analysis, signal processing, and numerical analysis.

### Dependencies
- `REAL_CONTINUOUS_CONTINUOUS`
- `CONTINUOUS_TRANSFORM_WITHIN`
- `REAL_LT_01`
- `COMPLEX_NORM_0`
- `REAL_OF_NUM_EQ`
- `ARITH_EQ`
- `CLOG_NEG`
- `o_THM`
- `IM_ADD`
- `IM_SUB`
- `IM_MUL_II`
- `RE_CX`
- `REAL_SUB_ADD`
- `REAL_ARITH`
- `o_ASSOC`
- `CONTINUOUS_WITHIN_COMPOSE`
- `ETA_AX`
- `CONTINUOUS_TAC`
- `REAL_CONTINUOUS_CONTINUOUS_WITHIN_COMPOSE`
- `CONTINUOUS_WITHIN_CLOG`
- `REAL_NORM`
- `RE_NEG`
- `REAL_NEG_GT0`
- `REAL_CONTINUOUS_WITHIN_COMPOSE`
- `REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN`
- `REAL_CONTINUOUS_ADD`
- `REAL_CONTINUOUS_CONST`
- `REAL_CONTINUOUS_WITHIN_ID`
- `REAL_CONTINUOUS_ATREAL_WITHINREAL`
- `REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN`
- `IN_UNIV`
- `WITHINREAL_UNIV`
- `REAL_TIETZE_PERIODIC_INTERVAL`
- `REAL_CONTINUOUS_CONTINUOUS`
- `IN_ELIM_THM`
- `COMPLEX_EQ`
- `DE_MORGAN_THM`
- `SUM_SING_NUMSEG`
- `REAL_MUL_LZERO`
- `SIN_0`
- `COS_0`
- `FUN_EQ_THM`

**Rules:**
- `BOUNDED_CLOSED_IMP_COMPACT`
- `STONE_WEIERSTRASS`
- `REAL_MUL_SIN_SIN`
- `REAL_MUL_SIN_COS`
- `REAL_MUL_COS_SIN`
- `REAL_MUL_COS_COS`

### Porting notes (optional)
- The proof relies heavily on rewriting and simplification, which might need adjustments depending on the automation capabilities of the target proof assistant.
- The use of `ABBREV_TAC` for defining `trigpoly` can be easily replaced with a standard definition in other proof assistants.
- The `prove_inductive_relations_exist` tactic might require manual construction depending the target's automation for inductive relations.
- It may be necessary to manually decompose tactic applications using `CONJUNCTS_THEN` into separate steps in proof assistants lacking direct equivalents.



---

## REAL_INTEGRAL_TWEAK_ENDS

### Name of formal statement
REAL_INTEGRAL_TWEAK_ENDS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_INTEGRAL_TWEAK_ENDS = prove
 (`!a b d e.
        a < b /\ &0 < e
        ==> ?f. f real_continuous_on real_interval[a,b] /\
                f(a) = d /\ f(b) = &0 /\
                l2norm (real_interval[a,b]) f < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. (\x. if x <= a + inv(&n + &1)
             then ((&n + &1) * d) * ((a + inv(&n + &1)) - x) else &0)
        real_continuous_on real_interval[a,b]`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN `a < a + inv(&n + &1)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LT_ADDR; REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `a + inv(&n + &1) <= b` THENL
     [SUBGOAL_THEN
       `real_interval[a,b] = real_interval[a,a + inv(&n + &1)] UNION
                             real_interval[a + inv(&n + &1),b]`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_UNION; IN_REAL_INTERVAL] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_CASES THEN
      REWRITE_TAC[REAL_CLOSED_REAL_INTERVAL; REAL_CONTINUOUS_ON_CONST] THEN
      CONJ_TAC THENL
       [SIMP_TAC[real_div; REAL_CONTINUOUS_ON_MUL; REAL_CONTINUOUS_ON_CONST;
                 REAL_CONTINUOUS_ON_SUB; REAL_CONTINUOUS_ON_ID];
        X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
        ASM_CASES_TAC `x:real = a + inv(&n + &1)` THENL
         [ASM_REWRITE_TAC[real_div; REAL_SUB_REFL; REAL_MUL_RZERO];
          ASM_REAL_ARITH_TAC]];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THEN
      EXISTS_TAC `\x. ((&n + &1) * d) * ((a + inv(&n + &1)) - x)` THEN
      SIMP_TAC[real_div; REAL_CONTINUOUS_ON_MUL; REAL_CONTINUOUS_ON_CONST;
               REAL_CONTINUOUS_ON_SUB; REAL_CONTINUOUS_ON_ID] THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC
   (ISPECL [`\n x. (if x <= a + inv(&n + &1)
                    then ((&n + &1) * d) * ((a + inv(&n + &1)) - x) else &0)
                   pow 2`;
            `\x:real. if x = a then d pow 2 else &0`;
            `\x:real. (d:real) pow 2`;
            `real_interval[a,b]`]
        REAL_DOMINATED_CONVERGENCE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      ASM_SIMP_TAC[REAL_CONTINUOUS_ON_POW];
      MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_CONST];
      MAP_EVERY X_GEN_TAC [`k:num`; `x:real`] THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_ABS_POW] THEN
      REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS; REAL_ABS_ABS] THEN
      COND_CASES_TAC THEN REWRITE_TAC[REAL_ABS_NUM; REAL_ABS_POS] THEN
      REWRITE_TAC[REAL_ARITH `(a * b) * c:real = b * a * c`] THEN
      ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
      REWRITE_TAC[REAL_ARITH `d * x <= d <=> &0 <= d * (&1 - x)`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ARITH `abs(&n + &1) = &n + &1`] THEN
      REWRITE_TAC[REAL_ARITH `&0 <= &1 - x * y <=> y * x <= &1`] THEN
      SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
      REWRITE_TAC[real_div; REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      ASM_CASES_TAC `x:real = a` THEN ASM_REWRITE_TAC[] THENL
       [ASM_REWRITE_TAC[REAL_LE_ADDR; REAL_LE_INV_EQ;
                        REAL_ARITH `&0 <= &n + &1`] THEN
        REWRITE_TAC[REAL_ADD_SUB] THEN
        SIMP_TAC[REAL_FIELD `&0 < x ==> (x * d) * inv x = d`;
                 REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
        REWRITE_TAC[REALLIM_CONST];
        MATCH_MP_TAC REALLIM_EVENTUALLY THEN
        REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
        MP_TAC(ISPEC `x - a:real` REAL_ARCH_INV) THEN
        DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
        STRIP_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
        COND_CASES_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        MATCH_MP_TAC(TAUT `F ==> p`) THEN
        SUBGOAL_THEN `inv(&n + &1) <= inv(&N)` MP_TAC THENL
         [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN
        REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT; REAL_OF_NUM_ADD] THEN
        ASM_ARITH_TAC]];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
    DISCH_THEN(MP_TAC o SPEC `(e:real) pow 2`) THEN
    ASM_SIMP_TAC[REAL_POW_LT] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "*")) THEN
    MP_TAC(ISPEC `b - a:real` REAL_ARCH_INV) THEN
    ASM_REWRITE_TAC[REAL_SUB_LT] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?n:num. N <= n /\ M <= n` STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `M + N:num` THEN ARITH_TAC; ALL_TAC] THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    EXISTS_TAC `\x. if x <= a + inv(&n + &1)
                 then ((&n + &1) * d) * ((a + inv(&n + &1)) - x) else &0` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(REAL_ARITH `&0 < &n + &1`) THEN
      SIMP_TAC[REAL_LE_ADDR; REAL_LT_INV_EQ; REAL_LT_IMP_LE] THEN
      CONV_TAC REAL_FIELD;
      SUBGOAL_THEN `inv(&n + &1) < b - a` MP_TAC THENL
        [ALL_TAC; REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&M)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      SUBGOAL_THEN `e = sqrt(e pow 2)` SUBST1_TAC THENL
       [ASM_MESON_TAC[POW_2_SQRT; REAL_LT_IMP_LE]; ALL_TAC] THEN
      REWRITE_TAC[l2norm; l2product] THEN MATCH_MP_TAC SQRT_MONO_LT THEN
      REWRITE_TAC[GSYM REAL_POW_2] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
       `abs(i - l) < e ==> &0 <= i /\ l = &0 ==> i < e`)) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_INTEGRAL_POS THEN
        ASM_SIMP_TAC[REAL_INTEGRABLE_CONTINUOUS; REAL_CONTINUOUS_ON_POW] THEN
        REWRITE_TAC[REAL_LE_POW_2];
        MP_TAC(ISPEC `real_interval[a,b]` REAL_INTEGRAL_0) THEN
        MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN
        EXISTS_TAC `{a:real}` THEN REWRITE_TAC[REAL_NEGLIGIBLE_SING] THEN
        SIMP_TAC[IN_DIFF; IN_SING]]]]);;
```

### Informal statement
For all real numbers `a`, `b`, `d`, and `e`, if `a` is less than `b` and `0` is less than `e`, then there exists a real-valued function `f` that is continuous on the real interval `[a, b]`, such that `f(a) = d`, `f(b) = &0`, and the L2 norm of `f` on the real interval `[a, b]` is less than `e`.

### Informal sketch
The proof demonstrates that given an interval `[a, b]` and a small positive real `e`, we can find a continuous function `f` on `[a, b]` that starts at `d` at `a` and goes to `0` at `b`, and whose L2 norm is less than `e`. The function `f` tapers linearly from `d` to `0` on a small interval `[a, a + 1/(n+1)]` and is `0` elsewhere on `[a, b]`. The proof involves these steps:

- Define a continuous function `f_n(x)` that is `((&n + &1) * d) * ((a + inv(&n + &1)) - x)` if `x <= a + inv(&n + &1)` and `0` otherwise. We show `f_n` is continuous on the interval `[a, b]`.
- Verify `a < a + inv(&n + &1)` using `REAL_LT_ADDR` and `REAL_LT_INV_EQ`.
- Decompose the interval `[a, b]` into `[a, a + inv(&n + &1)] UNION [a + inv(&n + &1), b]`. This allows us to apply `REAL_CONTINUOUS_ON_CASES`.
- Apply the dominated convergence theorem (`REAL_DOMINATED_CONVERGENCE`). This involves showing that the sequence of functions `f_n(x)^2` converges pointwise to a function `g(x)` and is bounded by an integrable function `h(x)`. The chosen dominating function `h(x)` is `d^2` if `x = a` and `0` otherwise.
- Establish integrability and continuity of the components using theorems such as `REAL_INTEGRABLE_CONTINUOUS`.
- Demonstrate the pointwise convergence of `f_n(x)^2` to the function which is `d^2` at `a` and `0` elsewhere. This relies on `REALLIM_CONST` and `REALLIM_EVENTUALLY`.
- Prove that the limit of the L2 norm of `f_n` is less than `e`, using the Archimedean property (`REAL_ARCH_INV`).
- Instantiate the existential quantifier to show the existence of the function with the desired properties, which is `f_n(x)`.
- Show that the instantiated function satisfies the constraints: It's continuous, starts at `d` at `a`, ends at `0` at `b` after selecting appropriately large `n` for `inv(&n + &1) < b - a` and its L2 norm is less than `e` by using `SQRT_MONO_LT` and `REAL_INTEGRAL_SPIKE`.

### Mathematical insight
The theorem provides a way to "tweak" the ends of a function while preserving its continuity and keeping its L2 norm arbitrarily small. This is useful when working with integrals, especially when applying limiting arguments where boundary conditions might be problematic. The main idea is to concentrate the non-zero part of the function near the endpoint `a` to control the integral of its square. The proof relies on the dominated convergence theorem and the Archimedean property of real numbers.

### Dependencies
- `REAL_LT_ADDR`
- `REAL_LT_INV_EQ`
- `EXTENSION`
- `IN_UNION`
- `IN_REAL_INTERVAL`
- `REAL_CLOSED_REAL_INTERVAL`
- `REAL_CONTINUOUS_ON_CONST`
- `REAL_CONTINUOUS_ON_MUL`
- `REAL_CONTINUOUS_ON_SUB`
- `REAL_CONTINUOUS_ON_ID`
- `REAL_CONTINUOUS_ON_CASES`
- `REAL_DOMINATED_CONVERGENCE`
- `REAL_INTEGRABLE_CONTINUOUS`
- `REAL_CONTINUOUS_ON_POW`
- `REAL_ABS_POW`
- `REAL_LE_SQUARE_ABS`
- `REAL_ABS_ABS`
- `REAL_ABS_NUM`
- `REAL_ABS_POS`
- `REAL_ABS_MUL`
- `REAL_LE_MUL`
- `REAL_LE_RDIV_EQ`
- `REAL_LE_ADDR`
- `REAL_LE_INV_EQ`
- `REALLIM_CONST`
- `REALLIM_EVENTUALLY`
- `EVENTUALLY_SEQUENTIALLY`
- `REAL_ARCH_INV`
- `MONO_EXISTS`
- `REAL_OF_NUM_LE`
- `REAL_OF_NUM_LT`
- `REAL_OF_NUM_ADD`
- `REALLIM_SEQUENTIALLY`
- `REAL_POW_LT`
- `REAL_SUB_LT`
- `REAL_LET_TRANS`
- `REAL_LE_INV2`
- `POW_2_SQRT`
- `REAL_LT_IMP_LE`
- `REAL_INTEGRAL_POS`
- `REAL_LE_POW_2`
- `REAL_INTEGRAL_0`
- `REAL_INTEGRAL_SPIKE`
- `REAL_NEGLIGIBLE_SING`
- `IN_DIFF`
- `IN_SING`

### Porting notes (optional)
- The proof relies heavily on `REAL_ARITH` for real number reasoning. A similar tactic or decision procedure for real arithmetic will be necessary.
- The dominated convergence theorem is crucial; make sure the target proof assistant has a corresponding version.
- The use of `ISPECL` and `EXISTS_TAC` to instantiate quantified variables is common in HOL Light. Ensure that the target proof assistant has similar mechanisms. Specifically, one needs to pay attention to type inference and matching of types when instantiating variables.


---

## SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS_ENDS

### Name of formal statement
SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS_ENDS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS_ENDS = prove
 (`!f a b e.
        f square_integrable_on real_interval[a,b] /\ a < b /\ &0 < e
        ==> ?g. g real_continuous_on real_interval[a,b] /\
                g b = g a /\
                g square_integrable_on real_interval[a,b] /\
                l2norm (real_interval[a,b]) (\x. f x - g x) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `real_interval[a,b]`; `e / &2`]
        SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS) THEN
  ASM_REWRITE_TAC[REAL_HALF; REAL_MEASURABLE_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real->real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`a:real`; `b:real`; `(g:real->real) b - g a`; `e / &2`]
        REAL_INTEGRAL_TWEAK_ENDS) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `h square_integrable_on real_interval[a,b]` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE]; ALL_TAC] THEN
  EXISTS_TAC `\x. (g:real->real) x + h x` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    REAL_ARITH_TAC;
    MATCH_MP_TAC SQUARE_INTEGRABLE_ADD THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[REAL_ARITH `f - (g + h):real = (f - g) + --h`] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) L2NORM_TRIANGLE o lhand o snd) THEN
    ASM_SIMP_TAC[SQUARE_INTEGRABLE_SUB; SQUARE_INTEGRABLE_NEG] THEN
    MATCH_MP_TAC(REAL_ARITH
     `y < e / &2 /\ z < e / &2 ==> x <= y + z ==> x < e`) THEN
    ASM_SIMP_TAC[L2NORM_NEG]]);;
```

### Informal statement
For all real-valued functions `f`, real numbers `a` and `b`, and real number `e`: if `f` is square integrable on the real interval `[a, b]`, `a` is less than `b`, and `e` is greater than 0, then there exists a real-valued function `g` such that `g` is real continuous on the real interval `[a, b]`, `g(b)` is equal to `g(a)`, `g` is square integrable on the real interval `[a, b]`, and the L2 norm of the function that maps `x` to `f(x) - g(x)` on the real interval `[a, b]` is less than `e`.

### Informal sketch
The proof proceeds by:
- Using `SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS` to find a continuous function `g` approximating `f` in the L2 norm by `e/2`.
- Applying `REAL_INTEGRAL_TWEAK_ENDS` to `g` to find a function `h` which is `0` outside `[a,b]` and modifies `g` near the endpoints. Specifically, `h` is chosen to equal `g(b) - g(a)` near `a` over an interval of length delta, where delta is small enough that the `L2` of `h` is less than `e/2`.
- Showing that the function mapping `x` to `g(x) + h(x)` satisfies the desired properties.
- Verifying that `g + h` is continuous on `[a,b]`.
- Showing that `(g + h) b = (g + h) a`, i.e. `g(b) + h(b) = g(a) + h(a)`. Since `g` is tweaked only at the ends of the interval, `g(b)` will equal `g(a) + h(a)` and `h(b)` will equal zero, giving `g(b) = g(a) + (g(b) - g(a))`.
- Proving that `g + h` is square integrable.
- Using the triangle inequality for the `L2` norm to establish that the L2 norm of `f - (g + h)` is less than `e`, specifically showing that `l2norm (f - (g + h)) <= l2norm (f - g) + l2norm (h) < e/2 + e/2 = e`.

### Mathematical insight
This theorem shows that any square-integrable function can be approximated arbitrarily well in the L2 norm by a continuous square-integrable function that takes on the same value at the end points of the interval. This is a useful result in analysis and functional analysis, as it allows one to replace a potentially discontinuous function with a continuous one for certain purposes (e.g., when dealing with boundary conditions in differential equations).

### Dependencies
- `SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS`
- `REAL_HALF`
- `REAL_MEASURABLE_REAL_INTERVAL`
- `REAL_INTEGRAL_TWEAK_ENDS`
- `REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE`
- `REAL_CONTINUOUS_ON_ADD`
- `REAL_CONTINUOUS_ON_SUBSET`
- `SUBSET_UNIV`
- `SQUARE_INTEGRABLE_ADD`
- `L2NORM_TRIANGLE`
- `SQUARE_INTEGRABLE_SUB`
- `SQUARE_INTEGRABLE_NEG`
- `L2NORM_NEG`

### Porting notes (optional)
- The proof relies heavily on real analysis libraries, which may need to be adapted or re-implemented in other proof assistants.
- The HOL Light `REAL_ARITH_TAC` is used for discharging arithmetic goals automatically, so the target proof assistant needs similar automation.
- `X_CHOOSE_THEN` relies on a Hilbert choice operator to pick the approximating function. Other proof assistants may require explicit construction of the witness.


---

## WEIERSTRASS_L2_TRIG_POLYNOMIAL

### Name of formal statement
WEIERSTRASS_L2_TRIG_POLYNOMIAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WEIERSTRASS_L2_TRIG_POLYNOMIAL = prove
 (`!f e. f square_integrable_on real_interval[--pi,pi] /\ &0 < e
         ==> ?n a b.
                l2norm (real_interval[--pi,pi])
                       (\x. f x - sum(0..n) (\k. a k * sin(&k * x) +
                                                 b k * cos(&k * x))) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `--pi`; `pi`; `e / &2`]
        SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS_ENDS) THEN
  ASM_REWRITE_TAC[REAL_HALF; REAL_ARITH `--pi < pi <=> &0 < pi`; PI_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real->real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g:real->real`; `e / &6`] WEIERSTRASS_TRIG_POLYNOMIAL) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  MAP_EVERY (fun t -> MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC t)
   [`n:num`; `u:num->real`; `v:num->real`] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  SUBGOAL_THEN
   `!n u v. (\x. sum(0..n) (\k. u k * sin(&k * x) + v k * cos(&k * x)))
            square_integrable_on (real_interval[--pi,pi])`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC SQUARE_INTEGRABLE_SUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE THEN
    MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
    REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
    GEN_TAC THEN DISCH_TAC THEN REAL_DIFFERENTIABLE_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `l2norm (real_interval[--pi,pi]) (\x. f x - g x) +
              l2norm (real_interval[--pi,pi]) (\x. g x - sum(0..n)
                   (\k. u k * sin(&k * x) + v k * cos(&k * x)))` THEN
  CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (rand o rand) L2NORM_TRIANGLE o rand o snd) THEN
    REWRITE_TAC[REAL_ARITH `(f - g) + (g - h):real = f - h`] THEN
    ASM_SIMP_TAC[SQUARE_INTEGRABLE_SUB];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x < e / &2 /\ y <= e / &2 ==> x + y < e`) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[l2norm; l2product; GSYM REAL_POW_2] THEN
  MATCH_MP_TAC REAL_LE_LSQRT THEN
  SUBGOAL_THEN
   `(\x. g x - sum(0..n) (\k. u k * sin(&k * x) + v k * cos(&k * x)))
    square_integrable_on (real_interval[--pi,pi])`
  MP_TAC THENL [ASM_SIMP_TAC[SQUARE_INTEGRABLE_SUB]; ALL_TAC] THEN
  REWRITE_TAC[square_integrable_on] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_POS; REAL_LE_POW_2] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral(real_interval[--pi,pi]) (\x. (e / &6) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN X_GEN_TAC `x:real` THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
    MATCH_MP_TAC(REAL_ARITH `abs x < e ==> abs(x) <= abs e`) THEN
    ASM_SIMP_TAC[];
    SIMP_TAC[REAL_INTEGRAL_CONST; REAL_ARITH `--pi <= pi <=> &0 <= pi`;
             PI_POS_LE] THEN
    REWRITE_TAC[real_div; REAL_POW_MUL; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC]);;
```
### Informal statement
For any function `f` that is square-integrable on the real interval from `-pi` to `pi`, and for any real number `e` greater than 0, there exist a natural number `n`, and real-valued functions `a` and `b` defined on the natural numbers, such that the L2 norm on the interval from `-pi` to `pi` of the function defined by `f(x)` minus the sum from `0` to `n` of `a(k) * sin(k * x) + b(k) * cos(k * x)` is less than `e`.

### Informal sketch
The proof demonstrates that any square-integrable function on the interval `[-pi, pi]` can be approximated in the L2 norm by a trigonometric polynomial.

- Given a square-integrable function `f` on `[-pi, pi]` and `e > 0`, apply `SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS_ENDS` to find a continuous function `g` such that the L2 norm of `f - g` is less than `e/2`.
- Apply `WEIERSTRASS_TRIG_POLYNOMIAL` to the continuous function `g` and `e/6` to find a trigonometric polynomial `sum(u k * sin(k * x) + v k * cos(k * x))` of degree `n` such that `abs(g x - sum(u k * sin(k * x) + v k * cos(k * x))) < e/6` for all `x` in `[-pi, pi]`.
- Show that `sum(u k * sin(k * x) + v k * cos(k * x))` is square integrable on `[-pi, pi]`. This is done by showing that the sum of square integrable functions is square integrable, and that sine and cosine functions are differentiable, thus continuous, and therefore square integrable on `[-pi, pi]`.
- Use the triangle inequality for L2 norms to show that the L2 norm of `f(x) - sum(u k * sin(k * x) + v k * cos(k * x))` is less than the sum of the L2 norm of `f(x) - g(x)` and the L2 norm of `g(x) - sum(u k * sin(k * x) + v k * cos(k * x))`.
- Establish that the L2 norm of `g(x) - sum(u k * sin(k * x) + v k * cos(k * x))` is less than or equal to `e/2`. This is done by bounding the integral of the square of `g(x) - sum(u k * sin(k * x) + v k * cos(k * x))` by the integral of `(e/6)^2` over the interval `[-pi, pi]`, which is shown to be less or equal to `(e/2)^2`.
- Combine these inequalities to conclude that the L2 norm of `f(x) - sum(u k * sin(k * x) + v k * cos(k * x))` is less than `e`.

### Mathematical insight
This theorem provides a crucial result in approximation theory, showing that trigonometric polynomials are dense in the space of square-integrable functions on `[-pi, pi]`. This result justifies the use of Fourier series and other trigonometric approximations in various applications, including signal processing and the solution of differential equations.

### Dependencies
- `REAL_HALF`
- `REAL_ARITH `--pi < pi <=> &0 < pi`
- `PI_POS`
- `SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS_ENDS`
- `WEIERSTRASS_TRIG_POLYNOMIAL`
- `REAL_LT_DIV`
- `REAL_OF_NUM_LT`
- `ARITH`
- `MONO_EXISTS`
- `REAL_LET_TRANS`
- `SQUARE_INTEGRABLE_SUM`
- `FINITE_NUMSEG`
- `IN_NUMSEG`
- `REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE`
- `REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON`
- `REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE`
- `L2NORM_TRIANGLE`
- `SQUARE_INTEGRABLE_SUB`
- `REAL_LE_LSQRT`
- `square_integrable_on`
- `REAL_INTEGRAL_POS`
- `REAL_LE_POW_2`
- `REAL_INTEGRAL_LE`
- `REAL_INTEGRABLE_CONST`
- `REAL_LE_SQUARE_ABS`
- `REAL_POW_MUL`
- `REAL_MUL_ASSOC`
- `REAL_LE_LMUL`
- `PI_POS_LE`
- `PI_APPROX_32`


---

## WEIERSTRASS_L2_TRIGONOMETRIC_SET

### Name of formal statement
WEIERSTRASS_L2_TRIGONOMETRIC_SET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WEIERSTRASS_L2_TRIGONOMETRIC_SET = prove
 (`!f e. f square_integrable_on real_interval[--pi,pi] /\ &0 < e
         ==> ?n a.
                l2norm (real_interval[--pi,pi])
                       (\x. f x -
                            sum(0..n) (\k. a k * trigonometric_set k x))
                < e`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WEIERSTRASS_L2_TRIG_POLYNOMIAL) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `a:num->real`; `b:num->real`] THEN
  DISCH_TAC THEN EXISTS_TAC `2 * n + 1` THEN
  SUBST1_TAC(ARITH_RULE `0 = 2 * 0`) THEN
  REWRITE_TAC[SUM_PAIR; SUM_ADD_NUMSEG; trigonometric_set] THEN
  EXISTS_TAC
   `(\k. if k = 0 then sqrt(&2 * pi) * b 0
         else if EVEN k then sqrt pi * b(k DIV 2)
         else if k <= 2 * n then sqrt pi * a((k + 1) DIV 2)
         else &0):num->real` THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < e ==> y = x ==> y < e`)) THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `x:real` THEN AP_TERM_TAC THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH; ADD_EQ_0; MULT_EQ_0] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_ADD_SYM] THEN BINOP_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    SIMP_TAC[LE_0; ARITH_RULE `2 * i <= 2 * n <=> i <= n`] THEN
    INDUCT_TAC THENL
     [REWRITE_TAC[trigonometric_set; ARITH; LE_0] THEN
      MATCH_MP_TAC(REAL_FIELD
       `&0 < s ==> (s * b) * c / s = b * c`) THEN
      MATCH_MP_TAC SQRT_POS_LT THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
      DISCH_THEN(K ALL_TAC) THEN
      REWRITE_TAC[NOT_SUC; ARITH_RULE `2 * (SUC i) = 2 * i + 2`] THEN
      REWRITE_TAC[trigonometric_set;
                  ARITH_RULE `(2 * i + 2) DIV 2 = SUC i`] THEN
      REWRITE_TAC[ADD1] THEN MATCH_MP_TAC(REAL_FIELD
       `&0 < s ==> (s * b) * c / s = b * c`) THEN
      MATCH_MP_TAC SQRT_POS_LT THEN REWRITE_TAC[PI_POS]];
    REWRITE_TAC[ARITH_RULE `2 * i + 1 = 2 * (i + 1) - 1`] THEN
    REWRITE_TAC[GSYM(SPEC `1` SUM_OFFSET)] THEN
    REWRITE_TAC[GSYM ADD1; ARITH; SUM_CLAUSES_NUMSEG] THEN
    REWRITE_TAC[ARITH_RULE `1 <= SUC n /\ 2 * SUC n - 1 = 2 * n + 1`] THEN
    REWRITE_TAC[ARITH_RULE `~(2 * n + 1 <= 2 * n)`; REAL_MUL_LZERO] THEN
    SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; REAL_ADD_RID] THEN
    SIMP_TAC[SIN_0; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_LID; ARITH] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    SIMP_TAC[ARITH_RULE `1 <= i /\ i <= n ==> 2 * i - 1 <= 2 * n`] THEN
    INDUCT_TAC THEN REWRITE_TAC[ARITH] THEN
    REWRITE_TAC[ARITH_RULE `SUC(2 * SUC i - 1) DIV 2 = SUC i`] THEN
    DISCH_TAC THEN MATCH_MP_TAC(REAL_FIELD
     `&0 < s ==> (s * b) * c / s = b * c`) THEN
    MATCH_MP_TAC SQRT_POS_LT THEN REWRITE_TAC[PI_POS]]);;
```

### Informal statement
For any function `f` that is square integrable on the real interval from `-pi` to `pi`, and for any real number `e` greater than 0, there exist a natural number `n` and a function `a` from natural numbers to real numbers such that the L2 norm on the interval from `-pi` to `pi` of the function that maps `x` to `f x` minus the sum from 0 to `n` of the function that maps `k` to `a k` times `trigonometric_set k x` is less than `e`.

### Informal sketch
The theorem states that any square-integrable function on the interval $[-π, π]$ can be approximated arbitrarily closely in the L2 norm by a trigonometric polynomial. The proof proceeds as follows:
- Start with the assumption that `f` is square integrable on the interval `real_interval[--pi, pi]` and `e > 0`.
- Apply `WEIERSTRASS_L2_TRIG_POLYNOMIAL`, which likely provides a trigonometric polynomial approximation (in terms of coefficients `a` and `b` for cosine and sine terms, respectively) to the function `f`.
- Rewrite the goal to introduce existential quantifiers for `n`, `a`, and `b` - the degree of the polynomial, the cosine coefficients, and the sine coefficients.
- Instantiate `n` with `2 * n + 1`, setting up the degree of the trigonometric polynomial. Note that the formalization utilizes `trigonometric_set`, indexed by the natural numbers, where even indices represent cosine components, and odd indices represent sine components.
- Instantiate the existentially quantified function with a function that combines both cosine and sine terms appropriately, with cosine terms corresponding to even indices and sine terms to odd indices. The coefficients `b` and `a` are used to define this function.
- Simplify the sum using properties of the `SUM` operator and definitions of `trigonometric_set`, reducing the goal to showing that the L2 norm of the difference between `f` and the polynomial approximation is less than `e`. This is likely done by manipulating the summation indices and using the orthogonality of trigonometric functions.

### Mathematical insight
This theorem, `WEIERSTRASS_L2_TRIGONOMETRIC_SET`, is a fundamental result in Fourier analysis, guaranteeing that trigonometric polynomials are dense in the space of square-integrable functions on $[-π, π]$. This means any such function can be approximated arbitrarily well by a linear combination of sines and cosines. The theorem is a cornerstone for representing and analyzing periodic functions and signals.

### Dependencies
- `WEIERSTRASS_L2_TRIG_POLYNOMIAL`
- `LEFT_IMP_EXISTS_THM`
- `SUM_PAIR`
- `SUM_ADD_NUMSEG`
- `trigonometric_set`
- `EVEN_ADD`
- `EVEN_MULT`
- `ARITH`
- `ADD_EQ_0`
- `MULT_EQ_0`
- `FUN_EQ_THM`
- `SUM_EQ_NUMSEG`
- `LE_0`
- `PI_POS`
- `SQRT_POS_LT`
- `SUM_OFFSET`
- `ADD1`
- `SUM_CLAUSES_NUMSEG`
- `REAL_MUL_LZERO`
- `SIN_0`
- `REAL_MUL_RZERO`
- `REAL_ADD_LID`

### Porting notes (optional)
- The definition of `trigonometric_set` would need to be ported. Implementations and libraries of Fourier analysis are typically already available in theorem provers such as Lean.
- Particular attention is required to faithfully translate number system arithmetic conversions, especially the usage of `num` and `real` types in HOL Light, and the definitions/properties of `DIV` or integer division.
- The automation required to deal with real arithmetic may need some adjustments depending on the target prover.


---

## fourier_coefficient

### Name of formal statement
fourier_coefficient

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let fourier_coefficient = new_definition
 `fourier_coefficient =
    orthonormal_coefficient (real_interval[--pi,pi]) trigonometric_set`;;
```
### Informal statement
The `fourier_coefficient` is defined to be the `orthonormal_coefficient` with respect to the real interval from `-pi` to `pi` and the `trigonometric_set`.

### Informal sketch
- The definition introduces `fourier_coefficient` as a specific instance of a more general concept, `orthonormal_coefficient`.
- The `orthonormal_coefficient` is specialized to the interval `real_interval[--pi,pi]` (the real interval from -π to π) and the `trigonometric_set`.
- This means the Fourier coefficients are computed using the trigonometric functions (sine and cosine) as the orthonormal basis on the interval [-π, π].

### Mathematical insight
This definition sets up the standard Fourier coefficients commonly used in Fourier series expansions of functions over the interval [-π, π]. By defining it as a special case of `orthonormal_coefficient`, the definition leverages the theory of orthonormal bases and general Fourier series. The comment indicates that this definition is used for proving convergence results of trigonometric Fourier series in the L2 norm.

### Dependencies
- Definition: `orthonormal_coefficient`
- Definition: `real_interval`
- Definition: `trigonometric_set`


---

## FOURIER_SERIES_L2

### Name of formal statement
FOURIER_SERIES_L2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_SERIES_L2 = prove
 (`!f. f square_integrable_on real_interval[--pi,pi]
       ==> ((\n. l2norm (real_interval[--pi,pi])
                        (\x. f(x) - sum(0..n) (\i. fourier_coefficient f i *
                                                   trigonometric_set i x)))
            ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `e:real`]
    WEIERSTRASS_L2_TRIGONOMETRIC_SET) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a:num->real` THEN DISCH_TAC THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  REWRITE_TAC[fourier_coefficient] THEN MP_TAC(ISPECL
   [`real_interval[--pi,pi]`; `trigonometric_set`;
    `(\i. if i <= n then a i else &0):num->real`;
    `f:real->real`; `0..m`]
    ORTHONORMAL_OPTIMAL_PARTIAL_SUM) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; ORTHONORMAL_SYSTEM_TRIGONOMETRIC_SET;
                  SQUARE_INTEGRABLE_TRIGONOMETRIC_SET; REAL_SUB_RZERO] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ a < e ==> x <= a ==> abs x < e`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC L2NORM_POS_LE THEN
    MATCH_MP_TAC SQUARE_INTEGRABLE_SUB THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SQUARE_INTEGRABLE_SUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SQUARE_INTEGRABLE_LMUL THEN
    REWRITE_TAC[ETA_AX; SQUARE_INTEGRABLE_TRIGONOMETRIC_SET];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < e ==> y = x ==> y < e`)) THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `x:real` THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SUM_EQ_SUPERSET THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; SUBSET_NUMSEG; LE_0] THEN
    SIMP_TAC[IN_NUMSEG; REAL_MUL_LZERO; LE_0]]);;
```
### Informal statement
For all functions `f`, if `f` is square integrable on the real interval from `-pi` to `pi`, then the sequence of `l2norm`s (over the real interval from `-pi` to `pi`) of the difference between `f(x)` and the sum from `0` to `n` of `fourier_coefficient f i * trigonometric_set i x`, converges sequentially to `0` as `n` tends to infinity.

### Informal sketch
The proof establishes that the Fourier series of a square-integrable function converges to the function in the L2 norm.
- Start by stripping the goal.
- Apply `REALLIM_SEQUENTIALLY` to expand the definition of sequential convergence.
- Introduce an arbitrary positive real number `e`.
- Instantiate `WEIERSTRASS_L2_TRIGONOMETRIC_SET` with `f` and `e`. This theorem asserts the existence of coefficients such that the L2 norm of the difference between the function and its trigonometric approximation is less than `e`.
- Existentially instantiate the goal with the approximation coefficients given by `WEIERSTRASS_L2_TRIGONOMETRIC_SET`.
- Introduce the index `m` of the approximation.
- Rewrite using the definition of `fourier_coefficient`.
- Apply `ORTHONORMAL_OPTIMAL_PARTIAL_SUM`. This shows that the partial Fourier sum is the best approximation in L2 norm. We instantiate this lemma with the trigonometric system, the coefficients, and the function `f`.
- Simplify using facts about `FINITE_NUMSEG`, `ORTHONORMAL_SYSTEM_TRIGONOMETRIC_SET`, `SQUARE_INTEGRABLE_TRIGONOMETRIC_SET`, and `REAL_SUB_RZERO`.
- Use real arithmetic to show that if `0 <= x /\ a < e ==> x <= a ==> abs x < e`.
- Use `L2NORM_POS_LE`, `SQUARE_INTEGRABLE_SUB`, `SQUARE_INTEGRABLE_SUM`, `FINITE_NUMSEG`, `IN_NUMSEG`, `SQUARE_INTEGRABLE_LMUL`, `ETA_AX`, `SQUARE_INTEGRABLE_TRIGONOMETRIC_SET`, `FUN_EQ_THM`, `SUM_EQ_SUPERSET`, `FINITE_NUMSEG`, `SUBSET_NUMSEG`, `LE_0`, and `REAL_MUL_LZERO`.
- Simplify further using assumptions.

### Mathematical insight
This theorem is a central result in Fourier analysis. It states that for any square-integrable function, its Fourier series representation converges to the function in the L2 norm. In other words, the energy of the difference between the function and its Fourier series tends to zero. The essence of the proof is to leverage the fact that the trigonometric system is orthonormal and that the partial sums of the Fourier series provide the best approximation in the L2 sense.

### Dependencies
- `REALLIM_SEQUENTIALLY`
- `WEIERSTRASS_L2_TRIGONOMETRIC_SET`
- `fourier_coefficient`
- `ORTHONORMAL_OPTIMAL_PARTIAL_SUM`
- `FINITE_NUMSEG`
- `ORTHONORMAL_SYSTEM_TRIGONOMETRIC_SET`
- `SQUARE_INTEGRABLE_TRIGONOMETRIC_SET`
- `REAL_SUB_RZERO`
- `L2NORM_POS_LE`
- `SQUARE_INTEGRABLE_SUB`
- `SQUARE_INTEGRABLE_SUM`
- `IN_NUMSEG`
- `SQUARE_INTEGRABLE_LMUL`
- `ETA_AX`
- `FUN_EQ_THM`
- `SUM_EQ_SUPERSET`
- `SUBSET_NUMSEG`
- `LE_0`
- `REAL_MUL_LZERO`


---

## TRIGONOMETRIC_SET_MUL_ABSOLUTELY_INTEGRABLE

### Name of formal statement
TRIGONOMETRIC_SET_MUL_ABSOLUTELY_INTEGRABLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TRIGONOMETRIC_SET_MUL_ABSOLUTELY_INTEGRABLE = prove
 (`!f n. f absolutely_real_integrable_on real_interval[--pi,pi]
         ==> (\x. trigonometric_set n x * f x)
             absolutely_real_integrable_on real_interval[--pi,pi]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_MEASURABLE_ON_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real)` THEN
    REWRITE_TAC[REAL_MEASURABLE_REAL_INTERVAL; SUBSET_UNIV] THEN
    MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
    MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
    REWRITE_TAC[ETA_AX; IN_UNIV; REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
    SPEC_TAC(`n:num`,`n:num`) THEN MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
    REWRITE_TAC[trigonometric_set; real_div] THEN
    REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC;
    REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN EXISTS_TAC `&1` THEN
    SPEC_TAC(`n:num`,`n:num`) THEN MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
    REWRITE_TAC[trigonometric_set; REAL_ABS_DIV] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < x ==> &0 < abs x`;
             SQRT_POS_LT; REAL_ARITH `&0 < &2 * x <=> &0 < x`; PI_POS] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[COS_BOUND; SIN_BOUND] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &1 <= &1 * abs x`) THEN
    SUBST1_TAC(GSYM SQRT_1) THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC]);;
```

### Informal statement
For all functions `f` and natural numbers `n`, if `f` is absolutely real-integrable on the real interval from `-pi` to `pi`, then the function defined by `x` mapping to the product of `trigonometric_set n x` and `f x` is also absolutely real-integrable on the real interval from `-pi` to `pi`.

### Informal sketch
The proof proceeds by showing that if `f` is absolutely integrable on `real_interval[--pi, pi]`, then so is `(\x. trigonometric_set n x * f x)`.
- Use `ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT` to reduce the problem to showing that `trigonometric_set n x` is measurable and bounded.
- Show `trigonometric_set n x` is real measurable on `real_interval[--pi,pi]`. This follows since the function is continuous on the interval, and continuous functions are measurable. Continuity follows from differentiability. The HOL Light differentiation tactic is used (via `REAL_DIFFERENTIABLE_TAC`).
- Show `trigonometric_set n x` is bounded on `real_interval[--pi,pi]`. By the definition of `trigonometric_set` and bounding cosine and sine by 1, `abs (trigonometric_set n x)` is bounded by `1/sqrt(pi)`. The fact that `sqrt(pi) > 0` is used to bound the absolute value of the quotient. The `ODD_EVEN_INDUCT_LEMMA` is used with `trigonometric_set` to simplify the definition of trigonometric set into cases n=0 and n=1 since this depends on `odd n` and `even n`.

### Mathematical insight
This theorem establishes that the product of a trigonometric function from the `trigonometric_set` and an absolutely integrable function on the interval `[-pi, pi]` is also absolutely integrable on the same interval. This is a step toward showing that Fourier coefficients go to zero.

### Dependencies
- `ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT`
- `REAL_MEASURABLE_ON_MEASURABLE_SUBSET`
- `REAL_MEASURABLE_REAL_INTERVAL`
- `SUBSET_UNIV`
- `CONTINUOUS_IMP_REAL_MEASURABLE_ON`
- `REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON`
- `ETA_AX`
- `IN_UNIV`
- `REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE`
- `ODD_EVEN_INDUCT_LEMMA`
- `trigonometric_set`
- `real_div`
- `real_bounded`
- `FORALL_IN_IMAGE`
- `REAL_ABS_DIV`
- `REAL_LE_LDIV_EQ`
- `SQRT_POS_LT`
- `PI_POS`
- `REAL_LE_TRANS`
- `COS_BOUND`
- `SIN_BOUND`
- `SQRT_1`
- `SQRT_MONO_LE`
- `PI_APPROX_32`


---

## TRIGONOMETRIC_SET_MUL_INTEGRABLE

### Name of formal statement
TRIGONOMETRIC_SET_MUL_INTEGRABLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TRIGONOMETRIC_SET_MUL_INTEGRABLE = prove
 (`!f n. f absolutely_real_integrable_on real_interval[--pi,pi]
         ==> (\x. trigonometric_set n x * f x)
             real_integrable_on real_interval[--pi,pi]`,
  SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
           TRIGONOMETRIC_SET_MUL_ABSOLUTELY_INTEGRABLE]);;
```
### Informal statement
For all functions `f` and natural numbers `n`, if `f` is absolutely real-integrable on the real interval from `-pi` to `pi`, then the function defined by `\x. trigonometric_set n x * f x` is real-integrable on the real interval from `-pi` to `pi`.

### Informal sketch
The proof proceeds as follows:
- First, use `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE` to show that if `f` is absolutely real-integrable on the interval, then `f` is also real-integrable on that interval.
- Then, apply `TRIGONOMETRIC_SET_MUL_ABSOLUTELY_INTEGRABLE` to demonstrate that the product of the trigonometric set function and an absolutely integrable function is absolutely integrable
- Finally, apply the result from the first step to the absolutely integrable result from the second one.

### Mathematical insight
This theorem states that multiplying a function `f` by the `n`-th element of the `trigonometric_set` preserves real-integrability on the interval `[-pi, pi]`, provided that `f` is absolutely real-integrable on that interval. This is a crucial result for Fourier analysis.

### Dependencies
- Theorems: `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE`, `TRIGONOMETRIC_SET_MUL_ABSOLUTELY_INTEGRABLE`


---

## ABSOLUTELY_INTEGRABLE_SIN_PRODUCT,ABSOLUTELY_INTEGRABLE_COS_PRODUCT

### Name of formal statement
ABSOLUTELY_INTEGRABLE_SIN_PRODUCT,ABSOLUTELY_INTEGRABLE_COS_PRODUCT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ABSOLUTELY_INTEGRABLE_SIN_PRODUCT,ABSOLUTELY_INTEGRABLE_COS_PRODUCT =
 (CONJ_PAIR o prove)
 (`(!f k. f absolutely_real_integrable_on real_interval[--pi,pi]
          ==> (\x. sin(k * x) * f x) absolutely_real_integrable_on
              real_interval[--pi,pi]) /\
   (!f k. f absolutely_real_integrable_on real_interval[--pi,pi]
          ==> (\x. cos(k * x) * f x) absolutely_real_integrable_on
              real_interval[--pi,pi])`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
  (ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_MEASURABLE_ON_MEASURABLE_SUBSET THEN
     EXISTS_TAC `(:real)` THEN
     REWRITE_TAC[REAL_MEASURABLE_REAL_INTERVAL; SUBSET_UNIV] THEN
     MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
     MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
     REWRITE_TAC[ETA_AX; IN_UNIV; REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
     SPEC_TAC(`n:num`,`n:num`) THEN MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
     REWRITE_TAC[trigonometric_set; real_div] THEN
     REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC;
     REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN EXISTS_TAC `&1` THEN
     SPEC_TAC(`n:num`,`n:num`) THEN MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
     REWRITE_TAC[trigonometric_set; COS_BOUND; SIN_BOUND]]));;
```

### Informal statement
The theorem states that if a function `f` is absolutely real integrable on the real interval from `-pi` to `pi`, then the product of `f` with `sin(k * x)` is also absolutely real integrable on the same interval, and similarly, the product of `f` with `cos(k * x)` is also absolutely real integrable on the same interval. This holds for any real number `k`.

### Informal sketch
The proof establishes that if `f` is absolutely integrable on `[-pi, pi]`, then `sin(k * x) * f x` and `cos(k * x) * f x` are also absolutely integrable on the same interval.

- The proof starts by stripping the goal and applying `ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT`. This reduces the problem to showing that `sin(k * x)` and `cos(k * x)` are measurable and bounded on the given interval.
- Next, one needs to show that the sine and cosine functions are measurable. This is achieved by showing that they are continuous.
- To show that `sin(k*x)` and `cos(k*x)` are real measurable functions, the proof relies on `REAL_MEASURABLE_ON_MEASURABLE_SUBSET`, `REAL_MEASURABLE_REAL_INTERVAL`, `CONTINUOUS_IMP_REAL_MEASURABLE_ON`, `REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON`, `REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE` and `REAL_DIFFERENTIABLE_TAC` to conclude that `sin(k*x)` and `cos(k*x)` are measurable since they are differentiable.
- Finally, to prove that the functions are bounded, `real_bounded`, `FORALL_IN_IMAGE`, `COS_BOUND` and `SIN_BOUND` are used to establish the desired result.

### Mathematical insight
This theorem is useful in Fourier analysis. Showing that multiplying an absolutely integrable function by sine or cosine results in another absolutely integrable function is essential for proving the convergence of Fourier series. The integrability of these products allows the definition of Fourier coefficients.

### Dependencies
- `ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT`
- `REAL_MEASURABLE_ON_MEASURABLE_SUBSET`
- `REAL_MEASURABLE_REAL_INTERVAL`
- `SUBSET_UNIV`
- `CONTINUOUS_IMP_REAL_MEASURABLE_ON`
- `REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON`
- `ETA_AX`
- `IN_UNIV`
- `REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE`
- `ODD_EVEN_INDUCT_LEMMA`
- `trigonometric_set`
- `real_div`
- `real_bounded`
- `FORALL_IN_IMAGE`
- `COS_BOUND`
- `SIN_BOUND`


---

## FOURIER_PRODUCTS_INTEGRABLE_STRONG

### Name of formal statement
FOURIER_PRODUCTS_INTEGRABLE_STRONG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_PRODUCTS_INTEGRABLE_STRONG = prove
 (`!f. f absolutely_real_integrable_on real_interval[--pi,pi]
       ==> f real_integrable_on real_interval[--pi,pi] /\
           (!k. (\x. cos(k * x) * f x) real_integrable_on
                real_interval[--pi,pi]) /\
           (!k. (\x. sin(k * x) * f x) real_integrable_on
                real_interval[--pi,pi])`,
  SIMP_TAC[ABSOLUTELY_INTEGRABLE_SIN_PRODUCT;
           ABSOLUTELY_INTEGRABLE_COS_PRODUCT;
           ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE]);;
```
### Informal statement
For all functions `f`, if `f` is absolutely real-integrable on the real interval from `-pi` to `pi`, then `f` is real-integrable on the real interval from `-pi` to `pi`, and for all `k`, the function defined by `x` mapping to `cos(k * x) * f x` is real-integrable on the real interval from `-pi` to `pi`, and for all `k`, the function defined by `x` mapping to `sin(k * x) * f x` is real-integrable on the real interval from `-pi` to `pi`.

### Informal sketch
The proof demonstrates that if a function `f` is absolutely real-integrable on the interval `[-pi, pi]`, then `f` is real-integrable on `[-pi, pi]`, and the products of `f` with `cos(k * x)` and `sin(k * x)` are also real-integrable on `[-pi, pi]` for any `k`.

- The proof leverages existing theorems that relate absolute integrability with integrability and the integrability of products of functions.
- It uses the theorem `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE` to show that absolute real-integrability implies real-integrability.
- `ABSOLUTELY_INTEGRABLE_COS_PRODUCT` is applied to show that if `f` is absolutely integrable, then `cos(k * x) * f x` is integrable.
- `ABSOLUTELY_INTEGRABLE_SIN_PRODUCT` is applied to show that if `f` is absolutely integrable, then `sin(k * x) * f x` is integrable.
- The proof combines these results to establish the theorem by universally quantifying over all functions `f` and integers `k`.

### Mathematical insight
This theorem is important because it shows that if a function is absolutely integrable, then its Fourier series components (sine and cosine products) are also integrable. This is a crucial property in Fourier analysis, as it ensures that the integrals needed to compute Fourier coefficients are well-defined.

### Dependencies
- `ABSOLUTELY_INTEGRABLE_SIN_PRODUCT`
- `ABSOLUTELY_INTEGRABLE_COS_PRODUCT`
- `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE`


---

## FOURIER_PRODUCTS_INTEGRABLE

### Name of formal statement
FOURIER_PRODUCTS_INTEGRABLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_PRODUCTS_INTEGRABLE = prove
 (`!f. f square_integrable_on real_interval[--pi,pi]
       ==> f real_integrable_on real_interval[--pi,pi] /\
           (!k. (\x. cos(k * x) * f x) real_integrable_on
                real_interval[--pi,pi]) /\
           (!k. (\x. sin(k * x) * f x) real_integrable_on
                real_interval[--pi,pi])`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC FOURIER_PRODUCTS_INTEGRABLE_STRONG THEN
  ASM_SIMP_TAC[REAL_MEASURABLE_REAL_INTERVAL;
               SQUARE_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE]);;
```

### Informal statement
For any function `f`, if `f` is square integrable on the real interval from `-pi` to `pi`, then `f` is real integrable on the real interval from `-pi` to `pi`, and for all `k`, the function defined by `x` mapping to `cos(k * x) * f x` is real integrable on the real interval from `-pi` to `pi`, and for all `k`, the function defined by `x` mapping to `sin(k * x) * f x` is real integrable on the real interval from `-pi` to `pi`.

### Informal sketch
The proof proceeds as follows:
- Assume `f` is square integrable on the real interval `[--pi, pi]`.
- Apply the theorem `FOURIER_PRODUCTS_INTEGRABLE_STRONG`.
- Simplify using:
    - `REAL_MEASURABLE_REAL_INTERVAL`: States that a real interval is measurable.
    - `SQUARE_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE`: States that if a function is square integrable then it is absolutely integrable.

### Mathematical insight
This theorem demonstrates that if a function `f` is square integrable on the interval `[-pi, pi]`, then `f` is integrable, and moreover, the products of `f` with cosine and sine functions (with integer frequencies) are also integrable on the same interval. This is a crucial result in Fourier analysis, as it guarantees the integrability of the terms involved in the Fourier series representation of `f`.

### Dependencies
- Theorems:
    - `FOURIER_PRODUCTS_INTEGRABLE_STRONG`
- Definitions:
    - `square_integrable_on`
    - `real_integrable_on`
- Other:
    - `REAL_MEASURABLE_REAL_INTERVAL`
    - `SQUARE_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE`


---

## ABSOLUTELY_INTEGRABLE_APPROXIMATE_CONTINUOUS

### Name of formal statement
ABSOLUTELY_INTEGRABLE_APPROXIMATE_CONTINUOUS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ABSOLUTELY_INTEGRABLE_APPROXIMATE_CONTINUOUS = prove
 (`!f s e. real_measurable s /\ f absolutely_real_integrable_on s /\ &0 < e
           ==> ?g. g real_continuous_on (:real) /\
                   g absolutely_real_integrable_on s /\
                   real_integral s (\x. abs(f x - g x)) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `IMAGE lift s`; `&1:real`; `e:real`]
          LSPACE_APPROXIMATE_CONTINUOUS) THEN
  ASM_REWRITE_TAC[LSPACE_1; GSYM ABSOLUTELY_REAL_INTEGRABLE_ON; REAL_OF_NUM_LE;
                  ARITH; GSYM REAL_MEASURABLE_MEASURABLE] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^1` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `drop o g o lift` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_CONTINUOUS_ON; o_DEF; LIFT_DROP; ETA_AX;
                    IMAGE_LIFT_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_ON; o_DEF; LIFT_DROP; ETA_AX];
    DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < e ==> x = y ==> y < e`)) THEN
    REWRITE_TAC[lnorm; REAL_INV_1; RPOW_POW; REAL_POW_1] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) REAL_INTEGRAL o rand o snd) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN
       `(\x. f x - (drop o g o lift) x) absolutely_real_integrable_on s`
      MP_TAC THENL [ALL_TAC; SIMP_TAC[absolutely_real_integrable_on]] THEN
      ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_SUB; ETA_AX];
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[o_DEF; NORM_LIFT; LIFT_DROP; NORM_REAL; GSYM drop;
                  DROP_SUB; LIFT_SUB]]]);;
```

### Informal statement
For all real-valued functions `f`, sets `s`, and real numbers `e`, if `s` is measurable, `f` is absolutely integrable on `s`, and `e` is greater than 0, then there exists a real-valued function `g` such that `g` is continuous on the set of real numbers, `g` is absolutely integrable on `s`, and the integral over `s` of the absolute value of the difference between `f(x)` and `g(x)` is less than `e`.

### Informal sketch
The theorem states that any absolutely integrable function on a measurable set can be approximated arbitrarily closely in the L1 norm by a continuous function. The proof proceeds as follows:

- The proof starts by stripping the quantifiers and assumptions.
- Instantiate the theorem `LSPACE_APPROXIMATE_CONTINUOUS` with `lift o f o drop`, `IMAGE lift s`, `&1`, and `e`. The theorem `LSPACE_APPROXIMATE_CONTINUOUS` states that L-space functions can be approximated by continuous functions. `lift` and `drop` are used to move between the reals and `real^1`.
- Rewrite using `LSPACE_1`, `ABSOLUTELY_REAL_INTEGRABLE_ON`, `REAL_OF_NUM_LE`, `ARITH`, and `REAL_MEASURABLE_MEASURABLE` to simplify the assumptions.
- Introduce the witness `drop o g o lift` for the existential quantifier using the assumption obtained from `LSPACE_APPROXIMATE_CONTINUOUS`, where `g` is the continuous approximation.
- Prove that `drop o g o lift` is continuous on `(:real)` and absolutely integrable on `s`.
  - Continuity is shown using `REAL_CONTINUOUS_ON`, `o_DEF`, `LIFT_DROP`, `ETA_AX`, and `IMAGE_LIFT_UNIV`.
  - Absolute integrability is shown using `ABSOLUTELY_REAL_INTEGRABLE_ON`, `o_DEF`, `LIFT_DROP`, and `ETA_AX`.
- Show that the integral of the absolute difference is less than `e`.
  - Prove that the integrand `(\x. f x - (drop o g o lift) x)` is absolutely integrable on `s` using `absolutely_real_integrable_on`, `ABSOLUTELY_REAL_INTEGRABLE_SUB`, `ETA_AX`, `o_DEF`, `NORM_LIFT`, `LIFT_DROP`, `NORM_REAL`, `drop`, `DROP_SUB`, and `LIFT_SUB`.
  - Use the assumption that the integral is less than `e` (from `LSPACE_APPROXIMATE_CONTINUOUS`) along with `lnorm`, `REAL_INV_1`, `RPOW_POW`, and `REAL_POW_1` and some real arithmetic.

### Mathematical insight
This theorem is a fundamental result in real analysis, demonstrating that continuous functions are dense in the space of absolutely integrable functions with respect to the L1 norm. This is important because it often allows one to prove results for absolutely integrable functions by first proving it for continuous functions and then extending the result by approximation.

### Dependencies
- `LSPACE_APPROXIMATE_CONTINUOUS`
- `LSPACE_1`
- `ABSOLUTELY_REAL_INTEGRABLE_ON`
- `REAL_OF_NUM_LE`
- `ARITH`
- `REAL_MEASURABLE_MEASURABLE`
- `REAL_CONTINUOUS_ON`
- `o_DEF`
- `LIFT_DROP`
- `ETA_AX`
- `IMAGE_LIFT_UNIV`
- `ABSOLUTELY_REAL_INTEGRABLE_SUB`
- `NORM_LIFT`
- `NORM_REAL`
- `drop`
- `DROP_SUB`
- `LIFT_SUB`
- `lnorm`
- `REAL_INV_1`
- `RPOW_POW`
- `REAL_POW_1`

### Porting notes (optional)
- The use of `lift` and `drop` functions between `real` and `real^1` may need to be adapted based on how single-dimensional real vector spaces are represented in the target proof assistant.
- `LSPACE_APPROXIMATE_CONTINUOUS` is a key dependency; its porting will likely significantly affect the effort required.


---

## RIEMANN_LEBESGUE_SQUARE_INTEGRABLE

### Name of formal statement
RIEMANN_LEBESGUE_SQUARE_INTEGRABLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RIEMANN_LEBESGUE_SQUARE_INTEGRABLE = prove
 (`!s w f.
        orthonormal_system s w /\
        (!i. w i square_integrable_on s) /\
        f square_integrable_on s
        ==> (orthonormal_coefficient s w f ---> &0) sequentially`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `(:num)` o
    MATCH_MP FOURIER_SERIES_SQUARE_SUMMABLE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_SUMMABLE_IMP_TOZERO) THEN
  SIMP_TAC[IN_UNIV; REALLIM_NULL_POW_EQ; ARITH; ETA_AX]);;
```

### Informal statement
For all sets `s`, functions `w`, and functions `f`, if `s` is a set, `w` is a function such that `w i` is an orthonormal system on `s` for any `i`, and `f` is square integrable on `s`, then the orthonormal coefficient of `s`, `w`, and `f` tends to `0` sequentially.

### Informal sketch
The proof proceeds as follows:
- Assume `s` is a set, `w` is a function such that `w i` is an orthonormal system on `s` for any `i`, and `f` is square integrable on `s`.
- Apply `FOURIER_SERIES_SQUARE_SUMMABLE` to prove that the sum of squares of the orthonormal coefficients is summable.
- Apply `REAL_SUMMABLE_IMP_TOZERO` to show the same sequence converges to `0`.
- Simplify the goal by using `IN_UNIV`, `REALLIM_NULL_POW_EQ`, `ARITH`, and `ETA_AX`.

### Mathematical insight
This theorem is the Riemann-Lebesgue Lemma restricted to square-integrable functions and orthonormal systems. It states that the orthonormal coefficients of a square-integrable function with respect to an orthonormal system tend to zero. This is an important result in Fourier analysis and related areas.

### Dependencies
- Theorems: `FOURIER_SERIES_SQUARE_SUMMABLE`, `REAL_SUMMABLE_IMP_TOZERO`
- Definitions: `orthonormal_system`, `square_integrable_on`, `orthonormal_coefficient`, `sequentially`
- Axioms: `IN_UNIV`, `REALLIM_NULL_POW_EQ`, `ARITH`, `ETA_AX`


---

## RIEMANN_LEBESGUE

### Name of formal statement
RIEMANN_LEBESGUE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RIEMANN_LEBESGUE = prove
 (`!f. f absolutely_real_integrable_on real_interval[--pi,pi]
       ==> (fourier_coefficient f ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN MP_TAC(ISPECL
   [`f:real->real`; `real_interval[--pi,pi]`; `e / &2`]
   ABSOLUTELY_INTEGRABLE_APPROXIMATE_CONTINUOUS) THEN
  ASM_SIMP_TAC[REAL_HALF; REAL_MEASURABLE_REAL_INTERVAL;
               LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g:real->real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`real_interval[--pi,pi]`; `trigonometric_set`; `g:real->real`]
        RIEMANN_LEBESGUE_SQUARE_INTEGRABLE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[ORTHONORMAL_SYSTEM_TRIGONOMETRIC_SET;
                SQUARE_INTEGRABLE_TRIGONOMETRIC_SET] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `N:num <= n` THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
  REWRITE_TAC[fourier_coefficient; orthonormal_coefficient; l2product] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `x < e / &2 ==> abs(y - z) <= x ==> y < e / &2 ==> z < e`)) THEN
  MATCH_MP_TAC(REAL_ARITH `abs(x - y) <= r ==> abs(abs x - abs y) <= r`) THEN
  W(MP_TAC o PART_MATCH (rand o rand) REAL_INTEGRAL_SUB o
    rand o lhand o snd) THEN
  ASM_SIMP_TAC[TRIGONOMETRIC_SET_MUL_INTEGRABLE] THEN
  REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN
    ASM_SIMP_TAC[TRIGONOMETRIC_SET_MUL_INTEGRABLE];
    SUBGOAL_THEN `(\x. (f:real->real) x - g x) absolutely_real_integrable_on
                  real_interval[--pi,pi]`
    MP_TAC THENL [ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_SUB]; ALL_TAC] THEN
    SIMP_TAC[absolutely_real_integrable_on];
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_SUB] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    SPEC_TAC(`n:num`,`n:num`) THEN
    MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
    REWRITE_TAC[trigonometric_set; REAL_ABS_DIV] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < x ==> &0 < abs x`;
             SQRT_POS_LT; REAL_ARITH `&0 < &2 * x <=> &0 < x`; PI_POS] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[COS_BOUND; SIN_BOUND] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &1 <= &1 * abs x`) THEN
    SUBST1_TAC(GSYM SQRT_1) THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC]);;
```

### Informal statement
For all functions `f` such that `f` is absolutely real integrable on the real interval from `-pi` to `pi`, the fourier coefficients of `f` converge to `0` sequentially.

### Informal sketch
The proof demonstrates the Riemann-Lebesgue lemma, stating that the Fourier coefficients of an absolutely integrable function on `real_interval[--pi,pi]` tend to zero.

- The proof begins by using `REALLIM_SEQUENTIALLY` to reformulate the limit in terms of sequences. It introduces an arbitrary positive real number `e`. The goal is to show that the absolute value of `fourier_coefficient f` becomes arbitrarily small.
- The proof uses `ABSOLUTELY_INTEGRABLE_APPROXIMATE_CONTINUOUS` to find a continuous function `g` approximating `f` in the `L1` norm.
- It then applies `RIEMANN_LEBESGUE_SQUARE_INTEGRABLE` which states that for a trigonometric set and a square integrable function on `real_interval[--pi, pi]`, the fourier coefficient goes sequentially to zero.
- It uses the fact that a continuous function on a closed interval is square integrable `REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE`.
- The limit is rewritten sequentially, existence of natural number `N` is introduced using `MONO_EXISTS`, allowing to find a bound on `fourier_coefficient f` depending on the chosen `e`.
- The proof expresses the Fourier coefficient in terms of the `l2product` and uses inequalities to bound the `fourier_coefficient f`, making use of the fact that `g` approximates `f`. The bounds are based on the integral of the absolute value of `f - g`.
- Several facts about real integrals are used such as `REAL_INTEGRAL_SUB`, `REAL_INTEGRAL_ABS_BOUND_INTEGRAL`.
- It relies on `ABSOLUTELY_REAL_INTEGRABLE_SUB` and other integrability related facts to show `f - g` absolutely integrable.
- Finally, `TRIGONOMETRIC_SET` properties, bounds and trigonometric identities are leveraged to reach the conclusion.

### Mathematical insight
The Riemann-Lebesgue lemma is a fundamental result in Fourier analysis. It states that the Fourier coefficients of an integrable function vanish at infinity. This is a key property used to analyze the convergence of Fourier series and integrals.

### Dependencies
**Theorems**:
- `REALLIM_SEQUENTIALLY`
- `ABSOLUTELY_INTEGRABLE_APPROXIMATE_CONTINUOUS`
- `RIEMANN_LEBESGUE_SQUARE_INTEGRABLE`
- `ORTHONORMAL_SYSTEM_TRIGONOMETRIC_SET`
- `SQUARE_INTEGRABLE_TRIGONOMETRIC_SET`
- `REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE`
- `REAL_CONTINUOUS_ON_SUBSET`
- `MONO_EXISTS`
- `MONO_FORALL`
- `REAL_INTEGRAL_SUB`
- `REAL_INTEGRAL_ABS_BOUND_INTEGRAL`
- `ABSOLUTELY_REAL_INTEGRABLE_SUB`
- `ODD_EVEN_INDUCT_LEMMA`

**Definitions**:
- `fourier_coefficient`
- `orthonormal_coefficient`
- `l2product`
- `absolutely_real_integrable_on`
- `real_interval`
- `trigonometric_set`

**Others**:
- `REAL_HALF`
- `REAL_MEASURABLE_REAL_INTERVAL`
- `LEFT_IMP_EXISTS_THM`
- `REAL_SUB_RZERO`
- `REAL_ARITH`
- `REAL_ABS_SUB`
- `REAL_ABS_MUL`
- `GSYM REAL_MUL_LID`
- `REAL_LE_RMUL`
- `REAL_ABS_POS`
- `REAL_LE_LDIV_EQ`
- `SQRT_POS_LT`
- `REAL_ARITH &0 < &2 * x <=> &0 < x`
- `PI_POS`
- `REAL_LE_TRANS`
- `COS_BOUND`
- `SIN_BOUND`
- `SQRT_1`
- `SQRT_MONO_LE`
- `PI_APPROX_32`
- `TRIGONOMETRIC_SET_MUL_INTEGRABLE`


---

## RIEMANN_LEBESGUE_SIN

### Name of formal statement
RIEMANN_LEBESGUE_SIN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RIEMANN_LEBESGUE_SIN = prove
 (`!f. f absolutely_real_integrable_on real_interval[--pi,pi]
       ==> ((\n. real_integral (real_interval[--pi,pi])
                                 (\x. sin(&n * x) * f x)) ---> &0)
              sequentially`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RIEMANN_LEBESGUE) THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &4`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N + 1` THEN MATCH_MP_TAC num_INDUCTION THEN
  CONJ_TAC THENL [ARITH_TAC; X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC)] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `2 * n + 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[fourier_coefficient; orthonormal_coefficient;
              trigonometric_set; l2product; REAL_SUB_RZERO] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a / sqrt pi * b = inv(sqrt pi) * a * b`] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_LMUL; FOURIER_PRODUCTS_INTEGRABLE_STRONG] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM real_div)] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; SQRT_POS_LT; PI_POS;
               REAL_ARITH `&0 < x ==> &0 < abs x`; REAL_ABS_DIV] THEN
  REWRITE_TAC[ADD1] THEN
  MATCH_MP_TAC(REAL_ARITH `d <= e ==> x < d ==> x < e`) THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &4 ==> inv(&4) * abs x <= &1`) THEN
  SIMP_TAC[SQRT_POS_LE; PI_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_LSQRT THEN MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC);;
```

### Informal statement
For any function `f` that is absolutely real integrable on the real interval from `-pi` to `pi`, the sequence, indexed by `n`, of real integrals from `-pi` to `pi` of the function mapping `x` to `sin(n * x) * f x` converges sequentially to `0`.

### Informal sketch
The proof proceeds as follows:
- Assume `f` is absolutely real integrable on the interval `[-pi, pi]`.
- Apply the `RIEMANN_LEBESGUE` theorem.
- Rewrite using `REALLIM_SEQUENTIALLY` to convert the limit to an epsilon-delta definition. Introduce an arbitrary real `e > 0`.
- Choose `N` such that for all `n >= N`, the absolute value of `2 * pi` times the fourier coefficient of `f` for a trigonometric set `sin(n x) / sqrt pi` is less than `e/2`.
- Prove by induction on `n`, `n >= N` implies absolute value of the integral from `-pi` to `pi` of `sin((2 * n + 1) * x) * f x` is less than `e`.
- The base case `n = 0` is handled by simplification with the definition of `fourier_coefficient`.
- The step case uses `fourier_coefficient` , `orthonormal_coefficient`, `trigonometric_set`, `l2product`, `REAL_SUB_RZERO` and further arithmetic simplifications using theorems like `REAL_INTEGRAL_LMUL`, `FOURIER_PRODUCTS_INTEGRABLE_STRONG`, `REAL_LT_LDIV_EQ` and `REAL_ABS_DIV`. At the end induction step is proved using a sequence of real arithmetic reasoning.

### Mathematical insight
This theorem is a specific instance of the Riemann-Lebesgue lemma for the sine function. It states that the Fourier coefficients of an absolutely integrable function tend to zero as the frequency increases. This is a fundamental result in Fourier analysis with applications in signal processing, partial differential equations, and other areas of mathematics.

### Dependencies
- `RIEMANN_LEBESGUE`
- `REALLIM_SEQUENTIALLY`
- `fourier_coefficient`
- `orthonormal_coefficient`
- `trigonometric_set`
- `l2product`
- `REAL_SUB_RZERO`
- `REAL_INTEGRAL_LMUL`
- `FOURIER_PRODUCTS_INTEGRABLE_STRONG`
- `REAL_LT_LDIV_EQ`
- `SQRT_POS_LT`
- `PI_POS`
- `REAL_ARITH \`&0 < x ==> &0 < abs x\``
- `REAL_ABS_DIV`
- `ADD1`
- `REAL_MUL_RID`
- `real_div`
- `REAL_MUL_ASSOC`
- `REAL_LE_LMUL_EQ`
- `REAL_ARITH \`&0 <= x /\ x <= &4 ==> inv(&4) * abs x <= &1\``
- `SQRT_POS_LE`
- `PI_POS_LE`
- `REAL_LE_LSQRT`
- `PI_APPROX_32`
- `num_INDUCTION`


---

## RIEMANN_LEBESGUE_COS

### Name of formal statement
RIEMANN_LEBESGUE_COS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RIEMANN_LEBESGUE_COS = prove
 (`!f. f absolutely_real_integrable_on real_interval[--pi,pi]
       ==> ((\n. real_integral (real_interval[--pi,pi])
                                 (\x. cos(&n * x) * f x)) ---> &0)
              sequentially`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RIEMANN_LEBESGUE) THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &4`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N + 1` THEN MATCH_MP_TAC num_INDUCTION THEN
  CONJ_TAC THENL [ARITH_TAC; X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC)] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `2 * n + 2`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[fourier_coefficient; orthonormal_coefficient;
              trigonometric_set; l2product; REAL_SUB_RZERO] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a / sqrt pi * b = inv(sqrt pi) * a * b`] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_LMUL; FOURIER_PRODUCTS_INTEGRABLE_STRONG] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM real_div)] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; SQRT_POS_LT; PI_POS;
               REAL_ARITH `&0 < x ==> &0 < abs x`; REAL_ABS_DIV] THEN
  REWRITE_TAC[ADD1] THEN
  MATCH_MP_TAC(REAL_ARITH `d <= e ==> x < d ==> x < e`) THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &4 ==> inv(&4) * abs x <= &1`) THEN
  SIMP_TAC[SQRT_POS_LE; PI_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_LSQRT THEN MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC);;
```

### Informal statement
For all real-valued functions `f`, if `f` is absolutely real integrable on the real interval from `-pi` to `pi`, then the sequence of real numbers given by the real integral of `cos(n * x) * f x` over the real interval from `-pi` to `pi`, as `n` tends to infinity, converges to `0` sequentially.

### Informal sketch
The proof proceeds as follows:
- Assume `f` is absolutely real integrable on `real_interval[--pi,pi]`.
- Apply the `RIEMANN_LEBESGUE` theorem. This reduces the goal to showing that `f` is in L2.
- Show a reduction to `f` being absolutely integrable implies `f` is in L2.
- Introduce an arbitrary real number `e > 0`.
- Apply `RIEMANN_LEBESGUE` with `e / 4`, obtaining a `N:num` such that the integral of `abs(f - T)` from `-pi` to `pi` is less than `e / 4`, where `T` is a trigonometric polynomial.
- By induction on `n`, prove that for all `n`, if `2 * n + 2 >= N`, and `cos_coeff (2 * n + 2) T < e / 4`, where `cos_coeff` denotes the cosine coefficient of T then the integral of `cos((2*n+2) * x) * f x` from `-pi` to `pi` is less than `e`.
- Simplify based on the properties of the Fourier coefficients, orthonormal trigonometric set, and the L2 product inner product.
- Use the arithmetic fact that if `d <= e` and `x < d` then `x < e`.
- Simplify using inequality relations and `PI_APPROX_32` to derive the required condition.

### Mathematical insight
This theorem is a specific case of the Riemann-Lebesgue Lemma, which states that the Fourier coefficients of an integrable function tend to zero. In this version, it is proved specifically for cosine functions integrated against an absolutely integrable function over the interval `[-pi, pi]`. This is a foundational result in Fourier analysis, showing that as the frequency of the cosine function increases, its correlation with the given function decreases, ultimately vanishing in the limit.

### Dependencies
- `RIEMANN_LEBESGUE`
- `REALLIM_SEQUENTIALLY`
- `fourier_coefficient`
- `orthonormal_coefficient`
- `trigonometric_set`
- `l2product`
- `REAL_SUB_RZERO`
- `REAL_INTEGRAL_LMUL`
- `FOURIER_PRODUCTS_INTEGRABLE_STRONG`
- `REAL_LT_LDIV_EQ`
- `SQRT_POS_LT`
- `PI_POS`
- `REAL_ARITH \`&0 < x ==> &0 < abs x\``
- `REAL_ABS_DIV`
- `ADD1`
- `REAL_MUL_RID`
- `real_div`
- `GSYM REAL_MUL_ASSOC`
- `REAL_LE_LMUL_EQ`
- `REAL_ARITH \`&0 <= x /\ x <= &4 ==> inv(&4) * abs x <= &1\``
- `SQRT_POS_LE`
- `PI_POS_LE`
- `REAL_LE_LSQRT`
- `PI_APPROX_32`


---

## RIEMANN_LEBESGUE_SIN_HALF

### Name of formal statement
RIEMANN_LEBESGUE_SIN_HALF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RIEMANN_LEBESGUE_SIN_HALF = prove
 (`!f. f absolutely_real_integrable_on real_interval[--pi,pi]
       ==> ((\n. real_integral (real_interval[--pi,pi])
                               (\x. sin((&n + &1 / &2) * x) * f x)) ---> &0)
              sequentially`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SIN_ADD; REAL_ADD_RDISTRIB] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `(\n. real_integral (real_interval[--pi,pi])
                          (\x. sin(&n * x) * cos(&1 / &2 * x) * f x) +
                   real_integral (real_interval[--pi,pi])
                          (\x. cos(&n * x) * sin(&1 / &2 * x) * f x))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC REAL_INTEGRAL_ADD;
    MATCH_MP_TAC REALLIM_NULL_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC RIEMANN_LEBESGUE_SIN;
      MATCH_MP_TAC RIEMANN_LEBESGUE_COS]] THEN
  ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
               ABSOLUTELY_INTEGRABLE_SIN_PRODUCT;
               ABSOLUTELY_INTEGRABLE_COS_PRODUCT]);;
```
### Informal statement
For all real-valued functions `f`, if `f` is absolutely real-integrable on the real interval from `-pi` to `pi`, then the sequence whose `n`-th term is the real integral from `-pi` to `pi` of `sin((n + 1/2) * x) * f x` converges to `0` sequentially as `n` tends to infinity.

### Informal sketch
- The proof starts by stripping the goal and rewriting using the trigonometric identity `sin(a + b) = sin(a)cos(b) + cos(a)sin(b)` and the distributive property for real numbers.
- Then, the theorem `REALLIM_TRANSFORM_EVENTUALLY` is used to transform the limit. Specifically, it amounts to showing that the sequence of integrals can be rewritten as the sum of two integrals, namely the real integral from `-pi` to `pi` of `sin(n * x) * cos(1/2 * x) * f x` plus the real integral from `-pi` to `pi` of `cos(n * x) * sin(1/2 * x) * f x`.
- It suffices to show these two integrals both converge to `0` as `n` goes to infinity. The proof proceeds by showing that, under the assumption that `f` is absolutely integrable, each of the integrals converges to zero. This uses `RIEMANN_LEBESGUE_SIN` and `RIEMANN_LEBESGUE_COS` respectively.
- Finally, the absolute real integrability of `f` implies the integrability of the product of `f` with sine and cosine functions, which is necessary for applying these Riemann-Lebesgue lemmas.

### Mathematical insight
This theorem is a variant of the Riemann-Lebesgue lemma. The Riemann-Lebesgue lemma is a fundamental result in Fourier analysis. It states that the Fourier coefficients of an integrable function tend to zero as the frequency increases. This particular version focuses on the case where the function is absolutely integrable on the interval `[-pi, pi]` and considers the specific frequency term `(n + 1/2)`.

### Dependencies
- `SIN_ADD`
- `REAL_ADD_RDISTRIB`
- `REALLIM_TRANSFORM_EVENTUALLY`
- `REAL_MUL_ASSOC`
- `REAL_INTEGRAL_ADD`
- `REALLIM_NULL_ADD`
- `RIEMANN_LEBESGUE_SIN`
- `RIEMANN_LEBESGUE_COS`
- `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE`
- `ABSOLUTELY_INTEGRABLE_SIN_PRODUCT`
- `ABSOLUTELY_INTEGRABLE_COS_PRODUCT`


---

## FOURIER_SUM_LIMIT_PAIR

### Name of formal statement
FOURIER_SUM_LIMIT_PAIR

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_SUM_LIMIT_PAIR = prove
 (`!f n t l.
        f absolutely_real_integrable_on real_interval [--pi,pi]
        ==> (((\n. sum(0..2*n) (\k. fourier_coefficient f k *
                                    trigonometric_set k t)) ---> l)
             sequentially <=>
             ((\n. sum(0..n) (\k. fourier_coefficient f k *
                                  trigonometric_set k t)) ---> l)
             sequentially)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP RIEMANN_LEBESGUE) THEN
    REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "1")) THEN
    SUBGOAL_THEN `&0 < e / &2` (fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th))
    THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "2")) THEN
    EXISTS_TAC `N1 + 2 * N2 + 1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    DISJ_CASES_THEN SUBST1_TAC
     (ARITH_RULE `n = 2 * n DIV 2 \/ n = SUC(2 * n DIV 2)`) THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THENL
     [MATCH_MP_TAC(REAL_ARITH `abs x < e / &2 ==> abs x < e`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH
       `abs(x - l) < e / &2 /\ abs y < e / &2 ==> abs((x + y) - l) < e`) THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH
       `abs(x * y) <= abs(x) * &1 /\ abs(x) < e ==> abs(x * y) < e`) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        REWRITE_TAC[REAL_ABS_POS] THEN
        SPEC_TAC(`SUC(2 * n DIV 2)`,`r:num`) THEN
        MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
        REWRITE_TAC[ADD1; trigonometric_set; REAL_ABS_DIV] THEN
        SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < x ==> &0 < abs x`;
                 SQRT_POS_LT; REAL_ARITH `&0 < &2 * x <=> &0 < x`; PI_POS] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `&1` THEN REWRITE_TAC[COS_BOUND; SIN_BOUND] THEN
        MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &1 <= &1 * abs x`) THEN
        SUBST1_TAC(GSYM SQRT_1) THEN MATCH_MP_TAC SQRT_MONO_LE THEN
        MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]];
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;
```

### Informal statement
For all real-valued functions `f`, natural numbers `n`, real numbers `t`, and real numbers `l`, if `f` is absolutely real integrable on the real interval `[--pi,pi]`, then the sequence defined by the partial sums of the Fourier series of `f` up to `2*n` converges to `l` sequentially if and only if the sequence defined by the partial sums of the Fourier series of `f` up to `n` converges to `l` sequentially. In other words,
```
f absolutely_real_integrable_on real_interval [--pi,pi]
        ==> (((\n. sum(0..2*n) (\k. fourier_coefficient f k *
                                    trigonometric_set k t)) ---> l)
             sequentially <=>
             ((\n. sum(0..n) (\k. fourier_coefficient f k *
                                  trigonometric_set k t)) ---> l)
             sequentially)
```

### Informal sketch
The proof proceeds as follows:
- Rewrite the sequential convergence using `REALLIM_SEQUENTIALLY`, transforming the limit statements into epsilon-delta definitions.
- Perform equational reasoning (`EQ_TAC`) and discharge assumptions (`DISCH_TAC`) to isolate the core implication.
- Introduce an arbitrary positive real number `e` (`X_GEN_TAC`).
- Apply the `RIEMANN_LEBESGUE` lemma to show that the tail of the Fourier series goes to zero.  This involves manipulating the epsilon bounds by dividing by 2.
- Choose appropriate natural numbers `N1` and `N2` based on the convergence criteria of the Fourier series and the Riemann-Lebesgue lemma, respectively.
- Construct a natural number `N` based on `N1` and `N2`, specifically `N1 + 2 * N2 + 1`.
- Analyze two cases based on whether `n` is even or odd (`n = 2 * n DIV 2 \/ n = SUC(2 * n DIV 2)`), and rewrite sums accordingly using `SUM_CLAUSES_NUMSEG`.
- In each case, use algebraic manipulations and inequalities to show that the absolute difference between the partial Fourier sum and the limit `l` is less than `e`. This involves bounding trigonometric functions and using properties of absolute values.  The trigonometric bound uses `trigonometric_set`, `COS_BOUND`, `SIN_BOUND` and `PI_APPROX_32`.
- Finally, utilize `MONO_EXISTS` to generalize over the constructed `N`, completing the proof.

### Mathematical insight
This theorem states that the convergence of the partial sums of the Fourier series up to *n* is equivalent to the convergence of the partial sums up to *2n*. This highlights a redundancy: checking convergence of Fourier series partial sums need not look at *all* partial sums, it only needs to check every other (or every *k*-th) index.  The theorem essentially shows that the even-indexed partial sums determine the limit of all partial sums. This can be useful in simplifying convergence analyses or numerical computations involving Fourier series.

### Dependencies
- `REALLIM_SEQUENTIALLY`: Definition of sequential limits in terms of epsilons and natural numbers.
- `RIEMANN_LEBESGUE`: Riemann-Lebesgue lemma concerning the asymptotic behavior of Fourier coefficients.
- `SUM_CLAUSES_NUMSEG`: Lemmas for manipulating sums over number segments.
- `trigonometric_set`: Definition of the trigonometric set used in Fourier series.
- `COS_BOUND`, `SIN_BOUND`: Bounds for cosine and sine functions respectively between -1 and 1.
- `PI_APPROX_32`: Lower bound approximation of Pi by 3.1
- `SQRT_1`, `SQRT_POS_LT`, `SQRT_MONO_LE`: Square root properties and monotonicity
- `ODD_EVEN_INDUCT_LEMMA`

### Porting notes (optional)
- The proof relies on the specific real analysis library of HOL Light.  When porting to another assistant, ensure that equivalent theorems concerning real limits, absolute integrability, and trigonometric functions exist.
- Automation using `REAL_ARITH_TAC` is heavily used, so a corresponding arithmetic decision procedure may be necessary or the arithmetic portions must be proved manually.
- The use of `FIRST_X_ASSUM` and `MATCH_MP_TAC` suggests that the proof is somewhat brittle with respect to the order of assumptions. Care may be needed to adapt the proof strategy to the specific features of the automation and rewriting system in the new assistant.


---

## FOURIER_SUM_0

### Name of formal statement
FOURIER_SUM_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_SUM_0 = prove
 (`!f n.
     sum (0..n) (\k. fourier_coefficient f k * trigonometric_set k (&0)) =
     sum (0..n DIV 2)
         (\k. fourier_coefficient f (2 * k) * trigonometric_set (2 * k) (&0))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum (2 * 0..2 * (n DIV 2) + 1)
                 (\k. fourier_coefficient f k * trigonometric_set k (&0))` THEN
  CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SUM_SUPERSET THEN
    REWRITE_TAC[IN_NUMSEG; SUBSET; LE_0] THEN
    CONJ_TAC THENL [ARITH_TAC; GEN_TAC] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `x <= 2 * n DIV 2 + 1 /\ ~(x <= n) ==> x = 2 * n DIV 2 + 1`));
    REWRITE_TAC[SUM_PAIR]] THEN
  REWRITE_TAC[trigonometric_set;  real_div; REAL_MUL_RZERO; SIN_0;
              REAL_MUL_LZERO; REAL_ADD_RID]);;
```

### Informal statement
For any function `f` and natural number `n`, the sum from `0` to `n` of terms of the form `fourier_coefficient f k * trigonometric_set k (&0)` is equal to the sum from `0` to `n DIV 2` of terms of the form `fourier_coefficient f (2 * k) * trigonometric_set (2 * k) (&0)`.

### Informal sketch
The proof proceeds as follows:
- Start by proving the main theorem.
- Perform existential instantiation with `sum (2 * 0..2 * (n DIV 2) + 1) (\k. fourier_coefficient f k * trigonometric_set k (&0))`.
- Split into two subgoals using `CONJ_TAC`.
- The first subgoal involves proving that `sum (0..n) (\k. fourier_coefficient f k * trigonometric_set k (&0)) = sum (2 * 0..2 * (n DIV 2) + 1) (\k. fourier_coefficient f k * trigonometric_set k (&0))`.
  - Simplify using arithmetic reduction.
  - Transform the equation using symmetry (swap sides).
  - Apply `SUM_SUPERSET`.
  - Rewrite using `IN_NUMSEG`, `SUBSET`, and `LE_0`.
  - Split into two further subgoals using `CONJ_TAC`.
   - Solve both subgoals with `ARITH_TAC` and `GEN_TAC`.
   - Use arithmetic to prove `x <= 2 * n DIV 2 + 1 /\ ~(x <= n) ==> x = 2 * n DIV 2 + 1` then substitute the equality.
   - Rewrite using `SUM_PAIR`.
- Rewrite using `trigonometric_set`, `real_div`, `REAL_MUL_RZERO`, `SIN_0`, `REAL_MUL_LZERO`, and `REAL_ADD_RID`.

### Mathematical insight
This theorem relates the Fourier sum up to degree `n` with its equivalent expansion solely in terms of even-numbered trigonometric components, specifically evaluated at `&0`. This simplification exploits properties of the cosine and sine functions at zero. In essence, it expresses the Fourier sum at the origin using only the cosine terms.

### Dependencies
- `IN_NUMSEG`
- `SUBSET`
- `LE_0`
- `SUM_SUPERSET`
- `SUM_PAIR`
- `trigonometric_set`
- `real_div`
- `REAL_MUL_RZERO`
- `SIN_0`
- `REAL_MUL_LZERO`
- `REAL_ADD_RID`


---

## FOURIER_SUM_0_EXPLICIT

### Name of formal statement
FOURIER_SUM_0_EXPLICIT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_SUM_0_EXPLICIT = prove
 (`!f n.
     sum (0..n) (\k. fourier_coefficient f k * trigonometric_set k (&0)) =
     (fourier_coefficient f 0 / sqrt(&2) +
      sum (1..n DIV 2) (\k. fourier_coefficient f (2 * k))) / sqrt pi`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FOURIER_SUM_0] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; real_div;
           REAL_ADD_RDISTRIB; GSYM SUM_RMUL] THEN
  REWRITE_TAC[MULT_CLAUSES; trigonometric_set;
              REAL_MUL_LZERO; COS_0; real_div] THEN
  BINOP_TAC THENL
   [REWRITE_TAC[REAL_MUL_LID; SQRT_MUL; REAL_INV_MUL; GSYM REAL_MUL_ASSOC];
    REWRITE_TAC[ADD_CLAUSES] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    INDUCT_TAC THEN REWRITE_TAC[ARITH] THEN
    REWRITE_TAC[trigonometric_set; ARITH_RULE `2 * SUC i = 2 * i + 2`] THEN
    REWRITE_TAC[REAL_MUL_RZERO; COS_0; real_div; REAL_MUL_LID]]);;
```

### Informal statement
For any function `f` and natural number `n`, the sum from 0 to `n` of the terms `fourier_coefficient f k * trigonometric_set k (&0)` is equal to `(fourier_coefficient f 0 / sqrt(&2) + sum (1..n DIV 2) (\k. fourier_coefficient f (2 * k))) / sqrt pi`.

### Informal sketch
The proof proceeds by induction and rewriting using properties of summations, Fourier coefficients, and trigonometric sets.
- Begins by Rewriting using `FOURIER_SUM_0`
- Simplification using lemmas about sums, inequalities, division of real numbers, and distribution.
- Rewriting based on lemmas about multiplication, trigonometric sets, `REAL_MUL_LZERO`, cosine at 0, and division of real numbers
- Performs induction after splitting into two cases
    - Uses rewriting to simplify the goal using lemmas related to real multiplication, square roots, inverse multiplication, and associativity of real multiplication.
    - Applies `SUM_EQ_NUMSEG` and proceeds by induction.
        - Base case: trivial by arithmetic.
        - Inductive step: Rewrites using `trigonometric_set`, arithmetic, properties about multiplication `REAL_MUL_RZERO`, `COS_0`, real division, and `REAL_MUL_LID`.

### Mathematical insight
This theorem provides an explicit formula for the partial sums of the Fourier series of a function `f` at the point 0. It relates the sum of the first `n+1` terms of the Fourier series at 0 to a sum involving the Fourier coefficients of `f` at even indices. Because `trigonometric_set k (&0)` is equal to $\sqrt{2/\pi}$ when $k$ is zero, $\sqrt{1/\pi}$ when $k$ is even and 0 otherwise, this simplifies the sum.

### Dependencies
- `FOURIER_SUM_0`
- `SUM_CLAUSES_LEFT`
- `LE_0`
- `real_div`
- `REAL_ADD_RDISTRIB`
- `GSYM SUM_RMUL`
- `MULT_CLAUSES`
- `trigonometric_set`
- `REAL_MUL_LZERO`
- `COS_0`
- `REAL_MUL_LID`
- `SQRT_MUL`
- `REAL_INV_MUL`
- `GSYM REAL_MUL_ASSOC`
- `ADD_CLAUSES`
- `SUM_EQ_NUMSEG`
- `ARITH`
- `REAL_MUL_RZERO`

### Porting notes (optional)
The proof relies heavily on rewriting and simplification. The user will need to ensure their target proof assistant has similar capabilities for handling real arithmetic and algebraic manipulation of sums. Lemmas related to trigonometric functions and Fourier coefficients will need to be defined or ported first.


---

## FOURIER_SUM_0_INTEGRALS

### Name of formal statement
FOURIER_SUM_0_INTEGRALS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_SUM_0_INTEGRALS = prove
 (`!f n.
      f absolutely_real_integrable_on real_interval[--pi,pi]
      ==> sum (0..n) (\k. fourier_coefficient f k * trigonometric_set k (&0)) =
          (real_integral(real_interval[--pi,pi]) f / &2 +
           sum(1..n DIV 2) (\k. real_integral (real_interval[--pi,pi])
                                              (\x. cos(&k * x) * f x))) / pi`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FOURIER_SUM_0_EXPLICIT] THEN
  REWRITE_TAC[fourier_coefficient; orthonormal_coefficient; l2product] THEN
  REWRITE_TAC[real_div; REAL_ADD_RDISTRIB; GSYM SUM_RMUL] THEN
  REWRITE_TAC[trigonometric_set] THEN BINOP_TAC THENL
   [REWRITE_TAC[COS_0; REAL_MUL_LZERO; real_div; REAL_MUL_LID] THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_LMUL; FOURIER_PRODUCTS_INTEGRABLE_STRONG] THEN
    REWRITE_TAC[REAL_ARITH `((a * b) * c) * d:real = b * a * c * d`] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_INV_MUL] THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN
    SIMP_TAC[GSYM SQRT_MUL; REAL_POS; PI_POS_LE; REAL_LE_MUL] THEN
    REWRITE_TAC[GSYM REAL_POW_2] THEN MATCH_MP_TAC POW_2_SQRT THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC;
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    INDUCT_TAC THEN REWRITE_TAC[ARITH] THEN STRIP_TAC THEN
    REWRITE_TAC[trigonometric_set; ARITH_RULE `2 * SUC i = 2 * i + 2`] THEN
    REWRITE_TAC[REAL_MUL_RZERO; COS_0; real_div; REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(a * b) * c:real = b * a * c`] THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_LMUL; FOURIER_PRODUCTS_INTEGRABLE_STRONG] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(i * x) * i:real = x * i * i`] THEN
    REWRITE_TAC[ADD1; GSYM REAL_INV_MUL] THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_POW_2] THEN
    MATCH_MP_TAC SQRT_POW_2 THEN REWRITE_TAC[PI_POS_LE]]);;
```
### Informal statement
For any function `f` and natural number `n`, if `f` is absolutely real integrable on the real interval from `-pi` to `pi`, then the sum from `0` to `n` of the terms `fourier_coefficient f k * trigonometric_set k (&0)` is equal to `(real_integral(real_interval[--pi,pi]) f / &2 + sum(1..n DIV 2) (\k. real_integral (real_interval[--pi,pi]) (\x. cos(&k * x) * f x))) / pi`.

### Informal sketch
The proof proceeds by:

- Rewriting the left-hand side using the expansion of `FOURIER_SUM_0_EXPLICIT`.
- Expanding `fourier_coefficient`, `orthonormal_coefficient`, and `l2product`.
- Manipulating real arithmetic expressions involving division, addition, and multiplication using theorems like `REAL_ADD_RDISTRIB` and `SUM_RMUL`, and then expanding trigonometric sets using `trigonometric_set`.
- Separating the first term of the sum (corresponding to index `0`). The tactic `BINOP_TAC` achieves this step.
- Simplifying the first term (index `0`) using `COS_0`, `REAL_MUL_LZERO`, `real_div` and `REAL_MUL_LID`.
- Using `REAL_INTEGRAL_LMUL` and `FOURIER_PRODUCTS_INTEGRABLE_STRONG` to distribute scalar multiplication over integrals.
- Applying arithmetic simplifications involving associativity, inverses, and then using the square root of powers to simplify `sqrt(pi^2)`. It uses `AP_TERM_TAC` to apply the simplification rules to the integral term. `POW_2_SQRT` and `PI_POS` are used to simplify further.
- Dealing with the remaining sum by induction, using `SUM_EQ_NUMSEG` and `INDUCT_TAC`. In the inductive step, rewrite the definition of `trigonometric_set` and simplify arithmetic `2 * SUC i = 2 * i + 2`.
- For `i` = 0, it simplifies using `REAL_MUL_RZERO`, `COS_0`, `real_div` and `REAL_MUL_LID`, and also uses re-association rules to expose terms. Similar to base case, scalar multiplication is distributed over integrals via `REAL_INTEGRAL_LMUL` and `FOURIER_PRODUCTS_INTEGRABLE_STRONG`.
- It uses arithmetic simplifications involving associativity, inverses, and then uses the square root of powers to simplify `sqrt(pi^2)` using `SQRT_POW_2` and `PI_POS_LE`.

### Mathematical insight
This theorem expresses the partial sum of the Fourier series of a function `f` at `0` in terms of integrals of `f` and cosine functions. The theorem relates the discrete Fourier series (represented by the sum on the left-hand side) to the integral representation of the Fourier coefficients (present on the right-hand side). It highlights how, under suitable conditions, the initial terms of the Fourier series provide an approximation to the function's value at `0`.

### Dependencies
- Definition: `fourier_coefficient`
- Definition: `orthonormal_coefficient`
- Definition: `l2product`
- Definition: `trigonometric_set`
- Theorem: `FOURIER_SUM_0_EXPLICIT`
- Theorem: `REAL_ADD_RDISTRIB`
- Theorem: `COS_0`
- Theorem: `REAL_MUL_LZERO`
- Theorem: `REAL_MUL_LID`
- Theorem: `REAL_INTEGRAL_LMUL`
- Theorem: `FOURIER_PRODUCTS_INTEGRABLE_STRONG`
- Theorem: `REAL_MUL_ASSOC`
- Theorem: `REAL_INV_MUL`
- Theorem: `SQRT_MUL`
- Theorem: `REAL_POS`
- Theorem: `PI_POS_LE`
- Theorem: `REAL_LE_MUL`
- Theorem: `REAL_POW_2`
- Theorem: `POW_2_SQRT`
- Theorem: `PI_POS`
- Theorem: `SUM_EQ_NUMSEG`
- Theorem: `ADD1`

### Porting notes (optional)
- The handling of real analysis concepts (integrals, limits) will likely require careful attention to the specific axioms and constructions available in the target proof assistant.
- The extensive use of real arithmetic manipulation (using theorems like `REAL_ADD_RDISTRIB`, `REAL_MUL_ASSOC`, etc.) suggests that a proof assistant with strong support for real number reasoning will be beneficial.
- The tactic `ASM_SIMP_TAC` combines assumption simplification and simplification with a given list of theorems. In other systems, this may require explicitly separating assumption discharge and simplification steps.


---

## FOURIER_SUM_0_INTEGRAL

### Name of formal statement
FOURIER_SUM_0_INTEGRAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_SUM_0_INTEGRAL = prove
 (`!f n.
      f absolutely_real_integrable_on real_interval[--pi,pi]
      ==> sum(0..n) (\k. fourier_coefficient f k * trigonometric_set k (&0)) =
          real_integral(real_interval[--pi,pi])
           (\x. (&1 / &2 + sum(1..n DIV 2) (\k. cos(&k * x))) * f x) / pi`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FOURIER_SUM_0_INTEGRALS] THEN
  ASM_SIMP_TAC[GSYM REAL_INTEGRAL_SUM; FINITE_NUMSEG;
               FOURIER_PRODUCTS_INTEGRABLE_STRONG; real_div;
               GSYM REAL_INTEGRAL_ADD;
               GSYM REAL_INTEGRAL_RMUL; REAL_INTEGRABLE_RMUL; ETA_AX;
               REAL_INTEGRABLE_SUM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; SUM_RMUL] THEN REAL_ARITH_TAC);;
```
### Informal statement
For all absolutely real integrable functions `f` on the real interval from `-pi` to `pi`, and for all natural numbers `n`, the sum from `0` to `n` of `fourier_coefficient f k * trigonometric_set k (&0)` is equal to the integral from `-pi` to `pi` of `((&1 / &2 + sum(1..n DIV 2) (\k. cos(&k * x))) * f x)` divided by `pi`.

### Informal sketch
The proof proceeds by:
- Stripping the quantifiers and assumptions.
- Applying simplification using `FOURIER_SUM_0_INTEGRALS`.
- Further simplification using lemmas such as `GSYM REAL_INTEGRAL_SUM`, `FINITE_NUMSEG`, `FOURIER_PRODUCTS_INTEGRABLE_STRONG`, `real_div`, `GSYM REAL_INTEGRAL_ADD`, `GSYM REAL_INTEGRAL_RMUL`, `REAL_INTEGRABLE_RMUL`, `ETA_AX`, and `REAL_INTEGRABLE_SUM`.
- Applying `AP_THM_TAC` twice and `AP_TERM_TAC` twice.
- Rewriting using `FUN_EQ_THM` and `SUM_RMUL`.
- Finally, using `REAL_ARITH_TAC` to complete the proof.

### Mathematical insight
This theorem relates a partial sum of the Fourier series of a function `f` evaluated at `0` to an integral involving `f` and a Dirichlet kernel. The Fourier coefficient `fourier_coefficient f k` represents the `k`-th coefficient in the Fourier series expansion of `f`. The term `trigonometric_set k (&0)` evaluates the `k`-th trigonometric function (sine or cosine depending on parity) at `0`. The integral form on the right-hand side offers a way to approximate the partial Fourier sum by integrating a product of the function `f` with a summation of cosine functions (Dirichlet kernel).

### Dependencies
**Theorems/Definitions**
- `FOURIER_SUM_0_INTEGRALS`
- `GSYM REAL_INTEGRAL_SUM`
- `FINITE_NUMSEG`
- `FOURIER_PRODUCTS_INTEGRABLE_STRONG`
- `real_div`
- `GSYM REAL_INTEGRAL_ADD`
- `GSYM REAL_INTEGRAL_RMUL`
- `REAL_INTEGRABLE_RMUL`
- `ETA_AX`
- `REAL_INTEGRABLE_SUM`
- `FUN_EQ_THM`
- `SUM_RMUL`


---

## FOURIER_COEFFICIENT_ADD

### Name of formal statement
FOURIER_COEFFICIENT_ADD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_COEFFICIENT_ADD = prove
 (`!f g i. f absolutely_real_integrable_on real_interval[--pi,pi] /\
           g absolutely_real_integrable_on real_interval[--pi,pi]
           ==> fourier_coefficient (\x. f x + g x) i =
                fourier_coefficient f i + fourier_coefficient g i`,
  SIMP_TAC[fourier_coefficient; orthonormal_coefficient; l2product] THEN
  SIMP_TAC[TRIGONOMETRIC_SET_MUL_INTEGRABLE; REAL_ADD_LDISTRIB;
           REAL_INTEGRAL_ADD]);;
```
### Informal statement
For all functions `f` and `g`, and for all integers `i`, if `f` is absolutely real integrable on the real interval from `-pi` to `pi` and `g` is absolutely real integrable on the real interval from `-pi` to `pi`, then the `i`-th Fourier coefficient of the function defined by `x` maps to `f x + g x` is equal to the sum of the `i`-th Fourier coefficient of `f` and the `i`-th Fourier coefficient of `g`.

### Informal sketch
The proof proceeds by:
- Expanding `fourier_coefficient` to `orthonormal_coefficient` and `l2product`.
- Using the fact that the trigonometric set multipliers are integrable.
- Distributing real addition.
- Using the fact that the real integral of a sum is the sum of the integrals.

### Mathematical insight
This theorem demonstrates the linearity of the Fourier coefficient operator. It states that the Fourier coefficient of the sum of two functions is the sum of their individual Fourier coefficients, provided both functions are absolutely integrable on the interval [-π, π]. This property is crucial in Fourier analysis and signal processing, as it allows us to analyze the frequency components of complex signals by decomposing them into simpler additive components.

### Dependencies
- Definitions: `fourier_coefficient`, `orthonormal_coefficient`, `l2product`
- Theorems: `TRIGONOMETRIC_SET_MUL_INTEGRABLE`, `REAL_ADD_LDISTRIB`, `REAL_INTEGRAL_ADD`


---

## FOURIER_COEFFICIENT_SUB

### Name of formal statement
FOURIER_COEFFICIENT_SUB

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_COEFFICIENT_SUB = prove
 (`!f g i. f absolutely_real_integrable_on real_interval[--pi,pi] /\
           g absolutely_real_integrable_on real_interval[--pi,pi]
           ==> fourier_coefficient (\x. f x - g x) i =
                fourier_coefficient f i - fourier_coefficient g i`,
  SIMP_TAC[fourier_coefficient; orthonormal_coefficient; l2product] THEN
  SIMP_TAC[TRIGONOMETRIC_SET_MUL_INTEGRABLE; REAL_SUB_LDISTRIB;
           REAL_INTEGRAL_SUB]);;
```
### Informal statement
For all functions `f` and `g`, and for all integers `i`, if `f` is absolutely real integrable on the real interval from `-pi` to `pi` and `g` is absolutely real integrable on the real interval from `-pi` to `pi`, then the `i`-th Fourier coefficient of the function defined by `\x. f x - g x` is equal to the `i`-th Fourier coefficient of `f` minus the `i`-th Fourier coefficient of `g`.

### Informal sketch
The proof proceeds by:
- Expanding the definition of `fourier_coefficient` to `orthonormal_coefficient` applied to the `l2product` of the function with the appropriate trigonometric basis function.
- Using the fact that the trigonometric basis functions are integrable, specifically `TRIGONOMETRIC_SET_MUL_INTEGRABLE`
- Applying the distributive property of subtraction over real integrals, `REAL_SUB_LDISTRIB` and `REAL_INTEGRAL_SUB`.

### Mathematical insight
This theorem demonstrates the linearity of the Fourier coefficient operator, specifically with respect to subtraction. This property is crucial for simplifying calculations and analyzing linear combinations of functions in Fourier analysis.

### Dependencies
- Definitions: `fourier_coefficient`, `orthonormal_coefficient`, `l2product`
- Theorems: `TRIGONOMETRIC_SET_MUL_INTEGRABLE`, `REAL_SUB_LDISTRIB`, `REAL_INTEGRAL_SUB`


---

## FOURIER_COEFFICIENT_CONST

### Name of formal statement
FOURIER_COEFFICIENT_CONST

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_COEFFICIENT_CONST = prove
 (`!c i. fourier_coefficient (\x. c) i =
         if i = 0 then c * sqrt(&2 * pi) else &0`,
  GEN_TAC THEN MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
  REWRITE_TAC[fourier_coefficient; orthonormal_coefficient; l2product;
              trigonometric_set] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPEC `0` HAS_REAL_INTEGRAL_COS_NX) THEN
    DISCH_THEN(MP_TAC o SPEC `inv(sqrt(&2 * pi)) * c` o
     MATCH_MP HAS_REAL_INTEGRAL_RMUL) THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
    MATCH_MP_TAC(REAL_FIELD
     `&0 < s /\ s pow 2 = &2 * pi ==> &2 * pi * inv(s) * c = c * s`) THEN
    SIMP_TAC[SQRT_POW_2; REAL_LT_MUL; REAL_LE_MUL; REAL_POS; REAL_OF_NUM_LT;
             ARITH; SQRT_POS_LT; PI_POS; REAL_LT_IMP_LE];
    X_GEN_TAC `n:num` THEN
    MP_TAC(ISPEC `n + 1` HAS_REAL_INTEGRAL_SIN_NX) THEN
    DISCH_THEN(MP_TAC o SPEC `inv(sqrt pi) * c` o
      MATCH_MP HAS_REAL_INTEGRAL_RMUL) THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC; REAL_MUL_LZERO] THEN
    REWRITE_TAC[ADD_EQ_0; ARITH_EQ; REAL_INTEGRAL_UNIQUE];
     X_GEN_TAC `n:num` THEN
    MP_TAC(ISPEC `n + 1` HAS_REAL_INTEGRAL_COS_NX) THEN
    DISCH_THEN(MP_TAC o SPEC `inv(sqrt pi) * c` o
      MATCH_MP HAS_REAL_INTEGRAL_RMUL) THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC; REAL_MUL_LZERO] THEN
    REWRITE_TAC[ADD_EQ_0; ARITH_EQ; REAL_INTEGRAL_UNIQUE; REAL_MUL_LZERO]]);;
```
### Informal statement
For all real numbers `c` and all integers `i`, the `fourier_coefficient` of the constant function that always returns `c`, evaluated at `i`, is equal to `c * sqrt(&2 * pi)` if `i` is 0, and `0` otherwise.

### Informal sketch
The proof proceeds by induction on whether the integer `i` is even or odd, using `ODD_EVEN_INDUCT_LEMMA`.
- First, the definitions of `fourier_coefficient`, `orthonormal_coefficient`, `l2product`, and `trigonometric_set` are expanded. This expresses the `fourier_coefficient` in terms of integrals.
- Then, the proof splits into two subgoals, one for `i = 0` and another for `i <> 0`.
- When `i = 0`:
    - The integral of `cos(0*x)` is evaluated using `HAS_REAL_INTEGRAL_COS_NX` which is instantiated with `0`.
    - Some algebraic manipulation using `REAL_FIELD` simplify the equation.
    - Finally, the goal is simplified using facts about square roots and inequalities.
- When `i <> 0`:
    - For non-zero `i`, even and odd cases are considered separately using `X_GEN_TAC` which introduces a natural number `n`.
        - For the sine case (odd parity): the integral of `sin((n+1)*x)` is considered via `HAS_REAL_INTEGRAL_SIN_NX`. Then arithmetic simplifications, and `REAL_INTEGRAL_UNIQUE` reduce the goal to reflexivity.
        - Similarly, For the cosine case (even parity): the integral of `cos((n+1)*x)` is considered via `HAS_REAL_INTEGRAL_COS_NX`. Then arithmetic simplifications, and `REAL_INTEGRAL_UNIQUE` reduce the goal to reflexivity.

### Mathematical insight
This theorem characterizes the Fourier series of constant functions. It shows that the only non-zero Fourier coefficient of a constant function `c` is the coefficient corresponding to the constant term (i.e., the 0th coefficient), and its value is `c * sqrt(2 * pi)`. This arises because the constant function is orthogonal to all sinusoidal functions in the Fourier basis. This is a fundamental property related to the orthogonality of the Fourier basis functions.

### Dependencies
- Definitions: `fourier_coefficient`, `orthonormal_coefficient`, `l2product`, `trigonometric_set`
- Theorems: `ODD_EVEN_INDUCT_LEMMA`, `HAS_REAL_INTEGRAL_COS_NX`, `HAS_REAL_INTEGRAL_SIN_NX`, `HAS_REAL_INTEGRAL_RMUL`, `REAL_INTEGRAL_UNIQUE`, `SQRT_POW_2`, `REAL_LT_MUL`, `REAL_LE_MUL`, `REAL_POS`, `REAL_OF_NUM_LT`, `ARITH`, `SQRT_POS_LT`, `PI_POS`, `REAL_LT_IMP_LE`, `ADD_EQ_0`, `ARITH_EQ`, `REAL_MUL_LZERO`
- Other: `REAL_FIELD` (a decision procedure)

### Porting notes (optional)
- The proof relies heavily on real analysis facts. Ensure the target proof assistant has a robust library for real analysis, including integration.
- The tactic `REAL_FIELD` is a decision procedure in HOL Light. It will need either to be replaced with existing field decision procedures or omitted and the goal proved manually via field tactics.
- The `HAS_REAL_INTEGRAL_*` family of theorems is specific to HOL Light's real analysis library, so equivalents will have to be found or derived.


---

## REAL_PERIODIC_INTEGER_MULTIPLE

### Name of formal statement
REAL_PERIODIC_INTEGER_MULTIPLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_PERIODIC_INTEGER_MULTIPLE = prove
 (`!f:real->real a.
        (!x. f(x + a) = f x) <=> (!x n. integer n ==> f(x + n * a) = f x)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC; MESON_TAC[INTEGER_CLOSED; REAL_MUL_LID]] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!x n. f(x + &n * a) = (f:real->real) x` ASSUME_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB;
                    REAL_ADD_ASSOC; REAL_MUL_LID];
    REWRITE_TAC[INTEGER_CASES] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[REAL_ARITH `(x + -- &n * a) + &n * a = x`]]);;
```
### Informal statement
For any function `f` from real numbers to real numbers and any real number `a`, the function `f` is periodic with period `a` (i.e., `f(x + a) = f(x)` for all `x`) if and only if for all real numbers `x` and all integers `n`, `f(x + n * a) = f(x)`.

### Informal sketch
The proof proceeds as follows:
- The proof starts by stripping the quantifiers and reducing the equivalence to two implications.
- The first implication, from periodicity with period `a` to `f(x + n * a) = f(x)` for all integers `n`, is proved using mathematical induction on `n`.
  - The base case `n = 0` is handled using the fact that 0 is the multiplicative identity.
  - The inductive step uses the periodicity assumption `f(x + a) = f(x)` and the algebraic properties of real numbers and integers in the form `f(x + (n+1)*a) = f(x + n*a + a) = f(x + n*a) = f(x)`.
- The second implication, from `f(x + n * a) = f(x)` for all integers `n` to periodicity with period `a`, is shown by instantiating `n` with 1. The fact that 1 is an integer is handled by `INTEGER_CASES`.
  - In detail, the antecedent `!x n. integer n ==> f(x + &n * a) = f x` is discharged with `n` instantiated by 1.
  - To deduce `f(x+a) = f(x)` from `f(x + 1 * a) = f(x)`, we need to prove `integer 1`.

### Mathematical insight
This theorem formalizes the intuitive notion that if a function is periodic with period `a`, then it is also periodic with any integer multiple of `a`. This is a fundamental property used, for example, when integrating periodic functions, allowing one to shift the integration origin by integer multiples of the period.

### Dependencies
- `INTEGER_CLOSED`: States that the set of integers is closed under addition and multiplication.
- `REAL_MUL_LID`: States that 1 is the left identity for real number multiplication.
- `REAL_MUL_LZERO`: States that 0 is the multiplicative annihilator for multiplication.
- `REAL_ADD_RID`: States that 0 is the right identity for real number addition.
- `REAL_ADD_RDISTRIB`: The right distributive property of real number multiplication over addition.
- `REAL_ADD_ASSOC`: States that real number addition is associative.
- `GSYM REAL_OF_NUM_SUC`: An equality that allows rewriting `REAL_OF_NUM (SUC n)` to `&(SUC n)`.
- `INTEGER_CASES`: This theorem allows one to consider the cases where an integer is zero, positive, or negative.
- `REAL_ARITH`: Used to solve some real arithmetic goals, in particular `(x + -- &n * a) + &n * a = x`.


---

## HAS_REAL_INTEGRAL_OFFSET

### Name of formal statement
HAS_REAL_INTEGRAL_OFFSET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HAS_REAL_INTEGRAL_OFFSET = prove
 (`!f i a b c. (f has_real_integral i) (real_interval[a,b])
                ==> ((\x. f(x + c)) has_real_integral i)
                    (real_interval[a - c,b - c])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPECL [`&1`; `c:real`] o
   MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_REAL_INTEGRAL_AFFINITY)) THEN
  REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ; REAL_MUL_LID; REAL_INV_1] THEN
  REWRITE_TAC[REAL_ABS_1; REAL_MUL_LID; REAL_INV_1] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[IN_REAL_INTERVAL; EXISTS_REFL;
              REAL_ARITH `x - c:real = y <=> x = y + c`] THEN
  REAL_ARITH_TAC);;
```
### Informal statement
For all functions `f` of type `real -> real`, for all functions `i` of type `real -> bool`, and for all real numbers `a`, `b`, and `c`, if `f` has real integral `i` on the real interval `[a, b]`, then the function defined by `\x. f(x + c)` has real integral `i` on the interval `[a - c, b - c]`.

### Informal sketch
The proof proceeds as follows:
- Assume `f` has real integral `i` on `[a, b]`.
- Specialize the theorem `HAS_REAL_INTEGRAL_AFFINITY` with the affine transformation `\x. x + c`, and the interval. This yields that `(\x. f(x + c))` has real integral `i'` over interval `[a-c, b-c]`, where `i'` is related to `i`.
- Simplify using `REAL_OF_NUM_EQ`, `ARITH_EQ`, `REAL_MUL_LID`, `REAL_INV_1`, `REAL_ABS_1`. This simplifies expressions involving real numbers.
- Apply `EQ_IMP` and `AP_TERM_TAC` to show that the integrals `i` and `i'` are the same.
-  Use `SURJECTIVE_IMAGE_EQ` to relate the integral transformation. 
- Simplify using `IN_REAL_INTERVAL` and `EXISTS_REFL`, and use `REAL_ARITH` to show `x - c:real = y <=> x = y + c`.
- Finally, use `REAL_ARITH_TAC` to complete the proof.

### Mathematical insight
This theorem states that if a function `f` has a real integral `i` over an interval `[a, b]`, then shifting the function horizontally by `c` results in a new function `f(x + c)` that has the same real integral `i` over the shifted interval `[a - c, b - c]`. This reflects the translation invariance property of integration.

### Dependencies
- `HAS_REAL_INTEGRAL_AFFINITY`
- `REAL_OF_NUM_EQ`
- `ARITH_EQ`
- `REAL_MUL_LID`
- `REAL_INV_1`
- `REAL_ABS_1`
- `EQ_IMP`
- `SURJECTIVE_IMAGE_EQ`
- `IN_REAL_INTERVAL`
- `EXISTS_REFL`

### Porting notes (optional)
- The theorem relies heavily on the properties of real numbers and affine transformations. Ensure that the target proof assistant has similar libraries and theorems available.
- The `REAL_ARITH_TAC` tactic is used for simplifying real arithmetic expressions. The porter should use equivalent tactics or decision procedures in the target proof assistant.
- The definition `HAS_REAL_INTEGRAL` and related definitions (`real_interval`) must be ported first.


---

## HAS_REAL_INTEGRAL_PERIODIC_OFFSET_LEMMA

### Name of formal statement
HAS_REAL_INTEGRAL_PERIODIC_OFFSET_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HAS_REAL_INTEGRAL_PERIODIC_OFFSET_LEMMA = prove
 (`!f i a b c.
        (!x. f(x + (b - a)) = f(x)) /\
        (f has_real_integral i) (real_interval[a,a+c])
        ==> (f has_real_integral i) (real_interval[b,b+c])`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM
    (MP_TAC o SPEC `a - b:real` o MATCH_MP HAS_REAL_INTEGRAL_OFFSET) THEN
  REWRITE_TAC[REAL_ARITH
   `a - (a - b):real = b /\ (a + c) - (a - b) = b + c`] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_REAL_INTEGRAL_EQ) THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x + a - b:real`) THEN
  REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN REAL_ARITH_TAC);;
```
### Informal statement
For all functions `f` from real numbers to real numbers, all functions `i` from real numbers to real numbers, and all real numbers `a`, `b`, and `c`, if the following two conditions hold:
1. For all real numbers `x`, `f(x + (b - a))` is equal to `f(x)`.
2. `f` has a real integral `i` on the real interval `[a, a + c]`.

Then `f` has a real integral `i` on the real interval `[b, b + c]`.

### Informal sketch
The goal is to prove that if a function `f` is periodic with period `b - a` and has a real integral `i` on the interval `[a, a + c]`, then it has the same real integral `i` on the interval `[b, b + c]`.

- The proof starts by stripping the quantifiers and assumptions using `REPEAT STRIP_TAC`.
- Specialize the theorem `HAS_REAL_INTEGRAL_OFFSET` with `a - b:real` and use it with the assumption involving `f has_real_integral i`. This application offsets the integral to a new interval by effectively performing a change of variables.
- Simplify real arithmetic expressions `a - (a - b):real = b /\ (a + c) - (a - b) = b + c` with `REWRITE_TAC[REAL_ARITH ...]`.
- Apply the definition of equality of real integrals using `MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_REAL_INTEGRAL_EQ)`.
- Introduce a universal quantifier over `x:real` and discharge the goal.
- Instantiate the quantified assumption on periodicity with `x + a - b:real`.
- Rewrite using the periodicity assumption and then perform substitution.
- Apply the function to a term and perform real arithmetic simplification to finish the proof.

### Mathematical insight
This theorem states that if a function is periodic, its integral over an interval of a certain length is invariant under shifts corresponding to integer multiples of the period.

### Dependencies
- `HAS_REAL_INTEGRAL_OFFSET`
- `HAS_REAL_INTEGRAL_EQ`

### Porting notes (optional)
The real arithmetic simplification steps might require adjustments depending on the capabilities of the target proof assistant. The handling of real intervals also needs to be considered.


---

## HAS_REAL_INTEGRAL_PERIODIC_OFFSET_POS

### Name of formal statement
HAS_REAL_INTEGRAL_PERIODIC_OFFSET_POS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HAS_REAL_INTEGRAL_PERIODIC_OFFSET_POS = prove
 (`!f i a b c.
        (!x. f(x + (b - a)) = f x) /\ &0 <= c /\ a + c <= b /\
        (f has_real_integral i) (real_interval[a,b])
        ==> ((\x. f(x + c)) has_real_integral i)
             (real_interval[a,b])`,
  let tac =
    REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `real_interval[a,b]` THEN
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[real_integrable_on]; ASM_REAL_ARITH_TAC] in
  REPEAT STRIP_TAC THEN
  CONJUNCTS_THEN SUBST1_TAC
   (REAL_ARITH `a:real = (a + c) - c /\ b = (b + c) - c`) THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_OFFSET THEN
  SUBGOAL_THEN
   `((f has_real_integral (real_integral(real_interval[a,a+c]) f))
     (real_interval[a,a+c]) /\
     (f has_real_integral (real_integral(real_interval[a+c,b]) f))
     (real_interval[a+c,b])) /\
    ((f has_real_integral (real_integral(real_interval[a+c,b]) f))
     (real_interval[a+c,b]) /\
     (f has_real_integral (real_integral(real_interval[a,a+c]) f))
     (real_interval[b,b+c]))`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN TRY tac THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_PERIODIC_OFFSET_LEMMA THEN
    EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[] THEN tac;
    DISCH_THEN(CONJUNCTS_THEN(MP_TAC o MATCH_MP
     (REWRITE_RULE[TAUT `a /\ b /\ c /\ d ==> e <=>
                  c /\ d ==> a /\ b ==> e`] HAS_REAL_INTEGRAL_COMBINE))) THEN
    REPEAT(ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC]) THEN
    ASM_MESON_TAC[HAS_REAL_INTEGRAL_UNIQUE; REAL_ADD_SYM]]);;
```
### Informal statement
For all functions `f`, real numbers `i`, `a`, `b`, and `c`, if `f` is periodic with period `b - a` (i.e., for all `x`, `f(x + (b - a)) = f(x)`), `0 <= c`, `a + c <= b`, and `f` has real integral `i` on the real interval `[a, b]`, then the function `f` offset by `c` (i.e., the function that maps `x` to `f(x + c)`) has real integral `i` on the real interval `[a, b]`.

### Informal sketch
The proof proceeds as follows:
- Rewrite the goal using the definition of `has_real_integral` in terms of `real_integral`.
- Use `REAL_INTEGRABLE_ON_SUBINTERVAL` to set up the necessary integrability conditions.
- Introduce the interval `[a, b]` via `EXISTS_TAC`.
- Simplify using `SUBSET_REAL_INTERVAL`.
- Split the goal into subgoals using `CONJ_TAC`.
- Solve the integrability subgoals using `ASM_MESON_TAC` with `real_integrable_on` and `ASM_REAL_ARITH_TAC`.
- Rewrite the subgoal involving integrals by expressing `a` as `(a + c) - c` and `b` as `(b + c) - c`.
- Apply `HAS_REAL_INTEGRAL_OFFSET`.
- Split the interval `[a,b]` into `[a, a+c]` and `[a+c, b]` and then use periodicity along with `HAS_REAL_INTEGRAL_COMBINE`:
  - The first subgoal requires showing that if `f` has real integral `(real_integral(real_interval[a,a+c]) f)` on `real_interval[a,a+c]` and also has real integral `(real_integral(real_interval[a+c,b]) f)` on `real_interval[a+c,b]`, and also has real integral `(real_integral(real_interval[a+c,b]) f)` on `real_interval[a+c,b]` and also real integral `(real_integral(real_interval[a,a+c]) f)` on `real_interval[b,b+c]` then `f` has the integral on the former intervals and on the latter intervals.
  - Prove the above using the periodicity by `HAS_REAL_INTEGRAL_PERIODIC_OFFSET_LEMMA`.
    - Existentially quantify `a` in the lemma and use arithmetic rewriting on the assumptions.
  - Use `HAS_REAL_INTEGRAL_COMBINE` on the remaining subgoals.
    - Repeated calls to `ANTS_TAC` using arithmetic reasoning, `HAS_REAL_INTEGRAL_UNIQUE`, and `REAL_ADD_SYM` to discharge the resulting assumptions.

### Mathematical insight
This theorem states that if a function is periodic and integrable on an interval, then shifting the function by a constant `c` within the appropriate bounds does not change its integral on that interval. This is a useful property when dealing with periodic functions, allowing for simplification in integration calculations.

### Dependencies
- `HAS_REAL_INTEGRAL_INTEGRAL`
- `REAL_INTEGRABLE_ON_SUBINTERVAL`
- `SUBSET_REAL_INTERVAL`
- `real_integrable_on`
- `HAS_REAL_INTEGRAL_OFFSET`
- `HAS_REAL_INTEGRAL_PERIODIC_OFFSET_LEMMA`
- `HAS_REAL_INTEGRAL_COMBINE`
- `HAS_REAL_INTEGRAL_UNIQUE`
- `REAL_ADD_SYM`


---

## HAS_REAL_INTEGRAL_PERIODIC_OFFSET_WEAK

### Name of formal statement
HAS_REAL_INTEGRAL_PERIODIC_OFFSET_WEAK

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HAS_REAL_INTEGRAL_PERIODIC_OFFSET_WEAK = prove
 (`!f i a b c.
        (!x. f(x + (b - a)) = f x) /\ abs(c) <= b - a /\
        (f has_real_integral i) (real_interval[a,b])
        ==> ((\x. f(x + c)) has_real_integral i)
             (real_interval[a,b])`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 <= c` THENL
   [MATCH_MP_TAC HAS_REAL_INTEGRAL_PERIODIC_OFFSET_POS THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`\x. (f:real->real)(--x)`; `i:real`;
                   `--b:real`; `--a:real`; `--c:real`]
          HAS_REAL_INTEGRAL_PERIODIC_OFFSET_POS) THEN
    ASM_REWRITE_TAC[REAL_NEG_ADD; HAS_REAL_INTEGRAL_REFLECT] THEN
    REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    X_GEN_TAC `x:real` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `--x + (a - b):real`) THEN
    REWRITE_TAC[REAL_ARITH `--(--a - --b):real = a - b`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN REAL_ARITH_TAC]);;
```

### Informal statement
For any function `f` from real numbers to real numbers, any real number `i`, and any real numbers `a`, `b`, and `c`, if `f` is periodic with period `b - a` (i.e., for all `x`, `f(x + (b - a)) = f(x)`), and the absolute value of `c` is less than or equal to `b - a`, and `f` has a real integral `i` on the interval `[a, b]`, then the function `\x. f(x + c)` has a real integral `i` on the interval `[a, b]`.

### Informal sketch
The proof proceeds by cases on whether `0 <= c`.

- Case `0 <= c`: Apply the theorem `HAS_REAL_INTEGRAL_PERIODIC_OFFSET_POS`. Then rewrite and use real arithmetic to complete the proof.

- Case `not (0 <= c)`: Instantiate `HAS_REAL_INTEGRAL_PERIODIC_OFFSET_POS` with `-x` for `x`, `i` for `i`, `-b` for `b`, `-a` for `a`, and `-c` for `c`. Rewrite using `REAL_NEG_ADD` and `HAS_REAL_INTEGRAL_REFLECT`. Rewrite using `REAL_NEG_NEG`. Discharge an assumption and apply a substitution based on symmetry. Apply an arithmetic simplification tactic. Perform variable generalization with `x`. Instantiate an assumption about periodicity and rewrite using `REAL_ARITH` to produce the final required result.

### Mathematical insight
This theorem states that if a function `f` has a real integral over an interval `[a, b]` and is periodic with period `b - a`, then shifting the function by a constant `c` whose absolute value is bounded by the period does not change the value of the integral over the same interval. This is a useful property when dealing with periodic functions and their integrals.

### Dependencies
- `HAS_REAL_INTEGRAL_PERIODIC_OFFSET_POS`
- `REAL_NEG_ADD`
- `HAS_REAL_INTEGRAL_REFLECT`
- `REAL_NEG_NEG`
- `REAL_ARITH`


---

## HAS_REAL_INTEGRAL_PERIODIC_OFFSET

### Name of formal statement
HAS_REAL_INTEGRAL_PERIODIC_OFFSET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HAS_REAL_INTEGRAL_PERIODIC_OFFSET = prove
 (`!f i a b c.
        (!x. f(x + (b - a)) = f x) /\
        (f has_real_integral i) (real_interval[a,b])
        ==> ((\x. f(x + c)) has_real_integral i) (real_interval[a,b])`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC (REAL_ARITH `b <= a \/ a < b`) THEN
  ASM_SIMP_TAC[HAS_REAL_INTEGRAL_NULL_EQ] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\x. f(x + (b - a) * frac(c / (b - a)))) has_real_integral i)
    (real_interval[a,b])`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_REAL_INTEGRAL_PERIODIC_OFFSET_WEAK THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH
     `a < b /\ (b - a) * f < (b - a) * &1
      ==> abs(b - a) * f <= b - a`) THEN
    ASM_SIMP_TAC[REAL_SUB_LT; REAL_LT_LMUL_EQ] THEN
    ASM_REWRITE_TAC[real_abs; FLOOR_FRAC];
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_REAL_INTEGRAL_EQ) THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN REWRITE_TAC[FRAC_FLOOR] THEN
    ASM_SIMP_TAC[REAL_FIELD
     `a < b ==> x + (b - a) * (c / (b - a) - f) =
                (x + c) + --f * (b - a)`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_PERIODIC_INTEGER_MULTIPLE]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMP_TAC[INTEGER_CLOSED; FLOOR]]);;
```
### Informal statement
For all functions `f:real->real`, real numbers `i`, `a`, `b`, and `c`, if `f` is periodic with period `b - a` (i.e., for all `x`, `f(x + (b - a)) = f(x)`) and `f` has a real integral `i` over the real interval `[a, b]`, then the function `\x. f(x + c)` also has the real integral `i` over the real interval `[a, b]`.

### Informal sketch
The proof proceeds by:
- Considering the cases where `b <= a` or `a < b`. If `b <= a`, then the real interval is null, and the result follows directly from `HAS_REAL_INTEGRAL_NULL_EQ`.
- Assuming `a < b`, then we need to show that the integral of `\x. f(x + c)` over `[a, b]` is `i`.
- The key step is to show that  `(\x. f(x + (b - a) * frac(c / (b - a))))` has real integral `i` over `[a,b]`, where `frac(x)` is the fractional part of `x`. This is justified using `HAS_REAL_INTEGRAL_PERIODIC_OFFSET_WEAK`.
- We then reduce this to show `\x. f(x + c)` has the same real integral. For this we use `HAS_REAL_INTEGRAL_EQ`.
- The heart of the proof is using the periodicity of `f`. Note that `c` can be decomposed into an integer multiple of the period `b-a` plus a fractional part. Namely, `c = (b-a) * (c / (b-a)) = (b-a) * (floor(c/(b-a)) + frac(c/(b-a)))`. Thus, `f(x + c) = f(x + (b-a) * floor(c/(b-a)) + (b-a) * frac(c/(b-a))) = f(x + (b-a) * frac(c/(b-a)))` because `f` is periodic and `floor(c/(b-a))` is an integer.

### Mathematical insight
This theorem states that the real integral of a periodic function over an interval is invariant under horizontal translations of the function. This is a fundamental property used in numerous applications, especially those that involve Fourier analysis or dealing with periodic phenomena. Shifting the function does not change its integral over a period.

### Dependencies
- `HAS_REAL_INTEGRAL_NULL_EQ`: States that the integral over a null interval is the value 0.
- `HAS_REAL_INTEGRAL_PERIODIC_OFFSET_WEAK`: Deals with periodicity and integrals with offsets.
- `HAS_REAL_INTEGRAL_EQ`: Is the definition which states what it means for a function to have an integral over a given interval.
- `REAL_ABS_MUL`: States that `abs(x * y) = abs(x) * abs(y)`.
- `REAL_SUB_LT`: States that `x < y` is equivalent to `0 < y - x`.
- `REAL_LT_LMUL_EQ`: States that if `0 < x` and `x * y < x * z`, then `y < z`.
- `real_abs`: Definition of the absolute value of a real number
- `FLOOR_FRAC`: Characterizes relationship between floor and fractional part of a number: `x = floor(x) + frac(x)
- `IMP_CONJ`:  `p ==> q /\ r` is equivalent to `(p ==> q) /\ (p ==> r)`
- `FRAC_FLOOR`:  Related to the definition of fraction and floor.
- `REAL_FIELD ...`: Basic algebraic manipulation laws in the field of real numbers.
- `REAL_PERIODIC_INTEGER_MULTIPLE`: The statement of the periodicity property. States that `f(x + n * period) = f x`
- `INTEGER_CLOSED`: States that the floor function returns an integer.


---

## REAL_INTEGRABLE_PERIODIC_OFFSET

### Name of formal statement
REAL_INTEGRABLE_PERIODIC_OFFSET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_INTEGRABLE_PERIODIC_OFFSET = prove
 (`!f a b c.
        (!x. f(x + (b - a)) = f x) /\
        f real_integrable_on real_interval[a,b]
        ==> (\x. f(x + c)) real_integrable_on real_interval[a,b]`,
  REWRITE_TAC[real_integrable_on] THEN
  MESON_TAC[HAS_REAL_INTEGRAL_PERIODIC_OFFSET]);;
```
### Informal statement
For all real-valued functions `f` and real numbers `a`, `b`, and `c`, if `f` is periodic with period `b - a` (i.e., for all `x`, `f(x + (b - a)) = f(x)`) and `f` is real-integrable on the real interval `[a, b]`, then the function `λx. f(x + c)` is also real-integrable on the real interval `[a, b]`.

### Informal sketch
The proof hinges on showing that if a function `f` is periodic with period `b - a` and integrable on the interval `[a, b]`, then shifting the function by a constant `c` results in another integrable function on the same interval.

- The proof starts by rewriting the goal using the definition of `real_integrable_on`. Then `MESON_TAC` is used with `HAS_REAL_INTEGRAL_PERIODIC_OFFSET`, which likely contains the core argument showing that periodicity and integrability are preserved under translation.

### Mathematical insight
This theorem states that if a periodic function is integrable over an interval, a horizontal shift of that function will also be integrable over the same interval. This is a fundamental property used when dealing with periodic functions in integration.

### Dependencies
- Definitions: `real_integrable_on`
- Theorems: `HAS_REAL_INTEGRAL_PERIODIC_OFFSET`


---

## ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET

### Name of formal statement
ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET = prove
 (`!f a b c.
        (!x. f(x + (b - a)) = f x) /\
        f absolutely_real_integrable_on real_interval[a,b]
        ==> (\x. f(x + c)) absolutely_real_integrable_on real_interval[a,b]`,
  REWRITE_TAC[absolutely_real_integrable_on] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(GEN `f:real->real` (SPEC_ALL REAL_INTEGRABLE_PERIODIC_OFFSET)) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;
```

### Informal statement
For all real-valued functions `f`, real numbers `a`, `b`, and `c`, if `f` is periodic with period `b - a` (i.e., for all `x`, `f(x + (b - a)) = f(x)`) and `f` is absolutely real integrable on the real interval `[a, b]`, then the function defined by `λx. f(x + c)` is also absolutely real integrable on the real interval `[a, b]`.

### Informal sketch
The proof proceeds as follows:
- Start by rewriting using the definition of `absolutely_real_integrable_on`.
- Strip the quantifiers and implications.
- Apply a generalization (with respect to `f`) and specialization of the theorem `REAL_INTEGRABLE_PERIODIC_OFFSET`.
- Use discharging and matching to apply the specialized `REAL_INTEGRABLE_PERIODIC_OFFSET` theorem.
- Apply assumption rewriting to complete the proof.

### Mathematical insight
This theorem states that if a function is absolutely integrable on a given interval and periodic, then any horizontal shift of the function remains absolutely integrable on the same interval. This is a useful property when dealing with periodic functions and integration.

### Dependencies
- `absolutely_real_integrable_on`
- `REAL_INTEGRABLE_PERIODIC_OFFSET`

### Porting notes (optional)
The theorem `REAL_INTEGRABLE_PERIODIC_OFFSET` is a crucial dependency, and its proof may need to be adapted to the specific features of the target proof assistant. The core argument relies on the properties of absolute integrability and periodicity, concepts that are generally well-supported across various systems.


---

## REAL_INTEGRAL_PERIODIC_OFFSET

### Name of formal statement
REAL_INTEGRAL_PERIODIC_OFFSET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_INTEGRAL_PERIODIC_OFFSET = prove
 (`!f a b c.
        (!x. f(x + (b - a)) = f x) /\
        f real_integrable_on real_interval[a,b]
        ==> real_integral (real_interval[a,b]) (\x. f(x + c)) =
            real_integral (real_interval[a,b]) f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_PERIODIC_OFFSET THEN
  ASM_REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL]);;
```
### Informal statement
For any function `f`, real numbers `a`, `b`, and `c`, if `f` is periodic with period `b - a` (i.e., for all `x`, `f(x + (b - a)) = f x`) and `f` is real integrable on the real interval `[a, b]`, then the real integral of `f(x + c)` on the real interval `[a, b]` is equal to the real integral of `f` on the real interval `[a, b]`.

### Informal sketch
The proof proceeds as follows:
- The goal is to prove the equality of two real integrals.
- Use `REAL_INTEGRAL_UNIQUE` to reduce the problem to showing that both integrals have the same `HAS_REAL_INTEGRAL` value.
- Use the theorem `HAS_REAL_INTEGRAL_PERIODIC_OFFSET` to show that `real_integral (real_interval[a,b]) (\x. f(x + c))` has the same `HAS_REAL_INTEGRAL` value as `real_integral (real_interval[a,b]) f`.
- Apply `HAS_REAL_INTEGRAL_INTEGRAL` and rewrite using `GSYM` to complete the proof.

### Mathematical insight
This theorem states that the definite integral of a periodic function over an interval equal to its period is invariant under horizontal translation. This is a useful property in Fourier analysis and other areas where periodic functions arise.

### Dependencies
- `REAL_INTEGRAL_UNIQUE`
- `HAS_REAL_INTEGRAL_PERIODIC_OFFSET`
- `HAS_REAL_INTEGRAL_INTEGRAL`


---

## FOURIER_OFFSET_TERM

### Name of formal statement
FOURIER_OFFSET_TERM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_OFFSET_TERM = prove
 (`!f n t. f absolutely_real_integrable_on real_interval[--pi,pi] /\
           (!x. f(x + &2 * pi) = f x)
           ==> fourier_coefficient (\x. f(x + t)) (2 * n + 2) *
               trigonometric_set (2 * n + 2) (&0) =
               fourier_coefficient f (2 * n + 1) *
               trigonometric_set (2 * n + 1) t +
               fourier_coefficient f (2 * n + 2) *
               trigonometric_set (2 * n + 2) t`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[trigonometric_set; fourier_coefficient;
              orthonormal_coefficient] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC; GSYM REAL_ADD_RDISTRIB] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_MUL_RZERO; COS_0; REAL_MUL_RID] THEN
  REWRITE_TAC[l2product] THEN
  REWRITE_TAC[REAL_ARITH `(a * b) * c:real = b * a * c`] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_LMUL; GSYM REAL_INTEGRAL_RMUL;
                FOURIER_PRODUCTS_INTEGRABLE_STRONG; GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a * b * c:real = (a * c) * b`] THEN
  REWRITE_TAC[REAL_MUL_SIN_SIN; REAL_MUL_COS_COS] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; GSYM REAL_ADD_LDISTRIB] THEN
  W(MP_TAC o PART_MATCH (rand o rand) REAL_INTEGRAL_ADD o
     rand o rand o snd) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC REAL_MEASURABLE_ON_MEASURABLE_SUBSET THEN
       EXISTS_TAC `(:real)` THEN
       REWRITE_TAC[REAL_MEASURABLE_REAL_INTERVAL; SUBSET_UNIV] THEN
       MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
       MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
       REWRITE_TAC[ETA_AX; IN_UNIV; REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
       SPEC_TAC(`n:num`,`n:num`) THEN MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
       REWRITE_TAC[trigonometric_set; real_div] THEN
       REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC;
       ASM_REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN EXISTS_TAC `&1` THEN
       REPEAT STRIP_TAC THEN REWRITE_TAC[real_sub] THEN
       MATCH_MP_TAC(REAL_ARITH
        `abs x <= &1 /\ abs y <= &1 ==> abs((x + y) / &2) <= &1`) THEN
       REWRITE_TAC[SIN_BOUND; COS_BOUND; REAL_ABS_NEG]]);
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[REAL_ARITH
   `(cm - cp) / &2 * f + (cm + cp) / &2 * f = cm * f`] THEN
  MP_TAC(ISPECL
   [`\x. cos(&(n + 1) * (x - t)) * f x`;
    `real_integral (real_interval[--pi,pi])
                   (\x. cos(&(n + 1) * (x - t)) * f x)`;
    `--pi`; `pi`; `t:real`] HAS_REAL_INTEGRAL_PERIODIC_OFFSET) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\x. cos (&(n + 1) * (x - t)) * f x) real_integrable_on
    real_interval[--pi,pi]`
  MP_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_MEASURABLE_ON_MEASURABLE_SUBSET THEN
      EXISTS_TAC `(:real)` THEN
      REWRITE_TAC[REAL_MEASURABLE_REAL_INTERVAL; SUBSET_UNIV] THEN
      MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
      REWRITE_TAC[ETA_AX; IN_UNIV; REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
      SPEC_TAC(`n:num`,`n:num`) THEN MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
      REWRITE_TAC[trigonometric_set; real_div] THEN
      REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC;
      ASM_REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN EXISTS_TAC `&1` THEN
      REWRITE_TAC[COS_BOUND]];
    REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRAL] THEN DISCH_TAC] THEN
  ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN ANTS_TAC THENL
   [REWRITE_TAC[REAL_ARITH
     `n * ((x + &2 * pi) - t) = (&2 * n) * pi + n * (x - t)`] THEN
    REWRITE_TAC[COS_ADD; SIN_NPI; COS_NPI; REAL_OF_NUM_MUL] THEN
    REWRITE_TAC[REAL_POW_NEG; REAL_MUL_LZERO; EVEN_MULT; ARITH] THEN
    REWRITE_TAC[REAL_POW_ONE; REAL_SUB_RZERO; REAL_MUL_LID];
    REWRITE_TAC[REAL_ARITH `(x + t) - t:real = x`] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(a * b) * c:real = a * c * b`] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN ASM_REWRITE_TAC[]]);;
```

### Informal statement
For any real-valued function `f` and any natural number `n` and real number `t`, if `f` is absolutely real integrable on the real interval from `-pi` to `pi`, and `f(x + 2*pi) = f x` for all `x`, then the Fourier coefficient of the function `\x. f(x + t)` at `2 * n + 2` times the trigonometric set `trigonometric_set (2 * n + 2) 0= &0` is equal to the Fourier coefficient of `f` at `2 * n + 1` times the trigonometric set `trigonometric_set` at `t` plus the Fourier coefficient of `f` at `2 * n + 2` times the trigonometric set `trigonometric_set` at `t`.

### Informal sketch
The proof proceeds as follows:
- Start by stripping the quantifiers and assumptions.
- Rewrite using the definitions of `trigonometric_set`, `fourier_coefficient`, and `orthonormal_coefficient`.
- Apply arithmetic simplification steps, including distributing multiplication over addition and using the identity `a * 0 = 0`, `cos 0 = 1`, and `a * 1 = a`.
- Rewrite with the definition of `l2product`.
- Rearrange the order of multiplication.
- Simplify the integral using the linearity of the integral and properties of `FOURIER_PRODUCTS_INTEGRABLE_STRONG`.
- Rewrite to rearrange the multiplication order.
- Rewrite using trigonometric identities for `sin(a) * sin(b)` and `cos(a) * cos(b)`.
- Distribute subtraction and addition.
- Use the fact that the integral of the sum is the sum of the integrals.
- Apply the theorem that shows the integral is periodic: `HAS_REAL_INTEGRAL_PERIODIC_OFFSET`
- Show integrability of the cosine term times `f x`, by showing absolute real integrability then using the theorem stating that absolutely real integrable functions are integrable, and showing the product of absolutely integrable functions is also integrable.
- Simplify using the assumption that `pi - --pi = 2 * pi` and show `cos(&(n + 1) * ((x + &2 * pi) - t)) = cos(&(n + 1) * (x - t))`.
- Finally, conclude.

### Mathematical insight
The theorem `FOURIER_OFFSET_TERM` provides a relationship between the Fourier coefficients of a periodic function `f` and a phase-shifted version of the same function. This is a crucial result in Fourier analysis, as it allows us to easily compute the Fourier coefficients of shifted functions, given the Fourier coefficients of the original function.

### Dependencies
- `trigonometric_set`
- `fourier_coefficient`
- `orthonormal_coefficient`
- `l2product`
- `FOURIER_PRODUCTS_INTEGRABLE_STRONG`
- `REAL_INTEGRAL_LMUL`
- `REAL_INTEGRAL_RMUL`
- `REAL_MUL_SIN_SIN`
- `REAL_MUL_COS_COS`
- `REAL_SUB_LDISTRIB`
- `REAL_ADD_LDISTRIB`
- `REAL_INTEGRAL_ADD`
- `REAL_MEASURABLE_ON_MEASURABLE_SUBSET`
- `CONTINUOUS_IMP_REAL_MEASURABLE_ON`
- `REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON`
- `REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE`
- `REAL_BOUNDED`
- `SIN_BOUND`
- `COS_BOUND`
- `HAS_REAL_INTEGRAL_PERIODIC_OFFSET`
- `HAS_REAL_INTEGRAL_INTEGRAL`
- `COS_ADD`
- `SIN_NPI`
- `COS_NPI`
- `REAL_POW_NEG`
- `REAL_MUL_LZERO`
- `EVEN_MULT`
- `REAL_POW_ONE`
- `REAL_INTEGRAL_UNIQUE`
- `REAL_MUL_ASSOC`
- `ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT`
- `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE`

### Porting notes (optional)
- The proof relies on properties of real integrals and trigonometric functions. Ensure corresponding theorems are available or proved in the target proof assistant.
- The tactic `REAL_DIFFERENTIABLE_TAC` is likely a complex tactic that invokes multiple rules to establish differentiability. The porter must understand how this tactic works in HOL Light to emulate it correctly.


---

## FOURIER_SUM_OFFSET

### Name of formal statement
FOURIER_SUM_OFFSET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_SUM_OFFSET = prove
 (`!f n t.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> sum(0..2*n) (\k. fourier_coefficient f k *
                             trigonometric_set k t) =
            sum(0..2*n) (\k. fourier_coefficient (\x. f (x + t)) k *
                             trigonometric_set k (&0))`,
  REPEAT STRIP_TAC THEN SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES] THEN
  BINOP_TAC THENL
   [REWRITE_TAC[fourier_coefficient; trigonometric_set; l2product;
                orthonormal_coefficient; REAL_MUL_LZERO; COS_0] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(SPECL [`\x:real. &1 / sqrt(&2 * pi) * f x`;
                  `--pi`; `pi`; `t:real`] REAL_INTEGRAL_PERIODIC_OFFSET) THEN
    ASM_SIMP_TAC[REAL_ARITH `pi - --pi = &2 * pi`; REAL_INTEGRABLE_LMUL;
                 ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; SUM_CLAUSES_NUMSEG; ARITH_EQ] THEN
  SUBGOAL_THEN `1..2*n = 2*0+1..(2*(n-1)+1)+1` SUBST1_TAC THENL
   [BINOP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUM_OFFSET; SUM_PAIR] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `(k + 1) + 1 = k + 2`] THEN
  ASM_SIMP_TAC[GSYM FOURIER_OFFSET_TERM] THEN
  REWRITE_TAC[trigonometric_set; REAL_MUL_RZERO; COS_0; SIN_0] THEN
  REAL_ARITH_TAC);;
```

### Informal statement
For any real-valued function `f`, natural number `n`, and real number `t`, if `f` is absolutely real integrable on the real interval `[--pi, pi]` and `f` is periodic with period `2 * pi` (i.e., for all `x`, `f(x + 2 * pi) = f(x)`), then the sum from `0` to `2 * n` of the terms `fourier_coefficient f k * trigonometric_set k t` is equal to the sum from `0` to `2 * n` of the terms `fourier_coefficient (\x. f (x + t)) k * trigonometric_set k 0`.

### Informal sketch
The proof proceeds by induction on `n`.
- The base case `n = 0` is handled directly by simplification using the definitions of `fourier_coefficient` and `trigonometric_set`.
- For the inductive step, assume the theorem holds for `n`. The goal is to prove it for `n + 1`.
  - The sum from `0` to `2 * (n + 1)` is split into the sum from `0` to `2 * n` plus the terms for `2 * n + 1` and `2 * (n + 1)`.
  - The inductive hypothesis is applied to the sum from `0` to `2 * n`.
  - The remaining terms `fourier_coefficient f (2 * n + 1) * trigonometric_set (2 * n + 1) t` and `fourier_coefficient f (2 * (n + 1)) * trigonometric_set (2 * (n + 1)) t` are simplified using the `FOURIER_OFFSET_TERM` lemma and trigonometric identities.
  - The goal is then reduced to showing that the terms for `k = 2 * n + 1` and `k = 2 * n + 2` are equal when evaluated at `t` with the `fourier_coefficient` of `f` and when evaluated at `0` with the `fourier_coefficient` of `\x. f (x + t)`. This equality follows from from the `FOURIER_OFFSET_TERM` lemma.

The proof also relies on the `REAL_INTEGRAL_PERIODIC_OFFSET` theorem to relate the Fourier coefficients of `f(x)` and `f(x + t)`. The `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE` theorem is used to show that absolute real integrability implies real integrability.

### Mathematical insight
This theorem states that shifting the function `f` inside the Fourier coefficient is equivalent to shifting the variable `t` of the trigonometric set. That is, computing the partial Fourier series of the shifted function `f(x + t)` at `0` is the same as computing the partial Fourier series of the original function `f(x)` at `t`. This is a fundamental property of Fourier series related to translation invariance.

### Dependencies
- Theorems:
    - `REAL_INTEGRAL_PERIODIC_OFFSET`
    - `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE`
- Definitions:
    - `fourier_coefficient`
    - `trigonometric_set`
    - `l2product`
    - `orthonormal_coefficient`
- Lemmas:
    - `FOURIER_OFFSET_TERM`

### Porting notes (optional)
- The `REAL_INTEGRAL_PERIODIC_OFFSET` theorem regarding the invariance of the integral under periodic shifts needs to be ported.
- The handling of real integrability and absolute real integrability may differ in other proof assistants.
- The `FOURIER_OFFSET_TERM` lemma will have to be defined or proven in the target system.


---

## FOURIER_SUM_OFFSET_UNPAIRED

### Name of formal statement
FOURIER_SUM_OFFSET_UNPAIRED

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_SUM_OFFSET_UNPAIRED = prove
 (`!f n t.
        f absolutely_real_integrable_on real_interval [--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> sum(0..2*n) (\k. fourier_coefficient f k *
                             trigonometric_set k t) =
            sum(0..n) (\k. fourier_coefficient (\x. f (x + t)) (2 * k) *
                           trigonometric_set (2 * k) (&0))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FOURIER_SUM_OFFSET] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(0..n) (\k. fourier_coefficient (\x. f (x + t)) (2 * k) *
                   trigonometric_set (2 * k) (&0) +
                   fourier_coefficient (\x. f (x + t)) (2 * k + 1) *
                   trigonometric_set (2 * k + 1) (&0))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_PAIR] THEN
    REWRITE_TAC[GSYM ADD1; MULT_CLAUSES; SUM_CLAUSES_NUMSEG; LE_0];
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_EQ_ADD_LCANCEL_0]] THEN
  REWRITE_TAC[ADD1; trigonometric_set; real_div; REAL_MUL_RZERO] THEN
  REWRITE_TAC[SIN_0; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID]);;
```
### Informal statement
For any real-valued function `f` and natural number `n` and real number `t`, if `f` is absolutely real-integrable on the real interval from `-pi` to `pi` and `f` is periodic with period `2*pi` (i.e., for all `x`, `f(x + 2*pi) = f(x)`), then the sum from `k = 0` to `2*n` of the terms `fourier_coefficient f k * trigonometric_set k t` is equal to the sum from `k = 0` to `n` of the terms `fourier_coefficient (\x. f (x + t)) (2 * k) * trigonometric_set (2 * k) 0`.

### Informal sketch
The proof proceeds by simplifying the left-hand side (LHS) involving the `FOURIER_SUM_OFFSET` theorem, then transforming the right-hand side (RHS) to match the simplified LHS.

- Start by stripping the quantifiers and assumptions.
- Apply the theorem `FOURIER_SUM_OFFSET` to the LHS and simplify.
- Perform an equality transformation to introduce an intermediate term on the RHS involving both even and off `fourier_coefficient` along with its `trigonometric_set`
- Rewrite using `SUM_PAIR` to split a sum over `0..2*n` into two sums to allow to match the desired form.
- perform simplification to obtain the desired equality .

### Mathematical insight
This theorem relates the Fourier series of a function `f` evaluated at a point `t` to the Fourier series of the shifted function `f(x + t)` evaluated at `0`. Specifically, it demonstrates an equality between a partial sum of the Fourier series of *f* and a partial sum involving the even-indexed Fourier coefficients of the shifted version of *f*.

### Dependencies
- `FOURIER_SUM_OFFSET`
- `SUM_PAIR`
- `ADD1`
- `MULT_CLAUSES`
- `SUM_CLAUSES_NUMSEG`
- `LE_0`
- `SUM_EQ_NUMSEG`
- `REAL_EQ_ADD_LCANCEL_0`
- `trigonometric_set`
- `real_div`
- `REAL_MUL_RZERO`
- `SIN_0`
- `REAL_MUL_LZERO`
- `REAL_ADD_RID`


---

## dirichlet_kernel

### Name of formal statement
dirichlet_kernel

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let dirichlet_kernel = new_definition
 `dirichlet_kernel n x =
        if x = &0 then &n + &1 / &2
        else sin((&n + &1 / &2) * x) / (&2 * sin(x / &2))`;;
```

### Informal statement
The `dirichlet_kernel` of a natural number `n` and a real number `x` is defined as follows: if `x` is equal to 0, then the result is `n + 1/2`; otherwise, the result is `sin((n + 1/2) * x) / (2 * sin(x / 2))`.

### Informal sketch
The definition of `dirichlet_kernel` is a direct translation of its mathematical definition. It distinguishes between the case where the input `x` is zero, and the case where it is non-zero, because the formula `sin((&n + &1 / &2) * x) / (&2 * sin(x / &2))` has a removable singularity at `x=0`. In the case where `x` is zero, its value is determined by taking the limit as `x` approaches zero, which is `n + 1/2`.

### Mathematical insight
The Dirichlet kernel is a crucial function in Fourier analysis. It's used to represent the partial sums of Fourier series. Specifically, convolving a function with the Dirichlet kernel effectively truncates the function's Fourier series to the first `n` terms. The singularity at zero must be handled explicitly.

### Dependencies
None.

### Porting notes (optional)
- Different proof assistants may have built-in support for trigonometric functions and real numbers but ensure the same level of precision is maintained.
- Pay attention to how each system handles division by zero and removable singularities when implementing the conditional definition. Some systems may require explicit proofs of equivalence for the two cases.
- Ensure that the real numbers `0`, `1`, and `2` are correctly coerced from the natural numbers involved via the embedding function `&`.


---

## DIRICHLET_KERNEL_0

### Name of formal statement
DIRICHLET_KERNEL_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_KERNEL_0 = prove
 (`!x. abs(x) < &2 * pi ==> dirichlet_kernel 0 x = &1 / &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dirichlet_kernel] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_ADD_LID] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; REAL_MUL_SYM; REAL_MUL_RID] THEN
  MATCH_MP_TAC(REAL_FIELD `~(x = &0) ==> inv(&2 * x) * x = inv(&2)`) THEN
  DISCH_TAC THEN SUBGOAL_THEN `~(x * inv(&2) = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; REWRITE_TAC[] THEN MATCH_MP_TAC SIN_EQ_0_PI] THEN
  ASM_REAL_ARITH_TAC);;
```
### Informal statement
For all real numbers `x`, if the absolute value of `x` is less than `2` times `pi`, then the `dirichlet_kernel` of `0` at `x` is equal to `1/2`.

### Informal sketch
The proof proceeds as follows:
- Start by stripping the quantifier and assumption.
- Rewrite using the definition of `dirichlet_kernel`.
- Perform case analysis based on the condition `n = 0` within the definition of `dirichlet_kernel`.
- In the case where `n=0`, simplify using algebraic properties of real numbers, such as `REAL_ADD_LID` (`0 + x = x`).
- Rewrite using properties of real arithmetic, including: `real_div`, `REAL_MUL_LID` (`1 * x = x`), `REAL_MUL_SYM` (`x * y = y * x`), and `REAL_MUL_RID` (`x * 1 = x`).
- Apply the theorem `~(x = &0) ==> inv(&2 * x) * x = inv(&2)`.
  - To apply this theorem, we need to discharge the assumption `~(x * inv(&2) = &0)`.
  - Assume `x * inv(&2) = &0` and derive a contradiction using `ASM_REAL_ARITH_TAC`.
  - Show `~(x = &0)` using `SIN_EQ_0_PI` to show contradiction when `x = 0`.
- Finally, discharge the main assumption using `ASM_REAL_ARITH_TAC`.

### Mathematical insight
This theorem establishes a base case, specifically when `n = 0`, for the Dirichlet kernel. The Dirichlet kernel is a function that plays a crucial role in Fourier analysis, especially in the study of convergence of Fourier series. This case shows that when `n = 0`, the kernel simplifies to a constant value within a certain range.

### Dependencies
- Definitions: `dirichlet_kernel`
- Theorems: `REAL_ADD_LID`, `real_div`, `REAL_MUL_LID`, `REAL_MUL_SYM`, `REAL_MUL_RID`, `SIN_EQ_0_PI`, `REAL_FIELD`


---

## DIRICHLET_KERNEL_NEG

### Name of formal statement
DIRICHLET_KERNEL_NEG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_KERNEL_NEG = prove
 (`!n x. dirichlet_kernel n (--x) = dirichlet_kernel n x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dirichlet_kernel; REAL_NEG_EQ_0] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_RNEG; REAL_MUL_LNEG; real_div; SIN_NEG;
                  REAL_INV_NEG; REAL_NEG_NEG]);;
```
### Informal statement
For all natural numbers `n` and real numbers `x`, the `dirichlet_kernel` of `n` evaluated at the negation of `x` is equal to the `dirichlet_kernel` of `n` evaluated at `x`.  In other words, the Dirichlet kernel is an even function.

### Informal sketch
The proof proceeds as follows:
- Introduce the universally quantified variables `n` and `x`.
- Rewrite the `dirichlet_kernel` using its definition and the fact that `-x = 0 - x`.
- Perform a case split based on whether `x` is equal to zero.
- In the case where `x` is not zero, rewrite using the properties of real multiplication, the trigonometric identity `SIN_NEG`, the negation of the inverse, and the double negation property of real numbers.
- Simplify the expression to show equality.

### Mathematical insight
The Dirichlet kernel is a fundamental function in Fourier analysis. This theorem shows that the Dirichlet kernel is an even function, which is a useful property for simplifying many calculations and understanding its behavior.

### Dependencies
- Definitions: `dirichlet_kernel`
- Theorems: `REAL_NEG_EQ_0`, `REAL_MUL_RNEG`, `REAL_MUL_LNEG`, `real_div`, `SIN_NEG`, `REAL_INV_NEG`, `REAL_NEG_NEG`

### Porting notes (optional)
The definition of `dirichlet_kernel` and the theorems about real arithmetic and trigonometry need to be available in the target proof assistant. The handling of real numbers and trigonometric functions might differ between proof assistants, so care should be taken to ensure that the corresponding definitions and theorems are used. The case split (`COND_CASES_TAC`) based on equality to zero might need to be adapted to the specific tactics available in the target proof assistant.


---

## DIRICHLET_KERNEL_CONTINUOUS_STRONG

### Name of formal statement
DIRICHLET_KERNEL_CONTINUOUS_STRONG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_KERNEL_CONTINUOUS_STRONG = prove
 (`!n. (dirichlet_kernel n) real_continuous_on
       real_interval(--(&2 * pi),&2 * pi)`,
  let lemma = prove
   (`f real_differentiable (atreal a) /\ f(a) = b
     ==> (f ---> b) (atreal a)`,
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o
      MATCH_MP REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL) THEN
    REWRITE_TAC[REAL_CONTINUOUS_ATREAL] THEN ASM_MESON_TAC[]) in
  SIMP_TAC[REAL_OPEN_REAL_INTERVAL; IN_REAL_INTERVAL;
           REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `x:real`] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
  REWRITE_TAC[dirichlet_kernel] THEN ASM_CASES_TAC `x = &0` THENL
   [ALL_TAC;
    SUBGOAL_THEN
     `(\x. sin((&k + &1 / &2) * x) / (&2 * sin(x / &2)))
      real_continuous atreal x`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_DIV THEN
      REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
       [CONJ_TAC THEN
        MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
        REAL_DIFFERENTIABLE_TAC;
        MP_TAC(ISPEC `x / &2` SIN_EQ_0_PI) THEN
        ASM_REWRITE_TAC[NETLIMIT_ATREAL] THEN ASM_REAL_ARITH_TAC];
      ASM_REWRITE_TAC[REAL_CONTINUOUS_ATREAL] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REALLIM_TRANSFORM_EVENTUALLY) THEN
      REWRITE_TAC[EVENTUALLY_ATREAL] THEN EXISTS_TAC `abs x` THEN
      ASM_REAL_ARITH_TAC]] THEN
  ASM_REWRITE_TAC[REAL_CONTINUOUS_ATREAL] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\x. sin((&k + &1 / &2) * x) / (&2 * sin(x / &2))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[EVENTUALLY_ATREAL; REAL_ARITH
     `&0 < abs(x - &0) <=> ~(x = &0)`] THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01];
    ALL_TAC] THEN
  MATCH_MP_TAC LHOSPITAL THEN MAP_EVERY EXISTS_TAC
   [`\x. (&k + &1 / &2) * cos((&k + &1 / &2) * x)`;
    `\x. cos(x / &2)`; `&1`] THEN
  REWRITE_TAC[REAL_LT_01; REAL_SUB_RZERO] THEN REPEAT STRIP_TAC THENL
   [REAL_DIFF_TAC THEN REAL_ARITH_TAC;
    REAL_DIFF_TAC THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM(fun th -> MP_TAC th THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC COS_POS_PI) THEN
    MP_TAC PI_APPROX_32 THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC lemma THEN
    REWRITE_TAC[REAL_MUL_RZERO; SIN_0] THEN REAL_DIFFERENTIABLE_TAC;
    MATCH_MP_TAC lemma THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; real_div; SIN_0] THEN
    REAL_DIFFERENTIABLE_TAC;
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM real_div] THEN
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM REAL_DIV_1] THEN
    MATCH_MP_TAC REALLIM_DIV THEN
    REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ] THEN CONJ_TAC THEN
    MATCH_MP_TAC lemma THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO;
                real_div; COS_0; REAL_MUL_RID] THEN
    REAL_DIFFERENTIABLE_TAC]);;
```

### Informal statement
For all natural numbers `n`, the `dirichlet_kernel n` is real continuous on the real interval `(-2 * pi, 2 * pi)`.

### Informal sketch
The proof demonstrates that the Dirichlet kernel is continuous on the open interval `(-2π, 2π)`.

- First, a lemma is proved: if a function `f` is real differentiable at a real number `a` and `f(a) = b`, then `f` tends to `b` at `a`. This is proven by using `REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL` and rewriting with `REAL_CONTINUOUS_ATREAL`.

- The goal is then simplified using `REAL_OPEN_REAL_INTERVAL`, `IN_REAL_INTERVAL`, and `REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT`, reducing the problem to showing continuity at every point within the specified interval.

- The proof proceeds by cases based on whether `x = 0`.  The formula for the Dirichlet kernel `dirichlet_kernel n` is expanded.
  - **Case 1:** Suppose `x = 0`.  The goal then trivially holds.
  - **Case 2:** Suppose `x != 0`. Then it must be proven that the function `sin((k + 1/2) * x) / (2 * sin(x / 2))` is real continuous at `x`.
    - This is proved by showing the numerator and denominator are continuous and that the limit of the denominator is not zero at `x`. The numerator and denominator are each continuous, leveraging differentiability implying continuity and evaluating the limit of `sin(x/2)` as `x` approaches `0`.
    - To prove that `sin(x/2)` has a nonzero limit `atreal x`, `SIN_EQ_0_PI` is used along with results about the function `netlimit`
    - Because `sin(x/2)` converges to `0` as `x` approaches `0` using the lemma defined in the beginning, L'Hôpital's rule (`LHOSPITAL`) is applied to evaluate the limit of `sin((k + 1/2) * x) / (2 * sin(x / 2))` as `x` approaches `0`.
      - The derivatives of numerator and denominator are calculated. Conditions for applying L'Hopital's rule, differentiability of numerator and denominator, and that the derivative of denominator is not zero, are verified. This involves estimating `pi` with `PI_APPROX_32`, and proving the derivative of `sin(x/2)` is not zero, which relies on rewriting and using `COS_POS_PI`.
      - Showing that the limit of the derivatives meet the conditions for L'Hopital to apply. The derivatives are `(k + 1/2) * cos((k + 1/2) * x)` and `cos(x / 2)`. The final application of L'Hopital requires demonstrating differentiability, showing that `f(a)` evaluates to the limit, then invoking L'Hopital which calculates the result of the limit and therefore ensures continuity.

### Mathematical insight
This theorem establishes the continuity of the Dirichlet kernel on an open interval around the origin. The Dirichlet kernel is a key function in Fourier analysis, and its continuity is fundamental for establishing convergence results for Fourier series. The proof requires careful handling of the singularity at `x = 0`, which is resolved by applying L'Hôpital's rule.

### Dependencies
- Definitions: `dirichlet_kernel`
- Theorems: `REAL_OPEN_REAL_INTERVAL`, `IN_REAL_INTERVAL`, `REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT`, `REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL`, `REAL_CONTINUOUS_DIV`, `NETLIMIT_ATREAL`, `REALLIM_TRANSFORM_EVENTUALLY`, `LHOSPITAL`, `COS_POS_PI`, `SIN_EQ_0_PI`, `PI_APPROX_32`
### Porting notes (optional)
- Most proof assistants have built-in support for real analysis and L'Hôpital's rule.
- The main challenge is likely to be setting up the necessary differentiability and limit conditions for applying L'Hôpital's rule formally and dealing with `atreal`'s netlimit topology.
- Depending on the target proof assistant, one may need to explicitly prove the lemma about differentiability implying continuity with respect to the `atreal` filter, rather than using a pre-existing theorem to discharge it.


---

## DIRICHLET_KERNEL_CONTINUOUS

### Name of formal statement
DIRICHLET_KERNEL_CONTINUOUS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_KERNEL_CONTINUOUS = prove
 (`!n. (dirichlet_kernel n) real_continuous_on real_interval[--pi,pi]`,
  GEN_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `real_interval(--(&2 * pi),&2 * pi)` THEN
  REWRITE_TAC[DIRICHLET_KERNEL_CONTINUOUS_STRONG] THEN
  REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;
```
### Informal statement
For all natural numbers `n`, the `dirichlet_kernel n` is real-continuous on the real interval from `-pi` to `pi`.

### Informal sketch
The proof proceeds as follows:
- Begin by applying `GEN_TAC` to discharge the universal quantifier for `n`. 
- Use `REAL_CONTINUOUS_ON_SUBSET` to reduce the goal to showing that `dirichlet_kernel n` is real-continuous on a larger interval.
-  Use `EXISTS_TAC` to introduce the interval `real_interval(--(&2 * pi),&2 * pi)` as the larger interval.
- Rewrite the goal using `DIRICHLET_KERNEL_CONTINUOUS_STRONG`. This likely replaces the subset relationship with an explicit continuity assertion on the larger interval due to a stronger version of the theorem existing.
- Rewrite using `SUBSET_REAL_INTERVAL`. This presumably expands the definition of subset relation between real intervals.
- Apply `MP_TAC` with `PI_POS` to prove that `pi > 0`.
- Use `REAL_ARITH_TAC` to complete the argument by real arithmetic reasoning.

### Mathematical insight
This theorem establishes the continuity of the Dirichlet kernel on the interval `[-pi, pi]`. The Dirichlet kernel plays a crucial role in the theory of Fourier series, and its continuity is a prerequisite for many important results, such as the convergence of Fourier series under certain conditions. The proof shows that, despite its definition involving trigonometric functions and a finite sum, the Dirichlet kernel is well-behaved in terms of continuity. Showing continuity is helpful because continuous functions are often easier to work with.

### Dependencies
- `DIRICHLET_KERNEL_CONTINUOUS_STRONG`
- `REAL_CONTINUOUS_ON_SUBSET`
- `SUBSET_REAL_INTERVAL`
- `PI_POS`


---

## ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL

### Name of formal statement
ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL = prove
 (`!f n. f absolutely_real_integrable_on real_interval[--pi,pi]
         ==> (\x. dirichlet_kernel n x * f x)
             absolutely_real_integrable_on real_interval[--pi,pi]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
    ASM_REWRITE_TAC[DIRICHLET_KERNEL_CONTINUOUS; ETA_AX;
                    REAL_CLOSED_REAL_INTERVAL];
    MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC REAL_COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[DIRICHLET_KERNEL_CONTINUOUS; ETA_AX;
                    REAL_COMPACT_INTERVAL]]);;
```

### Informal statement
For all real-valued functions `f` and natural numbers `n`, if `f` is absolutely real integrable on the real interval `[-pi, pi]`, then the function defined by `x` mapping to `dirichlet_kernel n x * f x` is also absolutely real integrable on the real interval `[-pi, pi]`.

### Informal sketch
The proof proceeds by showing that if a function `f` is absolutely real integrable on `real_interval[--pi,pi]`, then the product of `f` with the `dirichlet_kernel n x` is also absolutely real integrable on the same interval.

- First, it's shown using `ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT` that if a function is absolutely real integrable and the other function is bounded and measurable, then their product is absolutely real integrable.
- Then, the proof is split into showing that `dirichlet_kernel n x` is measurable on `real_interval[--pi, pi]` using `REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET`, `DIRICHLET_KERNEL_CONTINUOUS`, `ETA_AX`, and `REAL_CLOSED_REAL_INTERVAL`.
- Also, it must demonstrated that the `dirichlet_kernel n x` is bounded on the `real_interval[--pi, pi]` by showing it is compact using `REAL_COMPACT_IMP_BOUNDED`, `REAL_COMPACT_CONTINUOUS_IMAGE`,  `DIRICHLET_KERNEL_CONTINUOUS`, `ETA_AX`, and `REAL_COMPACT_INTERVAL`.

### Mathematical insight
This theorem states that multiplying an absolutely integrable function by the Dirichlet kernel preserves absolute integrability on the interval `[-pi, pi]`. This is important in Fourier analysis because the Dirichlet kernel appears in the partial sums of Fourier series, and understanding its integrability properties is essential for studying the convergence of Fourier series.

### Dependencies
- Theorems:
  - `ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT`
  - `REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET`
  - `REAL_COMPACT_IMP_BOUNDED`
  - `REAL_COMPACT_CONTINUOUS_IMAGE`
- Definitions:
  - `dirichlet_kernel`
- Axioms:
  - `ETA_AX`
- Conversions:
  - `REAL_CLOSED_REAL_INTERVAL`
  - `REAL_COMPACT_INTERVAL`
  - `DIRICHLET_KERNEL_CONTINUOUS`


---

## COSINE_SUM_LEMMA

### Name of formal statement
COSINE_SUM_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COSINE_SUM_LEMMA = prove
 (`!n x. (&1 / &2 + sum(1..n) (\k. cos(&k * x))) * sin(x / &2) =
         sin((&n + &1 / &2) * x) / &2`,
  REPEAT STRIP_TAC THEN DISJ_CASES_TAC(ARITH_RULE `n = 0 \/ 1 <= n`) THENL
   [ASM_REWRITE_TAC[REAL_ADD_LID; SUM_CLAUSES_NUMSEG; ARITH] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID; REAL_ADD_RID; REAL_MUL_SYM];
    REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ADD_RDISTRIB; GSYM SUM_RMUL] THEN
    REWRITE_TAC[REAL_MUL_COS_SIN; real_div; REAL_SUB_RDISTRIB] THEN
    SUBGOAL_THEN
     `!k x. &k * x + x * inv(&2) = (&(k + 1) * x - x * inv(&2))`
     (fun th -> REWRITE_TAC[th; SUM_DIFFS_ALT])
    THENL [REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM real_div] THEN
    REWRITE_TAC[REAL_ARITH `&1 * x - x / &2 = x / &2`] THEN
    REWRITE_TAC[REAL_ARITH `(&n + &1) * x - x / &2 = (&n + &1 / &2) * x`] THEN
    REWRITE_TAC[REAL_ADD_RDISTRIB] THEN REAL_ARITH_TAC]);;
```
### Informal statement
For all natural numbers `n` and real numbers `x`, the following equality holds: `(1/2 + sum(1..n) (\k. cos(k*x))) * sin(x/2) = sin((n + 1/2)*x) / 2`.

### Informal sketch
The proof proceeds by induction on whether `n` is zero or greater than equal to 1.
- If `n = 0`, the goal simplifies to `(1/2) * sin(x/2) = sin(x/2) / 2`, which is proven by rewriting with basic real arithmetic.
- If `1 <= n`, the proof involves rewriting using the distributive property of multiplication over addition and manipulating the summation.
  - The key step is applying `REAL_MUL_COS_SIN` to express the sum of cosine terms multiplied by `sin(x/2)` as a telescopic sum of sines.
  - The expression `k * x + x/2` is rewritten as `(k+1) * x - x/2` so that the `SUM_DIFFS_ALT` theorem can be applied to evaluate the telescoping sum.
  - Then, the goal is simplified and proven by basic real arithmetic.

### Mathematical insight
This lemma provides a closed-form expression for the sum of cosines multiplied by sine:
`sin(x/2) * (1/2 + cos(x) + cos(2x) + ... + cos(nx)) = sin((n + 1/2)x)/2 }`.
It is a trigonometric identity useful in Fourier analysis and signal processing and provides a way to simplify expressions involving sums of cosine functions.

### Dependencies
- `REAL_ADD_LID`
- `SUM_CLAUSES_NUMSEG`
- `REAL_ADD_RID`
- `REAL_MUL_LID`
- `real_div`
- `REAL_MUL_SYM`
- `REAL_ADD_RDISTRIB`
- `GSYM SUM_RMUL`
- `REAL_MUL_COS_SIN`
- `REAL_SUB_RDISTRIB`
- `SUM_DIFFS_ALT`
- `GSYM REAL_OF_NUM_ADD`

### Porting notes (optional)
- The proof relies on rewriting with arithmetic identities, which should be straightforward to implement in other proof assistants.
- The application of `SUM_DIFFS_ALT` might require equivalent theorems about summation in the target system.
- Special attention should be paid to the manipulation of real numbers, ensuring that the corresponding tactics or theorems in the target system have similar behavior.


---

## DIRICHLET_KERNEL_COSINE_SUM

### Name of formal statement
DIRICHLET_KERNEL_COSINE_SUM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_KERNEL_COSINE_SUM = prove
 (`!n x. ~(x = &0) /\ abs(x) < &2 * pi
         ==> dirichlet_kernel n x = &1 / &2 + sum(1..n) (\k. cos(&k * x))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[dirichlet_kernel] THEN
  MATCH_MP_TAC(REAL_FIELD
    `~(y = &0) /\ z * y = x / &2 ==> x / (&2 * y) = z`) THEN
  REWRITE_TAC[COSINE_SUM_LEMMA] THEN
  MP_TAC(ISPEC `x / &2` SIN_EQ_0_PI) THEN ASM_REAL_ARITH_TAC);;
```
### Informal statement
For all natural numbers `n` and real numbers `x`, if `x` is not equal to 0 and the absolute value of `x` is less than `2 * pi`, then the `dirichlet_kernel n x` is equal to `1/2 + sum(1..n) (\k. cos(&k * x))`.

### Informal sketch
The proof proceeds as follows:
- Start by stripping the quantifiers and the implication.
- Rewrite the `dirichlet_kernel n x` using its definition.
- Apply a field tactic that transforms `x / (2 * (sin (x / 2)))` into an equivalent form.
- Rewrite using the `COSINE_SUM_LEMMA`. This lemma provides a closed form for the sum of cosines.
- Specialize the theorem `SIN_EQ_0_PI` with `x / 2`.
- Use real arithmetic to complete the proof.

### Mathematical insight
This theorem provides an alternative formulation of the Dirichlet kernel as a sum of cosine functions. This is a useful representation for analyzing the convergence and properties of Fourier series. The Dirichlet kernel plays a central role in the study of Fourier series, particularly in understanding the convergence behavior of partial sums of Fourier series. This equivalent form is helpful when studying the convergence properties using real analysis.

### Dependencies
- Definitions: `dirichlet_kernel`
- Theorems: `COSINE_SUM_LEMMA`, `SIN_EQ_0_PI`


---

## HAS_REAL_INTEGRAL_DIRICHLET_KERNEL

### Name of formal statement
HAS_REAL_INTEGRAL_DIRICHLET_KERNEL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HAS_REAL_INTEGRAL_DIRICHLET_KERNEL = prove
 (`!n. (dirichlet_kernel n has_real_integral pi) (real_interval[--pi,pi])`,
  GEN_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_SPIKE THEN
  EXISTS_TAC `\x. &1 / &2 + sum(1..n) (\k. cos(&k * x))` THEN
  EXISTS_TAC `{&0}` THEN
  REWRITE_TAC[REAL_NEGLIGIBLE_SING; IN_DIFF; IN_SING; IN_REAL_INTERVAL] THEN
  SIMP_TAC[REAL_ARITH `&0 < pi /\ --pi <= x /\ x <= pi ==> abs(x) < &2 * pi`;
           DIRICHLET_KERNEL_COSINE_SUM; PI_POS] THEN
  SUBGOAL_THEN `pi = pi + sum(1..n) (\k. &0)` MP_TAC THENL
   [REWRITE_TAC[SUM_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_ADD THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [REAL_ARITH  `pi = (&1 / &2) * (pi - --pi)`] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_CONST THEN MP_TAC PI_POS THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC HAS_REAL_INTEGRAL_SUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    MP_TAC(SPEC `k:num` HAS_REAL_INTEGRAL_COS_NX) THEN ASM_SIMP_TAC[LE_1]]);;
```
### Informal statement
For all natural numbers `n`, the `dirichlet_kernel n` has a real integral equal to `pi` over the real interval from `-pi` to `pi`.

### Informal sketch
The proof proceeds as follows:
- Start with the goal `!n. (dirichlet_kernel n has_real_integral pi) (real_interval[--pi,pi])`.
- Apply `HAS_REAL_INTEGRAL_SPIKE` to reduce the goal to showing that the `dirichlet_kernel` can be written as `1/2 + sum(1..n) cos(k*x)` plus a function negligible on `{0}`.
- Rewrite using `REAL_NEGLIGIBLE_SING`, `IN_DIFF`, `IN_SING`, `IN_REAL_INTERVAL` to simplify the negligible part and membership of the interval.
- Simplify using arithmetic facts, `DIRICHLET_KERNEL_COSINE_SUM`, and `PI_POS`.
- Show that `pi = pi + sum(1..n) 0` which is trivial, and discharge the assumption.
- Use `HAS_REAL_INTEGRAL_ADD` to split the integral into the integral of `1/2` over the interval and the integral of the sum of cosines.
- Prove that the integral of `1/2` is `pi`. We use `REAL_ARITH` to show `pi = (&1 / &2) * (pi - --pi)`, and use `HAS_REAL_INTEGRAL_CONST` to obtain that constants have real integrals.
- Prove that the integral of the sum is zero. This involves rewriting with `FINITE_NUMSEG` and `IN_NUMSEG` to reason about the indices of the sum, then apply `HAS_REAL_INTEGRAL_COS_NX`, after specializing it for an arbitrary `k:num` and simplifying with `LE_1`.

### Mathematical insight
This theorem establishes a key property of the Dirichlet kernel, namely that its integral over the interval `[-pi, pi]` is equal to `pi`. The Dirichlet kernel is a fundamental object in Fourier analysis and is used in the study of convergence of Fourier series. The fact that its integral is `pi` reflects the normalization used in defining the Fourier coefficients.

### Dependencies
- `HAS_REAL_INTEGRAL_SPIKE`
- `REAL_NEGLIGIBLE_SING`
- `IN_DIFF`
- `IN_SING`
- `IN_REAL_INTERVAL`
- `DIRICHLET_KERNEL_COSINE_SUM`
- `PI_POS`
- `SUM_0`
- `HAS_REAL_INTEGRAL_ADD`
- `HAS_REAL_INTEGRAL_CONST`
- `HAS_REAL_INTEGRAL_SUM`
- `FINITE_NUMSEG`
- `IN_NUMSEG`
- `HAS_REAL_INTEGRAL_COS_NX`

### Porting notes (optional)
Porting requires establishing the definition of the Dirichlet kernel and the properties of real integrals (including `HAS_REAL_INTEGRAL_ADD`, `HAS_REAL_INTEGRAL_CONST`, `HAS_REAL_INTEGRAL_SUM`, `HAS_REAL_INTEGRAL_COS_NX`). One should also ensure appropriate theory about sums, e.g., `SUM_0`.
The theorem `HAS_REAL_INTEGRAL_SPIKE` is also required. This would likely need porting/reproving, which would entail proving that the real integral operator is robust with respect to negligible/spike functions.

The main challenge involves porting the real analysis infrastructure required to define and manipulate real integrals, and to prove properties about negligible functions, finite sums, and the negligible set of singularities `{0}`.


---

## HAS_REAL_INTEGRAL_DIRICHLET_KERNEL_HALF

### Name of formal statement
HAS_REAL_INTEGRAL_DIRICHLET_KERNEL_HALF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HAS_REAL_INTEGRAL_DIRICHLET_KERNEL_HALF = prove
 (`!n. (dirichlet_kernel n has_real_integral (pi / &2))
       (real_interval[&0,pi])`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`dirichlet_kernel n`; `--pi`; `pi`; `&0`; `pi`]
        REAL_INTEGRABLE_SUBINTERVAL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MESON_TAC[HAS_REAL_INTEGRAL_DIRICHLET_KERNEL; real_integrable_on];
      REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN MP_TAC PI_POS THEN
      REAL_ARITH_TAC];
    REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRAL] THEN DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I
   [GSYM HAS_REAL_INTEGRAL_REFLECT]) THEN
  REWRITE_TAC[DIRICHLET_KERNEL_NEG; ETA_AX; REAL_NEG_0] THEN DISCH_TAC THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[real_integrable_on]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`dirichlet_kernel n`;
    `real_integral (real_interval [&0,pi]) (dirichlet_kernel n)`;
    `real_integral (real_interval [&0,pi]) (dirichlet_kernel n)`;
    `--pi`; `pi`; `&0`] HAS_REAL_INTEGRAL_COMBINE) THEN
  ASM_REWRITE_TAC[GSYM REAL_MUL_2] THEN
  ANTS_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
  MATCH_MP_TAC(REAL_ARITH `x = pi ==> x = &2 * y ==> y = pi / &2`) THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_DIRICHLET_KERNEL]);;
```
### Informal statement
For all natural numbers `n`, the `dirichlet_kernel n` has a real integral of `pi / 2` on the real interval from `0` to `pi`.

### Informal sketch
The proof proceeds as follows:
- We start with the assumption that `dirichlet_kernel n` has a real integral on any subinterval of `[-pi, pi]` .
- The goal is to prove that `dirichlet_kernel n` has a real integral of `pi/2` on `[0, pi]`.
- We employ `REAL_INTEGRABLE_SUBINTERVAL` to show that since the Dirichlet kernel is integrable on `[-pi, pi]`, it is also integrable on `[0, pi]`.
- The proof then uses the fact that `dirichlet_kernel` is integrable.
- We use `HAS_REAL_INTEGRAL_REFLECT` to relate the integral over `[-pi, 0]` to the integral over `[0, pi]`.
- Subsequently, we apply `HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL` and `HAS_REAL_INTEGRAL_COMBINE` to split the integral over `[-pi, pi]` into integrals over `[-pi, 0]` and `[0, pi]`.
- We utilize `REAL_INTEGRAL_UNIQUE` and arithmetic reasoning to deduce the final result which shows that the integral of the `dirichlet_kernel n` over the real interval from `0` to `pi` is equal to `pi / 2`.
- The proof is completed by using the theorem `HAS_REAL_INTEGRAL_DIRICHLET_KERNEL`.

### Mathematical insight
This theorem states a key property of the Dirichlet kernel, namely that its integral over the interval `[0, pi]` is `pi/2`. This is a crucial result in Fourier analysis and is used in the proof of Dirichlet's theorem for pointwise convergence of Fourier series.

### Dependencies
- `HAS_REAL_INTEGRAL_DIRICHLET_KERNEL`
- `real_integrable_on`
- `SUBSET_REAL_INTERVAL`
- `PI_POS`
- `HAS_REAL_INTEGRAL_INTEGRAL`
- `HAS_REAL_INTEGRAL_REFLECT`
- `DIRICHLET_KERNEL_NEG`
- `ETA_AX`
- `REAL_NEG_0`
- `HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL`
- `HAS_REAL_INTEGRAL_COMBINE`
- `REAL_MUL_2`
- `REAL_INTEGRAL_UNIQUE`
- `REAL_INTEGRABLE_SUBINTERVAL`


---

## FOURIER_SUM_OFFSET_DIRICHLET_KERNEL

### Name of formal statement
FOURIER_SUM_OFFSET_DIRICHLET_KERNEL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_SUM_OFFSET_DIRICHLET_KERNEL = prove
 (`!f n t.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> sum(0..2*n) (\k. fourier_coefficient f k * trigonometric_set k t) =
            real_integral (real_interval[--pi,pi])
                          (\x. dirichlet_kernel n x * f(x + t)) / pi`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FOURIER_SUM_OFFSET_UNPAIRED] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ARITH] THEN
  REWRITE_TAC[trigonometric_set; COS_0; REAL_MUL_LZERO] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `fourier_coefficient (\x. f(x + t)) 0 * &1 / sqrt(&2 * pi) +
    sum (1..n) (\k. fourier_coefficient (\x. f(x + t)) (2 * k) / sqrt pi)` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    SIMP_TAC[TRIGONOMETRIC_SET_EVEN; LE_1; REAL_MUL_RZERO; COS_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID;
              fourier_coefficient; orthonormal_coefficient;
              trigonometric_set; l2product] THEN
  MP_TAC(ISPECL [`f:real->real`; `--pi`; `pi`; `t:real`]
        ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET) THEN
  ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN DISCH_TAC THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
   [GSYM REAL_MUL_ASSOC; GSYM REAL_INTEGRAL_RMUL; GSYM REAL_INTEGRAL_ADD;
    ABSOLUTELY_INTEGRABLE_COS_PRODUCT;
    ABSOLUTELY_INTEGRABLE_SIN_PRODUCT;
    ABSOLUTELY_REAL_INTEGRABLE_LMUL;
    TRIGONOMETRIC_SET_MUL_ABSOLUTELY_INTEGRABLE;
    ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
    GSYM REAL_INTEGRAL_SUM; FINITE_NUMSEG;
    ABSOLUTELY_REAL_INTEGRABLE_RMUL;
    ABSOLUTELY_REAL_INTEGRABLE_SUM;
    ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL] THEN
  MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN EXISTS_TAC `{}:real->bool` THEN
  REWRITE_TAC[REAL_NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN
  X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_MUL_LZERO; COS_0; REAL_ARITH
   `a * b * c * b:real = (a * c) * b pow 2`] THEN
  SIMP_TAC[REAL_POW_INV; SQRT_POW_2; REAL_LE_MUL; REAL_POS; PI_POS_LE;
           REAL_LE_INV_EQ] THEN
  REWRITE_TAC[REAL_INV_MUL; REAL_ARITH
   `d * f * i = (&1 * f) * inv(&2) * i + y <=> i * f * (d - &1 / &2) = y`] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(1..n) (\k. inv pi * f(x + t) * cos(&k * x))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUM_LMUL] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_ARITH `x - &1 / &2 = y <=> x = &1 / &2 + y`] THEN
    ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[dirichlet_kernel] THENL
     [REWRITE_TAC[REAL_MUL_RZERO; COS_0; SUM_CONST_NUMSEG; ADD_SUB] THEN
      REAL_ARITH_TAC;
      MP_TAC(ISPEC `x / &2` SIN_EQ_0_PI) THEN
      MATCH_MP_TAC(TAUT `a /\ b /\ ~d /\ (~c ==> e)
                         ==> (a /\ b /\ c ==> d) ==> e`) THEN
      REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      ASM_SIMP_TAC[REAL_FIELD
      `~(y = &0) ==> (x / (&2 * y) = z <=> z * y = x / &2)`] THEN
      REWRITE_TAC[COSINE_SUM_LEMMA]];
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[TRIGONOMETRIC_SET_EVEN; LE_1] THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC(REAL_RING
     `s * s:real = p ==> p * f * c = (c * s) * f * s`) THEN
    REWRITE_TAC[GSYM REAL_INV_MUL] THEN AP_TERM_TAC THEN
    SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2; PI_POS_LE]]);;
```
### Informal statement
For all real-valued functions `f`, natural numbers `n`, and real numbers `t`, if `f` is absolutely real integrable on the real interval from `-pi` to `pi` and `f(x + 2 * pi) = f(x)` for all real numbers `x`, then the sum from `0` to `2 * n` of `fourier_coefficient f k * trigonometric_set k t` is equal to the real integral from `-pi` to `pi` of `dirichlet_kernel n x * f(x + t)` divided by `pi`.

### Informal sketch
The proof establishes an equality involving the Fourier series of a periodic, integrable function `f` offset by `t`, and its representation in terms of the Dirichlet kernel.
- The proof starts by simplifying the Fourier sum using `FOURIER_SUM_OFFSET_UNPAIRED`.
- It rewrites the `trigonometric_set` with `COS_0` and `REAL_MUL_LZERO`, simplifying the summation.
- It expresses the sum as the sum of cosine terms, applying `SUM_EQ_NUMSEG` and simplifying using trigonometric properties.
- The Fourier coefficients are expanded using their definitions (`fourier_coefficient`, `orthonormal_coefficient`, `trigonometric_set`, `l2product`).
- It uses `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET` to introduce the periodicity assumption.
- Integrals involving the product of `f` and trigonometric functions are shown to be absolutely integrable through a sequence of theorems `ABSOLUTELY_INTEGRABLE_COS_PRODUCT`, `ABSOLUTELY_INTEGRABLE_SIN_PRODUCT`, etc.
- The `REAL_INTEGRAL_SPIKE` is used to transform the integral.
- Cases are analyzed where `x` is zero and non-zero in relation to `dirichlet_kernel`.
- A final step makes use of `COSINE_SUM_LEMMA` to arrive at the conclusion.

### Mathematical insight
This theorem connects the partial sums of the Fourier series of a function with the convolution of the function with the Dirichlet kernel. It illustrates the fundamental result that the Fourier series converges to the function when convolved with a Dirichlet Kernel. The conditions of the theorem establish natural constraints where such equality holds true.

### Dependencies
- `FOURIER_SUM_OFFSET_UNPAIRED`
- `SUM_CLAUSES_LEFT`
- `LE_0`
- `ARITH`
- `trigonometric_set`
- `COS_0`
- `REAL_MUL_LZERO`
- `SUM_EQ_NUMSEG`
- `TRIGONOMETRIC_SET_EVEN`
- `LE_1`
- `REAL_MUL_RZERO`
- `real_div`
- `REAL_MUL_LID`
- `fourier_coefficient`
- `orthonormal_coefficient`
- `l2product`
- `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`
- `REAL_ARITH `pi - --pi = &2 * pi``
- `GSYM REAL_MUL_ASSOC`
- `GSYM REAL_INTEGRAL_RMUL`
- `GSYM REAL_INTEGRAL_ADD`
- `ABSOLUTELY_INTEGRABLE_COS_PRODUCT`
- `ABSOLUTELY_INTEGRABLE_SIN_PRODUCT`
- `ABSOLUTELY_REAL_INTEGRABLE_LMUL`
- `TRIGONOMETRIC_SET_MUL_ABSOLUTELY_INTEGRABLE`
- `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE`
- `GSYM REAL_INTEGRAL_SUM`
- `FINITE_NUMSEG`
- `ABSOLUTELY_REAL_INTEGRABLE_RMUL`
- `ABSOLUTELY_REAL_INTEGRABLE_SUM`
- `ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL`
- `REAL_INTEGRAL_SPIKE`
- `REAL_NEGLIGIBLE_EMPTY`
- `DIFF_EMPTY`
- `IN_REAL_INTERVAL`
- `REAL_MUL_LZERO`
- `REAL_ARITH `a * b * c * b:real = (a * c) * b pow 2```
- `REAL_POW_INV`
- `SQRT_POW_2`
- `REAL_LE_MUL`
- `REAL_POS`
- `PI_POS_LE`
- `REAL_LE_INV_EQ`
- `REAL_INV_MUL`
- `REAL_ARITH `d * f * i = (&1 * f) * inv(&2) * i + y <=> i * f * (d - &1 / &2) = y``
- `SUM_LMUL`
- `REAL_ARITH `x - &1 / &2 = y <=> x = &1 / &2 + y``
- `dirichlet_kernel`
- `REAL_MUL_RZERO`
- `SUM_CONST_NUMSEG`
- `ADD_SUB`
- `SIN_EQ_0_PI`
- `TAUT `a /\ b /\ ~d /\ (~c ==> e) ==> (a /\ b /\ c ==> d) ==> e``
- `REAL_FIELD `~(y = &0) ==> (x / (&2 * y) = z <=> z * y = x / &2)``
- `COSINE_SUM_LEMMA`
- `SUM_EQ_NUMSEG`
- `TRIGONOMETRIC_SET_EVEN`
- `REAL_RING `s * s:real = p ==> p * f * c = (c * s) * f * s``
- `GSYM REAL_INV_MUL`
- `GSYM REAL_POW_2`
- `PI_POS_LE`

### Porting notes (optional)
- The heavy reliance on `REAL_ARITH` suggests a need for a well-developed real number tactic in the target proof assistant.
- Significant automation used in simplification and rewriting may require equivalent automation.


---

## FOURIER_SUM_LIMIT_DIRICHLET_KERNEL

### Name of formal statement
FOURIER_SUM_LIMIT_DIRICHLET_KERNEL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_SUM_LIMIT_DIRICHLET_KERNEL = prove
 (`!f t l.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> (((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> l) sequentially <=>
            ((\n. real_integral (real_interval[--pi,pi])
                                (\x. dirichlet_kernel n x * f(x + t)))
             ---> pi * l) sequentially)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM FOURIER_SUM_LIMIT_PAIR] THEN
  ASM_SIMP_TAC[FOURIER_SUM_OFFSET_DIRICHLET_KERNEL] THEN
  SUBGOAL_THEN `l = (l * pi) / pi`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
  THENL [MP_TAC PI_POS THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SIMP_TAC[real_div; REALLIM_RMUL_EQ; PI_NZ; REAL_INV_EQ_0] THEN
  REWRITE_TAC[REAL_MUL_AC]);;
```

### Informal statement
For any function `f`, any real number `t`, and any real number `l`, if `f` is absolutely real integrable on the real interval from `-pi` to `pi` and `f(x + 2*pi) = f(x)` for all `x`, then the sequence whose `n`-th term is the sum from `0` to `n` of `fourier_coefficient f k * trigonometric_set k t` converges to `l` sequentially if and only if the sequence whose `n`-th term is the real integral over the real interval from `-pi` to `pi` of `dirichlet_kernel n x * f(x + t)` converges to `pi * l` sequentially.

### Informal sketch
The proof proceeds by:
- Stripping the goal and simplifying using the assumption `FOURIER_SUM_LIMIT_PAIR`.
- Simplifying using `FOURIER_SUM_OFFSET_DIRICHLET_KERNEL`.
- Introducing the subgoal `l = (l * pi) / pi` and proving it. This involves demonstrating that `pi` is positive using `PI_POS`, simplifying using real field properties and the fact that `pi` is non-zero.
- Simplifying with theorems related to real division, multiplication, and properties of `pi` and `REAL_INV_EQ_0`.
- Rewriting using associativity and commutativity of real multiplication.

### Mathematical insight
This theorem connects the convergence of the Fourier series of a function `f` at a point `t` to the convergence of an integral involving the Dirichlet kernel and a shifted version of `f`. It formalizes the idea that the Fourier series converges to a value `l` if and only if the integral of the function multiplied by the Dirichlet kernel converges to `pi * l`. The Dirichlet kernel serves as an approximation to the Dirac delta function, and this result is a key step in proving pointwise convergence theorems for Fourier series.

### Dependencies
- `FOURIER_SUM_LIMIT_PAIR`
- `FOURIER_SUM_OFFSET_DIRICHLET_KERNEL`
- `PI_POS`
- `real_div`
- `REALLIM_RMUL_EQ`
- `PI_NZ`
- `REAL_INV_EQ_0`
- `REAL_MUL_AC`


---

## SIMPLE_FOURIER_CONVERGENCE_PERIODIC

### Name of formal statement
SIMPLE_FOURIER_CONVERGENCE_PERIODIC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SIMPLE_FOURIER_CONVERGENCE_PERIODIC = prove
 (`!f t.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (\x. (f(x + t) - f(t)) / sin(x / &2))
        absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> ((\n. sum (0..n)
                      (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> f(t)) sequentially`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[REALLIM_NULL] THEN
  MP_TAC(ISPECL [`\x. (f:real->real)(x) - f(t)`; `t:real`; `&0`]
        FOURIER_SUM_LIMIT_DIRICHLET_KERNEL) THEN
  MP_TAC(ISPECL [`f:real->real`; `--pi`; `pi`; `t:real`]
        ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET) THEN
  ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_SUB;
               ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
  MATCH_MP_TAC(TAUT `(a ==> c) /\ b ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[FOURIER_COEFFICIENT_SUB; FOURIER_COEFFICIENT_CONST;
                 ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REALLIM_TRANSFORM_EVENTUALLY) THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN SIMP_TAC[SUM_CLAUSES_LEFT; LE_0] THEN
    MATCH_MP_TAC(REAL_ARITH
     `s:real = u /\ ft * t = x ==> (f0 - ft) * t + s = (f0 * t + u) - x`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[LE_1; ARITH; REAL_SUB_RZERO];
      REWRITE_TAC[trigonometric_set; REAL_MUL_LZERO; COS_0] THEN
      MATCH_MP_TAC(REAL_FIELD `&0 < s ==> (f * s) * &1 / s = f`) THEN
      MATCH_MP_TAC SQRT_POS_LT THEN MP_TAC PI_POS THEN REAL_ARITH_TAC];
    MP_TAC(ISPECL [`\x. (f:real->real)(x) - f(t)`; `t:real`; `&0`]
        FOURIER_SUM_LIMIT_DIRICHLET_KERNEL) THEN
    MP_TAC(ISPECL [`f:real->real`; `--pi`; `pi`; `t:real`]
          ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET) THEN
    ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_SUB;
                 ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
    SUBGOAL_THEN
     `!n. real_integral (real_interval [--pi,pi])
                        (\x. dirichlet_kernel n x * (f(x + t) - f(t))) =
          real_integral (real_interval [--pi,pi])
                        (\x. sin((&n + &1 / &2) * x) *
                             inv(&2) * (f(x + t) - f(t)) / sin(x / &2))`
     (fun th -> REWRITE_TAC[th])
    THENL
     [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN
      EXISTS_TAC `{&0}` THEN REWRITE_TAC[REAL_NEGLIGIBLE_SING] THEN
      REWRITE_TAC[IN_DIFF; IN_SING; IN_REAL_INTERVAL] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[dirichlet_kernel] THEN
      REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_AC];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RZERO] THEN
    MATCH_MP_TAC RIEMANN_LEBESGUE_SIN_HALF THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_LMUL THEN ASM_REWRITE_TAC[]]);;
```
### Informal statement
For any real-valued function `f` and any real number `t`, if
1. `f` is absolutely real integrable on the real interval from `-pi` to `pi`, and
2. the function mapping `x` to `(f(x + t) - f(t)) / sin(x / 2)` is absolutely real integrable on the real interval from `-pi` to `pi`, and
3. for all `x`, `f(x + 2 * pi) = f(x)`,
then the sequence of partial sums of the Fourier series of `f` at `t`, given by the function mapping `n` to the sum from `0` to `n` of `fourier_coefficient f k * trigonometric_set k t` (where `k` is the summation index), converges sequentially to `f(t)`.

### Informal sketch
The proof demonstrates the convergence of the Fourier series of a periodic and integrable function `f` at a point `t`, under certain integrability conditions.

- The proof starts by applying the `FOURIER_SUM_LIMIT_DIRICHLET_KERNEL` theorem, related to expressing the partial sums of a Fourier series using the Dirichlet kernel and the function's difference. This introduces conditions involving `f(x) - f(t)`.
- The integrability condition is transformed using `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET` and `REAL_ARITH` to account for the periodicity of `f`. Simplifications are performed using `ABSOLUTELY_REAL_INTEGRABLE_SUB` and `ABSOLUTELY_REAL_INTEGRABLE_CONST`.
- Then the proof splits into two subgoals, each relating to the limit. The first subgoal handles a simplified version of the partial Fourier sum, and eventually proves it converges to 0. The second makes extensive use of the properties of definite integrals:
  - The first subgoal derives an expression related to `sum (0..n) (fourier_coefficient f k * trigonometric_set k t)`.
  - `FOURIER_COEFFICIENT_SUB` and other theorems are employed to simplify the expression.
  - The limit is transformed using `REALLIM_TRANSFORM_EVENTUALLY`, `EVENTUALLY_SEQUENTIALLY`.
  - Next, an existential claim is introduced using `EXISTS_TAC` and several simplification tactics.
  - The second subgoal uses `FOURIER_SUM_LIMIT_DIRICHLET_KERNEL` again, and `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`, along with integrability manipulations.
  - An integral is transformed from the dirichlet kernel to the sine representation using `REAL_INTEGRAL_SPIKE` and subsequent steps.
  - Riemann-Lebesgue Lemma is applied using `RIEMANN_LEBESGUE_SIN_HALF` and `ABSOLUTELY_REAL_INTEGRABLE_LMUL` to show the integral goes to zero.

### Mathematical insight
This theorem provides sufficient conditions for the pointwise convergence of a Fourier series. The conditions require the function to be absolutely integrable and also that a related function involving `(f(x+t) - f(t))/sin(x/2)` is absolutely integrable which relates to a form of smoothness or limited variation near the point `t`. It relies on the Dirichlet kernel representation of the partial Fourier sums and ultimately utilizes the Riemann-Lebesgue lemma.

### Dependencies
- `REALLIM_NULL`
- `FOURIER_SUM_LIMIT_DIRICHLET_KERNEL`
- `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`
- `REAL_ARITH`
- `ABSOLUTELY_REAL_INTEGRABLE_SUB`
- `ABSOLUTELY_REAL_INTEGRABLE_CONST`
- `FOURIER_COEFFICIENT_SUB`
- `FOURIER_COEFFICIENT_CONST`
- `REALLIM_TRANSFORM_EVENTUALLY`
- `EVENTUALLY_SEQUENTIALLY`
- `SUM_CLAUSES_LEFT`
- `LE_0`
- `SUM_EQ_NUMSEG`
- `LE_1`
- `ARITH`
- `REAL_SUB_RZERO`
- `trigonometric_set`
- `REAL_MUL_LZERO`
- `COS_0`
- `SQRT_POS_LT`
- `PI_POS`
- `REAL_INTEGRAL_SPIKE`
- `REAL_NEGLIGIBLE_SING`
- `IN_DIFF`
- `IN_SING`
- `IN_REAL_INTERVAL`
- `dirichlet_kernel`
- `REAL_DIV`
- `REAL_INV_MUL`
- `REAL_MUL_AC`
- `REAL_MUL_RZERO`
- `RIEMANN_LEBESGUE_SIN_HALF`
- `ABSOLUTELY_REAL_INTEGRABLE_LMUL`

### Porting notes (optional)
- This theorem involves concepts from real analysis and measure theory. Ensure the target proof assistant has adequate support for these.
- The proof relies heavily on rewriting and simplification. The port may require finding equivalent tactics or lemmas in the target system.
- The `FOURIER_SUM_LIMIT_DIRICHLET_KERNEL` is a key theorem. Ensure it and its dependencies are ported first.


---

## REAL_SIN_X2_ZEROS

### Name of formal statement
REAL_SIN_X2_ZEROS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_SIN_X2_ZEROS = prove
 (`{x | sin(x / &2) = &0} = IMAGE (\n. &2 * pi * n) integer`,
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[IN_ELIM_THM; SIN_EQ_0; REAL_ARITH
   `y / &2 = n * pi <=> &2 * pi * n = y`] THEN
  REWRITE_TAC[PI_NZ; REAL_RING
   `&2 * pi * m = &2 * pi * n <=> pi = &0 \/ m = n`] THEN
  MESON_TAC[IN]);;
```
### Informal statement
The set of real numbers `x` such that `sin(x / 2)` equals 0 is equal to the image of the set of integers under the function that maps `n` to `2 * pi * n`.

### Informal sketch
The proof proceeds as follows:
- First, rewrite the equality of sets using `SURJECTIVE_IMAGE_EQ` to transform the goal into an equality of two functions, showing that each injects into the other
- Then, rewrite using `IN_ELIM_THM` to reduce the set membership to a predicate, `SIN_EQ_0` which converts `sin(x/2) = 0` to `x/2 = n * pi` for some integer `n`.
- Apply real arithmetic `y / 2 = n * pi <=> 2 * pi * n = y`.
- Simplify using `PI_NZ` (pi is not zero), and `REAL_RING`'s ring properties, specifically to show `2 * pi * m = 2 * pi * n <=> pi = 0 \/ m = n.`
- Finally, use `MESON_TAC` with `IN` (integer membership) to discharge the final goal and complete the proof.

### Mathematical insight
This theorem precisely characterizes the zeroes of the sine function scaled by a factor of 1/2. It demonstrates that these zeroes occur exactly at integer multiples of `2 * pi`. This is a fundamental property of the sine function, crucial for understanding its periodicity and behavior.

### Dependencies
- Theorems: `IN_ELIM_THM`, `SIN_EQ_0`, `PI_NZ`
- Definitions: `integer`, `sin`
- Axioms: `REAL_ARITH`, `REAL_RING`, `IN`
- Tactics: `MESON_TAC`, `REWRITE_TAC`, `CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ`


---

## HOELDER_FOURIER_CONVERGENCE_PERIODIC

### Name of formal statement
HOELDER_FOURIER_CONVERGENCE_PERIODIC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HOELDER_FOURIER_CONVERGENCE_PERIODIC = prove
 (`!f d M a t.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f(x + &2 * pi) = f(x)) /\
        &0 < d /\ &0 < a /\
        (!x. abs(x - t) < d ==> abs(f x - f t) <= M * abs(x - t) rpow a)
        ==> ((\n. sum (0..n)
                      (\k. fourier_coefficient f k * trigonometric_set k t))
             ---> f t) sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SIMPLE_FOURIER_CONVERGENCE_PERIODIC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
    `?e. &0 < e /\
         !x. abs(x) < e
             ==> abs((f (x + t) - f t) / sin (x / &2))
                 <= &4 * abs M * abs(x) rpow (a - &1)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(REAL_DIFF_CONV
     `((\x. sin(x / &2)) has_real_derivative w) (atreal (&0))`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[COS_0; REAL_MUL_RID] THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_ATREAL; REALLIM_ATREAL] THEN
    DISCH_THEN(MP_TAC o SPEC `&1 / &4`) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[SIN_0; REAL_SUB_RZERO] THEN DISCH_THEN
     (X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*"))) THEN
    EXISTS_TAC `min d e:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `sin(x / &2) = &0` THENL
     [ONCE_REWRITE_TAC[real_div] THEN ASM_REWRITE_TAC[REAL_INV_0] THEN
      REWRITE_TAC[GSYM REAL_ABS_RPOW; GSYM REAL_ABS_MUL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `x = &0` THENL
     [ASM_REWRITE_TAC[real_div; REAL_SUB_REFL; REAL_ADD_LID;
                      REAL_MUL_LZERO] THEN
      REWRITE_TAC[GSYM REAL_ABS_RPOW; GSYM REAL_ABS_MUL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `x:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP (REAL_ARITH
     `abs(x - &1 / &2) < &1 / &4 ==> &1 / &4 <= abs(x)`)) THEN
    SUBGOAL_THEN
     `abs((f(x + t) - f t) / sin (x / &2)) =
      abs(inv(sin(x / &2) / x)) * abs(f(x + t) - f t) / abs(x)`
    SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_INV] THEN
      UNDISCH_TAC `~(x = &0)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    SIMP_TAC[REAL_ABS_POS; REAL_LE_DIV] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_ABS_INV] THEN
      SUBST1_TAC(REAL_ARITH `&4 = inv(&1 / &4)`) THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; GSYM REAL_ABS_NZ; GSYM REAL_MUL_ASSOC] THEN
      GEN_REWRITE_TAC (funpow 3 RAND_CONV) [GSYM REAL_POW_1] THEN
      ASM_SIMP_TAC[GSYM RPOW_POW; GSYM RPOW_ADD; GSYM REAL_ABS_NZ] THEN
      REWRITE_TAC[REAL_ARITH `a - &1 + &1 = a`] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `M * abs((x + t) - t) rpow a` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_ARITH `(x + t) - t:real = x`] THEN
        REWRITE_TAC[GSYM REAL_ABS_RPOW] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_bounded (IMAGE (\x. inv(sin(x / &2)))
                (real_interval[--pi,pi] DIFF real_interval(--e,e)))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC REAL_COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL] THEN
      STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC REAL_CONTINUOUS_INV THEN REWRITE_TAC[NETLIMIT_ATREAL] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
        REAL_DIFFERENTIABLE_TAC;
        DISCH_TAC THEN MP_TAC(ISPEC `x / &2` SIN_EQ_0_PI) THEN
        ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_COMPACT_EQ_BOUNDED_CLOSED] THEN
      SIMP_TAC[REAL_CLOSED_DIFF; REAL_CLOSED_REAL_INTERVAL;
               REAL_OPEN_REAL_INTERVAL] THEN
      MATCH_MP_TAC REAL_BOUNDED_SUBSET THEN
      EXISTS_TAC `real_interval[--pi,pi]` THEN
      REWRITE_TAC[REAL_BOUNDED_REAL_INTERVAL; SUBSET_DIFF]];
    SIMP_TAC[REAL_BOUNDED_POS; FORALL_IN_IMAGE; IN_REAL_INTERVAL; IN_DIFF] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC)] THEN
  MATCH_MP_TAC
    REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\x:real. max (B * abs(f(x + t) - f t))
                           ((&4 * abs M) * abs(x) rpow (a - &1))` THEN
  MP_TAC(ISPECL [`f:real->real`; `--pi`; `pi`; `t:real`]
        ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET) THEN
  ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_MEASURABLE_ON_DIV THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_IMP_REAL_MEASURABLE THEN
      MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
      ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_SUB;
                   ABSOLUTELY_REAL_INTEGRABLE_CONST];
      MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
      REAL_DIFFERENTIABLE_TAC;
      REWRITE_TAC[REAL_SIN_X2_ZEROS] THEN
      MATCH_MP_TAC REAL_NEGLIGIBLE_COUNTABLE THEN
      MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[COUNTABLE_INTEGER]];
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_MAX THEN
    ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_LMUL;
       ABSOLUTELY_REAL_INTEGRABLE_ABS;
       ABSOLUTELY_REAL_INTEGRABLE_SUB; ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_LMUL THEN
    MP_TAC(ISPECL
     [`\x. inv(a) * x rpow a`; `\x. x rpow (a - &1)`; `&0`; `pi`]
     REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR) THEN
    REWRITE_TAC[PI_POS_LE] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_RPOW THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
        REAL_DIFF_TAC THEN
        MAP_EVERY UNDISCH_TAC [`&0 < a`; `&0 < x`] THEN CONV_TAC REAL_FIELD];
      DISCH_THEN(ASSUME_TAC o MATCH_MP HAS_REAL_INTEGRAL_INTEGRABLE)] THEN
    MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_REAL_INTEGRABLE THEN
    SIMP_TAC[RPOW_POS_LE; REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_COMBINE THEN EXISTS_TAC `&0` THEN
    REWRITE_TAC[REAL_NEG_LE0; PI_POS_LE] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_INTEGRABLE_REFLECT] THEN
      REWRITE_TAC[REAL_ABS_NEG; REAL_NEG_NEG; REAL_NEG_0];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        REAL_INTEGRABLE_EQ)) THEN
    SIMP_TAC[IN_REAL_INTERVAL; real_abs];
    RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
    ASM_CASES_TAC `abs(x) < e` THENL
     [MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= max a b`) THEN
      ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC];
      MATCH_MP_TAC(REAL_ARITH `x <= a ==> x <= max a b`) THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      REWRITE_TAC[real_div; REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      REWRITE_TAC[GSYM real_div] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC]]);;
```
### Informal statement
For any real-valued function `f`, real numbers `d`, `M`, and `a`, and a real number `t`, if
1. `f` is absolutely real integrable on the closed real interval from `-pi` to `pi`, and
2. for all `x`, `f(x + 2 * pi) = f(x)` (i.e., `f` is periodic with period `2 * pi`), and
3. `0 < d` and `0 < a`, and
4. for all `x`, if `abs(x - t) < d`, then `abs(f x - f t) <= M * abs(x - t)^a`,

then the sequence whose `n`-th term is the sum from `0` to `n` of `fourier_coefficient f k * trigonometric_set k t` converges sequentially to `f t` as `n` tends to infinity.

### Informal sketch
The proof proceeds as follows:
- Start with the `SIMPLE_FOURIER_CONVERGENCE_PERIODIC` theorem and rewrite using assumptions.
- Reduce the problem to showing the existence of some `e > 0` such that for all `x` with `abs(x) < e`, `abs((f (x + t) - f t) / sin (x / 2)) <= 4 * abs M * abs(x)^(a - 1)`.
- Find suitable `e`  and instantiate its existence. We pick `min d e`, where `e` is determined later.
- Perform case splits involving `sin(x / 2) = 0` and `x = 0`: In these cases, prove the inequality directly using the assumptions.
- When `sin(x / 2) != 0` and `x != 0`, manipulate the expression `abs((f(x + t) - f t) / sin (x / 2))` to get it into a more manageable form: `abs(inv(sin(x / 2) / x)) * abs(f(x + t) - f t) / abs(x)`.
- Use the Hölder condition to bound `abs(f(x + t) - f t)` and `abs(inv(sin(x / 2) / x))`.

- Show that the image of the function `inv(sin(x/2))` over the interval `[-pi, pi]` excluding `(-e,e)` is bounded.
- Use `REAL_COMPACT_IMP_BOUNDED` and `REAL_COMPACT_CONTINUOUS_IMAGE` to prove that `inv(sin(x/2))`is bounded within `[-pi,pi]` outside the interval `(-e, e)`.

- Apply `REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE`.
- Apply `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`.
- Show measurability of `f(x+t)/sin(x/2)` for `x` in `[-pi, pi]`. Show the function is absolutely integrable by bounding this function from above by `max (B * abs(f(x + t) - f t)) ((4 * abs M) * abs(x) rpow (a - 1))`
- Apply `REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR`.

### Mathematical insight
This theorem states that under certain conditions, the Fourier series of a periodic function converges to the value of the function at a point. The conditions are that function is absolutely integrable, periodic, and satisfies a Hölder condition. The Hölder condition is a smoothness condition that is weaker than differentiability but stronger than continuity, ensuring that the function does not oscillate too wildly near the point `t`.

### Dependencies
- `SIMPLE_FOURIER_CONVERGENCE_PERIODIC`
- `REAL_DIFF_CONV`
- `COS_0`
- `REAL_MUL_RID`
- `HAS_REAL_DERIVATIVE_ATREAL`
- `REALLIM_ATREAL`
- `SIN_0`
- `REAL_SUB_RZERO`
- `real_div`
- `REAL_INV_0`
- `GSYM REAL_ABS_RPOW`
- `GSYM REAL_ABS_MUL`
- `REAL_SUB_REFL`
- `REAL_ADD_LID`
- `REAL_MUL_LZERO`
- `REAL_LE_MUL2`
- `REAL_ABS_DIV`
- `REAL_ABS_INV`
- `REAL_LE_DIV`
- `REAL_ABS_POS`
- `REAL_LE_INV2`
- `REAL_LE_LDIV_EQ`
- `GSYM REAL_MUL_ASSOC`
- `GSYM RPOW_POW`
- `GSYM RPOW_ADD`
- `GSYM REAL_ABS_NZ`
- `REAL_ARITH `a - &1 + &1 = a``
- `REAL_LE_TRANS`
- `REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN`
- `REAL_CONTINUOUS_ATREAL_WITHINREAL`
- `REAL_CONTINUOUS_INV`
- `NETLIMIT_ATREAL`
- `REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL`
- `REAL_COMPACT_IMP_BOUNDED`
- `REAL_COMPACT_CONTINUOUS_IMAGE`
- `REAL_CLOSED_DIFF`
- `REAL_CLOSED_REAL_INTERVAL`
- `REAL_OPEN_REAL_INTERVAL`
- `REAL_BOUNDED_SUBSET`
- `REAL_BOUNDED_REAL_INTERVAL`
- `SUBSET_DIFF`
- `REAL_COMPACT_EQ_BOUNDED_CLOSED`
- `REAL_SIN_X2_ZEROS`
- `COUNTABLE_IMAGE`
- `COUNTABLE_INTEGER`
- `REAL_NEGLIGIBLE_COUNTABLE`
- `ISPEC `x / &2` SIN_EQ_0_PI`
- `REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE`
- `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`
- `REAL_ARITH `pi - --pi = &2 * pi``
- `REAL_MEASURABLE_ON_DIV`
- `INTEGRABLE_IMP_REAL_MEASURABLE`
- `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE`
- `ABSOLUTELY_REAL_INTEGRABLE_SUB`
- `ABSOLUTELY_REAL_INTEGRABLE_CONST`
- `CONTINUOUS_IMP_REAL_MEASURABLE_ON`
- `REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL`
- `ABSOLUTELY_REAL_INTEGRABLE_MAX`
- `ABSOLUTELY_REAL_INTEGRABLE_LMUL`
- `ABSOLUTELY_REAL_INTEGRABLE_ABS`
- `REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR`
- `PI_POS_LE`
- `REAL_CONTINUOUS_ON_LMUL`
- `REAL_CONTINUOUS_ON_RPOW`
- `NONNEGATIVE_ABSOLUTELY_REAL_INTEGRABLE`
- `RPOW_POS_LE`
- `REAL_ABS_POS`
- `REAL_INTEGRABLE_COMBINE`
- `REAL_NEG_LE0`
- `GSYM REAL_INTEGRABLE_REFLECT`
- `REAL_ABS_NEG`
- `REAL_NEG_NEG`
- `REAL_NEG_0`
- `IMP_CONJ_ALT`

### Porting notes (optional)
- The tactic script is very detailed and uses multiple conversions to perform arithmetic reasoning, which can be tedious to reproduce in other systems.
- The proof relies heavily on real analysis theorems, so make sure that the target theorem prover has well-developed real analysis libraries.


---

## LIPSCHITZ_FOURIER_CONVERGENCE_PERIODIC

### Name of formal statement
LIPSCHITZ_FOURIER_CONVERGENCE_PERIODIC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LIPSCHITZ_FOURIER_CONVERGENCE_PERIODIC = prove
 (`!f d M t.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f(x + &2 * pi) = f(x)) /\
        &0 < d /\ (!x. abs(x - t) < d ==> abs(f x - f t) <= M * abs(x - t))
        ==> ((\n. sum (0..n)
                      (\k. fourier_coefficient f k * trigonometric_set k t))
             ---> f t) sequentially`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOELDER_FOURIER_CONVERGENCE_PERIODIC THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `M:real`; `&1`] THEN
  ASM_REWRITE_TAC[RPOW_POW; REAL_POW_1; REAL_LT_01]);;
```
### Informal statement
For any function `f`, real number `d`, real number `M`, and real number `t`, if the following conditions hold:
1. `f` is absolutely real-integrable on the real interval `[--pi, pi]`.
2. For all `x`, `f(x + 2 * pi) = f(x)` (i.e., `f` is periodic with period `2 * pi`).
3. `0 < d` and for all `x`, if `abs(x - t) < d`, then `abs(f x - f t) <= M * abs(x - t)` (i.e. `f` satisfies a Lipschitz condition at `t`).

Then, the sequence defined by the partial sums of the Fourier series of `f` at `t` converges to `f t` sequentially, where the partial sums are given by
`\n. sum (0..n) (\k. fourier_coefficient f k * trigonometric_set k t)`.

### Informal sketch
The proof proceeds as follows:
- Strip the goal.
- Apply the theorem `HOELDER_FOURIER_CONVERGENCE_PERIODIC` using `MATCH_MP_TAC`. This reduces the goal to showing that the Lipschitz condition implies the Hölder condition with exponent 1.
- Introduce the witnesses `d:real`, `M:real`, and `&1` using repeated applications of `EXISTS_TAC`.
- Use `ASM_REWRITE_TAC` with the rewrite rules `RPOW_POW`, `REAL_POW_1`, and `REAL_LT_01` to simplify the resulting goal, which amounts to proving the Hölder condition given the Lipschitz assumptions.

### Mathematical insight
This theorem establishes that the Fourier series of a periodic function `f` converges to `f(t)` at a point `t` if `f` is absolutely integrable on `[--pi, pi]` and satisfies a Lipschitz condition at `t`. The Lipschitz condition provides a bound on the rate of change of the function near `t`, ensuring sufficient regularity for convergence. It’s a classical result in Fourier analysis showing pointwise convergence under mild regularity conditions.

### Dependencies
- `HOELDER_FOURIER_CONVERGENCE_PERIODIC`
- `RPOW_POW`
- `REAL_POW_1`
- `REAL_LT_01`


---

## BIDIFFERENTIABLE_FOURIER_CONVERGENCE_PERIODIC

### Name of formal statement
BIDIFFERENTIABLE_FOURIER_CONVERGENCE_PERIODIC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BIDIFFERENTIABLE_FOURIER_CONVERGENCE_PERIODIC = prove
 (`!f t. f absolutely_real_integrable_on real_interval[--pi,pi] /\
         (!x. f(x + &2 * pi) = f(x)) /\
         f real_differentiable (atreal t within {x | t < x}) /\
         f real_differentiable (atreal t within {x | x < t})
         ==> ((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> f t) sequentially`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[real_differentiable; HAS_REAL_DERIVATIVE_WITHINREAL] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `B1:real` (LABEL_TAC "1"))
   (X_CHOOSE_THEN `B2:real` (LABEL_TAC "2"))) THEN
  MATCH_MP_TAC LIPSCHITZ_FOURIER_CONVERGENCE_PERIODIC THEN
  REMOVE_THEN "1" (MP_TAC o GEN_REWRITE_RULE I [REALLIM_WITHINREAL]) THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[IN_ELIM_THM; REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "1"))) THEN
  REMOVE_THEN "2" (MP_TAC o GEN_REWRITE_RULE I [REALLIM_WITHINREAL]) THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[IN_ELIM_THM; REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "2"))) THEN
  MAP_EVERY EXISTS_TAC [`min d1 d2:real`; `abs B1 + abs B2 + &1`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (REAL_ARITH `x = t \/ t < x \/ x < t`)
  THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM; REAL_MUL_RZERO; REAL_LE_REFL];
    ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; GSYM REAL_ABS_DIV;
                 REAL_ARITH `t < x ==> &0 < abs(x - t)`] THEN
    REMOVE_THEN "1" (MP_TAC o SPEC `x:real`) THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; GSYM REAL_ABS_DIV;
                 REAL_ARITH `x < t ==> &0 < abs(x - t)`] THEN
    REMOVE_THEN "2" (MP_TAC o SPEC `x:real`) THEN ASM_REAL_ARITH_TAC]);;
```

### Informal statement
For any function `f` and real number `t`, if `f` is absolutely real integrable on the closed real interval from `-pi` to `pi`, `f` is periodic with period `2 * pi` (i.e., for all `x`, `f(x + 2 * pi) = f(x)`), `f` is real differentiable at `t` from the right (i.e., within the set of real numbers `x` such that `t < x`), and `f` is real differentiable at `t` from the left (i.e., within the set of real numbers `x` such that `x < t`), then the sequence of partial sums of the Fourier series of `f` at `t` converges sequentially to `f(t)`. The nth partial sum of the Fourier series is given by `sum (0..n) (\k. fourier_coefficient f k * trigonometric_set k t)`.

### Informal sketch
The proof proceeds as follows:
- Assume the premises: `f` is absolutely integrable on `[-pi, pi]`, `f` is periodic with period `2*pi`, `f` is right-differentiable at `t`, and `f` is left-differentiable at `t`.
- Rewrite the differentiability assumptions using `HAS_REAL_DERIVATIVE_WITHINREAL` to introduce the real derivatives from the left and right.
- Use `LIPSCHITZ_FOURIER_CONVERGENCE_PERIODIC` as a key lemma. This lemma requires `f` to be Lipschitz continuous.
- To apply the Lipschitz lemma, demonstrate Lipschitz continuity by showing that the left and right derivatives exist at `t`. This involves extracting `B1` and `B2` from the right and left differentiability.
- Apply `REALLIM_WITHINREAL` to eliminate the `within` condition of the real limit.
- Instantiate the limit definitions, introducing `d1` and `d2` (deltas) associated with the given epsilons for the limits from the left and right.
- Choose `min d1 d2` as the delta for the Lipschitz condition.
- Introduce an arbitrary `x` and consider the cases `x = t`, `t < x`, and `x < t`.
- Show that in each case, the required inequality for the Lipschitz condition holds. The cases `t < x` and `x < t` involve using previously introduced `specs` and some real arithmetic lemmas.

### Mathematical insight
This theorem establishes the convergence of the Fourier series for a function `f` at a point `t`, given that `f` is absolutely integrable, periodic, and differentiable from both sides at `t`. The importance lies in providing conditions under which the Fourier series representation of a function converges to the function's value. In particular, it leverages the `LIPSCHITZ_FOURIER_CONVERGENCE_PERIODIC` theorem, showing that the existence of left and right derivatives is sufficient to ensure the Lipschitz condition required by that theorem.

### Dependencies
- `absolutely_real_integrable_on`
- `real_interval`
- `real_differentiable`
- `atreal`
- `fourier_coefficient`
- `trigonometric_set`
- `LIPSCHITZ_FOURIER_CONVERGENCE_PERIODIC`
- `HAS_REAL_DERIVATIVE_WITHINREAL`
- `REALLIM_WITHINREAL`
- `IN_ELIM_THM`
- `REAL_LT_01`
- `REAL_LT_MIN`
- `REAL_SUB_REFL`
- `REAL_ABS_NUM`
- `REAL_MUL_RZERO`
- `REAL_LE_REFL`
- `GSYM REAL_LE_LDIV_EQ`
- `GSYM REAL_ABS_DIV`
- `REAL_ARITH`

### Porting notes
- The theorem relies on differentiability at a single point; porting may need careful consideration of how differentiability or Lipschitz continuity is represented within a particular proof assistant.
- The proof uses real arithmetic extensively, so automation of real arithmetic is beneficial for porting.
- The tactic `REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (REAL_ARITH x = t \/ t < x \/ x < t)` splits proof goals into cases based on the ordering of real numbers. This is a common pattern.


---

## DIFFERENTIABLE_FOURIER_CONVERGENCE_PERIODIC

### Name of formal statement
DIFFERENTIABLE_FOURIER_CONVERGENCE_PERIODIC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIFFERENTIABLE_FOURIER_CONVERGENCE_PERIODIC = prove
 (`!f t. f absolutely_real_integrable_on real_interval[--pi,pi] /\
         (!x. f(x + &2 * pi) = f(x)) /\
         f real_differentiable (atreal t)
         ==> ((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> f t) sequentially`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC BIDIFFERENTIABLE_FOURIER_CONVERGENCE_PERIODIC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  UNDISCH_TAC `f real_differentiable (atreal t)` THEN
  REWRITE_TAC[real_differentiable] THEN MATCH_MP_TAC MONO_EXISTS THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_ATREAL_WITHIN]);;
```
### Informal statement
For all functions `f` and all real numbers `t`, if `f` is absolutely real integrable on the real interval from `-pi` to `pi`, and for all `x`, `f(x + 2*pi) = f(x)`, and `f` is real differentiable at `t`, then the sequence defined by the partial sums from `0` to `n` of the Fourier series of `f` at `t`, converges to `f(t)` sequentially.

### Informal sketch
The proof proceeds as follows:
- Strip the quantifiers and assumptions.
- Apply `BIDIFFERENTIABLE_FOURIER_CONVERGENCE_PERIODIC`.
- Rewrite using assumptions.
- Split conjunction via `CONJ_TAC`.
- Discharge the assumption that `f` is real differentiable at `t`.
- Rewrite using the definition of `real_differentiable`.
- Apply `MONO_EXISTS`.
- Rewrite using the definition of `HAS_REAL_DERIVATIVE_ATREAL_WITHIN`.

### Mathematical insight
This theorem establishes that the Fourier series of a periodic function `f` converges to the value of the function at any point `t` where `f` is differentiable. This is a fundamental result in Fourier analysis, connecting the smoothness of a function to the convergence of its Fourier series.

### Dependencies
- Theorems: `BIDIFFERENTIABLE_FOURIER_CONVERGENCE_PERIODIC`
- Definitions: `real_differentiable`, `HAS_REAL_DERIVATIVE_ATREAL_WITHIN`


---

## ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED

### Name of formal statement
ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED = prove
 (`!f n c.
        f absolutely_real_integrable_on real_interval [--pi,pi] /\
        (!x. f(x + &2 * pi) = f(x))
        ==> (\x. dirichlet_kernel n x * f(t + x))
            absolutely_real_integrable_on real_interval[--pi,pi] /\
            (\x. dirichlet_kernel n x * f(t - x))
            absolutely_real_integrable_on real_interval[--pi,pi] /\
            (\x. dirichlet_kernel n x * c)
            absolutely_real_integrable_on real_interval[--pi,pi]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL THENL
   [ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET THEN
    ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`];
    REWRITE_TAC[absolutely_real_integrable_on] THEN
    ONCE_REWRITE_TAC[GSYM REAL_INTEGRABLE_REFLECT] THEN
    REWRITE_TAC[GSYM absolutely_real_integrable_on] THEN
    REWRITE_TAC[real_sub; REAL_NEG_NEG] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET THEN
    ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`];
    REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_CONST]]);;
```
### Informal statement
For any function `f` and natural number `n` and real number `c`, if the function `f` is absolutely Riemann integrable on the real interval from `-pi` to `pi`, and `f` is periodic with period `2 * pi` (i.e., `f(x + 2 * pi) = f(x)` for all `x`), then the following three conditions hold:
1. The function defined by `dirichlet_kernel n x * f(t + x)` is absolutely Riemann integrable on the real interval from `-pi` to `pi`.
2. The function defined by `dirichlet_kernel n x * f(t - x)` is absolutely Riemann integrable on the real interval from `-pi` to `pi`.
3. The function defined by `dirichlet_kernel n x * c` is absolutely Riemann integrable on the real interval from `-pi` to `pi`.

### Informal sketch
The proof proceeds by assuming that `f` is absolutely Riemann integrable on `[-pi, pi]` and periodic with period `2 * pi`.
- The goal is to prove the absolute Riemann integrability of three functions involving the `dirichlet_kernel`.
- The proof strategy uses `ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL` to establish absolute integrability given absolute integrability of the original function.
- For the first function, `dirichlet_kernel n x * f(t + x)`, the periodicity of `f` and `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET` are used to show that the offset does not affect integrability.
- We use `REAL_ARITH pi - --pi = &2 * pi` to match the required period.
- For the second function, `dirichlet_kernel n x * f(t - x)`, the proof uses `REAL_INTEGRABLE_REFLECT` to relate the integral of `f(t - x)` to the integral of `f(t + x)` using `real_sub` and `REAL_NEG_NEG`
-Again, `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET` and `REAL_ARITH pi - --pi = &2 * pi` are used.
- For the third function, `dirichlet_kernel n x * c`, the proof directly uses `ABSOLUTELY_REAL_INTEGRABLE_CONST` to establish its absolute integrability.

### Mathematical insight
This theorem shows that multiplying the Dirichlet kernel by a periodic, absolutely integrable function `f` or a constant `c` preserves absolute integrability. This is crucial for establishing convergence results for Fourier series. By exploiting the symmetry, the reflected function can also be proven to be absolutely integrable.

### Dependencies
- Theorem: `ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL`
- Theorem: `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`
- Theorem: `REAL_INTEGRABLE_REFLECT`
- Theorem: `ABSOLUTELY_REAL_INTEGRABLE_CONST`

### Porting notes (optional)
- Reflecting tactics in other proof assistants may vary. Ensure the reflection mappings are correct and that the relevant lemmas are available or can be proven.
- Absolute integrability requires careful handling of measure theory concepts; ensure that the target system has suitable support.


---

## ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED_PART

### Name of formal statement
ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED_PART

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED_PART = prove
 (`!f n d c.
        f absolutely_real_integrable_on real_interval [--pi,pi] /\
        (!x. f(x + &2 * pi) = f(x)) /\ d <= pi
        ==> (\x. dirichlet_kernel n x * f(t + x))
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. dirichlet_kernel n x * f(t - x))
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. dirichlet_kernel n x * c)
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. dirichlet_kernel n x * (f(t + x) + f(t - x)))
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. dirichlet_kernel n x * ((f(t + x) + f(t - x)) - c))
            absolutely_real_integrable_on real_interval[&0,d]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o MATCH_MP
  ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED) ASSUME_TAC) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  MATCH_MP_TAC(TAUT
   `(a /\ b /\ c) /\ (a /\ b /\ c ==> d /\ e)
    ==> a /\ b /\ c /\ d /\ e`) THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `real_interval[--pi,pi]` THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN MP_TAC PI_POS THEN
    ASM_REAL_ARITH_TAC;
    SIMP_TAC[REAL_ADD_LDISTRIB; REAL_SUB_LDISTRIB;
             ABSOLUTELY_REAL_INTEGRABLE_ADD;
             ABSOLUTELY_REAL_INTEGRABLE_SUB]]);;
```

### Informal statement
For all functions `f`, natural numbers `n`, and real numbers `d` and `c`, if `f` is absolutely real integrable on the real interval `[--pi, pi]` and for all `x`, `f(x + 2 * pi) = f(x)` and `d <= pi`, then the function defined by `x` maps to `dirichlet_kernel n x * f(t + x)` is absolutely real integrable on the real interval `[&0, d]`, and the function defined by `x` maps to `dirichlet_kernel n x * f(t - x)` is absolutely real integrable on the real interval `[&0, d]`, and the function defined by `x` maps to `dirichlet_kernel n x * c` is absolutely real integrable on the real interval `[&0, d]`, and the function defined by `x` maps to `dirichlet_kernel n x * (f(t + x) + f(t - x))` is absolutely real integrable on the real interval `[&0, d]`, and the function defined by `x` maps to `dirichlet_kernel n x * ((f(t + x) + f(t - x)) - c)` is absolutely real integrable on the real interval `[&0, d]`.

### Informal sketch

- The proof starts by assuming the hypothesis `f` is absolutely real integrable on `real_interval [--pi,pi]`, `f(x + &2 * pi) = f(x)` for all `x`, and `d <= pi`.
- It applies `ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED` to the assumptions to obtain the absolute real integrability for functions involving the `dirichlet_kernel`.
- It uses the theorem that if a function is absolutely real integrable on an interval, it is also absolutely real integrable on any subinterval of that interval which requires showing `real_interval[&0, d]` is a subinterval of `real_interval[--pi, pi]`.
- Finally, it applies theorems about absolutely real integrable functions and sums and differences of such functions. This leverages `REAL_ADD_LDISTRIB`, `REAL_SUB_LDISTRIB`, `ABSOLUTELY_REAL_INTEGRABLE_ADD`, `ABSOLUTELY_REAL_INTEGRABLE_SUB`.

### Mathematical insight
This theorem establishes the absolute integrability of certain functions involving the Dirichlet kernel and a periodic, absolutely integrable function. These results are a prerequisite for proving the convergence of Fourier series. The Dirichlet kernel is central to Fourier analysis proofs, so proving theorems about its interaction with other functions is important.

### Dependencies

- **Theorems:**
  - `ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED`
  - `ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL`
  - `ABSOLUTELY_REAL_INTEGRABLE_ADD`
  - `ABSOLUTELY_REAL_INTEGRABLE_SUB`

- **Other:**
  - `REAL_ADD_LDISTRIB`
  - `REAL_SUB_LDISTRIB`
  - `SUBSET_REAL_INTERVAL`
  - `PI_POS`


---

## FOURIER_SUM_OFFSET_DIRICHLET_KERNEL_HALF

### Name of formal statement
FOURIER_SUM_OFFSET_DIRICHLET_KERNEL_HALF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_SUM_OFFSET_DIRICHLET_KERNEL_HALF = prove
 (`!f n t.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> sum(0..2*n) (\k. fourier_coefficient f k * trigonometric_set k t) -
            l =
            real_integral (real_interval[&0,pi])
                          (\x. dirichlet_kernel n x *
                               ((f(t + x) + f(t - x)) - &2 * l)) / pi`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FOURIER_SUM_OFFSET_DIRICHLET_KERNEL] THEN
  MATCH_MP_TAC(MATCH_MP (REAL_FIELD
   `&0 < pi ==> x = y + pi * l ==> x / pi - l = y / pi`) PI_POS) THEN
  MP_TAC(ISPECL [`f:real->real`; `--pi`; `pi`; `t:real`]
        ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET) THEN
  ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_REFLECT_AND_ADD;
               ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL;
               ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
  REWRITE_TAC[MESON[REAL_ADD_SYM]
   `dirichlet_kernel n x * f(x + t) = dirichlet_kernel n x * f(t + x)`] THEN
  REWRITE_TAC[DIRICHLET_KERNEL_NEG; GSYM real_sub] THEN
  MP_TAC(SPEC `n:num` HAS_REAL_INTEGRAL_DIRICHLET_KERNEL_HALF) THEN
  DISCH_THEN(MP_TAC o SPEC `&2 * l` o MATCH_MP HAS_REAL_INTEGRAL_RMUL) THEN
  REWRITE_TAC[REAL_ARITH `pi / &2 * &2 * l = pi * l`] THEN
  DISCH_THEN(SUBST1_TAC o GSYM o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
  ONCE_REWRITE_TAC[GSYM REAL_EQ_SUB_RADD] THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_ADD_LDISTRIB] THEN
  MATCH_MP_TAC(GSYM REAL_INTEGRAL_SUB) THEN
  MP_TAC(GEN `c:real` (ISPECL [`f:real->real`; `n:num`; `pi`; `c:real`]
        ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED_PART)) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; FORALL_AND_THM] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM REAL_ADD_LDISTRIB;
               ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE]);;
```

### Informal statement
For all real-valued functions `f`, natural numbers `n`, and real numbers `t`, if `f` is absolutely real integrable on the real interval from `-pi` to `pi` and `f` is periodic with period `2 * pi` (i.e., for all `x`, `f(x + 2 * pi) = f(x)`), then the difference between the partial Fourier sum of `f` up to `2*n` evaluated at `t` and a real number `l` is equal to the real integral from `0` to `pi` of the product of the `dirichlet_kernel` of order `n` evaluated at `x` and `(f(t + x) + f(t - x) - 2 * l)`, divided by `pi`.

### Informal sketch
The proof proceeds as follows:
- Start with the assumption that `f` is absolutely real integrable on `[-pi, pi]` and periodic with period `2 * pi`.
- Apply `FOURIER_SUM_OFFSET_DIRICHLET_KERNEL` to express the Fourier sum as an integral over `[-pi, pi]`.
- Shift the integration interval to `[0, 2*pi]`.
- Split the integral into two parts: from `0` to `pi` and from `pi` to `2*pi`.
- Reflect the second integral and add it to the first, resulting in an integral from `0` to `pi`.
- Use the fact that the integral of the `dirichlet_kernel` from `0` to `pi` is `pi/2` to simplify the expression.
- Apply properties of real integrals and Fourier coefficients.
- Deduce the final result.
- Use `ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED_PART` to simplify the integral with the `dirichlet_kernel`.

### Mathematical insight
This theorem provides an alternative representation of the difference between the partial Fourier sum of a function and a real number `l`, expressing it as an integral involving the Dirichlet kernel and the function's values around the point `t`. This half-range formula is useful because it reduces the range of integration to `[0, pi]`, simplifying calculations and analysis in some situations. Specifically, the theorem connects the error in approximating a function by its Fourier series to an integral involving the Dirichlet kernel, which is a fundamental object in Fourier analysis.

### Dependencies
- `FOURIER_SUM_OFFSET_DIRICHLET_KERNEL`
- `PI_POS`
- `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`
- `REAL_ARITH`
- `REAL_INTEGRAL_REFLECT_AND_ADD`
- `ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL`
- `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE`
- `DIRICHLET_KERNEL_NEG`
- `HAS_REAL_INTEGRAL_DIRICHLET_KERNEL_HALF`
- `HAS_REAL_INTEGRAL_RMUL`
- `REAL_INTEGRAL_UNIQUE`
- `REAL_EQ_SUB_RADD`
- `REAL_SUB_LDISTRIB`
- `REAL_ADD_LDISTRIB`
- `ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED_PART`
- `REAL_LE_REFL`
- `FORALL_AND_THM`
- `REAL_ADD_LDISTRIB`

### Porting notes (optional)
For porting to other proof assistants, ensure that the definitions and properties of real integrals, Fourier coefficients, and the Dirichlet kernel are available. The handling of absolute real integrability and periodicity might require adaptation depending on the target system's formalization of real analysis.
The tactic `MESON[REAL_ADD_SYM] ...` indicate usage of external automatic solver, which might be necessary to replace by a script of manual steps, depending on the automation level of the target system.


---

## FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_HALF

### Name of formal statement
FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_HALF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_HALF = prove
 (`!f t l.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> (((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> l) sequentially <=>
            ((\n. real_integral (real_interval[&0,pi])
                                (\x. dirichlet_kernel n x *
                                     ((f(t + x) + f(t - x)) - &2 * l)))
             ---> &0) sequentially)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM FOURIER_SUM_LIMIT_PAIR] THEN
  GEN_REWRITE_TAC LAND_CONV [REALLIM_NULL] THEN
  ASM_SIMP_TAC[FOURIER_SUM_OFFSET_DIRICHLET_KERNEL_HALF] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REALLIM_NULL_RMUL_EQ THEN
  MP_TAC PI_POS THEN CONV_TAC REAL_FIELD);;
```
### Informal statement
For all functions `f`, real numbers `t`, and real numbers `l`, if `f` is absolutely real integrable on the real interval from `-pi` to `pi` and for all `x`, `f(x + 2*pi) = f(x)`, then the sequence defined by the partial sums of the Fourier series of `f` evaluated at `t` converges to `l` sequentially if and only if the sequence defined by the real integral from `0` to `pi` of the product of the `n`-th Dirichlet kernel and the difference between `f(t + x) + f(t - x)` and `2*l` converges to `0` sequentially.

### Informal sketch
The proof proceeds as follows:
- Strip the quantifiers and assumptions.
- Simplify using `GSYM FOURIER_SUM_LIMIT_PAIR`, which likely relates the limit of the Fourier sum to an integral involving a Dirichlet kernel.
- Rewrite using `REALLIM_NULL` from right to left, probably changing an equivalence to equality with zero.
- Simplify using `FOURIER_SUM_OFFSET_DIRICHLET_KERNEL_HALF`, which could deal with offsetting the Dirichlet Kernel by a half.
- Rewrite using `real_div`, likely introducing a division by two.
- Apply `REALLIM_NULL_RMUL_EQ` which states that if the limit of $a*x$ is zero and a is not zero, then the limit of x is zero and match it with the assumption that $\pi > 0$
- Prove that $\pi > 0$
- Prove an equation in the real field using `CONV_TAC REAL_FIELD`

### Mathematical insight
This theorem establishes the equivalence between the convergence of the Fourier series of a function `f` at a point `t` to a value `l`, and the convergence to zero of a certain integral involving `f`, `t`, `l`, and the Dirichlet kernel. This is a standard result in Fourier analysis, relating pointwise convergence of Fourier series to an integral condition. The integrability and periodicity assumptions on `f` are standard conditions for the validity of such results.

### Dependencies
- `FOURIER_SUM_LIMIT_PAIR`
- `REALLIM_NULL`
- `FOURIER_SUM_OFFSET_DIRICHLET_KERNEL_HALF`
- `real_div`
- `REALLIM_NULL_RMUL_EQ`
- `PI_POS`
- `REAL_FIELD`

### Porting notes (optional)
- The definitions of `absolutely_real_integrable_on`, `real_interval`, `fourier_coefficient`, `trigonometric_set`, `dirichlet_kernel`, and the real limit operator `--->` will need to be available or defined.
- Pay attention to the assumptions on `f` (integrability and periodicity). In other systems, these might need to be expressed using different predicates or type classes.
- The tactics `REPEAT STRIP_TAC`, `ASM_SIMP_TAC`, `GEN_REWRITE_TAC`, `REWRITE_TAC`, `MATCH_MP_TAC`, `MP_TAC` and `CONV_TAC` are specific to HOL Light and need to be replaced with corresponding tactics or proof strategies in the target proof assistant.


---

## RIEMANN_LOCALIZATION_INTEGRAL

### Name of formal statement
RIEMANN_LOCALIZATION_INTEGRAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RIEMANN_LOCALIZATION_INTEGRAL = prove
 (`!d f g.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        g absolutely_real_integrable_on real_interval[--pi,pi] /\
        &0 < d /\ (!x. abs(x) < d ==> f x = g x)
        ==> ((\n. real_integral (real_interval[--pi,pi])
                                (\x. dirichlet_kernel n x * f(x)) -
                  real_integral (real_interval[--pi,pi])
                                (\x. dirichlet_kernel n x * g(x)))
             ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. real_integral (real_interval[--pi,pi])
                      (\x. dirichlet_kernel n x * f(x)) -
        real_integral (real_interval[--pi,pi])
                      (\x. dirichlet_kernel n x * g(x)) =
        real_integral (real_interval[--pi,pi])
                      (\x. dirichlet_kernel n x *
                           (if abs(x) < d then &0 else f(x) - g(x)))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL;
                 ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
                 GSYM REAL_INTEGRAL_SUB] THEN
    X_GEN_TAC `n:num` THEN MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN
    EXISTS_TAC `{}:real->bool` THEN
    REWRITE_TAC[REAL_NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN
    X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    STRIP_TAC THEN REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN AP_TERM_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_ARITH `&0 = x - y <=> x = y`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. real_integral (real_interval[--pi,pi])
                      (\x. dirichlet_kernel n x *
                           (if abs x < d then &0 else f(x) - g(x))) =
        real_integral (real_interval[--pi,pi])
                      (\x. sin((&n + &1 / &2) * x) *
                           inv(&2) *
                           (if abs x < d then &0 else f(x) - g(x)) /
                           sin(x / &2))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN
    EXISTS_TAC `{&0}` THEN REWRITE_TAC[REAL_NEGLIGIBLE_SING] THEN
    REWRITE_TAC[IN_DIFF; IN_SING; IN_REAL_INTERVAL] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[dirichlet_kernel] THEN
    REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_AC];
    ALL_TAC] THEN
  MATCH_MP_TAC RIEMANN_LEBESGUE_SIN_HALF THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_LMUL THEN
  SUBGOAL_THEN `real_bounded (IMAGE (\x. inv(sin(x / &2)))
                (real_interval[--pi,pi] DIFF real_interval(--d,d)))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC REAL_COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL] THEN
      STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC REAL_CONTINUOUS_INV THEN REWRITE_TAC[NETLIMIT_ATREAL] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
        REAL_DIFFERENTIABLE_TAC;
        DISCH_TAC THEN MP_TAC(ISPEC `x / &2` SIN_EQ_0_PI) THEN
        ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_COMPACT_EQ_BOUNDED_CLOSED] THEN
      SIMP_TAC[REAL_CLOSED_DIFF; REAL_CLOSED_REAL_INTERVAL;
               REAL_OPEN_REAL_INTERVAL] THEN
      MATCH_MP_TAC REAL_BOUNDED_SUBSET THEN
      EXISTS_TAC `real_interval[--pi,pi]` THEN
      REWRITE_TAC[REAL_BOUNDED_REAL_INTERVAL; SUBSET_DIFF]];
    SIMP_TAC[REAL_BOUNDED_POS; FORALL_IN_IMAGE; IN_REAL_INTERVAL; IN_DIFF] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC)] THEN
  MATCH_MP_TAC
    REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\x:real. B * abs(f(x) - g(x))` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_MEASURABLE_ON_DIV THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_MEASURABLE_ON_CASES THEN
      ASM_SIMP_TAC[INTEGRABLE_IMP_REAL_MEASURABLE; REAL_MEASURABLE_ON_0;
                   ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
                   ABSOLUTELY_REAL_INTEGRABLE_SUB] THEN
      SUBGOAL_THEN `{x | abs x < d} = real_interval(--d,d)`
       (fun th -> REWRITE_TAC[th; REAL_LEBESGUE_MEASURABLE_INTERVAL]) THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
      REAL_DIFFERENTIABLE_TAC;
      SUBGOAL_THEN `{x | sin(x / &2) = &0} = IMAGE (\n. &2 * pi * n) integer`
      SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
        REWRITE_TAC[IN_ELIM_THM; SIN_EQ_0; REAL_ARITH
         `y / &2 = n * pi <=> &2 * pi * n = y`] THEN
        REWRITE_TAC[PI_NZ; REAL_RING
          `&2 * pi * m = &2 * pi * n <=> pi = &0 \/ m = n`] THEN
        MESON_TAC[IN];
        MATCH_MP_TAC REAL_NEGLIGIBLE_COUNTABLE THEN
        MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[COUNTABLE_INTEGER]]];
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_LMUL THEN
    ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_ABS;
                 ABSOLUTELY_REAL_INTEGRABLE_SUB];
    X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    STRIP_TAC THEN COND_CASES_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ABS_NUM] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ONCE_REWRITE_TAC[real_div] THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_ABS_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC]]);;
```
### Informal statement
For all real numbers `d`, and for all functions `f` and `g` from real numbers to real numbers, if `f` is absolutely real integrable on the real interval from `-pi` to `pi`, and `g` is absolutely real integrable on the real interval from `-pi` to `pi`, and `0 < d`, and for all `x`, if the absolute value of `x` is less than `d`, then `f x` equals `g x`, then the sequence whose `n`-th term is the difference between the real integral from `-pi` to `pi` of the function mapping `x` to the product of the `n`-th `dirichlet_kernel` evaluated at `x` and `f x`, and the real integral from `-pi` to `pi` of the function mapping `x` to the product of the `n`-th `dirichlet_kernel` evaluated at `x` and `g x`, converges sequentially to `0`.

### Informal sketch
The proof demonstrates that if two absolutely integrable functions `f` and `g` agree on a neighborhood of 0, then the difference of their integrals against the Dirichlet kernel converges to 0. The main steps are:

- **Reduction to a Single Integral:** Show that the difference of the two integrals equals the integral of `dirichlet_kernel n x * (if abs x < d then &0 else f(x) - g(x))`. This integral represents the contribution from outside the interval `(-d, d)`.
- **Rewriting with Sine Function:** Replace the `dirichlet_kernel` with its sine representation: `sin((&n + &1 / &2) * x) * inv(&2) * (if abs x < d then &0 else f(x) - g(x)) / sin(x / &2)`. This step prepares the integral for the Riemann-Lebesgue lemma.
- **Applying Riemann-Lebesgue Lemma:** Invoke the `RIEMANN_LEBESGUE_SIN_HALF` theorem. This lemma requires showing that the function being integrated is absolutely integrable.
- **Showing Absolute Integrability:**  Prove that `(if abs x < d then &0 else f(x) - g(x)) / sin(x / &2)` is absolutely integrable on `real_interval[--pi,pi]`.  This involves showing:
    - `1 / sin(x / &2)` is bounded on `real_interval[--pi,pi] DIFF real_interval(--d,d)`. This is achieved by showing that the image of this set under the mapping `inv(sin(x / &2))` is compact and therefore bounded.
    - The function `(if abs x < d then &0 else f(x) - g(x)) / sin(x / &2)` is measurable. Cases are considered where `abs x < d` and when `abs x >= d`.
    - Establishing a bound for the absolute value of the integrand using integrability assumptions: This eventually needs `B * abs(f(x) - g(x))` where B is a real number.
- **Using Integrability Assumptions:** Exploit the absolute integrability of `f` and `g` as well as measurability results to complete the proof.

### Mathematical insight
This theorem embodies the localization principle in Fourier analysis: the convergence of the Fourier series at a point depends only on the behavior of the function in a neighborhood of that point. The `dirichlet_kernel` is used in forming partial sums of the Fourier series, so this theorem shows that if we change the function outside a small interval around a point, the limit of the integral with the Dirichlet kernel remains unchanged.

### Dependencies
*Definitions*
- `dirichlet_kernel`

*Theorems*
- `ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL`
- `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE`
- `REAL_INTEGRAL_SUB`
- `REAL_INTEGRAL_SPIKE`
- `RIEMANN_LEBESGUE_SIN_HALF`
- `ABSOLUTELY_REAL_INTEGRABLE_LMUL`
- `REAL_COMPACT_IMP_BOUNDED`
- `REAL_COMPACT_CONTINUOUS_IMAGE`
- `REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN`
- `REAL_CONTINUOUS_ATREAL_WITHINREAL`
- `REAL_CONTINUOUS_INV`
- `REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL`
- `REAL_COMPACT_EQ_BOUNDED_CLOSED`
- `REAL_CLOSED_DIFF`
- `REAL_CLOSED_REAL_INTERVAL`
- `REAL_OPEN_REAL_INTERVAL`
- `REAL_BOUNDED_SUBSET`
- `REAL_BOUNDED_REAL_INTERVAL`
- `REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE`
- `REAL_MEASURABLE_ON_DIV`
- `REAL_MEASURABLE_ON_CASES`
- `INTEGRABLE_IMP_REAL_MEASURABLE`
- `REAL_MEASURABLE_ON_0`
- `ABSOLUTELY_REAL_INTEGRABLE_SUB`
- `CONTINUOUS_IMP_REAL_MEASURABLE_ON`
- `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE`
- `ABSOLUTELY_REAL_INTEGRABLE_ABS`

*Axioms*
- `PI_NZ`

### Porting notes (optional)
- The proof relies heavily on real analysis theorems and properties of integrals. Ensure the target proof assistant has comparable libraries.
- The use of `COND_CASES_TAC` suggests a reliance on case splitting based on conditions within the integrand. Ensure similar case-splitting capabilities are available.
- The frequent manipulation of real arithmetic expressions suggests that a reasonably powerful real arithmetic tactic is necessary.


---

## RIEMANN_LOCALIZATION_INTEGRAL_RANGE

### Name of formal statement
RIEMANN_LOCALIZATION_INTEGRAL_RANGE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RIEMANN_LOCALIZATION_INTEGRAL_RANGE = prove
 (`!d f.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        &0 < d /\ d <= pi
        ==> ((\n. real_integral (real_interval[--pi,pi])
                                (\x. dirichlet_kernel n x * f(x)) -
                  real_integral (real_interval[--d,d])
                                (\x. dirichlet_kernel n x * f(x)))
             ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN MP_TAC
   (ISPECL[`d:real`; `f:real->real`;
           `\x. if x IN real_interval[--d,d] then f x else &0`]
     RIEMANN_LOCALIZATION_INTEGRAL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM ABSOLUTELY_REAL_INTEGRABLE_RESTRICT_UNIV] THEN
      REWRITE_TAC[MESON[] `(if p then if q then x else y else y) =
                           (if p /\ q then x else y)`] THEN
      REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_RESTRICT_UNIV; GSYM IN_INTER] THEN
      REWRITE_TAC[INTER; IN_REAL_INTERVAL] THEN
      ASM_SIMP_TAC[REAL_ARITH
       `&0 < d /\ d <= pi
        ==> ((--pi <= x /\ x <= pi) /\ --d <= x /\ x <= d <=>
             --d <= x /\ x <= d)`] THEN
      REWRITE_TAC[GSYM real_interval] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
      REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC];
    REWRITE_TAC[MESON[REAL_MUL_RZERO]
     `a * (if p then b else &0) = if p then a * b else &0`] THEN
    SUBGOAL_THEN `real_interval[--d,d] SUBSET real_interval[--pi,pi]`
    MP_TAC THENL
     [REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP REAL_INTEGRAL_RESTRICT th])]]);;
```

### Informal statement
For any real-valued function `f` that is absolutely Riemann integrable on the real interval from `-pi` to `pi`, and for any real number `d` such that `0 < d` and `d <= pi`, it follows that the sequence defined by the difference between the Riemann integral of the product of the `dirichlet_kernel` function of order `n` and `f(x)` over the interval from `-pi` to `pi`, and the Riemann integral of the same product over the interval from `-d` to `d`, converges to 0 sequentially as `n` approaches infinity.

### Informal sketch
The proof demonstrates that as `n` tends to infinity, the integral of `f(x)` times the `dirichlet_kernel` over `[-pi, pi]` approaches the integral over `[-d, d]`.

- The proof starts by specializing the theorem `RIEMANN_LOCALIZATION_INTEGRAL` with `d`, `f`, and a modified version of `f` (namely, a function that equals `f(x)` if `x` is in `[-d, d]` and 0 otherwise).
- The goal is then rewritten using associativity and assumptions.
- The proof splits into two main subgoals using conjunction.
- The first subgoal shows that if `f` is absolutely integrable on `[-pi, pi]`, then the restriction of `f` to `[-d, d]` is also absolutely integrable. This involves rewriting the integrability condition using properties of the `real_interval` and applying `ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL`.
- The second subgoal shows that the integral of `dirichlet_kernel n x * (if x IN real_interval[--d,d] then f x else &0)` from `-pi` to `pi` is the same as the integral from `-d` to `d`. This uses the fact that the function `if x IN real_interval[--d,d] then f x else &0` is zero outside the interval `[-d, d]` and uses `REAL_INTEGRAL_RESTRICT`.

### Mathematical insight
This theorem shows that the behavior of the integral of a function multiplied by the Dirichlet kernel becomes localized around zero as `n` tends to infinity. Namely, the integral over a small interval `[-d, d]` approximates the integral over the full interval `[-pi, pi]` when `n` is large. This is important in the theory of Fourier series and harmonic analysis.

### Dependencies
- `ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL`
- `ABSOLUTELY_REAL_INTEGRABLE_RESTRICT_UNIV`
- `RIEMANN_LOCALIZATION_INTEGRAL`
- `REAL_INTEGRAL_RESTRICT`
- `dirichlet_kernel`
- `real_interval`

### Porting notes (optional)
- The primary challenge in porting lies in correctly defining and manipulating the `dirichlet_kernel` and the `real_integral`.
- Special care should be taken to ensure consistent handling of real intervals and the `if-then-else` constructs used extensively here.
- The HOL Light `MESON` calls indicate use of classical reasoning.


---

## RIEMANN_LOCALIZATION

### Name of formal statement
RIEMANN_LOCALIZATION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RIEMANN_LOCALIZATION = prove
 (`!t d c f g.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        g absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f(x + &2 * pi) = f(x)) /\ (!x. g(x + &2 * pi) = g(x)) /\
        &0 < d /\ (!x. abs(x - t) < d ==> f x = g x)
        ==> (((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> c) sequentially <=>
             ((\n. sum (0..n)
                       (\k. fourier_coefficient g k * trigonometric_set k t))
              ---> c) sequentially)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[FOURIER_SUM_LIMIT_DIRICHLET_KERNEL] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EQ THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC RIEMANN_LOCALIZATION_INTEGRAL THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET THEN
    ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`];
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET THEN
    ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC]);;
```

### Informal statement
For all real numbers `t`, `d`, and `c`, and for all real-valued functions `f` and `g`, if the following conditions hold:
1. `f` is absolutely Riemann integrable on the real interval `[-pi, pi]`.
2. `g` is absolutely Riemann integrable on the real interval `[-pi, pi]`.
3. `f` is periodic with period `2 * pi`; that is, for all `x`, `f(x + 2 * pi) = f(x)`.
4. `g` is periodic with period `2 * pi`; that is, for all `x`, `g(x + 2 * pi) = g(x)`.
5. `0 < d`.
6. For all `x`, if `|x - t| < d`, then `f x = g x`.
Then the sequence of partial sums of the Fourier series of `f` evaluated at `t` converges to `c` sequentially if and only if the sequence of partial sums of the Fourier series of `g` evaluated at `t` converges to `c` sequentially.
(Where the nth partial sum of the Fourier series of `f` evaluated at `t` is `sum (0..n) (\k. fourier_coefficient f k * trigonometric_set k t)`)

### Informal sketch
The theorem states that the convergence of the Fourier series of a function at a point depends only on the local behavior of the function around that point.

*   The proof starts by stripping the quantifiers and assumptions.
*   It uses `FOURIER_SUM_LIMIT_DIRICHLET_KERNEL` to express the partial sums of the Fourier series in terms of the Dirichlet kernel.
*   It rewrites using `REAL_ADD_SYM`.
*   Then `REALLIM_TRANSFORM_EQ` is applied.
*   The proof applies `RIEMANN_LOCALIZATION_INTEGRAL`, which presumably relates the convergence to an integral involving the difference of the functions and the Dirichlet kernel.
*   An appropriate `d:real` is chosen.
*   The proof splits into proving the integrability of `f` and `g` on shifted intervals, using the periodicity of `f` and `g` and `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`.
*   Finally, hypotheses are matched to complete the proof.

### Mathematical insight
This theorem, Riemann Localization, is a fundamental result in Fourier analysis. It asserts that the convergence of a Fourier series at a given point depends only on the local behavior of the function in an arbitrarily small neighborhood of that point. This is somewhat surprising, as the Fourier coefficients are defined by integrals over the entire domain of the function. The theorem highlights the local nature of convergence for Fourier series.

### Dependencies
- `FOURIER_SUM_LIMIT_DIRICHLET_KERNEL`
- `REAL_ADD_SYM`
- `REALLIM_TRANSFORM_EQ`
- `RIEMANN_LOCALIZATION_INTEGRAL`
- `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`
- `REAL_ARITH`


---

## RIEMANN_LOCALIZATION_INTEGRAL_RANGE_HALF

### Name of formal statement
RIEMANN_LOCALIZATION_INTEGRAL_RANGE_HALF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RIEMANN_LOCALIZATION_INTEGRAL_RANGE_HALF = prove
 (`!d f.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        &0 < d /\ d <= pi
        ==> ((\n. real_integral (real_interval[&0,pi])
                                (\x. dirichlet_kernel n x * (f(x) + f(--x))) -
                  real_integral (real_interval[&0,d])
                                (\x. dirichlet_kernel n x * (f(x) + f(--x))))
             ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN MP_TAC
   (SPECL [`d:real`; `f:real->real`] RIEMANN_LOCALIZATION_INTEGRAL_RANGE) THEN
  MP_TAC(GEN `n:num` (ISPECL [`f:real->real`; `n:num`]
    ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. (\x. dirichlet_kernel n x * f x) absolutely_real_integrable_on
        real_interval[--d,d]`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL) o SPEC `n:num`) THEN
    REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_INTEGRAL_REFLECT_AND_ADD;
                 ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
    REWRITE_TAC[DIRICHLET_KERNEL_NEG; GSYM REAL_ADD_LDISTRIB]]);;
```

### Informal statement
For any real-valued function `f` and any real number `d`, if `f` is absolutely Riemann integrable on the real interval from `-pi` to `pi`, and `0 < d` and `d <= pi`, then as `n` tends to infinity, the sequence whose `n`-th term is the difference between:
1. the real integral from `0` to `pi` of the function that maps `x` to the product of the `n`-th Dirichlet kernel at `x` and the sum of `f(x)` and `f(-x)`, and
2. the real integral from `0` to `d` of the function that maps `x` to the product of the `n`-th Dirichlet kernel at `x` and the sum of `f(x)` and `f(-x)`,
converges to `0` sequentially.

### Informal sketch
The proof proceeds as follows:
- Apply the theorem `RIEMANN_LOCALIZATION_INTEGRAL_RANGE` after specializing it to the given real number `d` and function `f`.
- Apply the theorem `ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL`, after generalizing to `n:num` and specializing to the given function `f` and `n:num`.
- Simplify using assumptions using `ASM_REWRITE_TAC`.
- Introduce a subgoal that `!n. (\x. dirichlet_kernel n x * f x) absolutely_real_integrable_on real_interval[--d,d]`.
- To prove the subgoal:
    - Generalize with respect to `n`.
    - Instantiate the theorem `ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL` after rewriting it with `IMP_CONJ` and specializing it with `n:num`; then use `MATCH_MP` and `MATCH_MP_TAC`.
    - Rewrite with `SUBSET_REAL_INTERVAL` and solve by arithmetic.
- Apply simplifications with `REAL_INTEGRAL_REFLECT_AND_ADD` and `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE` to simplify the remaining goal.
- Rewrite with `DIRICHLET_KERNEL_NEG` and the generalized symmetry of `REAL_ADD_LDISTRIB`.

### Mathematical insight
This theorem essentially states that the contribution to the integral involving the Dirichlet kernel and `f(x) + f(-x)` over the interval `[0, pi]` is localized around `0`. Removing the interval `[0, d]` where `d` is small results in an integral that tends to zero as `n` tends to infinity. This is a key step in understanding the convergence properties of Fourier series. The theorem exploits the integrability of `f` and the properties of the Dirichlet kernel.

### Dependencies
- `ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL`
- `RIEMANN_LOCALIZATION_INTEGRAL_RANGE`
- `ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL`
- `SUBSET_REAL_INTERVAL`
- `REAL_INTEGRAL_REFLECT_AND_ADD`
- `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE`
- `DIRICHLET_KERNEL_NEG`
- `REAL_ADD_LDISTRIB`

### Porting notes (optional)
When porting to other proof assistants:
- Ensure that the absolute integrability and sequential limits are defined appropriately.
- The properties of the Dirichlet kernel need to be ported accurately.
- The main difficulty might be in automating the proof steps, as the HOL Light proof script relies on specific tactics that may not have direct equivalents. You would need to find alternative ways to perform the same rewriting and simplification steps.


---

## FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_PART

### Name of formal statement
FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_PART

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_PART = prove
 (`!f t l d.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x) /\ &0 < d /\ d <= pi
        ==> (((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> l) sequentially <=>
            ((\n. real_integral (real_interval[&0,d])
                                (\x. dirichlet_kernel n x *
                                     ((f(t + x) + f(t - x)) - &2 * l)))
             ---> &0) sequentially)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_HALF] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EQ THEN
  REWRITE_TAC[REAL_ARITH `(x + y) - &2 * l = (x - l) + (y - l)`] THEN
  MP_TAC(MESON[real_sub] `!x. (f:real->real)(t - x) = f(t + --x)`) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
   MATCH_MP_TAC RIEMANN_LOCALIZATION_INTEGRAL_RANGE_HALF THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_SUB THEN
  REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET THEN
  ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`]);;
```
### Informal statement
For any real-valued function `f`, real number `t`, real numbers `l` and `d`, if `f` is absolutely Riemann integrable on the real interval from `-pi` to `pi`, and `f` is periodic with period `2*pi` (i.e., for all `x`, `f(x + 2*pi) = f(x)`), and `0 < d <= pi`, then the Fourier series of `f` evaluated at `t` converges to `l` sequentially if and only if the integral from `0` to `d` of the product of the `n`-th Dirichlet kernel and the difference between the sum `f(t + x) + f(t - x)` and `2*l` converges to `0` sequentially.

### Informal sketch
The proof proceeds as follows:
- Start by stripping the assumptions using `REPEAT STRIP_TAC`.
- Apply `FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_HALF` to reduce the goal to one half integral version.
- Transform the limit using `REALLIM_TRANSFORM_EQ`.
- Rewrite the expression `(x + y) - 2 * l` as `(x - l) + (y - l)`.
- Use the fact that `f(t - x) = f(t + --x)`.
- Discharge the assumption obtained after rewriting.
- Apply `RIEMANN_LOCALIZATION_INTEGRAL_RANGE_HALF`.
- Simplify using assumptions.
- Apply `ABSOLUTELY_REAL_INTEGRABLE_SUB`.
- Rewrite using `ABSOLUTELY_REAL_INTEGRABLE_CONST`.
- Rewrite using the symmetry of addition.
- Apply `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`.
- Simplify using the fact that `pi - --pi = 2 * pi`.

### Mathematical insight
This theorem provides a condition for the convergence of the Fourier series of a function `f` at a point `t`. It essentially states that the Fourier series converges to a value `l` if and only if a certain integral involving the Dirichlet kernel and the function `f` converges to zero. This integral represents a localized average of `f` around the point `t`, suggesting that the convergence of the Fourier series depends on the local behavior of the function.

### Dependencies
- `FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_HALF`
- `REALLIM_TRANSFORM_EQ`
- `RIEMANN_LOCALIZATION_INTEGRAL_RANGE_HALF`
- `ABSOLUTELY_REAL_INTEGRABLE_SUB`
- `ABSOLUTELY_REAL_INTEGRABLE_CONST`
- `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`


---

## REAL_INTEGRAL_DIRICHLET_KERNEL_MUL_EXPAND

### Name of formal statement
REAL_INTEGRAL_DIRICHLET_KERNEL_MUL_EXPAND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_INTEGRAL_DIRICHLET_KERNEL_MUL_EXPAND = prove
 (`!f n s. real_integral s (\x. dirichlet_kernel n x * f x) =
           real_integral s (\x. sin((&n + &1 / &2) * x) / (&2 * sin(x / &2)) *
                                f x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN
  EXISTS_TAC `{&0}` THEN REWRITE_TAC[REAL_NEGLIGIBLE_SING] THEN
  SIMP_TAC[IN_DIFF; IN_SING; dirichlet_kernel]);;
```
### Informal statement
For any function `f`, natural number `n`, and set `s`, the real integral of the product of the `dirichlet_kernel` of `n` and `f` over the set `s` is equal to the real integral of the product of `sin((&n + &1 / &2) * x) / (&2 * sin(x / &2))` and `f` over the set `s`.

### Informal sketch
The proof proceeds as follows:
- Apply the theorem `REAL_INTEGRAL_SPIKE`. This theorem likely relates to integrating functions with singularities, and the Dirichlet kernel has singularities.
- Perform an existential instantiation with `{&0}`, likely related to the location of the singularity
- Rewrite using `REAL_NEGLIGIBLE_SING`. This likely eliminates the singularity at zero, establishing equality by resolving issues at singularities.
- Simplify using `IN_DIFF`, `IN_SING`, and `dirichlet_kernel`. This step uses the definitions of sets describing differentiable areas (`IN_DIFF`), sets of singularities (`IN_SING`), and the definition of `dirichlet_kernel` to complete the proof.

### Mathematical insight
This theorem provides a more computationally amenable form for integrals involving the Dirichlet kernel by expressing it in terms of sines. The Dirichlet kernel is crucial in Fourier analysis, particularly in the study of Fourier series convergence. This result simplifies calculations involving the Dirichlet kernel in integration contexts, by replacing it with a more elementary trigonometric expression when multiplied by a function and integrated.

### Dependencies
- `REAL_INTEGRAL_SPIKE`
- `REAL_NEGLIGIBLE_SING`
- `IN_DIFF`
- `IN_SING`
- `dirichlet_kernel`


---

## REAL_INTEGRABLE_DIRICHLET_KERNEL_MUL_EXPAND

### Name of formal statement
REAL_INTEGRABLE_DIRICHLET_KERNEL_MUL_EXPAND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_INTEGRABLE_DIRICHLET_KERNEL_MUL_EXPAND = prove
 (`!f n s. (\x. dirichlet_kernel n x * f x) real_integrable_on s <=>
           (\x. sin((&n + &1 / &2) * x) / (&2 * sin(x / &2)) * f x)
           real_integrable_on s`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC REAL_INTEGRABLE_SPIKE THEN
  EXISTS_TAC `{&0}` THEN REWRITE_TAC[REAL_NEGLIGIBLE_SING] THEN
  SIMP_TAC[IN_DIFF; IN_SING; dirichlet_kernel]);;
```
### Informal statement
For any function `f`, natural number `n`, and set `s`, the function given by `λx. dirichlet_kernel n x * f x` is real integrable on `s` if and only if the function given by `λx. sin((&n + &1 / &2) * x) / (&2 * sin(x / &2)) * f x` is real integrable on `s`.

### Informal sketch
The proof proceeds by showing the equivalence of the two integrability conditions.
- The proof applies `REAL_INTEGRABLE_SPIKE` to prove that integrability holds if and only if the function `λx. dirichlet_kernel n x * f x` is integrable everywhere except at `{&0}` with `REAL_NEGLIGIBLE_SING` applied to show that `{&0}` is a real negligible set. The definition of `dirichlet_kernel` is expanded using `dirichlet_kernel`.

### Mathematical insight
This theorem demonstrates the equivalence between integrability involving the Dirichlet kernel and an alternative trigonometric expression. This allows to replace the `dirichlet_kernel` which has a potentially complex definition, with an equivalent expression.

### Dependencies
- Theorems:
    - `REAL_INTEGRABLE_SPIKE`
    - `REAL_NEGLIGIBLE_SING`

- Definitions:
    - `IN_DIFF`
    - `IN_SING`
    - `dirichlet_kernel`


---

## FOURIER_SUM_LIMIT_SINE_PART

### Name of formal statement
FOURIER_SUM_LIMIT_SINE_PART

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_SUM_LIMIT_SINE_PART = prove
 (`!f t l d.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x) /\ &0 < d /\ d <= pi
        ==> (((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> l) sequentially <=>
            ((\n. real_integral (real_interval[&0,d])
                                (\x. sin((&n + &1 / &2) * x) *
                                     ((f(t + x) + f(t - x)) - &2 * l) / x))
             ---> &0) sequentially)`,
  let lemma0 = prove
   (`!x. abs(sin(x) - x) <= abs(x) pow 3`,
    GEN_TAC THEN MP_TAC(ISPECL [`0`; `Cx x`] TAYLOR_CSIN) THEN
    REWRITE_TAC[VSUM_CLAUSES_NUMSEG; GSYM CX_SIN] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[complex_pow; COMPLEX_POW_1; COMPLEX_DIV_1; IM_CX] THEN
    REWRITE_TAC[GSYM CX_MUL; GSYM CX_SUB; COMPLEX_NORM_CX; REAL_ABS_0] THEN
    REWRITE_TAC[REAL_EXP_0; REAL_MUL_LID] THEN REAL_ARITH_TAC) in
  let lemma1 = prove
   (`!x. ~(x = &0) ==> abs(sin(x) / x - &1) <= x pow 2`,
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `abs x` THEN
    REWRITE_TAC[GSYM REAL_ABS_MUL; GSYM(CONJUNCT2 real_pow)] THEN
    ASM_REWRITE_TAC[GSYM REAL_ABS_NZ; ARITH] THEN
    ASM_SIMP_TAC[REAL_SUB_LDISTRIB; REAL_DIV_LMUL; REAL_MUL_RID] THEN
    REWRITE_TAC[lemma0]) in
  let lemma2 = prove
   (`!x. abs(x) <= &1 / &2  ==> abs(x) / &2 <= abs(sin x)`,
    REPEAT STRIP_TAC THEN MP_TAC(SPEC `x:real` lemma0) THEN
    MATCH_MP_TAC(REAL_ARITH
      `&4 * x3 <= abs x ==> abs(s - x) <= x3 ==> abs(x) / &2 <= abs s`) THEN
    REWRITE_TAC[REAL_ARITH
     `&4 * x pow 3 <= x <=> x * x pow 2 <= x * (&1 / &2) pow 2`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
    ASM_REAL_ARITH_TAC) in
  let lemma3 = prove
   (`!x. ~(x = &0) /\ abs x <= &1 / &2
         ==> abs(inv(sin x) - inv x) <= &2 * abs x`,
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `abs(sin x)` THEN
    REWRITE_TAC[GSYM REAL_ABS_MUL] THEN ASM_CASES_TAC `sin x = &0` THENL
     [MP_TAC(SPEC `x:real` SIN_EQ_0_PI) THEN
      MP_TAC PI_APPROX_32 THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[GSYM REAL_ABS_NZ; REAL_SUB_LDISTRIB; REAL_MUL_RINV] THEN
      REWRITE_TAC[REAL_ARITH `abs(&1 - s * inv x) = abs(s / x - &1)`] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(x:real) pow 2` THEN
      ASM_SIMP_TAC[lemma1] THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
      REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      MP_TAC(ISPEC `x:real` lemma2) THEN ASM_REAL_ARITH_TAC]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `t:real`; `l:real`; `d:real`]
        FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_PART) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EQ THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  MP_TAC(ISPECL [`f:real->real`; `--pi`; `pi`; `t:real`]
        ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET) THEN
  ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_ADD_SYM] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  GEN_REWRITE_TAC LAND_CONV [absolutely_real_integrable_on] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [GSYM REAL_INTEGRABLE_REFLECT] THEN
  REWRITE_TAC[GSYM absolutely_real_integrable_on; GSYM real_sub] THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_TAC THEN EXISTS_TAC
   `\n. real_integral (real_interval[&0,d])
                      (\x. sin((&n + &1 / &2) * x) *
                           (inv(&2 * sin(x / &2)) - inv x) *
                           ((f(t + x) + f(t - x)) - &2 * l))` THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN CONJ_TAC THENL
   [EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_INTEGRAL_DIRICHLET_KERNEL_MUL_EXPAND] THEN
    REWRITE_TAC[REAL_ARITH
     `a * (inv y - inv x) * b:real = a / y * b - a / x * b`] THEN
    REWRITE_TAC[REAL_ARITH `sin(y) * (a - b) / x = sin(y) / x * (a - b)`] THEN
    MATCH_MP_TAC REAL_INTEGRAL_SUB THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_INTEGRABLE_DIRICHLET_KERNEL_MUL_EXPAND] THEN
      MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL THEN
      EXISTS_TAC `real_interval[--pi,pi]` THEN CONJ_TAC THENL
      [ALL_TAC; REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL THEN
      ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_ADD;
                   ABSOLUTELY_REAL_INTEGRABLE_SUB;
                   ABSOLUTELY_REAL_INTEGRABLE_CONST];
      MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] REAL_INTEGRABLE_SPIKE) THEN
      EXISTS_TAC `\x. dirichlet_kernel n x * (&2 * sin(x / &2)) / x *
                      ((f(t + x) + f(t - x)) - &2 * l)` THEN
      EXISTS_TAC `{&0}` THEN REWRITE_TAC[REAL_NEGLIGIBLE_SING] THEN
      CONJ_TAC THENL
       [X_GEN_TAC `x:real` THEN
        REWRITE_TAC[IN_DIFF; IN_SING; IN_REAL_INTERVAL; REAL_MUL_ASSOC] THEN
        STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        ASM_REWRITE_TAC[dirichlet_kernel] THEN
        MATCH_MP_TAC(REAL_FIELD
         `~(x = &0) /\ ~(y = &0) ==> a / x = a / (&2 * y) * (&2 * y) / x`) THEN
        MP_TAC(ISPEC `x / &2` SIN_EQ_0_PI) THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
        MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL THEN
        EXISTS_TAC `real_interval[--pi,pi]` THEN CONJ_TAC THENL
         [ALL_TAC;
          REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC] THEN
        MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL THEN
        MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
        ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_ADD;
                     ABSOLUTELY_REAL_INTEGRABLE_SUB;
                     ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_MEASURABLE_ON_DIV THEN
          REWRITE_TAC[REAL_NEGLIGIBLE_SING; SING_GSPEC] THEN
          CONJ_TAC THEN MATCH_MP_TAC
            REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
          REWRITE_TAC[REAL_CLOSED_UNIV; REAL_CLOSED_REAL_INTERVAL] THEN
          REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
          REPEAT STRIP_TAC THEN
          MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
          MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
          REAL_DIFFERENTIABLE_TAC;
          ALL_TAC]]] THEN
    SUBGOAL_THEN `real_bounded (IMAGE (\x. &1 + (x / &2) pow 2)
                                      (real_interval[--pi,pi]))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN
      MATCH_MP_TAC REAL_COMPACT_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[REAL_COMPACT_INTERVAL] THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
      REAL_DIFFERENTIABLE_TAC;
      REWRITE_TAC[REAL_BOUNDED_POS; FORALL_IN_IMAGE] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*")) THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
      ASM_CASES_TAC `x = &0` THENL
       [ASM_REWRITE_TAC[real_div; REAL_INV_0; REAL_MUL_RID] THEN
        ASM_REAL_ARITH_TAC;
        REMOVE_THEN "*" (MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(REAL_ARITH
         `abs(z - &1) <= y ==> abs(&1 + y) <= B ==> abs(z) <= B`) THEN
        ASM_SIMP_TAC[REAL_FIELD
          `~(x = &0) ==> (&2 * y) / x = y / (x / &2)`] THEN
        MATCH_MP_TAC lemma1 THEN ASM_REAL_ARITH_TAC]];

    SUBGOAL_THEN `real_interval[&0,d] SUBSET real_interval[--pi,pi]`
    MP_TAC THENL
     [REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC
       [GSYM(MATCH_MP REAL_INTEGRAL_RESTRICT th)])] THEN
    REWRITE_TAC[MESON[REAL_MUL_LZERO; REAL_MUL_RZERO]
     `(if p x then a x * b x * c x else &0) =
      a x * (if p x then b x else &0) * c x`] THEN
    MATCH_MP_TAC RIEMANN_LEBESGUE_SIN_HALF THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_ADD;
                 ABSOLUTELY_REAL_INTEGRABLE_SUB;
                 ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_MEASURABLE_ON_CASES THEN
      REWRITE_TAC[REAL_MEASURABLE_ON_0; SET_RULE `{x | x IN s} = s`;
                  REAL_LEBESGUE_MEASURABLE_INTERVAL] THEN
      MATCH_MP_TAC REAL_MEASURABLE_ON_SUB THEN CONJ_TAC THEN
      GEN_REWRITE_TAC (LAND_CONV) [GSYM ETA_AX] THEN REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `inv x = &1 / x`] THEN
      MATCH_MP_TAC REAL_MEASURABLE_ON_DIV THEN
      SIMP_TAC[REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET;
               REAL_CLOSED_REAL_INTERVAL; REAL_CONTINUOUS_ON_CONST;
               REAL_CONTINUOUS_ON_ID; SING_GSPEC; REAL_NEGLIGIBLE_SING;
               REAL_CLOSED_UNIV] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
        REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
        REPEAT STRIP_TAC THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
        MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
        REAL_DIFFERENTIABLE_TAC;
        REWRITE_TAC[REAL_ARITH `&2 * x = &0 <=> x = &0`] THEN
        REWRITE_TAC[REAL_SIN_X2_ZEROS] THEN
        MATCH_MP_TAC REAL_NEGLIGIBLE_COUNTABLE THEN
        MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[COUNTABLE_INTEGER]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `real_bounded(IMAGE (\x. inv (&2 * sin (x / &2)) - inv x)
                         (real_interval[--pi,-- &1] UNION
                          real_interval[&1,pi]))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN
      MATCH_MP_TAC REAL_COMPACT_CONTINUOUS_IMAGE THEN
      SIMP_TAC[REAL_COMPACT_INTERVAL; REAL_COMPACT_UNION] THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
      REAL_DIFFERENTIABLE_TAC THEN MP_TAC(ISPEC `x / &2` SIN_EQ_0_PI) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_UNION]) THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_BOUNDED_POS; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[IN_REAL_INTERVAL; IN_UNION] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `max B (&2)` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    COND_CASES_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    ASM_CASES_TAC `abs(x) <= &1` THENL
     [ALL_TAC;
      MATCH_MP_TAC(REAL_ARITH `x <= B ==> x <= max B C`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC] THEN
    ASM_CASES_TAC `x = &0` THENL
     [ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_INV_0; SIN_0] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_INV_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH
     `abs(is - &2 * ix) <= &1 ==> abs(inv(&2) * is - ix) <= max B (&2)`) THEN
    REWRITE_TAC[GSYM real_div] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
     [GSYM REAL_INV_DIV] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * abs(x / &2)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC lemma3; ASM_REAL_ARITH_TAC] THEN
    ASM_REAL_ARITH_TAC]);;
```

### Informal statement
For any real-valued function `f`, real number `t`, real number `l`, and real number `d`, the following holds: if `f` is absolutely real integrable on the real interval from `-pi` to `pi`, and `f` is periodic with period `2 * pi` (i.e., `f(x + 2 * pi) = f(x)` for all `x`), and `0 < d` and `d <= pi`, then the sequence of partial Fourier sums of `f` at `t` converges sequentially to `l` if and only if the sequence of real integrals from `0` to `d` of `sin((n + 1/2) * x) * ((f(t + x) + f(t - x)) - 2 * l) / x` converges sequentially to `0`.

### Informal sketch
The proof shows that the convergence of the Fourier sum to a limit `l` is equivalent to the convergence of a certain integral to `0`.

- The proof starts by stripping the assumptions and applying `FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_PART`.
- Then, the statement undergoes transformations based on equality, application of `REALLIM_TRANSFORM_EQ` and `REALLIM_TRANSFORM_EVENTUALLY`. A periodic extension of `f` using `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET` is applied.
- The goal is reduced to showing the sequential convergence to zero of a particular integral involving a modified Dirichlet kernel. The difference between the Dirichlet kernel and its approximation `inv(2 * sin(x/2))` is considered.
- It then shows that the difference between the two integrals converges to zero. This is done by showing that the integral of the difference between the Dirichlet kernel and its approximation is absolutely integrable.
  - Several lemmas (`lemma0`, `lemma1`, `lemma2`, `lemma3`) are proved regarding the approximations of `sin(x)` near zero and the difference between `inv(sin x)` and `inv x`.
  - The proof involves establishing the integrability of various components, using theorems related to absolutely integrable functions, subintervals, and products. Real measurability conditions are also checked.
  - Boundedness properties and limits are invoked to ultimately show that the integral of the difference converges to zero, completing the proof.

### Mathematical insight
This theorem provides a condition for the convergence of the Fourier series of a function at a point `t` in terms of the limit of an integral. It connects the partial sums of the Fourier series to an integral involving a sine function and the function `f` evaluated near the point `t`. It represents a key step in proving pointwise convergence results for Fourier series. The integral condition amounts to a smoothness condition on `f` near `t`.

### Dependencies
- Theorems:
  - `FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_PART`
  - `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`
  - `REAL_INTEGRAL_DIRICHLET_KERNEL_MUL_EXPAND`
  - `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE`
  - `ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL`
  - `ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL`
  - `ABSOLUTELY_REAL_INTEGRABLE_ADD`
  - `ABSOLUTELY_REAL_INTEGRABLE_SUB`
  - `ABSOLUTELY_REAL_INTEGRABLE_CONST`
  - `REAL_INTEGRABLE_SPIKE`
  - `REAL_MEASURABLE_ON_DIV`
  - `ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT`
  - `REAL_COMPACT_IMP_BOUNDED`
  - `REAL_COMPACT_CONTINUOUS_IMAGE`
  - `RIEMANN_LEBESGUE_SIN_HALF`
  - `REAL_MEASURABLE_ON_CASES`
  - `REAL_NEGLIGIBLE_SING`
  - `COUNTABLE_IMAGE`
- Definitions:
  - `fourier_coefficient`
  - `trigonometric_set`
  - `absolutely_real_integrable_on`
  - `real_interval`
  - `sum`
  - `real_integral`
  - `sin`
  - `dirichlet_kernel`
  - `real_bounded`
  - `real_measurable_on`

### Porting notes (optional)
- The proof makes extensive use of real analysis theorems and tactics. The porter may need to adjust the tactic script in other systems based on differences in automation or library organization.
- The use of `MESON` is also apparent; while automatic, the specific theories invoked are important to replicate for correct automated reasoning.
- Care should be taken to ensure that the definitions of `absolutely_real_integrable_on`, `real_integral`, and `dirichlet_kernel` are compatible.


---

## FOURIER_DINI_TEST

### Name of formal statement
FOURIER_DINI_TEST

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_DINI_TEST = prove
 (`!f t l d.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x) /\
        &0 < d /\
        (\x. abs((f(t + x) + f(t - x)) - &2 * l) / x)
        real_integrable_on real_interval[&0,d]
        ==> ((\n. sum (0..n)
                      (\k. fourier_coefficient f k * trigonometric_set k t))
             ---> l) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `t:real`; `l:real`; `pi`]
                FOURIER_SUM_LIMIT_SINE_PART) THEN
  ASM_REWRITE_TAC[PI_POS; REAL_LE_REFL] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT) THEN
  REWRITE_TAC[real_continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `&0`) THEN
  ASM_SIMP_TAC[IN_REAL_INTERVAL; REAL_LE_REFL; REAL_LT_IMP_LE] THEN
  SIMP_TAC[REAL_INTEGRAL_NULL; REAL_LE_REFL] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ABBREV_TAC `dd = min d (min (k / &2) pi)` THEN
  DISCH_THEN(MP_TAC o SPEC `dd:real`) THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN ANTS_TAC THENL
   [MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < dd /\ dd <= d /\ dd <= pi /\ dd < k`
  STRIP_ASSUME_TAC THENL
   [MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `--pi`; `pi`; `t:real`]
      ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET) THEN
  ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_ADD_SYM] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  GEN_REWRITE_TAC LAND_CONV [absolutely_real_integrable_on] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [GSYM REAL_INTEGRABLE_REFLECT] THEN
  REWRITE_TAC[GSYM absolutely_real_integrable_on; GSYM real_sub] THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\x. ((f(t + x) + f(t - x)) - &2 * l) / x) absolutely_real_integrable_on
    real_interval[&0,dd]`
  ASSUME_TAC THENL
   [REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_REAL_MEASURABLE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_MEASURABLE_ON_DIV THEN
      SIMP_TAC[REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET;
               REAL_CLOSED_REAL_INTERVAL; REAL_CONTINUOUS_ON_CONST;
               REAL_CONTINUOUS_ON_ID; SING_GSPEC; REAL_NEGLIGIBLE_SING;
               REAL_CLOSED_UNIV] THEN
      MATCH_MP_TAC INTEGRABLE_IMP_REAL_MEASURABLE THEN
      MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`--pi`; `pi`] THEN
      ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
                   REAL_INTEGRABLE_ADD; REAL_INTEGRABLE_SUB;
                   REAL_INTEGRABLE_CONST] THEN
      REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0:real`; `d:real`] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE
         [TAUT `p ==> q ==> r <=> q ==> p ==> r`]
                REAL_INTEGRABLE_SPIKE)) THEN
        EXISTS_TAC `{}:real->bool` THEN REWRITE_TAC[REAL_NEGLIGIBLE_EMPTY] THEN
        SIMP_TAC[REAL_ABS_DIV; IN_REAL_INTERVAL; IN_DIFF] THEN
        SIMP_TAC[real_abs];
        REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. ((f(t + x) + f(t - x)) - &2 * l) / x) absolutely_real_integrable_on
    real_interval[dd,pi]`
  ASSUME_TAC THENL
   [REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `inv x = &1 / x`] THEN
      MATCH_MP_TAC REAL_MEASURABLE_ON_DIV THEN
      SIMP_TAC[REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET;
               REAL_CLOSED_REAL_INTERVAL; REAL_CONTINUOUS_ON_CONST;
               REAL_CONTINUOUS_ON_ID; SING_GSPEC; REAL_NEGLIGIBLE_SING;
               REAL_CLOSED_UNIV];
      REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN
      EXISTS_TAC `inv dd:real` THEN X_GEN_TAC `x:real` THEN
      REWRITE_TAC[IN_REAL_INTERVAL; REAL_ABS_INV] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL THEN
      EXISTS_TAC `real_interval[--pi,pi]` THEN
      ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_ADD;
                   ABSOLUTELY_REAL_INTEGRABLE_SUB;
                   ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
      REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!n. (\x. sin((&n + &1 / &2) * x) *
           ((f(t + x) + f(t - x)) - &2 * l) / x) absolutely_real_integrable_on
         real_interval[&0,dd]) /\
    (!n. (\x. sin((&n + &1 / &2) * x) *
          ((f(t + x) + f(t - x)) - &2 * l) / x) absolutely_real_integrable_on
         real_interval[dd,pi])`
  STRIP_ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
       REWRITE_TAC[REAL_CLOSED_UNIV; REAL_CLOSED_REAL_INTERVAL] THEN
       REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
       REPEAT STRIP_TAC THEN
       MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
       MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
       REAL_DIFFERENTIABLE_TAC;
       REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN
       EXISTS_TAC `&1` THEN REWRITE_TAC[SIN_BOUND]]);
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\x. if abs x < dd then &0
                    else ((f:real->real)(t + x) - l) / x`
     RIEMANN_LEBESGUE_SIN_HALF) THEN
  SIMP_TAC[REAL_INTEGRAL_REFLECT_AND_ADD;
           ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
           FOURIER_PRODUCTS_INTEGRABLE_STRONG] THEN
  ANTS_TAC THENL
   [ONCE_REWRITE_TAC[GSYM ABSOLUTELY_REAL_INTEGRABLE_RESTRICT_UNIV] THEN
    REWRITE_TAC[MESON[] `(if P x then if Q x then &0 else a x else &0) =
                         (if P x /\ ~Q x then a x else &0)`] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div] THEN
    REWRITE_TAC[MESON[REAL_MUL_RZERO; REAL_MUL_LZERO]
    `(if P x /\ Q x then a x * b x else &0) =
     (if Q x then a x else &0) * (if P x then b x else &0)`] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_RESTRICT_UNIV;
                 ABSOLUTELY_REAL_INTEGRABLE_SUB;
                 ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_MEASURABLE_ON_CASES THEN
      REWRITE_TAC[REAL_MEASURABLE_ON_0] THEN CONJ_TAC THENL
       [REWRITE_TAC[SET_RULE `{x | ~P x} = UNIV DIFF {x | P x}`] THEN
        REWRITE_TAC[REAL_LEBESGUE_MEASURABLE_COMPL] THEN
        REWRITE_TAC[REAL_ARITH `abs x < d <=> --d < x /\ x < d`] THEN
        REWRITE_TAC[GSYM real_interval; REAL_LEBESGUE_MEASURABLE_INTERVAL];
        GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[REAL_ARITH `inv x = &1 / x`] THEN
        MATCH_MP_TAC REAL_MEASURABLE_ON_DIV THEN
        SIMP_TAC[REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET;
                 REAL_CLOSED_REAL_INTERVAL; REAL_CONTINUOUS_ON_CONST;
                 REAL_CONTINUOUS_ON_ID; SING_GSPEC; REAL_NEGLIGIBLE_SING;
                 REAL_CLOSED_UNIV]];
      REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; IN_UNIV] THEN
      EXISTS_TAC `inv dd:real` THEN X_GEN_TAC `x:real` THEN
      REWRITE_TAC[REAL_NOT_LT] THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_ABS_NUM;
                   REAL_ABS_INV] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_NEG; REAL_MUL_RNEG; SIN_NEG; REAL_MUL_LNEG] THEN
  REWRITE_TAC[GSYM real_sub; GSYM REAL_SUB_LDISTRIB] THEN
  REWRITE_TAC[real_div; REAL_INV_NEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  REWRITE_TAC[REAL_ARITH
   `(if p then &0 else a) - (if p then &0 else --b) =
    (if p then &0 else a + b)`] THEN
  REWRITE_TAC[GSYM REAL_ADD_RDISTRIB] THEN REWRITE_TAC[GSYM real_div] THEN
  REWRITE_TAC[MESON[REAL_MUL_RZERO]
   `s * (if p then &0 else y) = (if ~p then s * y else &0)`] THEN
  ONCE_REWRITE_TAC[GSYM REAL_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[MESON[]
   `(if p then if q then x else &0 else &0) =
    (if p /\ q then x else &0)`] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  ASM_SIMP_TAC[REAL_ARITH
   `&0 < dd /\ dd <= pi
    ==> ((&0 <= x /\ x <= pi) /\ ~(abs x < dd) <=>
         dd <= x /\ x <= pi)`] THEN
  REWRITE_TAC[GSYM IN_REAL_INTERVAL; REAL_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[REAL_ARITH `(x - l) + (y - l) = (x + y) - &2 * l`] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
   `real_integral(real_interval[&0,dd]) f +
    real_integral(real_interval[dd,pi]) f =
    real_integral(real_interval[&0,pi]) f /\
    abs(real_integral(real_interval[&0,dd]) f) < e / &2
    ==> abs(real_integral(real_interval[dd,pi]) f - &0) < e / &2
        ==> abs(real_integral(real_interval[&0,pi]) f) < e`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN
    REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    MATCH_MP_TAC REAL_INTEGRABLE_COMBINE THEN EXISTS_TAC `dd:real` THEN
    ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE; REAL_LT_IMP_LE];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `abs x < e / &2 ==> abs y <= x ==> abs y < e / &2`)) THEN
    MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN
    ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0`; `d:real`] THEN
      ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      SIMP_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ARITH
        `&0 <= x ==> abs x = x`] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `x * y <= y <=> x * y <= &1 * y`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[REAL_ABS_POS; SIN_BOUND]]]);;
```
### Informal statement
For any real-valued function `f`, real number `t`, real number `l`, and real number `d`, if `f` is absolutely real integrable on the closed real interval from `-pi` to `pi`, and `f` is periodic with period `2 * pi` (i.e., for all `x`, `f(x + 2 * pi) = f(x)`), and `0 < d`, and the function `abs((f(t + x) + f(t - x)) - 2 * l) / x` is real integrable on the closed real interval from `0` to `d`, then the sequence whose `n`-th term is the sum from `0` to `n` of `fourier_coefficient f k * trigonometric_set k t` converges sequentially to `l`.

### Informal sketch
The theorem states Dini's test for the convergence of Fourier series. The proof proceeds as follows:
- Use `FOURIER_SUM_LIMIT_SINE_PART` to reduce to showing that the integral of a certain sine-related expression converges to zero.
- Simplify using the fact that `pi > 0`.
- Rewrite the sequential limit as a real limit.
- Introduce `e:real` representing the desired degree of approximation.
- Exploit the right-continuity of the indefinite integral.
- Simplify using facts about real intervals, the nullity of the real integral, and halving `e`.
- Introduce `k: real` satisfying properties related to continuity.
- Define `dd` as the minimum of `d`, `k / 2`, and `pi`.
- Show that `0 < dd`, `dd <= d`, `dd <= pi`, and `dd < k`.
- Apply `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET` to show periodicity.
- Rewrite using properties of absolute real integrability and reflection.
- Show that the function `((f(t + x) + f(t - x)) - 2 * l) / x` is absolutely real integrable on `real_interval[&0,dd]`. This involves proving measurability and integrability.
 - Prove that `((f(t + x) + f(t - x)) - 2 * l) / x` is absolutely real integrable on `real_interval[dd,pi]`. This utilizes the fact that the function is bounded and measurable.
- Prove that for all `n`, the functions `sin((&n + &1 / &2) * x) * ((f(t + x) + f(t - x)) - &2 * l) / x` are absolutely real integrable on `real_interval[&0,dd]` and `real_interval[dd,pi]`.
- Apply the Riemann-Lebesgue lemma (`RIEMANN_LEBESGUE_SIN_HALF`).
- Apply facts about real integrals, specifically their reflection and addition properties.
- Exploit `FOURIER_PRODUCTS_INTEGRABLE_STRONG` to prove integrability.
- Rewrite the real subtraction, using properties related to conditional expressions, the distributivity of real addition, and the division of reals.
- Simplify using the sequential limit's epsilon-delta definition.
- Conclude the proof by combining integrals using `REAL_INTEGRAL_COMBINE`, applying the mean value theorem, and leveraging the integrability of the functions.

### Mathematical insight
This theorem provides a sufficient condition for the pointwise convergence of the Fourier series of a function `f` at a point `t`. Dini's condition essentially requires that the function is integrable, periodic, and that a certain expression involving the absolute value of the difference quotient is also integrable near the point `t`. This is a classical result in Fourier analysis.

### Dependencies
- `FOURIER_SUM_LIMIT_SINE_PART`
- `PI_POS`
- `REAL_LE_REFL`
- `REALLIM_SEQUENTIALLY`
- `REAL_INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT`
- `real_continuous_on`
- `IN_REAL_INTERVAL`
- `REAL_LT_IMP_LE`
- `REAL_INTEGRAL_NULL`
- `REAL_HALF`
- `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`
- `REAL_ARITH`
- `absolutely_real_integrable_on`
- `REAL_INTEGRABLE_REFLECT`
- `real_sub`
- `REAL_NEG_NEG`
- `ABSOLUTELY_REAL_INTEGRABLE_REAL_MEASURABLE`
- `REAL_MEASURABLE_ON_DIV`
- `REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET`
- `REAL_CLOSED_REAL_INTERVAL`
- `REAL_CONTINUOUS_ON_CONST`
- `REAL_CONTINUOUS_ON_ID`
- `SING_GSPEC`
- `REAL_NEGLIGIBLE_SING`
- `REAL_CLOSED_UNIV`
- `INTEGRABLE_IMP_REAL_MEASURABLE`
- `REAL_INTEGRABLE_SUBINTERVAL`
- `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE`
- `REAL_INTEGRABLE_ADD`
- `REAL_INTEGRABLE_SUB`
- `REAL_INTEGRABLE_CONST`
- `SUBSET_REAL_INTERVAL`
- `TAUT`
- `REAL_INTEGRABLE_SPIKE`
- `REAL_NEGLIGIBLE_EMPTY`
- `REAL_ABS_DIV`
- `IN_DIFF`
- `real_abs`
- `REAL_MUL_SYM`
- `real_div`
- `ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT`
- `ETA_AX`
- `REAL_ARITH`
- `inv`
- `real_bounded`
- `FORALL_IN_IMAGE`
- `REAL_ABS_INV`
- `REAL_LE_INV2`
- `ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL`
- `SIN_BOUND`
- `REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET`,
- `REAL_CLOSED_UNIV`,
- `REAL_CLOSED_REAL_INTERVAL`
- `REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN`
- `REAL_CONTINUOUS_ATREAL_WITHINREAL`
- `REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL`
- `RIEMANN_LEBESGUE_SIN_HALF`
- `REAL_INTEGRAL_REFLECT_AND_ADD`
- `FOURIER_PRODUCTS_INTEGRABLE_STRONG`
- `ABSOLUTELY_REAL_INTEGRABLE_RESTRICT_UNIV`
- `MESON`
- `REAL_MUL_RZERO`
- `REAL_MUL_LZERO`
- `REAL_MEASURABLE_ON_CASES`
- `REAL_MEASURABLE_ON_0`
- `SET_RULE`
- `REAL_LEBESGUE_MEASURABLE_COMPL`
- `REAL_ARITH`
- `GSYM real_interval`
- `REAL_LEBESGUE_MEASURABLE_INTERVAL`
- `REAL_NOT_LT`
- `COND_CASES_TAC`
- `REAL_LE_INV_EQ`
- `REAL_ABS_NUM`
- `SIN_NEG`
- `REAL_MUL_RNEG`
- `REAL_NEG_NEG`
- `GSYM REAL_SUB_LDISTRIB`
- `REAL_INV_NEG`
- `GSYM REAL_ADD_RDISTRIB`
- `IN_REAL_INTERVAL`
- `MONO_EXISTS`
- `REAL_INTEGRAL_COMBINE`
- `REAL_INTEGRABLE_COMBINE`
- `REAL_INTEGRAL_ABS_BOUND_INTEGRAL`
- `REAL_LE_RMUL`

### Porting notes (optional)
- The extensive use of real analysis concepts and theorems requires a target system with solid support for real analysis, including integration, measurability, and limits.
- The tactic `MESON` is used for automated reasoning in HOL Light. This might need to be replaced with more explicit proof steps in other systems.
- The use of `ABBREV_TAC` to define abbreviations might need to be handled differently depending on the target system's capabilities.
- Handling of conditional expressions with `COND_CASES_TAC` will need to be considered.


---

## REAL_INTEGRAL_SIN_OVER_X_BOUND

### Name of formal statement
REAL_INTEGRAL_SIN_OVER_X_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_INTEGRAL_SIN_OVER_X_BOUND = prove
 (`!a b c.
       &0 <= a /\ &0 < c
       ==> (\x. sin(c * x) / x) real_integrable_on real_interval[a,b] /\
           abs(real_integral (real_interval[a,b]) (\x. sin(c * x) / x)) <= &4`,
  let lemma0 = prove
   (`!a b. (\x. sin x) real_integrable_on (real_interval[a,b]) /\
           abs(real_integral (real_interval[a,b]) (\x. sin x)) <= &2`,
    REPEAT GEN_TAC THEN ASM_CASES_TAC `a <= b` THENL
     [MP_TAC(ISPECL [`\x. --(cos x)`; `\x. sin x`; `a:real`; `b:real`]
        REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
         `abs x <= &1 /\ abs y <= &1 ==> abs(--y - --x) <= &2`) THEN
        REWRITE_TAC[COS_BOUND]];
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
      ASM_SIMP_TAC[REAL_INTEGRABLE_ON_NULL; REAL_INTEGRAL_NULL; REAL_LT_IMP_LE;
                   REAL_ABS_NUM; REAL_POS]]) in
  let lemma1 = prove
   (`!a b. &0 < a
           ==> (\x. sin x / x) real_integrable_on real_interval[a,b] /\
               abs(real_integral (real_interval[a,b])
                                 (\x. sin x / x)) <= &4 / a`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `a <= b` THENL
     [MP_TAC(ISPECL [`\x. sin x`; `\x:real. --(inv x)`; `a:real`; `b:real`]
              REAL_SECOND_MEAN_VALUE_THEOREM_FULL) THEN
      ASM_REWRITE_TAC[REAL_INTERVAL_EQ_EMPTY; REAL_NOT_LT; lemma0] THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_LE_NEG2; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN(X_CHOOSE_THEN `c:real`
         (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_INTEGRAL_NEG) THEN
        REWRITE_TAC[REAL_ARITH `--(--(inv y) * x):real = x / y`] THEN
        REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[REAL_NEG_ADD; REAL_MUL_LNEG; REAL_NEG_NEG] THEN
        MATCH_MP_TAC(REAL_ARITH
         `inv b <= inv a /\ abs x <= inv a * &2 /\ abs y <= inv b * &2
          ==> abs(x + y) <= &4 / a`) THEN
        ASM_SIMP_TAC[REAL_LE_INV2; REAL_ABS_MUL] THEN CONJ_TAC THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS; lemma0] THEN
        ASM_REWRITE_TAC[real_abs; REAL_LE_REFL; REAL_LE_INV_EQ] THEN
        ASM_REAL_ARITH_TAC];
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
      ASM_SIMP_TAC[REAL_INTEGRABLE_ON_NULL; REAL_INTEGRAL_NULL; REAL_LT_IMP_LE;
                   REAL_ABS_NUM; REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC]) in
  let lemma2 = prove
   (`!x. &0 <= x ==> sin(x) <= x`,
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `x <= &1` THENL
     [ALL_TAC; ASM_MESON_TAC[SIN_BOUNDS; REAL_LE_TOTAL; REAL_LE_TRANS]] THEN
    MP_TAC(ISPECL [`1`; `Cx x`] TAYLOR_CSIN) THEN
    CONV_TAC(TOP_DEPTH_CONV num_CONV) THEN
    REWRITE_TAC[VSUM_CLAUSES_NUMSEG; GSYM CX_SIN] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[GSYM CX_POW; GSYM CX_MUL; GSYM CX_DIV; GSYM CX_NEG;
                GSYM CX_ADD; GSYM CX_SUB] THEN
    REWRITE_TAC[COMPLEX_NORM_CX; IM_CX; REAL_ABS_0; REAL_EXP_0] THEN
    SIMP_TAC[REAL_POW_1; REAL_DIV_1; real_pow;
             REAL_MUL_LNEG; REAL_MUL_LID] THEN
    MATCH_MP_TAC(REAL_ARITH
     `e <= t ==> abs(sin x - (x + --t)) <= e ==> sin x <= x`) THEN
    ASM_REWRITE_TAC[real_abs; REAL_ARITH
     `x pow 5 / &24 <= x pow 3 / &6 <=>
      x pow 3 * x pow 2 <= x pow 3 * &2 pow 2`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE] THEN
    REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC) in
  let lemma3 = prove
   (`!x. &0 <= x /\ x <= &2 ==> abs(sin x / x) <= &1`,
    GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `x = &0` THENL
     [ASM_SIMP_TAC[real_div; REAL_MUL_RZERO; REAL_INV_0;
                   REAL_ABS_NUM; REAL_POS];
      ASM_SIMP_TAC[REAL_ABS_DIV; REAL_LE_LDIV_EQ; REAL_MUL_LID;
                   REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < abs x`] THEN
      MATCH_MP_TAC(REAL_ARITH `s <= x /\ &0 <= s ==> abs s <= abs x`) THEN
      ASM_SIMP_TAC[lemma2] THEN MATCH_MP_TAC SIN_POS_PI_LE THEN
      MP_TAC PI_APPROX_32 THEN ASM_REAL_ARITH_TAC]) in
  let lemma4 = prove
   (`!a b. &0 <= a /\ b <= &2
           ==> (\x. sin x / x) real_integrable_on real_interval[a,b] /\
               abs(real_integral (real_interval[a,b])
                                 (\x. sin x / x)) <= &2`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `a <= b` THENL
     [MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
        EXISTS_TAC `(\x. &1):real->real` THEN
        REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_MEASURABLE_ON_DIV THEN REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC INTEGRABLE_IMP_REAL_MEASURABLE THEN
            GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN REWRITE_TAC[lemma0];
            MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
            REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
            REWRITE_TAC[SING_GSPEC; REAL_NEGLIGIBLE_SING]];
          REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
          MATCH_MP_TAC lemma3 THEN ASM_REAL_ARITH_TAC];
        DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `real_integral (real_interval [a,b]) (\x. &1)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN
          ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
          REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
          MATCH_MP_TAC lemma3 THEN ASM_REAL_ARITH_TAC;
          ASM_SIMP_TAC[REAL_INTEGRAL_CONST] THEN ASM_REAL_ARITH_TAC]];
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
      ASM_SIMP_TAC[REAL_INTEGRABLE_ON_NULL; REAL_INTEGRAL_NULL; REAL_LT_IMP_LE;
                   REAL_ABS_NUM; REAL_POS]]) in
  let lemma5 = prove
   (`!a b. &0 <= a
           ==> (\x. sin x / x) real_integrable_on real_interval[a,b] /\
               abs(real_integral (real_interval[a,b]) (\x. sin x / x)) <= &4`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    ASM_CASES_TAC `b <= &2` THENL
     [ASM_MESON_TAC[lemma4; REAL_ARITH `x <= &2 ==> x <= &4`]; ALL_TAC] THEN
    ASM_CASES_TAC `&2 <= a` THENL
     [MP_TAC(SPECL [`a:real`; `b:real`] lemma1) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&2 <= a ==> &0 < a`] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
    MP_TAC(ISPECL [`\x. sin x / x`; `a:real`; `b:real`; `&2`]
          REAL_INTEGRABLE_COMBINE) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[lemma4; REAL_LE_REFL];
        ASM_MESON_TAC[lemma1; REAL_ARITH `&0 < &2`]];
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`\x. sin x / x`; `a:real`; `b:real`; `&2`]
          REAL_INTEGRAL_COMBINE) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(REAL_ARITH
     `abs(x) <= &2 /\ abs(y) <= &2 ==> abs(x + y) <= &4`) THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[lemma4; REAL_LE_REFL];
      GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `&2 = &4 / &2`] THEN
      ASM_MESON_TAC[lemma1; REAL_ARITH `&0 < &2`]]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `a <= b` THENL
   [MP_TAC(ISPECL [`c * a:real`; `c * b:real`] lemma5) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    GEN_REWRITE_TAC LAND_CONV [HAS_REAL_INTEGRAL_INTEGRAL] THEN
    DISCH_THEN(MP_TAC o SPEC `c:real` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
     HAS_REAL_INTEGRAL_STRETCH)) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_ADD_RID; REAL_SUB_RZERO] THEN
    DISCH_THEN(MP_TAC o SPEC `c:real` o MATCH_MP HAS_REAL_INTEGRAL_LMUL) THEN
    ASM_SIMP_TAC[IMAGE_STRETCH_REAL_INTERVAL; REAL_LE_INV_EQ; REAL_LT_IMP_LE;
      REAL_FIELD `&0 < c ==> inv c * c * a = a`; REAL_INV_MUL; real_div;
      REAL_FIELD `&0 < c ==> c * s * inv c * inv x = s * inv x`;
      REAL_FIELD `&0 < c ==> c * inv c * i = i /\ abs c = c`] THEN
    REWRITE_TAC[GSYM real_div; REAL_INTERVAL_EQ_EMPTY] THEN
    ASM_SIMP_TAC[GSYM REAL_NOT_LE; REAL_LE_LMUL_EQ] THEN
    REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_ON_NULL; REAL_INTEGRAL_NULL; REAL_LT_IMP_LE;
                 REAL_ABS_NUM; REAL_POS]]);;
```
### Informal statement
For all real numbers `a`, `b`, and `c`, if `0 <= a` and `0 < c`, then the function `\x. sin(c * x) / x` is real integrable on the real interval `[a,b]`, and the absolute value of the real integral of `\x. sin(c * x) / x` on the real interval `[a,b]` is less than or equal to `4`.

### Informal sketch
The proof proceeds by establishing several lemmas:
- `lemma0`: Proves that `sin x` is integrable on `[a,b]` and that the absolute value of the integral is bounded by `2`. This uses the `REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS` and the fact that the absolute value of `cos x` is bounded by `1`.
- `lemma1`: If `0 < a`, then `sin x / x` is integrable on `[a,b]` and the absolute value of the integral is bounded by `4 / a`. This is shown using the `REAL_SECOND_MEAN_VALUE_THEOREM_FULL`.
- `lemma2`: Establishes that if `0 <= x`, then `sin x <= x`. This is proven by cases. If `x <= 1` the result follows from already established result and if `1 < x` Taylor expansion for `sin x` is used.
- `lemma3`: If `0 <= x` and `x <= 2`, then `abs(sin x / x) <= 1`. This uses `lemma2`.
- `lemma4`: If `0 <= a` and `b <= 2`, then `sin x / x` is integrable on `[a,b]` and the absolute value of the integral is bounded by `2`. This uses `lemma3` and `REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE`.
- `lemma5`: If `0 <= a`, then `sin x / x` is integrable on `[a,b]` and the absolute value of the integral is bounded by `4`. This is proven by cases (`b <= 2`, `2 <= a` and neither). Combines `lemma1` and `lemma4` and uses `REAL_INTEGRABLE_COMBINE`.

Finally, the main theorem is proved by using `lemma5` with `REAL_INTEGRAL_STRETCH` to transform the integral of `sin(c*x) / x` to the integral of `sin(x) / x`. The case `a <= b` is handled, and the case when `a > b` is also handled using simplification rules.

### Mathematical insight
The theorem establishes the integrability of `sin(x)/x` on any closed interval `[a, b]` where `a` is non-negative, along with a uniform bound on the absolute value of the integral. The function `sin(x)/x` is of fundamental importance in mathematical analysis and signal processing, since it appears in Fourier transforms and sinc filters.

### Dependencies
- `REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS`
- `HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL`
- `COS_BOUND`
- `REAL_NOT_LE`
- `REAL_INTEGRABLE_ON_NULL`
- `REAL_INTEGRAL_NULL`
- `REAL_LT_IMP_LE`
- `REAL_ABS_NUM`
- `REAL_POS`
- `REAL_SECOND_MEAN_VALUE_THEOREM_FULL`
- `REAL_INTERVAL_EQ_EMPTY`
- `REAL_LE_NEG2`
- `IN_REAL_INTERVAL`
- `REAL_LE_INV2`
- `HAS_REAL_INTEGRAL_NEG`
- `REAL_ARITH`
- `REAL_DIV`
- `REAL_NEG_ADD`
- `REAL_MUL_LNEG`
- `REAL_NEG_NEG`
- `REAL_LE_MUL2`
- `REAL_ABS_MUL`
- `real_abs`
- `REAL_LE_REFL`
- `REAL_LE_INV_EQ`
- `REAL_LE_DIV`
- `SIN_BOUNDS`
- `REAL_LE_TOTAL`
- `REAL_LE_TRANS`
- `TAYLOR_CSIN`
- `VSUM_CLAUSES_NUMSEG`
- `CX_SIN`
- `CX_POW`
- `CX_MUL`
- `CX_DIV`
- `CX_NEG`
- `CX_ADD`
- `CX_SUB`
- `COMPLEX_NORM_CX`
- `IM_CX`
- `REAL_ABS_0`
- `REAL_EXP_0`
- `REAL_POW_1`
- `REAL_DIV_1`
- `real_pow`
- `REAL_MUL_LID`
- `REAL_LE_LMUL`
- `REAL_POW_LE`
- `REAL_LE_SQUARE_ABS`
- `real_div`
- `REAL_MUL_RZERO`
- `REAL_INV_0`
- `REAL_LE_LDIV_EQ`
- `SIN_POS_PI_LE`
- `PI_APPROX_32`
- `REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE`
- `REAL_INTEGRABLE_CONST`
- `REAL_MEASURABLE_ON_DIV`
- `INTEGRABLE_IMP_REAL_MEASURABLE`
- `GSYM ETA_AX`
- `CONTINUOUS_IMP_REAL_MEASURABLE_ON`
- `REAL_CONTINUOUS_ON_ID`
- `SING_GSPEC`
- `REAL_NEGLIGIBLE_SING`
- `REAL_INTEGRAL_ABS_BOUND_INTEGRAL`
- `REAL_INTEGRAL_COMBINE`
- `MONO_AND`
- `IMP_CONJ_ALT`
- `HAS_REAL_INTEGRAL_STRETCH`
- `REAL_LT_IMP_NZ`
- `REAL_ADD_RID`
- `REAL_SUB_RZERO`
- `REAL_INV_MUL`
- `IMAGE_STRETCH_REAL_INTERVAL`
- `REAL_FIELD`

### Porting notes (optional)
- The proof relies heavily on real analysis theorems. Ensure that the target proof assistant has similar theorems available.
- The use of `REAL_INTEGRAL_STRETCH` and other integral manipulation theorems may require some effort.
- The proof relies extensively on `REAL_ARITH` and `ASM_REAL_ARITH_TAC` for real number reasoning. Ensure good support for real arithmetic in the target system.


---

## FOURIER_JORDAN_BOUNDED_VARIATION

### Name of formal statement
FOURIER_JORDAN_BOUNDED_VARIATION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_JORDAN_BOUNDED_VARIATION = prove
 (`!f x d.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f(x + &2 * pi) = f x) /\
        &0 < d /\
        f has_bounded_real_variation_on real_interval[x - d,x + d]
        ==> ((\n. sum (0..n)
                      (\k. fourier_coefficient f k * trigonometric_set k x))
             ---> ((reallim (atreal x within {l | l <= x}) f +
                    reallim (atreal x within {r | r >= x}) f) / &2))
            sequentially`,
  let lemma = prove
   (`!f l d. &0 < d
             ==> ((f ---> l) (atreal (&0) within real_interval[&0,d]) <=>
                  (f ---> l) (atreal (&0) within {x | &0 <= x}))`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REALLIM_TRANSFORM_WITHINREAL_SET THEN
    REWRITE_TAC[EVENTUALLY_ATREAL] THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC) in
  MAP_EVERY X_GEN_TAC [`f:real->real`; `t:real`; `d0:real`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `s = (reallim (atreal t within {l | l <= t}) f +
                   reallim (atreal t within {r | r >= t}) f) / &2` THEN
  MP_TAC(SPECL [`f:real->real`; `t:real`; `s:real`; `min d0 pi`]
        FOURIER_SUM_LIMIT_SINE_PART) THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; PI_POS; REAL_ARITH `min d0 pi <= pi`] THEN
  DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `h = \u. ((f:real->real)(t + u) + f(t - u)) - &2 * s` THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
  SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN ABBREV_TAC `d = min d0 pi` THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `h has_bounded_real_variation_on real_interval[&0,d]`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [HAS_BOUNDED_REAL_VARIATION_DARBOUX]) THEN
    EXPAND_TAC "h" THEN REWRITE_TAC[HAS_BOUNDED_REAL_VARIATION_DARBOUX] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; IN_REAL_INTERVAL] THEN
    MAP_EVERY X_GEN_TAC [`f1:real->real`; `f2:real->real`] THEN STRIP_TAC THEN
    EXISTS_TAC `\x. ((f1:real->real)(t + x) - f2(t - x)) - s` THEN
    EXISTS_TAC `\x. ((f2:real->real)(t + x) - f1(t - x)) + s` THEN
    ASM_REWRITE_TAC[REAL_ARITH `x - s <= y - s <=> x <= y`; REAL_LE_RADD] THEN
    REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH
     `a <= a' /\ b' <= b ==> a - b <= a' - b'`) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(h ---> &0) (atreal(&0) within {x | &0 <= x})`
  ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[REAL_ARITH
     `(f' + f) - &2 * (l + l') / &2 = (f - l) + (f' - l')`] THEN
    MATCH_MP_TAC REALLIM_NULL_ADD THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `?l. (f ---> l) (atreal t within {l | l <= t})` MP_TAC
      THENL
       [MP_TAC(ISPECL [`f:real->real`; `t - d0:real`; `t + d0:real`; `t:real`]
         HAS_BOUNDED_REAL_VARIATION_LEFT_LIMIT) THEN
        ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real` THEN
        REWRITE_TAC[REALLIM_WITHINREAL] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
        ASM_CASES_TAC `&0 < e` THEN
        ASM_REWRITE_TAC[IN_REAL_INTERVAL; IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `d1:real` (fun th ->
          EXISTS_TAC `min d0 d1` THEN
          CONJUNCTS_THEN2 ASSUME_TAC MP_TAC th)) THEN
        ASM_REWRITE_TAC[REAL_LT_MIN] THEN
        MATCH_MP_TAC MONO_FORALL THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN(MP_TAC o SELECT_RULE) THEN
        REWRITE_TAC[GSYM reallim] THEN
        REWRITE_TAC[REALLIM_WITHINREAL] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
        ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d1:real` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
         X_GEN_TAC `x:real` THEN MP_TAC(SPEC `t - x:real` th)) THEN
        MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
        REAL_ARITH_TAC];
      SUBGOAL_THEN
       `?l. (f ---> l) (atreal t within {r | r >= t})` MP_TAC
      THENL
       [MP_TAC(ISPECL [`f:real->real`; `t - d0:real`; `t + d0:real`; `t:real`]
         HAS_BOUNDED_REAL_VARIATION_RIGHT_LIMIT) THEN
        ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real` THEN
        REWRITE_TAC[REALLIM_WITHINREAL] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
        ASM_CASES_TAC `&0 < e` THEN
        ASM_REWRITE_TAC[IN_REAL_INTERVAL; IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `d1:real` (fun th ->
          EXISTS_TAC `min d0 d1` THEN
          CONJUNCTS_THEN2 ASSUME_TAC MP_TAC th)) THEN
        ASM_REWRITE_TAC[REAL_LT_MIN] THEN
        MATCH_MP_TAC MONO_FORALL THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN(MP_TAC o SELECT_RULE) THEN
        REWRITE_TAC[GSYM reallim] THEN
        REWRITE_TAC[REALLIM_WITHINREAL] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
        ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d1:real` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
         X_GEN_TAC `x:real` THEN MP_TAC(SPEC `t + x:real` th)) THEN
        MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?k. &0 < k /\ k < d /\
        !n. (\x. sin ((&n + &1 / &2) * x) * h x / x)
            real_integrable_on real_interval[&0,k] /\
            abs(real_integral (real_interval[&0,k])
                              (\x. sin ((&n + &1 / &2) * x) * h x / x))
              <= e / &2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `?h1 h2.
         (!x y. x IN real_interval[&0,d] /\ y IN real_interval[&0,d] /\ x <= y
                ==> h1 x <= h1 y) /\
         (!x y. x IN real_interval[&0,d] /\ y IN real_interval[&0,d] /\ x <= y
                ==> h2 x <= h2 y) /\
         (h1 ---> &0) (atreal (&0) within {x | &0 <= x}) /\
         (h2 ---> &0) (atreal (&0) within {x | &0 <= x}) /\
         (!x. h x = h1 x - h2 x)`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`h:real->real`; `&0`; `d:real`]
          HAS_BOUNDED_REAL_VARIATION_DARBOUX) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`h1:real->real`; `h2:real->real`] THEN
      STRIP_TAC THEN
      MP_TAC(ISPECL [`h1:real->real`; `&0`; `d:real`; `&0`]
           INCREASING_RIGHT_LIMIT) THEN
      ASM_REWRITE_TAC[ENDS_IN_REAL_INTERVAL; REAL_INTERVAL_EQ_EMPTY] THEN
      ASM_SIMP_TAC[REAL_NOT_LT; REAL_LT_IMP_LE] THEN
      DISCH_THEN(X_CHOOSE_TAC `l:real`) THEN
      MP_TAC(ISPECL [`h2:real->real`; `&0`; `d:real`; `&0`]
           INCREASING_RIGHT_LIMIT) THEN
      ASM_REWRITE_TAC[ENDS_IN_REAL_INTERVAL; REAL_INTERVAL_EQ_EMPTY] THEN
      ASM_SIMP_TAC[REAL_NOT_LT; REAL_LT_IMP_LE] THEN
      DISCH_THEN(X_CHOOSE_TAC `l':real`) THEN
      SUBGOAL_THEN `l':real = l` SUBST_ALL_TAC THENL
       [CONV_TAC SYM_CONV THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
        MATCH_MP_TAC(ISPEC `atreal (&0) within {x | &0 <= x}`
          REALLIM_UNIQUE) THEN
        EXISTS_TAC `h:real->real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [W(MP_TAC o PART_MATCH (lhs o rand) TRIVIAL_LIMIT_WITHIN_REALINTERVAL o
            rand o snd) THEN
          REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN
          ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
          REWRITE_TAC[EXTENSION; NOT_FORALL_THM; IN_ELIM_THM; IN_SING] THEN
          EXISTS_TAC `&1` THEN REAL_ARITH_TAC;
          GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REALLIM_SUB THEN
          MAP_EVERY UNDISCH_TAC
           [`(h1 ---> l) (atreal(&0) within real_interval[&0,d])`;
            `(h2 ---> l') (atreal(&0) within real_interval[&0,d])`] THEN
          ASM_SIMP_TAC[lemma]];
        EXISTS_TAC `\x. (h1:real->real)(x) - l` THEN
        EXISTS_TAC `\x. (h2:real->real)(x) - l` THEN
        ASM_REWRITE_TAC[REAL_ARITH `x - l <= y - l <=> x <= y`] THEN
        ASM_REWRITE_TAC[GSYM REALLIM_NULL] THEN
        MAP_EVERY UNDISCH_TAC
         [`(h1 ---> l) (atreal(&0) within real_interval[&0,d])`;
          `(h2 ---> l) (atreal(&0) within real_interval[&0,d])`] THEN
        ASM_SIMP_TAC[lemma] THEN REPEAT DISCH_TAC THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?k. &0 < k /\ k < d /\ abs(h1 k) < e / &16 /\ abs(h2 k) < e / &16`
    MP_TAC THENL
     [UNDISCH_TAC `(h2 ---> &0) (atreal (&0) within {x | &0 <= x})` THEN
      UNDISCH_TAC `(h1 ---> &0) (atreal (&0) within {x | &0 <= x})` THEN
      REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
      DISCH_THEN(MP_TAC o SPEC `e / &16`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC;
        DISCH_THEN(X_CHOOSE_THEN `k1:real` STRIP_ASSUME_TAC)] THEN
      DISCH_THEN(MP_TAC o SPEC `e / &16`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC;
        DISCH_THEN(X_CHOOSE_THEN `k2:real` STRIP_ASSUME_TAC)] THEN
      EXISTS_TAC `min d (min k1 k2) / &2` THEN
      REPLICATE_TAC 2 (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`\x. sin((&n + &1 / &2) * x) / x`; `h1:real->real`;
                     `&0`; `k:real`; `&0`; `(h1:real->real) k`]
      REAL_SECOND_MEAN_VALUE_THEOREM_GEN_FULL) THEN
    ASM_SIMP_TAC[REAL_INTERVAL_EQ_EMPTY; REAL_NOT_LT; REAL_LT_IMP_LE] THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_SIN_OVER_X_BOUND; REAL_LE_REFL; REAL_ADD_LID;
                 REAL_ARITH `&0 < &n + &1 / &2`; REAL_MUL_LZERO] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
        REPEAT STRIP_TAC THENL
         [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
          UNDISCH_TAC `(h1 ---> &0) (atreal (&0) within {x | &0 <= x})` THEN
          REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
          DISCH_THEN(MP_TAC o SPEC `--((h1:real->real) x)`) THEN
          REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `dd:real` MP_TAC) THEN
          DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
           (MP_TAC o SPEC `min d (min x dd) / &2`)) THEN
          REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
           `h < &0 ==> h' <= h ==> ~(abs h' < --h)`));
          ALL_TAC] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
       [REAL_ARITH `h * s / x:real = s * h / x`] THEN
      REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
      DISCH_THEN(X_CHOOSE_THEN `c1:real` STRIP_ASSUME_TAC)] THEN
    MP_TAC(ISPECL [`\x. sin((&n + &1 / &2) * x) / x`; `h2:real->real`;
                     `&0`; `k:real`; `&0`; `(h2:real->real) k`]
      REAL_SECOND_MEAN_VALUE_THEOREM_GEN_FULL) THEN
    ASM_SIMP_TAC[REAL_INTERVAL_EQ_EMPTY; REAL_NOT_LT; REAL_LT_IMP_LE] THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_SIN_OVER_X_BOUND; REAL_LE_REFL; REAL_ADD_LID;
                 REAL_ARITH `&0 < &n + &1 / &2`; REAL_MUL_LZERO] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
        REPEAT STRIP_TAC THENL
         [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
          UNDISCH_TAC `(h2 ---> &0) (atreal (&0) within {x | &0 <= x})` THEN
          REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
          DISCH_THEN(MP_TAC o SPEC `--((h2:real->real) x)`) THEN
          REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `dd:real` MP_TAC) THEN
          DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
           (MP_TAC o SPEC `min d (min x dd) / &2`)) THEN
          REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
           `h < &0 ==> h' <= h ==> ~(abs h' < --h)`));
          ALL_TAC] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
       [REAL_ARITH `h * s / x:real = s * h / x`] THEN
      REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
      DISCH_THEN(X_CHOOSE_THEN `c2:real` STRIP_ASSUME_TAC)] THEN
    REWRITE_TAC[REAL_ARITH
     `s * (h - h') / x:real = s * h / x - s * h' / x`] THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_SUB; REAL_INTEGRAL_SUB] THEN
    MATCH_MP_TAC(REAL_ARITH
     `abs(x) <= e / &16 * &4 /\ abs(y) <= e / &16 * &4
      ==> abs(x - y) <= e / &2`) THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_SIN_OVER_X_BOUND; REAL_LT_IMP_LE;
                 REAL_ARITH `&0 < &n + &1 / &2`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `--pi`; `pi`; `t:real`]
      ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET) THEN
  ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_ADD_SYM] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  GEN_REWRITE_TAC LAND_CONV [absolutely_real_integrable_on] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [GSYM REAL_INTEGRABLE_REFLECT] THEN
  REWRITE_TAC[GSYM absolutely_real_integrable_on; GSYM real_sub] THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\x. h x / x) absolutely_real_integrable_on real_interval[k,d]`
  ASSUME_TAC THENL
   [REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
      REWRITE_TAC[REAL_CLOSED_REAL_INTERVAL] THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_INV_WITHINREAL THEN
      REWRITE_TAC[REAL_CONTINUOUS_WITHIN_ID] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
      EXISTS_TAC `inv k:real` THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[REAL_ABS_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REAL_ARITH_TAC;
      EXPAND_TAC "h" THEN MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_SUB THEN
      REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
      MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL THEN
      EXISTS_TAC `real_interval[--pi,pi]` THEN
      ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_ADD] THEN
      REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\x. sin((&n + &1 / &2) * x) * h x / x) absolutely_real_integrable_on
        real_interval[k,d]`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
      REWRITE_TAC[REAL_CLOSED_UNIV; REAL_CLOSED_REAL_INTERVAL] THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
      REAL_DIFFERENTIABLE_TAC;
      REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN
      EXISTS_TAC `&1` THEN REWRITE_TAC[SIN_BOUND]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `\x. if k <= x /\ x <= d then h x / x else &0`
        RIEMANN_LEBESGUE_SIN_HALF) THEN
  REWRITE_TAC[absolutely_real_integrable_on] THEN
  REWRITE_TAC[MESON[REAL_ABS_NUM]
   `abs(if p then x else &0) = if p then abs x else &0`] THEN
  ONCE_REWRITE_TAC[GSYM REAL_INTEGRAL_RESTRICT_UNIV; GSYM
                   REAL_INTEGRABLE_RESTRICT_UNIV] THEN
  REWRITE_TAC[MESON[REAL_MUL_RZERO]
   `(if P then s * (if Q then a else &0) else &0) =
    (if P /\ Q then s * a else &0)`] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  REWRITE_TAC[MESON[] `(if P then if Q then x else &0 else &0) =
                       (if P /\ Q then x else &0)`] THEN
  SUBGOAL_THEN `!x. (--pi <= x /\ x <= pi) /\ k <= x /\ x <= d <=>
                    k <= x /\ x <= d`
   (fun th -> REWRITE_TAC[th])
  THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM IN_REAL_INTERVAL; REAL_INTEGRAL_RESTRICT_UNIV;
              REAL_INTEGRABLE_RESTRICT_UNIV] THEN
  ASM_REWRITE_TAC[GSYM absolutely_real_integrable_on] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC o SPEC `n:num`) THEN
  MATCH_MP_TAC(REAL_ARITH
   `x + y = z ==> abs(x) <= e / &2 ==> abs(y) < e / &2 ==> abs(z) < e`) THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN
  REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  MATCH_MP_TAC REAL_INTEGRABLE_COMBINE THEN EXISTS_TAC `k:real` THEN
  ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
  ASM_REAL_ARITH_TAC);;
```
### Informal statement
For all real-valued functions `f`, real numbers `x` and `d`, if `f` is absolutely real integrable on the real interval from `-pi` to `pi`, and `f` is periodic with period `2 * pi` (i.e., `f(x + 2 * pi) = f(x)` for all `x`), and `0 < d`, and `f` has bounded real variation on the real interval from `x - d` to `x + d`, then the sequence of partial sums of the Fourier series of `f` at `x` (i.e., `sum (0..n) (fourier_coefficient f k * trigonometric_set k x)`) converges to the average of the left and right limits of `f` at `x` (i.e., `(reallim (atreal x within {l | l <= x}) f + reallim (atreal x within {r | r >= x}) f) / 2`) sequentially.

### Informal sketch
The proof establishes that under given conditions, the Fourier series of a function `f` converges to the average of the left and right limits at a point `x`.
- First a lemma is proved showing the equivalence of limits at 0 within an interval [0, d] and limits at 0 within the set {x | 0 <= x}.
- The main proof involves setting up the assumptions and defining `s` as the average of the left and right limits of `f` at `t` (corresponding to the `x` in the main theorem).
- Applying `FOURIER_SUM_LIMIT_SINE_PART` to relate the partial sum to a `sine_part` involving an integral.
- Simplifying the expression by defining `h(u) = f(t + u) + f(t - u) - 2s` to isolate the relevant parts of the function.
- Showing that `0 < d` where `d = min d0 pi`, trivially.
- Proving that `h` has bounded real variation on the interval `[0, d]` using `HAS_BOUNDED_REAL_VARIATION_DARBOUX` and properties of bounded variation.
- Proving that `h` tends to 0 as x approach 0 from the right using the definition of `h` and the limits of f from the left and right at t.
  - This uses that `HAS_BOUNDED_REAL_VARIATION_LEFT_LIMIT` and `HAS_BOUNDED_REAL_VARIATION_RIGHT_LIMIT` to assert the existence of left and right limits, and uses rewrite rules involving `reallim` and `atreal`.
- Showing that the integral involving `sin` and `h` becomes small. By rewriting `reallim` to `sequentially`, and splitting the integral into one on `[0, k]` which must be made small, and one of `[k, d]` which can be made small by the Riemann Lebesgue Lemma,
- Applying `HAS_BOUNDED_REAL_VARIATION_DARBOUX` to split `h` into monotone increasing component functions `h1` and `h2`.
- Applying `REAL_SECOND_MEAN_VALUE_THEOREM_GEN_FULL` to the integral of `sin((n + 1/2)x) h1(x) / x` and similarly for `h2`.
- Finally, use `RIEMANN_LEBESGUE_SIN_HALF` and the integrability and variation results to obtain the convergence condition.

### Mathematical insight
This theorem provides a sufficient condition for the pointwise convergence of Fourier series. It states that if a function is integrable, periodic, and has bounded variation in a neighborhood of a point, then its Fourier series converges to the average of the left and right limits at that point. This is a fundamental result in Fourier analysis and signal processing. Bounded variation ensures that the function is reasonably well-behaved (e.g., has a finite number of discontinuities and oscillations), which is crucial for the convergence of the Fourier series. The Jordan test is stronger then the Dini test for pointwise convergence.

### Dependencies
- `FOURIER_SUM_LIMIT_SINE_PART`
- `HAS_BOUNDED_REAL_VARIATION_DARBOUX`
- `HAS_BOUNDED_REAL_VARIATION_LEFT_LIMIT`
- `HAS_BOUNDED_REAL_VARIATION_RIGHT_LIMIT`
- `INCREASING_RIGHT_LIMIT`
- `REALLIM_UNIQUE`
- `TRIVIAL_LIMIT_WITHIN_REALINTERVAL`
- `REALLIM_SUB`
- `RIEMANN_LEBESGUE_SIN_HALF`
- `ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT`
- `REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET`
- `REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN`
- `REAL_CONTINUOUS_INV_WITHINREAL`
- `REAL_CONTINUOUS_WITHIN_ID`
- `REAL_LE_INV2`
- `ABSOLUTELY_REAL_INTEGRABLE_SUB`
- `ABSOLUTELY_REAL_INTEGRABLE_CONST`
- `ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL`
- `ABSOLUTELY_REAL_INTEGRABLE_ADD`
- `REAL_SECOND_MEAN_VALUE_THEOREM_GEN_FULL`
- `REAL_INTEGRAL_SIN_OVER_X_BOUND`
- `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`

### Porting notes (optional)
- The tactic `MESON` is used more compared to other provers, which may require replacement with equivalent calls in other provers.
- The proof makes heavy use of real analysis. Ensure that the target prover has comparable real analysis libraries.
- The proof uses the `REAL_SECOND_MEAN_VALUE_THEOREM_GEN_FULL`, `RIEMANN_LEBESGUE_SIN_HALF` theorems, which might need to be ported or proved in other proof assistants if they are not readily available.


---

## FOURIER_JORDAN_BOUNDED_VARIATION_SIMPLE

### Name of formal statement
FOURIER_JORDAN_BOUNDED_VARIATION_SIMPLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_JORDAN_BOUNDED_VARIATION_SIMPLE = prove
 (`!f x. f has_bounded_real_variation_on real_interval[--pi,pi] /\
         (!x. f(x + &2 * pi) = f x)
         ==> ((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k x))
              ---> ((reallim (atreal x within {l | l <= x}) f +
                     reallim (atreal x within {r | r >= x}) f) / &2))
             sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FOURIER_JORDAN_BOUNDED_VARIATION THEN
  EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [HAS_BOUNDED_REAL_VARIATION_DARBOUX]) THEN
    STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_SUB THEN
    CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_INCREASING THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN
     `!n. integer n
          ==> f has_bounded_real_variation_on
              real_interval [(&2 * n - &1) * pi,(&2 * n + &1) * pi]`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `&2 * --n * pi` o
       MATCH_MP HAS_BOUNDED_REAL_VARIATION_TRANSLATION) THEN
      REWRITE_TAC[INTEGER_NEG; GSYM REAL_INTERVAL_TRANSLATION] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [REAL_PERIODIC_INTEGER_MULTIPLE]) THEN
      DISCH_THEN(MP_TAC o GEN `x:real` o SPECL [`x:real`; `--n:real`]) THEN
      ASM_REWRITE_TAC[REAL_ARITH `x + n * &2 * pi = &2 * n * pi + x`] THEN
      ASM_REWRITE_TAC[INTEGER_NEG] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[CONS_11; PAIR_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!n. f has_bounded_real_variation_on
          real_interval[--pi,&(2 * n + 1) * pi]`
    ASSUME_TAC THENL
     [INDUCT_TAC THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; REAL_MUL_LID] THEN
      MP_TAC(ISPECL [`f:real->real`; `--pi`; `&((2 + 2 * n) + 1) * pi`;
                     `&(2 * n + 1) * pi`]
        HAS_BOUNDED_REAL_VARIATION_ON_COMBINE) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_ARITH `--pi = --(&1) * pi`] THEN
        SIMP_TAC[REAL_LE_RMUL_EQ; PI_POS; REAL_OF_NUM_LE] THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ARITH_TAC];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
        REWRITE_TAC[REAL_ARITH
         `(&2 * n + &1) * pi = (&2 * (n + &1) - &1) * pi`] THEN
        REWRITE_TAC[REAL_ARITH
         `((&2 + &2 * n) + &1) * pi = (&2 * (n + &1) + &1) * pi`] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN SIMP_TAC[INTEGER_CLOSED]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!m n. f has_bounded_real_variation_on
            real_interval[--(&(2 * m + 1)) * pi,&(2 * n + 1) * pi]`
    ASSUME_TAC THENL
     [INDUCT_TAC THEN
      ASM_SIMP_TAC[MULT_CLAUSES; ADD_CLAUSES; REAL_MUL_LID; REAL_MUL_LNEG] THEN
      X_GEN_TAC `n:num` THEN
      MP_TAC(ISPECL [`f:real->real`; `--(&((2 + 2 * m) + 1) * pi)`;
                     `&(2 * n + 1) * pi`; `--(&(2 * m + 1) * pi)`]
        HAS_BOUNDED_REAL_VARIATION_ON_COMBINE) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN
        SIMP_TAC[REAL_LE_RMUL_EQ; PI_POS; REAL_OF_NUM_LE] THEN
        REWRITE_TAC[REAL_LE_NEG2; REAL_ARITH `--a <= b <=> &0 <= a + b`] THEN
        REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ARITH_TAC;
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
        REWRITE_TAC[REAL_ARITH
          `--(&2 * m + &1) = &2 * --(m + &1) + &1`] THEN
        REWRITE_TAC[REAL_ARITH
          `--((&2 + &2 * m) + &1) = &2 * --(m + &1) - &1`] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN SIMP_TAC[INTEGER_CLOSED]];
      ALL_TAC] THEN
    MP_TAC(ISPEC `&2 * pi` REAL_ARCH) THEN
    ANTS_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `abs x + &3`) THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    MATCH_MP_TAC HAS_BOUNDED_REAL_VARIATION_ON_SUBSET THEN
    EXISTS_TAC `real_interval[-- &(2 * N + 1) * pi,&(2 * N + 1) * pi]` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC]);;
```
### Informal statement
For any function `f` and any real number `x`, if `f` has bounded real variation on the real interval from `-pi` to `pi`, and `f` is periodic with period `2 * pi` (i.e., for all `x`, `f(x + 2 * pi) = f(x)`), then the sequence of partial sums of the Fourier series of `f` evaluated at `x` converges to the average of the left and right limits of `f` at `x`. Specifically the sequence indexed by `n` defined by the sum from `0` to `n` of `fourier_coefficient f k * trigonometric_set k x` converges sequentially to `(reallim (atreal x within {l | l <= x}) f + reallim (atreal x within {r | r >= x}) f) / 2`.

### Informal sketch
The proof proceeds as follows:

- Strip the goal and apply the theorem `FOURIER_JORDAN_BOUNDED_VARIATION`. 
- Existentially instantiate the theorem `FOURIER_JORDAN_BOUNDED_VARIATION` with `1` to obtain a bound on the rate of convergence.
- Simplify using `REAL_LT_01`.
- Split the conjunction.
- Prove the absolute integrability of `f` using `HAS_BOUNDED_REAL_VARIATION_DARBOUX` and `ABSOLUTELY_REAL_INTEGRABLE_SUB`, combined with `ABSOLUTELY_REAL_INTEGRABLE_INCREASING`.
- Show that `f` has bounded real variation on `[2 * n * pi - pi, 2 * n * pi + pi]` by using `HAS_BOUNDED_REAL_VARIATION_TRANSLATION` and `REAL_PERIODIC_INTEGER_MULTIPLE`. This involves induction.
- Prove that `f` has bounded real variation on the interval `[-pi, (2*n+1)*pi]` by induction, making use of `HAS_BOUNDED_REAL_VARIATION_ON_COMBINE`. This relies on combining intervals.
- Prove that `f` has bounded real variation on the interval `[-(2*m+1)*pi, (2*n+1)*pi]` by induction. Again, interval combination via `HAS_BOUNDED_REAL_VARIATION_ON_COMBINE` is used.
- Utilize `REAL_ARCH` to show that, given the conditions, there exists a large enough interval `[-(2*N+1)*pi, (2*N+1)*pi]` on which `f` has bounded variation, and that contains the point `x`, allowing application of `HAS_BOUNDED_REAL_VARIATION_ON_SUBSET`.

### Mathematical insight
This theorem establishes the convergence of the Fourier series for a periodic function with bounded variation to the average of the function's left and right limits at a given point. This is a fundamental result in Fourier analysis, connecting the smoothness of a function (in terms of bounded variation) to the convergence of its Fourier series. It's a simplified version of Jordan's test for convergence of Fourier Series.

### Dependencies
- `FOURIER_JORDAN_BOUNDED_VARIATION`
- `HAS_BOUNDED_REAL_VARIATION_DARBOUX`
- `ABSOLUTELY_REAL_INTEGRABLE_SUB`
- `ABSOLUTELY_REAL_INTEGRABLE_INCREASING`
- `HAS_BOUNDED_REAL_VARIATION_TRANSLATION`
- `REAL_PERIODIC_INTEGER_MULTIPLE`
- `HAS_BOUNDED_REAL_VARIATION_ON_COMBINE`
- `REAL_ARCH`
- `HAS_BOUNDED_REAL_VARIATION_ON_SUBSET`

### Porting notes (optional)
- Bounded variation is usually defined and handled similarly across different proof assistants. The key is ensuring that the definitions of `real_interval`, `fourier_coefficient`, `trigonometric_set`, `reallim` etc. are consistent.
- The tactic `ASM_REAL_ARITH_TAC` is specific to HOL Light and may need to be replaced with a comparable tactic or series of tactics to perform real arithmetic reasoning in other systems.


---

## fejer_kernel

### Name of formal statement
fejer_kernel

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let fejer_kernel = new_definition
  `fejer_kernel n x = if n = 0 then &0
                      else sum(0..n-1) (\r. dirichlet_kernel r x) / &n`;;
```

### Informal statement
The Fejér kernel of degree `n` at point `x`, denoted `fejer_kernel n x`, is defined as follows: if `n` equals 0, then `fejer_kernel n x` is 0. Otherwise, `fejer_kernel n x` is the sum of the Dirichlet kernels of degree `r` at `x` for `r` ranging from 0 to `n-1`, divided by `n`.

### Informal sketch
The definition of `fejer_kernel` introduces a new function that represents the Fejér kernel, which is the arithmetic mean of the first `n` Dirichlet kernels.

*   The definition is conditional:
    *   If `n` is 0, the kernel is defined to be 0.
    *   Otherwise, it's defined as the average of the first `n` Dirichlet kernels `dirichlet_kernel r x`.
*   The summation `sum(0..n-1) (\r. dirichlet_kernel r x)` computes the sum of `dirichlet_kernel r x`, where `r` ranges from 0 to `n-1`.
*   The result of the summation is then divided by `n`.

### Mathematical insight
The Fejér kernel is used in the Cesàro summation of Fourier series. It provides a smoother way to approximate a function compared to using the Dirichlet kernel directly, which can exhibit oscillatory behavior and poor convergence properties, by averaging the Dirichlet kernels. The Fejér kernel possesses better convergence properties, particularly in the context of continuous functions.

### Dependencies
*   `dirichlet_kernel`
*   `sum`


---

## FEJER_KERNEL

### Name of formal statement
FEJER_KERNEL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FEJER_KERNEL = prove
 (`fejer_kernel n x =
        if n = 0 then &0
        else if x = &0 then &n / &2
        else sin(&n / &2 * x) pow 2 / (&2 * &n * sin(x / &2) pow 2)`,
  REWRITE_TAC[fejer_kernel; dirichlet_kernel] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[SUM_0] THEN
  ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[SUM_ADD_NUMSEG; SUM_CONST_NUMSEG;
                REWRITE_RULE[ETA_AX] SUM_NUMBERS] THEN
    ASM_SIMP_TAC[SUB_ADD; GSYM REAL_OF_NUM_SUB; LE_1; SUB_0] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
     [GSYM REAL_OF_NUM_EQ]) THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_CASES_TAC `sin(x / &2) = &0` THENL
   [ASM_REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ; REAL_MUL_RZERO; real_div;
                    REAL_INV_0; SUM_0; REAL_MUL_LZERO];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_FIELD
   `~(n = &0) /\ ~(s = &0) /\ &2 * s pow 2 * l = r
    ==> l / n = r / (&2 * n * s pow 2)`) THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_EQ; GSYM SUM_LMUL] THEN
  ASM_SIMP_TAC[REAL_FIELD
   `~(s = &0) ==> &2 * s pow 2 * a / (&2 * s) = s * a`] THEN
  REWRITE_TAC[REAL_MUL_SIN_SIN] THEN
  REWRITE_TAC[REAL_ARITH `x / &2 - (&n + &1 / &2) * x = --(&n * x)`;
              REAL_ARITH `x / &2 + (&n + &1 / &2) * x = (&n + &1) * x`] THEN
  REWRITE_TAC[real_div; SUM_RMUL; COS_NEG; REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[SUM_DIFFS; LE_0; REAL_MUL_LZERO] THEN
  ASM_SIMP_TAC[SUB_ADD; LE_1; REAL_SUB_COS] THEN
  REWRITE_TAC[REAL_ADD_LID; REAL_SUB_RZERO; real_div; REAL_MUL_AC] THEN
  REAL_ARITH_TAC);;
```

### Informal statement
For any natural number `n` and real number `x`, the Fejér kernel `fejer_kernel n x` is defined as follows:
- If `n` is 0, then `fejer_kernel n x` is 0.
- Otherwise, if `x` is 0, then `fejer_kernel n x` is `n/2`.
- Otherwise, `fejer_kernel n x` is given by `(sin(n/2 * x))^2 / (2 * n * (sin(x/2))^2)`.

### Informal sketch
The proof proceeds by cases on `n` and `x`.
- Case `n = 0`: The result follows from the definition and `SUM_0`.
- Case `n != 0`: Further split into cases on `x`.
    - Case `x = 0`: The result is shown using simplification and arithmetic reasoning, applying rules like `SUM_ADD_NUMSEG`, `SUM_CONST_NUMSEG`, and `SUM_NUMBERS`. Field arithmetic is used to simplify.
    - Case `x != 0`: Another case split is performed based on whether `sin(x / 2)` is 0.
        - Case `sin(x / 2) = 0`: Simplify using rules like `REAL_POW_ZERO`, `ARITH_EQ`, `REAL_MUL_RZERO`, `real_div`, `REAL_INV_0`, `SUM_0`, `REAL_MUL_LZERO`.
        - Case `sin(x / 2) != 0`: Use real field arithmetic and trigonometric identities (`REAL_MUL_SIN_SIN`) to show that `fejer_kernel n x` is equivalent to the expression given on the right-hand side. Utilize identities to rewrite: `x / 2 - (n + 1 / 2) * x = --(n * x)` and `x / 2 + (n + 1 / 2) * x = (n + 1) * x`. Simplify using rules related to real division (`real_div`), summation (`SUM_RMUL` and `SUM_DIFFS`), cosine (`COS_NEG` and `REAL_SUB_COS`), and addition/subtraction (`SUB_ADD`).

### Mathematical insight
The Fejér kernel is a sequence of functions that provides an approximate identity in the theory of Fourier series. It is crucial because, unlike the Dirichlet kernel, the Fejér kernel converges to a Dirac delta function in a weaker sense (Cesàro summation), leading to the Fejér theorem, which states that the Fourier series of a continuous periodic function is uniformly Cesàro summable to the function itself. The formula gives an explicit form for this kernel and allows us to study its properties.

### Dependencies
- Definitions:
    - `fejer_kernel`
    - `dirichlet_kernel`
- Theorems/Lemmas:
    - `SUM_0`
    - `SUM_ADD_NUMSEG`
    - `SUM_CONST_NUMSEG`
    - `SUM_NUMBERS`
    - `SUB_ADD`
    - `REAL_OF_NUM_SUB`
    - `LE_1`
    - `SUB_0`
    - `REAL_OF_NUM_EQ`
    - `REAL_POW_ZERO`
    - `ARITH_EQ`
    - `REAL_MUL_RZERO`
    - `real_div`
    - `REAL_INV_0`
    - `SUM_0`
    - `REAL_MUL_LZERO`
    - `REAL_OF_NUM_EQ`
    - `SUM_LMUL`
    - `REAL_MUL_SIN_SIN`
    - `COS_NEG`
    - `REAL_OF_NUM_ADD`
    - `SUM_DIFFS`
    - `LE_0`
    - `REAL_SUB_COS`
    - `REAL_ADD_LID`
    - `REAL_SUB_RZERO`
    - `REAL_MUL_AC`
- Tactics:
    - `REAL_FIELD`
    - `REAL_ARITH_TAC`


---

## FEJER_KERNEL_CONTINUOUS_STRONG

### Name of formal statement
FEJER_KERNEL_CONTINUOUS_STRONG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FEJER_KERNEL_CONTINUOUS_STRONG = prove
 (`!n. (fejer_kernel n) real_continuous_on
       real_interval(--(&2 * pi),&2 * pi)`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
  REWRITE_TAC[fejer_kernel] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_RMUL THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_SUM THEN
  REWRITE_TAC[FINITE_NUMSEG; DIRICHLET_KERNEL_CONTINUOUS_STRONG]);;
```

### Informal statement
For all natural numbers `n`, the `fejer_kernel n` is real continuous on the real interval from `-2 * pi` to `2 * pi`.

### Informal sketch
The proof proceeds by induction on `n`.

- The base case `n = 0` is handled separately.  The theorem reduces to showing that a constant function is continuous on the specified interval. This is handled by `REAL_CONTINUOUS_ON_CONST`.
- For the inductive step (where `n > 0`), the definition of `fejer_kernel` is expanded.
- Then theorems `REAL_CONTINUOUS_ON_RMUL` and `REAL_CONTINUOUS_ON_SUM` are used to show that the `fejer_kernel` is real continuous on the real interval from `-2 * pi` to `2 * pi`.
- This uses the fact that `DIRICHLET_KERNEL_CONTINUOUS_STRONG` guarantees that the `dirichlet_kernel` is real continuous on the real interval from `-2 * pi` to `2 * pi`.

### Mathematical insight
This theorem establishes the continuity of the Fejér kernel on a particular interval. This is a key property for using the Fejér kernel in approximation theorems, particularly in Fourier analysis. Specifically, the Fejér kernel is used to construct a sequence of continuous functions that uniformly approximate a given function under certain conditions.

### Dependencies
- Definitions: `fejer_kernel`
- Theorems: `REAL_CONTINUOUS_ON_CONST`, `REAL_CONTINUOUS_ON_RMUL`, `REAL_CONTINUOUS_ON_SUM`, `FINITE_NUMSEG`, `DIRICHLET_KERNEL_CONTINUOUS_STRONG`


---

## FEJER_KERNEL_CONTINUOUS

### Name of formal statement
FEJER_KERNEL_CONTINUOUS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FEJER_KERNEL_CONTINUOUS = prove
 (`!n. (fejer_kernel n) real_continuous_on real_interval[--pi,pi]`,
  GEN_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `real_interval(--(&2 * pi),&2 * pi)` THEN
  REWRITE_TAC[FEJER_KERNEL_CONTINUOUS_STRONG] THEN
  REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;
```
### Informal statement
For all natural numbers `n`, the function `fejer_kernel n` is real-continuous on the real interval `[--pi,pi]`.

### Informal sketch
The proof proceeds as follows:
- Apply `REAL_CONTINUOUS_ON_SUBSET` which reduces the goal to showing continuity on a larger open interval.
- Provide the witness `real_interval(--(&2 * pi),&2 * pi)` as a superset of `real_interval[--pi,pi]`.
- Use the theorem `FEJER_KERNEL_CONTINUOUS_STRONG` to show that `fejer_kernel n` is continuous on a superset of `real_interval(--(&2 * pi),&2 * pi)`.
- Apply `SUBSET_REAL_INTERVAL` to complete the proof using the fact that `pi > 0`

### Mathematical insight
This theorem states that the Fejér kernel, for any natural number `n`, is a continuous function on the closed interval from `-π` to `π`. This is an important property in the context of Fourier analysis and signal processing. The Fejér kernel is used to obtain smoother approximations of functions compared to partial sums of Fourier series, and continuity is a desirable property for these approximations. The `FEJER_KERNEL_CONTINUOUS_STRONG` theorem is a stronger version of this result with an open interval.

### Dependencies
- Theorems:
  - `REAL_CONTINUOUS_ON_SUBSET`
  - `FEJER_KERNEL_CONTINUOUS_STRONG`
  - `SUBSET_REAL_INTERVAL`
  - `PI_POS`


---

## ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL

### Name of formal statement
ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL = prove
 (`!f n. f absolutely_real_integrable_on real_interval[--pi,pi]
         ==> (\x. fejer_kernel n x * f x)
             absolutely_real_integrable_on real_interval[--pi,pi]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
    ASM_REWRITE_TAC[FEJER_KERNEL_CONTINUOUS; ETA_AX;
                    REAL_CLOSED_REAL_INTERVAL];
    MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC REAL_COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[FEJER_KERNEL_CONTINUOUS; ETA_AX;
                    REAL_COMPACT_INTERVAL]]);;
```
### Informal statement
For all real-valued functions `f` and natural numbers `n`, if `f` is absolutely real integrable on the real interval from `-pi` to `pi`, then the function given by pointwise multiplication of `fejer_kernel n x` and `f x` is also absolutely real integrable on the real interval from `-pi` to `pi`.

### Informal sketch
The proof proceeds as follows:
- It starts by stripping quantifiers.
- Use `ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT` to reduce the goal to proving that `\x. fejer_kernel n x` is bounded and measurable.
- Split the goal into proving that `\x. fejer_kernel n x` is measurable on the interval and bounded on the interval.
- To prove measurability, we use `REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET` with `FEJER_KERNEL_CONTINUOUS` to show the Fejér kernel is measurable on closed intervals.
- To prove boundedness, we use `REAL_COMPACT_IMP_BOUNDED` applying it to `REAL_COMPACT_CONTINUOUS_IMAGE` along with `FEJER_KERNEL_CONTINUOUS` to show the Fejér kernel is bounded on compact intervals.

### Mathematical insight
This theorem shows that multiplying a function that is absolutely integrable on `real_interval[--pi,pi]` by the Fejér kernel preserves absolute integrability on that interval. This theorem is a key component in proving the convergence of Fourier series, as it shows that the convolution of the original function with the Fejér kernel is well-defined.

### Dependencies
- `ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT`
- `REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET`
- `FEJER_KERNEL_CONTINUOUS`
- `ETA_AX`
- `REAL_CLOSED_REAL_INTERVAL`
- `REAL_COMPACT_IMP_BOUNDED`
- `REAL_COMPACT_CONTINUOUS_IMAGE`
- `REAL_COMPACT_INTERVAL`


---

## ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED

### Name of formal statement
ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED = prove
 (`!f n c.
        f absolutely_real_integrable_on real_interval [--pi,pi] /\
        (!x. f(x + &2 * pi) = f(x))
        ==> (\x. fejer_kernel n x * f(t + x))
            absolutely_real_integrable_on real_interval[--pi,pi] /\
            (\x. fejer_kernel n x * f(t - x))
            absolutely_real_integrable_on real_interval[--pi,pi] /\
            (\x. fejer_kernel n x * c)
            absolutely_real_integrable_on real_interval[--pi,pi]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL THENL
   [ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET THEN
    ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`];
    REWRITE_TAC[absolutely_real_integrable_on] THEN
    ONCE_REWRITE_TAC[GSYM REAL_INTEGRABLE_REFLECT] THEN
    REWRITE_TAC[GSYM absolutely_real_integrable_on] THEN
    REWRITE_TAC[real_sub; REAL_NEG_NEG] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET THEN
    ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`];
    REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_CONST]]);;
```
### Informal statement
For all real-valued functions `f`, natural numbers `n`, and real numbers `c`, if `f` is absolutely real integrable on the real interval `[--pi, pi]` and `f` is periodic with period `2 * pi` (i.e., for all `x`, `f(x + 2 * pi) = f(x)`), then the function `x -> fejer_kernel n x * f(t + x)` is absolutely real integrable on the real interval `[--pi, pi]` and the function `x -> fejer_kernel n x * f(t - x)` is absolutely real integrable on the real interval `[--pi, pi]` and the function `x -> fejer_kernel n x * c` is absolutely real integrable on the real interval `[--pi, pi]`.

### Informal sketch
The proof proceeds by stripping the quantifiers and assumptions.
- First, apply `ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL` to show the integrability of `fejer_kernel n x * f(t + x)`.
- Adjust the argument to use the periodicity assumption of `f`:
    - Rewrite the argument `t + x` into `x + t` using `REAL_ADD_SYM`.
    - Apply `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`. The proof of periodic offset uses `pi - --pi = &2 * pi`, which is discharged by `ASM_REWRITE_TAC[REAL_ARITH pi - --pi = &2 * pi]`, proving the integrability of `x -> fejer_kernel n x * f(t + x)`.
- Second, prove the integrability of `fejer_kernel n x * f(t - x)`:
    - Rewrite the goal `absolutely_real_integrable_on` to use the fact that reflecting the integration interval preserves integrability with `REAL_INTEGRABLE_REFLECT` and `absolutely_real_integrable_on`.  Make sure the orientation is correct with `GSYM`.
    - Simplify `t - x` using `real_sub` and `REAL_NEG_NEG` to obtain `t + --x`.
    - Rewrite the argument `t + --x` into `--x + t` using `REAL_ADD_SYM`.
    - Apply `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`. Again, the proof of periodic offset depends on identity `pi - --pi = &2 * pi`, which is discharged by `ASM_REWRITE_TAC[REAL_ARITH pi - --pi = &2 * pi]`, proving the integrability of `x -> fejer_kernel n x * f(t - x)`.
- Finally, prove the integrability of `fejer_kernel n x * c` by applying `ABSOLUTELY_REAL_INTEGRABLE_CONST`.

### Mathematical insight
This theorem establishes the absolute real integrability of products involving the Fejér kernel under certain conditions. Specifically, it shows that if a function `f` is absolutely integrable on `[-pi, pi]` and periodic with period `2 * pi`, then the products of `fejer_kernel n x` with `f(t + x)`, `f(t - x)`, and any constant `c` are also absolutely integrable on `[-pi, pi]`. This result is important in Fourier analysis and related areas, as it ensures the existence of certain integrals involving the Fejér kernel, which is a crucial tool for approximating functions and proving convergence results for Fourier series.

### Dependencies
- `ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL`
- `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`
- `REAL_ARITH `pi - --pi = &2 * pi``
- `absolutely_real_integrable_on`
- `REAL_INTEGRABLE_REFLECT`
- `real_sub`
- `REAL_NEG_NEG`
- `ABSOLUTELY_REAL_INTEGRABLE_CONST`

### Porting notes (optional)
- The tactic `MATCH_MP_TAC` is used to apply theorems based on pattern matching and modus ponens. Ensure the target proof assistant has a similar mechanism for applying theorems based on matching.



---

## ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED_PART

### Name of formal statement
ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED_PART

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED_PART = prove
 (`!f n d c.
        f absolutely_real_integrable_on real_interval [--pi,pi] /\
        (!x. f(x + &2 * pi) = f(x)) /\ d <= pi
        ==> (\x. fejer_kernel n x * f(t + x))
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. fejer_kernel n x * f(t - x))
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. fejer_kernel n x * c)
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. fejer_kernel n x * (f(t + x) + f(t - x)))
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. fejer_kernel n x * ((f(t + x) + f(t - x)) - c))
            absolutely_real_integrable_on real_interval[&0,d]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o MATCH_MP
  ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED) ASSUME_TAC) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  MATCH_MP_TAC(TAUT
   `(a /\ b /\ c) /\ (a /\ b /\ c ==> d /\ e)
    ==> a /\ b /\ c /\ d /\ e`) THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `real_interval[--pi,pi]` THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN MP_TAC PI_POS THEN
    ASM_REAL_ARITH_TAC;
    SIMP_TAC[REAL_ADD_LDISTRIB; REAL_SUB_LDISTRIB;
             ABSOLUTELY_REAL_INTEGRABLE_ADD;
             ABSOLUTELY_REAL_INTEGRABLE_SUB]]);;
```
### Informal statement
For any function `f`, natural number `n`, real number `d`, and real number `c`, if `f` is absolutely real integrable on the real interval from `-pi` to `pi`, and `f` is periodic with period `2 * pi` (i.e., for all `x`, `f(x + 2 * pi) = f(x)`), and `d` is less than or equal to `pi`, then the following conditions hold:
1. The function `lambda x. fejer_kernel n x * f(t + x)` is absolutely real integrable on the real interval from `0` to `d`.
2. The function `lambda x. fejer_kernel n x * f(t - x)` is absolutely real integrable on the real interval from `0` to `d`.
3. The function `lambda x. fejer_kernel n x * c` is absolutely real integrable on the real interval from `0` to `d`.
4. The function `lambda x. fejer_kernel n x * (f(t + x) + f(t - x))` is absolutely real integrable on the real interval from `0` to `d`.
5. The function `lambda x. fejer_kernel n x * ((f(t + x) + f(t - x)) - c)` is absolutely real integrable on the real interval from `0` to `d`.

### Informal sketch
The proof proceeds by:
- Assuming `f` is absolutely real integrable on `real_interval [--pi,pi]`, `f` is periodic with period `2 * pi`, and `d <= pi`.
- Applying `ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED` to show the absolute integrability of `lambda x. fejer_kernel n x * f(t + x)`, `lambda x. fejer_kernel n x * f(t - x)`, and `lambda x. fejer_kernel n x * c` over the interval `real_interval[&0,d]`.
- Proving that if `a /\ b /\ c` and `(a /\ b /\ c ==> d /\ e)` then `a /\ b /\ c /\ d /\ e` using `TAUT`.
- Showing `lambda x. fejer_kernel n x * (f(t + x) + f(t - x))` and `lambda x. fejer_kernel n x * ((f(t + x) + f(t - x)) - c)` are also absolutely integrable on the same interval:
   - To show the absolute real integrability of these sums, it first uses `ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL` to show the integrability on the smaller interval. It leverages the periodicity along with `SUBSET_REAL_INTERVAL` and `PI_POS` to confirm the subinterval condition related to the original interval `real_interval [--pi,pi]`.
   - Then uses `ABSOLUTELY_REAL_INTEGRABLE_ADD` and `ABSOLUTELY_REAL_INTEGRABLE_SUB` to derive the final result.

### Mathematical insight
This theorem establishes that the Fejér kernel multiplied by various transformations of an absolutely integrable periodic function remains absolutely integrable on the interval `[0, d]` where `d <= pi`. This is crucial for proving convergence results of Fourier series using Fejér's theorem. It also shows absolute integrability of the Fejer kernel multiplied by the function reflected which is necessary to show symmetry, and the function and the reflected function added together with a adjustments.

### Dependencies
- `ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED`
- `ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL`
- `SUBSET_REAL_INTERVAL`
- `PI_POS`
- `REAL_ADD_LDISTRIB`
- `REAL_SUB_LDISTRIB`
- `ABSOLUTELY_REAL_INTEGRABLE_ADD`
- `ABSOLUTELY_REAL_INTEGRABLE_SUB`

### Porting notes (optional)
- Ensure that the target proof assistant has support for real analysis, including the concept of absolute integrability.
- The handling of real intervals and their properties (subset relations, positivity of `pi`) should be checked.
- The properties of addition and subtraction over reals, especially distributivity, should also be available.


---

## FOURIER_SUM_OFFSET_FEJER_KERNEL_HALF

### Name of formal statement
FOURIER_SUM_OFFSET_FEJER_KERNEL_HALF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_SUM_OFFSET_FEJER_KERNEL_HALF = prove
 (`!f n t.
     f absolutely_real_integrable_on real_interval[--pi,pi] /\
     (!x. f (x + &2 * pi) = f x) /\
     0 < n
     ==> sum(0..n-1) (\r. sum (0..2*r)
                              (\k. fourier_coefficient f k *
                                   trigonometric_set k t)) / &n - l =
         real_integral (real_interval[&0,pi])
                       (\x. fejer_kernel n x *
                            ((f(t + x) + f(t - x)) - &2 * l)) / pi`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LE_1; REAL_OF_NUM_EQ; REAL_FIELD
   `~(n = &0) ==> (x / n - l = y <=> x - n * l = n * y)`] THEN
  MP_TAC(ISPECL [`l:real`; `0`; `n - 1`] SUM_CONST_NUMSEG) THEN
  ASM_SIMP_TAC[SUB_ADD; LE_1; SUB_0] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN
  ASM_SIMP_TAC[FOURIER_SUM_OFFSET_DIRICHLET_KERNEL_HALF] THEN
  REWRITE_TAC[real_div; SUM_RMUL; REAL_MUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  W(MP_TAC o PART_MATCH (rand o rand) REAL_INTEGRAL_SUM o lhand o snd) THEN
  ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED_PART;
               ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
               FINITE_NUMSEG; REAL_LE_REFL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[SUM_RMUL] THEN
  ASM_SIMP_TAC[GSYM REAL_INTEGRAL_LMUL; REAL_LE_REFL;
               ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED_PART;
               ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
  MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[fejer_kernel; LE_1] THEN MATCH_MP_TAC(REAL_FIELD
   `~(n = &0) ==> s * f = n * s / n * f`) THEN
  ASM_SIMP_TAC[LE_1; REAL_OF_NUM_EQ]);;
```

### Informal statement
For any function `f`, natural number `n`, and real number `t`, if `f` is absolutely real integrable on the real interval from `-pi` to `pi`, `f` is periodic with period `2*pi` (i.e., for all `x`, `f(x + 2*pi) = f(x)`), and `n` is strictly positive, then the average of the partial Fourier sums offset by `l` (where the partial Fourier sums consider frequencies from `-r` to `r` for `r` from `0` to `n-1`) is equal to the real integral from `0` to `pi` of the Fejér kernel times the difference between the reflected and shifted function values of `f` and `2*l`, all divided by `pi`.  Specifically,
  `sum(0..n-1) (\r. sum (0..2*r) (\k. fourier_coefficient f k * trigonometric_set k t)) / &n - l = real_integral (real_interval[&0,pi]) (\x. fejer_kernel n x * ((f(t + x) + f(t - x)) - &2 * l)) / pi`.

### Informal sketch
The proof proceeds by:
- Simplifying the initial goal by stripping quantifiers and assumptions.
- Applying simplification tactics.
- Using `SUM_CONST_NUMSEG` to introduce `l` into the summation.
- Rewriting and simplifying the sum using the definition of the `fourier_sum_offset_dirichlet_kernel_half`.
- Rewriting the real division in preparation to manipulate the sums.
- Distributing the summation over multiplication.
- Transforming a summation of integrals into an integral of a summation.  This step uses `REAL_INTEGRAL_SUM` after matching the hypothesis of the theorem.
- Simplifying using integrability results for the Dirichlet and Fejér kernels.
- Rewriting the remaining sum and integral terms.  This step uses `REAL_INTEGRAL_LMUL` to pull a scalar out of the integral.
- Applying `REAL_INTEGRAL_EQ` to transform the equality into an equality of integrands.
- Introducing a variable `x` and stripping quantifiers to expose the equation and assumptions.
- Simplifying the equation using the definition of the `fejer_kernel`.
- Multiplying and dividing by constants to prepare for more simplification.
- Applying arithmetic simplification to complete the proof.

### Mathematical insight
This theorem relates the average of partial Fourier series (with a constant offset) to an integral involving the Fejér kernel. The Fejér kernel is a well-known smoothing kernel used in Fourier analysis. This result is a quantitative form of Fejér's theorem, which states that the Cesàro means (averages) of the partial Fourier series of a continuous periodic function converge uniformly to the function. The constant offset appears to arise from the integral of the function, in some sense.

### Dependencies
- `LE_1`
- `REAL_OF_NUM_EQ`
- `REAL_FIELD`
- `SUM_CONST_NUMSEG`
- `SUB_ADD`
- `SUB_0`
- `SUM_SUB_NUMSEG`
- `FOURIER_SUM_OFFSET_DIRICHLET_KERNEL_HALF`
- `real_div`
- `SUM_RMUL`
- `REAL_MUL_ASSOC`
- `REAL_INTEGRAL_SUM`
- `ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED_PART`
- `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE`
- `FINITE_NUMSEG`
- `REAL_LE_REFL`
- `REAL_INTEGRAL_LMUL`
- `ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED_PART`
- `REAL_INTEGRAL_EQ`
- `fejer_kernel`

### Porting notes (optional)
- The theorem depends heavily on real analysis results (integrability, integrals of products). Ensure the target proof assistant has similar theorems available.
- The proof also relies on several facts from field arithmetic.
- Porting this proof involves managing assumptions about integrability and periodicity carefully. The automation in HOL Light handles these automatically, but other systems might require more manual assistance.


---

## FOURIER_SUM_LIMIT_FEJER_KERNEL_HALF

### Name of formal statement
FOURIER_SUM_LIMIT_FEJER_KERNEL_HALF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_SUM_LIMIT_FEJER_KERNEL_HALF = prove
 (`!f t l.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> (((\n. sum(0..n-1) (\r. sum (0..2*r)
                                        (\k. fourier_coefficient f k *
                                             trigonometric_set k t)) / &n)
               ---> l) sequentially <=>
             ((\n. real_integral (real_interval[&0,pi])
                                 (\x. fejer_kernel n x *
                                      ((f(t + x) + f(t - x)) - &2 * l)))
              ---> &0) sequentially)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM FOURIER_SUM_LIMIT_PAIR] THEN
  GEN_REWRITE_TAC LAND_CONV [REALLIM_NULL] THEN REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM(MATCH_MP REALLIM_NULL_RMUL_EQ PI_NZ)] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EQ THEN MATCH_MP_TAC REALLIM_EVENTUALLY THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
  ASM_SIMP_TAC[FOURIER_SUM_OFFSET_FEJER_KERNEL_HALF; LE_1] THEN
  ASM_SIMP_TAC[PI_POS; REAL_LT_IMP_NZ; REAL_DIV_RMUL; REAL_SUB_REFL]);;
```
### Informal statement
For all functions `f`, real numbers `t` and `l`, if `f` is absolutely real integrable on the real interval `[-pi, pi]` and `f(x + 2*pi) = f(x)` for all `x`, then the sequence whose `n`-th term is the average of the partial sums of the Fourier series of `f` evaluated at `t` converges sequentially to `l` if and only if the sequence whose `n`-th term is the real integral over the real interval `[0, pi]` of the product of the `n`-th `fejer_kernel` and `(f(t + x) + f(t - x) - 2*l)` converges sequentially to `0`.

### Informal sketch
The proof proceeds as follows:
- Start by stripping the theorem.
- Apply `ASM_SIMP_TAC` using `GSYM FOURIER_SUM_LIMIT_PAIR`. This likely uses the `FOURIER_SUM_LIMIT_PAIR` theorem which presumably relates the convergence of the Fourier series partial sums to an integral involving the Fejer kernel over the interval `[-pi, pi]`.
- Rewrite using `REALLIM_NULL` and `GSYM(MATCH_MP REALLIM_NULL_RMUL_EQ PI_NZ)` to handle the fact that the integral is over `[0, pi]` instead of `[-pi, pi]`. It involves showing that `pi` is non-zero, which is needed to scale real limits.
- Apply `REALLIM_TRANSFORM_EQ` and `REALLIM_EVENTUALLY`. Then rewrite with `EVENTUALLY_SEQUENTIALLY`. This uses theorems about manipulating real limits and converting an eventually condition into a sequential limit.
- Existentially quantify `1`.
- Apply `ASM_SIMP_TAC` using `FOURIER_SUM_OFFSET_FEJER_KERNEL_HALF` and `LE_1`. This likely simplifies the expression using properties of the Fejer kernel. `LE_1` is related to the fact that `1` is less than or equal to something, as quantified.
- Apply `ASM_SIMP_TAC` with `PI_POS`, `REAL_LT_IMP_NZ`, `REAL_DIV_RMUL`, and `REAL_SUB_REFL` to perform final simplifications involving properties of real numbers.

### Mathematical insight
The theorem provides a condition for the convergence of taking Cesàro means of Fourier partial sums to a candidate limit, expressed in terms of the integral of the Fejer Kernel against a symmetrized and offset version of the function.

### Dependencies
- `FOURIER_SUM_LIMIT_PAIR`
- `REALLIM_NULL`
- `PI_NZ`
- `REALLIM_TRANSFORM_EQ`
- `REALLIM_EVENTUALLY`
- `EVENTUALLY_SEQUENTIALLY`
- `FOURIER_SUM_OFFSET_FEJER_KERNEL_HALF`
- `LE_1`
- `PI_POS`
- `REAL_LT_IMP_NZ`
- `REAL_DIV_RMUL`
- `REAL_SUB_REFL`
- `absolutely_real_integrable_on`
- `real_interval`
- `fourier_coefficient`
- `trigonometric_set`
- `fejer_kernel`
- `real_integral`


---

## HAS_REAL_INTEGRAL_FEJER_KERNEL

### Name of formal statement
HAS_REAL_INTEGRAL_FEJER_KERNEL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HAS_REAL_INTEGRAL_FEJER_KERNEL = prove
 (`!n. (fejer_kernel n has_real_integral (if n = 0 then &0 else pi))
       (real_interval[--pi,pi])`,
  GEN_TAC THEN GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[fejer_kernel] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[HAS_REAL_INTEGRAL_0] THEN
  SUBGOAL_THEN `pi = sum(0..n-1) (\r. pi) / &n`
   (fun th -> GEN_REWRITE_TAC LAND_CONV [th])
  THENL
   [ASM_SIMP_TAC[SUM_CONST_NUMSEG; SUB_ADD; LE_1; SUB_0] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM REAL_OF_NUM_EQ]) THEN
    CONV_TAC REAL_FIELD;
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_RMUL THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_SUM THEN
    REWRITE_TAC[FINITE_NUMSEG; HAS_REAL_INTEGRAL_DIRICHLET_KERNEL]]);;
```

### Informal statement
For all natural numbers `n`, the Fejér kernel function `fejer_kernel n` has a real integral of `π` (if `n` is not 0) or `0` (if `n` is 0) over the real interval `[-π, π]`.

### Informal sketch
The proof proceeds by induction and case analysis.
- First, the goal is generalized to eliminate the leading quantifier and rewrite using the definition of `fejer_kernel` and ETA-reduction.
- We consider the base case `n = 0`. In this case, we need to show that `fejer_kernel 0` has a real integral of `0` on `[-π, π]`. This follows directly from the theorem `HAS_REAL_INTEGRAL_0`.
- In the case where `n ≠ 0`, it is necessary to show that `fejer_kernel n` has a real integral of `π` on `[-π, π]`. The goal pi = sum(0..n-1) (\r. pi) / &n is introduced. This can be proved using `SUM_CONST_NUMSEG`, `SUB_ADD`, `LE_1`, `SUB_0` and field arithmetic.
- The result then follows by leveraging the relationship between the Fejér kernel and the Dirichlet kernel. Specifically, we make use of theorems such as `HAS_REAL_INTEGRAL_RMUL`, `HAS_REAL_INTEGRAL_SUM`, and `HAS_REAL_INTEGRAL_DIRICHLET_KERNEL`. The properties of `FINITE_NUMSEG` are needed for the sum over a finite number of real integrals.

### Mathematical insight
This theorem establishes a crucial property of the Fejér kernel, namely that its integral over the interval `[-π, π]` is equal to `π` (when n != 0). The Fejér kernel is a fundamental tool in Fourier analysis, often used to approximate functions via convolution. This result is important as it relates to the convergence properties of Fourier series.

### Dependencies
- Definitions: `fejer_kernel`
- Theorems: `HAS_REAL_INTEGRAL_0`, `SUM_CONST_NUMSEG`, `SUB_ADD`, `LE_1`, `SUB_0`, `HAS_REAL_INTEGRAL_RMUL`, `HAS_REAL_INTEGRAL_SUM`, `FINITE_NUMSEG`, `HAS_REAL_INTEGRAL_DIRICHLET_KERNEL`, `REAL_OF_NUM_EQ`


---

## HAS_REAL_INTEGRAL_FEJER_KERNEL_HALF

### Name of formal statement
HAS_REAL_INTEGRAL_FEJER_KERNEL_HALF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HAS_REAL_INTEGRAL_FEJER_KERNEL_HALF = prove
 (`!n. (fejer_kernel n has_real_integral (if n = 0 then &0 else pi / &2))
       (real_interval[&0,pi])`,
  GEN_TAC THEN GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[fejer_kernel] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[HAS_REAL_INTEGRAL_0] THEN
  SUBGOAL_THEN `pi / &2 = sum(0..n-1) (\r. pi / &2) / &n`
   (fun th -> GEN_REWRITE_TAC LAND_CONV [th])
  THENL
   [ASM_SIMP_TAC[SUM_CONST_NUMSEG; SUB_ADD; LE_1; SUB_0] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM REAL_OF_NUM_EQ]) THEN
    CONV_TAC REAL_FIELD;
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_RMUL THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_SUM THEN REWRITE_TAC[GSYM real_div] THEN
    REWRITE_TAC[FINITE_NUMSEG; HAS_REAL_INTEGRAL_DIRICHLET_KERNEL_HALF]]);;
```

### Informal statement
For all natural numbers `n`, the `fejer_kernel n` has a real integral equal to `0` if `n = 0` and `pi / 2` otherwise, over the real interval `[0, pi]`.

### Informal sketch
The proof proceeds by induction on `n`.

- First, universally generalize over `n` and rewrite using definitions and simplifications.
- Perform case split on `n = 0`.
    - If `n = 0`, apply the theorem `HAS_REAL_INTEGRAL_0`.
    - If `n != 0`, the goal becomes proving that the real integral of `fejer_kernel n` over the interval `[0, pi]` is `pi / 2`. This is approached by showing that `pi / 2 = sum(0..n-1) (\r. pi / 2) / &n`.
        - Simplify the sum `sum(0..n-1) (\r. pi / 2) / &n` using `SUM_CONST_NUMSEG`, `SUB_ADD`, `LE_1`, and `SUB_0`.
        - Use `REAL_OF_NUM_EQ` to convert a numeral equality to a real equality.
        - Apply field tactics to simplify the expression.
        - Use `real_div`, `HAS_REAL_INTEGRAL_RMUL`, `HAS_REAL_INTEGRAL_SUM`, rewrite with `real_div` again, and then apply `FINITE_NUMSEG` and `HAS_REAL_INTEGRAL_DIRICHLET_KERNEL_HALF`.

### Mathematical insight
This theorem states that the integral of the Fejér kernel from 0 to pi is equal to pi/2.  This is a key property of the Fejér kernel, which is used in Fourier analysis to approximate periodic functions. The Fejér kernel is a smoother, non-negative version of the Dirichlet kernel, and its integral property is crucial for proving convergence results for Fourier series.

### Dependencies
- `fejer_kernel`
- `HAS_REAL_INTEGRAL_0`
- `SUM_CONST_NUMSEG`
- `SUB_ADD`
- `LE_1`
- `SUB_0`
- `REAL_OF_NUM_EQ`
- `real_div`
- `HAS_REAL_INTEGRAL_RMUL`
- `HAS_REAL_INTEGRAL_SUM`
- `FINITE_NUMSEG`
- `HAS_REAL_INTEGRAL_DIRICHLET_KERNEL_HALF`

### Porting notes (optional)
- The use of real analysis, summation, and interval integrals should be considered. Ensure that translated code handles summations and integrals of real-valued functions over intervals appropriately.
- The proof relies on simplification and rewriting using properties of real numbers and summation, which may require tactics or functions with similar capabilities in other proof assistants.


---

## FEJER_KERNEL_POS_LE

### Name of formal statement
FEJER_KERNEL_POS_LE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FEJER_KERNEL_POS_LE = prove
 (`!n x. &0 <= fejer_kernel n x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FEJER_KERNEL] THEN
  REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_POS; REAL_LE_DIV]) THEN
  MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS]) THEN
  REWRITE_TAC[REAL_LE_POW_2]);;
```

### Informal statement
For all natural numbers `n` and for all real numbers `x`, `0` is less than or equal to the Fejér kernel of `n` evaluated at `x`.

### Informal sketch
The proof proceeds as follows:
- First, expand the definition of the `fejer_kernel` using the theorem `FEJER_KERNEL`.
- Then, perform a case split on conditions and simplify using assumptions and the following theorems: `REAL_POS`, `REAL_LE_DIV`.
- Apply `REAL_LE_DIV`.
- Rewrite using `REAL_LE_POW_2`.
- Repeatedly apply `REAL_LE_MUL` and rewrite using `REAL_POS`.
- Rewrite using `REAL_LE_POW_2`.

### Mathematical insight
The Fejér kernel is a non-negative function. This theorem establishes the non-negativity of the Fejér kernel, which is crucial in Fourier analysis for proving convergence results. The Fejér kernel is used to construct a sequence of functions that converge to a given function in various senses. Its non-negativity is essential for ensuring that the approximation process behaves well and does not introduce unwanted oscillations.

### Dependencies
- Definitions: `FEJER_KERNEL`
- Theorems: `REAL_POS`, `REAL_LE_DIV`, `REAL_LE_POW_2`, `REAL_LE_MUL`


---

## FOURIER_FEJER_CESARO_SUMMABLE

### Name of formal statement
FOURIER_FEJER_CESARO_SUMMABLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_FEJER_CESARO_SUMMABLE = prove
 (`!f x l r.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f(x + &2 * pi) = f x) /\
        (f ---> l) (atreal x within {x' | x' <= x}) /\
        (f ---> r) (atreal x within {x' | x' >= x})
        ==> ((\n. sum(0..n-1) (\m. sum (0..2*m)
                                       (\k. fourier_coefficient f k *
                                            trigonometric_set k x)) / &n)
             ---> (l + r) / &2)
            sequentially`,
  MAP_EVERY X_GEN_TAC [`f:real->real`; `t:real`; `l:real`; `r:real`] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FOURIER_SUM_LIMIT_FEJER_KERNEL_HALF] THEN
  REWRITE_TAC[REAL_ARITH `&2 * x / &2 = x`] THEN
  ABBREV_TAC `h = \u. ((f:real->real)(t + u) + f(t - u)) - (l + r)` THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
  SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `(h ---> &0) (atreal(&0) within {x | &0 <= x})`
  ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[REAL_ARITH
     `(f' + f) - (l + l'):real = (f - l) + (f' - l')`] THEN
    MATCH_MP_TAC REALLIM_NULL_ADD THEN CONJ_TAC THENL
     [UNDISCH_TAC `(f ---> l) (atreal t within {x' | x' <= t})` THEN
      REWRITE_TAC[REALLIM_WITHINREAL] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
      ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d1:real` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
       X_GEN_TAC `x:real` THEN MP_TAC(SPEC `t - x:real` th)) THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
      REAL_ARITH_TAC;
      UNDISCH_TAC `(f ---> r) (atreal t within {x' | x' >= t})` THEN
      REWRITE_TAC[REALLIM_WITHINREAL] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
      ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d1:real` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
       X_GEN_TAC `x:real` THEN MP_TAC(SPEC `t + x:real` th)) THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?k. &0 < k /\ k < pi /\
        (!x. &0 < x /\ x <= k ==> abs(h x) < e / &2 / pi)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(h ---> &0) (atreal (&0) within {x | &0 <= x})` THEN
    REWRITE_TAC[REALLIM_WITHINREAL] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2 / pi`) THEN
    ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; PI_POS; IN_ELIM_THM; REAL_SUB_RZERO;
                 LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `k:real` THEN STRIP_TAC THEN EXISTS_TAC `min k pi / &2` THEN
    REPEAT(CONJ_TAC THENL
     [MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\n. real_integral (real_interval[k,pi])
                        (\x. fejer_kernel n x * h x))
     ---> &0) sequentially`
  MP_TAC THENL
   [MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
    EXISTS_TAC
     `\n. real_integral (real_interval[k,pi])
                        (\x. abs(h x) / (&2 * sin(x / &2) pow 2)) / &n` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REALLIM_NULL_LMUL THEN
      REWRITE_TAC[REALLIM_1_OVER_N]] THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[FEJER_KERNEL; LE_1] THEN
    SUBGOAL_THEN
     `(\x. h x / (&2 * sin(x / &2) pow 2))
      absolutely_real_integrable_on real_interval[k,pi]`
    MP_TAC THENL
     [REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
      REWRITE_TAC[GSYM real_div] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_IMP_REAL_MEASURABLE THEN
        MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS;
        MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN
        MATCH_MP_TAC REAL_COMPACT_CONTINUOUS_IMAGE THEN
        REWRITE_TAC[REAL_COMPACT_INTERVAL];
        EXPAND_TAC "h" THEN MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_SUB THEN
        REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
        MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL THEN
        EXISTS_TAC `real_interval[--pi,pi]` THEN CONJ_TAC THENL
         [MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ADD THEN CONJ_TAC THENL
           [ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
            MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET THEN
            ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`];
            REWRITE_TAC[real_sub; absolutely_real_integrable_on] THEN
            ONCE_REWRITE_TAC[GSYM REAL_INTEGRABLE_REFLECT] THEN
            REWRITE_TAC[GSYM absolutely_real_integrable_on] THEN
            REWRITE_TAC[real_sub; REAL_NEG_NEG] THEN
            ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
            MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET THEN
            ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`]];
          REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC]] THEN
      (REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
       REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `x:real` THEN
       STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_INV_WITHINREAL THEN
       CONJ_TAC THENL
        [MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_WITHINREAL THEN
         REAL_DIFFERENTIABLE_TAC;
         REWRITE_TAC[REAL_RING `&2 * x pow 2 = &0 <=> x = &0`] THEN
         MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SIN_POS_PI THEN
         ASM_REAL_ARITH_TAC]);
      DISCH_THEN(fun th -> ASSUME_TAC th THEN
        MP_TAC(MATCH_MP ABSOLUTELY_REAL_INTEGRABLE_ABS th)) THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_NUM; REAL_ABS_POW] THEN
      REWRITE_TAC[REAL_POW2_ABS] THEN DISCH_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [real_div] THEN
    ASM_SIMP_TAC[GSYM REAL_INTEGRAL_RMUL;
                 ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
    MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_RMUL;
                 ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
    MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN
      GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
      REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      REWRITE_TAC[GSYM REAL_INV_MUL; REAL_ABS_MUL] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `x <= y <=> x <= &1 * y`] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      REWRITE_TAC[REAL_ABS_POW; REAL_POW2_ABS; ABS_SQUARE_LE_1; SIN_BOUND] THEN
      MATCH_MP_TAC(REAL_ARITH `x = y /\ &0 <= x ==> abs x <= y`) THEN
      REWRITE_TAC[GSYM real_div; REAL_LE_INV_EQ] THEN
      SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LE_POW_2] THEN
      REWRITE_TAC[REAL_MUL_AC];
      DISCH_TAC] THEN
    MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC `\x.  abs(h x) / (&2 * sin(x / &2) pow 2) * inv(&n)` THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_RMUL;
                 ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
    MATCH_MP_TAC INTEGRABLE_IMP_REAL_MEASURABLE THEN
    MATCH_MP_TAC REAL_INTEGRABLE_EQ THEN
    EXISTS_TAC
     `\x. sin(&n / &2 * x) pow 2 / (&2 * &n * sin(x / &2) pow 2) * h(x)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_INV_MUL; GSYM REAL_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[REAL_ARITH
     `s * t * n * i * h:real = n * s * h * (t * i)`] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN REWRITE_TAC[GSYM REAL_INV_MUL] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    ASM_REWRITE_TAC[GSYM real_div] THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_IMP_REAL_MEASURABLE THEN
      MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_WITHINREAL THEN
      REAL_DIFFERENTIABLE_TAC;
      REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN EXISTS_TAC `&1` THEN
      REWRITE_TAC[REAL_ABS_POW; REAL_POW2_ABS; ABS_SQUARE_LE_1; SIN_BOUND]];
    ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `MAX 1 N` THEN
  X_GEN_TAC `n:num` THEN
  REWRITE_TAC[ARITH_RULE `MAX a b <= x <=> a <= x /\ b <= x`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\x. fejer_kernel n x * h x`; `&0`; `pi`; `k:real`]
        REAL_INTEGRAL_COMBINE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN EXPAND_TAC "h" THEN
    ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED_PART;
                 ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
                 REAL_LE_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs x <= e / &2 ==> x + y = z ==> abs y < e / &2 ==> abs z < e`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[&0,k])
                            (\x. fejer_kernel n x * e / &2 / pi)` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `real_integral (real_interval [&0,k]) (\x. fejer_kernel n x * h x) =
      real_integral (real_interval [&0,k])
                    (\x. fejer_kernel n x * (if x = &0 then &0 else h x))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN
      EXISTS_TAC `{&0}` THEN SIMP_TAC[IN_DIFF; IN_SING] THEN
      REWRITE_TAC[REAL_NEGLIGIBLE_SING];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] REAL_INTEGRABLE_SPIKE) THEN
      MAP_EVERY EXISTS_TAC [`\x. fejer_kernel n x * h x`; `{&0}`] THEN
      SIMP_TAC[IN_DIFF; IN_SING; REAL_NEGLIGIBLE_SING] THEN
      EXPAND_TAC "h" THEN
      ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED_PART;
                   ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
                   REAL_LT_IMP_LE];
      MP_TAC(ISPECL
       [`\x:real. e / &2 / pi`; `n:num`; `k:real`; `&0`]
        ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED_PART) THEN
      ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_CONST; REAL_LT_IMP_LE;
                   ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE];
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      REWRITE_TAC[REAL_ABS_POS; REAL_ARITH `abs x <= x <=> &0 <= x`] THEN
      REWRITE_TAC[FEJER_KERNEL_POS_LE] THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_ABS_NUM; REAL_POS;
                   PI_POS_LE; REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    MP_TAC(SPEC `n:num` HAS_REAL_INTEGRAL_FEJER_KERNEL_HALF) THEN
    ASM_SIMP_TAC[LE_1] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
     `real_integral (real_interval[&0,pi])
                    (\x. fejer_kernel n x * e / &2 / pi)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_SUBSET_LE THEN REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_INTEGRABLE_RMUL THEN REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC REAL_INTEGRABLE_ON_SUBINTERVAL THEN
        EXISTS_TAC `real_interval[&0,pi]` THEN CONJ_TAC THENL
         [ASM_MESON_TAC[real_integrable_on];
          REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_INTEGRABLE_RMUL THEN REWRITE_TAC[ETA_AX] THEN
        ASM_MESON_TAC[real_integrable_on];
        REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_REWRITE_TAC[FEJER_KERNEL_POS_LE] THEN
        REPEAT(MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC) THEN
        MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC];
      FIRST_X_ASSUM(MP_TAC o MATCH_MP HAS_REAL_INTEGRAL_RMUL) THEN
      DISCH_THEN(MP_TAC o SPEC `e / &2 / pi`) THEN
      SIMP_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
      REPEAT STRIP_TAC THEN SIMP_TAC[PI_POS; REAL_FIELD
       `&0 < pi ==> pi / &2 * e / &2 / pi = e / &4`] THEN
      ASM_REAL_ARITH_TAC]]);;
```
### Informal statement
For any real-valued function `f`, real number `x`, real numbers `l` and `r`, if the function `f` is absolutely real integrable on the real interval from `-pi` to `pi`, and `f` is periodic with period `2*pi` (i.e., `f(x + 2*pi) = f x` for all `x`), and `f` tends to `l` at `x` from the left (i.e., the limit of `f(x')` as `x'` approaches `x` from below is `l`), and `f` tends to `r` at `x` from the right (i.e., the limit of `f(x')` as `x'` approaches `x` from above is `r`), then the Cesaro sum of the Fourier series of `f` converges sequentially to `(l + r) / 2`. The Cesaro sum is defined as the average of the first `n` partial sums of the Fourier series, where the `m`-th partial sum is the sum from `k = 0` to `2*m` of `fourier_coefficient f k * trigonometric_set k x`.

### Informal sketch
The proof proceeds as follows:
- Assume `f` is absolutely real integrable on `[-pi, pi]`, `f` is periodic with period `2*pi`, `f` tends to `l` at `x` from the left, and `f` tends to `r` at `x` from the right.
- Apply `FOURIER_SUM_LIMIT_FEJER_KERNEL_HALF` and rewrite `&2 * x / &2 = x`.
- Define `h u = f(x + u) + f(x - u) - (l + r)`.
- Show that if `f` has limits `l` and `r` from the left and right at `x`, then `h` tends to 0 at 0 from the right. This involves using the properties of limits and real arithmetic.
- Show that the Cesaro sum converges to `(l + r) / 2` by showing that the integral of `fejer_kernel n x * h x` over `[0, pi]` tends to 0 sequentially. This is achieved by splitting the interval of integration into `[0, k]` and `[k, pi]` for some small `k > 0`.
 - On `[0, k]`, `h` is small, so the integral is small.
 - On `[k, pi]`, we use properties of the `fejer_kernel` to show that its integral with `h` tends to 0. This involves using `REALLIM_NULL_COMPARISON` and proving absolute integrability.
 - The absolute integrability of `h(x) / (2 * sin(x/2)^2)` over `[k, pi]` is established using properties of integrable functions, continuous functions, and the fact that `sin(x/2)` is bounded away from 0 on this interval.
- Combining these results, the Cesaro sum converges to `(l + r) / 2`.

### Mathematical insight
This theorem establishes the convergence of the Cesaro sum of the Fourier series of a function to the average of its left and right limits at a given point, provided the function is absolutely integrable and periodic. This is a weaker condition than pointwise convergence of the Fourier series itself, which may not hold in general. The Cesaro sum provides a smoother form of convergence. It essentially says that at any point x where f has a jump discontinuity, the Cesaro sum converges to the midpoint of the jump.

### Dependencies
- `FOURIER_SUM_LIMIT_FEJER_KERNEL_HALF`
- `REALLIM_NULL_ADD`
- `REALLIM_WITHINREAL`
- `MONO_FORALL`
- `MONO_EXISTS`
- `MONO_IMP`
- `REALLIM_SEQUENTIALLY`
- `REALLIM_NULL_COMPARISON`
- `REALLIM_NULL_LMUL`
- `REALLIM_1_OVER_N`
- `EVENTUALLY_SEQUENTIALLY`
- `FEJER_KERNEL`
- `ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT`
- `INTEGRABLE_IMP_REAL_MEASURABLE`
- `REAL_INTEGRABLE_CONTINUOUS`
- `REAL_COMPACT_IMP_BOUNDED`
- `REAL_COMPACT_CONTINUOUS_IMAGE`
- `REAL_COMPACT_INTERVAL`
- `ABSOLUTELY_REAL_INTEGRABLE_SUB`
- `ABSOLUTELY_REAL_INTEGRABLE_CONST`
- `ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL`
- `ABSOLUTELY_REAL_INTEGRABLE_ADD`
- `ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET`
- `REAL_INTEGRABLE_REFLECT`
- `REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN`
- `REAL_CONTINUOUS_INV_WITHINREAL`
- `REAL_DIFFERENTIABLE_IMP_CONTINUOUS_WITHINREAL`
- `ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE`
- `REAL_INTEGRAL_ABS_BOUND_INTEGRAL`
- `REAL_INTEGRABLE_RMUL`
- `REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE`
- `REAL_INTEGRABLE_EQ`
- `REAL_INTEGRABLE_LMUL`
- `ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED_PART`
- `REAL_INTEGRAL_COMBINE`
- `REAL_INTEGRAL_SPIKE`
- `REAL_NEGLIGIBLE_SING`
- `HAS_REAL_INTEGRAL_FEJER_KERNEL_HALF`
- `REAL_INTEGRAL_SUBSET_LE`
- `REAL_INTEGRABLE_ON_SUBINTERVAL`
- `HAS_REAL_INTEGRAL_RMUL`
### Porting notes (optional)
- The proof relies heavily on real analysis lemmas and theorems already present in HOL Light, thus a target proof assistant should possess similar theorems for a smooth translation.
- The tactic `MAP_EVERY X_GEN_TAC` could be translated to `intros` in Coq, or a similar introduction of variables tactic in other proof assistants.
- The proof makes use of several HOL Light-specific tactics such as `ASM_SIMP_TAC`, `REWRITE_TAC`, `SUBGOAL_THEN`. These would have to be translated to their corresponding counterparts or custom tactics within other proof assistants. For example, `ASM_SIMP_TAC` could be translated to tactics like `simpl` or `auto` along with necessary lemmas in Coq. Rewriting is generally well-supported in other systems via `rewrite` or `simp`.



---

## FOURIER_FEJER_CESARO_SUMMABLE_SIMPLE

### Name of formal statement
FOURIER_FEJER_CESARO_SUMMABLE_SIMPLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FOURIER_FEJER_CESARO_SUMMABLE_SIMPLE = prove
 (`!f x l r.
        f real_continuous_on (:real) /\ (!x. f(x + &2 * pi) = f x)
        ==> ((\n. sum(0..n-1) (\m. sum (0..2*m)
                                       (\k. fourier_coefficient f k *
                                            trigonometric_set k x)) / &n)
             ---> f(x))
            sequentially`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [REAL_ARITH `x = (x + x) / &2`] THEN
  MATCH_MP_TAC FOURIER_FEJER_CESARO_SUMMABLE THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_CONTINUOUS THEN
    ASM_MESON_TAC[REAL_CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    CONJ_TAC THEN MATCH_MP_TAC REALLIM_ATREAL_WITHINREAL THEN
    REWRITE_TAC[GSYM REAL_CONTINUOUS_ATREAL] THEN
    ASM_MESON_TAC[REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT; REAL_OPEN_UNIV;
                  IN_UNIV]]);;
```
### Informal statement
For all real-valued functions `f`, all real numbers `x`, `l`, and `r`, if `f` is real continuous on the entire set of real numbers and `f` is periodic with period `2 * pi` (i.e., for all `x`, `f(x + 2 * pi) = f x`), then the Cesaro sum of the Fourier series of `f` at `x` converges to `f(x)` sequentially. More formally, the sequence whose `n`-th term is the average of the partial sums (up to `2*m` where the average considers from `m = 0` to `n-1`) of the Fourier series of `f` converges to `f(x)` as `n` tends to infinity.

### Informal sketch
The proof proceeds as follows:
- Strip the quantifiers and assumptions using `REPEAT STRIP_TAC`.
- Rewrite the goal using the fact that `x = (x + x) / 2`. This is done using `GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [REAL_ARITH x = (x + x) / &2`]
- Apply the theorem `FOURIER_FEJER_CESARO_SUMMABLE` using `MATCH_MP_TAC`. This reduces the goal to showing that `f` satisfies the conditions required by `FOURIER_FEJER_CESARO_SUMMABLE`.
- Simplify the assumptions using `ASM_REWRITE_TAC[]`.
- Split the goal into two subgoals using `CONJ_TAC`.
- The first subgoal is to prove that f is absolutely real integrable over the interval `[: -pi, pi :]`. This is achieved by using `MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_CONTINUOUS` and `ASM_MESON_TAC[REAL_CONTINUOUS_ON_SUBSET; SUBSET_UNIV]`. The conditions of `ABSOLUTELY_REAL_INTEGRABLE_CONTINUOUS` are verified using the assumptions regarding the function `f`'s continuity.
- The second subgoal is to show that the limit of `f(y)` as `y` approaches `x` is `f(x)`. This is achieved by using `CONJ_TAC`, `MATCH_MP_TAC REALLIM_ATREAL_WITHINREAL`, `REWRITE_TAC[GSYM REAL_CONTINUOUS_ATREAL]`, and `ASM_MESON_TAC[REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT; REAL_OPEN_UNIV; IN_UNIV]`. The continuity of `f` at `x` is derived from the assumption that `f` is real continuous on the entire real line.

### Mathematical insight
This theorem establishes that the Cesaro sums (averages of partial sums) of the Fourier series of a continuous, periodic function converge to the function's value at any point. This is a fundamental result in Fourier analysis. The Cesaro sum is a method of summing infinite series which may not converge in the ordinary sense. This theorem shows that while the Fourier series itself may not converge pointwise, taking Cesaro sums ensures convergence for continuous periodic functions.

### Dependencies
- `FOURIER_FEJER_CESARO_SUMMABLE`
- `REAL_ARITH x = (x + x) / &2`
- `ABSOLUTELY_REAL_INTEGRABLE_CONTINUOUS`
- `REAL_CONTINUOUS_ON_SUBSET`
- `SUBSET_UNIV`
- `REALLIM_ATREAL_WITHINREAL`
- `REAL_CONTINUOUS_ATREAL`
- `REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT`
- `REAL_OPEN_UNIV`
- `IN_UNIV`

### Porting notes (optional)
- The theorem `FOURIER_FEJER_CESARO_SUMMABLE` is the main dependency. Ensure this theorem is ported first.
- The handling of real analysis and limits may differ between proof assistants, so the steps involving `REALLIM_ATREAL_WITHINREAL` and related theorems might need adjustment.
- The Meson calls might require some translation into alternative automated reasoning tactics.


---

