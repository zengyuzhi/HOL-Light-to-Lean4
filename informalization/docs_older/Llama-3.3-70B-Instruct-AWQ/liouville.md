# liouville.ml

## Overview

Number of statements: 22

The `liouville.ml` file formalizes the Liouville approximation theorem, a concept in number theory. It relies on definitions and constructions from the `floor.ml` and `poly.ml` files in the Library. The file's purpose is to provide a formal proof of the Liouville approximation theorem, likely involving the approximation of irrational numbers by rational ones. Its scope includes key definitions, theorems, and constructions related to this theorem, contributing to the broader library of mathematical theories.

## algebraic

### Name of formal statement
algebraic

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let algebraic = new_definition `algebraic(x) <=> ?p. ALL integer p /\ ~(poly p = poly []) /\ poly p x = &0`
```

### Informal statement
A number `x` is algebraic if and only if there exists an integer polynomial `p` such that `p` is not the zero polynomial and `p` evaluated at `x` equals zero.

### Informal sketch
* The definition of `algebraic` involves the existence of an integer polynomial `p` that is not the zero polynomial.
* This polynomial `p` must satisfy the condition that when evaluated at `x`, it equals zero.
* The use of `?p` indicates the existential quantification over polynomials.
* The condition `ALL integer p` ensures that `p` is an integer polynomial, and `~(poly p = poly [])` guarantees that `p` is not the zero polynomial.
* The key step in constructing or proving properties about `algebraic` numbers involves finding or utilizing such polynomials `p` for a given `x`.

### Mathematical insight
The concept of algebraic numbers is fundamental in number theory, representing numbers that are roots of non-constant polynomials with integer coefficients. This definition captures the essence of what it means for a number to be algebraic, emphasizing the relationship between the number and integer polynomials.

### Dependencies
* `poly`
* `integer`

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system represents polynomials and integers, as well as how existential quantification and equality are handled. For example, in Lean, you might use the `∃` symbol for existential quantification, while in Coq, you could use `exists`. Additionally, the representation of polynomials might vary, with some systems requiring explicit definitions of polynomial equality and evaluation.

---

## transcendental

### Name of formal statement
transcendental

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let transcendental = new_definition `transcendental(x) <=> ~(algebraic x)`
```

### Informal statement
The predicate `transcendental(x)` is defined to be true if and only if `x` is not `algebraic`.

### Informal sketch
* The definition of `transcendental(x)` is based on the negation of the `algebraic` property.
* To prove that a number is `transcendental`, one would need to show that it does not satisfy the `algebraic` condition.
* The definition relies on the `algebraic` predicate, which is assumed to be previously defined.

### Mathematical insight
The concept of a `transcendental` number is fundamental in number theory, referring to a number that is not the root of any polynomial equation with rational coefficients. This definition provides a straightforward way to identify such numbers by negating the `algebraic` property.

### Dependencies
* `algebraic`

### Porting notes
When translating this definition to other proof assistants, ensure that the `algebraic` predicate is properly defined and imported. Note that the handling of negation and predicate definitions may vary between systems, so careful attention to the specific syntax and semantics of the target system is required.

---

## REAL_INTEGER_EQ_0

### Name of formal statement
REAL_INTEGER_EQ_0

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let REAL_INTEGER_EQ_0 = prove
 (`!x. integer x /\ abs(x) < &1 ==> x = &0`,
  MESON_TAC[REAL_ABS_INTEGER_LEMMA; REAL_NOT_LE])
```

### Informal statement
For all x, if x is an integer and the absolute value of x is less than 1, then x is equal to 0.

### Informal sketch
* The proof involves assuming `x` is an integer and its absolute value is less than 1.
* It uses the `REAL_ABS_INTEGER_LEMMA` to derive properties about the absolute value of integers.
* The `REAL_NOT_LE` tactic is applied to handle the less-than relation.
* The proof aims to show that under these conditions, `x` must be equal to 0, leveraging properties of integers and absolute values.

### Mathematical insight
This theorem is important because it establishes a basic property relating integers and their absolute values. It's a fundamental step in building more complex arguments involving integers and their comparison, showcasing how certain properties of integers can be derived from basic definitions and axioms.

### Dependencies
#### Theorems
* `REAL_ABS_INTEGER_LEMMA`
* `REAL_NOT_LE`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to how integers and their absolute values are defined and handled. The use of `MESON_TAC` and specific lemmas like `REAL_ABS_INTEGER_LEMMA` and `REAL_NOT_LE` may need to be adapted based on the target system's tactics and libraries for real numbers and integers.

---

## FACT_LE_REFL

### Name of formal statement
FACT_LE_REFL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let FACT_LE_REFL = prove
 (`!n. n <= FACT n`,
  INDUCT_TAC THEN REWRITE_TAC[FACT; ARITH] THEN
  MATCH_MP_TAC(ARITH_RULE `x * 1 <= a ==> x <= a`) THEN
  REWRITE_TAC[LE_MULT_LCANCEL; NOT_SUC; FACT_LT;
              ARITH_RULE `1 <= n <=> 0 < n`])
```

### Informal statement
For all natural numbers n, n is less than or equal to the factorial of n.

### Informal sketch
* The proof starts with an induction over n, using `INDUCT_TAC`.
* The base case and inductive step involve rewriting using the definition of `FACT` and basic arithmetic properties (`REWRITE_TAC[FACT; ARITH]`).
* The `MATCH_MP_TAC` with the rule `x * 1 <= a ==> x <= a` is applied to establish a key inequality.
* Further rewrites are performed using properties such as `LE_MULT_LCANCEL`, `NOT_SUC`, `FACT_LT`, and the arithmetic rule `1 <= n <=> 0 < n` to simplify and conclude the proof.

### Mathematical insight
This theorem establishes a relationship between a number and its factorial, showing that any number is less than or equal to its factorial. This is intuitively true since the factorial of a number grows very rapidly. The theorem is important for various applications in combinatorics and number theory, where such comparisons are crucial.

### Dependencies
* Theorems:
  - `FACT`
  - `ARITH_RULE`
  - `LE_MULT_LCANCEL`
  - `NOT_SUC`
  - `FACT_LT`
* Definitions:
  - `FACT` (factorial function)
* Inductive rules:
  - `INDUCT_TAC` (induction tactic)

### Porting notes
When translating this theorem into another proof assistant like Lean, Coq, or Isabelle, pay special attention to how each system handles induction, arithmetic, and the factorial function. The use of `MATCH_MP_TAC` with a specific rule might need to be adapted based on the target system's tactic language and libraries. Additionally, the arithmetic properties and definitions like `FACT` must be defined or imported appropriately in the target system.

---

## EXP_LE_REFL

### Name of formal statement
EXP_LE_REFL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let EXP_LE_REFL = prove
 (`!a. 1 < a ==> !n. n <= a EXP n`,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC[EXP; ARITH] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
   `n <= x ==> 1 * x < y ==> SUC n <= y`)) THEN
  REWRITE_TAC[LT_MULT_RCANCEL; EXP_EQ_0] THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC)
```

### Informal statement
For all `a`, if `1` is less than `a`, then for all natural numbers `n`, `n` is less than or equal to `a` raised to the power of `n`.

### Informal sketch
* The proof starts by assuming `1 < a` and then proceeds by induction on `n`.
* The base case and inductive step involve rewriting expressions using the definitions of `EXP` and `ARITH`, as well as applying arithmetic rules such as `LT_MULT_RCANCEL` and `EXP_EQ_0`.
* The `MATCH_MP_TAC` and `ARITH_TAC` tactics are used to apply specific arithmetic rules and simplify expressions.
* The overall structure of the proof involves using induction and arithmetic manipulations to establish the inequality `n <= a EXP n` for all `n`.

### Mathematical insight
This theorem provides a bound on the growth rate of the exponential function `EXP` with base `a`, where `a` is greater than `1`. The result is useful in various mathematical contexts, such as analysis and number theory, where exponential growth is a fundamental concept. The theorem's proof illustrates the use of induction and arithmetic manipulations to establish a non-trivial inequality.

### Dependencies
* `EXP`
* `ARITH`
* `LT_MULT_RCANCEL`
* `EXP_EQ_0`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of arithmetic and the `EXP` function. Some systems may require explicit definitions or axioms for these concepts, while others may provide built-in support. Additionally, the use of induction and arithmetic tactics may need to be adapted to the target system's syntax and proof scripting language.

---

## MVT_INEQ

### Name of formal statement
MVT_INEQ

### Type of the formal statement
Theorem

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
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC)
```

### Informal statement
For all functions `f` and `f'` and all real numbers `a`, `d`, and `M`, if `M` is greater than `0`, `d` is greater than `0`, and for all `x` such that the absolute value of `x - a` is less than or equal to `d`, `f` is differentiable at `x` with derivative `f'` and the absolute value of `f'` at `x` is less than `M`, then for all `x` such that the absolute value of `x - a` is less than or equal to `d`, the absolute value of `f(x) - f(a)` is less than `M * d`.

### Informal sketch
* Start by assuming the premises: `0 < M`, `0 < d`, and for all `x` in the interval `[a - d, a + d]`, `f` is differentiable at `x` with `f'(x) < M`.
* Use the `MVT_ALT` theorem, which is an alternate version of the mean value theorem, to establish the existence of a point `z` in the interval `(a, x)` where `f'(z) = (f(x) - f(a)) / (x - a)`.
* Apply the `REAL_LET_TRANS` tactic to establish the inequality `abs(f(x) - f(a)) < M * d` by using the fact that `abs(f'(z)) < M` and `abs(x - a) <= d`.
* The proof involves several cases, including when `x = a`, `x < a`, and `x > a`, which are handled using `DISJ_CASES_THEN` and `ASSUME_TAC`.
* Key HOL Light terms used include `MVT_ALT`, `REAL_ARITH`, `REAL_LET_TRANS`, and `REAL_ABS_SUB`.

### Mathematical insight
The `MVT_INEQ` theorem provides an inequality version of the mean value theorem, which is a fundamental result in calculus. This theorem states that if a function `f` is differentiable on an interval `[a, b]` and `f'(x)` is bounded by `M` on this interval, then the absolute value of the difference quotient `(f(b) - f(a)) / (b - a)` is less than `M`. This result has numerous applications in calculus, including the study of limits, derivatives, and integrals.

### Dependencies
* Theorems:
  + `MVT_ALT`
  + `REAL_ARITH`
  + `REAL_LET_TRANS`
  + `REAL_ABS_SUB`
* Definitions:
  + `diffl` (differentiability)
  + `abs` (absolute value)

### Porting notes
When porting this theorem to other proof assistants, note that the `MVT_ALT` theorem may need to be proved or imported separately. Additionally, the `REAL_ARITH` and `REAL_LET_TRANS` tactics may need to be replaced with equivalent tactics in the target system. The use of `DISJ_CASES_THEN` and `ASSUME_TAC` to handle different cases may also require adaptation to the target system's case analysis and assumption mechanisms.

---

## POLY_MULTIPLE_INTEGER

### Name of formal statement
POLY_MULTIPLE_INTEGER

### Type of the formal statement
Theorem

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
  ASM_SIMP_TAC[INTEGER_CLOSED])
```

### Informal statement
For all polynomials `p`, all integers `q`, and all lists of integers `l`, if all elements of `l` are integers, then the expression `q` raised to the power of the length of `l`, multiplied by the polynomial `p` evaluated at `l` with `p` divided by `q`, is an integer.

### Informal sketch
* The proof starts by considering two cases based on whether `q` is zero or not.
* If `q` is zero, it uses `LIST_INDUCT_TAC` to induct over the list `l`, applying various rewrite rules (`poly`, `REAL_MUL_RZERO`, `INTEGER_CLOSED`, etc.) to simplify the expression.
* If `q` is not zero, it also uses `LIST_INDUCT_TAC` for induction over `l`, and applies several rewrite rules (`poly`, `REAL_MUL_RZERO`, `INTEGER_CLOSED`, etc.) to transform the expression.
* The proof then uses `REAL_ARITH` to manipulate the expression algebraically, followed by `ASM_SIMP_TAC` and `MATCH_MP_TAC` with `INTEGER_CLOSED` to establish that the resulting expression is an integer.
* Key steps involve recognizing the properties of polynomials, integer arithmetic, and the behavior of the `poly` function when evaluated at a list of integers.

### Mathematical insight
This theorem is important because it shows that under certain conditions, a polynomial expression involving integers and rational numbers can be guaranteed to yield an integer result. This has implications for various mathematical constructions and proofs, especially those involving polynomial equations and algebraic manipulations.

### Dependencies
* Theorems:
  + `INTEGER_CLOSED`
* Definitions:
  + `poly`
  + `real_pow`
  + `LENGTH`
* Inductive rules:
  + `LIST_INDUCT_TAC`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to how each system handles polynomial expressions, integer arithmetic, and the properties of rational numbers. Specifically, ensure that the target system's `poly` function or equivalent behaves similarly to the one in HOL Light, and that the necessary arithmetic properties (e.g., `INTEGER_CLOSED`) are available or can be derived. Additionally, the use of `LIST_INDUCT_TAC` and `ASM_CASES_TAC` may need to be adapted based on the target system's support for list induction and case analysis.

---

## SEPARATE_FINITE_SET

### Name of formal statement
SEPARATE_FINITE_SET

### Type of the formal statement
Theorem

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
  ASM_MESON_TAC[REAL_LE_REFL])
```

### Informal statement
For all real numbers `a` and finite sets `s` of real numbers, if `a` is not an element of `s`, then there exists a positive real number `d` such that for all `x` in `s`, `d` is less than or equal to the absolute difference between `x` and `a`.

### Informal sketch
* The proof starts by assuming `a` is not in `s` and `s` is finite.
* It then proceeds by strong induction on the finiteness of `s`, using `FINITE_INDUCT_STRONG`.
* The base case and inductive step involve showing the existence of a positive `d` that satisfies the condition for all `x` in `s`.
* Key steps include using `DE_MORGAN_THM` for handling set operations, `REAL_LT_01` for properties of real numbers, and `REAL_MIN_LE` along with `REAL_ABS_NZ` for reasoning about the minimum distance.
* The `EXISTS_TAC` tactic is used to introduce the witness `min d (abs(x - a))`, which is crucial for satisfying the condition.
* The conclusion is reached by applying `ASM_MESON_TAC` with `REAL_LE_REFL` to finalize the proof.

### Mathematical insight
This theorem is important because it shows that any point not in a finite set of real numbers is surrounded by an open interval that does not contain any points of the set. This is a fundamental property in real analysis, useful for proving separation properties and for constructing functions with specific properties.

### Dependencies
* Theorems:
  - `FINITE_INDUCT_STRONG`
  - `DE_MORGAN_THM`
  - `REAL_LT_01`
  - `REAL_MIN_LE`
  - `REAL_LT_MIN`
  - `GSYM REAL_ABS_NZ`
  - `REAL_SUB_0`
  - `REAL_LE_REFL`
* Definitions:
  - `FINITE`
  - `IN`
  - `abs`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles finite sets, real numbers, and the `min` function. The use of `EXISTS_TAC` to introduce a witness and the application of `ASM_MESON_TAC` for automated reasoning might need to be adapted based on the target system's tactics and automation capabilities. Additionally, ensure that the ported version correctly handles the quantifiers and the absolute value function, as these are crucial to the theorem's statement and proof.

---

## POLY_ROOT_SEPARATE_LE

### Name of formal statement
POLY_ROOT_SEPARATE_LE

### Type of the formal statement
Theorem

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
  REWRITE_TAC[GSYM REAL_ABS_NZ; REAL_SUB_0] THEN MESON_TAC[REAL_NOT_LT])
```

### Informal statement
For all polynomials `p` and real numbers `x`, if `p(x) = 0` and `p` is not the zero polynomial, then there exists a positive real number `d` such that for all real numbers `x'`, if `0 < |x' - x| < d`, then `p(x') ≠ 0`.

### Informal sketch
* The proof starts by assuming `p(x) = 0` and `p` is not the zero polynomial.
* It then applies the `SEPARATE_FINITE_SET` theorem to the set of roots of `p`, excluding `x`, to establish the existence of a separation.
* The proof uses `POLY_ROOTS_FINITE_SET` to recognize that the set of roots of a polynomial is finite.
* It then applies `MONO_EXISTS` to establish the existence of a positive `d` such that for all `x'` within `d` of `x` (but not at `x`), `p(x') ≠ 0`.
* The `REAL_ABS_NZ` and `REAL_SUB_0` theorems are used to handle absolute value and subtraction properties.
* Finally, `REAL_NOT_LT` is applied to conclude the non-zero nature of `p(x')` for `x'` in the specified range.

### Mathematical insight
This theorem provides a key property of polynomials, asserting the existence of a neighborhood around a root where the polynomial does not vanish, except at the root itself. This is crucial for understanding the behavior of polynomials and their roots in real analysis.

### Dependencies
* Theorems:
  + `SEPARATE_FINITE_SET`
  + `POLY_ROOTS_FINITE_SET`
  + `MONO_EXISTS`
  + `REAL_ABS_NZ`
  + `REAL_SUB_0`
  + `REAL_NOT_LT`
* Definitions:
  + `poly`
  + `abs`

### Porting notes
When translating this theorem into other proof assistants, pay special attention to how each system handles real numbers, absolute value, and polynomial roots. The `SEPARATE_FINITE_SET` theorem, in particular, may require careful consideration due to its reliance on finite sets and separation properties, which might be represented differently in other systems. Additionally, the use of `MONO_EXISTS` and other tactics may need to be adapted to the target system's proof scripting language and automation capabilities.

---

## POLY_ROOT_SEPARATE_LT

### Name of formal statement
POLY_ROOT_SEPARATE_LT

### Type of the formal statement
Theorem

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
   `&0 < d ==> &0 < d / &2 /\ (x <= d / &2 ==> x < d)`])
```

### Informal statement
For all polynomials `p` and real numbers `x`, if `p(x)` equals zero and `p` is not the zero polynomial, then there exists a positive real number `d` such that for all real numbers `x'`, if `x'` is within `d` units of `x` (but not equal to `x`), then `p(x')` does not equal zero.

### Informal sketch
* The proof starts by assuming the existence of a polynomial `p` and a real number `x` such that `p(x)` equals zero and `p` is not the zero polynomial.
* It then applies the `POLY_ROOT_SEPARATE_LE` theorem to find a positive real number `d` that satisfies certain properties.
* The proof then selects `d/2` as the desired distance, leveraging `REAL_ARITH` properties to establish the required inequalities and implications.
* Key steps involve using `GEN_TAC`, `DISCH_THEN`, `MATCH_MP`, `X_CHOOSE_THEN`, `EXISTS_TAC`, and `ASM_MESON_TAC` to manage assumptions, apply theorems, and prove the existence of `d`.

### Mathematical insight
This theorem provides a separation property for roots of polynomials, ensuring that if a polynomial has a root at `x`, then there is a neighborhood around `x` where the polynomial does not vanish, unless it is the zero polynomial. This is crucial for understanding the behavior of polynomials around their roots.

### Dependencies
* Theorems:
  + `POLY_ROOT_SEPARATE_LE`
  + `REAL_ARITH`
* Definitions:
  + `poly`

### Porting notes
When translating this theorem into other proof assistants, pay special attention to how each system handles real numbers, polynomials, and the `abs` function. Additionally, the use of `GEN_TAC`, `DISCH_THEN`, and `EXISTS_TAC` may need to be adapted to the target system's tactic language, potentially involving different constructs for assumption management and existential introduction.

---

## POLY_BOUND_INTERVAL

### Name of formal statement
POLY_BOUND_INTERVAL

### Type of the formal statement
Theorem

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
  REAL_ARITH_TAC)
```

### Informal statement
For all polynomials `p`, positive real numbers `d`, and real numbers `x`, there exists a positive real number `M` such that for all real numbers `x'` satisfying `|x' - x| ≤ d`, it holds that `|p(x')| < M`.

### Informal sketch
* The proof starts by assuming the existence of a polynomial `p`, a positive real number `d`, and a real number `x`.
* It then applies the `CONT_BOUNDED_ABS` theorem to `poly p` over the interval `[x - d, x + d]`, which asserts the boundedness of `poly p` over this interval.
* The `POLY_CONT` theorem is used to establish continuity of `poly p`, which is essential for applying `CONT_BOUNDED_ABS`.
* The proof then proceeds to find a suitable `M` that satisfies the condition `|p(x')| < M` for all `x'` in the given interval.
* This involves using `REAL_LET_TRANS` to establish a transitive inequality and `REAL_ARITH_TAC` to perform real arithmetic manipulations.
* Key HOL Light terms involved include `poly`, `CONT_BOUNDED_ABS`, `POLY_CONT`, and `REAL_LET_TRANS`.

### Mathematical insight
This theorem establishes that a polynomial is bounded over any closed interval. This is a fundamental property of polynomials, ensuring that their values remain finite and bounded within a specified range. The proof leverages the continuity of polynomials (`POLY_CONT`) and the boundedness of continuous functions over closed intervals (`CONT_BOUNDED_ABS`).

### Dependencies
* Theorems:
  + `CONT_BOUNDED_ABS`
  + `POLY_CONT`
  + `REAL_LET_TRANS`
* Definitions:
  + `poly`

### Porting notes
When translating this theorem into other proof assistants, pay attention to how each system handles polynomial functions, continuity, and boundedness. Specifically, ensure that the counterpart of `CONT_BOUNDED_ABS` and `POLY_CONT` are properly established in the target system. Additionally, the use of `REAL_LET_TRANS` and `REAL_ARITH_TAC` may need to be adapted based on the target system's support for real arithmetic and transitive inequalities.

---

## LIOUVILLE_INTERVAL

### Name of formal statement
LIOUVILLE_INTERVAL

### Type of the formal statement
Theorem

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
  ASM_REWRITE_TAC[REAL_LT_INV_EQ; REAL_LE_REFL])
```

### Informal statement
For all polynomials `p` and real numbers `x`, if `p(x) = 0` and `p` is not the zero polynomial, then there exists a positive real number `c` such that for all real numbers `x'`, if the absolute difference between `x'` and `x` is less than or equal to `c`, then the absolute value of the polynomial `poly_diff p` evaluated at `x'` is less than `1/c`. Additionally, for all real numbers `x'` such that `0` is less than the absolute difference between `x'` and `x`, which is less than or equal to `c`, `p(x')` is not equal to `0`.

### Informal sketch
* The proof starts by assuming `p(x) = 0` and `p` is not the zero polynomial.
* It then applies the `POLY_ROOT_SEPARATE_LT` theorem to establish a separation between roots.
* The `POLY_BOUND_INTERVAL` theorem is used to find a bound `M` for the polynomial `poly_diff p` in a neighborhood of `x`.
* The proof then constructs `c` as the minimum of `d` (from `POLY_ROOT_SEPARATE_LT`) and `1/M`, ensuring `c` is positive.
* It shows that for any `x'` within `c` distance from `x`, `poly_diff p` evaluated at `x'` is bounded by `1/c`.
* Furthermore, for any `x'` within the same distance but not equal to `x`, `p(x')` is not zero, leveraging the separation established earlier.
* Key tactics involve using `MP_TAC` for modus ponens, `X_CHOOSE_THEN` for existential instantiations, and `MATCH_MP_TAC` for applying theorems like `REAL_LTE_TRANS` and `REAL_LE_INV2`.

### Mathematical insight
This theorem provides a crucial property about the behavior of polynomials and their derivatives around roots, which is fundamental in various areas of mathematics, including algebra, analysis, and geometry. The existence of such an interval `c` around a root `x` of a polynomial `p` (which is not the zero polynomial) ensures that the derivative of `p` is bounded in this interval and that `p` does not have another root in this interval (except possibly at `x` itself). This insight is crucial for understanding the local behavior of polynomials and has implications for root finding algorithms, polynomial factorization, and more.

### Dependencies
* Theorems:
  - `POLY_ROOT_SEPARATE_LT`
  - `POLY_BOUND_INTERVAL`
  - `REAL_LTE_TRANS`
  - `REAL_LE_INV2`
* Definitions:
  - `poly`
  - `poly_diff`
  - `abs`
  - `real_div`
  - `REAL_INV_INV`
  - `REAL_MUL_LID`
  - `REAL_LT_MIN`
  - `REAL_LE_MIN`
  - `REAL_LT_INV_EQ`
  - `REAL_MIN_LE`
  - `REAL_LT_MIN`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, special attention should be paid to how each system handles:
- Polynomial definitions and operations (`poly`, `poly_diff`)
- Real number arithmetic and inequalities
- Existential quantification and choice (`X_CHOOSE_THEN`, `EXISTS_TAC`)
- Tactic applications and their equivalents in the target system.
The theorem's structure, relying on a series of tactic applications to establish the existence of `c` and its properties, suggests that a direct translation of the proof steps may be feasible, but careful consideration of the target system's libraries and tactic language will be necessary.

---

## LIOUVILLE

### Name of formal statement
LIOUVILLE

### Type of the formal statement
Theorem

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
  REWRITE_TAC[REAL_MUL_AC])
```

### Informal statement
For all algebraic numbers `x`, there exists a positive integer `n` and a positive real number `c` such that for all integers `p` and `q` (with `q` not equal to 0), either `x` is equal to the rational number `p/q` or the absolute difference between `x` and `p/q` is greater than `c` divided by `q` raised to the power of `n`.

### Informal sketch
* The proof starts by assuming `x` is an algebraic number and then uses the `LIOUVILLE_INTERVAL` theorem to establish the existence of a list `l` of real numbers and a positive real number `c`.
* It then proceeds to show that there exists an integer `n` (specifically, the length of the list `l`) such that for any integers `p` and `q` (with `q` not equal to 0), either `x` equals `p/q` or the absolute difference between `x` and `p/q` exceeds `c` divided by `q` raised to the power of `n`.
* The proof involves using various mathematical properties and theorems, including `REAL_ARITH`, `REAL_POW_LT`, `REAL_OF_NUM_LT`, `REAL_LE_LDIV_EQ`, and `MVT_INEQ`, to establish the required inequality.
* Key steps include using the `POLY_MULTIPLE_INTEGER` theorem to derive a contradiction and applying the `MATCH_MP_TAC` tactic with `REAL_INTEGER_EQ_0` to conclude the proof.

### Mathematical insight
Liouville's approximation theorem is a fundamental result in number theory, providing a bound on how well algebraic numbers can be approximated by rational numbers. The theorem is crucial in understanding the properties of transcendental numbers and has far-reaching implications in various areas of mathematics, including algebraic geometry and mathematical analysis.

### Dependencies
* Theorems:
  + `LIOUVILLE_INTERVAL`
  + `REAL_ARITH`
  + `POLY_MULTIPLE_INTEGER`
  + `MVT_INEQ`
  + `REAL_INTEGER_EQ_0`
* Definitions:
  + `algebraic`
  + `poly`
  + `poly_diff`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of real numbers, algebraic numbers, and the `LIOUVILLE_INTERVAL` theorem. Ensure that the target system supports the necessary mathematical structures and theorems. Additionally, be mindful of potential differences in tactic scripts and automation, as the proof relies heavily on `MATCH_MP_TAC` and other tactics specific to HOL Light.

---

## LIOUVILLE_IRRATIONAL

### Name of formal statement
LIOUVILLE_IRRATIONAL

### Type of the formal statement
Theorem

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
  ASM_MESON_TAC[LIOUVILLE; REAL_ABS_DIV; REAL_ABS_NUM])
```

### Informal statement
For all x, if x is algebraic and not rational, then there exists a positive integer n and a positive real number c such that for all integers p and q, where q is not zero, the absolute difference between x and the fraction p/q is greater than c divided by q to the power of n.

### Informal sketch
* The proof starts by assuming that x is algebraic and not rational.
* It then applies the `LIOUVILLE` theorem to establish the existence of a positive integer n and a positive real number c.
* The proof uses `REWRITE_TAC` with `RATIONAL_ALT` to rewrite the rationality condition, and `REPEAT STRIP_TAC` to strip away the universal quantifier.
* It then applies `MATCH_MP_TAC` with `LIOUVILLE` to derive the existence of n and c, and `GEN_TAC` to generalize the result.
* The proof also uses `MATCH_MP_TAC` with `MONO_AND` and `REWRITE_TAC` to simplify the expression, and `REPEAT` with `MATCH_MP_TAC` and `MONO_FORALL` to handle the universal quantifier.
* Finally, it uses `ASM_MESON_TAC` with `LIOUVILLE`, `REAL_ABS_DIV`, and `REAL_ABS_NUM` to derive the final result.

### Mathematical insight
This theorem is a corollary of the Liouville theorem, which states that algebraic numbers cannot be approximated too closely by rational numbers. The key idea is that if x is algebraic and not rational, then there exists a positive integer n and a positive real number c such that the absolute difference between x and any rational number p/q is greater than c divided by q to the power of n. This theorem provides a way to measure the "distance" between an algebraic irrational number and the set of rational numbers.

### Dependencies
* Theorems:
  * `LIOUVILLE`
  * `REAL_ABS_DIV`
  * `REAL_ABS_NUM`
* Definitions:
  * `algebraic`
  * `rational`
  * `RATIONAL_ALT`

### Porting notes
When porting this theorem to another proof assistant, note that the `REWRITE_TAC` and `MATCH_MP_TAC` tactics may need to be replaced with equivalent tactics in the target system. Additionally, the `MONO_EXISTS`, `MONO_AND`, and `MONO_FORALL` tactics may need to be replaced with tactics that handle monotonicity and quantifiers in the target system. The `ASM_MESON_TAC` tactic may also need to be replaced with a tactic that handles automatic proof search in the target system.

---

## liouville

### Name of formal statement
liouville

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let liouville = new_definition
`liouville = suminf (\n. &1 / &10 pow (FACT n))`
```

### Informal statement
Liouville's constant is defined as the sum from n = 0 to infinity of 1 divided by 10 to the power of the factorial of n.

### Informal sketch
* The definition of `liouville` involves the `suminf` function, which computes the sum of an infinite series.
* The series is defined by the lambda term `(\n. &1 / &10 pow (FACT n))`, which represents the nth term of the series.
* The `FACT` function computes the factorial of a number, and `pow` is used for exponentiation.
* The definition relies on the `suminf` function being able to handle infinite series and converge to a value.

### Mathematical insight
Liouville's constant is a transcendental number that is defined as the sum of an infinite series. It is a well-known example of a transcendental number, and its definition is often used to illustrate the concept of infinite series and convergence.

### Dependencies
* `suminf`
* `FACT`
* `pow`

### Porting notes
When porting this definition to another proof assistant, note that the `suminf` function may need to be defined or imported separately, and the `FACT` and `pow` functions may have different names or syntax. Additionally, the lambda term `(\n. &1 / &10 pow (FACT n))` may need to be rewritten using the target proof assistant's syntax for anonymous functions.

---

## LIOUVILLE_SUM_BOUND

### Name of formal statement
LIOUVILLE_SUM_BOUND

### Type of the formal statement
Theorem

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
  REWRITE_TAC[GSYM LT_NZ; FACT_LT] THEN ARITH_TAC)
```

### Informal statement
For all non-zero natural numbers `n` and for all natural numbers `d`, the sum from `n` to `n+d` of `1 / 10` raised to the power of the factorial of `k` is less than or equal to `2 / 10` raised to the power of the factorial of `n`.

### Informal sketch
* The proof starts by induction on `d`.
* The base case involves simplifying the sum using `SUM_SING_NUMSEG` and applying `REAL_LE_RMUL` to establish the inequality.
* For the inductive step, the sum is expanded using `SUM_CLAUSES_LEFT` and then manipulated using various arithmetic and real number properties to establish the inductive hypothesis.
* Key steps involve using `MATCH_MP_TAC` with `REAL_ARITH` to apply arithmetic rules, and `SIMP_TAC` to simplify expressions involving real numbers and factorials.
* The proof also relies on properties of factorials, such as `FACT_MONO`, and the `REAL_POW` and `REAL_LE` properties.

### Mathematical insight
This theorem provides a bound on a specific sum involving factorials and powers of 10, which is crucial for establishing convergence properties of certain series. The use of factorials and powers of 10 suggests a connection to the study of rapidly converging series, potentially in the context of analysis or number theory.

### Dependencies
#### Theorems
* `REAL_LE_RMUL`
* `REAL_ARITH`
* `REAL_LE_TRANS`
* `REAL_POW_MONO`
#### Definitions
* `FACT`
* `SUM`
* `REAL_POW`
#### Axioms and Rules
* `INDUCT_TAC`
* `GEN_TAC`
* `DISCH_TAC`
* `MATCH_MP_TAC`
* `SIMP_TAC`
* `CONV_TAC`
* `REWRITE_TAC`

---

## LIOUVILLE_PSUM_BOUND

### Name of formal statement
LIOUVILLE_PSUM_BOUND

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LIOUVILLE_PSUM_BOUND = prove
 (`!n d. ~(n = 0)
         ==> sum(n,d) (\k. &1 / &10 pow FACT k) <= &2 / &10 pow (FACT n)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `d = 0` THEN
  ASM_SIMP_TAC[sum; REAL_LE_DIV; REAL_POW_LE; REAL_POS] THEN
  ASM_SIMP_TAC[PSUM_SUM_NUMSEG] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(d = 0) ==> (n + d) - 1 = n + (d - 1)`] THEN
  ASM_SIMP_TAC[LIOUVILLE_SUM_BOUND])
```

### Informal statement
For all non-zero `n` and all `d`, the sum from `n` to `d` of `1 / 10` raised to the power of the factorial of `k` is less than or equal to `2 / 10` raised to the power of the factorial of `n`.

### Informal sketch
* The proof begins by considering the case when `d` equals `0` and then proceeds with the case when `d` is not equal to `0`.
* It utilizes the `sum` definition, `REAL_LE_DIV`, `REAL_POW_LE`, and `REAL_POS` to simplify the inequality.
* The `PSUM_SUM_NUMSEG` and `ARITH_RULE` are applied to further simplify the expression, specifically handling the arithmetic properties of the sum and the relationship between `n` and `d`.
* Finally, the `LIOUVILLE_SUM_BOUND` is used to establish the desired inequality.

### Mathematical insight
This theorem provides a bound on a specific sum involving factorials and powers of `10`, which is crucial in mathematical analysis, particularly in estimating or bounding certain expressions that arise in the study of functions or sequences. The `LIOUVILLE_SUM_BOUND` suggests a relationship between the sum of terms with factorials in the denominators and a simpler expression involving `2` and the factorial of `n`, indicating a controlled growth rate of the sum as `n` and `d` vary.

### Dependencies
* `sum`
* `REAL_LE_DIV`
* `REAL_POW_LE`
* `REAL_POS`
* `PSUM_SUM_NUMSEG`
* `ARITH_RULE`
* `LIOUVILLE_SUM_BOUND`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles summations, especially with non-standard indexing, and the representation of `REAL` numbers and their properties. The `REPEAT STRIP_TAC` and `ASM_CASES_TAC` tactics may have direct counterparts, but the automation level and the way terms are simplified might differ. The key challenge will be in accurately capturing the arithmetic and real number properties used in the proof.

---

## LIOUVILLE_SUMS

### Name of formal statement
LIOUVILLE_SUMS

### Type of the formal statement
Theorem

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
  REWRITE_TAC[FACT_LE_REFL; LE_EXP; ARITH] THEN SIMP_TAC[EXP_LE_REFL; ARITH])
```

### Informal statement
The series `(\k. &1 / &10 pow FACT k)` converges to `liouville`. This statement asserts the summability of a specific series, which is a crucial property in real analysis.

### Informal sketch
* The proof begins by applying the `REWRITE_TAC` tactic with the `liouville` definition to set up the summability argument.
* It then uses `MATCH_MP_TAC` with `SUMMABLE_SUM` to establish the conditions for the series to converge.
* The `X_GEN_TAC` and `DISCH_TAC` steps introduce and discharge a real number `e` to work with the definition of convergence.
* The `MP_TAC` and `REAL_ARCH_SIMPLE` steps involve choosing a natural number `N` based on the inverse of `e`, which is pivotal in establishing the convergence.
* The proof proceeds with a series of steps involving `EXISTS_TAC`, `CONJ_TAC`, and `MATCH_MP_TAC` to show that the series meets the conditions for convergence, leveraging properties of real numbers and inequalities.
* Key tactics like `REAL_LET_TRANS`, `REAL_LTE_TRANS`, and `LE_TRANS` are used to establish the necessary inequalities and relationships between terms in the series.
* The use of `LIOUVILLE_PSUM_BOUND` and other theorems provides bounds and relationships crucial for proving convergence.

### Mathematical insight
This theorem is significant because it establishes the convergence of a specific series, which is an essential result in real analysis. The series in question is related to the `liouville` constant, and proving its summability has implications for understanding the properties of this constant and its role in mathematical analysis. The proof showcases the use of various tactics and theorems to navigate the complexities of real analysis in a formal setting.

### Dependencies
#### Theorems
* `SUMMABLE_SUM`
* `LIOUVILLE_PSUM_BOUND`
* `REAL_ARCH_SIMPLE`
* `REAL_LET_TRANS`
* `REAL_LTE_TRANS`
* `LE_TRANS`
#### Definitions
* `liouville`
* `FACT`
* `SER_CAUCHY`
* `SUM_POS`
* `REAL_LE_DIV`
* `REAL_POW_LE`
* `REAL_POS`

---

## LIOUVILLE_PSUM_LE

### Name of formal statement
LIOUVILLE_PSUM_LE

### Type of the formal statement
Theorem

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
  SIMP_TAC[SUM_POS; REAL_LE_DIV; REAL_POW_LE; REAL_POS])
```

### Informal statement
For all natural numbers `n`, the sum from `0` to `n` of `1 / 10` raised to the power of the factorial of `k` is less than or equal to `liouville`.

### Informal sketch
* The proof starts by introducing a generic `n` using `GEN_TAC`.
* It then rewrites the sum using `suminf` and applies `MATCH_MP_TAC` with `SEQ_LE` to establish a relationship between the sum and a sequence.
* The proof involves choosing specific functions for `j` and `n` using `EXISTS_TAC`, which are both defined as sums from `0` to `n` of `1 / 10` raised to the power of the factorial of `k`.
* The `REWRITE_TAC` steps simplify the expression using various properties (`SEQ_CONST`, `GSYM sums`, `LIOUVILLE_SUMS`).
* Further simplification involves introducing `n` and a generic `m` using `X_GEN_TAC`, and then applying `SIMP_TAC` with various properties to establish inequalities.
* The final steps involve choosing a `d` and substituting it, followed by further simplifications using properties like `SUM_SPLIT`, `ADD_CLAUSES`, and `REAL_LE_ADDR`, culminating in the application of `SIMP_TAC` with properties like `SUM_POS`, `REAL_LE_DIV`, `REAL_POW_LE`, and `REAL_POS` to conclude the proof.

### Mathematical insight
This theorem is about comparing a partial sum of a series to a constant `liouville`. The series in question involves terms that decrease rapidly due to the factorial in the denominator, which suggests convergence. The theorem is likely part of a larger body of work on series convergence, possibly related to the Liouville function or constants, which are known for their transcendence properties.

### Dependencies
* Theorems:
  - `SEQ_LE`
  - `LIOUVILLE_SUMS`
* Definitions:
  - `liouville`
  - `suminf`
  - `FACT`
* Properties:
  - `SEQ_CONST`
  - `GSYM sums`
  - `SUM_POS`
  - `REAL_LE_DIV`
  - `REAL_POW_LE`
  - `REAL_POS`
  - `SUM_SPLIT`
  - `ADD_CLAUSES`
  - `REAL_LE_ADDR`
  - `GE`
  - `LE_EXISTS`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to how each system handles series, summations, and the properties of real numbers. The use of `GEN_TAC`, `EXISTS_TAC`, and `MATCH_MP_TAC` suggests that the proof involves generic introduction, existential introduction, and application of a previously proven lemma, respectively. These tactics have direct analogs in most proof assistants, but the specific properties and definitions used (like `liouville` and `LIOUVILLE_SUMS`) will need to be defined or imported appropriately. Additionally, the handling of binders and automation may differ, requiring adjustments to the proof script.

---

## LIOUVILLE_PSUM_LT

### Name of formal statement
LIOUVILLE_PSUM_LT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LIOUVILLE_PSUM_LT = prove
 (`!n. sum(0,n) (\k. &1 / &10 pow FACT k) < liouville`,
  GEN_TAC THEN MP_TAC(SPEC `SUC n` LIOUVILLE_PSUM_LE) THEN SIMP_TAC[sum] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < e ==> x + e <= y ==> x < y`) THEN
  SIMP_TAC[REAL_LT_DIV; REAL_POW_LT; REAL_OF_NUM_LT; ARITH])
```

### Informal statement
For all natural numbers `n`, the sum from `0` to `n` of `1` divided by `10` to the power of the factorial of `k` is less than the Liouville constant.

### Informal sketch
* The proof starts by generalizing the statement for an arbitrary natural number `n`.
* It then applies the `LIOUVILLE_PSUM_LE` theorem for `SUC n` (the successor of `n`) to establish a relationship between the sum and the Liouville constant.
* The `SIMP_TAC` tactic is used with the `sum` theorem to simplify the summation.
* The `MATCH_MP_TAC` tactic is applied with a real arithmetic rule to derive a conclusion about the comparison between the sum and the Liouville constant, using the fact that a small positive value (`e`) added to one side of an inequality preserves the inequality if the other side is greater.
* Further simplifications are made using `SIMP_TAC` with various real arithmetic and numerical theorems (`REAL_LT_DIV`, `REAL_POW_LT`, `REAL_OF_NUM_LT`, `ARITH`).

### Mathematical insight
This theorem provides a bound on a partial sum related to the Liouville constant, which is a transcendental number. The Liouville constant is known for being the first proven transcendental number, and such bounds are important in understanding its properties and the properties of similar constants.

### Dependencies
#### Theorems
* `LIOUVILLE_PSUM_LE`
* `REAL_ARITH`
* `REAL_LT_DIV`
* `REAL_POW_LT`
* `REAL_OF_NUM_LT`
* `ARITH`
#### Definitions
* `liouville`
* `sum`
* `FACT` (factorial function)

---

## LIOVILLE_PSUM_DIFF

### Name of formal statement
LIOVILLE_PSUM_DIFF

### Type of the formal statement
Theorem

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
  ASM_SIMP_TAC[ADD_CLAUSES; LIOUVILLE_PSUM_BOUND])
```

### Informal statement
For all non-zero natural numbers $n$, the Liouville constant is less than or equal to the sum from $0$ to $n$ of $1/10$ raised to the power of the factorial of $k$, plus $2/10$ raised to the power of the factorial of $n$.

### Informal sketch
* The proof starts by assuming a non-zero natural number $n$ and aims to establish the inequality involving the Liouville constant.
* It uses the `MATCH_MP_TAC SEQ_LE` tactic to apply a sequence lemma, which involves finding a sequence that satisfies certain properties.
* The proof then uses `EXISTS_TAC` to introduce specific sequences that will be used to bound the Liouville constant.
* The `REWRITE_TAC` steps apply various simplifications and identities, including `SEQ_CONST`, `GSYM sums`, and `LIOUVILLE_SUMS`, to transform the expression and prepare for the final inequality.
* The `EXISTS_TAC` and `X_GEN_TAC` steps introduce additional variables and perform case analysis to handle different values of $n$.
* The `DISCH_THEN` and `SUBST_ALL_TAC` steps are used to discharge assumptions and substitute values, leading to the final simplification using `ASM_SIMP_TAC` and `LIOUVILLE_PSUM_BOUND`.

### Mathematical insight
This theorem provides a bound on the Liouville constant, which is a well-known transcendental number. The proof involves constructing a sequence of rational numbers that converges to the Liouville constant and using properties of this sequence to establish the bound. The Liouville constant is important in number theory, particularly in the study of transcendental numbers.

### Dependencies
* `SEQ_LE`
* `LIOUVILLE_SUMS`
* `LIOUVILLE_PSUM_BOUND`
* `SEQ_CONST`
* `GSYM sums`
* `FACT` (factorial function)
* `liouville` (Liouville constant)

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of sequences, series, and limits. The `EXISTS_TAC` and `MATCH_MP_TAC` tactics may need to be replaced with equivalent constructs in the target system. Additionally, the `REWRITE_TAC` steps may require manual rewriting or the use of automated rewriting tools. The `LIOUVILLE_PSUM_BOUND` theorem, which is used in the final simplification, may need to be ported separately or re-proved in the target system.

---

## TRANSCENDENTAL_LIOUVILLE

### Name of formal statement
TRANSCENDENTAL_LIOUVILLE

### Type of the formal statement
Theorem

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
  REWRITE_TAC[FACT_LT; ARITH_RULE `1 <= x <=> 0 < x`])
```

### Informal statement
The theorem `TRANSCENDENTAL_LIOUVILLE` states that the `liouville` function is transcendental. This involves proving that for any non-zero real number `c` and any positive integer `m`, there exists a positive integer `n` such that a specific sum involving `n` and `c` satisfies certain inequalities, ultimately leading to the conclusion that `liouville` cannot be expressed as a root of a polynomial with rational coefficients.

### Informal sketch
* The proof starts by assuming the existence of a real number `c` and a positive integer `m` such that `liouville` is algebraic.
* It then applies various rewriting and simplification steps, including `REWRITE_TAC` and `DISCH_THEN`, to transform the expression and prepare for further reasoning.
* The proof introduces a new variable `k` and uses `X_CHOOSE_TAC` to select a suitable value, followed by the definition of `n` in terms of `m` and `k`.
* The main body of the proof involves a series of manipulations and applications of mathematical properties, including `REAL_ARCH_POW`, `PSUM_SUM_NUMSEG`, and `LIOUVILLE_PSUM_LT`, to establish the required inequalities.
* Key steps include the use of `SUBGOAL_THEN` to establish a specific equality, and `MATCH_MP_TAC` to apply relevant theorems such as `REAL_ARITH` and `REAL_LE_TRANS`.
* The proof concludes by applying `LE_MULT2` and `FACT_LT` to finalize the argument.

### Mathematical insight
The `TRANSCENDENTAL_LIOUVILLE` theorem is significant because it establishes the transcendence of the `liouville` function, which is a fundamental result in number theory. The proof relies on careful manipulation of inequalities and the properties of real numbers, as well as the application of specific theorems such as `LIOUVILLE_PSUM_LT`. The use of `liouville` as a counterexample to algebraicity is a key insight, as it allows the proof to proceed by contradiction.

### Dependencies
* Theorems:
	+ `LIOUVILLE`
	+ `REAL_ARCH_POW`
	+ `PSUM_SUM_NUMSEG`
	+ `LIOUVILLE_PSUM_LT`
	+ `REAL_ARITH`
	+ `REAL_LE_TRANS`
	+ `LE_MULT2`
	+ `FACT_LT`
* Definitions:
	+ `liouville`
	+ `transcendental`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to preserve the precise logical structure and quantifier scope. The use of `SUBGOAL_THEN` and `MATCH_MP_TAC` may require special attention, as these tactics can be sensitive to the specific proof assistant's handling of subgoals and theorem application. Additionally, the `REAL_ARCH_POW` and `PSUM_SUM_NUMSEG` theorems may need to be reformulated or replaced with equivalent results in the target system.

---

