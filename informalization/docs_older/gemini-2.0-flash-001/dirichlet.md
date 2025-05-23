# dirichlet.ml

## Overview

Number of statements: 73

`dirichlet.ml` formalizes Dirichlet's theorem on arithmetic progressions within HOL Light. It relies on imports for products, AGM, transcendentals, Pocklington's criterion, multiplicative functions, and the Mangoldt function. The file likely contains definitions and theorems related to proving the infinitude of primes in arithmetic progressions of the form *a + nd* where *a* and *d* are coprime.


## VSUM_VSUM_DIVISORS

### Name of formal statement
VSUM_VSUM_DIVISORS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VSUM_VSUM_DIVISORS = prove
 (`!f x. vsum (1..x) (\n. vsum {d | d divides n} (f n)) =
         vsum (1..x) (\n. vsum (1..(x DIV n)) (\k. f (k * n) n))`,
  SIMP_TAC[VSUM; FINITE_DIVISORS; LE_1] THEN
  SIMP_TAC[VSUM; FINITE_NUMSEG; ITERATE_ITERATE_DIVISORS;
           MONOIDAL_VECTOR_ADD]);;
```

### Informal statement
For any function `f` from natural numbers to a monoid and any natural number `x`, the sum of `f(n)` over all natural numbers `n` from 1 to `x`, where each `f(n)` is summed over all divisors `d` of `n`, is equal to the sum of `f(k * n)` over all natural numbers `n` from 1 to `x`, where each `f(k * n)` is summed over all natural numbers `k` from 1 to `x DIV n`.

### Informal sketch
The proof proceeds by rewriting the left-hand side using basic properties of summation and divisors.

- Start with the left-hand side: `vsum (1..x) (\n. vsum {d | d divides n} (f n))`.
- Rewrite using `FINITE_DIVISORS` to show that the set of divisors is finite.
- Rewrite using `LE_1`.
- Use `ITERATE_ITERATE_DIVISORS` to transform the summation over divisors of `n` into a double summation over `n` and `k` such that `k * n` ranges from `1` to `x`.
- Use `MONOIDAL_VECTOR_ADD` to rearrange the summations.

### Mathematical insight
This theorem provides a way to rearrange a double summation involving divisors. It's a specific instance of a more general class of identities for multiplicative functions in number theory. In essence, it states that summing over divisors of each number up to `x` is equivalent to summing over all pairs `(n, k)` such that their product `n * k` is less than or equal to `x`. This rearrangement is useful in various number-theoretic arguments, especially when dealing with divisor sums.

### Dependencies
- `VSUM`
- `FINITE_DIVISORS`
- `LE_1`
- `FINITE_NUMSEG`
- `ITERATE_ITERATE_DIVISORS`
- `MONOIDAL_VECTOR_ADD`


---

## REAL_EXP_1_LE_4

### Name of formal statement
REAL_EXP_1_LE_4

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_EXP_1_LE_4 = prove
 (`exp(&1) <= &4`,
  ONCE_REWRITE_TAC[ARITH_RULE `&1 = &1 / &2 + &1 / &2`; REAL_EXP_ADD] THEN
  REWRITE_TAC[REAL_ARITH `&4 = &2 * &2`; REAL_EXP_ADD] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
  MP_TAC(SPEC `&1 / &2` REAL_EXP_BOUND_LEMMA) THEN REAL_ARITH_TAC);;
```
### Informal statement
The exponential of 1 is less than or equal to 4: exp(1) <= 4.

### Informal sketch
The proof demonstrates that `exp(1)` is less than or equal to 4.
- First, the proof rewrites `&1` as `&1 / &2 + &1 / &2` and applies the theorem `REAL_EXP_ADD` to rewrite `exp(&1)` as `exp(&1 / &2 + &1 / &2)` to `exp(&1 / &2) * exp(&1 / &2)`. 
- The theorem rewrites `&4` as `&2 * &2` and applies theorem `REAL_EXP_ADD` to rewrite `exp(&1)` to `exp(&1 / &2) * exp(&1 / &2)`.
- Then, it uses `REAL_LE_MUL2` with `REAL_EXP_POS_LE`. 
- Then, it applies `REAL_EXP_BOUND_LEMMA` with `&1 / &2`.
- Finally, it uses `REAL_ARITH_TAC` to complete the arithmetic reasoning.

### Mathematical insight
This theorem provides a useful upper bound for the exponential function evaluated at 1. It's a simple but important estimate that can be used in real analysis.

### Dependencies
- `ARITH_RULE`
- `REAL_EXP_ADD`
- `REAL_ARITH`
- `REAL_LE_MUL2`
- `REAL_EXP_POS_LE`
- `REAL_EXP_BOUND_LEMMA`


---

## DECREASING_LOG_OVER_N

### Name of formal statement
DECREASING_LOG_OVER_N

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DECREASING_LOG_OVER_N = prove
 (`!n. 4 <= n ==> log(&n + &1) / (&n + &1) <= log(&n) / &n`,
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. clog z / z`; `\z. (Cx(&1) - clog(z)) / z pow 2`;
                 `Cx(&n)`; `Cx(&n + &1)`] COMPLEX_MVT_LINE) THEN
  REWRITE_TAC[IN_SEGMENT_CX_GEN] THEN
  REWRITE_TAC[REAL_ARITH `~(n + &1 <= x /\ x <= n)`] THEN ANTS_TAC THENL
   [X_GEN_TAC `w:complex` THEN STRIP_TAC THEN COMPLEX_DIFF_TAC THEN
    SUBGOAL_THEN `&0 < Re w` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `w = Cx(&0)` THEN ASM_SIMP_TAC[RE_CX; REAL_LT_REFL] THEN
    DISCH_TAC THEN UNDISCH_TAC `~(w = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD;
    DISCH_THEN(X_CHOOSE_THEN `z:complex`
     (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    SUBGOAL_THEN `&0 < &n /\ &0 < &n + &1` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM CX_LOG; GSYM CX_DIV; RE_CX; GSYM CX_SUB] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= --x ==> a - b = x ==> a <= b`) THEN
    REWRITE_TAC[RE_MUL_CX; GSYM REAL_MUL_LNEG] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `?u. z = Cx(u)` (CHOOSE_THEN SUBST_ALL_TAC) THENL
     [ASM_MESON_TAC[REAL; real]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IM_CX; RE_CX]) THEN
    UNDISCH_THEN `T` (K ALL_TAC) THEN
    SUBGOAL_THEN `&0 < u` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM CX_LOG; GSYM CX_SUB; GSYM CX_POW; GSYM CX_DIV; RE_CX;
      real_div; GSYM REAL_MUL_LNEG; REAL_NEG_SUB; GSYM REAL_POW_INV] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE] THEN
    REWRITE_TAC[REAL_SUB_LE] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    MP_TAC REAL_EXP_1_LE_4 THEN ASM_REAL_ARITH_TAC]);;
```

### Informal statement
For all natural numbers `n`, if `4 <= n`, then `log(n + 1) / (n + 1) <= log(n) / n`.

### Informal sketch
The proof demonstrates that the function `log(x) / x` is decreasing for `x >= 4`.
- Use the Mean Value Theorem (`COMPLEX_MVT_LINE`) on the complex-valued function `clog z / z` to relate the difference in function values to the derivative at an intermediate point. The derivative is `(1 - clog(z)) / z^2`.
- Show that the given segment is valid. This involves showing `~(n + 1 <= x /\ x <= n)`, which is trivially true.
- Prove that `Re w > 0`, where `w` is the intermediate point provided by the Mean Value Theorem. This involves case splitting on `w = Cx(&0)` (i.e. `w` is the complex number zero).
- Apply choose to select a real number `u` such that `z = Cx(u)`.
- Show that `0 < n` and `0 < n + 1`, which follows from `4 <= n`.
- Simplify using `CX_LOG`, `CX_DIV`, `RE_CX`, `CX_SUB` to express the real part of complex arithmetic.
- Deduce `0 <= -(x)` implies `a - b = x` implies `a <= b`.
- Rearrange and apply the inequality `REAL_LE_MUL`.
- Prove that `0 < u`.
- Simplify the resulting expression involving logarithms and exponentials using standard identities and inequalities. This involves showing `exp(1) <= 4` and applying the monotonicity of the exponential function and the logarithm function. Finally, real arithmetic is used to conclude the proof.

### Mathematical insight
This theorem establishes that the sequence `log(n) / n` is decreasing for `n >= 4`. This is a standard result in real analysis and is often useful for bounding sums and estimating the growth rate of functions. This fact is relevant across a variety of analysis theorems, especially in areas of convergence analysis.

### Dependencies
- `REAL_OF_NUM_LE`
- `COMPLEX_MVT_LINE`
- `IN_SEGMENT_CX_GEN`
- `RE_CX`
- `CX_LOG`
- `CX_DIV`
- `CX_SUB`
- `RE_MUL_CX`
- `REAL_LE_MUL`
- `REAL`
- `IM_CX`
- `real_div`
- `REAL_MUL_LNEG`
- `REAL_NEG_SUB`
- `REAL_POW_INV`
- `REAL_POW_2`
- `REAL_LE_SQUARE`
- `REAL_SUB_LE`
- `LOG_EXP`
- `LOG_MONO_LE_IMP`
- `REAL_EXP_POS_LT`
- `REAL_EXP_1_LE_4`

### Porting notes (optional)
- The proof relies heavily on the Mean Value Theorem for complex functions, and the corresponding definitions and theorems should be available or provable in the target proof assistant.
- The proof also makes extensive use of real arithmetic, so a good real number theory library is required.
- The tactics used in HOL Light, such as `ASM_REAL_ARITH_TAC`, indicate a reliance on automated reasoning for real arithmetic. Ensure that the target proof assistant has similar capabilities.


---

## EXISTS_COMPLEX_ROOT_NONTRIVIAL

### Name of formal statement
EXISTS_COMPLEX_ROOT_NONTRIVIAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EXISTS_COMPLEX_ROOT_NONTRIVIAL = prove
 (`!a n. 2 <= n ==> ?z. z pow n = a /\ ~(z = Cx(&1))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP(ARITH_RULE `2 <= n ==> ~(n = 0)`)) THEN
  ASM_CASES_TAC  `a = Cx(&0)` THENL
   [EXISTS_TAC `Cx(&0)` THEN ASM_REWRITE_TAC[COMPLEX_POW_ZERO] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  ASM_CASES_TAC `a = Cx(&1)` THENL
   [EXISTS_TAC `cexp(Cx(&2) * Cx pi * ii * Cx(&1 / &n))` THEN
    ASM_SIMP_TAC[COMPLEX_ROOT_UNITY_EQ_1; DIVIDES_ONE;
                 ARITH_RULE `2 <= n ==> ~(n = 1)`; COMPLEX_ROOT_UNITY];
    MATCH_MP_TAC(MESON[]
     `(!x. ~Q x ==> ~P x) /\ (?x. P x) ==> (?x. P x /\ Q x)`) THEN
    ASM_SIMP_TAC[COMPLEX_POW_ONE] THEN EXISTS_TAC `cexp(clog a / Cx(&n))` THEN
    ASM_SIMP_TAC[GSYM CEXP_N; COMPLEX_DIV_LMUL; CX_INJ; REAL_OF_NUM_EQ] THEN
    ASM_SIMP_TAC[CEXP_CLOG]]);;
```
### Informal statement
For all complex numbers `a` and natural numbers `n` such that `2 <= n`, there exists a complex number `z` such that `z` to the power of `n` equals `a`, and `z` is not equal to `Cx(&1)`.

### Informal sketch
The theorem states that for any complex number `a` and any natural number `n` greater than or equal to 2, there exists a complex nth root of `a` which is not equal to 1.

- The proof proceeds by considering two cases for `a`: `a = Cx(&0)` and `a = Cx(&1)`.
- If `a = Cx(&0)`, then `z = Cx(&0)` is a solution because `Cx(&0)` to the power `n` is `Cx(&0)` (using `COMPLEX_POW_ZERO`). Also `Cx(&0)` is not equal to `Cx(&1)`.
- If `a != Cx(&0)`, the proof then considers the case where `a = Cx(&1)`. In this subcase, `z = cexp(Cx(&2) * Cx pi * ii * Cx(&1 / &n))` is taken as a solution. This is derived exploiting `COMPLEX_ROOT_UNITY_EQ_1`, `DIVIDES_ONE`, `ARITH_RULE 2 <= n ==> ~(n = 1)` and `COMPLEX_ROOT_UNITY`. An additional assertion is made using the MESON tactic to ensure that `z` is not equal to `Cx(&1)`.
- The final subcase handled is when `a` is not equal to `Cx(&0)` and not equal to `Cx(&1)`. Then `z = cexp(clog a / Cx(&n))` is chosen. The proof simplifies and expands this choice using `CEXP_N`, `COMPLEX_DIV_LMUL`, `CX_INJ`, `REAL_OF_NUM_EQ`, and `CEXP_CLOG` to show that this definition of `z` indeed satisfies the required properties.

### Mathematical insight
This theorem establishes the existence of a complex nth root for any complex number, provided `n >= 2`, excluding the trivial root `Cx(&1)`. The proof demonstrates a constructive approach to finding such a root, either by setting the root to zero when the input is zero, by using roots of unity when the input is unity, or by using the complex exponential and logarithm functions when the input is neither. This result is important for building the complex number system and ensuring that complex numbers can complete algebraic operations like nth roots.

### Dependencies
- `COMPLEX_POW_ZERO `
- `COMPLEX_ROOT_UNITY_EQ_1`
- `DIVIDES_ONE`
- `ARITH_RULE 2 <= n ==> ~(n = 1)`
- `COMPLEX_ROOT_UNITY`
- `MESON[] (!x. ~Q x ==> ~P x) /\ (?x. P x) ==> (?x. P x /\ Q x)`
- `COMPLEX_POW_ONE`
- `GSYM CEXP_N`
- `COMPLEX_DIV_LMUL`
- `CX_INJ`
- `REAL_OF_NUM_EQ`
- `CEXP_CLOG`
- `ARITH_RULE 2 <= n ==> ~(n = 0)`


---

## dirichlet_character

### Name of formal statement
- dirichlet_character

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let dirichlet_character = new_definition
 `dirichlet_character d (c:num->complex) <=>
        (!n. c(n + d) = c(n)) /\
        (!n. c(n) = Cx(&0) <=> ~coprime(n,d)) /\
        (!m n. c(m * n) = c(m) * c(n))`;;
```
### Informal statement
- The predicate `dirichlet_character d c` holds if and only if the complex-valued function `c`, indexed by natural numbers, satisfies the following three conditions:
    - For all natural numbers `n`, `c(n + d) = c(n)`.
    - For all natural numbers `n`, `c(n)` equals the complex number `0` if and only if `n` is not coprime to `d`.
    - For all natural numbers `m` and `n`, `c(m * n) = c(m) * c(n)`.

### Informal sketch
- The definition introduces the notion of a Dirichlet character modulo `d`, represented by the predicate `dirichlet_character d c`. The proof ensures that `dirichlet_character d c` holds precisely when the function `c` has the specified properties.
    - The first condition, `!n. c(n + d) = c(n)`, enforces periodicity.
    - The second condition, `!n. c(n) = Cx(&0) <=> ~coprime(n,d)`, restricts the values of `c` to zero based on the coprimality of `n` and `d`.
    - The third condition, `!m n. c(m * n) = c(m) * c(n)`, imposes a multiplicative property.

### Mathematical insight
- The definition captures the essence of a Dirichlet character, a crucial concept in number theory. Dirichlet characters are complex-valued functions that are periodic, multiplicative, and related to the coprimality of integers. They are used extensively in analytic number theory to study the distribution of prime numbers and other arithmetic properties. The conditions imposed by the definition arise naturally from the properties required for a function to be considered a Dirichlet character.

### Dependencies
- `coprime`


---

## DIRICHLET_CHARACTER_PERIODIC

### Name of formal statement
DIRICHLET_CHARACTER_PERIODIC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_PERIODIC = prove
 (`!d c n. dirichlet_character d c ==> c(n + d) = c(n)`,
  SIMP_TAC[dirichlet_character]);;
```
### Informal statement
For all natural numbers `d`, `c`, and `n`, if `c` is a Dirichlet character modulo `d`, then `c(n + d) = c(n)`.

### Informal sketch
The proof relies on the definition of `dirichlet_character`.

- The hypothesis `dirichlet_character d c` is expanded using the definition `dirichlet_character`.
- The definition `dirichlet_character` asserts that `c` is periodic with period `d`.
- Therefore, `c(n + d) = c(n)`.

### Mathematical insight
This theorem states the periodicity property of Dirichlet characters. A Dirichlet character modulo `d` is a function that is periodic with period `d`. This is a fundamental property used extensively in number theory, particularly in the study of L-functions and the distribution of prime numbers.

### Dependencies
- Definition: `dirichlet_character`

### Porting notes (optional)
The main challenge in porting this theorem lies in ensuring that the definition of `dirichlet_character` is accurately represented in the target proof assistant. The periodicity property might also require some adaptation depending on how modular arithmetic is handled in the target system.


---

## DIRICHLET_CHARACTER_EQ_0

### Name of formal statement
DIRICHLET_CHARACTER_EQ_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_EQ_0 = prove
 (`!d c n. dirichlet_character d c ==> (c(n) = Cx(&0) <=> ~coprime(n,d))`,
  SIMP_TAC[dirichlet_character]);;
```

### Informal statement
For all natural number `d` and all functions `c` from natural numbers to complex numbers, if `c` is a Dirichlet character with modulus `d`, then for all natural numbers `n`, `c(n)` is equal to the complex number 0 if and only if `n` and `d` are not coprime.

### Informal sketch
The proof relies on the definition of `dirichlet_character`.

- Expand the definition `dirichlet_character d c` using `SIMP_TAC [dirichlet_character]`. This unfolds the conjunction of conditions that `c` must satisfy, including periodicity modulo `d` and being zero if and only if not coprime with `d`.
- The goal becomes trivial because the definition of `dirichlet_character` explicitly states that `c(n) = Cx(&0)` if and only if `~coprime(n, d)`.

### Mathematical insight
This theorem formalizes a fundamental property of Dirichlet characters: a Dirichlet character `c` modulo `d` vanishes (takes the value 0) at an integer `n` if and only if `n` and `d` share a common factor (i.e., are not coprime). This is a core aspect of their definition and significance in number theory.

### Dependencies
- Definitions: `dirichlet_character`


---

## DIRICHLET_CHARACTER_MUL

### Name of formal statement
DIRICHLET_CHARACTER_MUL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_MUL = prove
 (`!d c m n. dirichlet_character d c ==> c(m * n) = c(m) * c(n)`,
  SIMP_TAC[dirichlet_character]);;
```
### Informal statement
For all natural numbers `d`, `m`, and `n`, and for all functions `c` from natural numbers to complex numbers, if `c` is a Dirichlet character modulo `d`, then `c(m * n) = c(m) * c(n)`.

### Informal sketch
The proof uses the tactic `SIMP_TAC` with the definition `dirichlet_character`. This expands the definition of `dirichlet_character d c` and simplifies the equation `c(m * n) = c(m) * c(n)` using the properties that define a Dirichlet character. The critical elements in the definition used will be that `c` is multiplicative and that `c(n)` is zero when `gcd(n, d)` is not one.

### Mathematical insight
This theorem states that a Dirichlet character is a completely multiplicative function. This is a fundamental property of Dirichlet characters and reflects the underlying multiplicative structure of integers modulo `d`.

### Dependencies
- Definitions:
  - `dirichlet_character`


---

## DIRICHLET_CHARACTER_EQ_1

### Name of formal statement
DIRICHLET_CHARACTER_EQ_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_EQ_1 = prove
 (`!d c. dirichlet_character d c ==> c(1) = Cx(&1)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIRICHLET_CHARACTER_MUL) THEN
  DISCH_THEN(MP_TAC o repeat (SPEC `1`)) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[COMPLEX_FIELD `a = a * a <=> a = Cx(&0) \/ a = Cx(&1)`] THEN
  ASM_SIMP_TAC[DIRICHLET_CHARACTER_EQ_0] THEN
  MESON_TAC[COPRIME_1; COPRIME_SYM]);;
```

### Informal statement
For all `d` and `c`, if `c` is a Dirichlet character modulo `d`, then `c(1)` is equal to the complex number `1`.

### Informal sketch
The proof proceeds as follows:
- Assume that `c` is a Dirichlet character modulo `d`.
- Use the property of Dirichlet characters that `c(x * y) = c(x) * c(y)` (accessed via `DIRICHLET_CHARACTER_MUL`). Instantiate this with `x = 1` and `y = 1` to obtain `c(1 * 1) = c(1) * c(1)`, or equivalently, `c(1) = c(1) * c(1)`. This reduces to showing that `c(1)` is either `0` or `1`.
- Rewrite the equation `c(1) = c(1) * c(1)` as `c(1) = 0 \/ c(1) = 1` in the complex field.
- Using `DIRICHLET_CHARACTER_EQ_0`, if `gcd(n,d) != 1`, then `c(n) = 0`. Since `gcd(1,d) = 1` (using `COPRIME_1` and `COPRIME_SYM`), `c(1)` cannot be `0`, therefore it must be `1`.

### Mathematical insight
This theorem states a fundamental property of Dirichlet characters: the value of a Dirichlet character at 1 must always be 1. This reflects the multiplicative identity property inherent in the definition of a character.

### Dependencies
- `DIRICHLET_CHARACTER_MUL`
- `COMPLEX_FIELD`
- `DIRICHLET_CHARACTER_EQ_0`
- `COPRIME_1`
- `COPRIME_SYM`


---

## DIRICHLET_CHARACTER_POW

### Name of formal statement
DIRICHLET_CHARACTER_POW

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_POW = prove
 (`!d c m n. dirichlet_character d c ==> c(m EXP n) = c(m) pow n`,
  REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[EXP; complex_pow] THENL
   [ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_1]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_MUL th]) THEN
  ASM_REWRITE_TAC[]);;
```
### Informal statement
For all natural numbers `d`, all functions `c` from natural numbers to complex numbers, and all natural numbers `m` and `n`, if `c` is a Dirichlet character modulo `d`, then `c(m^n) = c(m)^n`.

### Informal sketch
The proof proceeds by induction on `n`.

- The base case, when `n = 0`, follows from the fact that `m^0 = 1` and the definition of a `dirichlet_character` which implies that `c(1) = 1`.
- The inductive step assumes that `c(m^n) = c(m)^n` and proves that `c(m^(n+1)) = c(m)^(n+1)`.
- This is shown by rewriting `c(m^(n+1))` as `c(m^n * m)`, then using the fact that `c` is a `dirichlet_character` (specifically, `DIRICHLET_CHARACTER_MUL`) to rewrite this as `c(m^n) * c(m)`.
- Finally, the induction hypothesis `c(m^n) = c(m)^n` is used to conclude that `c(m^n) * c(m) = c(m)^n * c(m) = c(m)^(n+1)`.

### Mathematical insight
This theorem states that a Dirichlet character preserves exponentiation; i.e., the value of the character at a number raised to a power is equal to the value of the character at the number, raised to that same power. This is an important property for reasoning about Dirichlet characters in number theory, as it allows one to relate the values of the character at different arguments in a simple way.

### Dependencies
- `DIRICHLET_CHARACTER_EQ_1`
- `DIRICHLET_CHARACTER_MUL`
- `EXP`
- `complex_pow`

### Porting notes (optional)
The usage of tactics such as `ASM_MESON_TAC` indicates the reliance on automated reasoning capabilities to discharge certain goals related to the properties of a Dirichlet character, and these inferences might need to be explicitly provided to proof assistants with weaker automation. The complex power function `complex_pow` may require a specific library or definition in the target proof assistant.


---

## DIRICHLET_CHARACTER_PERIODIC_GEN

### Name of formal statement
DIRICHLET_CHARACTER_PERIODIC_GEN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_PERIODIC_GEN = prove
 (`!d c m n. dirichlet_character d c ==> c(m * d + n) = c(n)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  GEN_TAC THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
  ONCE_REWRITE_TAC[ARITH_RULE `(mk + d) + n:num = (mk + n) + d`] THEN
  ASM_SIMP_TAC[DIRICHLET_CHARACTER_PERIODIC]);;
```

### Informal statement
For all natural numbers `d`, `c`, `m`, and `n`, if `c` is a Dirichlet character modulo `d`, then `c(m * d + n) = c(n)`.

### Informal sketch
The proof proceeds by induction on `m`.
- The base case `m = 0` follows directly.
- For the inductive step, we assume `c(m * d + n) = c(n)` and need to show `c((m + 1) * d + n) = c(n)`.  We rewrite `(m + 1) * d + n` as `m * d + d + n`, and then as `m * d + n + d`.
- We use the property that `c` is a Dirichlet character, which means that `c(x + d) = c(x)` for all `x`.
- Finally, by applying the induction hypothesis `c(m * d + n) = c(n)`, we conclude that `c(m * d + n + d) = c(n)`.

### Mathematical insight
This theorem states a fundamental property of Dirichlet characters: they are periodic with period equal to the modulus. This is a crucial property used throughout the theory of Dirichlet characters and L-functions.  It expresses the fact that the value of the character only depends on its argument modulo `d`.

### Dependencies
- Theorem: `RIGHT_FORALL_IMP_THM`
- Theorem: `DIRICHLET_CHARACTER_PERIODIC`
- Theorems involving arithmetic:
  - `ADD_CLAUSES`
  - `MULT_CLAUSES`

### Porting notes (optional)
The success of the proof rests on efficient rewriting and simplification, especially using the properties of a `dirichlet_character`. Ensure that the target proof assistant has similar capabilities for handling rewriting and simplification with assumptions. Also, the arithmetic rewriting might require some adjustment depending on how arithmetic is handled.


---

## DIRICHLET_CHARACTER_CONG

### Name of formal statement
DIRICHLET_CHARACTER_CONG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_CONG = prove
 (`!d c m n.
        dirichlet_character d c /\ (m == n) (mod d) ==> c(m) = c(n)`,
  REWRITE_TAC[CONG_CASES] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[DIRICHLET_CHARACTER_PERIODIC_GEN]);;
```
### Informal statement
For all `d`, `c`, `m`, and `n`, if `c` is a Dirichlet character modulo `d` and `m` is congruent to `n` modulo `d`, then `c(m)` equals `c(n)`.

### Informal sketch
The proof proceeds as follows:
- Start by applying `CONG_CASES`.
- Repeatedly strip the quantifiers and implications using `STRIP_TAC`.
- Use `DIRICHLET_CHARACTER_PERIODIC_GEN` together with assumption list simplification to complete the proof. This relies on the periodic property of Dirichlet characters and the congruence relation.

### Mathematical insight
This theorem states that Dirichlet characters are well-defined on congruence classes modulo their modulus. This is a fundamental property used extensively in number theory, especially in the study of L-functions and the distribution of primes in arithmetic progressions. A Dirichlet character takes the same value for all integers within the same congruence class modulo `d`.

### Dependencies
- Definitions:
    - `dirichlet_character`
- Theorems:
    - `CONG_CASES`
    - `DIRICHLET_CHARACTER_PERIODIC_GEN`


---

## DIRICHLET_CHARACTER_ROOT

### Name of formal statement
DIRICHLET_CHARACTER_ROOT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_ROOT = prove
 (`!d c n. dirichlet_character d c /\ coprime(d,n)
           ==> c(n) pow phi(d) = Cx(&1)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o GSYM o MATCH_MP DIRICHLET_CHARACTER_EQ_1) THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[GSYM(MATCH_MP DIRICHLET_CHARACTER_POW th)]) THEN
  MATCH_MP_TAC DIRICHLET_CHARACTER_CONG THEN
  EXISTS_TAC `d:num` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FERMAT_LITTLE THEN ASM_MESON_TAC[COPRIME_SYM]);;
```
### Informal statement
For all natural numbers `d` and `n`, and for all functions `c` from natural numbers to complex numbers, if `c` is a Dirichlet character modulo `d` and `d` and `n` are coprime, then `c(n)` raised to the power of Euler's totient function of `d` is equal to the complex number 1.

### Informal sketch
The proof proceeds as follows:
- Assume `c` is a Dirichlet character of modulus `d` and `d` and `n` are coprime.
- Use the property `DIRICHLET_CHARACTER_EQ_1` that `c(1) = 1`.
- Use `DIRICHLET_CHARACTER_POW` to rewrite `c(n) pow phi(d)` to `c(n pow phi(d))`.
- Apply `DIRICHLET_CHARACTER_CONG`, which states that if `x = y mod d`, then `c(x) = c(y)`.
- Show that `n pow phi(d) = 1 mod d`. This requires showing there exists a `d` such that the congruence relation holds.
- Apply Fermat's Little Theorem (`FERMAT_LITTLE`), which (since `coprime(d, n)`) states that `n pow phi(d) = 1 mod d`.

### Mathematical insight
This theorem states a fundamental property of Dirichlet characters: when raised to the power of Euler's totient function of their modulus, they evaluate to 1 for arguments coprime to the modulus. This is analogous to Euler's theorem and is crucial in analytic number theory when dealing with Dirichlet L-functions.

### Dependencies
- `dirichlet_character`
- `coprime`
- `phi` (Euler's totient function)
- `DIRICHLET_CHARACTER_EQ_1`
- `DIRICHLET_CHARACTER_POW`
- `DIRICHLET_CHARACTER_CONG`
- `FERMAT_LITTLE`
- `COPRIME_SYM`


---

## DIRICHLET_CHARACTER_NORM

### Name of formal statement
DIRICHLET_CHARACTER_NORM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_NORM = prove
 (`!d c n. dirichlet_character d c
           ==> norm(c n) = if coprime(d,n) then &1 else &0`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[COMPLEX_NORM_ZERO] THEN
    ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_0; COPRIME_SYM]] THEN
  ASM_CASES_TAC `d = 0` THENL
   [ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_1; COMPLEX_NORM_CX; REAL_ABS_NUM;
                  COPRIME_0; COPRIME_SYM];
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`; `n:num`]
    DIRICHLET_CHARACTER_ROOT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real`) THEN
  REWRITE_TAC[COMPLEX_NORM_POW; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`norm((c:num->complex) n)`; `phi d`] REAL_POW_EQ_1_IMP) THEN
  ASM_REWRITE_TAC[REAL_ABS_NORM] THEN
  ASM_MESON_TAC[PHI_LOWERBOUND_1_STRONG; LE_1]);;
```

### Informal statement
For all `d`, `c`, and `n`, if `c` is a Dirichlet character modulo `d`, then the norm of `c` applied to `n` is equal to 1 if `d` and `n` are coprime, and 0 otherwise.

### Informal sketch
- We aim to prove that if `c` is a Dirichlet character modulo `d`, then the norm of `c(n)` is 1 if `d` and `n` are coprime, and 0 otherwise.
- First, perform case splitting on `coprime(d, n)`.
    - If `coprime(d, n)` holds:
        - We use the theorem `DIRICHLET_CHARACTER_EQ_1` to show that `c(n)` is a complex number with absolute value 1. Thus, its norm is 1.
    - If `coprime(d, n)` does not hold:
        - We use the theorem `DIRICHLET_CHARACTER_EQ_0` to show that `c(n)` is zero. The norm of zero is zero.
- Then, we consider the case where `d = 0`.
    - If `d = 0`:
        - If `coprime(0, n)` holds, `c(n) = 1`, and `norm(c(n)) = 1`.
    - Apply `DIRICHLET_CHARACTER_ROOT` to obtain `c(n)^phi(d) = 1`.
- From `c(n)^phi(d) = 1`, take the norm of both sides, yielding `norm(c(n)^phi(d)) = norm(1)`.
- Using properties of the norm and absolute value, `norm(c(n))^phi(d) = 1`.
- Finally, use `PHI_LOWERBOUND_1_STRONG` and `REAL_POW_EQ_1_IMP` to conclude `norm(c(n)) = 1`.

### Mathematical insight
Dirichlet characters are important in number theory, particularly in the study of the distribution of prime numbers. This theorem states a fundamental property of Dirichlet characters, namely that the norm of the character evaluated at an integer `n` is 1 if `n` is coprime to the modulus `d`, and 0 otherwise. This property is essential in many applications of Dirichlet characters, such as proving Dirichlet's theorem on primes in arithmetic progressions.

### Dependencies
- Definitions: `dirichlet_character`
- Theorems: `DIRICHLET_CHARACTER_EQ_0`, `DIRICHLET_CHARACTER_EQ_1`, `COMPLEX_NORM_ZERO`, `COPRIME_SYM`, `COMPLEX_NORM_CX`, `REAL_ABS_NUM`, `COPRIME_0`, `DIRICHLET_CHARACTER_ROOT`, `COMPLEX_NORM_POW`, `REAL_POW_EQ_1_IMP`, `REAL_ABS_NORM`, `PHI_LOWERBOUND_1_STRONG`, `LE_1`


---

## chi_0

### Name of formal statement
chi_0

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let chi_0 = new_definition
 `chi_0 d n = if coprime(n,d) then Cx(&1) else Cx(&0)`;;
```

### Informal statement
For any natural number `d` and `n`, `chi_0 d n` is defined to be the complex number 1 if `n` and `d` are coprime, and the complex number 0 otherwise.

### Informal sketch
- The definition of `chi_0` is a straightforward conditional definition based on the result of `coprime(n, d)`.
- If `coprime(n, d)` evaluates to true, then `chi_0 d n` is defined to be `Cx(&1)`, which is the complex number 1.
- If `coprime(n, d)` evaluates to false, then `chi_0 d n` is defined to be `Cx(&0)`, which is the complex number 0.

### Mathematical insight
The function `chi_0` represents the principal Dirichlet character modulo `d`.  Dirichlet characters are important in number theory, especially in the study of Dirichlet L-functions and the distribution of prime numbers in arithmetic progressions. The principal character is a fundamental building block for constructing other Dirichlet characters and understanding their properties. It essentially acts as an indicator function for integers coprime to the modulus.

### Dependencies
- Definition: `coprime`
- Definition: `Cx`


---

## DIRICHLET_CHARACTER_CHI_0

### Name of formal statement
DIRICHLET_CHARACTER_CHI_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_CHI_0 = prove
 (`dirichlet_character d (chi_0 d)`,
  REWRITE_TAC[dirichlet_character; chi_0] THEN
  REWRITE_TAC[NUMBER_RULE `coprime(n + d,d) <=> coprime(n,d)`;
          NUMBER_RULE `coprime(m * n,d) <=> coprime(m,d) /\ coprime(n,d)`] THEN
  CONV_TAC COMPLEX_RING);;
```

### Informal statement
For any positive integer `d`, `chi_0 d` is a Dirichlet character modulo `d`.

### Informal sketch
The proof proceeds as follows:
- First, rewrite using the definitions of `dirichlet_character` and `chi_0`. This expands the goal to showing that `chi_0 d` satisfies the defining properties of a Dirichlet character.
- Then, rewrite using the number theory rules `coprime(n + d,d) <=> coprime(n,d)` and `coprime(m * n,d) <=> coprime(m,d) /\ coprime(n,d)`. These rules are used to simplify the conditions related to coprimality within the definition of `chi_0`.
- Finally, apply the conversion tactic `COMPLEX_RING` to simplify the resulting expression in the complex field. This proves that `chi_0 d` indeed satisfies the properties of a Dirichlet character.

### Mathematical insight
The theorem states that the function `chi_0`, which maps integers coprime to `d` to 1 and other integers to 0, is a Dirichlet character modulo `d`. This is important because `chi_0` is the principal Dirichlet character and serves as a fundamental example in the theory of Dirichlet characters. Dirichlet characters are crucial in analytic number theory, particularly in the study of Dirichlet L-functions.

### Dependencies
- Definitions: `dirichlet_character`, `chi_0`
- Theorems:
  - `NUMBER_RULE \`coprime(n + d,d) <=> coprime(n,d)\``
  - `NUMBER_RULE \`coprime(m * n,d) <=> coprime(m,d) /\ coprime(n,d)\``
  - `COMPLEX_RING`


---

## DIRICHLET_CHARACTER_EQ_PRINCIPAL

### Name of formal statement
DIRICHLET_CHARACTER_EQ_PRINCIPAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_EQ_PRINCIPAL = prove
 (`!d c. dirichlet_character d c
         ==> (c = chi_0 d <=> !n. coprime(n,d) ==> c(n) = Cx(&1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; chi_0] THEN
  ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_0]);;
```
### Informal statement
For all `d` and `c`, if `c` is a Dirichlet character modulo `d`, then `c` is equal to the principal character `chi_0 d` if and only if for all `n`, if `n` is coprime to `d`, then `c(n)` is equal to the complex number 1.

### Informal sketch
*   The proof starts by stripping the quantifiers and implication.
*   It then rewrites using the definition of `FUN_EQ_THM` (functional equality) and the definition of `chi_0`. Thus, the proof reduces to showing that `!n. coprime(n, d) ==> c n = Cx(&1)` is equivalent to `!n. c n = if coprime(n,d) then Cx(&1) else Cx(&0)`.
*   Finally, use `ASM_MESON_TAC` with the theorem `DIRICHLET_CHARACTER_EQ_0` to complete the proof. This uses automatic reasoning along with the discharge of assumptions. `DIRICHLET_CHARACTER_EQ_0` probably states that if any Dirichlet character maps a number coprime to the modulus to zero, then it maps everything coprime to modulus to zero.

### Mathematical insight
This theorem characterizes the principal Dirichlet character `chi_0 d` as the unique Dirichlet character modulo `d` that maps all integers coprime to `d` to 1. It formalizes the fundamental property that the principal character is an identity element in the group of Dirichlet characters.

### Dependencies
- Theorems:
    - `FUN_EQ_THM`
    - `DIRICHLET_CHARACTER_EQ_0`
- Definitions:
    - `dirichlet_character`
    - `chi_0`
    - `coprime`


---

## DIRICHLET_CHARACTER_NONPRINCIPAL

### Name of formal statement
DIRICHLET_CHARACTER_NONPRINCIPAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_NONPRINCIPAL = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> ?n. coprime(n,d) /\ ~(c n = Cx(&0)) /\ ~(c n = Cx(&1))`,
  MESON_TAC[DIRICHLET_CHARACTER_EQ_PRINCIPAL; DIRICHLET_CHARACTER_EQ_0]);;
```
### Informal statement
For all `d` and `c`, if `c` is a Dirichlet character modulo `d` and `c` is not the principal Dirichlet character modulo `d` (`chi_0 d`), then there exists an `n` such that `n` is coprime to `d` and `c(n)` is neither `Cx(&0)` nor `Cx(&1)`.

### Informal sketch
- The proof proceeds by contradiction, leveraging the properties of Dirichlet characters. The goal is to show that if `c` is a non-principal Dirichlet character modulo `d`, then there exists an `n` coprime to `d` such that `c(n)` is neither 0 nor 1.
- The proof uses `DIRICHLET_CHARACTER_EQ_PRINCIPAL` to show that if `c` is not the principal character, then there exists some `n` coprime to `d` s.t. `~(c n = Cx(&1))`.
- Then `DIRICHLET_CHARACTER_EQ_0` is used to show `~(c n = Cx(&0))`.
- These results are combined to arrive at a final result `coprime(n,d) /\ ~(c n = Cx(&0)) /\ ~(c n = Cx(&1))`.

### Mathematical insight
This theorem states a fundamental property of non-principal Dirichlet characters. It asserts that a non-principal character cannot only take the values 0 or 1 on integers coprime to its modulus. This is important because it distinguishes non-principal characters and highlights their richer structure. The theorem is essential for further analysis of Dirichlet characters and their applications in number theory, particularly in the study of L-functions and the distribution of prime numbers.

### Dependencies
- `DIRICHLET_CHARACTER_EQ_PRINCIPAL`
- `DIRICHLET_CHARACTER_EQ_0`

### Porting notes (optional)
When porting this, ensure the target system has a well-defined notion of Dirichlet characters and their principal character counterparts. The properties `DIRICHLET_CHARACTER_EQ_PRINCIPAL` and `DIRICHLET_CHARACTER_EQ_0` are crucial and must be established within the target environment. The handling of complex numbers (`Cx`) and coprimality (`coprime`) should be consistent with HOL Light.


---

## DIRICHLET_CHARACTER_0

### Name of formal statement
DIRICHLET_CHARACTER_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_0 = prove
 (`!c. dirichlet_character 0 c <=> c = chi_0 0`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[DIRICHLET_CHARACTER_CHI_0] THEN
  DISCH_TAC THEN REWRITE_TAC[chi_0; FUN_EQ_THM; COPRIME_0] THEN
  X_GEN_TAC `n:num` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_1; DIRICHLET_CHARACTER_EQ_0;
                COPRIME_0]);;
```

### Informal statement
For all `c`, `c` is a Dirichlet character modulo 0 if and only if `c` is equal to `chi_0` modulo 0, where `chi_0` is the principal Dirichlet character.

### Informal sketch
The proof establishes the equivalence between being a Dirichlet character modulo 0 and being the principal Dirichlet character modulo 0.

- First, expand the definition of `dirichlet_character 0 c` using `DIRICHLET_CHARACTER_CHI_0`
- Then, assume `dirichlet_character 0 c` and rewrite using the definitions of `chi_0`, functional equality, and the fact that 0 and `n` are coprime if and only if `n = 1` (`COPRIME_0`).
- Introduce an arbitrary natural number `n`. Perform case analysis based on a conditional statement.
- Use assumption rewriting and a Meson-based automated proof search, which leverages facts about Dirichlet characters, specifically, the values when the argument is 0 or 1 (`DIRICHLET_CHARACTER_EQ_1` and `DIRICHLET_CHARACTER_EQ_0`) and the behavior of coprimality with 0 (`COPRIME_0`).

### Mathematical insight
This theorem characterizes Dirichlet characters modulo 0. The only Dirichlet character modulo 0 is the trivial character. The theorem asserts that `chi_0` is the unique Dirichlet character modulo 0. This result is important for completeness and for understanding the boundary cases in the theory of Dirichlet characters.

### Dependencies
- Definitions:
  - `chi_0`
- Theorems:
  - `DIRICHLET_CHARACTER_CHI_0`
  - `FUN_EQ_THM`
  - `COPRIME_0`
  - `DIRICHLET_CHARACTER_EQ_1`
  - `DIRICHLET_CHARACTER_EQ_0`

### Porting notes (optional)
The main challenge may come from the Meson call. You may need to manually decompose the case analysis depending on how sophisticated the target prover's automation is. The rewriting steps should be relatively straightforward.


---

## DIRICHLET_CHARACTER_1

### Name of formal statement
DIRICHLET_CHARACTER_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_1 = prove
 (`!c. dirichlet_character 1 c <=> !n. c n = Cx(&1)`,
  GEN_TAC THEN REWRITE_TAC[dirichlet_character; COPRIME_1] THEN EQ_TAC THENL
   [STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`1`; `1`]) THEN
    ASM_REWRITE_TAC[ARITH; COMPLEX_RING
     `x = x * x <=> x = Cx(&0) \/ x = Cx(&1)`] THEN
    DISCH_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ADD1] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `0`)) THEN ASM_REWRITE_TAC[ARITH] THEN
    CONV_TAC COMPLEX_RING;
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING]);;
```

### Informal statement
For any function `c` from natural numbers to complex numbers, `c` is a Dirichlet character modulo 1 if and only if for all natural numbers `n`, `c(n)` is equal to the complex number 1.

### Informal sketch
The proof proceeds as follows:
- First, rewrite the definition of `dirichlet_character` and use the fact that `COPRIME_1` holds. This reduces the goal to proving the equivalence of two universal quantifications.
- To prove the equivalence, split it into two implications.
- For the first implication (from `dirichlet_character 1 c` to `!n. c n = Cx(&1)`):
    - Assume `dirichlet_character 1 c`.
    - Specialize the assumption `dirichlet_character 1 c` with `1` and `1`, and use the definition of `dirichlet_character`. This gives conditions about `c`.
    - Use the fact that `x = x * x` is equivalent to `x = 0` or `x = 1` in the complex numbers.
    - Perform induction on `n`.
        - In the base case, rewrite using the properties of complex numbers.
        - In the inductive step: rewrite using `ADD1`. Specialize assumptions regarding the dirichlet character at `0`. Rewrite using arithmetic. Rewrite using complex number properties to show equivalence to 1.
- For the second implication (from `!n. c n = Cx(&1)` to `dirichlet_character 1 c`):
    - Assume `!n. c n = Cx(&1)`.
    - Rewrite using the assumption.
    - Rewrite using properties of complex numbers.

### Mathematical insight
The statement provides a characterization of Dirichlet characters modulo 1. A Dirichlet character modulo 1 is the function that maps every natural number to 1. This is a basic but important case in the theory of Dirichlet characters.

### Dependencies
- `dirichlet_character`
- `COPRIME_1`
- `ARITH`
- `COMPLEX_RING`
- `ADD1`


---

## DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL

### Name of formal statement
DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> ~(d = 0) /\ ~(d = 1)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `d = 0` THEN
  ASM_REWRITE_TAC[DIRICHLET_CHARACTER_0; TAUT `~(p /\ ~p)`] THEN
  ASM_CASES_TAC `d = 1` THEN
  ASM_REWRITE_TAC[DIRICHLET_CHARACTER_1; chi_0; FUN_EQ_THM; COPRIME_1] THEN
  CONV_TAC TAUT);;
```

### Informal statement
For all `d` and `c`, if `c` is a Dirichlet character modulo `d` and `c` is not equal to the principal character `chi_0 d` modulo `d`, then `d` is not equal to 0 and `d` is not equal to 1.

### Informal sketch
The proof proceeds by contradiction, showing that if `d` is 0 or 1, then `c` must be the principal character `chi_0 d`.

- Assume `d = 0`. Use the theorem `DIRICHLET_CHARACTER_0` which states that there are no Dirichlet characters modulo 0, arriving at a contradiction.
- Assume `d = 1`. Use the theorem `DIRICHLET_CHARACTER_1` which states that the only Dirichlet character modulo 1 is the principal character `chi_0`.  Then using rewriting and `FUN_EQ_THM`, the assumption `~(c = chi_0 d)` leads to a contradiction.

### Mathematical insight
This theorem states a basic property of Dirichlet characters: non-principal Dirichlet characters are only defined for moduli greater than 1. The principal character modulo `d` is always a Dirichlet character modulo `d`, even when `d=0` or `d=1`, but in those cases, that is the *only* Dirichlet character.

### Dependencies
- `DIRICHLET_CHARACTER`
- `chi_0`
- `DIRICHLET_CHARACTER_0`
- `DIRICHLET_CHARACTER_1`
- `FUN_EQ_THM`
- `COPRIME_1`


---

## DIRICHLET_CHARACTER_ZEROSUM

### Name of formal statement
DIRICHLET_CHARACTER_ZEROSUM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_ZEROSUM = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> vsum(1..d) c = Cx(&0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIRICHLET_CHARACTER_NONPRINCIPAL) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC(COMPLEX_RING
   `!x. x * c = c /\ ~(x = Cx(&1)) ==> c = Cx(&0)`) THEN
  EXISTS_TAC `(c:num->complex) m` THEN
  ASM_SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  MATCH_MP_TAC(MESON[]
   `!t. vsum t f = vsum s f /\ vsum t g = vsum s g /\ vsum t f = vsum t g
        ==> vsum s f = vsum s g`) THEN
  EXISTS_TAC `{n | coprime(n,d) /\ n < d}` THEN
  REPEAT(CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
    SIMP_TAC[SUBSET; IN_NUMSEG; LT_IMP_LE; IN_ELIM_THM] THEN CONJ_TAC THEN
    X_GEN_TAC `r:num` THENL
     [ASM_CASES_TAC `r = 0` THENL [ALL_TAC; ASM_ARITH_TAC] THEN
      ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_REWRITE_TAC[COPRIME_0];
      ASM_CASES_TAC `coprime(r,d)` THEN ASM_REWRITE_TAC[] THENL
       [ASM_CASES_TAC `r:num = d` THEN ASM_REWRITE_TAC[LT_REFL] THENL
         [ASM_MESON_TAC[COPRIME_REFL]; ASM_ARITH_TAC];
        REWRITE_TAC[COMPLEX_VEC_0] THEN
        ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_0; COMPLEX_MUL_RZERO]]];
    ALL_TAC]) THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[GSYM(MATCH_MP DIRICHLET_CHARACTER_MUL (CONJUNCT1 th))]) THEN
  SIMP_TAC[VSUM; PHI_FINITE_LEMMA] THEN
  MATCH_MP_TAC ITERATE_OVER_COPRIME THEN SIMP_TAC[MONOIDAL_VECTOR_ADD] THEN
  ASM_MESON_TAC[DIRICHLET_CHARACTER_CONG]);;
```
### Informal statement
For all `d` and `c`, if `c` is a Dirichlet character modulo `d` and `c` is not the principal character `chi_0` modulo `d`, then the sum of the values of `c` from `1` to `d` is equal to the complex number `0`.

### Informal sketch
The proof proceeds as follows:
- Assume `d` and `c` such that `c` is a `dirichlet_character d` and `c` is not the principal Dirichlet character `chi_0 d`.
- Apply `DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL` and `DIRICHLET_CHARACTER_NONPRINCIPAL` to obtain properties of non-principal Dirichlet characters.
- Choose an `m:num` such that `c(m) /= Cx(&1)`.
- Show that if `x * c = c /\ ~(x = Cx(&1))` then `c = Cx(&0)`. This uses the ring structure of complex numbers..
- Use the fact that `vsum(1..d) (\i. c(m) * c(i)) = c(m) * vsum(1..d) c` and `FINITE_NUMSEG` to rewrite the sum.
- Instantiate `MESON[]` with the term `!t. vsum t f = vsum s f /\ vsum t g = vsum s g /\ vsum t f = vsum t g ==> vsum s f = vsum s g`.
- Let `S = {n | coprime(n,d) /\ n < d}`. Show that `vsum (1..d) c = vsum S c`, and that if `coprime(r, d)` and `r < d` then `c(r) /= 0` and `r = 0` is impossible. If `r = d` and `coprime(r, d)`, then `r` cannot be less than `d`.
- Show that `vsum (1..d) c = vsum iterates_over_coprime c` where `iterates_over_coprime` is `S`.
- Use the fact that `c(m) * vsum (1..d) c = vsum(1..d) c`. Since `c(m) /= Cx(&1)`, we have `vsum(1..d) c = Cx(&0)`. This uses the earlier instance of `COMPLEX_RING` equality.
- Simplify using `DIRICHLET_CHARACTER_MUL`, `VSUM`, `PHI_FINITE_LEMMA`, `ITERATE_OVER_COPRIME`, `MONOIDAL_VECTOR_ADD` and `DIRICHLET_CHARACTER_CONG`.

### Mathematical insight
This theorem states a fundamental property of non-principal Dirichlet characters: their values sum to zero over a complete residue system modulo d. This property is crucial in analytic number theory, particularly in the study of L-functions and the distribution of primes in arithmetic progressions.

### Dependencies
- `DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL`
- `DIRICHLET_CHARACTER_NONPRINCIPAL`
- `VSUM_COMPLEX_LMUL`
- `FINITE_NUMSEG`
- `DIRICHLET_CHARACTER_EQ_0`
- `DIRICHLET_CHARACTER_MUL`
- `VSUM`
- `PHI_FINITE_LEMMA`
- `ITERATE_OVER_COPRIME`
- `MONOIDAL_VECTOR_ADD`
- `DIRICHLET_CHARACTER_CONG`
- `COPRIME_SYM`
- `COPRIME_0`
- `COPRIME_REFL`
- `GSYM`
- `COMPLEX_RING`
- `COMPLEX_MUL_RZERO`
- `SUBSET`
- `IN_NUMSEG`
- `LT_IMP_LE`
- `IN_ELIM_THM`
- `LT_REFL`
- `MONOIDAL_VECTOR_ADD`

### Porting notes (optional)
- The proof relies on properties of complex numbers and Dirichlet characters, so ensure that the target proof assistant has adequate support for these concepts.
- The tactics `ASM_CASES_TAC` and `ASM_MESON_TAC` may need to be adapted or replaced with equivalent tactics in other proof assistants.
- The handling of finite sets (`vsum(1..d)`) will need to be translated carefully.


---

## DIRICHLET_CHARACTER_ZEROSUM_MUL

### Name of formal statement
DIRICHLET_CHARACTER_ZEROSUM_MUL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_ZEROSUM_MUL = prove
 (`!d c n. dirichlet_character d c /\ ~(c = chi_0 d)
           ==> vsum(1..d*n) c = Cx(&0)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; VSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[ARITH; COMPLEX_VEC_0] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  ASM_SIMP_TAC[VSUM_ADD_SPLIT; ARITH_RULE `1 <= n + 1`; COMPLEX_ADD_LID] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[VSUM_OFFSET] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP DIRICHLET_CHARACTER_ZEROSUM) THEN
  MATCH_MP_TAC VSUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC DIRICHLET_CHARACTER_CONG THEN EXISTS_TAC `d:num` THEN
  ASM_REWRITE_TAC[] THEN NUMBER_TAC);;
```
### Informal statement
For all natural numbers `d` and `n`, and for all complex-valued functions `c` of natural numbers, if `c` is a Dirichlet character modulo `d` and `c` is not the principal Dirichlet character modulo `d` (`chi_0 d`), then the sum of `c(i)` for `i` ranging from 1 to `d*n` is equal to the complex number 0.

### Informal sketch
The proof proceeds by induction on `n`. The base case `n = 0` is immediate. For the inductive step, we assume the result holds for `n`, and we want to show it holds for `n+1`. We split the summation `vsum(1..d*(n+1)) c` into `vsum(1..d*n) c + vsum(d*n+1..d*(n+1)) c`. By the induction hypothesis, the first term is `Cx(&0)`. We rewrite `vsum(d*n+1..d*(n+1)) c` as `vsum(1..d) c`, which equals `Cx(&0)` by the theorem `DIRICHLET_CHARACTER_ZEROSUM`. We prove `vsum(d*n+1..d*(n+1)) c = vsum(1..d) c` by applying the fact that `c` is congruent modulo `d` (`DIRICHLET_CHARACTER_CONG`). The result then follows.

### Mathematical insight
This theorem states that the sum of a non-principal Dirichlet character over any `d * n` consecutive integers is zero. This property is crucial in analytic number theory and the study of L-functions. It is a generalization of the property that the sum of a non-principal Dirichlet character over a complete residue system modulo d is zero.

### Dependencies
- `dirichlet_character`
- `chi_0`
- `vsum`
- `DIRICHLET_CHARACTER_ZEROSUM`
- `DIRICHLET_CHARACTER_CONG`
- `MULT_CLAUSES`
- `VSUM_CLAUSES_NUMSEG`
- `ARITH`
- `COMPLEX_VEC_0`
- `ADD_SYM`
- `VSUM_ADD_SPLIT`
- `ARITH_RULE`
- `COMPLEX_ADD_LID`
- `VSUM_OFFSET`
- `VSUM_EQ`


---

## DIRICHLET_CHARACTER_SUM_MOD

### Name of formal statement
DIRICHLET_CHARACTER_SUM_MOD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_SUM_MOD = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> vsum(1..n) c = vsum(1..(n MOD d)) c`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP
    DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP DIVISION) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
  SIMP_TAC[VSUM_ADD_SPLIT; ARITH_RULE `1 <= n + 1`] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN
  ASM_SIMP_TAC[DIRICHLET_CHARACTER_ZEROSUM_MUL; COMPLEX_ADD_LID] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[VSUM_OFFSET] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP DIRICHLET_CHARACTER_ZEROSUM) THEN
  MATCH_MP_TAC VSUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC DIRICHLET_CHARACTER_CONG THEN EXISTS_TAC `d:num` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUMBER_RULE);;
```

### Informal statement
For all natural numbers `d` and complex-valued Dirichlet characters `c` modulo `d`, if `c` is not the principal character `chi_0` modulo `d`, then the sum of the values of `c` from 1 to `n` equals the sum of the values of `c` from 1 to `n mod d`.

### Informal sketch
The proof demonstrates that the sum of a non-principal Dirichlet character modulo `d` from 1 to `n` is equal to the sum from 1 to `n mod d`.

- The proof starts by assuming that `c` is a Dirichlet character modulo `d` and is not the principal character.
- The theorem `DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL` is used to show some properties of non-principal Dirichlet characters.
- Division is introduced to express `n` as `n = (n DIV d) * d + (n MOD d)`.
- The sum from 1 to `n` is split into a sum from 1 to `(n DIV d) * d` and a sum from `(n DIV d) * d + 1` to `n`.
- The sum from `(n DIV d) * d + 1` to `n` is rewritten as a sum from 1 to `n MOD d`.
- The sum from 1 to `(n DIV d) * d ` is further split into `(n DIV d)` blocks of sums, each running over an entire period modulo `d`.
- The theorem `DIRICHLET_CHARACTER_ZEROSUM_MUL` is applied, using the fact that the sum of a non-principal Dirichlet character over a complete period is zero, making the sum from 1 to `(n DIV d) * d` equal to zero.
- Finally, `VSUM_EQ` is used to show equality and conclude that the sum from 1 to `n` equals the sum from 1 to `n mod d`.

### Mathematical insight
This theorem exploits the periodic nature of Dirichlet characters and their vanishing sum over complete periods when they are non-principal. This property is crucial for analyzing L-functions, number theory and the distribution of primes in arithmetic progressions.

### Dependencies

- `DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL`
- `DIVISION`
- `VSUM_ADD_SPLIT`
- `DIRICHLET_CHARACTER_ZEROSUM_MUL`
- `COMPLEX_ADD_LID`
- `VSUM_OFFSET`
- `DIRICHLET_CHARACTER_ZEROSUM`
- `VSUM_EQ`
- `DIRICHLET_CHARACTER_CONG`


---

## FINITE_DIRICHLET_CHARACTERS

### Name of formal statement
FINITE_DIRICHLET_CHARACTERS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FINITE_DIRICHLET_CHARACTERS = prove
 (`!d. FINITE {c | dirichlet_character d c}`,
  GEN_TAC THEN ASM_CASES_TAC `d = 0` THENL
   [ASM_SIMP_TAC[DIRICHLET_CHARACTER_0; SET_RULE `{x | x = a} = {a}`] THEN
    SIMP_TAC[FINITE_RULES];
    ALL_TAC] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\c n. c(n MOD d))
                    {c | (!m. m IN {m | m < d}
                             ==> c(m) IN (Cx(&0) INSERT
                                          {z | z pow (phi d) = Cx(&1)})) /\
                         (!m. ~(m IN {m | m < d})
                              ==> c(m) = Cx(&0))}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_FUNSPACE THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; FINITE_INSERT] THEN
    MATCH_MP_TAC FINITE_COMPLEX_ROOTS_UNITY THEN
    ASM_SIMP_TAC[PHI_LOWERBOUND_1_STRONG; LE_1];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `c:num->complex` THEN
  DISCH_TAC THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INSERT] THEN
  EXISTS_TAC `\n:num. if n < d then c(n) else Cx(&0)` THEN
  ASM_SIMP_TAC[DIVISION; FUN_EQ_THM] THEN CONJ_TAC THEN X_GEN_TAC `m:num` THENL
   [MATCH_MP_TAC DIRICHLET_CHARACTER_CONG THEN EXISTS_TAC `d:num` THEN
    ASM_MESON_TAC[CONG_MOD; CONG_SYM];
    ASM_MESON_TAC[DIRICHLET_CHARACTER_ROOT; COPRIME_SYM;
                  DIRICHLET_CHARACTER_EQ_0]]);;
```

### Informal statement
For all natural numbers `d`, the set of Dirichlet characters modulo `d` is finite.

### Informal sketch
The proof proceeds as follows:
- Case split on whether `d` is equal to `0`.
  - If `d = 0`, then the set of Dirichlet characters modulo `d` is the singleton set containing the zero function.
  - Since the singleton set is finite, this case is proved using `DIRICHLET_CHARACTER_0` and `FINITE_RULES`.
- If `d` is not equal to `0`, we show that the set of Dirichlet characters modulo `d` is a subset of the image of a finite set under a map.
  - Specifically, the map takes a function `c` from natural numbers to complex numbers, such that for all `m`, if `m` is less than `d`, then `c(m)` is a root of unity (specifically, an element of {z | z pow (phi d) = Cx(&1)}) with `Cx(&0)` included or `c(m)` is 0 otherwise.
  - The map sends such a function `c` to a function which maps to the corresponding function modulo d. The `IMAGE` of this set can expressed by `\c n. c(n MOD d)`.
  - `FINITE_SUBSET` is used to show that if the image set is finite, then since the set of dirichlet characters is a subset of this `IMAGE`, the set of dirichlet characters modulo `d` is finite.
  - It remains to show the `IMAGE` outlined above is finite. Showing the conditions for the function `c` yields this set is finite.
  - The set of such functions `c` is a subset of the function space from `{m | m < d}` to `(Cx(&0) INSERT {z | z pow (phi d) = Cx(&1)})`, and the rest are 0.
  - `FINITE_IMAGE` and `FINITE_FUNSPACE` along with properties of finiteness on numbers and `FINITE_INSERT` are used.
  - The `MATCH_MP_TAC FINITE_COMPLEX_ROOTS_UNITY` is used show `{z | z pow (phi d) = Cx(&1)}` is finite
  - Then it is shown that this `IMAGE` is indeed finite using `FINITE_NUMSEG_LT` and `FINITE_INSERT`.
- Finally, existence is shown along with properties of `DIRICHLET_CHARACTER_CONG` and `DIRICHLET_CHARACTER_ROOT`.

### Mathematical insight
The theorem states a fundamental property of Dirichlet characters: for a given modulus, there are only finitely many distinct characters. This is important because it allows us to enumerate and study the characters in a systematic way. The `phi(d)` term relates to the totient function, and is significant because `phi(d)` is the number of integers less than `d` that are relatively prime to `d`. The order of the roots of unity are related to the `phi(d)` function of the `d` modulus.

### Dependencies
- `DIRICHLET_CHARACTER_0`
- `SET_RULE`
- `FINITE_RULES`
- `FINITE_SUBSET`
- `FINITE_IMAGE`
- `FINITE_FUNSPACE`
- `FINITE_NUMSEG_LT`
- `FINITE_INSERT`
- `FINITE_COMPLEX_ROOTS_UNITY`
- `PHI_LOWERBOUND_1_STRONG`
- `LE_1`
- `SUBSET`
- `IN_ELIM_THM`
- `IN_IMAGE`
- `IN_INSERT`
- `DIVISION`
- `FUN_EQ_THM`
- `DIRICHLET_CHARACTER_CONG`
- `CONG_MOD`
- `CONG_SYM`
- `DIRICHLET_CHARACTER_ROOT`
- `COPRIME_SYM`
- `DIRICHLET_CHARACTER_EQ_0`

### Porting notes (optional)
- The finiteness proofs are always interesting when porting to other assistants. Make sure the correct libraries are present describing finiteness and set theory.
- Need to make sure complex numbers and their roots of unity are defined and used in the same way.
- Need to ensure the totient function, given here with `phi`, is well defined and present within the library.


---

## DIRICHLET_CHARACTER_MUL_CNJ

### Name of formal statement
DIRICHLET_CHARACTER_MUL_CNJ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_MUL_CNJ = prove
 (`!d c n. dirichlet_character d c /\ ~(c n = Cx(&0))
           ==> cnj(c n) * c n = Cx(&1) /\ c n * cnj(c n) = Cx(&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(COMPLEX_FIELD
   `inv z = w /\ ~(z = Cx(&0)) ==> w * z = Cx(&1) /\ z * w = Cx(&1)`) THEN
  ASM_REWRITE_TAC[COMPLEX_INV_CNJ] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM COMPLEX_NORM_NZ]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_NORM th]) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LT_REFL; COMPLEX_POW_ONE] THEN
  REWRITE_TAC[COMPLEX_DIV_1]);;
```
### Informal statement
For all Dirichlet characters `d` and all mappings `c` from natural numbers to complex numbers, if `c` is a Dirichlet character modulo `d` and `c n` is not equal to the complex number 0 for all `n`, then the complex conjugate of `c n` multiplied by `c n` equals the complex number 1, and `c n` multiplied by the complex conjugate of `c n` equals the complex number 1.

### Informal sketch
The proof proceeds as follows:
- Assume `c` is a Dirichlet character modulo `d` and `c n` is not zero.
- Apply the general complex field property that if `z` is nonzero and `w` is the inverse of `z`, then `w * z = 1` and `z * w = 1`.
- Rewrite using the fact that the complex conjugate of the inverse of a complex number z, `COMPLEX_INV_CNJ`, is the inverse of the complex conjugate of `z`.
- Apply the property that the complex norm squared of a nonzero number is nonzero, `GSYM COMPLEX_NORM_NZ`.
- Rewrite using the property that the norm of a Dirichlet character evaluated at any point is 1, `MATCH_MP DIRICHLET_CHARACTER_NORM`.
- Perform case splitting using `COND_CASES_TAC`.
- Simplify using the fact that `a < a` is false, and `COMPLEX_POW_ONE`.
- Rewrite using the definition of division by 1.

### Mathematical insight
This theorem states that for a Dirichlet character, the product of its value at any natural number `n` with its complex conjugate is equal to 1 when its value at `n` is not zero. Since a Dirichlet character is multiplicative and has norm 1, this result aligns with the multiplicative nature of complex conjugates and the fact that the complex norm squared of a complex number `z` is `z * cnj(z)`.

### Dependencies
- `dirichlet_character`
- `COMPLEX_FIELD`
- `COMPLEX_INV_CNJ`
- `COMPLEX_NORM_NZ`
- `DIRICHLET_CHARACTER_NORM`
- `REAL_LT_REFL`
- `COMPLEX_POW_ONE`
- `COMPLEX_DIV_1`


---

## DIRICHLET_CHARACTER_CNJ

### Name of formal statement
DIRICHLET_CHARACTER_CNJ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_CNJ = prove
 (`!d c. dirichlet_character d c ==> dirichlet_character d (\n. cnj(c n))`,
  SIMP_TAC[dirichlet_character; CNJ_MUL; CNJ_EQ_CX]);;
```
### Informal statement
For all natural numbers `d` and for all functions `c` from natural numbers to complex numbers, if `c` is a Dirichlet character modulo `d`, then the function that maps `n` to the complex conjugate of `c n` is also a Dirichlet character modulo `d`.

### Informal sketch
The proof shows that if a function `c` is a Dirichlet character modulo `d`, then its complex conjugate is also a Dirichlet character modulo `d`.
- The proof uses the definition of `dirichlet_character`.
- The proof uses the theorem stating that the conjugate of the product is the product of the conjugates (`CNJ_MUL`).
- The proof uses the theorem stating that complex conjugation preserves equality of complex numbers (`CNJ_EQ_CX`).

### Mathematical insight
This theorem shows that the complex conjugate of a Dirichlet character is also a Dirichlet character. This is useful because it says that if `c` satisfies the properties of a Dirichlet character then the function obtained by taking the complex conjugate also satisfies those properties.

### Dependencies
- Definitions:
  - `dirichlet_character`
- Theorems:
  - `CNJ_MUL`
  - `CNJ_EQ_CX`


---

## DIRICHLET_CHARACTER_GROUPMUL

### Name of formal statement
DIRICHLET_CHARACTER_GROUPMUL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_GROUPMUL = prove
 (`!d c1 c2. dirichlet_character d c1 /\ dirichlet_character d c2
             ==> dirichlet_character d (\n. c1(n) * c2(n))`,
  SIMP_TAC[dirichlet_character; COMPLEX_ENTIRE] THEN
  REWRITE_TAC[COMPLEX_MUL_AC]);;
```

### Informal statement
For any divisor `d`, and any two Dirichlet characters `c1` and `c2` modulo `d`, the pointwise product of `c1` and `c2`, defined as `\n. c1(n) * c2(n)`, is also a Dirichlet character modulo `d`.

### Informal sketch
The proof proceeds as follows:

- Assume `c1` and `c2` are Dirichlet characters modulo `d`. This means they satisfy the conditions specified by the definition of `dirichlet_character`.
- The goal is to show that the function `\n. c1(n) * c2(n)` also satisfies these same conditions.
- The proof uses simplification with the definition of `dirichlet_character` and the theorem that `COMPLEX_ENTIRE` to expand the definition and properties of complex numbers.
- It also uses rewriting with `COMPLEX_MUL_AC` which proves the associativity and commutativity of multiplication for complex numbers, to simplify and reorganize the resulting expressions, ultimately verifying that the pointwise product satisfies the conditions for being a Dirichlet character.

### Mathematical insight
This theorem states that the Dirichlet characters modulo a given divisor form a group under pointwise multiplication. This is a fundamental property in algebraic number theory. The fact that the product of two Dirichlet characters is again a Dirichlet character allows one to define a group structure (specifically, a finite abelian group) on the set of Dirichlet characters, which is crucial for understanding the distribution of primes in arithmetic progressions and the properties of L-functions.

### Dependencies
- Definition: `dirichlet_character`
- Theorem: `COMPLEX_ENTIRE`
- Theorem: `COMPLEX_MUL_AC`


---

## DIRICHLET_CHARACTER_GROUPINV

### Name of formal statement
DIRICHLET_CHARACTER_GROUPINV

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_GROUPINV = prove
 (`!d c. dirichlet_character d c ==> (\n. cnj(c n) * c n) = chi_0 d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[chi_0; FUN_EQ_THM] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [ASM_MESON_TAC[DIRICHLET_CHARACTER_MUL_CNJ; DIRICHLET_CHARACTER_EQ_0];
    ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_0; COMPLEX_MUL_RZERO]]);;
```
### Informal statement
For any Dirichlet character `c` modulo `d`, the function mapping `n` to the product of the complex conjugate of `c n` and  `c n` is equal to the principal Dirichlet character modulo `d`, denoted by `chi_0 d`.

### Informal sketch
The proof proceeds by induction.

- First, rewrite the goal using the definition of the principal Dirichlet character `chi_0 d`, to replace the right-hand side with a conditional expression which depends on whether `gcd(d,n) = 1`.
- Then consider two cases: one where `gcd(d, n) = 1`, and the other where `gcd(d, n) != 1`.
- In the case where `gcd(d, n) = 1`, apply `DIRICHLET_CHARACTER_MUL_CNJ` to show that `cnj(c n) * c n = 1`, and then use `DIRICHLET_CHARACTER_EQ_0`.
- In the case where `gcd(d, n) != 1`, apply `DIRICHLET_CHARACTER_EQ_0` combined with `COMPLEX_MUL_RZERO` to prove `cnj(c n) * c n = 0`.

### Mathematical insight
This theorem states that for any Dirichlet character, multiplying its value at a number `n` by the complex conjugate gives a value equal to the principal character. This characterizes `c n * conjugate(c n)` as a Dirichlet character, namely the principal character. If `c n` is nonzero, then `c n * conj(c n)` will equal 1, and if `c n` is zero, then `c n * conj(c n)` will equal 0. Since the dirichlet character is non-zero iff `gcd(d,n) = 1` this results in the principal character.

### Dependencies
- `chi_0`
- `FUN_EQ_THM`
- `DIRICHLET_CHARACTER_MUL_CNJ`
- `DIRICHLET_CHARACTER_EQ_0`
- `COMPLEX_MUL_RZERO`


---

## DIRICHLET_CHARACTER_SUM_OVER_NUMBERS

### Name of formal statement
DIRICHLET_CHARACTER_SUM_OVER_NUMBERS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_SUM_OVER_NUMBERS = prove
 (`!d c. dirichlet_character d c
         ==> vsum (1..d) c = if c = chi_0 d then Cx(&(phi d)) else Cx(&0)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[DIRICHLET_CHARACTER_ZEROSUM] THEN
  FIRST_X_ASSUM SUBST1_TAC THEN POP_ASSUM(K ALL_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[chi_0] THEN
  SIMP_TAC[GSYM VSUM_RESTRICT_SET; FINITE_NUMSEG; GSYM COMPLEX_VEC_0] THEN
  SIMP_TAC[phi; VSUM_CONST; FINITE_RESTRICT; FINITE_NUMSEG] THEN
  REWRITE_TAC[COMPLEX_CMUL; COMPLEX_MUL_RID] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
  X_GEN_TAC `x:num` THEN ASM_CASES_TAC `coprime(x,d)` THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;
```
### Informal statement
For all `d` and `c`, if `c` is a Dirichlet character modulo `d`, then the sum of the values of `c` from 1 to `d` is equal to `Cx(&(phi d))` if `c` is the principal character `chi_0` modulo `d`, and is equal to `Cx(&0)` otherwise, where `phi d` is Euler's totient function.

### Informal sketch
The proof proceeds by case distinction on whether the Dirichlet character `c` is equal to the principal character `chi_0 d` or not.

- Case 1: `c = chi_0 d`. In this case, we need to show that `vsum (1..d) c = Cx(&(phi d))`.
  - We rewrite `vsum (1..d) c` as the sum over numbers `x` in the range `1..d` restricted to those coprime to `d`. Then we apply the definition of `chi_0 d` to simplify `c x` to `Cx(&1)`.
  - We use `VSUM_CONST` and simplification to reduce the sum to the cardinality of the restricted set multiplied by `Cx(&1)`.
  - We use `phi d` to represent the cardinality of the set `{x | x IN 1..d /\ coprime(x,d)}`, and then use arithmetic to simplify the expression to `Cx(&(phi d))`.

- Case 2: `c <> chi_0 d`. In this case, we need to show that `vsum (1..d) c = Cx(&0)`.
  - We apply the theorem `DIRICHLET_CHARACTER_ZEROSUM`
  - `DIRICHLET_CHARACTER_ZEROSUM` states that if the character `c` is not equal to the principal character `chi_0 d` then the sum of `c` is 0.

### Mathematical insight
This theorem captures a fundamental orthogonality property of Dirichlet characters. It states that the sum of the values of a Dirichlet character over a complete residue system modulo `d` is zero unless the character is the principal character, in which case the sum is equal to `phi(d)`. This property is crucial in analytic number theory when studying L-functions and related objects.

### Dependencies
- `dirichlet_character`
- `chi_0`
- `phi`
- `vsum`
- `1..d` (numseg)
- `coprime`
- `Cx`
- `DIRICHLET_CHARACTER_ZEROSUM`
- `VSUM_RESTRICT_SET`
- `FINITE_NUMSEG`
- `COMPLEX_VEC_0`
- `VSUM_CONST`
- `FINITE_RESTRICT`
- `COMPLEX_CMUL`
- `COMPLEX_MUL_RID`
- `EXTENSION`
- `IN_ELIM_THM`
- `IN_NUMSEG`


---

## DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK

### Name of formal statement
DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK = prove
 (`!d n. vsum {c | dirichlet_character d c} (\x. x n) = Cx(&0) \/
         coprime(n,d) /\ !c. dirichlet_character d c ==> c(n) = Cx(&1)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `coprime(n,d)` THENL
   [ALL_TAC;
    DISJ1_TAC THEN REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
    MATCH_MP_TAC VSUM_EQ_0 THEN
    ASM_SIMP_TAC[IN_ELIM_THM; COMPLEX_VEC_0; DIRICHLET_CHARACTER_EQ_0]] THEN
  SUBGOAL_THEN
    `!c'. dirichlet_character d c'
          ==> vsum {c | dirichlet_character d c}
                   ((\c. c(n)) o (\c n. c'(n) * c(n))) =
              vsum {c | dirichlet_character d c} (\c. c(n))`
  MP_TAC THENL
   [ALL_TAC;
    SIMP_TAC[o_DEF; FINITE_DIRICHLET_CHARACTERS; VSUM_COMPLEX_LMUL] THEN
    REWRITE_TAC[COMPLEX_RING `a * x = x <=> a = Cx(&1) \/ x = Cx(&0)`] THEN
    ASM_MESON_TAC[]] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VSUM_INJECTION THEN
  REWRITE_TAC[FINITE_DIRICHLET_CHARACTERS; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[DIRICHLET_CHARACTER_GROUPMUL] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `(\c n. cnj(c'(n:num)) * c n)`) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN DISCH_TAC THEN X_GEN_TAC `m:num` THEN
  ASM_CASES_TAC `coprime(m,d)` THENL
   [ALL_TAC; ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_0]] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
  MATCH_MP_TAC(COMPLEX_RING
    `a * b = Cx(&1) ==> a * b * x = a * b * y ==> x = y`) THEN
  ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_0; DIRICHLET_CHARACTER_MUL_CNJ]);;
```

### Informal statement
For all positive integers `d` and `n`, either the sum of `c(n)` over all Dirichlet characters `c` modulo `d` is equal to the complex zero, or `n` and `d` are coprime and for all Dirichlet characters `c` modulo `d`, `c(n)` equals the complex one.

### Informal sketch
The proof proceeds by cases on whether `n` and `d` are coprime.

*   **Case 1:** Suppose `n` and `d` are *not* coprime.
    *   We aim to show that the sum of `c(n)` over all Dirichlet characters is zero.
    *   Simplifying using `COMPLEX_VEC_0` and `DIRICHLET_CHARACTER_EQ_0` reduces the goal to showing that a sum equals zero, which is then discharged by `VSUM_EQ_0`.

*   **Case 2:** Suppose `coprime(n, d)`.
    *   The goal becomes to show `!c. dirichlet_character d c ==> c(n) = Cx(&1)`.
    *   The proof proceeds by showing that for any Dirichlet character `c'`, the following holds: `vsum {c | dirichlet_character d c} (fun c => c(n)) = vsum {c | dirichlet_character d c} (fun c => (c'(n) * c(n)))`.
    *   This is achieved by using the fact that `FINITE_DIRICHLET_CHARACTERS` and `VSUM_COMPLEX_LMUL`. Also, the property expressed in the `COMPLEX_RING` is used: `a * x = x <=> a = Cx(&1) \/ x = Cx(&0)`.
    *   Then, demonstrating that `cnj(c'(n)) * c(n)` ranges over all dirichlet characters when `c` does by virtue of the group structure. `VSUM_INJECTION`, `FINITE_DIRICHLET_CHARACTERS`, `IN_ELIM_THM`, and `DIRICHLET_CHARACTER_GROUPMUL` are all relevant in establishing this.
    *   One uses the fact that any Dirichlet character `c` satisfies `cnj(c(n)) * c(n) = Cx(&1)` when `n` is coprime to `d`. This fact relies upon `DIRICHLET_CHARACTER_MUL_CNJ`.
    *   The assumption `coprime(m, d)` for fresh `m` is handled by `DIRICHLET_CHARACTER_EQ_0`.
    *   The proof uses the fact that if `a * b = Cx(&1)` then `a * b * x = a * b * y` implies `x = y`.

### Mathematical insight
This theorem states a fundamental property of Dirichlet characters: When summing the values of all Dirichlet characters (mod d) evaluated at a given integer n, the sum is either zero, or n is coprime to d and all Dirichlet characters evaluate to 1 at n

### Dependencies
*   Definitions:
    *   `dirichlet_character`
*   Theorems/Axioms:
    *   `COMPLEX_VEC_0`
    *   `VSUM_EQ_0`
    *   `IN_ELIM_THM`
    *   `DIRICHLET_CHARACTER_EQ_0`
    *   `o_DEF`
    *   `FINITE_DIRICHLET_CHARACTERS`
    *   `VSUM_COMPLEX_LMUL`
    *   `COMPLEX_RING` ``a * x = x <=> a = Cx(&1) \/ x = Cx(&0)``
    *   `VSUM_INJECTION`
    *   `DIRICHLET_CHARACTER_GROUPMUL`
    *   `FUN_EQ_THM`
    *   `DIRICHLET_CHARACTER_MUL_CNJ`
    *   `COMPLEX_RING` ``a * b = Cx(&1) ==> a * b * x = a * b * y ==> x = y``

### Porting notes (optional)
*   The proof relies heavily on properties of finite groups and complex numbers.
*   The tactic `ASM_CASES_TAC` performs case splitting on an assumption in the assumption list. The porter will need to find an equivalent tactic for doing so in the target proof assistant.
*   `FIRST_X_ASSUM` applies a tactic to the first assumption matching a certain criterion. This could be emulated using assumption indexing or other search techniques.
*   The automation relies on relatively straightforward discharge of equational and membership goals.


---

## DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_POS

### Name of formal statement
DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_POS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_POS = prove
 (`!d n. real(vsum {c | dirichlet_character d c} (\c. c n)) /\
         &0 <= Re(vsum {c | dirichlet_character d c} (\c. c n))`,
  MP_TAC DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_CX; RE_CX; REAL_LE_REFL] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_VSUM;
    SIMP_TAC[FINITE_DIRICHLET_CHARACTERS; RE_VSUM] THEN
    MATCH_MP_TAC SUM_POS_LE] THEN
  ASM_SIMP_TAC[FINITE_DIRICHLET_CHARACTERS; IN_ELIM_THM; REAL_CX; RE_CX] THEN
  REWRITE_TAC[REAL_POS]);;
```
### Informal statement

For all `d` and `n`, it is true that the real part of the sum over all `c` such that `c` is a Dirichlet character modulo `d`, of the values of `c` applied to `n`, is a real number.
Moreover, this real number is greater than or equal to 0.

### Informal sketch
The proof proceeds as follows:

- The initial goal is to prove that for all `d` and `n`, `real(vsum {c | dirichlet_character d c} (\c. c n))` and `&0 <= Re(vsum {c | dirichlet_character d c} (\c. c n))`.
- The proof starts using `DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK`, then applies universal generalization twice and strips the quantifiers and the conjunction.
- The goal is then rewritten using `REAL_CX`, `RE_CX`, and `REAL_LE_REFL`.
- The proof is split by the conjunction.
- The first subgoal, is handled with `REAL_VSUM`, `FINITE_DIRICHLET_CHARACTERS`, `RE_VSUM` and `SUM_POS_LE`.
- The second subgoal, is handled with `FINITE_DIRICHLET_CHARACTERS`, `IN_ELIM_THM`, `REAL_CX`, `RE_CX`, and `REAL_POS`.

### Mathematical insight
The theorem states that if you sum the values of all Dirichlet characters modulo `d` evaluated at `n`, the real part of the sum is a non-negative real number. This builds upon the weaker result `DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK` to strengthen the understanding of Dirichlet characters and their sums.

### Dependencies
- `DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK`
- `REAL_CX`
- `RE_CX`
- `REAL_LE_REFL`
- `REAL_VSUM`
- `FINITE_DIRICHLET_CHARACTERS`
- `RE_VSUM`
- `SUM_POS_LE`
- `IN_ELIM_THM`
- `REAL_POS`


---

## CHARACTER_EXTEND_FROM_SUBGROUP

### Name of formal statement
CHARACTER_EXTEND_FROM_SUBGROUP

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CHARACTER_EXTEND_FROM_SUBGROUP = prove
 (`!f h a d.
        h SUBSET {x | x < d /\ coprime(x,d)} /\
        (1 IN h) /\
        (!x y. x IN h /\ y IN h ==> ((x * y) MOD d) IN h) /\
        (!x. x IN h ==> ?y. y IN h /\ (x * y == 1) (mod d)) /\
        (!x. x IN h ==> ~(f x = Cx(&0))) /\
        (!x y. x IN h /\ y IN h
                 ==> f((x * y) MOD d) = f(x) * f(y)) /\
        a IN {x | x < d /\ coprime(x,d)} DIFF h
        ==> ?f' h'. (a INSERT h) SUBSET h' /\
                    h' SUBSET {x | x < d /\ coprime(x,d)} /\
                    (!x. x IN h ==> f'(x) = f(x)) /\
                    ~(f' a = Cx(&1)) /\
                    1 IN h' /\
                    (!x y. x IN h' /\ y IN h' ==> ((x * y) MOD d) IN h') /\
                    (!x. x IN h' ==> ?y. y IN h' /\ (x * y == 1) (mod d)) /\
                    (!x. x IN h' ==> ~(f' x = Cx(&0))) /\
                    (!x y. x IN h' /\ y IN h'
                           ==> f'((x * y) MOD d) = f'(x) * f'(y))`,
  REWRITE_TAC[IN_ELIM_THM; IN_DIFF; SUBSET] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 < d` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LT_IMP_LE) THEN
  SUBGOAL_THEN `?m x. 0 < m /\ x IN h /\ (a EXP m == x) (mod d)` MP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`phi d`; `1`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[PHI_LOWERBOUND_1_STRONG; LE_1]; ALL_TAC] THEN
    MATCH_MP_TAC FERMAT_LITTLE THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x s. x IN h ==> ((x EXP s) MOD d) IN h` ASSUME_TAC THENL
   [REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
    INDUCT_TAC THEN ASM_SIMP_TAC[EXP; MOD_LT] THEN
    SUBGOAL_THEN `((x * (x EXP s) MOD d) MOD d) IN h` MP_TAC THEN
    ASM_MESON_TAC[MOD_MULT_RMOD; ASSUME `1 <= d`; LE_1];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `am:num` STRIP_ASSUME_TAC) MP_TAC) THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `0 < m ==> m = 1 \/ 2 <= m`))
  THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN UNDISCH_TAC `(a EXP 1 == am) (mod d)` THEN
    ASM_SIMP_TAC[EXP_1; GSYM CONG_MOD_LT; MOD_LT] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o GEN `r:num` o SPEC `r MOD m`) THEN
  ASM_SIMP_TAC[DIVISION; LE_1; NOT_EXISTS_THM] THEN
  REWRITE_TAC[TAUT `~(a /\ b /\ c) <=> b /\ c ==> ~a`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!r x. x IN h /\ (a EXP r == x) (mod d) ==> m divides r`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[DIVIDES_MOD; LE_1] THEN
    REWRITE_TAC[ARITH_RULE `n = 0 <=> ~(0 < n)`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `(a EXP (r MOD m)) MOD d` THEN
    ASM_SIMP_TAC[CONG_RMOD; LE_1; CONG_REFL] THEN
    UNDISCH_TAC `!x. x IN h ==> (?y. y IN h /\ (x * y == 1) (mod d))` THEN
    DISCH_THEN(MP_TAC o SPEC `(a EXP (m * r DIV m)) MOD d`) THEN ANTS_TAC THENL
     [REWRITE_TAC[GSYM EXP_EXP] THEN
      SUBGOAL_THEN
       `(a EXP m) EXP (r DIV m) MOD d = (am EXP (r DIV m)) MOD d`
       (fun th -> ASM_SIMP_TAC[th]) THEN
      ASM_SIMP_TAC[GSYM CONG; LE_1] THEN
      ASM_SIMP_TAC[CONG_LMOD; CONG_EXP; LE_1];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(a EXP r == x) (mod d)` THEN
    MP_TAC(SPECL [`r:num`; `m:num`] DIVISION) THEN ASM_SIMP_TAC[LE_1] THEN
    DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[EXP_ADD] THEN
    DISCH_THEN(MP_TAC o SPEC `y:num` o MATCH_MP
    (NUMBER_RULE `!a. (x:num == y) (mod n) ==> (a * x == a * y) (mod n)`)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
     `(y * e * a == z) (mod n)
      ==> (e * y == 1) (mod n) ==> (a == z) (mod n)`)) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC CONG_TRANS THEN
      EXISTS_TAC `a EXP (m * r DIV m) MOD d * y` THEN
      ASM_SIMP_TAC[CONG_MULT; CONG_REFL; CONG_RMOD; LE_1];
      ALL_TAC] THEN
    ASM_SIMP_TAC[CONG; LE_1];
    ALL_TAC] THEN
  MP_TAC(SPECL [`(f:num->complex) am`; `m:num`]
               EXISTS_COMPLEX_ROOT_NONTRIVIAL) THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:complex` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?g. !x k. x IN h ==> g((x * a EXP k) MOD d) = f(x) * z pow k`
  MP_TAC THENL
   [REWRITE_TAC[MESON[] `(?g. !x a. p x ==> g(f a x) = h a x) <=>
                         (?g. !y x a. p x /\ f a x = y ==> g y = h a x)`] THEN
    REWRITE_TAC[GSYM SKOLEM_THM] THEN
    REWRITE_TAC[MESON[]
     `(!y. ?z. !x k. p x /\ f x k = y ==> z = g x k) <=>
      (!x k x' k'. p x /\ p x' /\ f x k = f x' k' ==> g x k = g x' k')`] THEN
    ONCE_REWRITE_TAC[MESON[]
     `(!x k y j. P x k y j) <=> (!k j x y. P x k y j)`] THEN
    MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `j:num`] THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN
    ASM_SIMP_TAC[GSYM CONG; LE_1] THEN STRIP_TAC THEN
    UNDISCH_TAC `k:num <= j` THEN REWRITE_TAC[LE_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` SUBST_ALL_TAC) THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN
    REWRITE_TAC[COMPLEX_POW_ADD; COMPLEX_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `m divides i` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `!x. x IN h ==> (?y. y IN h /\ (x * y == 1) (mod d))` THEN
      DISCH_THEN(MP_TAC o SPEC `y:num`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(z * x) MOD d` THEN ASM_SIMP_TAC[CONG_RMOD; LE_1] THEN
      MATCH_MP_TAC CONG_MULT_LCANCEL THEN EXISTS_TAC `y * a EXP k` THEN
      REWRITE_TAC[COPRIME_LMUL] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[COPRIME_EXP; COPRIME_SYM]; ALL_TAC] THEN
      UNDISCH_TAC `(x * a EXP k == y * a EXP (k + i)) (mod d)` THEN
      REWRITE_TAC[EXP_ADD] THEN UNDISCH_TAC `(y * z == 1) (mod d)` THEN
      CONV_TAC NUMBER_RULE;
      ALL_TAC] THEN
    REWRITE_TAC[divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:num` SUBST_ALL_TAC) THEN
    ASM_REWRITE_TAC[GSYM COMPLEX_POW_POW] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `f((y * (am EXP r) MOD d) MOD d):complex` THEN CONJ_TAC THENL
     [AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[CONG_MOD_LT] THEN
      MATCH_MP_TAC CONG_TRANS THEN
      EXISTS_TAC `y * (a EXP m) EXP r` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONG_MULT THEN
        ASM_SIMP_TAC[CONG_MULT; CONG_LMOD; CONG_REFL; LE_1] THEN
        MATCH_MP_TAC CONG_EXP THEN ASM_MESON_TAC[CONG_SYM];
        ALL_TAC] THEN
      MATCH_MP_TAC CONG_MULT_LCANCEL THEN EXISTS_TAC `a EXP k` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[COPRIME_EXP; COPRIME_SYM]; ALL_TAC] THEN
      UNDISCH_TAC `(x * a EXP k == y * a EXP (k + m * r)) (mod d)` THEN
      REWRITE_TAC[EXP_ADD; EXP_EXP] THEN CONV_TAC NUMBER_RULE;
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN
    SPEC_TAC(`r:num`,`s:num`) THEN INDUCT_TAC THEN
    ASM_SIMP_TAC[EXP; MOD_LT; complex_pow; COMPLEX_MUL_RID] THENL
     [UNDISCH_TAC
       `!x y. x IN h /\ y IN h ==> f ((x * y) MOD d):complex = f x * f y` THEN
      DISCH_THEN(MP_TAC o SPECL [`1`; `1`]) THEN
      ASM_SIMP_TAC[MULT_CLAUSES; MOD_LT] THEN
      UNDISCH_TAC `!x:num. x IN h ==> ~(f x = Cx (&0))` THEN
      DISCH_THEN(MP_TAC o SPEC `1`) THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `f((am * (am EXP s) MOD d) MOD d):complex` THEN CONJ_TAC THENL
     [ALL_TAC; ASM_SIMP_TAC[]] THEN
    AP_TERM_TAC THEN ASM_SIMP_TAC[MOD_MULT_RMOD; ASSUME `1 <= d`; LE_1];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:num->complex` THEN
  DISCH_THEN (LABEL_TAC "*") THEN
  EXISTS_TAC `{(x * a EXP k) MOD d | x IN h /\ k IN (:num)}` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT; IN_UNIV] THEN
    X_GEN_TAC `x:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [MAP_EVERY EXISTS_TAC [`1`; `1`];
      MAP_EVERY EXISTS_TAC [`x:num`; `0`]] THEN
    ASM_SIMP_TAC[EXP_1; MULT_CLAUSES; EXP; MOD_LT];
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`y:num`; `x:num`; `k:num`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_SIMP_TAC[DIVISION; LE_1; COPRIME_LMOD; COPRIME_LMUL] THEN
    ASM_MESON_TAC[COPRIME_EXP; COPRIME_SYM];
    X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    REMOVE_THEN "*" (MP_TAC o SPECL [`x:num`; `0`]) THEN
    ASM_SIMP_TAC[MOD_LT; EXP; MULT_CLAUSES; complex_pow; COMPLEX_MUL_RID];
    REMOVE_THEN "*" (MP_TAC o SPECL [`1`; `1`]) THEN
    ASM_SIMP_TAC[EXP_1; MULT_CLAUSES; MOD_LT; COMPLEX_POW_1] THEN
    UNDISCH_TAC `!x y. x IN h /\ y IN h ==> f ((x * y) MOD d) = f x * f y` THEN
    DISCH_THEN(MP_TAC o SPECL [`1`; `1`]) THEN
    ASM_SIMP_TAC[MULT_CLAUSES; MOD_LT] THEN
    UNDISCH_TAC `~(z = Cx(&1))` THEN CONV_TAC COMPLEX_RING;
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
    MAP_EVERY EXISTS_TAC [`1`; `0`] THEN
    ASM_SIMP_TAC[EXP; MULT_CLAUSES; MOD_LT];
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV; LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`r:num`; `s:num`; `x:num`; `k:num`; `y:num`; `j:num`] THEN
    STRIP_TAC THEN REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    MAP_EVERY EXISTS_TAC [`(x * y) MOD d`; `j + k:num`] THEN
    ASM_SIMP_TAC[MOD_MULT_LMOD; MOD_MULT_RMOD; LE_1] THEN
    REWRITE_TAC[EXP_ADD; MULT_AC];
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`y:num`; `x:num`; `k:num`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    UNDISCH_TAC `!x. x IN h ==> (?y. y IN h /\ (x * y == 1) (mod d))` THEN
    DISCH_THEN(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(z * a EXP ((phi d - 1) * k)) MOD d` THEN
    REWRITE_TAC[LEFT_EXISTS_AND_THM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CONG_TRANS THEN
    EXISTS_TAC `(x * a EXP k) * (z * a EXP ((phi d - 1) * k))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONG_MULT THEN ASM_SIMP_TAC[CONG_MOD; LE_1]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[ARITH_RULE
     `(x * a) * (z * ak):num = (x * z) * (a * ak)`] THEN
    GEN_REWRITE_TAC (LAND_CONV) [ARITH_RULE `1 = 1 * 1`] THEN
    MATCH_MP_TAC CONG_MULT THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM EXP_ADD] THEN
    SUBGOAL_THEN `k + (phi d - 1) * k = phi(d) * k` SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `k + a * k = (a + 1) * k`] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[SUB_ADD; PHI_LOWERBOUND_1_STRONG];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM EXP_EXP] THEN SUBST1_TAC(SYM(SPEC `k:num` EXP_ONE)) THEN
    MATCH_MP_TAC CONG_EXP THEN ASM_SIMP_TAC[FERMAT_LITTLE];
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC[COMPLEX_ENTIRE; COMPLEX_POW_EQ_0] THEN
    UNDISCH_TAC `!x:num. x IN h ==> ~(f x = Cx (&0))` THEN
    DISCH_THEN(MP_TAC o SPEC `am:num`) THEN ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(ASSUME `z pow m = f(am:num)`)) THEN
    REWRITE_TAC[COMPLEX_POW_EQ_0] THEN ASM_SIMP_TAC[LE_1];
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV; LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`r:num`; `s:num`; `x:num`; `k:num`; `y:num`; `j:num`] THEN
    STRIP_TAC THEN REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `g(((x * y) MOD d * a EXP (k + j)) MOD d):complex` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN ASM_SIMP_TAC[MOD_MULT_LMOD; MOD_MULT_RMOD; LE_1] THEN
      REWRITE_TAC[EXP_ADD; MULT_AC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[COMPLEX_POW_ADD; COMPLEX_MUL_AC]]);;
```

### Informal statement
For all `f`, `h`, `a`, and `d`, if:
1. `h` is a subset of the set of numbers less than `d` and coprime to `d`, and
2. 1 is in `h`, and
3. for all `x` and `y`, if `x` is in `h` and `y` is in `h`, then `(x * y) MOD d` is in `h`, and
4. for all `x`, if `x` is in `h`, then there exists a `y` such that `y` is in `h` and `(x * y == 1) (mod d)`, and
5. for all `x`, if `x` is in `h`, then `f(x)` is not equal to the complex number 0, and
6. for all `x` and `y`, if `x` is in `h` and `y` is in `h`, then `f((x * y) MOD d)` is equal to `f(x) * f(y)`, and
7. `a` is in the set of numbers less than `d` and coprime to `d` but not in `h`,

then there exist `f'` and `h'` such that:
1. `(a INSERT h)` is a subset of `h'`, and
2. `h'` is a subset of the set of numbers less than `d` and coprime to `d`, and
3. for all `x`, if `x` is in `h`, then `f'(x) = f(x)`, and
4. `f'(a)` is not equal to the complex number 1, and
5. 1 is in `h'`, and
6. for all `x` and `y`, if `x` is in `h'` and `y` is in `h'`, then `(x * y) MOD d` is in `h'`, and
7. for all `x`, if `x` is in `h'`, then there exists a `y` such that `y` is in `h'` and `(x * y == 1) (mod d)`, and
8. for all `x`, if `x` is in `h'`, then `f'(x)` is not equal to the complex number 0, and
9. for all `x` and `y`, if `x` is in `h'` and `y` is in `h'`, then `f'((x * y) MOD d)` is equal to `f'(x) * f'(y)`.

### Informal sketch
The proof proceeds as follows:
- It starts by rewriting the goal using simplification rules and then stripping quantifiers.
- It assumes that `1 < d`.
- It proves the existence of `m` and `x` such that `0 < m`, `x` is in `h`, and `(a EXP m == x) (mod d)` by setting `m` to `phi d` (Euler's totient function of `d`) and `x` to 1. Fermat's Little Theorem is used here.
- It proves that `!x s. x IN h ==> ((x EXP s) MOD d) IN h` by induction on `s`.
- It chooses `m` such that `(a EXP m == am) (mod d)`.
- It considers two cases: `m = 1` or `2 <= m`.
- If `m = 1`, it simplifies using `EXP_1` and congruence modulo, then finishes.
- If `2 <= m`, it uses the division algorithm to write an arbitrary number `r` as `m * (r DIV m) + (r MOD m)`.
- It proves that `!r x. x IN h /\ (a EXP r == x) (mod d) ==> m divides r`, showing that if `a^r` is congruent to an element of `h`, then `m` divides `r`. This is done by strong congruence arguments and leveraging the group structure of `h`.
- It applies `EXISTS_COMPLEX_ROOT_NONTRIVIAL` (which states that for any number there exists a nontrivial complex root) to get `z` such that `z pow m = Cx(&1)` and `~(z = Cx(&1))`.
- It proves the existence of `g` such that `!x k. x IN h ==> g((x * a EXP k) MOD d) = f(x) * z pow k`, essentially defining the extension character `g` by specifying its values on elements of the form `x * a^k`.
  - It uses `WLOG_LE` to reduce the proof to the case `k <= j`, where `k` and `j` are the powers of `a` appearing in `f(x * a^k)` and `f(a * a^j)`.
  - It shows that `m divides i`, where `i = j - k`.
  - It applies `EXISTS_COMPLEX_ROOT_NONTRIVIAL` with `am` as the power.
- It uses `MONO_EXISTS` and picks `g`.
- It proves that `{(x * a EXP k) MOD d | x IN h /\ k IN (:num)}` satisfies the condition of `h'`.

### Mathematical insight
This theorem provides a method to extend a character (a homomorphism into the complex numbers) defined on a subgroup of the multiplicative group modulo `d` to a larger subgroup, by adjoining an element `a`. The key insight is that the multiplicative order of 'a' modulo 'd' gives a relation that can be used to define the character on the extended subgroup consistently. Specifically, it shows how to construct a new subgroup `h'` containing both `h` and `a`, and a new character `f'` defined on `h'` which agrees with `f` on `h`. The `EXISTS_COMPLEX_ROOT_NONTRIVIAL` theorem is used to ensure that the necessary complex root exists to define the character extension. This is important in representation theory and character theory.

### Dependencies
- `IN_ELIM_THM`
- `IN_DIFF`
- `SUBSET`
- `PHI_LOWERBOUND_1_STRONG`
- `LE_1`
- `FERMAT_LITTLE`
- `RIGHT_FORALL_IMP_THM`
- `EXP`
- `MOD_LT`
- `MOD_MULT_RMOD`
- `DIVISION`
- `NOT_EXISTS_THM`
- `DIVIDES_MOD`
- `GSYM EXP_EXP`
- `CONG_RMOD`
- `EXISTS_COMPLEX_ROOT_NONTRIVIAL`
- `COMPLEX_POW_ADD`
- `COMPLEX_MUL_ASSOC`
- `divides`
- `GSYM COMPLEX_POW_POW`
- `EXP_ADD`
- `COMPLEX_MUL_RID`
- `complex_pow`
- `TAUT`
- `GSYM CONG`
- `CONG_LMOD`
- `CONG_EXP`
- `EQ_TRANS`
- `CONG_MULT`
- `COPRIME_EXP`
- `COPRIME_SYM`
- `CONG_MULT_LCANCEL`
- `CONG_MOD`
- `EXP_EXP`
- `GSYM EXP_ADD`
- `COPRIME_LMOD`
- `COPRIME_LMUL`
- `EXP_ONE`
- `COMPLEX_ENTIRE`
- `COMPLEX_POW_EQ_0`
- `MULT_AC`
### Porting notes (optional)
- The core of the proof relies on properties of modular arithmetic and complex numbers, notably the existence of roots of unity. Ensure that the target proof assistant has similar theorems available, or that they can be derived.
- The tactic `WLOG_LE` seems to do with without loss of generality, this might be applicable more broadly in other proof assistants if a similar approach is possible.
- The assumptions about coprimality will need to be carefully ported, ensuring that the definitions of `coprime` and related lemmas are available.


---

## DIRICHLET_CHARACTER_DISCRIMINATOR

### Name of formal statement
DIRICHLET_CHARACTER_DISCRIMINATOR

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_DISCRIMINATOR = prove
 (`!d n. 1 < d /\ ~((n == 1) (mod d))
          ==> ?c. dirichlet_character d c /\ ~(c n = Cx(&1))`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP LT_IMP_LE) THEN
  ASM_CASES_TAC `coprime(n,d)` THENL
   [ALL_TAC;
    EXISTS_TAC `chi_0 d` THEN
    ASM_REWRITE_TAC[DIRICHLET_CHARACTER_CHI_0; chi_0] THEN
    CONV_TAC COMPLEX_RING] THEN
  MP_TAC(ISPECL [`\n:num. Cx(&1)`; `{1}`; `n MOD d`; `d:num`]
                CHARACTER_EXTEND_FROM_SUBGROUP) THEN
  ASM_SIMP_TAC[IN_SING; IN_ELIM_THM; IN_DIFF] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[SUBSET; MULT_CLAUSES; MOD_LT; LE_1; IN_SING;
                 IN_ELIM_THM; DIVISION; COPRIME_LMOD; CONG_MOD_LT;
                 COMPLEX_MUL_LID; CX_INJ; REAL_OF_NUM_EQ; ARITH] THEN
    ASM_MESON_TAC[COPRIME_1; COPRIME_SYM; CONG_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f0:num->complex`; `h0:num->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!m. m <= CARD {x | x < d /\ coprime(x,d)}
        ==> ?f h. h SUBSET {x | x < d /\ coprime(x,d)} /\
                 (1 IN h) /\ (n MOD d) IN h /\
                 (!x y. x IN h /\ y IN h ==> ((x * y) MOD d) IN h) /\
                 (!x. x IN h ==> ?y. y IN h /\ (x * y == 1) (mod d)) /\
                 ~(f(n MOD d) = Cx(&1)) /\
                 (!x. x IN h ==> ~(f x = Cx(&0))) /\
                 (!x y. x IN h /\ y IN h
                          ==> f((x * y) MOD d) = f(x) * f(y)) /\
                 m <= CARD h`
  MP_TAC THENL
   [MATCH_MP_TAC num_WF THEN X_GEN_TAC `m:num` THEN
    DISCH_THEN(LABEL_TAC "*") THEN DISCH_TAC THEN
    ASM_CASES_TAC `m = 0` THENL
     [MAP_EVERY EXISTS_TAC [`f0:num->complex`; `h0:num->bool`] THEN
      ASM_REWRITE_TAC[LE_0] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP
     (MATCH_MP (ARITH_RULE `~(m = 0) ==> m - 1 < m`) (ASSUME `~(m = 0)`))) THEN
    ASM_SIMP_TAC[ARITH_RULE `x <= n ==> x - 1 <= n`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`f:num->complex`; `h:num->bool`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `m <= CARD(h:num->bool)` THENL
     [MAP_EVERY EXISTS_TAC [`f:num->complex`; `h:num->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ASSUME `h SUBSET {x | x < d /\ coprime (x,d)}`) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> ~(s = t) ==> ?a. a IN t /\ ~(a IN s)`)) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[IN_ELIM_THM]] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:num` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`f:num->complex`; `h:num->bool`; `a:num`; `d:num`]
                CHARACTER_EXTEND_FROM_SUBGROUP) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `ff:num->complex` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `hh:num->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD((a:num) INSERT h)` THEN
    SUBGOAL_THEN `FINITE(h:num->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{x | x IN {x | x < d} /\ coprime(x,d)}` THEN
      SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG_LT] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[CARD_CLAUSES] THEN
      UNDISCH_TAC `m - 1 <= CARD(h:num->bool)` THEN ARITH_TAC;
      MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{x | x IN {x | x < d} /\ coprime(x,d)}` THEN
      SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG_LT] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `CARD {x | x < d /\ coprime(x,d)}`) THEN
  REWRITE_TAC[LE_REFL] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:num->complex`; `h:num->bool`] THEN
  ASM_CASES_TAC `h = {x | x < d /\ coprime (x,d)}` THENL
   [ALL_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[CONJ_ASSOC] THEN MATCH_MP_TAC(TAUT `~b ==> a /\ b ==> c`) THEN
    REWRITE_TAC[NOT_LE] THEN MATCH_MP_TAC CARD_PSUBSET THEN
    ASM_REWRITE_TAC[PSUBSET] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{x:num | x < d}` THEN
    SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG_LT] THEN SET_TAC[]] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  STRIP_TAC THEN
  EXISTS_TAC `\n. if coprime(n,d) then f(n MOD d) else Cx(&0)` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[dirichlet_character] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `x:num` THENL
   [REWRITE_TAC[NUMBER_RULE `coprime(x + d:num,d) <=> coprime(x,d)`] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[GSYM CONG; LE_1] THEN CONV_TAC NUMBER_RULE;
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[COPRIME_LMOD; DIVISION; LE_1];
    X_GEN_TAC `y:num` THEN REWRITE_TAC[COPRIME_LMUL] THEN
    MAP_EVERY ASM_CASES_TAC [`coprime(x,d)`; `coprime(y,d)`] THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `f(((x MOD d) * (y MOD d)) MOD d):complex` THEN CONJ_TAC THENL
     [AP_TERM_TAC THEN ASM_SIMP_TAC[MOD_MULT_MOD2; LE_1];
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[DIVISION; COPRIME_LMOD; LE_1]]]);;
```

### Informal statement
For all natural numbers `d` and `n`, if `d` is greater than 1 and `n` is not congruent to 1 modulo `d`, then there exists a complex-valued function `c` such that `c` is a Dirichlet character modulo `d`, and `c(n)` is not equal to 1.

### Informal sketch
*   The proof proceeds by assuming `1 < d` and `~(n == 1) (mod d)`.
*   Case split on whether `n` and `d` are coprime.
*   If they are coprime, we simply use the trivial Dirichlet character `chi_0 d`, which maps any number coprime to `d` to 1.  Since `n` is not congruent to 1 modulo `d`, `chi_0 d` suffices.
*   If they are not coprime, we extend a character `f` defined on a subgroup `h` of `Z_d^*`. The subgroup `h` contains 1 and `n mod d`. The existence of such an `f` and `h` satisfying certain conditions is shown by induction on the cardinality of `Z_d^*`, i.e. `CARD {x | x < d /\ coprime(x,d)}`.
* The base case is when the cardinality is 0, meaning we should prove it when `m = 0`. Trivial character is chosen in this case.
* For the induction step, we assume the existence of `f` and `h` for `m`. If `m <= CARD h`, we can simply reuse the previous result since we have already `f` and `h`. If `m > CARD h` and `h` is not the entire group, we extend the existing character from `h` to `h INSERT {a}` where `a IN {x | x < d /\ coprime (x,d)} /\ ~(a IN h)`. Induction goes through because `CARD h` is at least the size of `m-1`.
*   Then we define a Dirichlet character `c` from `f`: `c n = if coprime(n,d) then f(n MOD d) else Cx(&0)`. This is shown to satisfy the properties of a Dirichlet character. Key idea: extend character from subgroup.

### Mathematical insight
The theorem states that for any modulus `d > 1` and any number `n` not congruent to 1 modulo `d`, we can find a Dirichlet character that distinguishes `n` from 1. This is key to separating out elements congruent to 1 modulo `d` when analyzing the distribution of primes. If all Dirichlet characters evaluated as 1 you couldn't distinguish this element by analytic means.

### Dependencies
*   `DIRICHLET_CHARACTER_CHI_0`
*   `chi_0`
*   `CHARACTER_EXTEND_FROM_SUBGROUP`
*   `IN_SING`
*   `IN_ELIM_THM`
*   `IN_DIFF`
*   `SUBSET`
*   `MULT_CLAUSES`
*   `MOD_LT`
*   `LE_1`
*   `DIVISION`
*   `COPRIME_LMOD`
*   `CONG_MOD_LT`
*   `COMPLEX_MUL_LID`
*   `CX_INJ`
*   `REAL_OF_NUM_EQ`
*   `ARITH`
*   `COPRIME_1`
*   `COPRIME_SYM`
*   `CONG_REFL`
*   `num_WF`
*   `MONO_EXISTS`
*   `FINITE_SUBSET`
*   `FINITE_RESTRICT`
*   `FINITE_NUMSEG_LT`
*   `CARD_CLAUSES`
*   `CARD_SUBSET`
*   `CARD_PSUBSET`
*   `PSUBSET`
*   `NUMBER_RULE coprime(x + d:num,d) <=> coprime(x,d)`
*   `COPRIME_LMUL`
*   `COMPLEX_MUL_LZERO`
*   `COMPLEX_MUL_RZERO`
*   `EQ_TRANS`
*   `MOD_MULT_MOD2`
* `dirichlet_character`
* `CONG`

### Porting notes (optional)
The most complex aspect to port involves `CHARACTER_EXTEND_FROM_SUBGROUP`, which represents a non-trivial algebraic construction. This will likely require careful attention in other proof assistants. Also, the heavy reliance on arithmetic tactics such as ARITH_TAC may need to be adjusted depending on what tactics are available in the target proof assistant.


---

## DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_INEXPLICIT

### Name of formal statement
DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_INEXPLICIT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_INEXPLICIT = prove
 (`!d n. vsum {c | dirichlet_character d c} (\c. c n) =
                if (n == 1) (mod d)
                then Cx(&(CARD {c | dirichlet_character d c}))
                else Cx(&0)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `d = 0` THENL
   [ASM_REWRITE_TAC[CONG_MOD_0; DIRICHLET_CHARACTER_0; SET_RULE
     `{x | x = a} = {a}`] THEN
    SIMP_TAC[VSUM_CLAUSES; CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY] THEN
    REWRITE_TAC[chi_0; COPRIME_0; VECTOR_ADD_RID] THEN REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  ASM_CASES_TAC `d = 1` THENL
   [ASM_REWRITE_TAC[CONG_MOD_1; DIRICHLET_CHARACTER_1] THEN
    REWRITE_TAC[GSYM FUN_EQ_THM; ETA_AX] THEN
    ASM_REWRITE_TAC[SET_RULE `{x | x = a} = {a}`] THEN
    SIMP_TAC[VSUM_CLAUSES; CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY] THEN
    REWRITE_TAC[VECTOR_ADD_RID; ARITH];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `vsum {c | dirichlet_character d c} (\c. Cx(&1))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_1; DIRICHLET_CHARACTER_CONG];
      SIMP_TAC[FINITE_DIRICHLET_CHARACTERS; VSUM_CONST] THEN
      REWRITE_TAC[COMPLEX_CMUL; COMPLEX_MUL_RID]];
    MP_TAC(SPECL [`d:num`; `n:num`]
      DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK) THEN
    ASM_MESON_TAC[DIRICHLET_CHARACTER_DISCRIMINATOR;
                  ARITH_RULE `~(d = 0) /\ ~(d = 1) ==> 1 < d`]]);;
```

### Informal statement
For all natural numbers `d` and `n`, the sum, over all Dirichlet characters `c` modulo `d`, of the complex number obtained by applying the character `c` to `n`, is equal to the complex number representation of the cardinality of the set of Dirichlet characters modulo `d` if `n` is congruent to 1 modulo `d`, and is equal to the complex number representation of 0 otherwise.

### Informal sketch
The proof proceeds by case analysis on the value of `d`.
- Case `d = 0`: Simplify using the definition of `dirichlet_character d c` and congruence modulo 0. The sum reduces to a single term corresponding to the zero character. Then use arithmetic facts to complete the proof.
- Case `d = 1`: Simplify using the definition of `dirichlet_character d c` and congruence modulo 1. The sum reduces to a single term. Then use arithmetic facts to complete the proof.
- Case `d > 1`: Perform case analysis on the condition `n == 1) (mod d)`.
  - If `n` is congruent to 1 modulo `d`, transform the sum into the sum of `Cx(&1)` over all Dirichlet characters modulo `d`. Simplify using the fact that the sum of a constant function is the constant times the size of the set. The result follows.
  - If `n` is not congruent to 1 modulo `d`, apply the theorem `DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK` and properties of `dirichlet_character` to show that the sum is 0.

### Mathematical insight
This theorem gives the second orthogonality relation for Dirichlet characters. It states that summing the values of all Dirichlet characters modulo `d` at a particular value `n` gives 0, unless `n` is congruent to 1 modulo `d`, in which case it returns the number of Dirichlet characters modulo `d`. This is a crucial result in analytic number theory, often used in proving results about the distribution of primes.

### Dependencies
- `CONG_MOD_0`
- `DIRICHLET_CHARACTER_0`
- `SET_RULE`
- `VSUM_CLAUSES`
- `CARD_CLAUSES`
- `FINITE_RULES`
- `NOT_IN_EMPTY`
- `chi_0`
- `COPRIME_0`
- `VECTOR_ADD_RID`
- `ARITH`
- `CONG_MOD_1`
- `DIRICHLET_CHARACTER_1`
- `FUN_EQ_THM`
- `ETA_AX`
- `FINITE_DIRICHLET_CHARACTERS`
- `VSUM_CONST`
- `COMPLEX_CMUL`
- `COMPLEX_MUL_RID`
- `DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK`
- `DIRICHLET_CHARACTER_DISCRIMINATOR`
- `DIRICHLET_CHARACTER_EQ_1`
- `DIRICHLET_CHARACTER_CONG`
- `IN_ELIM_THM`


---

## DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS

### Name of formal statement
DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS = prove
 (`!d n. 1 <= d
         ==> vsum {c | dirichlet_character d c} (\c. c(n)) =
                if (n == 1) (mod d) then Cx(&(phi d)) else Cx(&0)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_INEXPLICIT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\c n. (c:num->complex) n`; `{c | dirichlet_character d c}`;
                 `1..d`;] VSUM_SWAP) THEN
  SIMP_TAC[DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_INEXPLICIT;
           DIRICHLET_CHARACTER_SUM_OVER_NUMBERS; FINITE_NUMSEG;
           FINITE_DIRICHLET_CHARACTERS; ETA_AX] THEN
  REWRITE_TAC[VSUM_DELTA; GSYM COMPLEX_VEC_0] THEN
  REWRITE_TAC[IN_ELIM_THM; DIRICHLET_CHARACTER_CHI_0] THEN
  DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[GSYM VSUM_RESTRICT_SET; FINITE_NUMSEG] THEN
  SUBGOAL_THEN `{j | j IN 1..d /\ (j == 1) (mod d)} = {1}`
   (fun th -> SIMP_TAC[th; VSUM_SING]) THEN
  REWRITE_TAC[EXTENSION; IN_SING; IN_ELIM_THM; IN_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN EQ_TAC THEN ASM_SIMP_TAC[LE_REFL; CONG_REFL] THEN
  ASM_CASES_TAC `d = 1` THEN ASM_SIMP_TAC[CONG_MOD_1; LE_ANTISYM] THEN
  ASM_CASES_TAC `k:num = d` THENL
   [ASM_REWRITE_TAC[NUMBER_RULE `(d == 1) (mod d) <=> d divides 1`] THEN
    ASM_REWRITE_TAC[DIVIDES_ONE];
    STRIP_TAC THEN MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `d:num` THEN
    ASM_REWRITE_TAC[LT_LE]]);;
```

### Informal statement
For all positive integers `d` and all natural numbers `n`, if `d` is greater than or equal to 1, then the sum, over all Dirichlet characters modulo `d`, of each character `c` evaluated at `n`, is equal to `Cx(&(phi d))` if `n` is congruent to 1 modulo `d`, and is equal to `Cx(&0)` otherwise.

### Informal sketch
The proof proceeds as follows:
- Rewrite using `DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_INEXPLICIT` to express the sum over all Dirichlet characters as a restricted sum over numbers from `1` to `d` that are relatively prime to `d`.
- Perform case analysis based on the condition `(n == 1) (mod d)`.
- Swap the summation order (sum over numbers and sum over characters) using `VSUM_SWAP`.
- Simplify using `DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_INEXPLICIT` and `DIRICHLET_CHARACTER_SUM_OVER_NUMBERS`.
- Apply `VSUM_DELTA` to simplify the sum, which results in cases depending on whether the element being summed over is zero or one.
- Simplify utilizing `DIRICHLET_CHARACTER_CHI_0`.
- Simplify the set `{j | j IN 1..d /\ (j == 1) (mod d)}` to `{1}` for cases where `(n == 1) (mod d)`.
- Perform case analysis on `d = 1` and `k = d` for the condition `(n == 1) (mod d)`.
- The proof uses rewriting and simplification tactics to massage the expression into the desired form.

### Mathematical insight
This theorem gives a closed-form expression for the sum of all Dirichlet characters modulo `d`, evaluated at a natural number `n`. This is zero unless `n` is congruent to 1 modulo `d`, in which case the sum is `phi(d)`, where `phi` is Euler's totient function, representing the number of integers less than `d` that are relatively prime to `d`. This result highlights the orthogonality properties of Dirichlet characters.

### Dependencies
- `DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_INEXPLICIT`
- `DIRICHLET_CHARACTER_SUM_OVER_NUMBERS`
- `FINITE_NUMSEG`
- `FINITE_DIRICHLET_CHARACTERS`
- `ETA_AX`
- `VSUM_DELTA`
- `COMPLEX_VEC_0`
- `IN_ELIM_THM`
- `DIRICHLET_CHARACTER_CHI_0`
- `VSUM_RESTRICT_SET`
- `VSUM_SING`
- `EXTENSION`
- `IN_SING`
- `IN_NUMSEG`
- `LE_REFL`
- `CONG_REFL`
- `CONG_MOD_1`
- `LE_ANTISYM`
- `NUMBER_RULE`
- `DIVIDES_ONE`
- `LT_LE`

### Porting notes (optional)
- The definition of `dirichlet_character` and the related infrastructure need to be ported first.
- The handling of complex numbers (`Cx`) might require specific adaptations depending on the target proof assistant's library.
- The set theory and summation tactics might need to be adjusted based on the target system's automation capabilities.


---

## Lfunction_DEF

### Name of formal statement
Lfunction_DEF

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let Lfunction_DEF = new_definition
 `Lfunction c = infsum (from 1) (\n. c(n) / Cx(&n))`;;
```

### Informal statement
The L-function `Lfunction` of a sequence `c` of complex numbers is defined as the infinite sum, starting from `n = 1`, of the terms `c(n) / Cx(&n)`, where `Cx` converts a real number to a complex number.

### Informal sketch
The definition introduces the `Lfunction` by directly equating it to an infinite sum using the `infsum` operator. The function being summed maps each natural number `n` (starting from 1) to the complex number obtained by dividing the `n`-th term of the sequence `c` (i.e., `c(n)`) by the complex number `n` (represented as `Cx(&n)`).

### Mathematical insight
The `Lfunction` definition represents an L-series evaluated at $s=1$. L-functions are fundamental objects in number theory, and this definition provides a concrete instance of an L-function based on an arbitrary sequence of complex numbers. It is a key step to define a Dirichlet L-function.

### Dependencies
- `infsum`
- `from`
- `Cx`


---

## BOUNDED_LFUNCTION_PARTIAL_SUMS

### Name of formal statement
BOUNDED_LFUNCTION_PARTIAL_SUMS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BOUNDED_LFUNCTION_PARTIAL_SUMS = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> bounded {vsum (1..n) c | n IN (:num)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ONCE_REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_SUM_MOD th]) THEN
  MATCH_MP_TAC BOUNDED_SUBSET THEN
  EXISTS_TAC `IMAGE (\n. vsum(1..n) c:complex) (0..d)` THEN
  SIMP_TAC[FINITE_IMP_BOUNDED; FINITE_IMAGE; FINITE_NUMSEG] THEN
  REWRITE_TAC[SIMPLE_IMAGE; SUBSET; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_UNIV; IN_IMAGE] THEN
  EXISTS_TAC `n MOD d` THEN REWRITE_TAC[IN_NUMSEG; LE_0] THEN
  ASM_MESON_TAC[LT_IMP_LE; DIVISION;
                DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL]);;
```

### Informal statement
For all Dirichlet characters `d` and `c`, if `c` is a Dirichlet character with modulus `d` and `c` is not the principal character `chi_0 d`, then the set of partial sums of `c`, `{vsum (1..n) c | n IN (:num)}`, is bounded.

### Informal sketch
The proof demonstrates that for any non-principal Dirichlet character `c` modulo `d`, the set of its partial sums is bounded.
- Start by assuming `d` and `c` are such that `c` is a Dirichlet character modulo `d` and `c` is not the principal character `chi_0 d`.
- Apply the theorem `DIRICHLET_CHARACTER_SUM_MOD` to rewrite the partial sums. This theorem provides a property about the sum of Dirichlet characters.
- Use `BOUNDED_SUBSET` to show that if the image of the partial sums under a function is finite then it is a bounded subset.
- Show the existence of a set, namely `IMAGE (\n. vsum(1..n) c:complex) (0..d)`, over which a partial sum lies.
- Simplify using `FINITE_IMP_BOUNDED`, `FINITE_IMAGE`, and `FINITE_NUMSEG` to show the set is bounded.
- Rewrite using `SIMPLE_IMAGE`, `SUBSET`, and `FORALL_IN_IMAGE`.
- Generalize on `n:num` and rewrite using `IN_UNIV` and `IN_IMAGE`.
- Show the existence of `n MOD d`, and rewrite using `IN_NUMSEG` and `LE_0`.
- Finally, use `ASM_MESON_TAC` with auxiliary theorems about divisibility and the nature of non-principal Dirichlet characters to complete the proof.

### Mathematical insight
This theorem is related to the behavior of L-functions. Dirichlet characters are used to construct Dirichlet L-functions, and this theorem indicates a bound on the partial sums of a non-principal Dirichlet character. Boundedness of the partial sums has implications in the analysis of convergence and analytic properties of the associated L-function. The condition that the character is non-principal (i.e., not the trivial character) is crucial, as the sum of the principal character grows linearly with `n`.

### Dependencies
- `DIRICHLET_CHARACTER_SUM_MOD`
- `BOUNDED_SUBSET`
- `FINITE_IMP_BOUNDED`
- `FINITE_IMAGE`
- `FINITE_NUMSEG`
- `SIMPLE_IMAGE`
- `SUBSET`
- `FORALL_IN_IMAGE`
- `IN_UNIV`
- `IN_IMAGE`
- `IN_NUMSEG`
- `LE_0`
- `LT_IMP_LE`
- `DIVISION`
- `DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL`

### Porting notes (optional)
- The `ASM_MESON_TAC` call at the end suggests discharging several background assumptions. When porting, it might be necessary to explicitly state and prove these before calling the automated reasoner in the target system.
- The definition of `vsum` should be verified in the target system, as it could be implemented differently across proof assistants.


---

## LFUNCTION

### Name of formal statement
LFUNCTION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LFUNCTION = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> ((\n. c(n) / Cx(&n)) sums (Lfunction c)) (from 1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SIMP_TAC[Lfunction_DEF; SUMS_INFSUM] THEN
  REWRITE_TAC[complex_div] THEN MATCH_MP_TAC SERIES_DIRICHLET_COMPLEX THEN
  REPEAT(EXISTS_TAC `1`) THEN FIRST_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP BOUNDED_LFUNCTION_PARTIAL_SUMS th]) THEN
  REWRITE_TAC[LIM_INV_N; GSYM CX_INV; REAL_CX; RE_CX] THEN
  SIMP_TAC[REAL_LE_INV2; REAL_OF_NUM_LE; REAL_OF_NUM_LT; LE_1; LE_ADD]);;
```

### Informal statement
For all natural numbers `d` and functions `c`, if `c` is a Dirichlet character modulo `d` and `c` is not the principal character `chi_0 d`, then the series defined by the function that maps `n` to `c(n) / Cx(&n)` sums to `Lfunction c` starting from 1.

### Informal sketch
The proof demonstrates that the series with terms `c(n) / Cx(&n)` converges to `Lfunction c`, assuming `c` is a non-principal Dirichlet character.

- Start by assuming `c` is a Dirichlet character modulo `d` and `c` is not the principal character `chi_0 d`.
- Simplify using the definition `Lfunction_DEF` and `SUMS_INFSUM`. `Lfunction_DEF` expands the definition of the L-function, and `SUMS_INFSUM` provides properties of infinite sums.
- Rewrite using the definition of complex division `complex_div`.
- Apply the theorem `SERIES_DIRICHLET_COMPLEX`, which likely states the convergence of Dirichlet series under certain conditions.
- Existentially quantify `1`.
- Apply the theorem `BOUNDED_LFUNCTION_PARTIAL_SUMS` to show boundedness of the partial sums of L-function.
- Rewrite with `LIM_INV_N`, `GSYM CX_INV`, `REAL_CX`, and `RE_CX` to manipulate the limit and complex numbers.
- Simplify with `REAL_LE_INV2`, `REAL_OF_NUM_LE`, `REAL_OF_NUM_LT`, `LE_1`, and `LE_ADD` which perform real number arithmetic and inequalities.

### Mathematical insight
The theorem establishes the convergence of the Dirichlet series associated with a non-principal Dirichlet character to its corresponding L-function. This is a fundamental result in analytic number theory. The L-function is defined as an infinite sum (Dirichlet series), and this theorem provides a concrete way to evaluate it.

### Dependencies
- Definitions: `Lfunction_DEF`
- Theorems: `SUMS_INFSUM`, `SERIES_DIRICHLET_COMPLEX`, `BOUNDED_LFUNCTION_PARTIAL_SUMS`, `LIM_INV_N`
- Axioms/Theorems (Real Analysis): `REAL_LE_INV2`, `REAL_OF_NUM_LE`, `REAL_OF_NUM_LT`, `LE_1`, `LE_ADD`
- Theorems (Complex Analysis): `complex_div`, `CX_INV`, `REAL_CX`, `RE_CX`
- Types: `dirichlet_character`, `chi_0`

### Porting notes (optional)
The main challenge in porting this result lies in ensuring the correct definitions and theorems related to Dirichlet characters, Dirichlet series, and complex analysis are available in the target proof assistant. The convergence theorem `SERIES_DIRICHLET_COMPLEX` is likely a significant result that needs a careful port. Also, the proof involves reasoning about complex numbers and their relationship to real numbers, so the treatment of complex numbers in the target system should be considered.


---

## CNJ_CHI_0

### Name of formal statement
CNJ_CHI_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CNJ_CHI_0 = prove
 (`!d n. cnj(chi_0 d n) = chi_0 d n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[chi_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[CNJ_CX]);;
```

### Informal statement
For all `d` and `n`, the conjugate of `chi_0 d n` is equal to `chi_0 d n`.

### Informal sketch
The proof proceeds as follows:
- Start by generalizing the goal.
- Rewrite using the definition of `chi_0`.
- Perform case analysis, using `COND_CASES_TAC`, which likely corresponds to a conditional statement within the definition of `chi_0`.
- Rewrite using `CNJ_CX`.

### Mathematical insight
This theorem states that the character `chi_0` is self-conjugate. This property can be important when analyzing the structure of characters and their associated representations.

### Dependencies
- Definitions: `chi_0`, `cnj`
- Theorems: `CNJ_CX`


---

## LFUNCTION_CNJ

### Name of formal statement
LFUNCTION_CNJ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LFUNCTION_CNJ = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> Lfunction (\n. cnj(c n)) = cnj(Lfunction c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[Lfunction_DEF] THEN
  MATCH_MP_TAC INFSUM_UNIQUE THEN
  ONCE_REWRITE_TAC[GSYM CNJ_CX] THEN
  REWRITE_TAC[GSYM CNJ_DIV] THEN
  REWRITE_TAC[SUMS_CNJ; CNJ_CX; GSYM Lfunction_DEF] THEN
  ASM_MESON_TAC[LFUNCTION]);;
```
### Informal statement
For any Dirichlet character `d` and any character `c`, if `c` is a Dirichlet character modulo `d` and `c` is not the trivial character `chi_0 d`, then the L-function of the conjugate of `c` equals the conjugate of the L-function of `c`.

### Informal sketch
The proof proceeds as follows:
- Start by stripping the quantifiers and the implication.
- Rewrite using the definition of `Lfunction`.
- Apply `INFSUM_UNIQUE` to show uniqueness of infinite sums.
- Rewrite using `CNJ_CX` (conjugate of a complex number)
- Rewrite using `CNJ_DIV` (conjugate of a division)
- Rewrite using `SUMS_CNJ`, `CNJ_CX`, and the definition of `Lfunction`.
- Apply `ASM_MESON_TAC` with `LFUNCTION` to complete the proof.

### Mathematical insight
This theorem states a fundamental property of L-functions associated with Dirichlet characters, namely that conjugation commutes with the L-function. This is important because the conjugate of a Dirichlet character occurs naturally in the study of their properties and relationships; understanding how conjugation interacts with the L-function is crucial for many analytic arguments.

### Dependencies
- Definitions: `Lfunction_DEF`
- Theorems: `CNJ_CX`, `CNJ_DIV`, `SUMS_CNJ`, `LFUNCTION`
- Other: `INFSUM_UNIQUE`, `GSYM`


---

## LFUNCTION_PARTIAL_SUM

### Name of formal statement
LFUNCTION_PARTIAL_SUM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LFUNCTION_PARTIAL_SUM = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> ?B. &0 < B /\
                 !n. 1 <= n
                     ==> norm(Lfunction c - vsum(1..n) (\n. c(n) / Cx(&n)))
                          <= B / (&n + &1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:num->complex`; `\n. inv(Cx(&n))`; `1`; `1`]
                SERIES_DIRICHLET_COMPLEX_EXPLICIT) THEN
  REWRITE_TAC[LE_REFL] THEN FIRST_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP BOUNDED_LFUNCTION_PARTIAL_SUMS th]) THEN
  REWRITE_TAC[LIM_INV_N; GSYM CX_INV; REAL_CX; RE_CX] THEN
  SIMP_TAC[REAL_LE_INV2; REAL_OF_NUM_LE; REAL_OF_NUM_LT; LE_1; LE_ADD] THEN
  REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
  REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_INV; REAL_ABS_NUM] THEN
  REWRITE_TAC[CX_INV; GSYM complex_div; GSYM real_div] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC `\n. vsum(k+1..n) (\n. c(n) / Cx(&n))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP LFUNCTION) THEN
    MP_TAC(ISPECL [`sequentially`; `vsum (1..k) (\n. c n / Cx (&n))`]
                LIM_CONST) THEN
    REWRITE_TAC[GSYM IMP_CONJ_ALT; sums; FROM_INTER_NUMSEG] THEN
    DISCH_THEN(MP_TAC o MATCH_MP LIM_SUB) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC LIM_EVENTUALLY THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `k + 1` THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `k + 1 <= m ==> k <= m`)) THEN
    SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM] THEN
    ASM_SIMP_TAC[VSUM_ADD_SPLIT; ARITH_RULE `1 <= k ==> 1 <= k + 1`] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= k + 1`; REAL_OF_NUM_ADD]]);;
```

### Informal statement
For all Dirichlet characters `d` and complex-valued functions `c`, if `c` is a Dirichlet character with modulus `d` and `c` is not equal to the principal character `chi_0` with modulus `d`, then there exists a real number `B` greater than 0 such that for all natural numbers `n` greater than or equal to 1, the norm of the difference between the L-function of `c` and the partial sum from 1 to `n` of `c(n) / Cx(&n)` is less than or equal to `B / (&n + &1)`.

### Informal sketch
The proof aims to show the existence of a bound `B` for the error when approximating the L-function `Lfunction c` by its partial sums.

- Start by generalizing the goal, discharging the assumptions (`dirichlet_character d c /\ ~(c = chi_0 d)`), and specializing `SERIES_DIRICHLET_COMPLEX_EXPLICIT` with specific values to get an initial estimate.
- Simplify using `LE_REFL`.
- Use `BOUNDED_LFUNCTION_PARTIAL_SUMS` to relate the L-function to its partial sums.
- Rewrite using limits (`LIM_INV_N`), the definition of `CX_INV`, convert `REAL_CX` and `RE_CX`.
- Simplify using inequalities and properties such as `REAL_LE_INV2`, `REAL_OF_NUM_LE`, `REAL_OF_NUM_LT`, `LE_1`, `LE_ADD`, `REAL_LE_INV_EQ`, `REAL_POS`, `COMPLEX_NORM_CX`, `REAL_ABS_INV`, `REAL_ABS_NUM`, `CX_INV`, `complex_div`, and `real_div`.
- Use `MONO_EXISTS` to isolate the existence of `B`.
- Introduce `k` and discharge the assumption.
- Specialize `LIM_NORM_UBOUND` to obtain a bound based on the limit of the norm of the tail of the series.
- Show that `vsum(k+1..n) (\n. c(n) / Cx(&n))` is such a limit.
- split the goal into two subgoals using `CONJ_TAC`:
    - The first subgoal uses the fact that `Lfunction c` is the limit of the infinite sum, using `LFUNCTION`.
    - Transform the limit statement using `LIM_CONST`, `IMP_CONJ_ALT`, `sums`, `FROM_INTER_NUMSEG`, and `LIM_SUB`, and finally `LIM_TRANSFORM` and `LIM_EVENTUALLY`.
- Finally, use `ALWAYS_EVENTUALLY` to finish the proof.

### Mathematical insight
The theorem provides an explicit bound on the rate of convergence of the partial sums of the L-function associated with a Dirichlet character. This is an important result in analytic number theory, as it allows for effective computations and estimations involving L-functions. The condition `~(c = chi_0 d)` ensures that the character is non-principal, as the L-function of the principal character has a pole at `s = 1`, invalidating the bound.

### Dependencies
- `dirichlet_character`
- `chi_0`
- `Lfunction`
- `vsum`
- `Cx`
- `norm`
- `SERIES_DIRICHLET_COMPLEX_EXPLICIT`
- `BOUNDED_LFUNCTION_PARTIAL_SUMS`
- `LIM_INV_N`
- `CX_INV`
- `REAL_CX`
- `RE_CX`
- `REAL_LE_INV2`
- `REAL_OF_NUM_LE`
- `REAL_OF_NUM_LT`
- `LE_1`
- `LE_ADD`
- `REAL_LE_INV_EQ`
- `REAL_POS`
- `COMPLEX_NORM_CX`
- `REAL_ABS_INV`
- `REAL_ABS_NUM`
- `complex_div`
- `real_div`
- `LIM_NORM_UBOUND`
- `TRIVIAL_LIMIT_SEQUENTIALLY`
- `LIM_CONST`
- `IMP_CONJ_ALT`
- `sums`
- `FROM_INTER_NUMSEG`
- `LIM_SUB`
- `LIM_TRANSFORM`
- `LIM_EVENTUALLY`
- `EVENTUALLY_SEQUENTIALLY`
- `ARITH_RULE`
- `LEFT_IMP_EXISTS_THM`
- `VSUM_ADD_SPLIT`
- `ALWAYS_EVENTUALLY`


---

## LFUNCTION_PARTIAL_SUM_STRONG

### Name of formal statement
LFUNCTION_PARTIAL_SUM_STRONG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LFUNCTION_PARTIAL_SUM_STRONG = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> ?B. &0 < B /\
                 !n. norm(Lfunction c - vsum(1..n) (\n. c(n) / Cx(&n)))
                         <= B / (&n + &1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LFUNCTION_PARTIAL_SUM) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `max B (norm(Lfunction c))` THEN
  ASM_SIMP_TAC[REAL_LT_MAX] THEN X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[VSUM_CLAUSES_NUMSEG; VECTOR_SUB_RZERO; ARITH] THEN
    REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_SIMP_TAC[LE_1] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ARITH `&0 < &n + &1`] THEN
    REAL_ARITH_TAC]);;
```

### Informal statement
For all Dirichlet characters `d` and `c`, if `c` is a Dirichlet character `d` and `c` is not the principal character `chi_0` of `d`, then there exists a real number `B` greater than 0 such that for all natural numbers `n`, the norm of the difference between the L-function of `c` and the partial sum from 1 to `n` of `c(n) / n` is less than or equal to `B / (n + 1)`.

### Informal sketch
The proof proceeds as follows:
- Assume `d` is a Dirichlet character, `c` is a Dirichlet character modulo `d`, and `c` is not equal to the principal character, `chi_0 d`.
- Apply the theorem `LFUNCTION_PARTIAL_SUM` to obtain a bound `B` satisfying the weaker inequality `norm(Lfunction c - vsum(1..n) (\n. c(n) / Cx(&n))) <= B`.
- Choose a new bound `B` to be the maximum of the previous `B` and `norm(Lfunction c)`.
- Show that the desired inequality holds for all `n`.
- Perform case analysis on `n = 0`.
  - If `n = 0`, the partial sum is 0, and the inequality reduces to `norm(Lfunction c) <= B`, which holds by construction of `B`.
  - If `n > 0`, the original bound `B` from `LFUNCTION_PARTIAL_SUM` holds, and since `B <= max B (norm(Lfunction c))`, we still have the required bound. The inequality `B / (n + 1) <= B` holds for `n >= 0`, and thus the claim follows.

### Mathematical insight
This theorem provides a stronger bound on the convergence of the partial sums of the L-function associated with a Dirichlet character.  The original `LFUNCTION_PARTIAL_SUM` simply states that the partial sums are bounded. This improved version gives a rate of convergence proportional to 1/n, so improves the error bound on approximating the L-function. This is essential for numerical computations and estimating the L-function.

### Dependencies
- `dirichlet_character`
- `chi_0`
- `Lfunction`
- `vsum`
- `Cx`
- `norm`
- `LFUNCTION_PARTIAL_SUM`
- `VSUM_CLAUSES_NUMSEG`
- `VECTOR_SUB_RZERO`
- `REAL_LT_MAX`

### Porting notes (optional)
- The user should verify the definitions for `Lfunction`, `vsum`, `Cx`, and `norm` are available in the target proof assistant.
- Special care should be taken to deal with the coercion between natural numbers and real numbers. HOL Light uses `&` to represent this coercion, other assistants may have different syntax.
- The tactic `REAL_ARITH_TAC` may need to be replaced with equivalent tactics in the target environment to prove arithmetic inequalities.


---

## BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT_LEMMA

### Name of formal statement
BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT_LEMMA = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> bounded
              { Lfunction(c) *
                vsum(1..x) (\n. c(n) * Cx(mangoldt n / &n)) -
                vsum(1..x) (\n. c(n) * Cx(log(&n) / &n)) | x IN (:num)}`,
  REWRITE_TAC[BOUNDED_POS; SIMPLE_IMAGE; FORALL_IN_IMAGE; IN_UNIV] THEN
  REPEAT STRIP_TAC THEN
  SIMP_TAC[LOG_MANGOLDT_SUM; real_div; CX_MUL;  GSYM VSUM_CX; FINITE_DIVISORS;
           LE_1; GSYM VSUM_COMPLEX_LMUL; GSYM VSUM_COMPLEX_RMUL] THEN
  REWRITE_TAC[VSUM_VSUM_DIVISORS] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_MUL th]) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; COMPLEX_INV_MUL; CX_MUL; CX_INV] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING
   `(ck * cn) * cm * k * n:complex = (ck * k) * (cn * cm * n)`] THEN
  SIMP_TAC[VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  SIMP_TAC[GSYM VSUM_SUB; FINITE_NUMSEG] THEN
  REWRITE_TAC[GSYM COMPLEX_SUB_RDISTRIB] THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`] LFUNCTION_PARTIAL_SUM_STRONG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `&18 * B` THEN
  ASM_SIMP_TAC[REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
  X_GEN_TAC `x:num` THEN MATCH_MP_TAC VSUM_NORM_TRIANGLE THEN
  REWRITE_TAC[FINITE_NUMSEG; COMPLEX_NORM_MUL] THEN
  REWRITE_TAC[COMPLEX_NORM_INV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  REWRITE_TAC[GSYM real_div] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
  REWRITE_TAC[real_abs; MANGOLDT_POS_LE] THEN ASM_CASES_TAC `x = 0` THEN
  ASM_SIMP_TAC[SUM_CLAUSES_NUMSEG; ARITH; REAL_LE_MUL; REAL_LT_IMP_LE;
               REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..x) (\n. B / &x * mangoldt n)` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUM_LMUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `B / &x * &18 * &x` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
      REWRITE_TAC[REWRITE_RULE[ETA_AX] PSI_BOUND];
      ASM_SIMP_TAC[REAL_FIELD `~(x = &0) ==> B / x * &18 * x = &18 * B`;
                   REAL_OF_NUM_EQ; REAL_LE_REFL]]] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `n:num` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_NORM th]) THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_MUL_RID; REAL_LE_MUL;
               REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE; MANGOLDT_POS_LE] THEN
  REWRITE_TAC[real_div; REAL_ARITH `a * b * c <= d <=> (a * c) * b <= d`] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[MANGOLDT_POS_LE] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B / (&(x DIV n) + &1)` THEN
  ASM_REWRITE_TAC[GSYM complex_div] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_INV_INV] THEN
  ONCE_REWRITE_TAC[GSYM REAL_INV_MUL] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  SUBGOAL_THEN `1 <= x` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LT_DIV; REAL_OF_NUM_LT; LE_1] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  MP_TAC(SPECL [`x:num`; `n:num`] DIVISION) THEN ASM_ARITH_TAC);;
```

### Informal statement
For all `d` and `c`, if `c` is a Dirichlet character modulo `d` and `c` is not the principal character `chi_0` modulo `d`, then the set of values
```
{ Lfunction(c) *
  vsum(1..x) (\n. c(n) * Cx(mangoldt n / &n)) -
  vsum(1..x) (\n. c(n) * Cx(log(&n) / &n)) | x IN (:num)}
```
is bounded.

### Informal sketch
The proof shows that for a non-principal Dirichlet character `c` modulo `d`, the complex-valued function 
$$L(1, c) \sum_{n=1}^x \frac{c(n) \Lambda(n)}{n} - \sum_{n=1}^x \frac{c(n) \log n}{n}$$ is bounded as $x \rightarrow \infty$, where $\Lambda(n)$ is the Mangoldt function and $L(s, c)$ is the Dirichlet L-function.

- First rewrite the expression using `LOG_MANGOLDT_SUM` to express logarithmic derivative of $L(s, \chi)$ in terms of a sum involving the von Mangoldt function.
- Use properties of the Dirichlet character to rewrite the sums, and `VSUM_VSUM_DIVISORS` to rearrange the order of summation over divisors.
- Apply `LFUNCTION_PARTIAL_SUM_STRONG` to bound the difference between the L-function and its partial sum involving log n.
- Apply `VSUM_NORM_TRIANGLE` to bound the sums by taking absolute values.
- Use properties of complex numbers to obtain bounds on the norm of products and inverses of complex numbers.
- Split the proof into cases based on `x = 0`. If `x = 0` the sum is zero and, therefore, trivially bounded.
- Bound the sum involving the von Mangoldt function `mangoldt n` using `PSI_BOUND`, which states that the Chebyshev function $\psi(x) = \sum_{n \leq x} \Lambda(n) \leq 18x$ for sufficiently large $x$, which implies `sum(1..x) (\n. mangoldt n) <= 18 * x`. This is the crucial estimate.
- Split the remaining sums into real and imaginary parts using `COMPLEX_SUB_RDISTRIB`
- Use properties of the Dirichlet character to obtain `abs(c(n)) <= 1`.
- Simplify several expressions and use `REAL_LE_TRANS` and `REAL_LE_LMUL` to relate them.
- Finally use `DIVISION` to show that $\frac{x}{x/n + 1} \leq x$ and `REAL_LE_INV2` that if $x \leq y$ then $\frac{1}{y} \leq \frac{1}{x}$.
- This results in a bound, proving the theorem.

### Mathematical insight
This theorem is important in analytic number theory. It states that a certain sum involving the Mangoldt function and a non-principal Dirichlet character is bounded. This result is a key step in proving the prime number theorem for arithmetic progressions. This form of the statement, using the Mangoldt function, is convenient for controlling growth rates of sums.

### Dependencies
- `BOUNDED_POS`
- `SIMPLE_IMAGE`
- `FORALL_IN_IMAGE`
- `IN_UNIV`
- `LOG_MANGOLDT_SUM`
- `real_div`
- `CX_MUL`
- `GSYM VSUM_CX`
- `FINITE_DIVISORS`
- `LE_1`
- `GSYM VSUM_COMPLEX_LMUL`
- `GSYM VSUM_COMPLEX_RMUL`
- `VSUM_VSUM_DIVISORS`
- `DIRICHLET_CHARACTER_MUL`
- `GSYM REAL_OF_NUM_MUL`
- `COMPLEX_INV_MUL`
- `CX_INV`
- `COMPLEX_RING`
- `FINITE_NUMSEG`
- `GSYM VSUM_SUB`
- `GSYM COMPLEX_SUB_RDISTRIB`
- `LFUNCTION_PARTIAL_SUM_STRONG`
- `REAL_LT_MUL`
- `REAL_OF_NUM_LT`
- `ARITH`
- `VSUM_NORM_TRIANGLE`
- `COMPLEX_NORM_MUL`
- `COMPLEX_NORM_INV`
- `COMPLEX_NORM_CX`
- `REAL_ABS_NUM`
- `GSYM real_div`
- `REAL_MUL_ASSOC`
- `real_abs`
- `MANGOLDT_POS_LE`
- `SUM_CLAUSES_NUMSEG`
- `REAL_LE_MUL`
- `REAL_LT_IMP_LE`
- `REAL_LE_TRANS`
- `REWRITE_RULE[ETA_AX] PSI_BOUND`
- `REAL_FIELD`
- `REAL_OF_NUM_EQ`
- `REAL_LE_REFL`
- `SUM_LE_NUMSEG`
- `DIRICHLET_CHARACTER_NORM`
- `REAL_MUL_LZERO`
- `REAL_MUL_RZERO`
- `REAL_MUL_RID`
- `REAL_LE_DIV`
- `REAL_POS`
- `REAL_ARITH`
- `REAL_LE_RMUL`
- `GSYM real_div`
- `REAL_LE_LDIV_EQ`
- `GSYM complex_div`
- `GSYM REAL_MUL_ASSOC`
- `REAL_LE_LMUL_EQ`
- `GSYM REAL_INV_INV`
- `GSYM REAL_INV_MUL`
- `REAL_LE_INV2`
- `REAL_LT_DIV`
- `REAL_OF_NUM_ADD`
- `REAL_OF_NUM_MUL`
- `REAL_OF_NUM_LE`
- `DIVISION`

### Porting notes (optional)
- `LFUNCTION_PARTIAL_SUM_STRONG` seems to be a relatively involved external dependency and may need care during porting.
- The extensive use of field arithmetic lemmas such as `REAL_MUL_ASSOC`, `REAL_LE_RMUL` etc., may require the use of appropriate automation in other proof assistants to replicate efficiently.
- Pay attention to the discharging assumptions during the tactic script `COND_CASES_TAC`, `ASM_SIMP_TAC` etc., since these tactics have particular modes of operation in HOL Light.


---

## SUMMABLE_CHARACTER_LOG_OVER_N

### Name of formal statement
SUMMABLE_CHARACTER_LOG_OVER_N

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUMMABLE_CHARACTER_LOG_OVER_N = prove
 (`!c d. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> summable (from 1) (\n. c(n) * Cx(log(&n) / &n))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SERIES_DIRICHLET_COMPLEX THEN
  MAP_EVERY EXISTS_TAC [`4`; `1`] THEN REWRITE_TAC[REAL_CX] THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP BOUNDED_LFUNCTION_PARTIAL_SUMS th]) THEN
  CONJ_TAC THENL
   [SIMP_TAC[DECREASING_LOG_OVER_N; GSYM REAL_OF_NUM_ADD; RE_CX];
    MP_TAC LIM_LOG_OVER_N THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    ASM_SIMP_TAC[CX_LOG; CX_DIV; LE_1; REAL_OF_NUM_LT]]);;
```

### Informal statement
For all Dirichlet characters `d` and all complex-valued functions `c`, if `c` is a Dirichlet character for `d` and `c` is not equal to the principal character `chi_0` for `d`, then the series, starting from index 1, whose nth term is `c(n)` multiplied by the complex number `log(n)/n`, is summable.

### Informal sketch
The proof proceeds as follows:
- Assume `c` is a Dirichlet character for `d` and `c` is not the principal character `chi_0` for `d`.
- Apply `SERIES_DIRICHLET_COMPLEX` which reduces the problem to showing that the partial sums of `c(n)` are bounded and that `log(n)/n` is decreasing and tends to 0.
- Show that the partial sums of `c(n)` are bounded. This relies on `BOUNDED_LFUNCTION_PARTIAL_SUMS`.
- Show that `log(n)/n` is decreasing, which uses `DECREASING_LOG_OVER_N`.
- Show that the limit of `log(n)/n` as `n` tends to infinity is 0. This makes use of `LIM_LOG_OVER_N` and `LIM_TRANSFORM_EVENTUALLY`.

### Mathematical insight
This theorem establishes the summability of a specific Dirichlet series when the character is non-principal. Dirichlet series are fundamental in analytic number theory, connecting complex analysis to the study of primes and arithmetic functions. This particular result is likely used in proving results about L-functions associated with Dirichlet characters.

### Dependencies
- `dirichlet_character`
- `chi_0`
- `summable`
- `SERIES_DIRICHLET_COMPLEX`
- `BOUNDED_LFUNCTION_PARTIAL_SUMS`
- `DECREASING_LOG_OVER_N`
- `GSYM REAL_OF_NUM_ADD`
- `RE_CX`
- `LIM_LOG_OVER_N`
- `LIM_TRANSFORM_EVENTUALLY`
- `EVENTUALLY_SEQUENTIALLY`
- `CX_LOG`
- `CX_DIV`
- `LE_1`
- `REAL_OF_NUM_LT`


---

## BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT

### Name of formal statement
`BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT`

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> bounded
              { Lfunction(c) *
                vsum(1..x) (\n. c(n) * Cx(mangoldt n / &n)) | x IN (:num)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o
    MATCH_MP BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT_LEMMA) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SUMMABLE_CHARACTER_LOG_OVER_N) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUMMABLE_IMP_SUMS_BOUNDED) THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP BOUNDED_SUMS) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] BOUNDED_SUBSET) THEN
  REWRITE_TAC[SIMPLE_IMAGE; SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_UNIV; IN_ELIM_THM; RIGHT_EXISTS_AND_THM; EXISTS_IN_IMAGE;
              GSYM CONJ_ASSOC] THEN
  X_GEN_TAC `n:num` THEN REPEAT(EXISTS_TAC `n:num`) THEN VECTOR_ARITH_TAC);;
```
### Informal statement
For all Dirichlet characters `d` and `c`, if `c` is a Dirichlet character modulo `d` and `c` is not the trivial character `chi_0` modulo `d`, then the set of partial sums of `Lfunction(c)` times the sum from 1 to `x` of `c(n)` times `Cx(mangoldt n / &n)` is bounded as `x` ranges over the natural numbers.

### Informal sketch
The proof proceeds by showing that the partial sums are bounded.
- First, assume `d` and `c` are as described in the hypothesis. We aim to show that the set of sums is bounded.
- Use the lemma `BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT_LEMMA` to reduce the problem.
- Then the theorem `SUMMABLE_CHARACTER_LOG_OVER_N` shows that the sum is summable.
- From the theorem `SUMMABLE_IMP_SUMS_BOUNDED`, summability implies that the sums in question are bounded.
- Apply `BOUNDED_SUMS` followed by rewriting with `IMP_CONJ_ALT` and `BOUNDED_SUBSET` to complete the proof.

### Mathematical insight
This theorem establishes a boundedness result related to the Dirichlet L-function and the Mangoldt function. The Mangoldt function is crucial in prime number theory, and Dirichlet L-functions extend the Riemann zeta function using Dirichlet characters. Specifically, it shows that the partial sums of a particular series involving the Dirichlet character, the Mangoldt function, and the L-function are bounded. This type of result is importent in analytic number theory to e.g. bound zeros of L-functions.

### Dependencies
- `BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT_LEMMA`
- `SUMMABLE_CHARACTER_LOG_OVER_N`
- `SUMMABLE_IMP_SUMS_BOUNDED`
- `IMP_IMP`
- `BOUNDED_SUMS`
- `IMP_CONJ_ALT`
- `BOUNDED_SUBSET`
- `SIMPLE_IMAGE`
- `SUBSET`
- `FORALL_IN_IMAGE`
- `IN_UNIV`
- `IN_ELIM_THM`
- `RIGHT_EXISTS_AND_THM`
- `EXISTS_IN_IMAGE`
- `CONJ_ASSOC`


---

## BOUNDED_DIRICHLET_MANGOLDT_NONZERO

### Name of formal statement
BOUNDED_DIRICHLET_MANGOLDT_NONZERO

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BOUNDED_DIRICHLET_MANGOLDT_NONZERO = prove
 (`!d c.
      dirichlet_character d c /\ ~(c = chi_0 d) /\ ~(Lfunction c = Cx(&0))
      ==> bounded { vsum(1..x) (\n. c n * Cx(mangoldt n / &n)) | x IN (:num)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT) THEN
  REWRITE_TAC[BOUNDED_POS; SIMPLE_IMAGE; FORALL_IN_IMAGE; IN_UNIV] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; COMPLEX_NORM_NZ] THEN
  ASM_MESON_TAC[COMPLEX_NORM_NZ; REAL_LT_DIV]);;
```
### Informal statement
For all Dirichlet characters `d` and `c`, if `c` is a Dirichlet character modulo `d`, `c` is not the principal character `chi_0 d`, and the L-function `Lfunction c` is not identically zero, then the set of partial sums of `c(n) * mangoldt(n) / n` is bounded for `n` ranging from 1 to `x`, where the set is taken over all positive integers `x`.

### Informal sketch
The proof demonstrates that the partial sums of the Dirichlet-Mangoldt series `c(n) * mangoldt(n) / n` (where `c` is a nontrivial Dirichlet character) are bounded.

- Start by assuming `d` and `c` exist such that `c` is a Dirichlet character modulo `d`, `c` is not the principal character `chi_0 d`, and the L-function `Lfunction c` is not identically zero.

- The proof then applies the theorem `BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT` which directly states that the L-function associated with the Mangoldt function and a Dirichlet character (excluding the principal character) is bounded. Thus, the set of partial sums is bounded. The proof involves rewriting the original statement by using properties of bounded sets, images, and norms to simplify the expression to match the conclusion of  `BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT`. Specifically, it uses the facts that if `Lfunction c` is not zero, its norm is non-zero, and thus the sums are bounded. Basic facts about complex numbers such as `COMPLEX_NORM_MUL` and `REAL_MUL_SYM` are also employed to simplify expressions and manipulate norms.

### Mathematical insight
This theorem is a crucial step in understanding the distribution of prime numbers. Bounding the partial sums of the Dirichlet-Mangoldt series allows one to control the growth of certain arithmetic functions related to primes. The L-function associated with Dirichlet characters plays a key role in analytic number theory, especially in proving results about the distribution of primes in arithmetic progressions.

### Dependencies
- `BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT`
- `dirichlet_character`
- `chi_0`
- `Lfunction`
- `mangoldt`
- `BOUNDED_POS`
- `SIMPLE_IMAGE`
- `FORALL_IN_IMAGE`
- `IN_UNIV`
- `COMPLEX_NORM_MUL`
- `REAL_MUL_SYM`
- `REAL_LE_RDIV_EQ`
- `COMPLEX_NORM_NZ`
- `REAL_LT_DIV`


---

## MANGOLDT_LOG_SUM

### Name of formal statement
MANGOLDT_LOG_SUM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MANGOLDT_LOG_SUM = prove
 (`!n. 1 <= n
       ==> mangoldt(n) = --(sum {d | d divides n} (\d. mobius(d) * log(&d)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n. mangoldt n`; `\n. log(&n)`] MOBIUS_INVERSION) THEN
  ASM_SIMP_TAC[LOG_MANGOLDT_SUM; LE_1] THEN DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {d | d divides n} (\x. mobius x * (log(&n) - log(&x)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `d:num` THEN
    REWRITE_TAC[IN_ELIM_THM; DIVIDES_DIV_MULT] THEN
    ABBREV_TAC `q = n DIV d` THEN
    MAP_EVERY ASM_CASES_TAC [`q = 0`; `d = 0`] THEN
    ASM_SIMP_TAC[MULT_CLAUSES; LE_1] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_MUL; LOG_MUL; REAL_OF_NUM_LT; LE_1] THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_SUB_LDISTRIB; SUM_SUB; FINITE_DIVISORS; LE_1] THEN
    ASM_SIMP_TAC[SUM_RMUL; REWRITE_RULE[ETA_AX] DIVISORSUM_MOBIUS] THEN
    MATCH_MP_TAC(REAL_ARITH `a = &0 ==> a - b = --b`) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[LOG_1] THEN REAL_ARITH_TAC]);;
```

### Informal statement
For all natural numbers `n`, if `1 <= n`, then `mangoldt(n)` is equal to the negation of the sum over all `d` that divide `n` of `mobius(d) * log(&d)`.

### Informal sketch
The proof proceeds by:
- Applying `MOBIUS_INVERSION` with the instantiations `\n. mangoldt n` and `\n. log(&n)`.
- Simplifying using `LOG_MANGOLDT_SUM` and `LE_1`.
- Discharging the assumption.
- Applying an equality transformation.
- Showing that the sum `sum {d | d divides n} (\x. mobius x * log(&x))` is equal to `sum {d | d divides n} (\x. mobius x * (log(&n) - log(&x)))`; proceeds by showing that the difference between two sums is 0.
- Breaking the proof in two parts:
  - Transforming the sum using `SUM_EQ`, rewriting with `IN_ELIM_THM` and `DIVIDES_DIV_MULT`, abbreviating `n DIV d` as `q`, considering the cases `q = 0` and `d = 0`. Simplifying with `MULT_CLAUSES` and `LE_1`; substituting `q` by `n div d`, simplifying using `GSYM REAL_OF_NUM_MUL`, `LOG_MUL`, `REAL_OF_NUM_LT`, and `LE_1`, and concluding with real arithmetic.
  - Simplifying the sum using `REAL_SUB_LDISTRIB`, `SUM_SUB`.  Simplifying with `FINITE_DIVISORS` and `LE_1`; simplifying using `SUM_RMUL`; rewriting using `ETA_AX` and `DIVISORSUM_MOBIUS`; using `REAL_ARITH` to simplify the expression `a = &0 ==> a - b = --b`; considering the cases and rewriting using `LOG_1` and real arithmetic.

### Mathematical insight
This theorem relates the `mangoldt` function to the `mobius` function and the logarithm function via a divisor sum. The Mangoldt function `mangoldt(n)` is defined to be `log p` if `n` is a power of a prime `p`, and 0 otherwise. The theorem expresses `mangoldt(n)` in terms of a sum involving the Mobius function `mobius(d)` (which is 0 if `d` is not squarefree, 1 if `d` is a product of an even number of distinct primes, and -1 if `d` is a product of an odd number of distinct primes) and the logarithm of the divisors `d` of `n`. This relationship is a specific case of Mobius inversion.

### Dependencies
- theorem: `MOBIUS_INVERSION`
- theorem: `LOG_MANGOLDT_SUM`
- theorem: `LE_1`
- theorem: `IN_ELIM_THM`
- theorem: `DIVIDES_DIV_MULT`
- theorem: `MULT_CLAUSES`
- theorem: `REAL_OF_NUM_MUL`
- theorem: `LOG_MUL`
- theorem: `REAL_OF_NUM_LT`
- theorem: `REAL_SUB_LDISTRIB`
- theorem: `SUM_SUB`
- theorem: `FINITE_DIVISORS`
- theorem: `SUM_RMUL`
- theorem: `DIVISORSUM_MOBIUS`
- theorem: `LOG_1`


---

## BOUNDED_DIRICHLET_MANGOLDT_LEMMA

### Name of formal statement
BOUNDED_DIRICHLET_MANGOLDT_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BOUNDED_DIRICHLET_MANGOLDT_LEMMA = prove
 (`!d c x.
        dirichlet_character d c /\ ~(c = chi_0 d) /\ 1 <= x
        ==> Cx(log(&x)) + vsum (1..x) (\n. c(n) * Cx(mangoldt n / &n)) =
            vsum (1..x) (\n. c(n) / Cx(&n) *
                             vsum {d | d divides n}
                                  (\d. Cx(mobius(d) * log(&x / &d))))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MANGOLDT_LOG_SUM] THEN
  MATCH_MP_TAC(COMPLEX_RING `c - b = a ==> (a:complex) + b = c`) THEN
  SIMP_TAC[GSYM VSUM_SUB; FINITE_NUMSEG] THEN
  SIMP_TAC[CX_NEG; CX_DIV; GSYM VSUM_CX; FINITE_NUMSEG; FINITE_DIVISORS;
           LE_1] THEN
  REWRITE_TAC[SIMPLE_COMPLEX_ARITH
   `c / d * x - c * --y / d:complex = c / d * (x + y)`] THEN
  SIMP_TAC[GSYM VSUM_ADD; FINITE_DIVISORS; LE_1] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `vsum (1..x)
         (\n. c n / Cx(&n) * vsum {d | d divides n}
               (\d. Cx(mobius d * log(&x))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
    X_GEN_TAC `m:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    REWRITE_TAC[CX_MUL; GSYM COMPLEX_ADD_LDISTRIB] THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM CX_ADD; CX_INJ] THEN
    ASM_CASES_TAC `m = 0` THENL
     [ASM_MESON_TAC[DIVIDES_ZERO; LE_1]; ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_DIV; REAL_OF_NUM_LT; LE_1] THEN REAL_ARITH_TAC;
    SIMP_TAC[FINITE_DIVISORS; CX_MUL; SUM_RMUL; LE_1; VSUM_CX] THEN
    SIMP_TAC[REWRITE_RULE[ETA_AX] DIVISORSUM_MOBIUS] THEN
    SIMP_TAC[COND_RAND; COND_RATOR; COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO] THEN
    ASM_SIMP_TAC[VSUM_DELTA; GSYM COMPLEX_VEC_0; IN_NUMSEG; LE_REFL] THEN
    MP_TAC(SPECL [`d:num`; `c:num->complex`] DIRICHLET_CHARACTER_EQ_1) THEN
    ASM_SIMP_TAC[COMPLEX_MUL_LID; COMPLEX_DIV_1]]);;
```
### Informal statement
For any Dirichlet character `d` and any character `c` such that `c` is not the principal character `chi_0 d` and `x` is a real number greater than or equal to 1, the following equation holds:
`Cx(log(&x)) + vsum (1..x) (\n. c(n) * Cx(mangoldt n / &n)) = vsum (1..x) (\n. c(n) / Cx(&n) * vsum {d | d divides n} (\d. Cx(mobius(d) * log(&x / &d))))`.

### Informal sketch
The proof proceeds as follows:
- Start by using `MANGOLDT_LOG_SUM` to express the von Mangoldt function in terms of the Möbius function.
- Rearrange the equation using complex ring properties and simplification rules involving `vsum` (finite summation over a range of numbers) and complex numbers.
- Transform the right-hand side of the equation by introducing a new summation over divisors. The goal is to manipulate the sums and isolate terms involving `log(&x)`.
- Show the equality of the modified summations by proving that `vsum (1..x) (\n. c n / Cx(&n) * vsum {d | d divides n} (\d. Cx(mobius d * log(&x))))` .
- Split the summation based on whether `d` divides `n` and use properties of complex numbers.
- Perform case analysis on `m = 0` and applies `DIVIDES_ZERO` and `LE_1`
- Simplify using logarithmic identities, properties of divisors, and identities involving the Möbius function. Specifically, use the fact that the divisor sum of the Möbius function is an indicator function (equal to 1 if `n=1` and 0 otherwise).
- Apply Dirichlet character properties, `DIRICHLET_CHARACTER_EQ_1`. Simplify using the properties of complex numbers and the definition of the principal character, and prove using arithmetic reasoning.

### Mathematical insight
The theorem relates the sum of the Dirichlet character multiplied by the Mangoldt function to a sum involving the Möbius function. The Dirichlet character introduces arithmetic structure to the sums, filtering or weighting contributions based on congruence properties. The Mangoldt function detects prime powers, and the Möbius function is related to the prime factorization of integers. This type of identity is fundamental in analytic number theory for studying the distribution of primes in arithmetic progressions.

### Dependencies
- Theorems:
    - `MANGOLDT_LOG_SUM`
    - `COMPLEX_RING c - b = a ==> (a:complex) + b = c`
    - `EQ_TRANS`
    - `VSUM_EQ_NUMSEG`
    - `IN_ELIM_THM`
    - `DIVIDES_ZERO`
    - `LOG_DIV`
    - `REAL_OF_NUM_LT`
    - `LE_1`
    - `REWRITE_RULE[ETA_AX] DIVISORSUM_MOBIUS`
    - `DIRICHLET_CHARACTER_EQ_1`

- Definitions:
    - `dirichlet_character`
    - `chi_0`
    - `mangoldt`
    - `vsum`
    - `mobius`

- Other:
    - `SIMPLE_COMPLEX_ARITH c / d * x - c * --y / d:complex = c / d * (x + y)`
    - `FINITE_NUMSEG`
    - `FINITE_DIVISORS`
    - `GSYM VSUM_SUB`
    - `CX_NEG`
    - `CX_DIV`
    - `GSYM VSUM_CX`
    - `GSYM VSUM_ADD`
    - `CX_MUL`
    - `GSYM COMPLEX_ADD_LDISTRIB`
    - `GSYM CX_ADD`
    - `CX_INJ`
    - `SUM_RMUL`
    - `COND_RAND`
    - `COND_RATOR`
    - `COMPLEX_MUL_LZERO`
    - `COMPLEX_MUL_RZERO`
    - `VSUM_DELTA`
    - `GSYM COMPLEX_VEC_0`
    - `IN_NUMSEG`
    - `LE_REFL`
    - `COMPLEX_MUL_LID`
    - `COMPLEX_DIV_1`


---

## SUM_LOG_OVER_X_BOUND

### Name of formal statement
SUM_LOG_OVER_X_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_LOG_OVER_X_BOUND = prove
 (`!x. abs(sum(1..x) (\n. log(&x / &n) / &x)) <= &4`,
  X_GEN_TAC `x:num` THEN ASM_CASES_TAC `x = 0` THENL
   [ASM_SIMP_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ; REAL_ABS_NUM; REAL_POS];
    ALL_TAC] THEN
  SIMP_TAC[real_div; SUM_RMUL; REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NUM] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (1..x) (\n. abs(log(&x / &n)))` THEN
  REWRITE_TAC[SUM_ABS_NUMSEG] THEN
  ASM_SIMP_TAC[real_abs; LOG_POS; REAL_LE_RDIV_EQ; REAL_OF_NUM_LT;
               LE_1; REAL_MUL_LID; REAL_OF_NUM_LE; LOG_DIV] THEN
  REWRITE_TAC[SUM_SUB_NUMSEG; GSYM LOG_FACT] THEN
  REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LOG_FACT_BOUNDS) THEN
  MATCH_MP_TAC(REAL_ARITH
   `&2 * l + abs(x) + &1 <= b
    ==> abs(lf - (xl - x + &1)) <= &2 * l
        ==> xl - lf <= b`) THEN
 MATCH_MP_TAC(REAL_ARITH
   `&1 <= x /\ l <= x ==> &2 * l + abs(x) + &1 <= &4 * x`) THEN
  ASM_SIMP_TAC[REAL_OF_NUM_LE; LE_1; LOG_LE_REFL]);;
```
### Informal statement
For all natural numbers `x`, the absolute value of the sum from 1 to `x` of `log(&x / &n) / &x` is less than or equal to `&4`. Where `&x` and `&n` are the real representations of the natural numbers `x` and `n`, respectively, and `log` is the natural logarithm function.

### Informal sketch
The proof proceeds by induction on `x`.
- **Base Case:** If `x = 0`, the sum is empty, so the absolute value is 0, which is less than or equal to 4.
- **Inductive Step:** Assuming the inequality holds for some `x`, we wish to show it holds for `x+1`.
    - Initially, the aim is to prove `abs(sum(1..x) (\n. log(&x / &n) / &x)) <= &4`.
    - Simplify the expression using theorems like `real_div`, `SUM_RMUL`, `REAL_ABS_MUL`, `REAL_ABS_INV` and so on.
    - The proof rewrites the sum of logarithms as a logarithm of a factorial, then bounds the logarithm of the factorial using `LOG_FACT_BOUNDS`.
    - Uses `REAL_ARITH` to show that if `&2 * l + abs(x) + &1 <= b` and `abs(lf - (xl - x + &1)) <= &2 * l` then `xl - lf <= b`.
    - Finally, it uses `REAL_ARITH` to show that if `&1 <= x` and `l <= x` then `&2 * l + abs(x) + &1 <= &4 * x`.

### Mathematical insight
The theorem provides a bound on the sum of logarithms scaled by `1/x`. It connects the sum to `log(x!)`, which can then be approximated. The result is useful in estimating the asymptotic behavior of sums involving logarithms and factorials.

### Dependencies
- `SUM_CLAUSES_NUMSEG`
- `ARITH_EQ`
- `REAL_ABS_NUM`
- `real_div`
- `SUM_RMUL`
- `REAL_ABS_MUL`
- `REAL_ABS_INV`
- `GSYM real_div`
- `REAL_LE_LDIV_EQ`
- `REAL_OF_NUM_LT`
- `LE_1`
- `REAL_LE_TRANS`
- `SUM_ABS_NUMSEG`
- `real_abs`
- `LOG_POS`
- `REAL_LE_RDIV_EQ`
- `REAL_MUL_LID`
- `REAL_OF_NUM_LE`
- `LOG_DIV`
- `SUM_SUB_NUMSEG`
- `GSYM LOG_FACT`
- `SUM_CONST_NUMSEG`
- `ADD_SUB`
- `LOG_FACT_BOUNDS`
- `REAL_OF_NUM_LE`
- `LOG_LE_REFL`


---

## BOUNDED_DIRICHLET_MANGOLDT_ZERO

### Name of formal statement
BOUNDED_DIRICHLET_MANGOLDT_ZERO

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BOUNDED_DIRICHLET_MANGOLDT_ZERO = prove
 (`!d c.
      dirichlet_character d c /\ ~(c = chi_0 d) /\ Lfunction c = Cx(&0)
      ==> bounded { vsum(1..x) (\n. c n * Cx(mangoldt n / &n)) +
                    Cx(log(&x)) | x IN (:num)}`,
  ONCE_REWRITE_TAC[COMPLEX_ADD_SYM] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`] LFUNCTION_PARTIAL_SUM_STRONG) THEN
  ASM_REWRITE_TAC[COMPLEX_SUB_LZERO; NORM_NEG] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  SIMP_TAC[SET_RULE `{f x | x IN (:num)} = f 0 INSERT {f x | ~(x = 0)}`] THEN
  REWRITE_TAC[BOUNDED_INSERT; ARITH_RULE `~(n = 0) <=> 1 <= n`] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`]
    BOUNDED_DIRICHLET_MANGOLDT_LEMMA) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_DIVISORS; LE_1] THEN
  REWRITE_TAC[VSUM_VSUM_DIVISORS] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_MUL th]) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; CX_MUL; complex_div; COMPLEX_INV_MUL] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING
   `((ck * cn) * k' * n') * m * l = (cn * m * n') * l * (ck * k')`] THEN
  REWRITE_TAC[GSYM complex_div] THEN
  SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  EXISTS_TAC `&4 * B` THEN
  ASM_SIMP_TAC[REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN MATCH_MP_TAC VSUM_NORM_TRIANGLE THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
   `sum(1..x) (\n. inv(&n) * log(&x / &n) * B / (&(x DIV n) + &1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `n:num` THEN
    STRIP_TAC THEN REWRITE_TAC[] THEN ONCE_REWRITE_TAC[COMPLEX_NORM_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
     [REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_DIV; COMPLEX_NORM_CX] THEN
      FIRST_ASSUM(fun t -> SIMP_TAC[MATCH_MP DIRICHLET_CHARACTER_NORM t]) THEN
      COND_CASES_TAC THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_INV_EQ; REAL_POS] THEN
      REWRITE_TAC[REAL_MUL_LID; REAL_ABS_NUM] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
      ASM_SIMP_TAC[REAL_FIELD `&1 <= n ==> inv(n) * n = &1`; REAL_OF_NUM_LE;
                   REAL_ABS_MOBIUS];
      SIMP_TAC[CX_LOG; REAL_LT_DIV; REAL_OF_NUM_LT; LE_1] THEN
      SIMP_TAC[COMPLEX_NORM_CX; COMPLEX_NORM_MUL] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN SIMP_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[REAL_ARITH `abs x <= x <=> &0 <= x`] THEN
      ASM_SIMP_TAC[LOG_POS; REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; LE_1;
                   REAL_MUL_LID; REAL_OF_NUM_LE]];
    ALL_TAC] THEN
  SIMP_TAC[real_div; REAL_RING `a * l * B * i:real = ((l * i) * a) * B`] THEN
  REWRITE_TAC[SUM_RMUL] THEN ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..x) (\n. log(&x / &n) / &x)` THEN
  ASM_SIMP_TAC[REAL_ARITH `abs x <= a ==> x <= a`; SUM_LOG_OVER_X_BOUND] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[GSYM real_div; LOG_POS; REAL_LE_RDIV_EQ; REAL_OF_NUM_LT;
               LE_1; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_INV_INV] THEN
  REWRITE_TAC[GSYM REAL_INV_MUL] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LT_DIV; REAL_OF_NUM_LT; LE_1] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  MP_TAC(SPECL [`x:num`; `n:num`] DIVISION) THEN ASM_ARITH_TAC);;
```

### Informal statement
For all Dirichlet characters `d` and all complex-valued functions `c`, if `c` is a Dirichlet character with modulus `d`, `c` is not the trivial character `chi_0 d`, and the L-function `Lfunction c` evaluated at `1` (`Cx(&0)`) is zero, then the set of values obtained by summing `c n * mangoldt n / n` from `1` to `x` and adding `log(x)`, as `x` ranges over the natural numbers, is bounded.

### Informal sketch
The proof demonstrates that under the given conditions, the partial sums of the Dirichlet-Mangoldt series plus the logarithm function are bounded.

- The proof starts by relating the partial sum to the `Lfunction` via `LFUNCTION_PARTIAL_SUM_STRONG`.
- It uses the assumption `Lfunction c = Cx(&0)` to simplify the expression.
- The proof then introduces a bound `B` based on the assumption that the Dirichlet-Mangoldt series is bounded, using `BOUNDED_DIRICHLET_MANGOLDT_LEMMA`. This lemma is crucial in relating the Dirichlet-Mangoldt series to a bounded quantity.
- Multiple rewrite rules, especially using properties of complex numbers (`COMPLEX_ADD_SYM`, `COMPLEX_SUB_LZERO`, `NORM_NEG`, `COMPLEX_RING`, `complex_div`, `COMPLEX_INV_MUL`), are applied to manipulate the complex-valued expressions.
- Knowledge about `FINITE_DIVISORS` and `FINITE_NUMSEG` is used to rewrite sums over divisors and numerical segments.
- Properties of Dirichlet characters (`DIRICHLET_CHARACTER_MUL`, `DIRICHLET_CHARACTER_NORM`) are utilized.
- The proof involves bounding the norm of a sum by the sum of the norms `VSUM_NORM_TRIANGLE`.
- Then, bounding of the log term by using `SUM_LOG_OVER_X_BOUND`.
- Several arithmetic and real analysis results (e.g. `REAL_LT_MUL`, `REAL_OF_NUM_LT`, `LOG_POS`, `SUM_LE_NUMSEG`, `DIVISION`) are used to establish the bound.

### Mathematical insight
This theorem connects the vanishing of a Dirichlet L-function at 1 to the boundedness of a specific sum involving the Mangoldt function and the given Dirichlet character. The Mangoldt function is closely related to prime numbers, so this theorem implicitly relates the distribution of primes to the behavior of L-functions. The vanishing of the L-function at 1 is a special case, and this result suggests a constraint on the distribution of primes in arithmetic progressions.

### Dependencies
- `dirichlet_character`
- `chi_0`
- `Lfunction`
- `LFUNCTION_PARTIAL_SUM_STRONG`
- `COMPLEX_SUB_LZERO`
- `NORM_NEG`
- `BOUNDED_DIRICHLET_MANGOLDT_LEMMA`
- `GSYM VSUM_COMPLEX_LMUL`
- `FINITE_DIVISORS`
- `DIRICHLET_CHARACTER_MUL`
- `REAL_OF_NUM_MUL`
- `CX_MUL`
- `complex_div`
- `COMPLEX_INV_MUL`
- `COMPLEX_RING`
- `FINITE_NUMSEG`
- `REAL_LT_MUL`
- `REAL_OF_NUM_LT`
- `VSUM_NORM_TRIANGLE`
- `SUM_LOG_OVER_X_BOUND`
- `log`
- `DIVISION`

Real Analysis
- `LOG_POS`
- `REAL_LE_RDIV_EQ`
- `REAL_OF_NUM_LT`
- `LE_1`
- `REAL_MUL_LID`
- `REAL_OF_NUM_LE`
- `REAL_LE_LDIV_EQ`
### Porting notes (optional)
- The heavy use of complex number arithmetic and Dirichlet character properties will require careful translation of relevant libraries and definitions into another proof assistant.
- The proof relies heavily on rewrite tactics to simplify complex expressions. A similar automation strategy will be needed when porting.
- Boundedness proofs can be challenging in some proof assistants; ensure that your target system supports appropriate tools for reasoning about sets and real numbers.


---

## BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL_LEMMA

### Name of formal statement
BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL_LEMMA = prove
 (`!d. 1 <= d
       ==> norm(vsum(1..x) (\n. (chi_0 d n - Cx(&1)) * Cx(mangoldt n / &n)))
            <= sum {p | prime p /\ p divides d} (\p. log(&p))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {p | prime p /\ p divides d}
                  (\p. sum {k | 1 <= k /\ p EXP k <= x}
                           (\k. log(&p) / &p pow k))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[FINITE_SPECIAL_DIVISORS; LE_1] THEN
    X_GEN_TAC `p:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `2 <= p /\ 1 <= p /\ 1 < p` ASSUME_TAC THENL
     [ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 < p /\ 1 <= p`];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..x) (\k. log(&p) / &p pow k)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      ASM_SIMP_TAC[IN_DIFF; IN_NUMSEG; IN_ELIM_THM; SUBSET; REAL_POW_LE;
                   REAL_POS; REAL_LE_DIV; LOG_POS; REAL_OF_NUM_LE;
                   PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`] THEN
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `p EXP k` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP k` THEN
      ASM_SIMP_TAC[LT_POW2_REFL; LT_IMP_LE; EXP_MONO_LE];
      REWRITE_TAC[real_div; SUM_LMUL] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ; LOG_POS_LT; REAL_OF_NUM_LT] THEN
      SIMP_TAC[GSYM REAL_POW_INV; SUM_GP; REAL_INV_EQ_1; REAL_OF_NUM_EQ] THEN
      COND_CASES_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_SUB_LT; REAL_LT_LDIV_EQ;
                   REAL_MUL_LID; REAL_OF_NUM_LT; LE_1] THEN
      REWRITE_TAC[real_pow] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x * y /\ &2 * x <= &1
                                ==> x pow 1 - x * y <= &1 - x`) THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_POW_LE; REAL_POS; REAL_LE_MUL] THEN
      REWRITE_TAC[real_div; REAL_MUL_LID] THEN REWRITE_TAC[GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID; REAL_OF_NUM_LT;
                   REAL_OF_NUM_LE; LE_1]]] THEN
   W(MP_TAC o PART_MATCH (lhs o rand) SUM_SUM_PRODUCT o rand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_SPECIAL_DIVISORS; LE_1] THEN
      X_GEN_TAC `p:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `1..x` THEN
      SIMP_TAC[SUBSET; FINITE_NUMSEG; IN_NUMSEG; IN_ELIM_THM] THEN
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `p EXP k` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP k` THEN
      ASM_SIMP_TAC[LT_POW2_REFL; LT_IMP_LE; EXP_MONO_LE; PRIME_GE_2];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC VSUM_NORM_TRIANGLE THEN
    REWRITE_TAC[FINITE_NUMSEG; COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    REWRITE_TAC[chi_0; COND_RAND; COND_RATOR] THEN
    REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_SUB_LZERO] THEN
    REWRITE_TAC[COMPLEX_NORM_CX; NORM_NEG; REAL_ABS_NUM] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID] THEN
    REWRITE_TAC[mangoldt; COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ABS_NUM] THEN
    REWRITE_TAC[TAUT `(if a then &0 else if b then x else &0) =
                      (if ~a /\ b then x else &0)`] THEN
    SIMP_TAC[GSYM real_div; GSYM SUM_RESTRICT_SET; FINITE_NUMSEG] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SUM_EQ_GENERAL THEN EXISTS_TAC `\(p,k). p EXP k` THEN
    REWRITE_TAC[EXISTS_UNIQUE; EXISTS_PAIR_THM; FORALL_PAIR_THM] THEN
    REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG; PAIR_EQ] THEN CONJ_TAC THENL
     [X_GEN_TAC `y:num` THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:num` THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN
      STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      UNDISCH_TAC `~(coprime(p EXP k,d))` THEN
      ASM_SIMP_TAC[ONCE_REWRITE_RULE[COPRIME_SYM] COPRIME_PRIMEPOW; LE_1] THEN
      DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`q:num`; `j:num`] THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
      ASM_SIMP_TAC[EQ_PRIME_EXP] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `k:num`]  THEN
    ASM_SIMP_TAC[ONCE_REWRITE_RULE[COPRIME_SYM] COPRIME_PRIMEPOW; LE_1] THEN
    REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[EXP_EQ_0; LE_1; PRIME_0]; ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_POW; REAL_ABS_DIV; REAL_ABS_POW;
                REAL_ABS_NUM] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= y /\ x = y ==> abs x = y`) THEN
    ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_LE; PRIME_IMP_NZ; LE_1] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    X_GEN_TAC `q:num` THEN REWRITE_TAC[] THEN EQ_TAC THENL
     [ASM_MESON_TAC[PRIME_DIVEXP; DIVIDES_PRIME_PRIME];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `k = SUC(k - 1)` SUBST1_TAC THENL
       [ASM_ARITH_TAC; SIMP_TAC[EXP; DIVIDES_RMUL; DIVIDES_REFL]]]);;
```

### Informal statement
For all natural numbers `d`, if `1 <= d`, then the norm of the sum from `1` to `x` of the function that maps `n` to `(chi_0 d n - Cx(&1)) * Cx(mangoldt n / &n)` is less than or equal to the sum over the set of primes `p` such that `p` is prime and `p` divides `d` of the function that maps `p` to `log(&p)`.

### Informal sketch
The proof establishes an upper bound on a sum involving the principal Dirichlet character `chi_0` and the Mangoldt function. The main steps are:

- The proof starts by stripping the quantifier and assumption. Then a real inequality is transformed using `REAL_LE_TRANS`.
- An existential is used to instantiate the right hand side of the inequality with `sum {p | prime p /\ p divides d} (\p. sum {k | 1 <= k /\ p EXP k <= x} (\k. log(&p) / &p pow k))`.
- It splits the goal into two subgoals using `CONJ_TAC`.
- The second subgoal involves showing that `sum(1..x) (\n. (chi_0 d n - Cx(&1)) * Cx(mangoldt n / &n))` is less than or equal to `sum {p | prime p /\ p divides d} (\p. sum {k | 1 <= k /\ p EXP k <= x} (\k. log(&p) / &p pow k))`.
- A series of simplifications, rewriting, and transformations are applied, including using `SUM_LE`, `SUM_SUBSET_SIMPLE`, triangle inequality (`VSUM_NORM_TRIANGLE`), and properties of complex numbers (`COMPLEX_NORM_MUL`, `COMPLEX_NORM_CX`). The goal turns into manipulating `chi_0` and `mangoldt`.
- The proof involves reasoning about coprimality, divisors and prime powers. The tactic `ONCE_REWRITE_RULE[COPRIME_SYM] COPRIME_PRIMEPOW` is used. We also use `MONO_EXISTS`. The equality between the sums is proved by showing that the terms are equal using `SUM_EQ_GENERAL` and `EXISTS_UNIQUE`.
- The final steps focus on simplifying the real-valued expressions, using, facts about logarithms, powers, and inequalities (`REAL_ARITH`, `LOG_POS`, `REAL_ABS_DIV` etc), and properties about prime numbers (`PRIME_DIVEXP`, `DIVIDES_PRIME_PRIME`).

### Mathematical insight
The lemma provides an upper bound for a sum related to the Dirichlet character and the Mangoldt function. This type of bound is essential in analytic number theory, particularly when studying the distribution of prime numbers and related arithmetic functions. The lemma connects character sums to sums over prime divisors, which is a common strategy to reduce problems to the analysis of prime numbers.

### Dependencies
- Definitions: `chi_0`, `mangoldt`
- Theorems: `FINITE_SPECIAL_DIVISORS`, `LE_1`, `PRIME_GE_2`, `SUM_LE`, `SUM_SUBSET_SIMPLE`, `IN_DIFF`, `IN_NUMSEG`, `IN_ELIM_THM`, `SUBSET`, `REAL_POW_LE`, `REAL_POS`, `REAL_LE_DIV`, `LOG_POS`, `REAL_OF_NUM_LE`, `ARITH_RULE`, `LT_POW2_REFL`, `LT_IMP_LE`, `EXP_MONO_LE`, `real_div`, `SUM_LMUL`, `GSYM REAL_MUL_RID`, `REAL_LE_LMUL_EQ`, `LOG_POS_LT`, `REAL_OF_NUM_LT`, `GSYM REAL_POW_INV`, `SUM_GP`, `REAL_INV_EQ_1`, `REAL_OF_NUM_EQ`, `REAL_RAT_REDUCE_CONV`, `REAL_LE_LDIV_EQ`, `REAL_SUB_LT`, `REAL_LT_LDIV_EQ`, `REAL_MUL_LID`, `REAL_LE_DIV`, `REAL_POW_LE`, `REAL_LE_MUL`, `VSUM_NORM_TRIANGLE`, `FINITE_NUMSEG`, `COMPLEX_NORM_MUL`, `COMPLEX_NORM_CX`, `COMPLEX_SUB_REFL`, `COMPLEX_SUB_LZERO`, `NORM_NEG`, `REAL_ABS_NUM`, `REAL_MUL_LZERO`, `REAL_MUL_LID`, `COND_RAND`, `COND_RATOR`, `TAUT`, `GSYM real_div`, `GSYM SUM_RESTRICT_SET`, `REAL_EQ_IMP_LE`, `SYM_CONV`, `SUM_EQ_GENERAL`, `EXISTS_UNIQUE`, `EXISTS_PAIR_THM`, `FORALL_PAIR_THM`, `IN_ELIM_PAIR_THM`, `PAIR_EQ`, `MONO_EXISTS`, `ONCE_REWRITE_RULE[COPRIME_SYM] COPRIME_PRIMEPOW`, `EXP_EQ_0`, `PRIME_0`, `GSYM REAL_OF_NUM_POW`, `REAL_ABS_DIV`, `REAL_ABS_POW`, `PRIME_IMP_NZ`, `SELECT_UNIQUE`, `PRIME_DIVEXP`, `DIVIDES_PRIME_PRIME`

### Porting notes
- The frequent use of rewriting and simplification tactics suggests that a proof assistant with strong automation in these areas (e.g., Lean with `simp`, Coq with `simpl` and `auto`) would be beneficial.
- The reasoning about coprimality and divisibility of prime powers might require specific tactics or libraries in other proof assistants.
- Pay special attention to the definitions `chi_0` and `mangoldt` as their properties are crucial for the proof.


---

## BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL

### Name of formal statement
BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL = prove
 (`!d. 1 <= d
       ==> bounded { vsum(1..x) (\n. chi_0 d n * Cx(mangoldt n / &n)) -
                     Cx(log(&x)) | x IN (:num)}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bounded; SIMPLE_IMAGE; FORALL_IN_IMAGE; IN_UNIV] THEN
  EXISTS_TAC
   `abs(sum {p | prime p /\ p divides d} (\p. log(&p))) +
    abs(log(&0)) + &21` THEN
  X_GEN_TAC `x:num` THEN ASM_CASES_TAC `x = 0` THENL
   [ASM_SIMP_TAC[VSUM_CLAUSES_NUMSEG; ARITH; VECTOR_SUB_LZERO] THEN
    REWRITE_TAC[NORM_NEG; COMPLEX_NORM_CX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= a + b ==> x <= a + abs y + b`) THEN
  MATCH_MP_TAC(NORM_ARITH
   `!s'. norm(s') <= p /\ norm(s - s' - l) <= &21
        ==> norm(s - l) <= abs p + &21`) THEN
  EXISTS_TAC `vsum(1..x) (\n. (chi_0 d n - Cx(&1)) * Cx(mangoldt n / &n))` THEN
  ASM_SIMP_TAC[BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL_LEMMA] THEN
  SIMP_TAC[GSYM VSUM_SUB; FINITE_NUMSEG] THEN
  REWRITE_TAC[COMPLEX_RING `c * x - (c - Cx(&1)) * x = x`] THEN
  SIMP_TAC[GSYM CX_SUB; VSUM_CX; FINITE_NUMSEG; COMPLEX_NORM_CX] THEN
  MATCH_MP_TAC MERTENS_LEMMA THEN ASM_REWRITE_TAC[]);;
```

### Informal statement
For all positive integers `d`, the set of values obtained by the expression `vsum(1..x) (\n. chi_0 d n * Cx(mangoldt n / &n)) - Cx(log(&x))` as `x` ranges over the natural numbers is bounded. Here, `chi_0 d n` is the principal Dirichlet character modulo `d`, `mangoldt n` is the Mangoldt function evaluated at `n`, `Cx` converts a real number to a complex number, `vsum(1..x) f` denotes the sum of `f(n)` as `n` ranges from 1 to `x`, and `log(&x)` is the natural logarithm of `x` (converted to a real).

### Informal sketch
The proof proceeds as follows:

- The goal is to prove that for any positive integer `d`, the set `{ vsum(1..x) (\n. chi_0 d n * Cx(mangoldt n / &n)) - Cx(log(&x)) | x IN (:num)}` is bounded.
- The proof begins by rewriting using definitions of `bounded`, `SIMPLE_IMAGE`, `FORALL_IN_IMAGE`, and `IN_UNIV`. This reduces the problem to finding a constant bound.
- An existential quantifier is introduced, asserting the existence of a bound. The proposed bound is `abs(sum {p | prime p /\ p divides d} (\p. log(&p))) + abs(log(&0)) + &21`.
- A variable `x` is generalized using `X_GEN_TAC`. Then cases `x=0` is considered.
- In the case `x=0`, simplification is performed leading to reduction to a real arithmetic problem which is then solved.
- The proof then uses `MATCH_MP_TAC` with inequalities to introduce absolute values, which simplifies the expressions.
- An existential instantiation occurs with `vsum(1..x) (\n. (chi_0 d n - Cx(&1)) * Cx(mangoldt n / &n))`.
- A lemma `BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL_LEMMA` is applied, followed by simplification and rewriting rules involving sums, complex numbers, and finite sets.
- Finally, `MERTENS_LEMMA` is matched and applied.

### Mathematical insight
The theorem states a key result related to the distribution of prime numbers and Dirichlet characters. It shows that a certain sum involving the Mangoldt function, weighted by a Dirichlet character, when offset by the logarithm, remains bounded. This theorem is related to the prime number theorem for arithmetic progressions, and it provides a quantitative bound on the difference between the sum and the logarithm.

### Dependencies
- Definitions: `bounded`, `chi_0`, `mangoldt`, `Cx`, `vsum`, `log`
- Theorems/Lemmas: `BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL_LEMMA`, `MERTENS_LEMMA`, `VSUM_CLAUSES_NUMSEG`, `ARITH`, `VECTOR_SUB_LZERO`, `NORM_NEG`, `COMPLEX_NORM_CX`, `SIMPLE_IMAGE`, `FORALL_IN_IMAGE`, `IN_UNIV`, `GSYM VSUM_SUB`, `FINITE_NUMSEG`, `COMPLEX_RING`, `GSYM CX_SUB`, `VSUM_CX`, `FINITE_NUMSEG`

### Porting notes (optional)
- Ensure that the target proof assistant has well-defined notions of Dirichlet characters, the Mangoldt function, and complex numbers.
- The proof relies heavily on real and complex analysis, so ensure those libraries exist and are well-developed.
- The tactic `ASM_CASES_TAC `x = 0`` suggests a case split is required based on if x=0 which means you might need to handle possible exceptional values. Numerical values are also treated carefully and should be considered during the transition.


---

## SUM_OF_NUMBERS

### Name of formal statement
SUM_OF_NUMBERS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_OF_NUMBERS = prove
 (`!n. nsum(0..n) (\i. i) = (n * (n + 1)) DIV 2`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THEN ARITH_TAC);;
```
### Informal statement
For all natural numbers `n`, the sum of the numbers from 0 to `n` (inclusive) is equal to `(n * (n + 1)) / 2`.

### Informal sketch
The proof proceeds by mathematical induction on `n`.
- **Base Case (n=0):** Verify that the sum from 0 to 0 is (0 * (0 + 1)) / 2, which simplifies to 0 = 0.
- **Inductive Step:** Assume the formula holds for some `n`; that is, assume `nsum(0..n) (\i. i) = (n * (n + 1)) / 2`. We want to show that the formula holds for `n+1`; that is, we want to show `nsum(0..(n+1)) (\i. i) = ((n+1) * ((n+1) + 1)) / 2`.
    - Expand `nsum(0..(n+1)) (\i. i)` into `nsum(0..n) (\i. i) + (n+1)`.
    - Apply the inductive hypothesis to replace `nsum(0..n) (\i. i)` with `(n * (n + 1)) / 2`.
    - Now we have `(n * (n + 1)) / 2 + (n + 1)`.
    - Simplify the expression `(n * (n + 1)) / 2 + (n + 1)` to `((n+1) * (n+2)) / 2`, which is `((n+1) * ((n+1) + 1)) / 2`. This completes the inductive step.
- The arithmetic is handled by `ARITH_TAC`.

### Mathematical insight
This theorem states the well-known formula for the sum of the first `n` natural numbers. It is a fundamental result in discrete mathematics and is often used in various algorithmic analyses and mathematical proofs.

### Dependencies
- `NSUM_CLAUSES_NUMSEG`


---

## PRODUCT_POW_NSUM

### Name of formal statement
PRODUCT_POW_NSUM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PRODUCT_POW_NSUM = prove
 (`!s. FINITE s ==> product s (\i. z pow (f i)) = z pow (nsum s f)`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; NSUM_CLAUSES; real_pow; REAL_POW_ADD]);;
```
### Informal statement
For any set `s` that is finite, the product over `s` of the function mapping `i` to `z` raised to the power of `f i` is equal to `z` raised to the power of the sum over `s` of `f`.

### Informal sketch
The theorem states that the product of powers is the power of the sum. The proof is by strong induction on the finiteness of the set `s`.
- Base case: the empty set. The product over the empty set is 1 and the sum over the empty set is 0. The theorem then becomes `1 = z pow 0`, which is true.
- Inductive step: Assume the theorem holds for all finite subsets of `s`. We want to show that it holds for `s`. Let `x` be an element of `s`. Then `product s (\i. z pow (f i))` is equal to `(z pow (f x)) * (product (s minus x) (\i. z pow (f i)))`. By the inductive hypothesis, `product (s minus x) (\i. z pow (f i))` is equal to `z pow (nsum (s minus x) f)`. Thus, `product s (\i. z pow (f i))` is equal to `(z pow (f x)) * (z pow (nsum (s minus x) f))`, which equals `z pow ((f x) + nsum (s minus x) f)`, which equals `z pow (nsum s f)`.

The proof proceeds by strong induction on the finiteness of `s`, using `MATCH_MP_TAC FINITE_INDUCT_STRONG`. Then simplification is performed using `SIMP_TAC` with the clauses for `PRODUCT`, `NSUM`, and `real_pow`, specifically to deal with the power of a sum (`REAL_POW_ADD`).

### Mathematical insight
This theorem expresses a fundamental relationship between products, sums, and exponentiation. It is a generalization of the algebraic identity `z^(a+b) = z^a * z^b` to finite sets. This result can be useful in various contexts, such as probability theory, combinatorics, and analysis.

### Dependencies
- `FINITE_INDUCT_STRONG`
- `PRODUCT_CLAUSES`
- `NSUM_CLAUSES`
- `real_pow`
- `REAL_POW_ADD`

### Porting notes (optional)
- Ensure that the target proof assistant has a notion of finiteness for sets, as well as the definitions of `product` and `nsum` (summation over a set).
- The `real_pow` function might need to be replaced with an equivalent function for exponentiation in the target system.
- The inductive proof strategy should be adaptable to most proof assistants that support induction over finite sets.


---

## PRODUCT_SPECIAL

### Name of formal statement
PRODUCT_SPECIAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PRODUCT_SPECIAL = prove
 (`!z i. product (0..n) (\i. z pow i) = z pow ((n * (n + 1)) DIV 2)`,
  SIMP_TAC[PRODUCT_POW_NSUM; FINITE_NUMSEG; SUM_OF_NUMBERS]);;
```
### Informal statement
For all `z` and `n`, the product from `i = 0` to `n` of `z` raised to the power of `i` is equal to `z` raised to the power of `(n * (n + 1)) / 2`.

### Informal sketch
The proof proceeds by simplifying the expression `product (0..n) (\i. z pow i)`.
- First, `PRODUCT_POW_NSUM` is used to rewrite the product of powers into a power of a sum: `product (0..n) (\i. z pow i) = z pow (sum (0..n) (\i. i))`.
- Then, `FINITE_NUMSEG` is invoked to show that the set `{0, ..., n}` is finite.
- `SUM_OF_NUMBERS` is used to simplify the remaining summation expression: `sum (0..n) (\i. i) = (n * (n + 1)) DIV 2`.
- Combining these simplifications yields the desired result.

### Mathematical insight
This theorem establishes a closed-form expression for the product of consecutive powers of a number. It connects the product of powers to the power of a sum, then uses the well-known formula for the sum of integers from 0 to n, allowing for a concise representation of the original product.

### Dependencies
- Theorems: `PRODUCT_POW_NSUM`, `SUM_OF_NUMBERS`
- Definitions: `FINITE_NUMSEG`


---

## AGM_SPECIAL

### Name of formal statement
AGM_SPECIAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let AGM_SPECIAL = prove
 (`!n t. &0 <= t
         ==> (&n + &1) pow 2 * t pow n <= (sum(0..n) (\k. t pow k)) pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n + 1`; `\k. (t:real) pow (k - 1)`] AGM) THEN
  ASM_SIMP_TAC[REAL_POW_LE; ARITH_RULE `1 <= n + 1`] THEN
  SUBGOAL_THEN `1..n+1 = 0+1..n+1` SUBST1_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES]; ALL_TAC] THEN
  REWRITE_TAC[SUM_OFFSET; PRODUCT_OFFSET; ADD_SUB] THEN
  REWRITE_TAC[PRODUCT_SPECIAL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] REAL_POW_LE2)) THEN
  DISCH_THEN(MP_TAC o SPEC `2`) THEN
  ASM_SIMP_TAC[PRODUCT_POS_LE_NUMSEG; REAL_POW_LE] THEN
  REWRITE_TAC[REAL_POW_POW] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  SUBGOAL_THEN `2 * (n * (n + 1)) DIV 2 = n * (n + 1)` SUBST1_TAC THENL
   [SUBGOAL_THEN `EVEN(n * (n + 1))` MP_TAC THENL
     [REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH_EVEN] THEN CONV_TAC TAUT;
      SIMP_TAC[EVEN_EXISTS; LEFT_IMP_EXISTS_THM; DIV_MULT; ARITH]];
    REWRITE_TAC[GSYM REAL_POW_POW] THEN DISCH_THEN(MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] REAL_POW_LE2_REV)) THEN
    REWRITE_TAC[ADD_EQ_0; ARITH_EQ; REAL_POW_2; REAL_LE_SQUARE] THEN
    REWRITE_TAC[GSYM REAL_POW_2; GSYM REAL_OF_NUM_ADD] THEN
    ASM_SIMP_TAC[REAL_POW_DIV; REAL_LE_RDIV_EQ; REAL_POW_LT;
                 REAL_ARITH `&0 < &n + &1`] THEN
    REWRITE_TAC[REAL_MUL_AC]]);;
```

### Informal statement
For all natural numbers `n` and real numbers `t`, if `0 <= t`, then `(n + 1)^2 * t^n <= (sum(0..n) (\k. t^k))^2`.

### Informal sketch
The proof proceeds by induction on `n`. The base case is trivial. For the inductive step, assuming the statement holds for `n`, we aim to prove it for `n+1`.

- We apply the inductive hypothesis `AGM` with specific instantiations for `n` and the function.
- We simplify using inequalities related to real powers (`REAL_POW_LE`) and arithmetic.
- We rewrite the summation range `1..n+1` as `0+1..n+1`.
- We rewrite the summation to isolate the first term using `SUM_OFFSET` and `PRODUCT_OFFSET` lemmas.
- This step uses the inequality `PRODUCT_POS_LE_NUMSEG`, `REAL_POW_LE`, and rewrites concerning powers, multiplication.
- We simplify an expression about the division of `2 * (n * (n + 1)) DIV 2 = n * (n + 1)` by proving that `n * (n + 1)` divides evenly by 2.
- Then, the proof involves rewriting using properties of real powers (`REAL_POW_POW`, `REAL_POW_LE2`, and variations), addition, and arithmetic equations (`ADD_EQ_0`, `ARITH_EQ`). Finally, we simplify using properties of real powers with division, positivity conditions (`REAL_POW_DIV`, `REAL_LE_RDIV_EQ`, REAL_POW_LT), and ensure n+1 is positive which gives a final result by rewriting commutatively.

### Mathematical insight
The theorem `AGM_SPECIAL` relates a scaled power of `t` to the square of a geometric series. It likely forms part of a larger development concerning inequalities and the convergence or bounding of sums, with the inductive proof likely leveraging properties of the geometric mean and power functions.

### Dependencies
- `REAL_POW_LE`
- `AGM`
- `ARITH_RULE`
- `ADD_CLAUSES`
- `SUM_OFFSET`
- `PRODUCT_OFFSET`
- `ADD_SUB`
- `PRODUCT_SPECIAL`
- `IMP_CONJ_ALT`
- `REAL_POW_LE2`
- `PRODUCT_POS_LE_NUMSEG`
- `REAL_POW_POW`
- `MULT_SYM`
- `EVEN_ADD`
- `EVEN_MULT`
- `ARITH_EVEN`
- `EVEN_EXISTS`
- `LEFT_IMP_EXISTS_THM`
- `DIV_MULT`
- `GSYM`
- `REAL_POW_LE2_REV`
- `ADD_EQ_0`
- `ARITH_EQ`
- `REAL_POW_2`
- `REAL_LE_SQUARE`
- `REAL_OF_NUM_ADD`
- `REAL_POW_DIV`
- `REAL_LE_RDIV_EQ`
- `REAL_POW_LT`
- `REAL_ARITH`
- `REAL_MUL_AC`


---

## DIVISORSUM_PRIMEPOW

### Name of formal statement
DIVISORSUM_PRIMEPOW

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIVISORSUM_PRIMEPOW = prove
 (`!f p k. prime p
           ==> sum {m | m divides (p EXP k)} c = sum(0..k) (\i. c(p EXP i))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[DIVIDES_PRIMEPOW; SET_RULE
   `{m | ?i. P i /\ m = f i} = IMAGE f {i | P i}`] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
  REWRITE_TAC[GSYM NUMSEG_LE] THEN MATCH_MP_TAC SUM_IMAGE THEN
  ASM_SIMP_TAC[IN_ELIM_THM; EQ_EXP; FINITE_NUMSEG_LE] THEN
  ASM_MESON_TAC[PRIME_0; PRIME_1]);;
```
### Informal statement
For all functions `f`, prime numbers `p`, and natural numbers `k`, if `p` is prime, then the sum of `f(m)` over all `m` that divide `p^k` is equal to the sum of `f(p^i)` for `i` ranging from 0 to `k`.

### Informal sketch
The proof proceeds as follows:
- Start by stripping the quantifiers and assuming `prime p`.
- Rewrite the set `{m | m divides (p EXP k)}` as `IMAGE (p EXP) {i | i <= k}`, where `p EXP` is written as `p^i`.  This uses the theorem `DIVIDES_PRIMEPOW` which enumerates the divisors of a prime power and the fact that `{m | ?i. P i /\ m = f i} = IMAGE f {i | P i}`.
- Rewrite `p EXP i` as `p^i`.
- Rewrite `0 <= i /\ i <= k` as `i IN numseg k`.
- Apply the `SUM_IMAGE` theorem.
- Simplify using the fact that `i IN numseg k` is equivalent to `i <= k`, as well as theorems about exponentiation (`EQ_EXP`), and finiteness of numerical segments (`FINITE_NUMSEG_LE`).
- Apply `ASM_MESON_TAC` with theorems `PRIME_0` and `PRIME_1` to complete the proof.

### Mathematical insight
This theorem provides a way to compute the divisor sum of a prime power where the function being summed is expressible in terms of powers of that prime. It leverages the fact that divisors of `p^k` are precisely `p^0, p^1, ..., p^k`. This is valuable in number theory for analyzing multiplicative functions.

### Dependencies
- `DIVIDES_PRIMEPOW`: Defines the divisors of prime powers.
- `SET_RULE`
- `GSYM o_DEF`
- `NUMSEG_LE`
- `SUM_IMAGE`: A theorem about summing over the image of a function.
- `IN_ELIM_THM`: Elimination rule for set membership.
- `EQ_EXP`: Properties of exponentiation.
- `FINITE_NUMSEG_LE`: Finiteness of numerical segments.
- `PRIME_0`: 0 is not prime.
- `PRIME_1`: 1 is not prime.

### Porting notes (optional)
The key is to have a good representation of divisibility and a way to enumerate the divisors of a prime power. The `SUM_IMAGE` theorem has an equivalent in most proof assistants. The automation may need to be adjusted to account for the specific theorems available. The set comprehension and image construction are standard features.


---

## DIVISORVSUM_PRIMEPOW

### Name of formal statement
DIVISORVSUM_PRIMEPOW

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIVISORVSUM_PRIMEPOW = prove
 (`!f p k. prime p
           ==> vsum {m | m divides (p EXP k)} c = vsum(0..k) (\i. c(p EXP i))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[DIVIDES_PRIMEPOW; SET_RULE
   `{m | ?i. P i /\ m = f i} = IMAGE f {i | P i}`] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
  REWRITE_TAC[GSYM NUMSEG_LE] THEN MATCH_MP_TAC VSUM_IMAGE THEN
  ASM_SIMP_TAC[IN_ELIM_THM; EQ_EXP; FINITE_NUMSEG_LE] THEN
  ASM_MESON_TAC[PRIME_0; PRIME_1]);;
```
### Informal statement
For any function `f`, any prime number `p`, and any natural number `k`, if `p` is prime, then the summation of `c(m)` over all `m` that divide `p` to the power of `k` is equal to the summation of `c(p` to the power of `i)` with `i` ranging from 0 to `k`.

### Informal sketch
The proof proceeds by:
- Stripping the quantifiers and assumptions.
- Simplifying using `DIVIDES_PRIMEPOW` which characterizes the divisors of a prime power, and rewriting the set comprehension using `IMAGE` to convert the set of divisors into the image of exponentiation by `p`.
- Rewriting `o_DEF` (composition of functions) and `NUMSEG_LE` (natural number segment).
- Applying `VSUM_IMAGE` to change the summation over the image of a set to a summation over the original set.
- Simplifying using theorems about set membership (`IN_ELIM_THM`), exponentiation (`EQ_EXP`), and finiteness of number segments (`FINITE_NUMSEG_LE`).
- Using `ASM_MESON_TAC` with `PRIME_0` (0 is not prime) and `PRIME_1` (1 is not prime) to complete the proof.

### Mathematical insight
This theorem provides a formula for calculating the divisor sum of a prime power. It decomposes the sum over all divisors into a sum over powers of the prime, greatly simplifying computation of divisor sums in specific cases (e.g. when `c` is a simple function.) It expresses a useful property in number theory, allowing efficient computations involving the divisor sum function, especially when dealing with prime powers.

### Dependencies
- `DIVIDES_PRIMEPOW`
- `SET_RULE`
- `o_DEF`
- `NUMSEG_LE`
- `VSUM_IMAGE`
- `IN_ELIM_THM`
- `EQ_EXP`
- `FINITE_NUMSEG_LE`
- `PRIME_0`
- `PRIME_1`


---

## DIRICHLET_CHARACTER_DIVISORSUM_EQ_1

### Name of formal statement
DIRICHLET_CHARACTER_DIVISORSUM_EQ_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_DIVISORSUM_EQ_1 = prove
 (`!d c p k. dirichlet_character d c /\ prime p /\ p divides d
             ==> vsum {m | m divides (p EXP k)} c = Cx(&1)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `vsum {1} c : complex` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[VSUM_SING] THEN ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_1]] THEN
  MATCH_MP_TAC VSUM_SUPERSET THEN
  SIMP_TAC[SUBSET; IN_SING; IN_ELIM_THM; DIVIDES_1] THEN
  ASM_SIMP_TAC[DIVIDES_PRIMEPOW; LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`y:num`; `i:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[COMPLEX_VEC_0] THEN
  FIRST_ASSUM(fun th -> SIMP_TAC[MATCH_MP DIRICHLET_CHARACTER_EQ_0 th]) THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN REWRITE_TAC[COPRIME_REXP] THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[EXP] THEN
  ASM_MESON_TAC[COPRIME_SYM; PRIME_COPRIME_EQ]);;
```
### Informal statement
For all Dirichlet characters `d` and complex number `c`, for all primes `p`, and for all natural numbers `k`, if `d` is a Dirichlet character with conductor `c` and `p` is a prime number and `p` divides `d`, then the sum of `c` over the set of divisors of `p` to the power of `k` is equal to the complex number 1.

### Informal sketch
The proof proceeds by showing that the sum of the Dirichlet character values over the divisors of `p^k` equals `Cx(&1)` when `p` divides the conductor `d`.

- First, we aim to show `vsum {m | m divides (p EXP k)} c = Cx(&1)`.
- The first step is to use `EQ_TRANS` to replace the sum by `vsum {1} c` after showing that `vsum {m | m divides (p EXP k)} c = vsum {1} c`. The right-hand side is shown to be `Cx(&1)` using `VSUM_SING` and `DIRICHLET_CHARACTER_EQ_1`.
- To prove the equality of the two sums, we aim to use `VSUM_SUPERSET`.
- Simplify the condition `subset {m | m divides (p EXP k)} {1}` to `1 divides (p EXP k)`. We show that 1 divides `p EXP k` using `DIVIDES_1`.
- We rewrite the condition for membership of `m` in the first set using `DIVIDES_PRIMEPOW`: `m divides (p EXP k)` which is equivalent to `EXISTS y. m = p EXP y /\ y <= k`.
- Now we have the antecedent `prime p /\ p divides d /\ p EXP y divides d`.
- We discharge the assumption `prime p /\ p divides d` and show that if `y > 0` then `c(p EXP y) = Cx(&0)`.
- The proof proceeds by cases on `i = 0`. If `i = 0`, then `p EXP i = 1` and `c((RE(p), 0) ^ i) = c((&1, &0)) = Cx(&1)` because `(&1, &0)` is coprime the conductor of `c`.
- If `i > 0`, the result follows because `prime p`, and therefore `p EXP y` and `d` are not coprime.

### Mathematical insight
This theorem relates the divisors of a prime power to the value of the Dirichlet character. It says that if `p` divides the conductor `d`, then the Dirichlet character sums to 1. This result is a consequence of the properties of Dirichlet characters and how their values depend on the divisors of the conductor.

### Dependencies
- `DIRICHLET_CHARACTER`
- `prime`
- `divides`
- `vsum`
- `VSUM_SING`
- `VSUM_SUPERSET`
- `SUBSET`
- `IN_SING`
- `IN_ELIM_THM`
- `DIVIDES_1`
- `DIVIDES_PRIMEPOW`
- `LEFT_AND_EXISTS_THM`
- `LEFT_IMP_EXISTS_THM`
- `COMPLEX_VEC_0`
- `DIRICHLET_CHARACTER_EQ_0`
- `DIRICHLET_CHARACTER_EQ_1`
- `COPRIME_SYM`
- `COPRIME_REXP`
- `EXP`
- `PRIME_COPRIME_EQ`


---

## DIRICHLET_CHARACTER_REAL_CASES

### Name of formal statement
DIRICHLET_CHARACTER_REAL_CASES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_REAL_CASES = prove
 (`!d c. dirichlet_character d c /\ (!n. real(c n))
         ==> !n. c n = --Cx(&1) \/ c n = Cx(&0) \/ c n = Cx(&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP DIRICHLET_CHARACTER_NORM) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[REAL_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` SUBST1_TAC) THEN
  REWRITE_TAC[COMPLEX_NORM_CX; GSYM CX_NEG; CX_INJ] THEN REAL_ARITH_TAC);;
```

### Informal statement
For all `d` and `c`, if `c` is a Dirichlet character modulo `d` and the range of `c` is contained in the real numbers, then for all `n`, either `c n = -1`, or `c n = 0`, or `c n = 1`.

### Informal sketch
The proof proceeds as follows:
- Assume `c` is a Dirichlet character Mod `d` (`dirichlet_character d c`) and `c n` is real for all `n`
- Fix an arbitrary number `n`.
- Apply `DIRICHLET_CHARACTER_NORM` and specialize it to `n:num` and then use it to simplify the assumption `dirichlet_character d c`. This yields `complex_norm (c n) = 1 \/ c n = Cx(&0)`.
- Specialize the assumption `!n. real(c n)` with the fixed `n`.
- Rewrite using `REAL_EXISTS` to obtain a real number `t` such that `c n = Cx t`.
- Rewrite using `COMPLEX_NORM_CX` and `CX_NEG` and `CX_INJ` yielding `t = &0 \/ t = &1 \/ t = -- &1`.
- Apply real arithmetic to complete the proof, handling the three cases where c(n) = 0, c(n) = 1, c(n) = -1.

### Mathematical insight
This theorem states that if a Dirichlet character is real-valued, then its values can only be -1, 0, or 1. This is a fundamental property of real Dirichlet characters and is crucial in many number-theoretic applications.

### Dependencies
- `dirichlet_character`
- `DIRICHLET_CHARACTER_NORM`
- `REAL_EXISTS`
- `COMPLEX_NORM_CX`
- `CX_NEG`
- `CX_INJ`


---

## DIRICHLET_CHARACTER_DIVISORSUM_PRIMEPOW_POS

### Name of formal statement
DIRICHLET_CHARACTER_DIVISORSUM_PRIMEPOW_POS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_DIVISORSUM_PRIMEPOW_POS = prove
 (`!d c p k. dirichlet_character d c /\ (!n. real(c n)) /\ prime p
             ==> &0 <= Re(vsum {m | m divides (p EXP k)} c)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RE_VSUM; FINITE_DIVISORS; EXP_EQ_0; PRIME_IMP_NZ] THEN
  ASM_SIMP_TAC[DIVISORSUM_PRIMEPOW] THEN
  FIRST_ASSUM(fun th -> SIMP_TAC[MATCH_MP DIRICHLET_CHARACTER_POW th]) THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`] DIRICHLET_CHARACTER_REAL_CASES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `p:num`) THEN STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM CX_POW; RE_CX; SUM_POS_LE_NUMSEG;
               REAL_POW_LE; REAL_POS] THEN
  MATCH_MP_TAC(REAL_ARITH `(s = if EVEN k then &1 else &0) ==> &0 <= s`) THEN
  SPEC_TAC(`k:num`,`r:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[EVEN; SUM_CLAUSES_NUMSEG] THEN
  ASM_REWRITE_TAC[complex_pow; RE_CX; LE_0] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[COMPLEX_POW_NEG; COMPLEX_POW_ONE; COMPLEX_MUL_LNEG;
                  COMPLEX_MUL_RNEG; COMPLEX_NEG_NEG; COMPLEX_MUL_LID;
                  RE_NEG; RE_CX] THEN
  REAL_ARITH_TAC);;
```
### Informal statement
For all `d`, `c`, `p`, and `k`, if `d` is a Dirichlet character and `c` is a function such that `c n` is a real number for all `n`, and `p` is a prime number, then 0 is less than or equal to the real part of the sum of `c m` over all `m` that divide `p^k`.

### Informal sketch
The proof proceeds as follows:

- Start by stripping the quantifiers and the assumptions. Simplify using rewriting rules about `RE_VSUM`, `FINITE_DIVISORS`, `EXP_EQ_0`, and `PRIME_IMP_NZ`.
- Simplify further using `DIVISORSUM_PRIMEPOW`.
- Use `DIRICHLET_CHARACTER_POW` to simplify assumptions about Dirichlet characters.
- Apply case analysis on whether `d` is a real Dirichlet character using `DIRICHLET_CHARACTER_REAL_CASES`, discharging the assumption `p` is a number.
- Rewrite using assumptions.
- Simplify using rewriting rules such as `GSYM CX_POW`, `RE_CX`, `SUM_POS_LE_NUMSEG`, `REAL_POW_LE`, and `REAL_POS`.
- Use the arithmetic fact that if `s` is 1 if `k` is even and 0 otherwise, then `0 <= s`.
- Perform induction on `k`.
- Rewrite using `EVEN` and `SUM_CLAUSES_NUMSEG`.
- Simplify using rewriting rules such as `complex_pow`, `RE_CX`, `LE_0`.
- Perform case analysis.
- Simplify using rewriting rules for complex numbers, such as `COMPLEX_POW_NEG`, `COMPLEX_POW_ONE`, `COMPLEX_MUL_LNEG`, `COMPLEX_MUL_RNEG`, `COMPLEX_NEG_NEG`, `COMPLEX_MUL_LID`, `RE_NEG`, `RE_CX`.
- Finish by using real arithmetic.

### Mathematical insight
This theorem provides a lower bound (non-negativity) on the real part of a divisor sum involving a Dirichlet character and a real-valued function when the divisors are powers of a prime. It is crucial in analytic number theory when working with Dirichlet L-functions and related arithmetic functions. The positivity result is non-trivial and relies on the properties of Dirichlet characters and their interaction with prime powers in the divisor sum.

### Dependencies
- `DIRICHLET_CHARACTER_DIVISORSUM_PRIMEPOW_POS` depends on the following:
  - Definitions:
    - `dirichlet_character`
  - Theorems:
    - `RE_VSUM`
    - `FINITE_DIVISORS`
    - `EXP_EQ_0`
    - `PRIME_IMP_NZ`
    - `DIVISORSUM_PRIMEPOW`
    - `DIRICHLET_CHARACTER_POW`
    - `DIRICHLET_CHARACTER_REAL_CASES`
    - `GSYM CX_POW`
    - `RE_CX`
    - `SUM_POS_LE_NUMSEG`
    - `REAL_POW_LE`
    - `REAL_POS`
    - `EVEN`
    - `SUM_CLAUSES_NUMSEG`
    - `complex_pow`
    - `LE_0`
    - `COMPLEX_POW_NEG`
    - `COMPLEX_POW_ONE`
    - `COMPLEX_MUL_LNEG`
    - `COMPLEX_MUL_RNEG`
    - `COMPLEX_NEG_NEG`
    - `COMPLEX_MUL_LID`
    - `RE_NEG`


---

## DIRICHLET_CHARACTER_DIVISORSUM_POS

### Name of formal statement
DIRICHLET_CHARACTER_DIVISORSUM_POS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_DIVISORSUM_POS = prove
 (`!d c n. dirichlet_character d c /\ (!n. real(c n)) /\ ~(n = 0)
           ==> &0 <= Re(vsum {m | m divides n} c)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `~(n = 0) ==> n = 1 \/ 1 < n`))
  THENL
   [ASM_SIMP_TAC[DIVIDES_ONE; SING_GSPEC; VSUM_SING] THEN
    ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_1; RE_CX; REAL_POS];
    ALL_TAC] THEN
  UNDISCH_TAC `1 < n` THEN SPEC_TAC(`n:num`,`n:num`) THEN
  MATCH_MP_TAC INDUCT_COPRIME_STRONG THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[DIRICHLET_CHARACTER_DIVISORSUM_PRIMEPOW_POS]] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `\m:num. Re(c m)` REAL_MULTIPLICATIVE_DIVISORSUM) THEN
  REWRITE_TAC[real_multiplicative] THEN ANTS_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_MUL th]) THEN
    ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_1; RE_CX; REAL; CX_MUL];
  DISCH_THEN(MP_TAC o SPECL [`a:num`; `b:num`] o CONJUNCT2) THEN
  ASM_SIMP_TAC[GSYM RE_VSUM; FINITE_DIVISORS; MULT_EQ_0;
               ARITH_RULE `1 < n ==> ~(n = 0)`; REAL_LE_MUL]]);;
```

### Informal statement
For all Dirichlet characters `d`, functions `c` from numbers to complex numbers, and natural numbers `n`, if `d` is a Dirichlet character, and `c(n)` is a real number for all `n`, and `n` is not zero, then `0 <= Re(vsum {m | m divides n} c)`.
That is, the real part of the divisor sum of `c` over the divisors of `n` is non-negative.

### Informal sketch
The proof proceeds by induction on `n`.

- Base Case: If `n = 1`, then the divisors of `n` are just `{1}`, and the `vsum` is just `c(1)`.  Since `c(1)` is real, and `d` is a Dirichlet character (so `c(1) = 1`, by `DIRICHLET_CHARACTER_EQ_1`), it follows that `Re(c(1)) = 1 >= 0`.
- Inductive Step: Assume that for all `k < n`, if `d` is a Dirichlet character and `c(k)` is real for all `k`, then `0 <= Re(vsum {m | m divides k} c)`. We have two cases:
   - `n` is coprime, which is handled by `DIRICHLET_CHARACTER_DIVISORSUM_PRIMEPOW_POS`.
   - `n = a * b`. Use the fact that `Re(c(m))` is a real multiplicative divisor sum, and apply `REAL_MULTIPLICATIVE_DIVISORSUM`.
      - The goal reduces to proving `(!a b. Re(vsum {m | m divides a} c) * Re(vsum {m | m divides b} c) >= 0`, which is verified by induction hypothesis, and the fact that reals are closed under multiplication (`REAL_LE_MUL`).

### Mathematical insight
This theorem establishes that the divisor sum of a real-valued function `c` associated with a Dirichlet character is non-negative. This is an important property when studying Dirichlet characters and their relationship to number theory and L-functions. The theorem leverages the multiplicative property of Dirichlet characters and the divisor sum function to prove the non-negativity result.

### Dependencies
- `dirichlet_character`
- `DIVIDES_ONE`
- `SING_GSPEC`
- `VSUM_SING`
- `DIRICHLET_CHARACTER_EQ_1`
- `RE_CX`
- `REAL_POS`
- `INDUCT_COPRIME_STRONG`
- `DIRICHLET_CHARACTER_DIVISORSUM_PRIMEPOW_POS`
- `REAL_MULTIPLICATIVE_DIVISORSUM`
- `DIRICHLET_CHARACTER_MUL`
- `REAL`
- `CX_MUL`
- `GSYM RE_VSUM`
- `FINITE_DIVISORS`
- `MULT_EQ_0`
- `REAL_LE_MUL`


---

## lemma

### Name of formal statement
lemma

### Type of the formal statement
theorem

### Formal Content
```ocaml
let lemma = prove
 (`!x n. &0 <= x /\ x <= &1 ==> &1 - &n * x <= (&1 - x) pow n`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[real_pow] THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 - x) * (&1 - &n * x)` THEN
  ASM_SIMP_TAC[REAL_LE_LMUL; REAL_SUB_LE; GSYM REAL_OF_NUM_SUC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= n * x * x ==> &1 - (n + &1) * x <= (&1 - x) * (&1 - n * x)`) THEN
  SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LE_SQUARE]);;
```
### Informal statement
For all real numbers `x` and natural numbers `n`, if `0 <= x` and `x <= 1`, then `1 - n * x <= (1 - x) pow n`.

### Informal sketch
The proof proceeds by induction on `n`.
- Base case: `n = 0`. We need to show `1 <= 1 pow 0`, which simplifies to `1 <= 1`, which is true.
- Inductive step: Assume `1 - n * x <= (1 - x) pow n` for some `n`. We must show `1 - (n + 1) * x <= (1 - x) pow (n + 1)`.
    - The step starts with `1 - n * x <= (1 - x) pow n`.
    - The goal is to prove an inequality of the form `1 - (n + 1) * x <= (1 - x) * (1 - x) pow n`.
    - The proof uses the inductive hypothesis `1 - n * x <= (1 - x) pow n` and the condition `0 <= x <= 1`. This condition implies `0 <= 1 - x`, i.e. `1-x` is nonnegative.
    - The step uses `REAL_LE_LMUL` to multiply both sides of `1 - n * x <= (1 - x) pow n` by `1 - x`. By `REAL_LE_LMUL` the multiplication is valid since `0 <= 1 -x` which is true because we know `x <= 1` from predicate of the lemma.
    - The tactic `MATCH_MP_TAC (REAL_ARITH ...)` uses the fact that `0 <= n * x * x ==> 1 - (n + 1) * x <= (1 - x) * (1 - n * x)`.
    - Uses transitivity of inequalities (`REAL_LE_TRANS`) with `(1 - x) * (1 - n * x)` is the intermediate inequality.
    - The remaining part relies on showing `1 - (n + 1) * x <= (1 - x) * (1 - n * x)`, which arises after multiplying the induction hypothesis' RHS by `(1-x)`.

### Mathematical insight
This theorem establishes an inequality between a linear term and a power of `(1 - x)`. It provides a lower bound for `(1-x)^n`.

### Dependencies
- `RIGHT_FORALL_IMP_THM`
- `real_pow`
- `REAL_LE_TRANS`
- `REAL_LE_LMUL`
- `REAL_SUB_LE`
- `GSYM REAL_OF_NUM_SUC`
- `REAL_ARITH`
- `REAL_LE_MUL`
- `REAL_POS`
- `REAL_LE_SQUARE`

### Porting notes (optional)
The proof relies heavily on `REAL_ARITH` to discharge arithmetic subgoals. A similar tactic or decision procedure will be needed in other proof assistants. `REAL_LE_LMUL` is used to multiply both sides of an inequality by a non-negative number. Care should be exercised to ensure that the equivalent tactic in another proof assistant accounts for non-negativity during multiplication of inequalities.


---

## LFUNCTION_NONZERO_REAL

### Name of formal statement
LFUNCTION_NONZERO_REAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LFUNCTION_NONZERO_REAL = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d) /\ (!n. real(c n))
         ==> ~(Lfunction c = Cx(&0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`]
   DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. norm(z) < &1
        ==> summable (from 1) (\n. c(n) * z pow n / (Cx(&1) - z pow n))`
  MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THENL
     [MATCH_MP_TAC SUMMABLE_FROM_ELSEWHERE THEN EXISTS_TAC `2` THEN
      MATCH_MP_TAC SUMMABLE_EQ THEN EXISTS_TAC `\n:num. Cx(&0)` THEN
      REWRITE_TAC[GSYM COMPLEX_VEC_0; SUMMABLE_0] THEN
      ASM_SIMP_TAC[COMPLEX_VEC_0; COMPLEX_POW_ZERO; IN_FROM;
                   ARITH_RULE `2 <= n ==> ~(n = 0)`] THEN
      CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    MATCH_MP_TAC SERIES_COMPARISON_COMPLEX THEN
    EXISTS_TAC `\n. Cx(&2 * norm(z:complex) pow n)` THEN
    REWRITE_TAC[REAL_CX; RE_CX] THEN
    SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_POW_LE; NORM_POS_LE] THEN
    ASM_SIMP_TAC[CX_MUL; CX_POW; SUMMABLE_COMPLEX_LMUL; COMPLEX_NORM_CX;
                 REAL_ABS_NORM; SUMMABLE_GP] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL] THEN
    FIRST_ASSUM(fun th -> SIMP_TAC[MATCH_MP DIRICHLET_CHARACTER_NORM th]) THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_ABS_POS; REAL_LE_MUL] THEN
    REWRITE_TAC[TAUT `(p ==> (if q then x else T)) <=> p /\ q ==> x`] THEN
    MP_TAC(SPECL [`norm(z:complex)`; `&1 / &2`] REAL_ARCH_POW_INV) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[GE] THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NORM; REAL_ABS_NUM; REAL_ABS_POW] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[complex_div; COMPLEX_NORM_MUL; COMPLEX_NORM_POW] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; NORM_POS_LE] THEN
    REWRITE_TAC[COMPLEX_NORM_INV] THEN
    SUBST1_TAC(REAL_ARITH `&2 = inv(&1 / &2)`) THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(z) <= norm(w) - h ==> h <= norm(w - z)`) THEN
    REWRITE_TAC[COMPLEX_NORM_CX] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(z:complex) pow N` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REWRITE_TAC[COMPLEX_NORM_POW] THEN
    MATCH_MP_TAC REAL_POW_MONO_INV THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[summable; RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:complex->complex` (LABEL_TAC "+")) THEN
  ABBREV_TAC `b = \z n. inv(Cx(&n) * (Cx(&1) - z)) -
                        z pow n / (Cx(&1) - z pow n)` THEN
  SUBGOAL_THEN
   `!z:complex. norm(z) < &1 ==> ((\n. c(n) * b z n) sums --(f z)) (from 1)`
   (LABEL_TAC "*")
  THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "b" THEN
    REWRITE_TAC[COMPLEX_SUB_LDISTRIB; GSYM COMPLEX_SUB_LZERO] THEN
    MATCH_MP_TAC SERIES_SUB THEN ASM_SIMP_TAC[GSYM COMPLEX_SUB_LDISTRIB] THEN
    REWRITE_TAC[COMPLEX_INV_MUL; COMPLEX_MUL_ASSOC] THEN
    SUBST1_TAC(COMPLEX_RING `Cx(&0) = Cx(&0) * inv(Cx(&1) - z)`) THEN
    MATCH_MP_TAC SERIES_COMPLEX_RMUL THEN
    MP_TAC(SPECL [`d:num`; `c:num->complex`] LFUNCTION) THEN
    ASM_REWRITE_TAC[complex_div];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. norm(z) < &1
                    ==> ((\n. vsum {d | d divides n} (\d. c d) * z pow n) sums
                         f(z)) (from 1)`
  (LABEL_TAC "+") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[sums; FROM_INTER_NUMSEG] THEN
    SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_DIVISORS; LE_1] THEN
    REWRITE_TAC[VSUM_VSUM_DIVISORS] THEN
    REMOVE_THEN "+" (MP_TAC o SPEC `z:complex`) THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG; sums; FROM_INTER_NUMSEG] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM) THEN
    SIMP_TAC[GSYM VSUM_SUB; FINITE_NUMSEG] THEN
    REWRITE_TAC[GSYM COMPLEX_SUB_LDISTRIB] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[GSYM COMPLEX_POW_POW] THEN
    REWRITE_TAC[VSUM_GP; ARITH_RULE `n < 1 <=> n = 0`] THEN
    SIMP_TAC[DIV_EQ_0; LE_1] THEN SIMP_TAC[GSYM NOT_LE] THEN
    SUBGOAL_THEN `!k. 1 <= k ==> ~(z pow k = Cx(&1))` (fun th -> SIMP_TAC[th])
    THENL [ASM_MESON_TAC[COMPLEX_POW_EQ_1; LE_1; REAL_LT_REFL]; ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_POW_1; complex_div] THEN
    REWRITE_TAC[COMPLEX_RING `(zx * i - (zx - w) * i) = w * i`] THEN
    SIMP_TAC[COMPLEX_POW_POW] THEN MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\x. vsum (1..x)
                       (\n. z pow x * c n *
                            z pow (n - x MOD n) / (Cx(&1) - z pow n))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `x:num` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
      X_GEN_TAC `n:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC[complex_div; COMPLEX_INV_MUL; COMPLEX_MUL_ASSOC] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      ONCE_REWRITE_TAC[COMPLEX_RING `(zx * cn) * zn = cn * zx * zn`] THEN
      AP_TERM_TAC THEN REWRITE_TAC[GSYM COMPLEX_POW_ADD] THEN
      AP_TERM_TAC THEN REWRITE_TAC[MULT_CLAUSES] THEN
      MP_TAC(SPECL [`x:num`; `n:num`] DIVISION) THEN ASM_SIMP_TAC[LE_1] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_VEC_0] THEN
    MATCH_MP_TAC LIM_NULL_COMPARISON_COMPLEX THEN
    EXISTS_TAC `\x. Cx(norm(z) / (&1 - norm z)) * Cx(&x) * z pow x` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `x:num` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC VSUM_NORM_TRIANGLE THEN
      REWRITE_TAC[FINITE_NUMSEG; COMPLEX_NORM_MUL; COMPLEX_NORM_CX;
                  REAL_ABS_DIV; REAL_ABS_NUM] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `a * &x * b = &x * a * b`] THEN
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV)
       [GSYM CARD_NUMSEG_1] THEN
      MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
      FIRST_ASSUM(fun t -> SIMP_TAC[MATCH_MP DIRICHLET_CHARACTER_NORM t]) THEN
      COND_CASES_TAC THEN
      ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LE_DIV; REAL_ABS_POS;
                   NORM_POS_LE; REAL_LE_MUL; REAL_MUL_LID; REAL_ABS_NORM] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      SIMP_TAC[complex_div; real_div; COMPLEX_NORM_MUL; COMPLEX_NORM_INV] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN SIMP_TAC[NORM_POS_LE; REAL_LE_INV_EQ] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[COMPLEX_NORM_POW] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_POW_1] THEN
        MATCH_MP_TAC REAL_POW_MONO_INV THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE] THEN
        MATCH_MP_TAC(ARITH_RULE `m < r ==> 1 <= r - m`) THEN
        ASM_SIMP_TAC[DIVISION; LE_1];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_ARITH `&0 < abs(x - a) <=> ~(a = x)`] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[REAL_LT_REFL]; ALL_TAC] THEN
      MATCH_MP_TAC(NORM_ARITH
       `norm(w) = &1 /\ norm(z) < &1 /\ norm(zn) <= norm(z)
        ==> abs(&1 - norm(z)) <= norm(w - zn)`) THEN
      ASM_REWRITE_TAC[COMPLEX_NORM_NUM; COMPLEX_NORM_POW] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_POW_1] THEN
      MATCH_MP_TAC REAL_POW_MONO_INV THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC LIM_NULL_COMPLEX_LMUL THEN ASM_SIMP_TAC[LIM_N_TIMES_POWN];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(bounded
       { (f:complex->complex)(t) | real t /\ &0 <= Re t /\ norm(t) < &1 })`
  MP_TAC THENL
   [REWRITE_TAC[BOUNDED_POS] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    REWRITE_TAC[IMP_CONJ; FORALL_REAL] THEN
    REWRITE_TAC[COMPLEX_NORM_CX; RE_CX; IMP_IMP] THEN
    REWRITE_TAC[REAL_ARITH `&0 <= x /\ abs x < &1 <=> &0 <= x /\ x < &1`] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC o
      MATCH_MP PRIME_FACTOR) THEN
    X_CHOOSE_TAC `N:num` (SPEC `&2 * (B + &1)` REAL_ARCH_SIMPLE) THEN
    SUBGOAL_THEN `0 < N` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `t = &1 - inv(&(p EXP N)) / &2` THEN
    SUBGOAL_THEN `&0 <= t /\ t < &1` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "t" THEN
      MATCH_MP_TAC(REAL_ARITH
       `&0 < y /\ y <= &1 ==> &0 <= &1 - y / &2 /\ &1 - y / &2 < &1`) THEN
      ASM_SIMP_TAC[REAL_INV_LE_1; REAL_LT_INV_EQ; REAL_OF_NUM_LE;
                           REAL_OF_NUM_LT; LE_1; EXP_EQ_0; PRIME_IMP_NZ];
      ALL_TAC] THEN
    REMOVE_THEN "+" (MP_TAC o SPEC `Cx t`) THEN
    REWRITE_TAC[COMPLEX_NORM_CX; NOT_IMP] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN REWRITE_TAC[SERIES_FROM; LIM_SEQUENTIALLY] THEN
    DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:num` MP_TAC) THEN
    SUBGOAL_THEN `?n. M <= n /\ 1 <= n /\ p EXP N <= n` STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `p EXP N + M + 1` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `norm (f (Cx t):complex) <= B` THEN
    MATCH_MP_TAC(NORM_ARITH
     `B + &1 <= norm(x) ==> norm(y) <= B ==> ~(dist(x,y) < &1)`) THEN
    MATCH_MP_TAC(REAL_ARITH
     `a <= Re z /\ abs(Re z) <= norm z ==> a <= norm z`) THEN
    REWRITE_TAC[COMPLEX_NORM_GE_RE_IM] THEN
    SIMP_TAC[RE_VSUM; FINITE_NUMSEG; RE_MUL_CX; GSYM CX_POW] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (IMAGE (\k. p EXP k) (0..N))
                    (\x. Re (vsum {d | d divides x} (\d. c d)) * t pow x)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; IN_DIFF; SUBSET; IN_ELIM_THM;
                  FORALL_IN_IMAGE] THEN
      MP_TAC(SPECL [`d:num`; `c:num->complex`]
        DIRICHLET_CHARACTER_DIVISORSUM_POS) THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LE_MUL; LE_1; ETA_AX] THEN
      DISCH_THEN(K ALL_TAC) THEN
      REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
      ASM_SIMP_TAC[EXP_EQ_0; PRIME_IMP_NZ] THEN
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `p EXP N` THEN
      ASM_SIMP_TAC[LE_EXP; PRIME_IMP_NZ]] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) SUM_IMAGE o rand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[EQ_EXP] THEN ASM_MESON_TAC[PRIME_0; PRIME_1]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (0..N) (\k. &1 * &1 / &2)` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0; GSYM REAL_OF_NUM_ADD] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`d:num`; `c:num->complex`; `p:num`; `k:num`]
                DIRICHLET_CHARACTER_DIVISORSUM_EQ_1) THEN
      ASM_SIMP_TAC[ETA_AX; RE_CX; REAL_LE_REFL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`inv(&(p EXP N)) / &2`; `p EXP k`] lemma) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REWRITE_TAC[real_div; GSYM REAL_INV_MUL; REAL_OF_NUM_MUL] THEN
      REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
      MATCH_MP_TAC REAL_INV_LE_1 THEN
      REWRITE_TAC[REAL_OF_NUM_LE; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
      ASM_SIMP_TAC[EXP_EQ_0; MULT_EQ_0; ARITH; PRIME_IMP_NZ];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= a ==> a <= x ==> b <= x`) THEN
    MATCH_MP_TAC(REAL_ARITH `x * y <= &1 ==> &1 / &2 <= &1 - x * y / &2`) THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1;
                 EXP_EQ_0; PRIME_IMP_NZ] THEN
    ASM_REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_LE; LE_EXP] THEN
    ASM_MESON_TAC[PRIME_0];
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`]
    BOUNDED_LFUNCTION_PARTIAL_SUMS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP BOUNDED_PARTIAL_SUMS) THEN
  REWRITE_TAC[BOUNDED_POS] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN
  SIMP_TAC[IN_ELIM_THM; IN_UNIV; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[MESON[] `(!x a b. x = f a b ==> p a b) <=> (!a b. p a b)`] THEN
  X_GEN_TAC `B:real` THEN STRIP_TAC THEN EXISTS_TAC `&2 * B` THEN
  ASM_SIMP_TAC[REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
  X_GEN_TAC `z:complex` THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM NORM_NEG] THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC
   `\n. vsum(from 1 INTER (0..n)) (\k. c k * b (z:complex) k :complex)` THEN
  ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; GSYM sums] THEN
  REWRITE_TAC[FROM_INTER_NUMSEG] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
  MP_TAC(ISPECL [`c:num->complex`; `(b:complex->num->complex) z`;
                 `B:real`; `1`] SERIES_DIRICHLET_COMPLEX_VERY_EXPLICIT) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPEC `1`) THEN
    SUBGOAL_THEN `(b:complex->num->complex) z 1 = Cx(&1)` SUBST1_TAC THENL
     [EXPAND_TAC "b" THEN
      REWRITE_TAC[COMPLEX_POW_1; COMPLEX_INV_MUL; complex_div] THEN
      REWRITE_TAC[GSYM COMPLEX_SUB_RDISTRIB; COMPLEX_INV_1] THEN
      MATCH_MP_TAC COMPLEX_MUL_RINV THEN REWRITE_TAC[COMPLEX_SUB_0] THEN
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      UNDISCH_TAC `norm(Cx(&1)) < &1` THEN
      REWRITE_TAC[COMPLEX_NORM_CX; REAL_LT_REFL; REAL_ABS_NUM];
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_NORM_NUM; REAL_MUL_RID] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[LE_REFL]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `t:real` SUBST_ALL_TAC o
                GEN_REWRITE_RULE I [REAL_EXISTS]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RE_CX; COMPLEX_NORM_CX]) THEN
  SUBGOAL_THEN `!n. &0 < sum(0..n) (\m. t pow m)` ASSUME_TAC THENL
   [GEN_TAC THEN SIMP_TAC[LE_0; SUM_CLAUSES_LEFT; real_pow] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN
    ASM_SIMP_TAC[SUM_POS_LE_NUMSEG; REAL_POW_LE];
    ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN EXPAND_TAC "b" THEN
  REWRITE_TAC[GSYM CX_SUB; GSYM CX_POW; GSYM CX_DIV; GSYM CX_MUL;
              GSYM CX_INV; REAL_CX; RE_CX]
  THENL
   [ASM_SIMP_TAC[REAL_SUB_POW_L1; REAL_SUB_LE] THEN
    ASM_REWRITE_TAC[real_div; REAL_INV_MUL] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ; REAL_LT_MUL; REAL_OF_NUM_LT;
                 LE_1; REAL_ARITH `abs t < &1 ==> &0 < &1 - t`] THEN
    ASM_SIMP_TAC[real_div; REAL_FIELD
     `abs(t) < &1 ==> (x * inv(&1 - t) * y) * (&1 - t) = x * y`] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `x / y * &n = (&n * x) / y`] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..n-1) (\m. t pow n)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[SUM_CONST_NUMSEG; ARITH_RULE `1 <= n ==> n - 1 + 1 = n`;
                   SUB_0; REAL_LE_REFL];
      REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
      GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_MONO_INV THEN REPEAT CONJ_TAC THEN
      TRY ASM_REAL_ARITH_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_SUB_POW_L1; ARITH_RULE `1 <= n + 1`] THEN
  REWRITE_TAC[ADD_SUB; REAL_INV_MUL; real_div] THEN
  REWRITE_TAC[REAL_ARITH `x * t - y * t * z <= u * t - v * t * w <=>
                          t * (v * w - y * z) <= t * (u - x)`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_FIELD
   `&0 < y /\ &0 < z ==> x / y - w / z = (x * z - w * y) / (y * z)`] THEN
  SUBGOAL_THEN `t pow n * sum (0..n) (\m. t pow m) -
                t pow (n + 1) * sum (0..n - 1) (\m. t pow m) = t pow n`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL; GSYM REAL_POW_ADD] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `(n + 1) + x = n + x + 1`] THEN
    REWRITE_TAC[GSYM(SPEC `1` SUM_OFFSET); SUB_ADD; ADD_CLAUSES] THEN
    SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; GSYM SUM_LMUL; ADD_CLAUSES] THEN
    ASM_SIMP_TAC[SUB_ADD; REAL_POW_ADD] THEN
    REWRITE_TAC[REAL_ARITH `(x + y) - y:real = x`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_MUL; GSYM REAL_OF_NUM_ADD;
               REAL_OF_NUM_LE;
       REAL_FIELD `&1 <= n ==> inv(n) - inv(n + &1) = inv(n * (n + &1))`] THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
  REWRITE_TAC[ARITH] THEN CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN
           CONJ_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ]) THEN
    ASM_SIMP_TAC[REAL_POW_LE; SUM_POS_LE_NUMSEG] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `t:real`] AGM_SPECIAL) THEN
  MP_TAC(SPECL [`n - 1`; `t:real`] AGM_SPECIAL) THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; REAL_SUB_ADD] THEN
  REWRITE_TAC[IMP_IMP] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT;
               LE_1; REAL_ARITH `&0 < &n + &1`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE
   [TAUT `a /\ b /\ c /\ d ==> e <=> b /\ d ==> a /\ c ==> e`]
   REAL_LE_MUL2)) THEN
  ASM_SIMP_TAC[REAL_POW_LE; REAL_LE_MUL; REAL_ARITH `&0 <= &n + &1`] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y /\ a <= b ==> b <= x ==> a <= y`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_POW_2; real_div; REAL_INV_MUL; REAL_POW_MUL] THEN
    REWRITE_TAC[REAL_MUL_AC];
    REWRITE_TAC[GSYM REAL_POW_ADD; REAL_POW_POW] THEN
    MATCH_MP_TAC REAL_POW_MONO_INV THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ARITH_TAC]]);;
```

### Informal statement
For all natural numbers `d` and all functions `c` from natural numbers to complex numbers, if `c` is a Dirichlet character modulo `d` and `c` is not equal to the principal character `chi_0` modulo `d`, and for all natural numbers `n`, `c(n)` is a real number, then the L-function of `c` is not equal to the complex number 0.

### Informal sketch
The proof proceeds as follows:
- Assume `c` is a non-principal Dirichlet character whose values are real. Show that `Lfunction c` is not zero.
- Invoke `DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL` to show that `c` is non-trivial, i.e., for all `n`, `c(n)` is not always zero.
- Show that if `norm(z) < 1`, then the series `summable (from 1) (\n. c(n) * z pow n / (Cx(&1) - z pow n))`
- The goal is split into two cases depending on whether `z = Cx(&0)`.
  - When `z = Cx(&0)`, prove the summability by showing the series is equal to the zero series, `summable (\n. Cx(&0)) (from 1)`.
  - When `z` is not `Cx(&0)`, use the series comparison test `SERIES_COMPARISON_COMPLEX` with a geometric series `Cx(&2 * norm(z) pow n)`. Use `DIRICHLET_CHARACTER_NORM` to show the norm of `c(n)` is bounded by 1. Apply `SUMMABLE_GP` to conclude the geometric series is summable and hence the original series is summable. Obtain `N` such that for all `n`, if `N <= n` then `norm(z)^n <= 1/2`. Combine the above to invoke `SERIES_COMPARISON_COMPLEX`.
- Prove `(!z:complex. norm(z) < &1 ==> ((\n. c(n) * b z n) sums --(f z)) (from 1))` where `b = \z n. inv(Cx(&n) * (Cx(&1) - z)) - z pow n / (Cx(&1) - z pow n)`.
  - Use the theorem `SERIES_SUB` and `SERIES_COMPLEX_RMUL` and the definition of `LFUNCTION` to reduce the goal.
- Prove `(!z. norm(z) < &1 ==> ((\n. vsum {d | d divides n} (\d. c d) * z pow n) sums f(z)) (from 1))`. This involves showing the convergence of the Dirichlet series to the given function `f(z)`.
  - Use `VSUM_VSUM_DIVISORS` to rewrite the vsummation of divisors. Use `SERIES_COMPLEX_RMUL` to handle the complex multiplication of the Dirichlet character values.
  - Apply a limit transformation, using `LIM_TRANSFORM` to relate partial sums of the Dirichlet series to the function `f(z)`.
  - Show that a certain term tends to 0 as `x` tends to infinity. To do this, use the theorem `LIM_NULL_COMPARISON_COMPLEX`, after applying the triangle inequality `VSUM_NORM_TRIANGLE`.
- Show `~(bounded { (f:complex->complex)(t) | real t /\ &0 <= Re t /\ norm(t) < &1 })`.
  - Assume it is bounded and derive a contradiction. The fact that the partial sums of the Dirichlet series are bounded and apply `BOUNDED_LFUNCTION_PARTIAL_SUMS`. Select a prime factor `p:num`.
  - Show that there exists some `t` such that `&0 <= t /\ t < &1`.
  - The contradiction is reached by invoking the theorem `BOUNDED_PARTIAL_SUMS`. By contradiction, this achieves that the L-function is not zero.

### Mathematical insight
This theorem states that if a Dirichlet character takes only real values and is not the principal character, then its L-function is non-zero. The L-function captures key properties of the Dirichlet character and is crucial in analytic number theory. The fact that it is non-zero is a fundamental property with many applications.

### Dependencies
- `DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL`
- `SUMMABLE_FROM_ELSEWHERE`
- `SUMMABLE_EQ`
- `COMPLEX_VEC_0`
- `COMPLEX_POW_ZERO`
- `IN_FROM`
- `ARITH_RULE`
- `SERIES_COMPARISON_COMPLEX`
- `SUMMABLE_COMPLEX_LMUL`
- `COMPLEX_NORM_CX`
- `REAL_ABS_NORM`
- `SUMMABLE_GP`
- `COMPLEX_NORM_MUL`
- `DIRICHLET_CHARACTER_NORM`
- `REAL_MUL_LZERO`
- `REAL_MUL_LID`
- `REAL_ABS_POS`
- `REAL_LE_MUL`
- `REAL_ARCH_POW_INV`
- `MONO_EXISTS`
- `GE`
- `REAL_ABS_MUL`
- `REAL_ABS_NUM`
- `REAL_ABS_POW`
- `complex_div`
- `REAL_LE_LMUL`
- `REAL_LE_INV2`
- `NORM_ARITH`
- `REAL_LE_TRANS`
- `REAL_LT_IMP_LE`
- `REAL_POW_MONO_INV`
- `summable`
- `RIGHT_IMP_EXISTS_THM`
- `SKOLEM_THM`
- `LFUNCTION`
- `SERIES_SUB`
- `SERIES_COMPLEX_RMUL`
- `sums`
- `FROM_INTER_NUMSEG`
- `FINITE_DIVISORS`
- `LE_1`
- `VSUM_VSUM_DIVISORS`
- `IMP_CONJ`
- `LIM_TRANSFORM`
- `COMPLEX_POW_EQ_1`
- `DIVISION`
- `LIM_NULL_COMPARISON_COMPLEX`
- `ALWAYS_EVENTUALLY`
- `VSUM_NORM_TRIANGLE`
- `CARD_NUMSEG_1`
- `SUM_BOUND`
- `IN_NUMSEG`
- `COND_CASES_TAC`
- `REAL_MUL_RZERO`
- `REAL_LE_DIV`
- `REAL_LE_MUL2`
- `REAL_LE_INV_EQ`
- `REAL_POW_MONO_INV`
- `LIM_NULL_COMPLEX_LMUL`
- `LIM_N_TIMES_POWN`
- `BOUNDED_POS`
- `SIMPLE_IMAGE_GEN`
- `FORALL_IN_IMAGE`
- `IN_ELIM_THM`
- `FORALL_REAL`
- `REAL_ARCH_SIMPLE`
- `PRIME_FACTOR`
- `EXP_EQ_0`
- `PRIME_IMP_NZ`
- `SERIES_FROM`
- `LIM_SEQUENTIALLY`
- `REAL_LT_01`
- `REAL_LE_REFL`
- `DIRICHLET_CHARACTER_DIVISORSUM_POS`
- `EQ_EXP`
- `PRIME_0`
- `PRIME_1`
- `REAL_OF_NUM_SUB`
- `bounded_LFUNCTION_PARTIAL_SUMS`
- `BOUNDED_PARTIAL_SUMS`
- `IN_UNIV`
- `LEFT_IMP_EXISTS_THM`
- `REAL_LT_MUL`
- `LIM_NORM_UBOUND`
- `TRIVIAL_LIMIT_SEQUENTIALLY`
- `SERIES_DIRICHLET_COMPLEX_VERY_EXPLICIT`
- `DIRICHLET_CHARACTER_DIVISORSUM_EQ_1`
- `AGM_SPECIAL`

### Porting notes (optional)
- The proof relies heavily on real and complex analysis facts, especially about convergence and limit arguments. Porting to a system with weaker support for real/complex analysis might require more manual work.
- The use of tactics such as `ASM_SIMP_TAC`, `REWRITE_TAC`, and `MATCH_MP_TAC` suggests a mix of simplification and equational reasoning, which should be portable to other systems. Systems with sophisticated rewriting engines might automate these steps.
- The theorem `DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL` and `DIRICHLET_CHARACTER_DIVISORSUM_EQ_1` are important building blocks and will need to be ported or proven independently.



---

## BOUNDED_DIFF_LOGMUL

### Name of formal statement
BOUNDED_DIFF_LOGMUL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BOUNDED_DIFF_LOGMUL = prove
 (`!f a. bounded {f x - Cx(log(&x)) * a | x IN (:num)}
         ==> (!x. &0 <= Re(f x)) ==> &0 <= Re a`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[BOUNDED_POS; SIMPLE_IMAGE; FORALL_IN_IMAGE; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `exp((B + &1) / --(Re a))` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  SUBGOAL_THEN `abs(Re(f n - Cx(log(&n)) * a)) <= B` MP_TAC THENL
   [ASM_MESON_TAC[COMPLEX_NORM_GE_RE_IM; REAL_LE_TRANS]; ALL_TAC] THEN
  REWRITE_TAC[RE_SUB; RE_MUL_CX; REAL_NOT_LE] THEN
  MATCH_MP_TAC(REAL_ARITH
   `B < l * --a /\ &0 <= f ==> B < abs(f - l * a)`) THEN
  ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ; REAL_NEG_GT0] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `log(exp((B + &1) / --Re a))` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[LOG_EXP; REAL_NEG_GT0; REAL_LT_DIV2_EQ] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT]]);;
```

### Informal statement
For any function `f` from natural numbers to complex numbers, and any complex number `a`, if the set of values `{f x - Cx(log(&x)) * a | x IN (:num)}` is bounded, then if `Re(f x)` is non-negative for all `x`, it follows that `Re a` is non-negative.

### Informal sketch
The proof proceeds by contradiction. Assuming that `Re a` is negative, we want to show that the set `{f x - Cx(log(&x)) * a | x IN (:num)}` is unbounded.
- Assume `bounded {f x - Cx(log(&x)) * a | x IN (:num)}` and `!x. &0 <= Re(f x)` and `Re a < &0`.
- From boundedness, there exists a real number `B` such that `abs(Re(f n - Cx(log(&n)) * a)) <= B` for all natural numbers `n`.
- Choose `n` to be `exp((B + &1) / --(Re a))`.
- Then show that for the chosen `n`, `abs(Re(f n - Cx(log(&n)) * a))` is greater than `B`, giving a contradiction.
 Use `REAL_ARITH` to rewrite `B < l * --a /\ &0 <= f ==> B < abs(f - l * a)`.

### Mathematical insight
This theorem states that if the difference between a function `f` and a logarithmic function scaled by a complex number `a` is bounded, and the real part of `f` is always non-negative, then the real part of `a` must also be non-negative. This is useful in complex analysis and asymptotic analysis.

### Dependencies
- `BOUNDED_POS`
- `SIMPLE_IMAGE`
- `FORALL_IN_IMAGE`
- `IN_UNIV`
- `REAL_NOT_LT`
- `REAL_ARCH_SIMPLE`
- `COMPLEX_NORM_GE_RE_IM`
- `REAL_LE_TRANS`
- `RE_SUB`
- `RE_MUL_CX`
- `REAL_NOT_LE`
- `REAL_LT_LDIV_EQ`
- `REAL_NEG_GT0`
- `REAL_LTE_TRANS`
- `LOG_EXP`
- `REAL_LT_DIV2_EQ`
- `LOG_MONO_LE_IMP`
- `REAL_EXP_POS_LT`


---

## LFUNCTION_NONZERO_NONPRINCIPAL

### Name of formal statement
LFUNCTION_NONZERO_NONPRINCIPAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LFUNCTION_NONZERO_NONPRINCIPAL = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> ~(Lfunction c = Cx(&0))`,
  let lemma = prove
   (`{a,b,c} SUBSET s
     ==> FINITE s
         ==> !f. sum s f = sum (s DIFF {a,b,c}) f + sum {a,b,c} f`,
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SUM_UNION_EQ THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]) in
  GEN_TAC THEN ASM_CASES_TAC `d = 0` THENL
   [ASM_MESON_TAC[DIRICHLET_CHARACTER_0]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x c. vsum(1..x) (\n. c n * Cx(mangoldt n / &n)) -
           Cx(log(&x)) *
           (if c = chi_0 d then Cx(&1)
            else if Lfunction c = Cx(&0) then --Cx(&1)
            else Cx(&0))`;
    `(:num)`;
    `{c | dirichlet_character d c}`]
   BOUNDED_SUMS_IMAGES) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_DIRICHLET_CHARACTERS; IN_ELIM_THM] THEN
    X_GEN_TAC `c:num->complex` THEN
    ASM_CASES_TAC `c = chi_0 d` THEN
    ASM_SIMP_TAC[COMPLEX_MUL_RID; BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL;
                 LE_1] THEN
    ASM_CASES_TAC `Lfunction c = Cx(&0)` THEN
    ASM_REWRITE_TAC[COMPLEX_SUB_RZERO; COMPLEX_MUL_RNEG; COMPLEX_MUL_RZERO;
                    COMPLEX_MUL_RID; COMPLEX_SUB_RNEG] THEN
    ASM_MESON_TAC[BOUNDED_DIRICHLET_MANGOLDT_ZERO;
                  BOUNDED_DIRICHLET_MANGOLDT_NONZERO; LE_1];
    ALL_TAC] THEN
  SIMP_TAC[VSUM_SUB; FINITE_DIRICHLET_CHARACTERS; VSUM_COMPLEX_LMUL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP BOUNDED_DIFF_LOGMUL) THEN
  REWRITE_TAC[IN_UNIV] THEN ANTS_TAC THENL
   [X_GEN_TAC `x:num` THEN
    W(MP_TAC o PART_MATCH (lhs o rand) VSUM_SWAP o funpow 2 rand o snd) THEN
    REWRITE_TAC[FINITE_DIRICHLET_CHARACTERS; FINITE_NUMSEG] THEN
    DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC[VSUM_COMPLEX_RMUL; FINITE_DIRICHLET_CHARACTERS] THEN
    SIMP_TAC[RE_VSUM; FINITE_NUMSEG; RE_MUL_CX] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_POS;
             REAL_LE_DIV; REAL_POS; MANGOLDT_POS_LE];
    ALL_TAC] THEN
  SIMP_TAC[RE_VSUM; FINITE_DIRICHLET_CHARACTERS] THEN
  REPLICATE_TAC 2 (ONCE_REWRITE_TAC[COND_RAND]) THEN
  REWRITE_TAC[RE_NEG; RE_CX] THEN DISCH_TAC THEN
  X_GEN_TAC `c:num->complex` THEN STRIP_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_NOT_LT]) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `{chi_0 d,c,(\n. cnj(c n))} SUBSET {c | dirichlet_character d c}`
  MP_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[DIRICHLET_CHARACTER_CHI_0; DIRICHLET_CHARACTER_CNJ];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP lemma) THEN
  REWRITE_TAC[FINITE_DIRICHLET_CHARACTERS] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC(REAL_ARITH `s <= &0 /\ t < &0 ==> s + t < &0`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= --x ==> x <= &0`) THEN
    REWRITE_TAC[GSYM SUM_NEG] THEN MATCH_MP_TAC SUM_POS_LE THEN
    SIMP_TAC[FINITE_DIRICHLET_CHARACTERS; FINITE_DIFF] THEN
    SIMP_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CLAUSES; FINITE_INSERT; IN_INSERT; NOT_IN_EMPTY;
               FINITE_RULES] THEN
  SUBGOAL_THEN `~(chi_0 d = (\n. cnj (c n)))` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `(\c n:num. cnj(c n))`) THEN
    REWRITE_TAC[CNJ_CNJ; FUN_EQ_THM; CNJ_CHI_0] THEN
    ASM_REWRITE_TAC[GSYM FUN_EQ_THM; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(c = \n:num. cnj(c n))` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    REWRITE_TAC[GSYM REAL_CNJ; FUN_EQ_THM] THEN
    ASM_MESON_TAC[LFUNCTION_NONZERO_REAL];
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`] LFUNCTION_CNJ) THEN
  ASM_SIMP_TAC[CNJ_EQ_CX] THEN REAL_ARITH_TAC);;
```

### Informal statement
For all `d` and `c`, if `c` is a Dirichlet character modulo `d` and `c` is not the principal Dirichlet character modulo `d`, then the value of the L-function of `c` is not equal to 0.

### Informal sketch
The proof proceeds as follows:
- Assume that `d` is a natural number and `c` is a Dirichlet character modulo `d` that is not the principal character `chi_0 d`.
- We aim to prove that `Lfunction c` is not equal to `Cx(&0)`.
- The proof starts by considering the case `d = 0`. In this case, it uses `DIRICHLET_CHARACTER_0` to derive a contradiction.
- It uses a result `BOUNDED_SUMS_IMAGES` about bounded sums of images, with appropriate instantiation.
- The proof then proceeds by contradiction, assuming `Lfunction c = Cx(&0)`.
- The argument involves manipulating finite sums using facts from `FINITE_DIRICHLET_CHARACTERS`.
- The proof applies a change of variables and splits the sum into parts.
- It uses inequalities `MANGOLDT_POS_LE`, `REAL_LE_DIV`, and `REAL_POS` along with results about the sum of Dirichlet characters `DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_POS`.
- It considers the subset `{chi_0 d, c, (\n. cnj(c n))}` of `{c | dirichlet_character d c}`.
- It applies a lemma to rewrite the sum over a set `s` as the sum over `s DIFF {a,b,c}` plus the sum over `{a,b,c}`.
- Finally `LFUNCTION_CNJ` and `LFUNCTION_NONZERO_REAL` will be used to achieve the result.

### Mathematical insight
The theorem states that the L-function associated with any non-principal Dirichlet character does not vanish at 1, which is a crucial result in analytic number theory.

### Dependencies
- `DIRICHLET_CHARACTER_0`
- `BOUNDED_SUMS_IMAGES`
- `FINITE_DIRICHLET_CHARACTERS`
- `COMPLEX_MUL_RID`
- `BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL`
- `LE_1`
- `COMPLEX_SUB_RZERO`
- `COMPLEX_MUL_RNEG`
- `COMPLEX_MUL_RZERO`
- `COMPLEX_SUB_RNEG`
- `BOUNDED_DIRICHLET_MANGOLDT_ZERO`
- `BOUNDED_DIRICHLET_MANGOLDT_NONZERO`
- `VSUM_SUB`
- `VSUM_COMPLEX_LMUL`
- `BOUNDED_DIFF_LOGMUL`
- `IN_UNIV`
- `VSUM_SWAP`
- `FINITE_NUMSEG`
- `VSUM_COMPLEX_RMUL`
- `RE_VSUM`
- `RE_MUL_CX`
- `SUM_POS_LE_NUMSEG`
- `DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_POS`
- `REAL_LE_DIV`
- `REAL_POS`
- `MANGOLDT_POS_LE`
- `RE_NEG`
- `RE_CX`
- `DIRICHLET_CHARACTER_CHI_0`
- `DIRICHLET_CHARACTER_CNJ`
- `CNJ_CNJ`
- `FUN_EQ_THM`
- `CNJ_CHI_0`
- `LFUNCTION_NONZERO_REAL`
- `LFUNCTION_CNJ`
- `CNJ_EQ_CX`

### Porting notes (optional)
- The proof relies heavily on rewriting and arithmetic reasoning. A proof assistant with strong automation for these tasks (e.g., `ring` tactic in Coq, `simp` tactic in Isabelle) will be helpful.
- The use of `Cx` notation for complex numbers might need adjustment depending on how complex numbers are represented in the target system.


---

## BOUNDED_DIRICHLET_MANGOLDT_NONPRINCIPAL

### Name of formal statement
BOUNDED_DIRICHLET_MANGOLDT_NONPRINCIPAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BOUNDED_DIRICHLET_MANGOLDT_NONPRINCIPAL = prove
 (`!d c.
      dirichlet_character d c /\ ~(c = chi_0 d)
      ==> bounded { vsum(1..x) (\n. c n * Cx(mangoldt n / &n)) | x IN (:num)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BOUNDED_DIRICHLET_MANGOLDT_NONZERO THEN
  EXISTS_TAC `d:num` THEN
  ASM_MESON_TAC[LFUNCTION_NONZERO_NONPRINCIPAL]);;
```
### Informal statement
For all natural numbers `d` and complex-valued functions `c`, if `c` is a Dirichlet character modulo `d` and `c` is not the principal character `chi_0` modulo `d`, then the set of partial sums of `c(n) * mangoldt(n) / n` is bounded, where the partial sums are indexed by natural numbers `x`. More formally, the set `{ sum(n=1 to x, c(n) * mangoldt(n) / n) | x is a natural number }` is bounded.

### Informal sketch
The proof proceeds by:
- Stripping the quantifiers and the implication.
- Applying `MATCH_MP_TAC` with `BOUNDED_DIRICHLET_MANGOLDT_NONZERO`. This likely reduces the goal to showing that the Dirichlet character is nonzero, which is then handled by assumption.
- Applying `EXISTS_TAC` to introduce an existential variable `d`.
- Using `ASM_MESON_TAC` with `LFUNCTION_NONZERO_NONPRINCIPAL` to discharge the remaining goal, likely using the assumptions about the character being non-principal.

### Mathematical insight
This theorem establishes the boundedness of partial sums of the Mangoldt function weighted by a non-principal Dirichlet character. This result is a crucial step in the analytic study of the distribution of prime numbers, especially in the context of primes in arithmetic progressions. The boundedness ensures that the Dirichlet series associated with the Mangoldt function and a non-principal character converges conditionally, which is important for further analysis (e.g., zero-free regions, prime number theorem for arithmetic progressions).

### Dependencies
- `dirichlet_character`
- `chi_0`
- `vsum`
- `mangoldt`
- `Cx`
- `BOUNDED_DIRICHLET_MANGOLDT_NONZERO`
- `LFUNCTION_NONZERO_NONPRINCIPAL`


---

## BOUNDED_SUM_OVER_DIRICHLET_CHARACTERS

### Name of formal statement
BOUNDED_SUM_OVER_DIRICHLET_CHARACTERS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BOUNDED_SUM_OVER_DIRICHLET_CHARACTERS = prove
 (`!d l. 1 <= d /\ coprime(l,d)
         ==> bounded { vsum {c | dirichlet_character d c}
                            (\c. c(l) *
                                 vsum(1..x) (\n. c n * Cx (mangoldt n / &n))) -
                       Cx(log(&x)) | x IN (:num)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x. Cx(log(&x)) =
                        vsum {c | dirichlet_character d c}
                             (\c. if c = chi_0 d then Cx(log(&x)) else Cx(&0))`
   (fun th -> ONCE_REWRITE_TAC[th])
  THENL
   [SIMP_TAC[VSUM_DELTA; GSYM COMPLEX_VEC_0] THEN
    REWRITE_TAC[IN_ELIM_THM; DIRICHLET_CHARACTER_CHI_0];
    ALL_TAC] THEN
  SIMP_TAC[GSYM VSUM_SUB; FINITE_DIRICHLET_CHARACTERS] THEN
  MATCH_MP_TAC BOUNDED_SUMS_IMAGES THEN
  REWRITE_TAC[FINITE_DIRICHLET_CHARACTERS; IN_ELIM_THM] THEN
  X_GEN_TAC `c:num->complex` THEN DISCH_TAC THEN
  ASM_CASES_TAC `c = chi_0 d` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL) THEN
    ASM_REWRITE_TAC[chi_0; COMPLEX_MUL_LID];
    REWRITE_TAC[COMPLEX_SUB_RZERO] THEN
    MP_TAC(SPECL [`d:num`; `c:num->complex`]
      BOUNDED_DIRICHLET_MANGOLDT_NONPRINCIPAL) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[BOUNDED_POS] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[COMPLEX_NORM_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
    FIRST_ASSUM(fun th -> SIMP_TAC[MATCH_MP DIRICHLET_CHARACTER_NORM th]) THEN
    REAL_ARITH_TAC]);;
```

### Informal statement
For all natural numbers `d` and `l`, if `1 <= d` and `l` and `d` are coprime, then the set of values obtained by the following expression is bounded:

```
{ sum_{c} (c(l) * sum_{n=1}^{x} (c(n) * (mangoldt n) / n)) - log x | x is a natural number }
```

where the outer sum is over all Dirichlet characters `c` modulo `d`. `c(n)` denotes the evaluation of `c` at `n`.

### Informal sketch
The proof proceeds by showing that the sum of character sums involving the von Mangoldt function, minus the logarithm, is bounded.

*   The main goal is to prove that the expression involving Dirichlet characters is bounded over all natural numbers `x`.

*   We replace `Cx(log(&x))` for a more complex but equivalent expression where we sum over all dirichlet characters `c` modulo `d` in the expression `vsum {c | dirichlet_character d c} (\c. if c = chi_0 d then Cx(log(&x)) else Cx(&0))`. The cases in which `c` is equal to the principal dirichlet character `chi_0 d` and when is not are handled.

*   We then use `VSUM_DELTA` and `COMPLEX_VEC_0` to simplify the term coming from `chi_0 d`.

*   Apply `BOUNDED_SUMS_IMAGES` and relevant rewriting rules.

*   Perform case analysis on whether `c` is the principal character `chi_0 d`.

*   If it is the principal character, use `BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL` and simplify.

*   If it is not the principal character, employ `BOUNDED_DIRICHLET_MANGOLDT_NONPRINCIPAL`

*   Use properties of `COMPLEX_NORM_MUL` and `REAL_LE_MUL2` along with dirichlet character norms to complete the proof.

### Mathematical insight

This theorem establishes a bound on a sum involving Dirichlet characters and the von Mangoldt function. This is a crucial step towards understanding the distribution of prime numbers in arithmetic progressions. Bounding such sums, which mix analytic number theory and algebraic objects, is a common motif for proving results about primes.

### Dependencies
* `coprime`
* `dirichlet_character`
* `mangoldt`
* `chi_0`
* `COMPLEX_VEC_0`
* `VSUM_DELTA`
* `IN_ELIM_THM`
* `DIRICHLET_CHARACTER_CHI_0`
* `GSYM VSUM_SUB`
* `FINITE_DIRICHLET_CHARACTERS`
* `BOUNDED_SUMS_IMAGES`
* `BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL`
* `BOUNDED_DIRICHLET_MANGOLDT_NONPRINCIPAL`
* `COMPLEX_MUL_LID`
* `COMPLEX_SUB_RZERO`
* `BOUNDED_POS`
* `MONO_EXISTS`
* `SIMPLE_IMAGE_GEN`
* `FORALL_IN_IMAGE`
* `IN_UNIV`
* `COMPLEX_NORM_MUL`
* `REAL_MUL_LID`
* `REAL_LE_MUL2`
* `NORM_POS_LE`
* `DIRICHLET_CHARACTER_NORM`


---

## DIRICHLET_MANGOLDT

### Name of formal statement
DIRICHLET_MANGOLDT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_MANGOLDT = prove
 (`!d k. 1 <= d /\ coprime(k,d)
         ==> bounded { Cx(&(phi d)) * vsum {n | n IN 1..x /\ (n == k) (mod d)}
                                           (\n. Cx(mangoldt n / &n)) -
                       Cx(log(&x)) | x IN (:num)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?l. (k * l == 1) (mod d)` CHOOSE_TAC THENL
   [ASM_MESON_TAC[CONG_SOLVE]; ALL_TAC] THEN
  MP_TAC(SPECL [`d:num`; `l:num`] BOUNDED_SUM_OVER_DIRICHLET_CHARACTERS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(k * l == 1) (mod d)` THEN
    CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> f x = g x) ==> {f x | x IN s} = {g x | x IN s}`) THEN
  X_GEN_TAC `x:num` THEN DISCH_THEN(K ALL_TAC) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG; FINITE_RESTRICT] THEN
  SIMP_TAC[VSUM_RESTRICT_SET; FINITE_NUMSEG] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) VSUM_SWAP o lhand o snd) THEN
  REWRITE_TAC[FINITE_DIRICHLET_CHARACTERS; FINITE_NUMSEG] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN
  MP_TAC(GSYM(SPEC `d:num` DIRICHLET_CHARACTER_MUL)) THEN
  SIMP_TAC[IN_ELIM_THM] THEN DISCH_THEN(K ALL_TAC) THEN
  SIMP_TAC[VSUM_COMPLEX_RMUL; FINITE_DIRICHLET_CHARACTERS] THEN
  ASM_SIMP_TAC[DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS] THEN
  SUBGOAL_THEN `(l * n == 1) (mod d) <=> (n == k) (mod d)` SUBST1_TAC THENL
   [UNDISCH_TAC `(k * l == 1) (mod d)` THEN CONV_TAC NUMBER_RULE;
    COND_CASES_TAC THEN ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_VEC_0]]);;
```
### Informal statement
For all natural numbers `d` and `k`, if `1 <= d` and `k` and `d` are coprime, then the set consisting of `Cx(&(phi d)) * vsum {n | n IN 1..x /\ (n == k) (mod d)} (\n. Cx(mangoldt n / &n)) - Cx(log(&x))` for `x IN (:num)` is bounded.

### Informal sketch
The proof demonstrates that the given expression involving a sum over integers congruent to `k` modulo `d` is bounded. The proof proceeds by:

- Using the theorem `BOUNDED_SUM_OVER_DIRICHLET_CHARACTERS`, which relates the sum to a sum over Dirichlet characters. This requires showing the existence of an `l` such that `k * l == 1 (mod d)`.
- Rewriting the sum over integers congruent to `k` modulo `d` in terms of sums involving Dirichlet characters.
 - Applying `VSUM_COMPLEX_LMUL` (left multiplication of complex numbers), `FINITE_NUMSEG`, `FINITE_RESTRICT`, `VSUM_RESTRICT_SET`, `FINITE_NUMSEG`.
- Swapping the order of summation using `VSUM_SWAP`. This is made possible by `FINITE_DIRICHLET_CHARACTERS` and `FINITE_NUMSEG`.
- Exploiting the orthogonality relations of Dirichlet characters (`DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS`). Specifically, the theorem `DIRICHLET_CHARACTER_MUL` is used for simplification.
- Showing that `(l * n == 1) (mod d)` is equivalent to `(n == k) (mod d)`, and rewriting using `COMPLEX_MUL_LZERO` in case of zero Dirichlet character value.

### Mathematical insight
The theorem relates the sum of the Mangoldt function over an arithmetic progression to the logarithm function, with an error term that is bounded. This is a key result in analytic number theory related to the distribution of prime numbers in arithmetic progressions. The result depends critically on properties of Dirichlet characters, especially their orthogonality relations.

### Dependencies
- `BOUNDED_SUM_OVER_DIRICHLET_CHARACTERS`
- `CONG_SOLVE`
- `VSUM_COMPLEX_LMUL`
- `FINITE_NUMSEG`
- `FINITE_RESTRICT`
- `VSUM_RESTRICT_SET`
- `VSUM_SWAP`
- `FINITE_DIRICHLET_CHARACTERS`
- `VSUM_EQ_NUMSEG`
- `COMPLEX_MUL_ASSOC`
- `DIRICHLET_CHARACTER_MUL`
- `IN_ELIM_THM`
- `VSUM_COMPLEX_RMUL`
- `DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS`
- `COMPLEX_MUL_LZERO`

### Porting notes (optional)
The main challenge is the availability and proof details of `BOUNDED_SUM_OVER_DIRICHLET_CHARACTERS` and the theory of Dirichlet characters. One also needs to have a tactic for modular arithmetic reasoning (`NUMBER_RULE`).
Ensure that the definition of `mangoldt n` (Mangoldt function) is consistent. Handling of complex numbers (`Cx`) and vector sums (`vsum`) might differ across proof assistants, so special attention is needed during the porting process.
Ensure the definition of `coprime(k,d)` is available, as well as theorems required to show existence of a modular inverse `l` when `k` and `d` are coprime. Handling of finite sets may also differ across systems.


---

## DIRICHLET_MANGOLDT_EXPLICIT

### Name of formal statement
DIRICHLET_MANGOLDT_EXPLICIT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_MANGOLDT_EXPLICIT = prove
 (`!d k. 1 <= d /\ coprime (k,d)
         ==> ?B. &0 < B /\
                 !x. abs(sum {n | n IN 1..x /\ (n == k) (mod d)}
                             (\n. mangoldt n / &n) -
                         log(&x) / &(phi d)) <= B`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIRICHLET_MANGOLDT) THEN
  REWRITE_TAC[BOUNDED_POS] THEN
  SIMP_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; IN_UNIV] THEN
  SIMP_TAC[VSUM_CX; FINITE_RESTRICT; FINITE_NUMSEG;
           GSYM CX_SUB; GSYM CX_MUL; COMPLEX_NORM_CX] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B / &(phi d)` THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; LE_1; PHI_LOWERBOUND_1_STRONG;
               REAL_LE_RDIV_EQ] THEN
  X_GEN_TAC `n:num` THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_ABS_NUM] THEN
  REWRITE_TAC[GSYM REAL_ABS_MUL] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[REAL_SUB_LDISTRIB; REAL_DIV_LMUL;
               LE_1; PHI_LOWERBOUND_1_STRONG; REAL_OF_NUM_EQ]);;
```

### Informal statement
For all positive integers `d` and `k` such that `1 <= d` and `k` and `d` are coprime, there exists a real number `B > 0` such that for all real numbers `x`, the absolute value of the difference between the sum of `mangoldt n / n` for `n` in the range from 1 to `x` such that `n` is congruent to `k` modulo `d`, and `log(x) / phi(d)` is less than or equal to `B`.

### Informal sketch
The proof demonstrates the explicit estimate in Dirichlet's theorem.
- Start with the assumption that `1 <= d` and `coprime(k,d)`.
- Apply the theorem `DIRICHLET_MANGOLDT` which asserts the existence of an appropriate bound `B` for the sums involving the `mangoldt` function.
- Rewrite using `BOUNDED_POS` to ensure positivity.
- Simplify using lemmas concerning images, `VSUM_CX`, finiteness, complex norms, and the relationship between complex subtraction and multiplication.
- Choose a bound `B` appropriately.
- Simplify the resulting expression using arithmetic properties of real numbers, including bounds on the Euler totient function `phi(d)`.

### Mathematical insight
This theorem provides an explicit error bound in Dirichlet's theorem on arithmetic progressions. It states that the sum of the von Mangoldt function over primes congruent to `k` modulo `d` is approximately `log(x) / phi(d)`, where `phi(d)` is Euler's totient function. The theorem provides a quantitative version of Dirichlet's theorem, specifying how quickly the sum converges to its expected value.

### Dependencies
- `DIRICHLET_MANGOLDT`
- `BOUNDED_POS`
- `SIMPLE_IMAGE`
- `FORALL_IN_IMAGE`
- `IN_UNIV`
- `VSUM_CX`
- `FINITE_RESTRICT`
- `FINITE_NUMSEG`
- `GSYM CX_SUB`
- `GSYM CX_MUL`
- `COMPLEX_NORM_CX`
- `REAL_LT_DIV`
- `REAL_OF_NUM_LT`
- `LE_1`
- `PHI_LOWERBOUND_1_STRONG`
- `REAL_LE_RDIV_EQ`
- `GSYM REAL_ABS_NUM`
- `GSYM REAL_ABS_MUL`
- `REAL_MUL_SYM`
- `REAL_SUB_LDISTRIB`
- `REAL_DIV_LMUL`
- `REAL_OF_NUM_EQ`


---

## DIRICHLET_STRONG

### Name of formal statement
DIRICHLET_STRONG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET_STRONG = prove
 (`!d k. 1 <= d /\ coprime(k,d)
         ==> ?B. &0 < B /\
                 !x. abs(sum {p | p IN 1..x /\ prime p /\ (p == k) (mod d)}
                             (\p. log(&p) / &p) -
                         log(&x) / &(phi d)) <= B`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC o
    MATCH_MP DIRICHLET_MANGOLDT_EXPLICIT) THEN
  EXISTS_TAC `B + &3` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs(x - y) <= a ==> abs(x - z) <= b ==> abs(y - z) <= b + a`) THEN
  MP_TAC(SPECL [`x:num`; `{n | n IN 1..x /\ (n == k) (mod d)}`]
               MERTENS_MANGOLDT_VERSUS_LOG) THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM] THEN REWRITE_TAC[CONJ_ACI]);;
```

### Informal statement
For all positive integers `d` and `k` such that `d` is greater than or equal to 1 and `k` is coprime to `d`, there exists a real number `B` greater than 0 such that for all natural numbers `x`, the absolute value of the difference between the sum over all primes `p` less than or equal to `x` such that `p` is congruent to `k` modulo `d` of `log(p) / p`, and `log(x) / phi(d)` is less than or equal to `B`. Here, `phi(d)` is Euler's totient function..

### Informal sketch
The proof demonstrates the existence of a bound, `B`, on the difference between two sums related to prime numbers in arithmetic progressions.

- Start by assuming `1 <= d` and `coprime(k, d)`.
- Apply `DIRICHLET_MANGOLDT_EXPLICIT` to obtain a bound `B` initially. This theorem presumably gives an explicit estimate for a similar quantity.
- Instantiate the existential quantifier by `B + &3` (likely to ensure positivity and accommodate later manipulations of the bound).
- Show that `B + &3 > 0` using arithmetic reasoning.
- Introduce an arbitrary natural number `x`.
- Apply `MERTENS_MANGOLDT_VERSUS_LOG` to estimate a different sum, namely the sum over all `n` less than or equal to `x` such that `n` is congruent to `k` modulo `d` of `mangoldt(n)/n`.
- Use the triangle inequality `abs(x - y) <= a ==> abs(x - z) <= b ==> abs(y - z) <= b + a` to combine the bound from `DIRICHLET_MANGOLDT_EXPLICIT` and `MERTENS_MANGOLDT_VERSUS_LOG`.
- Simplify the resulting expression using set theory lemmas (`SUBSET`, `IN_ELIM_THM`) and properties of conjunction (`CONJ_ACI`).

### Mathematical insight
This theorem formulates a strong, effective version of Dirichlet's theorem on primes in arithmetic progressions. It provides a quantitative estimate regarding how the sum of `log(p)/p` for primes `p <= x` in a given arithmetic progression compares to the expected value `log(x) / phi(d)`. The theorem suggests that this difference is bounded, offering a quantitative and effective estimate compared to many variants of Dirichlet's theorem.

### Dependencies
Number Theory:
- `coprime`
- `phi`
- `prime`

Real Analysis:
- `log`
- `abs` sum

Theorems:
- `DIRICHLET_MANGOLDT_EXPLICIT`
- `MERTENS_MANGOLDT_VERSUS_LOG`

Set Theory:
- `SUBSET`
- `IN_ELIM_THM`

Axioms/Theorems needed for reals:
- REAL_ARITH (triangle inequality)

### Porting notes (optional)
- The theorem relies on `DIRICHLET_MANGOLDT_EXPLICIT` and `MERTENS_MANGOLDT_VERSUS_LOG`, which are likely to be complex results. Porting this theorem effectively requires porting those dependencies, so examine these carefully first.
- `phi` should be easily translated but ensure it correctly computes Euler's totient function.
- The HOL Light uses some automation (`ASM_REAL_ARITH_TAC`), thus the porting may require manually constructing a proof, especially in systems with weaker real arithmetic automation.
- The tactics involving rewriting using `CONJ_ACI` will likely need to be adjusted based on how other systems handle associativity and commutativity of conjunction.


---

## DIRICHLET

### Name of formal statement
DIRICHLET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIRICHLET = prove
 (`!d k. 1 <= d /\ coprime(k,d)
         ==> INFINITE {p | prime p /\ (p == k) (mod d)}`,
  REWRITE_TAC[INFINITE] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `\n:num. n` o MATCH_MP UPPER_BOUND_FINITE_SET) THEN
  REWRITE_TAC[IN_ELIM_THM; NOT_EXISTS_THM] THEN X_GEN_TAC `n:num` THEN
  DISCH_TAC THEN MP_TAC(SPECL [`d:num`; `k:num`] DIRICHLET_STRONG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC
   `max (exp(&(phi d) *
            (&1 + B + sum {p | p IN 1..n /\ prime p /\ (p == k) (mod d)}
                          (\p. log(&p) / &p))))
        (max (&n) (&1))`
   REAL_ARCH_SIMPLE) THEN
  REWRITE_TAC[NOT_EXISTS_THM; REAL_MAX_LE; REAL_OF_NUM_LE] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `abs(x - y) <= b ==> y < &1 + b + x`)) THEN
  ASM_SIMP_TAC[REAL_NOT_LT; REAL_LE_RDIV_EQ; PHI_LOWERBOUND_1_STRONG;
               REAL_OF_NUM_LT; LE_1] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
  ASM_SIMP_TAC[EXP_LOG; REAL_OF_NUM_LT; LE_1] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `x <= a ==> x = y ==> y <= a`)) THEN
  REPLICATE_TAC 4 AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
  GEN_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[] THEN ASM_ARITH_TAC);;
```

### Informal statement
For all natural numbers `d` and `k`, if `d` is greater than or equal to 1 and `k` and `d` are coprime, then the set of prime numbers `p` such that `p` is congruent to `k` modulo `d` is infinite.

### Informal sketch
The proof demonstrates that for every `d`, `k` such that `1 <= d` and `coprime(k, d)`, the set `{p | prime p /\ (p == k) (mod d)}` is infinite. The proof proceeds as follows:
- It starts by using the theorem `INFINITE` to reduce the goal to showing that the set is not finite.
- An assumption is made that the set is finite.
- The theorem `DIRICHLET_STRONG` is applied. This theorem introduces a constant `B` and shows that if the sum of `log(p)/p` converges, then the set of primes p such that `p == k mod d` is finite.
- The proof then manipulates inequalities to arrive at a contradiction using theorems like `REAL_ARCH_SIMPLE`, `REAL_MAX_LE`, `REAL_OF_NUM_LE`.
- Several real arithmetic steps are used, along with facts about the Euler's totient function (`PHI_LOWERBOUND_1_STRONG`).
- The proof uses the fact that the exponential function is monotonically increasing (`REAL_EXP_MONO_LE`).
- A contradiction is reached, showing the initial assumption that the set is finite must be false.

### Mathematical insight
Dirichlet's theorem on arithmetic progressions is a fundamental result in number theory. It states that for any two positive coprime integers `k` and `d`, there are infinitely many primes of the form `k + nd`, where `n` is a non-negative integer. In other words, there are infinitely many primes that are congruent to `k` modulo `d`. The formal statement expresses this core idea within HOL Light. This theorem is significant because it guarantees the existence of infinitely many primes in any arithmetic progression where the first term and common difference are coprime.

### Dependencies
- Definitions: `INFINITE`, `coprime`, `prime`
- Theorems: `INFINITE`, `UPPER_BOUND_FINITE_SET`, `IN_ELIM_THM`, `NOT_EXISTS_THM`, `DIRICHLET_STRONG`, `REAL_ARCH_SIMPLE`, `REAL_MAX_LE`, `REAL_OF_NUM_LE`, `REAL_NOT_LT`, `REAL_LE_RDIV_EQ`, `PHI_LOWERBOUND_1_STRONG`, `REAL_OF_NUM_LT`, `LE_1`, `REAL_MUL_SYM`, `REAL_EXP_MONO_LE`, `EXP_LOG`, `EXTENSION`, `IN_NUMSEG`


---

