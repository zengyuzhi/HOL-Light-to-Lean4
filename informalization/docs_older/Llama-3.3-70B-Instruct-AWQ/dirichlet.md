# dirichlet.ml

## Overview

Number of statements: 73

The `dirichlet.ml` file formalizes Dirichlet's theorem, a fundamental result in number theory. It builds upon various supporting theories and constructions imported from other modules, including products, arithmetic-geometric means, and properties of multiplicative functions. The file's content is likely focused on defining key concepts and proving the theorem, which is a cornerstone of analytic number theory. Its role in the larger library is to provide a formal foundation for Dirichlet's theorem, enabling its application in other areas of number theory and analysis.

## VSUM_VSUM_DIVISORS

### Name of formal statement
VSUM_VSUM_DIVISORS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let VSUM_VSUM_DIVISORS = prove
 (`!f x. vsum (1..x) (\n. vsum {d | d divides n} (f n)) =
         vsum (1..x) (\n. vsum (1..(x DIV n)) (\k. f (k * n) n))`,
  SIMP_TAC[VSUM; FINITE_DIVISORS; LE_1] THEN
  SIMP_TAC[VSUM; FINITE_NUMSEG; ITERATE_ITERATE_DIVISORS;
           MONOIDAL_VECTOR_ADD])
```

### Informal statement
For all functions `f` and all positive integers `x`, the sum from 1 to `x` of the sum over all divisors `d` of `n` of `f(n)` is equal to the sum from 1 to `x` of the sum from 1 to `x` divided by `n` of `f(k * n) * n`.

### Informal sketch
* The proof involves rearranging a double sum using properties of summation and divisibility.
* The `SIMP_TAC` tactic is used with various theorems (`VSUM`, `FINITE_DIVISORS`, `LE_1`, `FINITE_NUMSEG`, `ITERATE_ITERATE_DIVISORS`, `MONOIDAL_VECTOR_ADD`) to simplify the expression and establish the equality.
* The key idea is to transform the sum over divisors into a sum over multiplication factors, utilizing the fact that every divisor `d` of `n` corresponds to a factor `k` such that `k * d = n`.

### Mathematical insight
This theorem appears to be related to Dirichlet's theorem, which is a fundamental result in number theory. The statement provides a way to rearrange a double sum involving divisors and a function `f`, which can be useful in various applications, such as analytic number theory or algebraic number theory. The theorem relies on properties of summation, divisibility, and the structure of the integers.

### Dependencies
* Theorems:
	+ `VSUM`
	+ `FINITE_DIVISORS`
	+ `LE_1`
	+ `FINITE_NUMSEG`
	+ `ITERATE_ITERATE_DIVISORS`
	+ `MONOIDAL_VECTOR_ADD`
* Definitions:
	+ `vsum`
	+ `divides`

### Porting notes
When translating this theorem to another proof assistant, pay attention to the handling of binders and the `vsum` function, as different systems may have different notations or conventions for these concepts. Additionally, the `SIMP_TAC` tactic and the specific theorems used may need to be adapted or replaced with equivalent constructs in the target system.

---

## REAL_EXP_1_LE_4

### Name of formal statement
REAL_EXP_1_LE_4

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let REAL_EXP_1_LE_4 = prove
 (`exp(&1) <= &4`,
  ONCE_REWRITE_TAC[ARITH_RULE `&1 = &1 / &2 + &1 / &2`; REAL_EXP_ADD] THEN
  REWRITE_TAC[REAL_ARITH `&4 = &2 * &2`; REAL_EXP_ADD] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
  MP_TAC(SPEC `&1 / &2` REAL_EXP_BOUND_LEMMA) THEN REAL_ARITH_TAC)
```

### Informal statement
For all real numbers, `exp(1)` is less than or equal to `4`, where this is proven using properties of exponentiation and arithmetic.

### Informal sketch
* Start with the expression `exp(1)` and apply the property `REAL_EXP_ADD` to split `1` into `1/2 + 1/2`.
* Use `REAL_ARITH` to recognize `4` as `2 * 2` and apply `REAL_EXP_ADD` again.
* Apply `REAL_LE_MUL2` to establish a relationship between the exponential terms and their product.
* Use `REAL_EXP_POS_LE` to assert the positivity and comparison of exponential terms.
* Apply `REAL_EXP_BOUND_LEMMA` specifically to `1/2` to derive a bound.
* Conclude using `REAL_ARITH_TAC` to finalize the arithmetic and comparison.

### Mathematical insight
This theorem provides a specific bound on the value of `exp(1)`, demonstrating how properties of exponentiation and basic arithmetic can be used to derive meaningful inequalities. The use of `REAL_EXP_ADD` and `REAL_LE_MUL2` showcases how the theorem leverages fundamental properties of real numbers and exponentiation to establish a comparison.

### Dependencies
#### Theorems
* `REAL_EXP_ADD`
* `REAL_LE_MUL2`
* `REAL_EXP_POS_LE`
* `REAL_EXP_BOUND_LEMMA`
#### Definitions
* `REAL_ARITH`
* `exp`

### Porting notes
When translating this theorem into another proof assistant, pay special attention to how the system handles arithmetic and exponential functions, as well as how it supports the manipulation of inequalities. The use of `MATCH_MP_TAC` and `MP_TAC` suggests that the proof relies on modus ponens and matching, which should be directly translatable. However, the specific tactics like `ONCE_REWRITE_TAC` and `REAL_ARITH_TAC` might require equivalent but differently named tactics in the target system.

---

## DECREASING_LOG_OVER_N

### Name of formal statement
DECREASING_LOG_OVER_N

### Type of the formal statement
Theorem

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
    MP_TAC REAL_EXP_1_LE_4 THEN ASM_REAL_ARITH_TAC])
```

### Informal statement
For all natural numbers `n` greater than or equal to 4, the inequality `log(n + 1) / (n + 1) ≤ log(n) / n` holds.

### Informal sketch
* The proof starts by applying the `COMPLEX_MVT_LINE` theorem to establish a relationship between `log(n + 1)` and `log(n)`.
* It then proceeds to analyze the real part of a complex number `w` and applies various simplifications and case analyses.
* The proof uses `MATCH_MP_TAC` to apply the `REAL_LE_MUL` theorem and derives several inequalities involving `log(n + 1)`, `log(n)`, and `n`.
* Key steps involve applying the `LOG_MONO_LE_IMP` theorem and using properties of exponential functions, such as `REAL_EXP_POS_LT` and `REAL_EXP_1_LE_4`.
* The `GEN_REWRITE_TAC` and `GSYM` tactics are used to manipulate expressions and apply various theorems.

### Mathematical insight
This theorem provides an inequality involving logarithmic functions, which can be useful in various mathematical contexts, such as analysis and number theory. The proof relies on properties of complex analysis, particularly the mean value theorem, and demonstrates how to apply these principles to derive inequalities involving logarithms.

### Dependencies
* Theorems:
	+ `COMPLEX_MVT_LINE`
	+ `REAL_LE_MUL`
	+ `LOG_MONO_LE_IMP`
	+ `REAL_EXP_POS_LT`
	+ `REAL_EXP_1_LE_4`
* Definitions:
	+ `clog`
	+ `Cx`
	+ `Re`
	+ `log`
* Other dependencies:
	+ `REAL_OF_NUM_LE`
	+ `IN_SEGMENT_CX_GEN`
	+ `REAL_ARITH`

---

## EXISTS_COMPLEX_ROOT_NONTRIVIAL

### Name of formal statement
EXISTS_COMPLEX_ROOT_NONTRIVIAL

### Type of the formal statement
Theorem

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
    ASM_SIMP_TAC[CEXP_CLOG]])
```

### Informal statement
For all complex numbers `a` and integers `n` such that `2 <= n`, there exists a complex number `z` such that `z` raised to the power of `n` equals `a` and `z` is not equal to 1.

### Informal sketch
* The proof starts by assuming `2 <= n`, which implies `n` is not 0.
* It then considers two cases for `a`: when `a` is 0 and when `a` is not 0.
* If `a` is 0, it constructs `z` as 0, since any number raised to a power and equal to 0 implies the base is 0.
* If `a` is 1, it further considers whether `n` is greater than 1 (since `n` cannot be less than 2 by the initial assumption).
* For `a = 1` and `n > 1`, it uses the fact that there exists a complex `n`th root of unity (excluding 1) to find a suitable `z`.
* For `a` not equal to 0 or 1, it uses the existence of a complex logarithm to construct `z` as `cexp(clog a / n)`, leveraging properties of complex exponentiation and logarithms to show this `z` satisfies `z^n = a`.
* The proof utilizes various properties and theorems related to complex numbers, such as `COMPLEX_POW_ZERO`, `COMPLEX_ROOT_UNITY_EQ_1`, and `CEXP_CLOG`, to justify the constructions and manipulations.

### Mathematical insight
This theorem is important because it establishes the existence of complex `n`th roots for any complex number `a` when `n` is greater than or equal to 2, with the exception of `a` being 1, for which it provides a specific construction of a root that is not 1. This is a fundamental property in complex analysis, underpinning many results and applications in mathematics and other fields.

### Dependencies
#### Theorems
* `COMPLEX_POW_ZERO`
* `COMPLEX_ROOT_UNITY_EQ_1`
* `DIVIDES_ONE`
* `COMPLEX_ROOT_UNITY`
* `COMPLEX_POW_ONE`
* `CEXP_CLOG`
#### Definitions
* `cexp`
* `clog`
* `Cx`
* `ii` (imaginary unit)
* `pow` (complex power operation)

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles complex numbers, their properties, and the specific constructions used (e.g., complex roots of unity, logarithms). Differences in automation, tactic systems, or built-in support for complex analysis may require adjustments to the proof strategy or additional lemmas.

---

## dirichlet_character

### Name of formal statement
dirichlet_character

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let dirichlet_character = new_definition
 `dirichlet_character d (c:num->complex) <=>
        (!n. c(n + d) = c(n)) /\
        (!n. c(n) = Cx(&0) <=> ~coprime(n,d)) /\
        (!m n. c(m * n) = c(m) * c(n))`;;
```

### Informal statement
The `dirichlet_character` is a property of a function `c` from natural numbers to complex numbers, with respect to a natural number `d`, such that:
- For all natural numbers `n`, `c(n + d)` equals `c(n)`.
- For all natural numbers `n`, `c(n)` equals zero if and only if `n` and `d` are not coprime.
- For all natural numbers `m` and `n`, `c(m * n)` equals the product of `c(m)` and `c(n)`.

### Informal sketch
* The definition involves three main conditions that `c` must satisfy to be considered a Dirichlet character modulo `d`.
* The first condition, `c(n + d) = c(n)`, implies that `c` is periodic with period `d`.
* The second condition, `c(n) = Cx(&0) <=> ~coprime(n,d)`, relates the value of `c(n)` to whether `n` and `d` are coprime, indicating `c(n)` is zero precisely when `n` and `d` share a common factor.
* The third condition, `c(m * n) = c(m) * c(n)`, specifies that `c` acts multiplicatively with respect to multiplication of its input.

### Mathematical insight
The `dirichlet_character` definition encapsulates the fundamental properties of a Dirichlet character in number theory, which are crucial for studying the distribution of prime numbers and other arithmetic properties. This definition is important because it provides a way to encode information about the factorization of numbers into a multiplicative function, facilitating deeper analysis in number theory.

### Dependencies
- `Cx`
- `coprime`

### Porting notes
When translating this definition into other proof assistants, special attention should be given to the handling of the `Cx` function, which represents complex numbers, and the `coprime` predicate, which checks for coprimality. Additionally, the periodicity and multiplicative properties of the Dirichlet character should be carefully preserved. In systems like Lean or Coq, defining a new type or structure for Dirichlet characters and then proving these properties as lemmas may be an effective approach.

---

## DIRICHLET_CHARACTER_PERIODIC

### Name of formal statement
DIRICHLET_CHARACTER_PERIODIC

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_PERIODIC = prove
 (`!d c n. dirichlet_character d c ==> c(n + d) = c(n)`,
  SIMP_TAC[dirichlet_character]);;
```

### Informal statement
For all integers `d`, `c`, and `n`, if `c` is a Dirichlet character modulo `d`, then `c(n + d)` is equal to `c(n)`.

### Informal sketch
* The proof involves assuming `c` is a `dirichlet_character` modulo `d`, which implies certain properties about `c`.
* The main logical stage is to apply these properties to show that `c(n + d)` equals `c(n)` for any integer `n`.
* The `SIMP_TAC` tactic suggests that the proof may involve simplifying the expression `c(n + d)` using the definition or properties of `dirichlet_character`.

### Mathematical insight
This statement captures a fundamental periodicity property of Dirichlet characters, which are crucial in number theory, especially in the context of Dirichlet series and L-functions. The periodicity of Dirichlet characters with period `d` is essential for their application in various number-theoretic problems.

### Dependencies
* `dirichlet_character`

### Porting notes
When translating this theorem into another proof assistant, ensure that the definition of `dirichlet_character` and its properties are correctly ported. Pay attention to how the target system handles modular arithmetic and periodic functions, as these are key to the theorem's statement and proof.

---

## DIRICHLET_CHARACTER_EQ_0

### Name of formal statement
DIRICHLET_CHARACTER_EQ_0

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_EQ_0 = prove
 (`!d c n. dirichlet_character d c ==> (c(n) = Cx(&0) <=> ~coprime(n,d))`,
  SIMP_TAC[dirichlet_character]);;
```

### Informal statement
For all integers `d`, `c`, and `n`, if `c` is a Dirichlet character modulo `d`, then `c(n)` equals 0 if and only if `n` and `d` are not coprime.

### Informal sketch
* The proof involves assuming `dirichlet_character d c` and then proving the equivalence `c(n) = 0` if and only if `~coprime(n,d)`.
* The `SIMP_TAC` tactic suggests simplification using the definition of `dirichlet_character`.
* Key steps likely involve using properties of Dirichlet characters and coprimality to establish both directions of the equivalence.

### Mathematical insight
This theorem provides insight into the behavior of Dirichlet characters, specifically when they evaluate to 0. It shows that for a Dirichlet character `c` modulo `d`, `c(n)` equals 0 precisely when `n` and `d` share a common factor greater than 1, highlighting a fundamental connection between Dirichlet characters and the arithmetic properties of their inputs.

### Dependencies
* `dirichlet_character`
* `coprime`

### Porting notes
When translating this into another proof assistant, special attention should be given to how Dirichlet characters and coprimality are defined and handled. The `SIMP_TAC` tactic indicates that simplification using the definition of `dirichlet_character` is crucial, so ensuring that similar simplification mechanisms are available and correctly applied in the target system is important. Additionally, the handling of modular arithmetic and the properties of Dirichlet characters may require careful consideration to ensure that the proof translates correctly.

---

## DIRICHLET_CHARACTER_MUL

### Name of formal statement
DIRICHLET_CHARACTER_MUL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_MUL = prove
 (`!d c m n. dirichlet_character d c ==> c(m * n) = c(m) * c(n)`,
  SIMP_TAC[dirichlet_character]);;
```

### Informal statement
For all integers `d`, `c`, `m`, and `n`, if `c` is a Dirichlet character modulo `d`, then the value of `c` at the product of `m` and `n` is equal to the product of the values of `c` at `m` and `n`.

### Informal sketch
* The proof starts with the assumption that `c` is a Dirichlet character modulo `d`, which implies certain properties about `c`.
* The goal is to show that `c(m * n)` equals `c(m) * c(n)`.
* The `SIMP_TAC` tactic is used with the `dirichlet_character` theorem, suggesting that the proof involves simplifying the expression using the definition or properties of Dirichlet characters.
* The key step likely involves applying the multiplicative property of Dirichlet characters, which states that `c(m * n)` equals `c(m) * c(n)` for any integers `m` and `n`.

### Mathematical insight
This statement is important because it establishes a fundamental property of Dirichlet characters, which are crucial in number theory, particularly in the study of Dirichlet series and their applications to problems in analytic number theory. The multiplicative property is essential for many applications, including the study of L-functions and the proof of the prime number theorem for arithmetic progressions.

### Dependencies
* `dirichlet_character`

### Porting notes
When porting this theorem to another proof assistant, ensure that the definition of `dirichlet_character` and its associated properties are correctly translated. The `SIMP_TAC` tactic with `dirichlet_character` suggests that the proof relies on the simplification of expressions using the properties of Dirichlet characters, which might be achieved through different means in other proof assistants, such as using rewrite rules or simplification tactics specific to the target system.

---

## DIRICHLET_CHARACTER_EQ_1

### Name of formal statement
DIRICHLET_CHARACTER_EQ_1

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_EQ_1 = prove
 (`!d c. dirichlet_character d c ==> c(1) = Cx(&1)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIRICHLET_CHARACTER_MUL) THEN
  DISCH_THEN(MP_TAC o repeat (SPEC `1`)) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[COMPLEX_FIELD `a = a * a <=> a = Cx(&0) \/ a = Cx(&1)`] THEN
  ASM_SIMP_TAC[DIRICHLET_CHARACTER_EQ_0] THEN
  MESON_TAC[COPRIME_1; COPRIME_SYM])
```

### Informal statement
For all `d` and `c`, if `c` is a Dirichlet character modulo `d`, then `c(1)` is equal to `1`.

### Informal sketch
* The proof starts by assuming `c` is a Dirichlet character modulo `d`.
* It then applies the `DIRICHLET_CHARACTER_MUL` property to `c(1)`, which states that `c` is multiplicative.
* The proof then simplifies the expression using `NUM_REDUCE_CONV` and applies the `COMPLEX_FIELD` property to reason about complex numbers.
* The `ASM_SIMP_TAC` tactic is used with `DIRICHLET_CHARACTER_EQ_0` to simplify the expression further.
* Finally, the `MESON_TAC` tactic is used with `COPRIME_1` and `COPRIME_SYM` to derive the conclusion.

### Mathematical insight
This theorem provides a fundamental property of Dirichlet characters, which are important in number theory. The property states that a Dirichlet character evaluated at `1` is always `1`, which is a crucial fact in many applications of Dirichlet characters.

### Dependencies
* Theorems:
	+ `DIRICHLET_CHARACTER_MUL`
	+ `DIRICHLET_CHARACTER_EQ_0`
	+ `COPRIME_1`
	+ `COPRIME_SYM`
* Definitions:
	+ `dirichlet_character`
	+ `Cx`

### Porting notes
When porting this theorem to another proof assistant, pay attention to the handling of complex numbers and the `COMPLEX_FIELD` property. Additionally, the `MESON_TAC` tactic may need to be replaced with a similar tactic or a manual proof step, depending on the target system's automation capabilities.

---

## DIRICHLET_CHARACTER_POW

### Name of formal statement
DIRICHLET_CHARACTER_POW

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_POW = prove
 (`!d c m n. dirichlet_character d c ==> c(m EXP n) = c(m) pow n`,
  REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[EXP; complex_pow] THENL
   [ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_1]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_MUL th]) THEN
  ASM_REWRITE_TAC[])
```

### Informal statement
For all `d`, `c`, `m`, and `n`, if `c` is a Dirichlet character modulo `d`, then `c(m` raised to the power of `n`) is equal to `c(m)` raised to the power of `n`.

### Informal sketch
* The proof starts by assuming `c` is a Dirichlet character modulo `d`, and then applies induction on `n`.
* In the base case, it uses the property of `dirichlet_character` to establish the result for `n = 0`.
* For the inductive step, it uses the `DIRICHLET_CHARACTER_MUL` property to reduce `c(m` raised to the power of `n`) to `c(m)` raised to the power of `n`, leveraging the `EXP` and `complex_pow` definitions.
* The proof also employs `ASM_MESON_TAC` to apply the `DIRICHLET_CHARACTER_EQ_1` theorem, ensuring that the character's properties are correctly applied.

### Mathematical insight
This theorem provides a crucial property of Dirichlet characters, showing that they behave multiplicatively with respect to exponentiation. This is essential in number theory, particularly in the study of Dirichlet series and their applications to problems like the distribution of prime numbers.

### Dependencies
* Theorems:
	+ `DIRICHLET_CHARACTER_EQ_1`
	+ `DIRICHLET_CHARACTER_MUL`
* Definitions:
	+ `dirichlet_character`
	+ `EXP`
	+ `complex_pow`

### Porting notes
When translating this theorem to other proof assistants, pay attention to the handling of binders and the representation of `dirichlet_character` properties. In particular, ensure that the `DIRICHLET_CHARACTER_EQ_1` and `DIRICHLET_CHARACTER_MUL` theorems are properly ported, as they are crucial for the proof. Additionally, consider the differences in induction and rewriting mechanisms between HOL Light and the target proof assistant.

---

## DIRICHLET_CHARACTER_PERIODIC_GEN

### Name of formal statement
DIRICHLET_CHARACTER_PERIODIC_GEN

### Type of the formal statement
Theorem

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
  ASM_SIMP_TAC[DIRICHLET_CHARACTER_PERIODIC])
```

### Informal statement
For all integers `d`, `c`, `m`, and `n`, if `c` is a Dirichlet character modulo `d`, then `c(m * d + n)` equals `c(n)`.

### Informal sketch
* The proof starts by assuming `c` is a Dirichlet character modulo `d`, which implies certain properties about `c`.
* It then applies `INDUCT_TAC` to proceed by induction, breaking down the problem into simpler cases.
* The `REWRITE_TAC` with `ADD_CLAUSES` and `MULT_CLAUSES` is used to simplify arithmetic expressions.
* A key step involves applying `GEN_REWRITE_TAC` with `GSYM th` to transform the expression using a previously derived fact `th`.
* The proof also utilizes `ONCE_REWRITE_TAC` with an arithmetic rule to rearrange terms, ultimately simplifying to a form where `ASM_SIMP_TAC` with `DIRICHLET_CHARACTER_PERIODIC` can be applied to conclude the proof.
* The use of `FIRST_X_ASSUM` and `GEN_TAC` helps in managing assumptions and generalizing the proof.

### Mathematical insight
This theorem captures a periodicity property of Dirichlet characters, which are crucial in number theory for studying properties of prime numbers and modular forms. The periodic nature of Dirichlet characters modulo `d` is fundamental in many applications, including the study of Dirichlet series and L-functions. This property essentially states that the value of a Dirichlet character `c` at `m * d + n` is the same as its value at `n`, reflecting the character's periodicity with period `d`.

### Dependencies
* `dirichlet_character`
* `DIRICHLET_CHARACTER_PERIODIC`
* Arithmetic rules and properties, including `ADD_CLAUSES`, `MULT_CLAUSES`, and `(mk + d) + n:num = (mk + n) + d`

### Porting notes
When translating this theorem into another proof assistant, pay special attention to how Dirichlet characters and their properties are defined and handled. The periodicity property might be a part of the character definition or a separate theorem, depending on the system. Additionally, the arithmetic manipulations and the use of induction might require adjustments based on the target system's strengths in automated reasoning and its support for mathematical structures like Dirichlet characters.

---

## DIRICHLET_CHARACTER_CONG

### Name of formal statement
DIRICHLET_CHARACTER_CONG

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_CONG = prove
 (`!d c m n.
        dirichlet_character d c /\ (m == n) (mod d) ==> c(m) = c(n)`,
  REWRITE_TAC[CONG_CASES] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[DIRICHLET_CHARACTER_PERIODIC_GEN]);;
```

### Informal statement
For all integers `d`, `c`, `m`, and `n`, if `c` is a Dirichlet character modulo `d` and `m` is congruent to `n` modulo `d`, then the value of `c` at `m` is equal to the value of `c` at `n`.

### Informal sketch
* The proof starts by assuming `c` is a `dirichlet_character` modulo `d` and `m` is congruent to `n` modulo `d`.
* It then applies `REWRITE_TAC` with `CONG_CASES` to rewrite the congruence relation.
* The `REPEAT STRIP_TAC` tactic is used to strip away the universal quantifiers and implications.
* Finally, `ASM_SIMP_TAC` is applied with `DIRICHLET_CHARACTER_PERIODIC_GEN` to simplify the expression using the periodicity property of Dirichlet characters.
* The key idea is to use the definition of a Dirichlet character and its periodicity to establish the equality of `c(m)` and `c(n)`.

### Mathematical insight
This theorem is important because it shows that Dirichlet characters are well-defined on residue classes modulo `d`, rather than just on individual integers. This property is crucial for many applications of Dirichlet characters in number theory.

### Dependencies
* `dirichlet_character`
* `CONG_CASES`
* `DIRICHLET_CHARACTER_PERIODIC_GEN`

### Porting notes
When translating this theorem to another proof assistant, pay attention to the handling of modular arithmetic and the definition of Dirichlet characters. The `REWRITE_TAC` and `ASM_SIMP_TAC` tactics may need to be replaced with equivalent tactics in the target system. Additionally, the `DIRICHLET_CHARACTER_PERIODIC_GEN` theorem may need to be ported as well, as it is used in the proof.

---

## DIRICHLET_CHARACTER_ROOT

### Name of formal statement
DIRICHLET_CHARACTER_ROOT

### Type of the formal statement
Theorem

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
  MATCH_MP_TAC FERMAT_LITTLE THEN ASM_MESON_TAC[COPRIME_SYM])
```

### Informal statement
For all natural numbers `d`, all Dirichlet characters `c` modulo `d`, and all natural numbers `n` that are coprime to `d`, it holds that `c(n)` raised to the power of Euler's totient function `phi(d)` equals 1.

### Informal sketch
* Start by assuming `d`, `c`, and `n` such that `c` is a Dirichlet character modulo `d` and `n` is coprime to `d`.
* Apply the property that `c` is a Dirichlet character to find a relation involving `c(n)`.
* Utilize the fact that `c(n)` can be related to `c` evaluated at 1 (due to `DIRICHLET_CHARACTER_EQ_1`) to simplify expressions involving `c(n)`.
* Employ `DIRICHLET_CHARACTER_POW` and `DIRICHLET_CHARACTER_CONG` to manipulate expressions involving powers of `c(n)`.
* Apply Fermat's Little Theorem (`FERMAT_LITTLE`) to numbers coprime to `d` to derive a congruence relation.
* Conclude that `c(n)` raised to the power of `phi(d)` equals 1 by combining the results of the previous steps.

### Mathematical insight
This theorem provides insight into the properties of Dirichlet characters, specifically how they behave when raised to certain powers related to the Euler's totient function. It connects Dirichlet characters with fundamental number theoretic concepts like coprimality and Euler's totient function, showcasing their deep roots in number theory.

### Dependencies
* Theorems:
  - `DIRICHLET_CHARACTER_EQ_1`
  - `DIRICHLET_CHARACTER_POW`
  - `DIRICHLET_CHARACTER_CONG`
  - `FERMAT_LITTLE`
* Definitions:
  - `dirichlet_character`
  - `coprime`
  - `phi` (Euler's totient function)
  - `Cx` (constant function returning 1)

### Porting notes
When translating this theorem into another proof assistant, pay special attention to how Dirichlet characters and the Euler's totient function are defined and used. The automation and tactic structure might differ, so understanding the mathematical content and the strategic flow of the proof is crucial. Additionally, the handling of coprimality and the application of Fermat's Little Theorem may require adjustments depending on the target system's libraries and automation capabilities.

---

## DIRICHLET_CHARACTER_NORM

### Name of formal statement
DIRICHLET_CHARACTER_NORM

### Type of the formal statement
Theorem

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
  ASM_MESON_TAC[PHI_LOWERBOUND_1_STRONG; LE_1])
```

### Informal statement
For all integers `d`, `c`, and `n`, if `c` is a Dirichlet character modulo `d`, then the norm of `c(n)` is equal to 1 if `d` and `n` are coprime, and 0 otherwise.

### Informal sketch
* The proof starts by considering the case when `d` and `n` are coprime and when they are not.
* If `d` equals 0, the proof uses `DIRICHLET_CHARACTER_EQ_1`, `COMPLEX_NORM_CX`, `REAL_ABS_NUM`, `COPRIME_0`, and `COPRIME_SYM` to establish the norm of `c(n)` is 1.
* For non-zero `d`, the proof applies `DIRICHLET_CHARACTER_ROOT` to `c(n)` and then uses properties of complex numbers, such as `COMPLEX_NORM_POW` and `COMPLEX_NORM_CX`, to simplify the expression.
* The proof then uses `REAL_POW_EQ_1_IMP` with `phi d` to derive the condition under which the norm of `c(n)` equals 1, leveraging `PHI_LOWERBOUND_1_STRONG` and `LE_1` for the final conclusion.

### Mathematical insight
This theorem provides a fundamental property of Dirichlet characters, which are crucial in number theory, especially in the context of Dirichlet's theorem on primes in arithmetic progressions. The norm condition given by this theorem helps in understanding the behavior of these characters, particularly how they interact with coprime numbers.

### Dependencies
* Theorems:
  + `DIRICHLET_CHARACTER_EQ_0`
  + `DIRICHLET_CHARACTER_EQ_1`
  + `DIRICHLET_CHARACTER_ROOT`
  + `REAL_POW_EQ_1_IMP`
  + `PHI_LOWERBOUND_1_STRONG`
* Definitions:
  + `dirichlet_character`
  + `norm`
  + `coprime`
  + `COMPLEX_NORM_ZERO`
  + `COMPLEX_NORM_POW`
  + `COMPLEX_NORM_CX`
  + `REAL_ABS_NUM`
  + `REAL_ABS_NORM`

---

## chi_0

### Name of formal statement
chi_0

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let chi_0 = new_definition
 `chi_0 d n = if coprime(n,d) then Cx(&1) else Cx(&0)`
```

### Informal statement
The function `chi_0` is defined as follows: for all integers `d` and `n`, `chi_0 d n` is equal to `Cx(&1)` if `n` and `d` are coprime, and `Cx(&0)` otherwise.

### Informal sketch
* The definition of `chi_0` relies on the `coprime` predicate to determine whether two numbers are relatively prime.
* The function `Cx` is used to construct a value based on the result of the coprimality test.
* The definition can be understood as a simple conditional statement, where the `if` condition checks for coprimality and the `then` and `else` branches specify the resulting values.

### Mathematical insight
The `chi_0` function appears to be related to the principal character mod `d`, which is a concept from number theory. This function is likely used to define a character, which is a fundamental object in number theory and algebra. The use of `Cx` suggests a connection to a specific mathematical structure, possibly a group or ring.

### Dependencies
* `coprime`
* `Cx`

### Porting notes
When translating this definition to another proof assistant, care should be taken to ensure that the `coprime` predicate and the `Cx` function are properly defined and imported. Additionally, the conditional statement may need to be rewritten to conform to the target system's syntax and semantics.

---

## DIRICHLET_CHARACTER_CHI_0

### Name of formal statement
DIRICHLET_CHARACTER_CHI_0

### Type of the formal statement
Theorem

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
The theorem `DIRICHLET_CHARACTER_CHI_0` states that for any `d`, the `dirichlet_character` of `d` evaluated at `chi_0 d` holds, where `chi_0` is a specific character. This involves properties of coprime numbers and complex ring operations.

### Informal sketch
* The proof starts with the `dirichlet_character` of `d` at `chi_0 d`, which is the core statement to be proven.
* It then applies `REWRITE_TAC` with `dirichlet_character` and `chi_0` definitions to transform the statement.
* Further simplification is done using `REWRITE_TAC` with number rules regarding coprime numbers, specifically the rules `coprime(n + d, d) <=> coprime(n, d)` and `coprime(m * n, d) <=> coprime(m, d) /\ coprime(n, d)`.
* The proof concludes with `CONV_TAC COMPLEX_RING`, which involves converting the expression to adhere to complex ring properties.

### Mathematical insight
This theorem is crucial for establishing properties of Dirichlet characters, particularly the principal character `chi_0`. It relies on understanding the relationship between Dirichlet characters, coprime numbers, and properties of the complex ring, showcasing how number theoretic concepts are intertwined with algebraic structures.

### Dependencies
#### Theorems and Definitions
* `dirichlet_character`
* `chi_0`
* `coprime`
* `NUMBER_RULE` for `coprime(n + d, d) <=> coprime(n, d)`
* `NUMBER_RULE` for `coprime(m * n, d) <=> coprime(m, d) /\ coprime(n, d)`
* `COMPLEX_RING`

### Porting notes
When translating this theorem into another proof assistant, special attention should be given to how coprime numbers and complex ring operations are handled. The `REWRITE_TAC` and `CONV_TAC` tactics might have direct counterparts, but the specific `NUMBER_RULE`s and the `COMPLEX_RING` conversion may require custom handling depending on the target system's library and automation capabilities.

---

## DIRICHLET_CHARACTER_EQ_PRINCIPAL

### Name of formal statement
DIRICHLET_CHARACTER_EQ_PRINCIPAL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_EQ_PRINCIPAL = prove
 (`!d c. dirichlet_character d c
         ==> (c = chi_0 d <=> !n. coprime(n,d) ==> c(n) = Cx(&1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; chi_0] THEN
  ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_0])
```

### Informal statement
For all `d` and `c`, if `c` is a Dirichlet character modulo `d`, then `c` is equal to the principal character `chi_0` modulo `d` if and only if for all `n` that are coprime to `d`, `c(n)` is equal to `1`.

### Informal sketch
* The proof starts by assuming `c` is a Dirichlet character modulo `d`.
* It then aims to show the equivalence `c = chi_0 d` if and only if for all `n` coprime to `d`, `c(n) = 1`.
* The forward direction involves using the properties of `chi_0` and the definition of a Dirichlet character.
* The reverse direction involves using the assumption that `c(n) = 1` for all `n` coprime to `d` to show `c` must be the principal character `chi_0`.
* Key steps involve using `REWRITE_TAC` with `FUN_EQ_THM` and `chi_0`, and applying `ASM_MESON_TAC` with `DIRICHLET_CHARACTER_EQ_0` to manage the equivalences and implications.

### Mathematical insight
This theorem provides a crucial characterization of the principal Dirichlet character `chi_0` modulo `d`, which plays a central role in number theory, especially in the context of Dirichlet series and L-functions. The principal character is defined such that `chi_0(n) = 1` if `n` is coprime to `d`, and `0` otherwise. This theorem helps in identifying and working with the principal character in terms of its functional equation, facilitating proofs and computations involving Dirichlet characters.

### Dependencies
* `dirichlet_character`
* `chi_0`
* `coprime`
* `Cx`
* `FUN_EQ_THM`
* `DIRICHLET_CHARACTER_EQ_0`

### Porting notes
When porting this theorem to another proof assistant, special attention should be given to how Dirichlet characters and the principal character are defined, as well as how coprimality is handled. The use of `REWRITE_TAC` and `ASM_MESON_TAC` suggests that the proof involves strategic rewriting and application of previously proven theorems, which may need to be adapted based on the target system's tactics and automation capabilities. Additionally, ensuring that the `FUN_EQ_THM` and character definitions align with the target system's function equality and character theories will be crucial.

---

## DIRICHLET_CHARACTER_NONPRINCIPAL

### Name of formal statement
DIRICHLET_CHARACTER_NONPRINCIPAL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_NONPRINCIPAL = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> ?n. coprime(n,d) /\ ~(c n = Cx(&0)) /\ ~(c n = Cx(&1))`,
  MESON_TAC[DIRICHLET_CHARACTER_EQ_PRINCIPAL; DIRICHLET_CHARACTER_EQ_0])
```

### Informal statement
For all `d` and `c`, if `c` is a Dirichlet character modulo `d` and `c` is not the principal character `chi_0` modulo `d`, then there exists a positive integer `n` such that `n` is coprime to `d`, `c(n)` is not equal to `0`, and `c(n)` is not equal to `1`.

### Informal sketch
* The proof starts with the assumption that `c` is a Dirichlet character modulo `d` and `c` is not the principal character `chi_0` modulo `d`.
* It uses the `MESON_TAC` tactic, which applies a set of meson rules to prove the goal.
* The rules used are `DIRICHLET_CHARACTER_EQ_PRINCIPAL` and `DIRICHLET_CHARACTER_EQ_0`, which likely provide properties of Dirichlet characters and their relationship to the principal character and the zero character.
* The proof strategy involves finding a suitable `n` that satisfies the conditions of being coprime to `d` and having `c(n)` not equal to `0` or `1`, leveraging the properties of Dirichlet characters and the given assumptions.

### Mathematical insight
This theorem provides insight into the properties of non-principal Dirichlet characters, specifically that they must take on values other than `0` and `1` for some input `n` that is coprime to the modulus `d`. This is important in number theory, particularly in the study of Dirichlet characters and their applications to problems like the distribution of prime numbers.

### Dependencies
* Theorems:
  + `DIRICHLET_CHARACTER_EQ_PRINCIPAL`
  + `DIRICHLET_CHARACTER_EQ_0`
* Definitions:
  + `dirichlet_character`
  + `chi_0`
  + `coprime`
  + `Cx`

### Porting notes
When translating this theorem into another proof assistant, special attention should be paid to the handling of the `MESON_TAC` tactic and the specific rules `DIRICHLET_CHARACTER_EQ_PRINCIPAL` and `DIRICHLET_CHARACTER_EQ_0`. These may need to be reimplemented or replaced with equivalent tactics and rules in the target system. Additionally, the representation of Dirichlet characters and the properties used in the proof may vary between systems, requiring careful mapping of concepts and theorems.

---

## DIRICHLET_CHARACTER_0

### Name of formal statement
DIRICHLET_CHARACTER_0

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_0 = prove
 (`!c. dirichlet_character 0 c <=> c = chi_0 0`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[DIRICHLET_CHARACTER_CHI_0] THEN
  DISCH_TAC THEN REWRITE_TAC[chi_0; FUN_EQ_THM; COPRIME_0] THEN
  X_GEN_TAC `n:num` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_1; DIRICHLET_CHARACTER_EQ_0;
                COPRIME_0])
```

### Informal statement
For all `c`, the `dirichlet_character` of `0` is equivalent to `c` being equal to `chi_0 0`. This statement asserts the existence of a unique Dirichlet character associated with `0`, which is `chi_0 0`.

### Informal sketch
* The proof starts by assuming an arbitrary `c` and aims to show the equivalence between `dirichlet_character 0 c` and `c = chi_0 0`.
* It proceeds by using `GEN_TAC` to generalize the statement, followed by `EQ_TAC` to set up an equivalence proof.
* The `SIMP_TAC` tactic is applied with `DIRICHLET_CHARACTER_CHI_0` to simplify the expression involving `dirichlet_character` and `chi_0`.
* The proof then uses `DISCH_TAC` to discharge assumptions, `REWRITE_TAC` to rewrite expressions involving `chi_0`, `FUN_EQ_THM`, and `COPRIME_0`.
* The `X_GEN_TAC` tactic is used to introduce a new variable `n` of type `num`, and `COND_CASES_TAC` is applied to consider cases.
* Finally, `ASM_REWRITE_TAC` and `ASM_MESON_TAC` are used with relevant theorems (`DIRICHLET_CHARACTER_EQ_1`, `DIRICHLET_CHARACTER_EQ_0`, `COPRIME_0`) to derive the conclusion.

### Mathematical insight
This theorem provides a fundamental property of Dirichlet characters, specifically identifying the character associated with `0`. It is crucial in number theory, particularly in the context of Dirichlet series and L-functions, as it establishes a base case for more general results.

### Dependencies
* Theorems:
  - `DIRICHLET_CHARACTER_CHI_0`
  - `DIRICHLET_CHARACTER_EQ_1`
  - `DIRICHLET_CHARACTER_EQ_0`
  - `COPRIME_0`
* Definitions:
  - `dirichlet_character`
  - `chi_0`
  - `FUN_EQ_THM`

### Porting notes
When translating this theorem into other proof assistants, pay close attention to the handling of binders, especially in the context of `GEN_TAC` and `X_GEN_TAC`. Additionally, the `SIMP_TAC` and `REWRITE_TAC` tactics might need to be adapted based on the target system's simplification and rewriting mechanisms. The `ASM_MESON_TAC` tactic, which is used for automatic proof, may require manual intervention or replacement with equivalent tactics in the target system to ensure the proof goes through.

---

## DIRICHLET_CHARACTER_1

### Name of formal statement
DIRICHLET_CHARACTER_1

### Type of the formal statement
Theorem

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
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING])
```

### Informal statement
For all `c`, `c` is a Dirichlet character of modulus 1 if and only if for all `n`, `c(n)` equals 1.

### Informal sketch
* The proof starts by assuming `c` is a Dirichlet character of modulus 1 and then derives that `c(n)` equals 1 for all `n`.
* It uses the definition of `dirichlet_character` and the property `COPRIME_1` to establish this equivalence.
* The converse direction is proven by assuming `c(n)` equals 1 for all `n` and showing that `c` satisfies the definition of a Dirichlet character of modulus 1.
* Key steps involve rewriting using `ARITH` and `COMPLEX_RING` properties, and applying `INDUCT_TAC` for induction.

### Mathematical insight
This theorem characterizes Dirichlet characters of modulus 1, which are crucial in number theory, particularly in the context of Dirichlet's theorem on primes in arithmetic progressions. The theorem provides a simple condition for a function to be a Dirichlet character of modulus 1, which is essential for further theoretical developments.

### Dependencies
* `dirichlet_character`
* `COPRIME_1`
* `ARITH`
* `COMPLEX_RING`
* `ADD1`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to the handling of the `dirichlet_character` definition and the properties `COPRIME_1`, `ARITH`, and `COMPLEX_RING`. Ensure that the target system's arithmetic and complex number libraries are used correctly to mirror the HOL Light proof. Additionally, the induction step (`INDUCT_TAC`) might need to be adapted based on the induction principles available in the target system.

---

## DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL

### Name of formal statement
DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> ~(d = 0) /\ ~(d = 1)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `d = 0` THEN
  ASM_REWRITE_TAC[DIRICHLET_CHARACTER_0; TAUT `~(p /\ ~p)`] THEN
  ASM_CASES_TAC `d = 1` THEN
  ASM_REWRITE_TAC[DIRICHLET_CHARACTER_1; chi_0; FUN_EQ_THM; COPRIME_1] THEN
  CONV_TAC TAUT)
```

### Informal statement
For all `d` and `c`, if `c` is a Dirichlet character modulo `d` and `c` is not the principal character modulo `d`, then `d` is not equal to 0 and `d` is not equal to 1.

### Informal sketch
* The proof starts by assuming `d` equals 0 and derives a contradiction using `DIRICHLET_CHARACTER_0` and the fact that a character cannot be both principal and non-principal.
* Then, it assumes `d` equals 1 and derives another contradiction using `DIRICHLET_CHARACTER_1`, `chi_0`, `FUN_EQ_THM`, and `COPRIME_1`, showing that the only character modulo 1 is the principal character.
* The proof concludes by combining these cases, showing that for any `d` and `c` where `c` is a non-principal Dirichlet character modulo `d`, `d` cannot be 0 or 1.

### Mathematical insight
This theorem provides a fundamental property of Dirichlet characters, highlighting that non-principal characters can only exist for moduli greater than 1. This is crucial in number theory, particularly in the study of Dirichlet series and their applications to problems like the distribution of prime numbers.

### Dependencies
* `DIRICHLET_CHARACTER_0`
* `DIRICHLET_CHARACTER_1`
* `chi_0`
* `FUN_EQ_THM`
* `COPRIME_1`
* `TAUT`

### Porting notes
When translating this theorem into another proof assistant, pay special attention to how Dirichlet characters are defined and how the `dirichlet_character` predicate is handled. Additionally, ensure that the proof assistant can handle the `GEN_TAC` and `ASM_CASES_TAC` tactics or their equivalents, as these are crucial for the proof's structure. The automation provided by `CONV_TAC TAUT` may also need to be adapted, depending on the target system's capabilities.

---

## DIRICHLET_CHARACTER_ZEROSUM

### Name of formal statement
DIRICHLET_CHARACTER_ZEROSUM

### Type of the formal statement
Theorem

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
  ASM_MESON_TAC[DIRICHLET_CHARACTER_CONG])
```

### Informal statement
For all `d` and `c`, if `c` is a Dirichlet character modulo `d` and `c` is not the principal character `chi_0` modulo `d`, then the sum of `c(n)` over all `n` from 1 to `d` is equal to 0.

### Informal sketch
* The proof starts by assuming that `c` is a Dirichlet character modulo `d` and `c` is not the principal character `chi_0` modulo `d`.
* It uses the `DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL` theorem to derive a non-trivial property of `c`.
* Then, it applies the `DIRICHLET_CHARACTER_NONPRINCIPAL` theorem to `c` and uses the result to choose an `m` such that `c(m)` is not equal to 1.
* The proof then uses the `COMPLEX_RING` theorem to show that `c(m)` is equal to 0.
* It then uses the `VSUM` definition and the `FINITE_NUMSEG` theorem to rewrite the sum of `c(n)` over all `n` from 1 to `d`.
* The proof then applies the `MESON` theorem to show that the sum of `c(n)` over all `n` from 1 to `d` is equal to the sum of `c(n)` over all `n` that are coprime to `d`.
* It then uses the `VSUM_SUPERSET` theorem and the `IN_NUMSEG` theorem to show that the sum of `c(n)` over all `n` that are coprime to `d` is equal to the sum of `c(n)` over all `n` from 1 to `d`.
* The proof then uses the `DIRICHLET_CHARACTER_EQ_0` theorem and the `COMPLEX_MUL_RZERO` theorem to show that the sum of `c(n)` over all `n` from 1 to `d` is equal to 0.

### Mathematical insight
The `DIRICHLET_CHARACTER_ZEROSUM` theorem is a fundamental property of Dirichlet characters, which are used to study the distribution of prime numbers. This theorem shows that the sum of a non-principal Dirichlet character over all `n` from 1 to `d` is equal to 0, which has important implications for the study of prime numbers and the distribution of values of Dirichlet characters.

### Dependencies
* Theorems:
 + `DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL`
 + `DIRICHLET_CHARACTER_NONPRINCIPAL`
 + `COMPLEX_RING`
 + `VSUM`
 + `FINITE_NUMSEG`
 + `MESON`
 + `VSUM_SUPERSET`
 + `IN_NUMSEG`
 + `DIRICHLET_CHARACTER_EQ_0`
 + `COMPLEX_MUL_RZERO`
 + `ITERATE_OVER_COPRIME`
 + `MONOIDAL_VECTOR_ADD`
 + `DIRICHLET_CHARACTER_CONG`
* Definitions:
 + `dirichlet_character`
 + `chi_0`
 + `coprime`
 + `vsum`

---

## DIRICHLET_CHARACTER_ZEROSUM_MUL

### Name of formal statement
DIRICHLET_CHARACTER_ZEROSUM_MUL

### Type of the formal statement
Theorem

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
  ASM_REWRITE_TAC[] THEN NUMBER_TAC)
```

### Informal statement
For all `d`, `c`, and `n`, if `c` is a Dirichlet character modulo `d` and `c` is not the principal character `chi_0` modulo `d`, then the sum of `c` from `1` to `d*n` is equal to the complex number `0`.

### Informal sketch
* The proof starts by assuming the premises: `dirichlet_character d c` and `c` is not equal to `chi_0 d`.
* It then proceeds by induction, using `INDUCT_TAC` to break down the problem into smaller sub-problems.
* The `REWRITE_TAC` and `ASM_SIMP_TAC` steps simplify the expressions and apply various properties of Dirichlet characters, such as `DIRICHLET_CHARACTER_ZEROSUM` and `DIRICHLET_CHARACTER_CONG`.
* The `MATCH_MP_TAC` steps apply the `VSUM_EQ` and `DIRICHLET_CHARACTER_CONG` theorems to establish the desired equality.
* Key steps involve using `VSUM_ADD_SPLIT` and `COMPLEX_ADD_LID` to manipulate the summations and complex numbers.

### Mathematical insight
This theorem is important because it establishes a fundamental property of Dirichlet characters, which are crucial in number theory. The result shows that the sum of a non-principal Dirichlet character over a certain range is zero, which has implications for various applications in analytic number theory.

### Dependencies
* Theorems:
	+ `DIRICHLET_CHARACTER_ZEROSUM`
	+ `VSUM_EQ`
	+ `DIRICHLET_CHARACTER_CONG`
* Definitions:
	+ `dirichlet_character`
	+ `chi_0`
	+ `vsum`
	+ `Cx`
* Inductive rules:
	+ `INDUCT_TAC`

### Porting notes
When translating this theorem to other proof assistants, pay attention to the handling of binders and the `INDUCT_TAC` step, as the induction strategy may need to be adapted. Additionally, the `MATCH_MP_TAC` steps may require manual instantiation of the theorems `VSUM_EQ` and `DIRICHLET_CHARACTER_CONG`, depending on the proof assistant's automation capabilities.

---

## DIRICHLET_CHARACTER_SUM_MOD

### Name of formal statement
DIRICHLET_CHARACTER_SUM_MOD

### Type of the formal statement
Theorem

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
  ASM_REWRITE_TAC[] THEN CONV_TAC NUMBER_RULE)
```

### Informal statement
For all `d` and `c`, if `c` is a Dirichlet character modulo `d` and `c` is not the principal character `chi_0` modulo `d`, then the sum of `c` from 1 to `n` is equal to the sum of `c` from 1 to `n` modulo `d`.

### Informal sketch
* The proof starts by assuming that `c` is a Dirichlet character modulo `d` and `c` is not the principal character `chi_0` modulo `d`.
* It then applies the `DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL` theorem to `c` and `d`.
* The proof proceeds by using the division algorithm to rewrite `n` as `qd + r`, where `q` is the quotient and `r` is the remainder.
* It then uses the `VSUM_ADD_SPLIT` and `ARITH_RULE` theorems to split the sum of `c` from 1 to `n` into the sum of `c` from 1 to `r`.
* The proof continues by applying various simplification and rewriting tactics, including `SIMP_TAC`, `ONCE_REWRITE_TAC`, and `ASM_SIMP_TAC`, to simplify the expression and ultimately show that the sum of `c` from 1 to `n` is equal to the sum of `c` from 1 to `n` modulo `d`.
* Key steps involve using the `DIRICHLET_CHARACTER_ZEROSUM` and `DIRICHLET_CHARACTER_CONG` theorems to establish the desired equality.

### Mathematical insight
This theorem provides a property of Dirichlet characters, which are important in number theory. The theorem shows that the sum of a Dirichlet character over a range can be reduced to a sum over a smaller range, modulo `d`. This property is useful in various applications, such as in the study of Dirichlet series and their analytic properties.

### Dependencies
#### Theorems
* `DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL`
* `DIVISION`
* `VSUM_ADD_SPLIT`
* `ARITH_RULE`
* `DIRICHLET_CHARACTER_ZEROSUM`
* `DIRICHLET_CHARACTER_CONG`
* `VSUM_EQ`
#### Definitions
* `dirichlet_character`
* `chi_0`
* `vsum` 

### Porting notes
When porting this theorem to another proof assistant, pay attention to the handling of binders and the `GEN_TAC` and `DISCH_TAC` tactics, which may need to be translated into the target system's equivalent constructs. Additionally, the `MATCH_MP` and `MATCH_MP_TAC` tactics may require special attention, as they involve pattern matching and tactic application. The `CONV_TAC` and `NUMBER_RULE` tactics may also need to be translated, as they involve conversions and arithmetic reasoning.

---

## FINITE_DIRICHLET_CHARACTERS

### Name of formal statement
FINITE_DIRICHLET_CHARACTERS

### Type of the formal statement
Theorem

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
                  DIRICHLET_CHARACTER_EQ_0]])
```

### Informal statement
For all `d`, the set of `c` such that `dirichlet_character d c` is finite.

### Informal sketch
* The proof proceeds by first considering the case when `d = 0`, where it uses `DIRICHLET_CHARACTER_0` and `SET_RULE` to simplify the set of characters.
* For `d ≠ 0`, it applies `FINITE_SUBSET` and exhibits a subset of the set of characters that is finite.
* The exhibited subset is constructed using the `IMAGE` of a function that maps `c` to `c(n MOD d)`, where `c` ranges over a set of functions defined by certain properties.
* The proof then shows that this image is finite by applying `FINITE_IMAGE`, `FINITE_FUNSPACE`, and `FINITE_COMPLEX_ROOTS_UNITY`.
* It also shows that the image is a subset of the original set of characters by using `SUBSET` and `IN_ELIM_THM`.
* The proof then uses `DIRICHLET_CHARACTER_CONG` and `DIRICHLET_CHARACTER_ROOT` to establish the required properties of the characters in the image.

### Mathematical insight
This theorem establishes the finiteness of the set of Dirichlet characters modulo `d`, which is a fundamental property in number theory. The proof constructs a finite subset of the characters and shows that it is the entire set of characters, thus establishing finiteness.

### Dependencies
* Theorems:
 + `DIRICHLET_CHARACTER_0`
 + `FINITE_SUBSET`
 + `FINITE_IMAGE`
 + `FINITE_FUNSPACE`
 + `FINITE_COMPLEX_ROOTS_UNITY`
 + `DIRICHLET_CHARACTER_CONG`
 + `DIRICHLET_CHARACTER_ROOT`
* Definitions:
 + `dirichlet_character`
 + `phi` (Euler's totient function)
* Axioms and rules:
 + `GEN_TAC`
 + `ASM_CASES_TAC`
 + `MATCH_MP_TAC`
 + `EXISTS_TAC`
 + `REWRITE_TAC`
 + `ASM_SIMP_TAC`
 + `CONJ_TAC`
 + `X_GEN_TAC`
 + `DISCH_TAC`

---

## DIRICHLET_CHARACTER_MUL_CNJ

### Name of formal statement
DIRICHLET_CHARACTER_MUL_CNJ

### Type of the formal statement
Theorem

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
  REWRITE_TAC[COMPLEX_DIV_1])
```

### Informal statement
For all `d`, `c`, and `n`, if `c` is a Dirichlet character modulo `d` and `c(n)` is not equal to 0, then the complex conjugate of `c(n)` multiplied by `c(n)` equals 1, and `c(n)` multiplied by its complex conjugate equals 1.

### Informal sketch
* The proof starts by assuming `c` is a Dirichlet character modulo `d` and `c(n)` is not zero.
* It then applies the `COMPLEX_FIELD` theorem, which states that if `z` is not zero and `w` is the inverse of `z`, then `w * z = 1` and `z * w = 1`.
* The proof uses `ASM_REWRITE_TAC` with `COMPLEX_INV_CNJ` to rewrite the inverse of `c(n)` as its complex conjugate.
* It then uses `FIRST_ASSUM` with `GEN_REWRITE_RULE` and `GSYM COMPLEX_NORM_NZ` to derive a property about the norm of `c(n)`.
* The `DIRICHLET_CHARACTER_NORM` theorem is applied to rewrite the norm of `c(n)`.
* The proof then proceeds with case analysis using `COND_CASES_TAC` and applies various rewriting rules to simplify the expressions.
* The final steps involve rewriting with `COMPLEX_DIV_1` to conclude the proof.

### Mathematical insight
This theorem establishes a basic property of Dirichlet characters, showing that they satisfy a certain multiplicative relationship with their complex conjugates. This property is essential in number theory, particularly in the study of Dirichlet characters and their applications to problems involving prime numbers and modular forms.

### Dependencies
* Theorems:
  + `COMPLEX_FIELD`
  + `DIRICHLET_CHARACTER_NORM`
* Definitions:
  + `dirichlet_character`
  + `COMPLEX_INV_CNJ`
  + `COMPLEX_NORM_NZ`
  + `COMPLEX_POW_ONE`
  + `COMPLEX_DIV_1`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of complex numbers, their inverses, and the properties of Dirichlet characters. The `COMPLEX_FIELD` theorem and its equivalent in the target system will be crucial. Additionally, ensure that the target system can handle the case analysis and rewriting steps in a similar manner to HOL Light.

---

## DIRICHLET_CHARACTER_CNJ

### Name of formal statement
DIRICHLET_CHARACTER_CNJ

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_CNJ = prove
 (`!d c. dirichlet_character d c ==> dirichlet_character d (\n. cnj(c n))`,
  SIMP_TAC[dirichlet_character; CNJ_MUL; CNJ_EQ_CX])
```

### Informal statement
For all `d` and `c`, if `c` is a Dirichlet character modulo `d`, then the function that maps each `n` to the complex conjugate of `c(n)` is also a Dirichlet character modulo `d`.

### Informal sketch
* The proof starts with the assumption that `c` is a Dirichlet character modulo `d`, which implies that `c` satisfies certain properties, such as being a multiplicative function.
* The goal is to show that the function `cnj(c n)` also satisfies these properties, specifically that it is a Dirichlet character modulo `d`.
* The proof uses the `SIMP_TAC` tactic with theorems `dirichlet_character`, `CNJ_MUL`, and `CNJ_EQ_CX` to simplify and establish the desired properties of `cnj(c n)`.
* The use of `CNJ_MUL` and `CNJ_EQ_CX` suggests that the proof involves properties of complex conjugation, such as its behavior under multiplication.

### Mathematical insight
This theorem is important because it shows that the complex conjugate of a Dirichlet character is also a Dirichlet character, which is a fundamental property in number theory. This result can be used to derive other properties of Dirichlet characters and has implications for various applications in number theory, such as the study of L-functions and the distribution of prime numbers.

### Dependencies
* Theorems:
  + `dirichlet_character`
  + `CNJ_MUL`
  + `CNJ_EQ_CX`

### Porting notes
When translating this theorem into another proof assistant, care should be taken to ensure that the properties of Dirichlet characters and complex conjugation are properly defined and used. The `SIMP_TAC` tactic may need to be replaced with equivalent tactics or rewriting rules in the target system. Additionally, the use of `CNJ_MUL` and `CNJ_EQ_CX` may require special attention, as the behavior of complex conjugation can vary between systems.

---

## DIRICHLET_CHARACTER_GROUPMUL

### Name of formal statement
DIRICHLET_CHARACTER_GROUPMUL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_GROUPMUL = prove
 (`!d c1 c2. dirichlet_character d c1 /\ dirichlet_character d c2
             ==> dirichlet_character d (\n. c1(n) * c2(n))`,
  SIMP_TAC[dirichlet_character; COMPLEX_ENTIRE] THEN
  REWRITE_TAC[COMPLEX_MUL_AC])
```

### Informal statement
For all `d`, `c1`, and `c2`, if `c1` is a Dirichlet character modulo `d` and `c2` is a Dirichlet character modulo `d`, then the function that maps each `n` to the product of `c1(n)` and `c2(n)` is also a Dirichlet character modulo `d`.

### Informal sketch
* The proof starts by assuming `c1` and `c2` are Dirichlet characters modulo `d`.
* It then constructs a new function that maps each `n` to the product `c1(n) * c2(n)`.
* The `SIMP_TAC` tactic is used with `dirichlet_character` and `COMPLEX_ENTIRE` to simplify the expression and establish properties of the new function.
* The `REWRITE_TAC` tactic with `COMPLEX_MUL_AC` is applied to utilize the associativity and commutativity of complex multiplication, further simplifying the expression and showing that the new function satisfies the conditions for being a Dirichlet character modulo `d`.

### Mathematical insight
This theorem is important because it shows that the set of Dirichlet characters modulo `d` is closed under pointwise multiplication, which is a fundamental operation in number theory. This property is crucial for constructing and manipulating Dirichlet characters, which play a significant role in many number theoretic applications, including the study of Dirichlet series and L-functions.

### Dependencies
* `dirichlet_character`
* `COMPLEX_ENTIRE`
* `COMPLEX_MUL_AC`

### Porting notes
When translating this theorem into other proof assistants, special attention should be paid to how Dirichlet characters are defined and how properties of complex numbers are handled. The `SIMP_TAC` and `REWRITE_TAC` tactics may have direct analogs in other systems, but the specific flags and theorems used (`dirichlet_character`, `COMPLEX_ENTIRE`, `COMPLEX_MUL_AC`) will need to be replaced with their equivalents in the target system. Additionally, the handling of quantifiers and the pointwise multiplication of functions may require careful consideration to ensure that the translation accurately reflects the original theorem.

---

## DIRICHLET_CHARACTER_GROUPINV

### Name of formal statement
DIRICHLET_CHARACTER_GROUPINV

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_GROUPINV = prove
 (`!d c. dirichlet_character d c ==> (\n. cnj(c n) * c n) = chi_0 d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[chi_0; FUN_EQ_THM] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [ASM_MESON_TAC[DIRICHLET_CHARACTER_MUL_CNJ; DIRICHLET_CHARACTER_EQ_0];
    ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_0; COMPLEX_MUL_RZERO]])
```

### Informal statement
For all `d` and `c`, if `c` is a Dirichlet character modulo `d`, then for all `n`, the product of the complex conjugate of `c(n)` and `c(n)` equals `chi_0(d)`, where `chi_0` denotes the principal Dirichlet character.

### Informal sketch
* The proof begins by assuming `c` is a Dirichlet character modulo `d`.
* It then applies `REPEAT STRIP_TAC` to strip away the universal quantifier and `REWRITE_TAC` to rewrite the equation using `chi_0` and `FUN_EQ_THM`.
* The proof proceeds with `COND_CASES_TAC`, considering two cases:
  + If `c(n)` is nonzero, it uses `ASM_MESON_TAC` with `DIRICHLET_CHARACTER_MUL_CNJ` and `DIRICHLET_CHARACTER_EQ_0` to derive the result.
  + If `c(n)` is zero, it uses `ASM_MESON_TAC` with `DIRICHLET_CHARACTER_EQ_0` and `COMPLEX_MUL_RZERO` to derive the result.

### Mathematical insight
This theorem provides insight into the properties of Dirichlet characters, specifically showing that the product of a character and its complex conjugate equals the principal character. This result is important in number theory, as Dirichlet characters play a crucial role in the study of Dirichlet series and their applications to problems in analytic number theory.

### Dependencies
* `dirichlet_character`
* `chi_0`
* `DIRICHLET_CHARACTER_MUL_CNJ`
* `DIRICHLET_CHARACTER_EQ_0`
* `COMPLEX_MUL_RZERO`
* `FUN_EQ_THM`

### Porting notes
When translating this theorem into other proof assistants, note that the `REPEAT STRIP_TAC` and `COND_CASES_TAC` tactics may need to be replaced with equivalent tactics or strategies in the target system. Additionally, the `ASM_MESON_TAC` tactic, which is used to apply a set of theorems to derive a conclusion, may require manual substitution or the use of a similar tactic in the target system.

---

## DIRICHLET_CHARACTER_SUM_OVER_NUMBERS

### Name of formal statement
DIRICHLET_CHARACTER_SUM_OVER_NUMBERS

### Type of the formal statement
Theorem

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
  ASM_REWRITE_TAC[] THEN ARITH_TAC)
```

### Informal statement
For all positive integers `d` and all `c`, if `c` is a Dirichlet character modulo `d`, then the sum of `c` over the numbers from 1 to `d` is equal to `Cx(&phi(d))` if `c` is the principal character modulo `d` (denoted `chi_0 d`), and `Cx(&0)` otherwise.

### Informal sketch
* The proof starts by considering the definition of a Dirichlet character and its properties.
* It then applies `COND_CASES_TAC` to split the proof into cases based on whether `c` is the principal character `chi_0 d`.
* The `ASM_SIMP_TAC` with `DIRICHLET_CHARACTER_ZEROSUM` suggests simplification using properties of Dirichlet characters, specifically leveraging the fact that the sum of a Dirichlet character over its period is zero unless it's the principal character.
* The use of `GEN_REWRITE_TAC` with `GSYM ETA_AX` indicates a step involving the application of a general rewrite rule, possibly related to the handling of complex numbers or character properties.
* Further simplifications and rewrites are applied, including those related to `chi_0`, `phi`, and properties of summations (`VSUM_CONST`, `FINITE_RESTRICT`, `FINITE_NUMSEG`).
* The proof involves recognizing that the sum of the principal character `chi_0 d` over the numbers 1 to `d` relates to Euler's totient function `phi(d)`, while for other characters, the sum is zero.
* The final steps involve arithmetic manipulations and possibly case analysis based on coprimality (`coprime(x,d)`), leading to the conclusion.

### Mathematical insight
This theorem captures an orthogonality relation among Dirichlet characters, which is fundamental in number theory. It states that the sum of a Dirichlet character over its period is non-zero only for the principal character, and in that case, it equals the Euler's totient function of the modulus. This property is crucial in various applications, including the proof of Dirichlet's theorem on arithmetic progressions.

### Dependencies
- `dirichlet_character`
- `chi_0`
- `phi`
- `DIRICHLET_CHARACTER_ZEROSUM`
- `VSUM_CONST`
- `FINITE_RESTRICT`
- `FINITE_NUMSEG`
- `COMPLEX_CMUL`
- `COMPLEX_MUL_RID`

### Porting notes
When translating this into another proof assistant, special attention should be given to how Dirichlet characters and their properties are defined and used. The handling of summations, especially over finite sets, and the treatment of complex numbers may also require careful consideration due to differences in how these are represented and manipulated across systems. Additionally, the use of `COND_CASES_TAC` and `ASM_SIMP_TAC` suggests that conditional statements and simplification tactics may need to be adapted to the target system's syntax and proof strategies.

---

## DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK

### Name of formal statement
DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK

### Type of the formal statement
Theorem

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
  ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_0; DIRICHLET_CHARACTER_MUL_CNJ])
```

### Informal statement
For all `d` and `n`, either the sum of `c(n)` over all `c` such that `dirichlet_character d c` is `0`, or `n` and `d` are coprime and for all `c` such that `dirichlet_character d c`, `c(n)` equals `1`.

### Informal sketch
* The proof starts by considering cases based on whether `n` and `d` are coprime.
* If they are not coprime, the sum is shown to be `0` by using the property that `dirichlet_character d c` implies `c(n) = 0` when `n` and `d` are not coprime.
* If `n` and `d` are coprime, the proof involves showing that for any `c'` such that `dirichlet_character d c'`, a certain property about the sum of `c(n)` over all `c` holds.
* This involves using properties of `vsum`, `dirichlet_character`, and complex numbers, including the fact that `a * x = x` if and only if `a = 1` or `x = 0`.
* The proof then proceeds by using `VSUM_INJECTION` and properties of `dirichlet_character` to establish the desired result.
* Key steps involve using `MATCH_MP_TAC` with `VSUM_EQ_0` and `COMPLEX_RING` to derive equalities and using `ASM_MESON_TAC` to apply the `dirichlet_character` properties.

### Mathematical insight
This theorem provides insight into the properties of Dirichlet characters, specifically how they behave under summation and how their values relate to coprimality. It's a fundamental result in number theory, connecting the concepts of Dirichlet characters, coprimality, and summation over characters.

### Dependencies
#### Theorems
* `VSUM_EQ_0`
* `COMPLEX_RING`
#### Definitions
* `dirichlet_character`
* `vsum`
* `coprime`
#### Other
* `FINITE_DIRICHLET_CHARACTERS`
* `DIRICHLET_CHARACTER_EQ_0`
* `DIRICHLET_CHARACTER_GROUPMUL`
* `DIRICHLET_CHARACTER_MUL_CNJ` 

### Porting notes
When translating this into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles binders, summations, and properties of complex numbers. The use of `MATCH_MP_TAC` and `ASM_MESON_TAC` may need to be adapted, as these tactics are specific to HOL Light. Additionally, the representation of `dirichlet_character` and related properties may vary between systems, requiring careful consideration to ensure the translation accurately captures the mathematical structure and intent of the original proof.

---

## DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_POS

### Name of formal statement
DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_POS

### Type of the formal statement
Theorem

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
  REWRITE_TAC[REAL_POS])
```

### Informal statement
For all `d` and `n`, the real part of the sum over all `c` such that `c` is a Dirichlet character modulo `d`, of `c(n)`, is real and non-negative.

### Informal sketch
* The proof starts by applying `DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK` using `MP_TAC`.
* It then proceeds to introduce universal quantifiers for `d` and `n` using `MATCH_MP_TAC MONO_FORALL` and `GEN_TAC`.
* The statement is then split into two parts using `CONJ_TAC`: one part showing the sum is real, and the other part showing the real part of the sum is non-negative.
* To show the sum is real, `MATCH_MP_TAC REAL_VSUM` is applied.
* To show the real part of the sum is non-negative, `SIMP_TAC` and `MATCH_MP_TAC SUM_POS_LE` are used, leveraging the fact that the set of Dirichlet characters modulo `d` is finite (`FINITE_DIRICHLET_CHARACTERS`).
* The proof concludes by simplifying using `ASM_SIMP_TAC` and rewriting with `REAL_POS`.

### Mathematical insight
This theorem provides a property about the sum of values of Dirichlet characters, which are crucial in number theory, especially in the context of Dirichlet series and L-functions. The theorem ensures that for any modulus `d` and any integer `n`, the sum of the values of all Dirichlet characters modulo `d` evaluated at `n` has a non-negative real part. This is significant because it gives insight into the behavior of these characters, which are used to study properties of prime numbers and other arithmetic functions.

### Dependencies
#### Theorems
* `DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK`
* `REAL_VSUM`
* `SUM_POS_LE`
#### Definitions
* `dirichlet_character`
* `REAL_CX`
* `RE_CX`
* `REAL_LE_REFL`
* `FINITE_DIRICHLET_CHARACTERS`
* `IN_ELIM_THM`
* `REAL_POS`

---

## CHARACTER_EXTEND_FROM_SUBGROUP

### Name of formal statement
CHARACTER_EXTEND_FROM_SUBGROUP

### Type of the formal statement
Theorem

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
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN MAP_EVERY EXISTS_TAC [`1`; `0`] THEN
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
    ONCE_REWRITE_TAC[ARITH_RULE `(x * a) * (z * ak):num = (x * z) * (a * ak)`] THEN
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
For all functions `f`, sets `h`, elements `a`, and positive integers `d`, if `h` is a subset of `{x | x < d /\ coprime(x,d)}`, `1` is in `h`, for all `x` and `y` in `h`, `(x * y) MOD d` is in `h`, for all `x` in `h`, there exists `y` in `h` such that `x * y == 1 (mod d)`, for all `x` in `h`, `f(x)` is not equal to `0`, for all `x` and `y` in `h`, `f((x * y) MOD d)` equals `f(x) * f(y)`, and `a` is in `{x | x < d /\ coprime(x,d)}` but not in `h`, then there exists a function `f'` and a set `h'` such that `a INSERT h` is a subset of `h'`, `h'` is a subset of `{x | x < d /\ coprime(x,d)}`, for all `x` in `h`, `f'(x)` equals `f(x)`, `f'(a)` is not equal to `1`, `1` is in `h'`, for all `x` and `y` in `h'`, `(x * y) MOD d` is in `h'`, for all `x` in `h'`, there exists `y` in `h'` such that `x * y == 1 (mod d)`, for all `x` in `h'`, `f'(x)` is not equal to `0`, and for all `x` and `y` in `h'`, `f'((x * y) MOD d)` equals `f'(x) * f'(y)`.

### Informal sketch
The proof of `CHARACTER_EXTEND_FROM_SUBGROUP` involves several main stages:
* It starts by assuming the given conditions about `h`, `f`, `a`, and `d`.
* It uses `FERMAT_LITTLE` to establish the existence of `m` and `x` in `h` such that `a EXP m == x (mod d)`.
* It then shows that for all `x` in `h` and `s`, `(x EXP s) MOD d` is in `h`.
* The proof proceeds to find a complex number `z` that is a non-trivial `m`-th root of unity, where `m` is the order of `a` modulo `d`.
* It defines a new function `g` on the set `{(x * a EXP k) MOD d | x IN h /\ k IN (:num)}` such that `g((x * a EXP k) MOD d) = f(x) * z pow k`.
* The proof then verifies that `g` satisfies the required properties to extend `f` to a larger set `h'` containing `a`.
* Finally, it constructs `h'` and shows that it meets all the conditions stated in the theorem.

### Mathematical insight
The `CHARACTER_EXTEND_FROM_SUBGROUP` theorem provides a way to extend a character `f` from a subgroup `h` of `{x | x < d /\ coprime(x,d)}` to a larger set `h'` containing a given element `a`, under certain conditions. This is useful in number theory, particularly in the study of characters and their properties.

### Dependencies
#### Theorems
* `FERMAT_LITTLE`
* `PHI_LOWERBOUND_1_STRONG`
* `EXISTS_COMPLEX_ROOT_NONTRIVIAL`
#### Definitions
* `coprime`
* `EXP`
* `MOD`
* `Cx` (complex number constructor)

### Porting notes
When translating this theorem into another proof assistant, special attention should be paid to the handling of:
* Modular arithmetic properties and theorems like `FERMAT_LITTLE`.
* The definition and properties of the `coprime` relation.
* The use of complex numbers and their roots, particularly the `EXISTS_COMPLEX_ROOT_NONTRIVIAL` theorem.
* The construction of the function `g` and its properties, which may require careful handling of binders and function definitions.
* The overall structure of the proof, which involves several cases and the use of various mathematical properties and theorems.

---

## DIRICHLET_CHARACTER_DISCRIMINATOR

### Name of formal statement
DIRICHLET_CHARACTER_DISCRIMINATOR

### Type of the formal statement
Theorem

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
      ASM_SIMP_TAC[DIVISION; COPRIME_LMOD; LE_1]]])
```

### Informal statement
For all `d` and `n`, if `1 < d` and `n` is not congruent to `1` modulo `d`, then there exists a `dirichlet_character` `c` of modulus `d` such that `c(n)` is not equal to `1`.

### Informal sketch
* The proof starts by assuming `1 < d` and `n` is not congruent to `1` modulo `d`.
* It then considers two cases: `coprime(n, d)` and `~coprime(n, d)`.
* In the case of `coprime(n, d)`, it uses the `CHARACTER_EXTEND_FROM_SUBGROUP` theorem to extend a character from a subgroup.
* It then uses well-founded induction to prove the existence of a character `c` of modulus `d` such that `c(n)` is not equal to `1`.
* The induction step involves finding a new character `ff` and a new subgroup `hh` that satisfy certain properties.
* The proof then uses the `MONO_EXISTS` tactic to prove the existence of `ff` and `hh`.
* Finally, it uses the `dirichlet_character` definition to construct the desired character `c`.

### Mathematical insight
This theorem is important because it shows that for any `d` and `n` satisfying certain conditions, there exists a `dirichlet_character` `c` of modulus `d` that distinguishes `n` from `1` modulo `d`. This is a key result in number theory, particularly in the study of Dirichlet characters and their applications to problems in analytic number theory.

### Dependencies
* `dirichlet_character`
* `CHARACTER_EXTEND_FROM_SUBGROUP`
* `coprime`
* `MOD`
* `CONG`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the `dirichlet_character` definition and the `CHARACTER_EXTEND_FROM_SUBGROUP` theorem are properly translated. Additionally, the use of well-founded induction and the `MONO_EXISTS` tactic may require special attention, as these concepts may be implemented differently in other proof assistants.

---

## DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_INEXPLICIT

### Name of formal statement
DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_INEXPLICIT

### Type of the formal statement
Theorem

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
                  ARITH_RULE `~(d = 0) /\ ~(d = 1) ==> 1 < d`])
```

### Informal statement
For all `d` and `n`, the sum over all `c` such that `c` is a Dirichlet character modulo `d`, of `c(n)`, is equal to the cardinality of the set of all Dirichlet characters modulo `d` if `n` is congruent to 1 modulo `d`, and is equal to 0 otherwise.

### Informal sketch
* The proof proceeds by cases on `d`: 
  * If `d` is 0, the statement is proved by simplifying the expression using `CONG_MOD_0`, `DIRICHLET_CHARACTER_0`, and properties of sets and sums.
  * If `d` is 1, the statement is proved by simplifying the expression using `CONG_MOD_1`, `DIRICHLET_CHARACTER_1`, and properties of functions and sets.
  * For other values of `d`, the proof uses a conditional case split and applies `EQ_TRANS` to transform the sum into a more manageable form. It then uses `VSUM_EQ` and `DIRICHLET_CHARACTER_EQ_1` to simplify the expression, and finally applies `DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK` to conclude the proof.

### Mathematical insight
This theorem provides a key property of Dirichlet characters, which are important in number theory. The statement relates the sum of Dirichlet characters evaluated at a given `n` to the cardinality of the set of Dirichlet characters modulo `d`, depending on whether `n` is congruent to 1 modulo `d`. This property is crucial in various applications, including the study of Dirichlet series and the proof of the Prime Number Theorem.

### Dependencies
* Theorems:
  + `DIRICHLET_CHARACTER_EQ_1`
  + `DIRICHLET_CHARACTER_CONG`
  + `DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK`
  + `CONG_MOD_0`
  + `CONG_MOD_1`
  + `DIRICHLET_CHARACTER_0`
  + `DIRICHLET_CHARACTER_1`
* Definitions:
  + `dirichlet_character`
  + `vsum`
  + `CARD`
* Axioms and rules:
  + `EQ_TRANS`
  + `VSUM_EQ`
  + `IN_ELIM_THM`
  + `FINITE_DIRICHLET_CHARACTERS`
  + `VSUM_CONST`
  + `COMPLEX_CMUL`
  + `COMPLEX_MUL_RID`
  + `ARITH_RULE`

### Porting notes
When translating this theorem into other proof assistants, special attention should be paid to the handling of binders and the representation of Dirichlet characters. The use of `EQ_TRANS` and `VSUM_EQ` may require careful handling of equality and summation in the target system. Additionally, the `DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK` theorem, which is used in the proof, may need to be ported or proved separately in the target system.

---

## DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS

### Name of formal statement
DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS

### Type of the formal statement
Theorem

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
    ASM_REWRITE_TAC[LT_LE]])
```

### Informal statement
For all positive integers `d` and integers `n`, if `1` is less than or equal to `d`, then the sum over all Dirichlet characters `c` modulo `d` of `c(n)` equals `Cx(&(phi d))` if `n` is congruent to `1` modulo `d`, and `Cx(&0)` otherwise.

### Informal sketch
* The proof begins by assuming `1 <= d` and then considers the sum of `c(n)` over all Dirichlet characters `c` modulo `d`.
* It then applies various simplifications and transformations, including `REWRITE_TAC` with `DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_INEXPLICIT`, and `COND_CASES_TAC` to handle different cases based on the value of `n` modulo `d`.
* The `VSUM_SWAP` theorem is used to swap the order of summation, and `SIMP_TAC` is applied with several theorems to simplify the expression.
* The proof then proceeds by cases, considering whether `d = 1` and whether `k = d`, using `ASM_CASES_TAC` and `ASM_REWRITE_TAC` to derive the desired conclusion.
* Key steps involve recognizing that the sum over Dirichlet characters can be simplified using properties of the characters and modular arithmetic.

### Mathematical insight
This theorem provides a formula for the sum of Dirichlet characters `c` modulo `d` evaluated at `n`, which is essential in number theory, particularly in the study of Dirichlet series and their applications. The formula distinguishes between `n` being congruent to `1` modulo `d` (in which case the sum is related to Euler's totient function `phi(d)`) and other cases where the sum is zero.

### Dependencies
#### Theorems
* `DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_INEXPLICIT`
* `VSUM_SWAP`
* `DIRICHLET_CHARACTER_SUM_OVER_NUMBERS`
* `FINITE_NUMSEG`
* `FINITE_DIRICHLET_CHARACTERS`
* `ETA_AX`
* `VSUM_DELTA`
* `GSYM COMPLEX_VEC_0`
* `IN_ELIM_THM`
* `DIRICHLET_CHARACTER_CHI_0`
* `EXTENSION`
* `IN_SING`
* `IN_ELIM_THM`
* `IN_NUMSEG`
* `CONG_MOD_1`
* `LE_ANTISYM`
* `CONG_IMP_EQ`
* `DIVIDES_ONE`

#### Definitions
* `dirichlet_character`
* `Cx`
* `phi`

---

## Lfunction_DEF

### Name of formal statement
Lfunction_DEF

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let Lfunction_DEF = new_definition
 `Lfunction c = infsum (from 1) (\n. c(n) / Cx(&n))`
```

### Informal statement
The function `Lfunction` is defined as the infinite sum from 1 to infinity of the series `c(n) / Cx(n)`, where `c` is a function that takes a natural number `n` and returns a value, and `Cx` is a function that takes a natural number `n` and returns a value.

### Informal sketch
* The definition of `Lfunction` involves an infinite sum, which suggests a limit process.
* The summand `c(n) / Cx(&n)` depends on the functions `c` and `Cx`, and the variable `n`.
* To prove properties about `Lfunction`, one might need to use results about infinite series, such as convergence tests or properties of limits.
* Key HOL Light terms like `infsum` and `from` are used to define the infinite sum.

### Mathematical insight
The `Lfunction` definition appears to be related to L-series, which are a type of infinite series that arise in number theory. The definition at `s = 1` suggests a special case or a specific value of interest. This definition is likely important for studying properties of L-series or for applying them in other mathematical contexts.

### Dependencies
* `infsum`
* `from`
* `c`
* `Cx`

### Porting notes
When porting this definition to another proof assistant, care should be taken to ensure that the infinite sum is properly defined and that the functions `c` and `Cx` are correctly represented. Additionally, the `from` function, which likely generates a sequence of natural numbers starting from 1, should be translated correctly. In some systems, the `infsum` function may need to be defined or imported from a library.

---

## BOUNDED_LFUNCTION_PARTIAL_SUMS

### Name of formal statement
BOUNDED_LFUNCTION_PARTIAL_SUMS

### Type of the formal statement
Theorem

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
                DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL])
```

### Informal statement
For all `d` and `c`, if `c` is a Dirichlet character modulo `d` and `c` is not the principal character `chi_0` modulo `d`, then the set of all partial sums of `c` from 1 to any natural number `n` is bounded.

### Informal sketch
* The proof starts by assuming `c` is a Dirichlet character modulo `d` and `c` is not the principal character.
* It then applies the `DIRICHLET_CHARACTER_SUM_MOD` theorem to rewrite the sum of `c` over a range in terms of its periodicity modulo `d`.
* The `BOUNDED_SUBSET` theorem is used to show that the set of partial sums is bounded by exhibiting a bounded set that contains it.
* The bounded set is constructed as the image of the function that maps each `n` to the sum of `c` from 1 to `n`, restricted to the finite set `{0, 1, ..., d}`.
* The proof then simplifies the expression for the bounded set using various properties of finite sets and modular arithmetic.
* Key steps involve recognizing that the set of sums is finite because it is the image of a finite set, and that this finiteness implies boundedness.
* The `ASM_MESON_TAC` tactic is used to automatically prove the final steps, which involve straightforward but tedious manipulations of logical formulas.

### Mathematical insight
This theorem is important because it establishes a fundamental property of Dirichlet characters: their partial sums are bounded when the character is non-principal. This boundedness is crucial in many applications of Dirichlet characters, particularly in analytic number theory. The theorem's proof illustrates how properties of Dirichlet characters, combined with basic principles of modular arithmetic and the logic of bounded sets, lead to significant conclusions about their behavior.

### Dependencies
* `DIRICHLET_CHARACTER_SUM_MOD`
* `BOUNDED_SUBSET`
* `FINITE_IMP_BOUNDED`
* `FINITE_IMAGE`
* `FINITE_NUMSEG`
* `SIMPLE_IMAGE`
* `SUBSET`
* `FORALL_IN_IMAGE`
* `LT_IMP_LE`
* `DIVISION`
* `DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL` 

### Porting notes
When translating this theorem into another proof assistant, special attention should be given to how Dirichlet characters and their properties are defined and used. The proof's reliance on `ASM_MESON_TAC` for the final steps may require manual translation or reproof in the target system, as automated proof tools can vary significantly between systems. Additionally, the handling of modular arithmetic and the representation of bounded sets may differ, requiring careful consideration to ensure that the ported theorem accurately reflects the original statement and proof.

---

## LFUNCTION

### Name of formal statement
LFUNCTION

### Type of the formal statement
Theorem

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
  SIMP_TAC[REAL_LE_INV2; REAL_OF_NUM_LE; REAL_OF_NUM_LT; LE_1; LE_ADD])
```

### Informal statement
For all `d` and `c`, if `c` is a Dirichlet character modulo `d` and `c` is not the principal character `chi_0` modulo `d`, then the series `∑(c(n) / n)` converges to the `L`-function of `c`, where the sum is taken over all positive integers `n`.

### Informal sketch
* The proof starts by assuming `d` and `c` such that `c` is a Dirichlet character modulo `d` and `c` is not the principal character.
* It then applies various simplifications and rewrites to transform the series `∑(c(n) / n)` into a form where its convergence can be established.
* Key steps involve:
  + Using the definition of `Lfunction` (`Lfunction_DEF`) and properties of infinite sums (`SUMS_INFSUM`).
  + Applying the `SERIES_DIRICHLET_COMPLEX` theorem to establish convergence.
  + Utilizing the `BOUNDED_LFUNCTION_PARTIAL_SUMS` property to bound partial sums.
  + Simplifying expressions involving complex numbers and limits (`LIM_INV_N`, `GSYM CX_INV`, `REAL_CX`, `RE_CX`).
  + Applying various real number properties (`REAL_LE_INV2`, `REAL_OF_NUM_LE`, `REAL_OF_NUM_LT`, `LE_1`, `LE_ADD`) to finalize the proof.

### Mathematical insight
This theorem is crucial in number theory as it establishes the convergence of the `L`-series for non-principal Dirichlet characters, which is a fundamental property used in many applications, including the study of prime numbers and the distribution of prime numbers in arithmetic progressions.

### Dependencies
#### Theorems
* `SERIES_DIRICHLET_COMPLEX`
* `BOUNDED_LFUNCTION_PARTIAL_SUMS`
#### Definitions
* `Lfunction_DEF`
* `dirichlet_character`
* `chi_0`
#### Properties
* `SUMS_INFSUM`
* `REAL_LE_INV2`
* `REAL_OF_NUM_LE`
* `REAL_OF_NUM_LT`
* `LE_1`
* `LE_ADD`
* `LIM_INV_N`
* `GSYM CX_INV`
* `REAL_CX`
* `RE_CX`

### Porting notes
When translating this theorem into other proof assistants, special attention should be given to handling the series convergence and the properties of Dirichlet characters. The `SERIES_DIRICHLET_COMPLEX` theorem and the `BOUNDED_LFUNCTION_PARTIAL_SUMS` property might require careful porting due to differences in how these systems handle complex analysis and number theory. Additionally, the automation provided by `REPEAT` and `MATCH_MP_TAC` tactics in HOL Light may need to be manually replicated or adjusted according to the target proof assistant's capabilities.

---

## CNJ_CHI_0

### Name of formal statement
CNJ_CHI_0

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CNJ_CHI_0 = prove
 (`!d n. cnj(chi_0 d n) = chi_0 d n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[chi_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[CNJ_CX])
```

### Informal statement
For all `d` and `n`, the conjugate of `chi_0 d n` is equal to `chi_0 d n`.

### Informal sketch
* The proof starts by generalizing over all possible `d` and `n` using `GEN_TAC`.
* It then rewrites the `chi_0` term using its definition, as indicated by `REWRITE_TAC[chi_0]`.
* The proof proceeds by considering cases, as suggested by `COND_CASES_TAC`.
* Finally, it applies a rewrite rule `CNJ_CX` to simplify the expression, as indicated by `ASM_REWRITE_TAC[CNJ_CX]`, to establish the equality.

### Mathematical insight
This theorem establishes a property of the conjugate of a character `chi_0`, specifically that it is equal to itself. This property is likely important in the context of group theory or representation theory, where characters and their conjugates play a significant role.

### Dependencies
* `chi_0`
* `cnj`
* `CNJ_CX`

### Porting notes
When translating this theorem into another proof assistant, care should be taken to ensure that the `GEN_TAC`, `REWRITE_TAC`, `COND_CASES_TAC`, and `ASM_REWRITE_TAC` tactics are appropriately mirrored. In particular, the handling of binders and automation may differ between systems, and the `CNJ_CX` rewrite rule may need to be redefined or reimplemented.

---

## LFUNCTION_CNJ

### Name of formal statement
LFUNCTION_CNJ

### Type of the formal statement
Theorem

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
  ASM_MESON_TAC[LFUNCTION])
```

### Informal statement
For all `d` and `c`, if `c` is a Dirichlet character modulo `d` and `c` is not the principal character `chi_0` modulo `d`, then the L-function of the conjugate of `c` is equal to the conjugate of the L-function of `c`.

### Informal sketch
* Start by assuming `c` is a Dirichlet character modulo `d` and `c` is not the principal character `chi_0` modulo `d`.
* Use the definition of `Lfunction` to express `Lfunction (\n. cnj(c n))` and `cnj(Lfunction c)` in terms of infinite sums.
* Apply the `INFSUM_UNIQUE` theorem to establish the uniqueness of the L-function.
* Use properties of complex conjugation, such as `CNJ_CX` and `CNJ_DIV`, to simplify the expressions.
* Apply `LFUNCTION` theorem to conclude the equality.

### Mathematical insight
This theorem establishes a relationship between the L-function of a Dirichlet character and its conjugate. The L-function is a fundamental object in number theory, and understanding its properties is crucial for many applications. This theorem provides insight into how the L-function behaves under conjugation, which is an essential operation in number theory.

### Dependencies
* Theorems:
	+ `INFSUM_UNIQUE`
	+ `LFUNCTION`
* Definitions:
	+ `Lfunction`
	+ `dirichlet_character`
	+ `chi_0`
	+ `cnj`

### Porting notes
When porting this theorem to another proof assistant, pay attention to the handling of infinite sums and complex conjugation. The `INFSUM_UNIQUE` theorem may need to be restated or proved in the target system. Additionally, the `LFUNCTION` theorem and the definitions of `Lfunction`, `dirichlet_character`, `chi_0`, and `cnj` will need to be translated or defined in the target system.

---

## LFUNCTION_PARTIAL_SUM

### Name of formal statement
LFUNCTION_PARTIAL_SUM

### Type of the formal statement
Theorem

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
    ASM_SIMP_TAC[ARITH_RULE `1 <= k + 1`; REAL_OF_NUM_ADD]])
```

### Informal statement
For all `d` and `c`, if `c` is a Dirichlet character modulo `d` and `c` is not the principal character `chi_0` modulo `d`, then there exists a positive real number `B` such that for all natural numbers `n` greater than or equal to 1, the norm of the difference between the `L`-function of `c` and the partial sum from 1 to `n` of `c(n)` divided by `n` is less than or equal to `B` divided by `n + 1`.

### Informal sketch
* The proof starts by assuming `c` is a Dirichlet character modulo `d` and `c` is not the principal character `chi_0` modulo `d`.
* It then applies the `SERIES_DIRICHLET_COMPLEX_EXPLICIT` theorem to establish a bound on the partial sums of the series.
* The proof proceeds to simplify and manipulate the expression using various rewrite rules and simplification tactics, including `REWRITE_TAC`, `SIMP_TAC`, and `MATCH_MP_TAC`.
* The `MONO_EXISTS` tactic is used to introduce an existential quantifier for the real number `B`.
* The proof then splits into two main cases, one dealing with the limit of the partial sums and the other with the boundedness of the `L`-function.
* Key HOL Light terms used include `Lfunction`, `vsum`, `Cx`, `inv`, and `norm`.

### Mathematical insight
This theorem provides an explicit bound on the truncation error of the `L`-series of a Dirichlet character, which is crucial in analytic number theory. The `L`-function is a fundamental object in number theory, and understanding its properties is essential for many applications. This theorem gives a quantitative estimate of how well the partial sums of the `L`-series approximate the actual `L`-function.

### Dependencies
* Theorems:
	+ `SERIES_DIRICHLET_COMPLEX_EXPLICIT`
	+ `BOUNDED_LFUNCTION_PARTIAL_SUMS`
	+ `LIM_NORM_UBOUND`
	+ `LIM_CONST`
	+ `LIM_SUB`
	+ `LIM_TRANSFORM`
	+ `LIM_EVENTUALLY`
* Definitions:
	+ `dirichlet_character`
	+ `chi_0`
	+ `Lfunction`
	+ `vsum`
	+ `Cx`
	+ `inv`
	+ `norm`

---

## LFUNCTION_PARTIAL_SUM_STRONG

### Name of formal statement
LFUNCTION_PARTIAL_SUM_STRONG

### Type of the formal statement
Theorem

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
    REAL_ARITH_TAC])
```

### Informal statement
For all `d` and `c`, if `c` is a Dirichlet character modulo `d` and `c` is not the principal character `chi_0` modulo `d`, then there exists a real number `B` greater than `0` such that for all natural numbers `n`, the norm of the difference between the `L`-function of `c` and the partial sum from `1` to `n` of `c(n)` divided by `n` is less than or equal to `B` divided by `n + 1`.

### Informal sketch
* The proof starts by assuming `d` and `c` such that `c` is a Dirichlet character modulo `d` and `c` is not the principal character `chi_0` modulo `d`.
* It then applies the `LFUNCTION_PARTIAL_SUM` theorem to obtain a real number `B` that satisfies certain properties.
* The proof then proceeds by cases on whether `n` is `0` or not. 
* If `n` is `0`, it simplifies the expression using `VSUM_CLAUSES_NUMSEG`, `VECTOR_SUB_RZERO`, and `ARITH`.
* If `n` is not `0`, it uses `LFUNCTION_PARTIAL_SUM` again and applies various real arithmetic properties to derive the desired inequality.
* Key steps involve choosing an appropriate `B` using `EXISTS_TAC` and applying `REAL_ARITH_TAC` for real arithmetic reasoning.

### Mathematical insight
This theorem provides a bound on the difference between the `L`-function of a Dirichlet character and its partial sums, which is crucial in analytic number theory for studying the properties of `L`-functions. The `L`-function is a fundamental object in number theory, and understanding its behavior is essential for many applications, including the distribution of prime numbers.

### Dependencies
* Theorems:
  + `LFUNCTION_PARTIAL_SUM`
  + `REAL_ARITH`
  + `REAL_LE_DIV2_EQ`
* Definitions:
  + `dirichlet_character`
  + `chi_0`
  + `Lfunction`
  + `vsum`
  + `Cx`
* Other:
  + `GEN_TAC`
  + `DISCH_TAC`
  + `MATCH_MP`
  + `EXISTS_TAC`
  + `ASM_SIMP_TAC`
  + `X_GEN_TAC`
  + `ASM_CASES_TAC`
  + `REAL_ARITH_TAC` 

### Porting notes
When translating this theorem into another proof assistant, pay special attention to the handling of real arithmetic and the choice of `B` using `EXISTS_TAC`. The `REAL_ARITH_TAC` tactic in HOL Light is particularly powerful for automating real arithmetic proofs, but its equivalent in other systems may require more manual effort or different automation strategies. Additionally, the `LFUNCTION_PARTIAL_SUM` theorem, which is used as a lemma here, may need to be ported first or proven independently in the target system.

---

## BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT_LEMMA

### Name of formal statement
BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT_LEMMA

### Type of the formal statement
Theorem

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
  MP_TAC(SPECL [`x:num`; `n:num`] DIVISION) THEN ASM_ARITH_TAC)
```

### Informal statement
For all `d` and `c`, if `c` is a Dirichlet character modulo `d` and `c` is not the principal character `chi_0` modulo `d`, then the set of values of the expression `Lfunction(c) * vsum(1..x) (c(n) * Cx(mangoldt n / &n)) - vsum(1..x) (c(n) * Cx(log(&n) / &n))` for all `x` in the set of natural numbers is bounded.

### Informal sketch
* The proof starts by assuming `d` and `c` such that `c` is a Dirichlet character modulo `d` and `c` is not the principal character `chi_0` modulo `d`.
* It then applies various simplifications and transformations to the expression involving `Lfunction(c)` and the sums, using properties of Dirichlet characters, the `mangoldt` function, and complex numbers.
* The proof involves choosing a real number `B` based on the `LFUNCTION_PARTIAL_SUM_STRONG` theorem and then showing that the expression is bounded by `&18 * B`.
* Key steps include applying the triangle inequality for sums, using properties of the `mangoldt` function and the `log` function, and simplifying expressions involving complex numbers.
* The proof also involves case analysis and the use of various theorems and lemmas, such as `DIRICHLET_CHARACTER_MUL`, `VSUM_NORM_TRIANGLE`, and `REAL_LE_TRANS`.

### Mathematical insight
This theorem provides a bound on a specific expression involving Dirichlet L-functions and sums, which is important in number theory. The proof involves a combination of properties of Dirichlet characters, the `mangoldt` function, and complex analysis. The theorem is likely used in further results in number theory, such as the study of the distribution of prime numbers.

### Dependencies
* `dirichlet_character`
* `Lfunction`
* `mangoldt`
* `VSUM_NORM_TRIANGLE`
* `REAL_LE_TRANS`
* `DIRICHLET_CHARACTER_MUL`
* `LFUNCTION_PARTIAL_SUM_STRONG`
* `PSI_BOUND`

### Porting notes
When porting this theorem to another proof assistant, special attention should be paid to the handling of complex numbers, Dirichlet characters, and the `mangoldt` function. The proof involves a number of non-trivial manipulations of these objects, and the corresponding definitions and theorems should be carefully translated. Additionally, the use of tactics such as `REWRITE_TAC` and `MATCH_MP_TAC` may need to be adapted to the target proof assistant's syntax and semantics.

---

## SUMMABLE_CHARACTER_LOG_OVER_N

### Name of formal statement
SUMMABLE_CHARACTER_LOG_OVER_N

### Type of the formal statement
Theorem

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
    ASM_SIMP_TAC[CX_LOG; CX_DIV; LE_1; REAL_OF_NUM_LT]])
```

### Informal statement
For all Dirichlet characters `c` of modulus `d`, such that `c` is not the principal character `chi_0` of `d`, the series `∑[n=1 to ∞] c(n) * (log(n) / n)` is summable.

### Informal sketch
* The proof starts by assuming `c` is a Dirichlet character of modulus `d` and `c` is not equal to `chi_0 d`.
* It then applies the `SERIES_DIRICHLET_COMPLEX` theorem to establish the summability of the series.
* The proof involves showing that the terms of the series satisfy certain conditions, including the boundedness of partial sums, which is achieved using `BOUNDED_LFUNCTION_PARTIAL_SUMS`.
* The decreasing nature of `log(n) / n` is utilized, as expressed by `DECREASING_LOG_OVER_N`, to further support the summability argument.
* The limit of `log(n) / n` as `n` approaches infinity is also considered, leveraging `LIM_LOG_OVER_N` and `LIM_TRANSFORM_EVENTUALLY` to demonstrate that this limit is 0, which is crucial for establishing summability.

### Mathematical insight
This theorem is important because it establishes the summability of a specific series involving Dirichlet characters, which are fundamental objects in number theory. The summability of such series has implications for various applications, including the study of the distribution of prime numbers and the properties of L-functions. The theorem provides a key step in analyzing these series, leveraging properties of Dirichlet characters and the behavior of logarithmic functions.

### Dependencies
* Theorems:
  - `SERIES_DIRICHLET_COMPLEX`
  - `BOUNDED_LFUNCTION_PARTIAL_SUMS`
  - `LIM_LOG_OVER_N`
  - `LIM_TRANSFORM_EVENTUALLY`
* Definitions:
  - `dirichlet_character`
  - `chi_0`
  - `Cx`
  - `log`
  - `summable`

### Porting notes
When translating this theorem into other proof assistants, special attention should be given to the handling of Dirichlet characters, the `SERIES_DIRICHLET_COMPLEX` theorem, and the properties of logarithmic functions. The `LIM_LOG_OVER_N` and `LIM_TRANSFORM_EVENTUALLY` theorems may require careful translation due to differences in how limits and eventually properties are formalized in different systems. Additionally, the use of `MAP_EVERY` and `EXISTS_TAC` tactics might need to be adapted based on the target proof assistant's tactic language and support for automation.

---

## BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT

### Name of formal statement
BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT

### Type of the formal statement
Theorem

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
  X_GEN_TAC `n:num` THEN REPEAT(EXISTS_TAC `n:num`) THEN VECTOR_ARITH_TAC)
```

### Informal statement
For all `d` and `c`, if `c` is a Dirichlet character modulo `d` and `c` is not the principal character `chi_0` modulo `d`, then the set of values of the form `Lfunction(c) * ∑[n=1 to x] (c(n) * mangoldt(n) / n)` for all natural numbers `x` is bounded.

### Informal sketch
* The proof begins by assuming the conditions on `d` and `c`, specifically that `c` is a Dirichlet character modulo `d` and `c` is not the principal character.
* It then applies `BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT_LEMMA` to establish a key property.
* The proof continues by using `SUMMABLE_CHARACTER_LOG_OVER_N` to show summability, which implies the sums are bounded via `SUMMABLE_IMP_SUMS_BOUNDED`.
* Further simplifications and manipulations are applied, including `REWRITE_TAC` for implications and `MATCH_MP_TAC` for applying `BOUNDED_SUBSET` and other rules, to ultimately show the boundedness of the set in question.
* The use of `X_GEN_TAC` and `EXISTS_TAC` suggests the introduction of a generic `n` and the existence of such an `n` to satisfy certain conditions, facilitating the application of `VECTOR_ARITH_TAC` to conclude the proof.

### Mathematical insight
This theorem is significant because it establishes a boundedness property for a specific set related to Dirichlet characters and their L-functions, which is crucial in number theory, particularly in the study of properties of L-functions and their applications in analytic continuation and the distribution of prime numbers.

### Dependencies
- `dirichlet_character`
- `chi_0`
- `Lfunction`
- `mangoldt`
- `BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT_LEMMA`
- `SUMMABLE_CHARACTER_LOG_OVER_N`
- `SUMMABLE_IMP_SUMS_BOUNDED`
- `BOUNDED_SUBSET`
- `SIMPLE_IMAGE`
- `SUBSET`
- `FORALL_IN_IMAGE`
- `IN_UNIV`
- `IN_ELIM_THM`
- `RIGHT_EXISTS_AND_THM`
- `EXISTS_IN_IMAGE`
- `GSYM`
- `CONJ_ASSOC`

---

## BOUNDED_DIRICHLET_MANGOLDT_NONZERO

### Name of formal statement
BOUNDED_DIRICHLET_MANGOLDT_NONZERO

### Type of the formal statement
Theorem

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
  ASM_MESON_TAC[COMPLEX_NORM_NZ; REAL_LT_DIV])
```

### Informal statement
For all `d` and `c`, if `c` is a Dirichlet character modulo `d`, `c` is not the principal character `chi_0` modulo `d`, and the L-function of `c` is not identically zero, then the set of sums from 1 to `x` of `c(n) * mangoldt(n) / n` is bounded for all natural numbers `x`.

### Informal sketch
* The proof begins by assuming the premises: `c` is a Dirichlet character modulo `d`, `c` is not the principal character, and the L-function of `c` is not identically zero.
* It then applies the `BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT` theorem to establish a bound on the sum.
* The proof involves rewriting and simplifying expressions using various theorems and tactics, including `REWRITE_TAC`, `DISCH_THEN`, and `ASM_SIMP_TAC`.
* Key steps involve using properties of Dirichlet characters, L-functions, and the `mangoldt` function to establish the boundedness of the sum.
* The `COMPLEX_NORM_NZ` and `REAL_LT_DIV` theorems are used to reason about complex numbers and real numbers.

### Mathematical insight
This theorem establishes a boundedness property for a specific sum involving Dirichlet characters and the mangoldt function. The result is important in number theory, particularly in the study of L-functions and their properties. The theorem provides a crucial step in understanding the behavior of these functions, which are essential in many number theoretic applications.

### Dependencies
* Theorems:
	+ `BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT`
	+ `COMPLEX_NORM_NZ`
	+ `REAL_LT_DIV`
* Definitions:
	+ `dirichlet_character`
	+ `chi_0`
	+ `Lfunction`
	+ `mangoldt`

### Porting notes
When translating this theorem into other proof assistants, care should be taken to ensure that the properties of Dirichlet characters, L-functions, and the mangoldt function are correctly ported. The `BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT` theorem, in particular, may require special attention due to its role in establishing the boundedness property. Additionally, the use of `REPEAT GEN_TAC` and `DISCH_THEN` tactics may need to be adapted to the target proof assistant's tactic language.

---

## MANGOLDT_LOG_SUM

### Name of formal statement
MANGOLDT_LOG_SUM

### Type of the formal statement
Theorem

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
    COND_CASES_TAC THEN ASM_REWRITE_TAC[LOG_1] THEN REAL_ARITH_TAC])
```

### Informal statement
For all natural numbers `n` greater than or equal to 1, the `mangoldt` function of `n` is equal to the negative of the sum over all divisors `d` of `n` of the product of the `mobius` function of `d` and the natural logarithm of `d`.

### Informal sketch
* The proof starts by applying `MOBIUS_INVERSION` to relate `mangoldt(n)` to a sum involving `mobius` and `log`.
* It then uses `EQ_TRANS` to introduce an intermediate expression involving a sum over divisors `d` of `n`, with terms of the form `mobius(d) * (log(n) - log(d))`.
* The proof proceeds by showing that this intermediate sum is equal to the original sum, using properties of sums, `mobius`, and `log`.
* Key steps involve simplifying expressions using `ASM_SIMP_TAC` and `REAL_ARITH_TAC`, and applying specific properties like `LOG_MANGOLDT_SUM` and `DIVISORSUM_MOBIUS`.
* The `MATCH_MP_TAC` and `COND_CASES_TAC` tactics are used to apply specific rules and handle cases.

### Mathematical insight
This theorem provides a relationship between the `mangoldt` function, which is important in number theory, and a sum involving the `mobius` function and logarithms. The `mangoldt` function is related to the von Mangoldt function, which is used in the study of prime numbers and the distribution of prime numbers. This relationship can be useful in deriving properties of the `mangoldt` function and in applying it to problems in number theory.

### Dependencies
* Theorems:
  + `MOBIUS_INVERSION`
  + `LOG_MANGOLDT_SUM`
  + `DIVISORSUM_MOBIUS`
* Definitions:
  + `mangoldt`
  + `mobius`
  + `log`

### Porting notes
When translating this theorem into another proof assistant, care should be taken to ensure that the properties of the `mangoldt` and `mobius` functions, as well as the `log` function, are correctly defined and applied. The use of `SUM` and `REAL_ARITH_TAC` may require special attention, as the handling of sums and real arithmetic can differ between proof assistants. Additionally, the application of specific tactics like `MATCH_MP_TAC` and `COND_CASES_TAC` may need to be adapted to the target system's tactic language.

---

## BOUNDED_DIRICHLET_MANGOLDT_LEMMA

### Name of formal statement
BOUNDED_DIRICHLET_MANGOLDT_LEMMA

### Type of the formal statement
Theorem

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
    ASM_SIMP_TAC[COMPLEX_MUL_LID; COMPLEX_DIV_1]])
```

### Informal statement
For all `d`, `c`, and `x`, if `c` is a Dirichlet character modulo `d`, `c` is not the principal character `chi_0` modulo `d`, and `x` is greater than or equal to 1, then the following equation holds: `Cx(log(x)) + vsum (1..x) (c(n) * Cx(mangoldt n / n)) = vsum (1..x) (c(n) / Cx(n) * vsum {d | d divides n} (Cx(mobius(d) * log(x / d))))`.

### Informal sketch
* The proof starts by applying `MANGOLDT_LOG_SUM` to simplify the expression involving `mangoldt n`.
* It then applies `COMPLEX_RING` to rearrange terms and `VSUM_SUB` to split the summation.
* The proof continues by applying various simplification tactics, including `CX_NEG`, `CX_DIV`, and `GSYM VSUM_CX`.
* The `MATCH_MP_TAC EQ_TRANS` tactic is used to introduce an intermediate expression, which is then simplified using `VSUM_EQ_NUMSEG` and `AP_TERM_TAC`.
* The proof also involves case analysis on `m = 0` and application of `REAL_ARITH_TAC` to establish the final equality.
* Key steps involve manipulating summations, applying properties of Dirichlet characters, and using the `mobius` function.

### Mathematical insight
This theorem relates the sum of a Dirichlet character `c` applied to numbers up to `x` with the sum of a related expression involving the `mangoldt` function and the `mobius` function. The result provides insight into the properties of Dirichlet characters and their relationship to the distribution of prime numbers.

### Dependencies
* `dirichlet_character`
* `chi_0`
* `mangoldt`
* `mobius`
* `Cx`
* `log`
* `VSUM`
* `COMPLEX_RING`
* `MANGOLDT_LOG_SUM`
* `DIVISORSUM_MOBIUS` 

### Porting notes
When porting this theorem to another proof assistant, pay attention to the handling of complex numbers, Dirichlet characters, and the `mangoldt` and `mobius` functions. The `VSUM` notation may need to be translated to the target system's notation for summation. Additionally, the `MATCH_MP_TAC` and `EXISTS_TAC` tactics may need to be replaced with equivalent constructs in the target system.

---

## SUM_LOG_OVER_X_BOUND

### Name of formal statement
SUM_LOG_OVER_X_BOUND

### Type of the formal statement
Theorem

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
  ASM_SIMP_TAC[REAL_OF_NUM_LE; LE_1; LOG_LE_REFL])
```

### Informal statement
For all `x`, the absolute value of the sum from 1 to `x` of `log(x / n)` divided by `x` is less than or equal to 4.

### Informal sketch
* The proof starts by considering the case when `x` equals 0, handling it separately using `ASM_SIMP_TAC` and `SUM_CLAUSES_NUMSEG`.
* For non-zero `x`, it applies various simplifications and properties of real numbers, logarithms, and summations, including `REAL_LE_LDIV_EQ`, `LOG_POS`, and `SUM_ABS_NUMSEG`.
* The proof then invokes `MATCH_MP_TAC` with `REAL_LE_TRANS` to establish a relationship between the sum of absolute values of logarithms and another expression.
* It further simplifies the sum using `SUM_SUB_NUMSEG` and `GSYM LOG_FACT`, and applies `MATCH_MP_TAC` with `REAL_ARITH` to derive inequalities involving `l`, `x`, and `b`.
* The final steps involve applying `FIRST_ASSUM` with `MATCH_MP LOG_FACT_BOUNDS` and additional `MATCH_MP_TAC` with `REAL_ARITH` to conclude the proof.

### Mathematical insight
This theorem provides a bound on the absolute value of a summation involving logarithms, which is crucial in various mathematical analyses, particularly in number theory and calculus. The statement and its proof highlight the interplay between properties of logarithms, summations, and real numbers, demonstrating how these concepts are used to derive meaningful bounds.

### Dependencies
#### Theorems
* `REAL_LE_TRANS`
* `LOG_FACT_BOUNDS`
* `REAL_ARITH`
#### Definitions
* `SUM_CLAUSES_NUMSEG`
* `REAL_ABS_NUM`
* `LOG_POS`
* `REAL_LE_LDIV_EQ`
* `SUM_ABS_NUMSEG`
* `LOG_FACT`
* `REAL_OF_NUM_LE`
* `LOG_LE_REFL`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to the handling of:
- Quantifiers and binders, as different systems may have distinct ways of expressing and manipulating them.
- Real numbers and their properties, as the proof heavily relies on `REAL_LE_LDIV_EQ`, `REAL_OF_NUM_LT`, and other real number properties.
- Logarithmic functions and their properties, such as `LOG_POS` and `LOG_DIV`.
- Summation notation and its manipulation, as seen with `SUM_CLAUSES_NUMSEG`, `SUM_ABS_NUMSEG`, and `SUM_SUB_NUMSEG`.
- Tactical proofs, as the structure and application of tactics like `MATCH_MP_TAC`, `EXISTS_TAC`, and `ASM_SIMP_TAC` may need to be adapted to the target system's proof scripting language.

---

## BOUNDED_DIRICHLET_MANGOLDT_ZERO

### Name of formal statement
BOUNDED_DIRICHLET_MANGOLDT_ZERO

### Type of the formal statement
Theorem

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
  MP_TAC(SPECL [`x:num`; `n:num`] DIVISION) THEN ASM_ARITH_TAC)
```

### Informal statement
For all `d` and `c` such that `c` is a Dirichlet character modulo `d`, `c` is not the principal character `chi_0`, and the `L`-function of `c` is `Cx(&0)`, it holds that the set `{ vsum(1..x) (\n. c n * Cx(mangoldt n / &n)) + Cx(log(&x)) | x IN (:num) }` is bounded.

### Informal sketch
* The proof starts by assuming the premises: `dirichlet_character d c`, `c` is not equal to `chi_0 d`, and `Lfunction c = Cx(&0)`.
* It then applies various rewriting and simplification steps, including `ONCE_REWRITE_TAC[COMPLEX_ADD_SYM]`, `REPEAT STRIP_TAC`, and `MP_TAC` with `LFUNCTION_PARTIAL_SUM_STRONG`.
* The proof proceeds by choosing a real number `B` and applying `DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC)`.
* It then uses `SIMP_TAC` and `REWRITE_TAC` to simplify the expression and apply properties of `dirichlet_character` and `Lfunction`.
* The proof involves several applications of `MATCH_MP_TAC` with various theorems, including `VSUM_NORM_TRIANGLE`, `REAL_LE_TRANS`, and `SUM_LE_NUMSEG`.
* Key steps include using `EXISTS_TAC `&4 * B`` to establish a bound and applying `X_GEN_TAC `x:num`` to discharge the existential quantifier.
* The proof concludes by applying `ASM_SIMP_TAC` and `ASM_ARITH_TAC` to simplify and establish the final bound.

### Mathematical insight
This theorem establishes a boundedness property for a specific set involving Dirichlet characters and their `L`-functions. The result is important in number theory, particularly in the study of properties of Dirichlet characters and their applications to problems in analytic number theory.

### Dependencies
* Theorems:
	+ `LFUNCTION_PARTIAL_SUM_STRONG`
	+ `BOUNDED_DIRICHLET_MANGOLDT_LEMMA`
	+ `VSUM_NORM_TRIANGLE`
	+ `REAL_LE_TRANS`
	+ `SUM_LE_NUMSEG`
* Definitions:
	+ `dirichlet_character`
	+ `Lfunction`
	+ `mangoldt`
	+ `Cx`
	+ `chi_0`

---

## BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL_LEMMA

### Name of formal statement
BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL_LEMMA

### Type of the formal statement
Theorem

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
       [ASM_ARITH_TAC; SIMP_TAC[EXP; DIVIDES_RMUL; DIVIDES_REFL]]])
```

### Informal statement
For all `d` such that `1 <= d`, the norm of the sum from `1` to `x` of `(chi_0 d n - Cx(&1)) * Cx(mangoldt n / &n)` is less than or equal to the sum over all prime `p` that divides `d` of `log(&p)`.

### Informal sketch
* The proof starts by assuming `1 <= d` and then uses `MATCH_MP_TAC REAL_LE_TRANS` to establish a bound on the norm of a summation involving `chi_0`, `Cx`, and `mangoldt`.
* It then breaks down into cases, using `CONJ_TAC` to separate the reasoning into two main parts: one involving `SUM_LE` and another involving `MATCH_MP_TAC VSUM_NORM_TRIANGLE`.
* Key steps include:
  + Establishing a bound on a sum involving `log(&p)` and `p pow k` using `SUM_SUBSET_SIMPLE` and `REAL_LE_TRANS`.
  + Using `MATCH_MP_TAC SUM_EQ_GENERAL` to reason about the sum over pairs `(p, k)` and applying `SELECT_UNIQUE` to establish uniqueness of certain terms.
  + Employing various simplifications and arithmetic properties, including `REAL_OF_NUM_POW`, `REAL_ABS_DIV`, and `EXP_MONO_LE`.
* The proof involves intricate manipulations of sums, logarithms, and properties of prime numbers, including `PRIME_GE_2`, `PRIME_DIVEXP`, and `COPRIME_PRIMEPOW`.

### Mathematical insight
This theorem provides a bound on a complex expression involving the `mangoldt` function, `chi_0`, and prime numbers, which is crucial in number theory, particularly in the context of the Dirichlet characters and the distribution of prime numbers. The `mangoldt` function is related to the von Mangoldt function, which plays a significant role in analytic number theory.

### Dependencies
* Theorems:
  + `REAL_LE_TRANS`
  + `SUM_LE`
  + `VSUM_NORM_TRIANGLE`
  + `SUM_SUBSET_SIMPLE`
  + `REAL_EQ_IMP_LE`
  + `SUM_EQ_GENERAL`
  + `SELECT_UNIQUE`
* Definitions:
  + `chi_0`
  + `mangoldt`
  + `Cx`
  + `prime`
  + `divides`
  + `coprime`
* Other:
  + Properties of prime numbers (`PRIME_GE_2`, `PRIME_DIVEXP`, `COPRIME_PRIMEPOW`)
  + Arithmetic properties (`REAL_OF_NUM_POW`, `REAL_ABS_DIV`, `EXP_MONO_LE`)

### Porting notes
When translating this theorem into another proof assistant, pay special attention to the handling of:
* The `mangoldt` function and its properties.
* The `chi_0` function and its interaction with `Cx`.
* The use of `SUM_SUBSET_SIMPLE` and `SUM_EQ_GENERAL`, which may require different formulations in other systems.
* The application of `SELECT_UNIQUE`, which might involve different uniqueness principles or proof strategies.
* The various arithmetic properties and simplifications, which could be automated differently or require explicit proof in other systems.

---

## BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL

### Name of formal statement
BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL

### Type of the formal statement
Theorem

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
  MATCH_MP_TAC MERTENS_LEMMA THEN ASM_REWRITE_TAC[])
```

### Informal statement
For all `d` such that `1 <= d`, the set of values `{ vsum(1..x) (\n. chi_0 d n * Cx(mangoldt n / &n)) - Cx(log(&x)) | x IN (:num)}` is bounded.

### Informal sketch
* The proof starts by assuming `1 <= d` and then applies various simplifications and rewrites using `REPEAT STRIP_TAC` and `REWRITE_TAC`.
* It then uses `EXISTS_TAC` to introduce a specific value that will be used to establish the boundedness of the given set.
* The proof proceeds by considering cases, specifically when `x = 0` and when `x` is not equal to `0`, using `ASM_CASES_TAC`.
* For the non-zero `x` case, it applies several mathematical properties and theorems, including `REAL_ARITH`, `NORM_ARITH`, and `MERTENS_LEMMA`, to establish the boundedness of the set.
* Key steps involve using `MATCH_MP_TAC` to apply these theorems and `EXISTS_TAC` to introduce specific values that help in proving the boundedness.

### Mathematical insight
This theorem is related to the properties of the `mangoldt` function and its relation to the `chi_0` function, in the context of Dirichlet series and their analytic properties. The boundedness of the set in question has implications for the behavior of these functions and series, which are crucial in number theory.

### Dependencies
* Theorems:
  + `MERTENS_LEMMA`
  + `BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL_LEMMA`
* Definitions:
  + `chi_0`
  + `mangoldt`
  + `Cx`
  + `vsum`
* Other:
  + `REAL_ARITH`
  + `NORM_ARITH`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles binders, quantifiers, and the application of theorems like `MERTENS_LEMMA`. The use of `EXISTS_TAC` and `MATCH_MP_TAC` may need to be adapted based on the target system's tactics and proof construction mechanisms. Additionally, the representation of complex numbers and the `Cx` function may vary, requiring adjustments to ensure compatibility.

---

## SUM_OF_NUMBERS

### Name of formal statement
SUM_OF_NUMBERS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SUM_OF_NUMBERS = prove
 (`!n. nsum(0..n) (\i. i) = (n * (n + 1)) DIV 2`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THEN ARITH_TAC);;
```

### Informal statement
For all natural numbers `n`, the sum of the numbers from 0 to `n` (inclusive) is equal to `n` times `n + 1` divided by 2.

### Informal sketch
* The proof proceeds by induction on `n`.
* The base case is likely trivial and is not explicitly mentioned.
* The inductive step involves rewriting the sum using `NSUM_CLAUSES_NUMSEG` and then applying arithmetic reasoning (`ARITH_TAC`) to establish the equality.
* The use of `INDUCT_TAC` suggests a straightforward inductive argument, while `ASM_REWRITE_TAC` applies specific rewrite rules to simplify the expression.

### Mathematical insight
This theorem formalizes the well-known formula for the sum of an arithmetic series, which is a fundamental result in mathematics. The formula is used extensively in various mathematical and computational contexts, and its formal proof provides a foundation for more complex results.

### Dependencies
* `NSUM_CLAUSES_NUMSEG`: a definition or theorem providing rewrite rules for `nsum` over a numeric segment.
* Basic arithmetic properties and rules, implicitly used by `ARITH_TAC`.

### Porting notes
When translating this theorem into other proof assistants, special attention should be paid to the handling of binders (in this case, the universal quantifier `!n`) and the arithmetic reasoning steps. The `INDUCT_TAC` and `ASM_REWRITE_TAC` tactics may have direct analogs in other systems, but the specific rewrite rules and arithmetic decision procedures may differ. Additionally, the representation of the `nsum` function and its properties may require careful consideration to ensure compatibility with the target proof assistant.

---

## PRODUCT_POW_NSUM

### Name of formal statement
PRODUCT_POW_NSUM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PRODUCT_POW_NSUM = prove
 (`!s. FINITE s ==> product s (\i. z pow (f i)) = z pow (nsum s f)`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; NSUM_CLAUSES; real_pow; REAL_POW_ADD])
```

### Informal statement
For all sets `s`, if `s` is finite, then the product over `s` of `z` raised to the power of `f(i)` equals `z` raised to the power of the natural sum of `f` over `s`.

### Informal sketch
* The proof proceeds by induction on the finiteness of `s`, using `FINITE_INDUCT_STRONG`.
* The base case and inductive step involve simplifying expressions using `PRODUCT_CLAUSES`, `NSUM_CLAUSES`, `real_pow`, and `REAL_POW_ADD`.
* The key insight is to apply these simplifications to transform the product and sum expressions into a form where the equality becomes apparent.
* The use of `MATCH_MP_TAC` and `SIMP_TAC` suggests that the proof involves strategic application of rules to simplify the expressions and reach the desired conclusion.

### Mathematical insight
This theorem provides a fundamental property relating products and sums of exponentiated terms, which is crucial in various mathematical contexts, such as algebra and analysis. The theorem's importance lies in its ability to simplify complex expressions involving products and sums, making it a useful tool in proofs involving these constructs.

### Dependencies
#### Theorems and Definitions
* `FINITE_INDUCT_STRONG`
* `PRODUCT_CLAUSES`
* `NSUM_CLAUSES`
* `real_pow`
* `REAL_POW_ADD`

### Porting notes
When translating this theorem into other proof assistants, special attention should be paid to the handling of finite sets, products, and sums, as well as the properties of exponentiation. The `FINITE_INDUCT_STRONG` tactic may need to be replaced with an equivalent induction principle in the target system. Additionally, the `SIMP_TAC` and `MATCH_MP_TAC` tactics may require manual replacement with corresponding simplification and matching mechanisms in the target system.

---

## PRODUCT_SPECIAL

### Name of formal statement
PRODUCT_SPECIAL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PRODUCT_SPECIAL = prove
 (`!z i. product (0..n) (\i. z pow i) = z pow ((n * (n + 1)) DIV 2)`,
  SIMP_TAC[PRODUCT_POW_NSUM; FINITE_NUMSEG; SUM_OF_NUMBERS])
```

### Informal statement
For all `z` and for all `i`, the product from `0` to `n` of `z` raised to the power of `i` is equal to `z` raised to the power of the integer division of `n` times `n + 1` by `2`.

### Informal sketch
* The theorem `PRODUCT_SPECIAL` involves proving an equality between a product and an exponential expression.
* The proof strategy employs `SIMP_TAC` with specific theorems `PRODUCT_POW_NSUM`, `FINITE_NUMSEG`, and `SUM_OF_NUMBERS` to simplify the product expression into the desired exponential form.
* Key steps likely involve recognizing the product as a geometric series, applying properties of exponentiation, and using the formula for the sum of the first `n` natural numbers.

### Mathematical insight
This theorem provides a compact formula for calculating the product of powers of a number `z` from `0` to `n`, which is equivalent to `z` raised to the power of the sum of the first `n` natural numbers. This is a fundamental property in algebra and arithmetic, useful in various mathematical derivations and proofs.

### Dependencies
* Theorems:
  - `PRODUCT_POW_NSUM`
  - `FINITE_NUMSEG`
  - `SUM_OF_NUMBERS`

### Porting notes
When translating this theorem into another proof assistant like Lean, Coq, or Isabelle, pay attention to how each system handles binder notation (e.g., `\i. z pow i`) and automation tactics similar to `SIMP_TAC`. Ensure that the target system's libraries include or can easily derive the necessary theorems `PRODUCT_POW_NSUM`, `FINITE_NUMSEG`, and `SUM_OF_NUMBERS`, or their equivalents.

---

## AGM_SPECIAL

### Name of formal statement
AGM_SPECIAL

### Type of the formal statement
Theorem

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
For all non-negative real numbers $t$ and for all natural numbers $n$, if $0 \leq t$, then $(n + 1)^2 \cdot t^n \leq \left(\sum_{k=0}^{n} t^k\right)^2$.

### Informal sketch
* The proof starts by applying the `AGM` theorem with specific instantiations to establish a key inequality.
* It then simplifies the expression using various `REWRITE_TAC` rules to transform the sum and product terms.
* The proof involves substituting and rearranging terms to set up for the application of `REAL_POW_LE2` and its reverse, leveraging properties of even numbers and arithmetic.
* The use of `SUBGOAL_THEN` and `DISCH_THEN` tactics indicates a strategic approach to handling subgoals and discharging assumptions to reach the final inequality.
* Key steps involve recognizing the relationship between the sum of powers of $t$ and the expression $(n + 1)^2 \cdot t^n$, utilizing properties of real numbers and inequalities.

### Mathematical insight
This theorem provides a specific instance of an inequality that relates the sum of powers of a non-negative real number $t$ to an expression involving $n$ and $t^n$. The inequality is significant because it offers a bound on the growth of the sum of powers of $t$ in terms of $n$ and $t^n$, which can be useful in various mathematical analyses, especially those involving series and sequences.

### Dependencies
* Theorems:
  + `AGM`
  + `REAL_POW_LE`
  + `REAL_POW_LE2`
  + `REAL_POW_LE2_REV`
* Definitions:
  + `SUM`
  + `PRODUCT`
  + `REAL_POW`
* Axioms and Rules:
  + `ARITH_RULE`
  + `EVEN_ADD`
  + `EVEN_MULT`
  + `REAL_ARITH`

### Porting notes
When translating this theorem into another proof assistant, pay special attention to the handling of real numbers, inequalities, and the `SUM` and `PRODUCT` functions. The use of `REWRITE_TAC` and `SUBGOAL_THEN`/`DISCH_THEN` tactics may need to be adapted based on the target system's tactic language and support for automation. Additionally, ensure that the `AGM` theorem and other dependencies are properly ported or have equivalents in the target system.

---

## DIVISORSUM_PRIMEPOW

### Name of formal statement
DIVISORSUM_PRIMEPOW

### Type of the formal statement
Theorem

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
  ASM_MESON_TAC[PRIME_0; PRIME_1])
```

### Informal statement
For all functions `f`, prime numbers `p`, and natural numbers `k`, if `p` is prime, then the sum of `c(m)` for all `m` that divide `p` raised to the power of `k` is equal to the sum from `0` to `k` of `c(p` raised to the power of `i)`.

### Informal sketch
* The proof starts by assuming `p` is a prime number and `k` is a natural number.
* It then applies various simplifications and rewrites using `DIVIDES_PRIMEPOW`, `SET_RULE`, and `GSYM o_DEF` to transform the sum over divisors into a sum over powers of `p`.
* The `SUM_IMAGE` theorem is used to equate the sum over the image of a function with the sum over the domain.
* Further simplifications using `IN_ELIM_THM`, `EQ_EXP`, and `FINITE_NUMSEG_LE` are applied to reach the final form of the equation.
* The proof concludes by using `ASM_MESON_TAC` with `PRIME_0` and `PRIME_1` to establish the desired equality.

### Mathematical insight
This theorem provides a formula for the sum of a function `c` applied to the divisors of a prime power `p` raised to the power of `k`. The key idea is to exploit the properties of prime numbers and the structure of the divisors of a prime power to simplify the sum into a more manageable form. This result is likely useful in number theoretic applications where sums over divisors are common.

### Dependencies
* Theorems:
  + `DIVIDES_PRIMEPOW`
  + `SUM_IMAGE`
  + `IN_ELIM_THM`
  + `EQ_EXP`
  + `FINITE_NUMSEG_LE`
  + `PRIME_0`
  + `PRIME_1`
* Definitions:
  + `prime`
  + `divides`
  + `sum`
  + `IMAGE`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of binders and the representation of the sum over divisors. The use of `SUM_IMAGE` and `IMAGE` may require careful consideration of the underlying set theory and the properties of functions. Additionally, the `ASM_MESON_TAC` and `GEN_REWRITE_TAC` tactics may need to be replaced with equivalent tactics or strategies in the target proof assistant.

---

## DIVISORVSUM_PRIMEPOW

### Name of formal statement
DIVISORVSUM_PRIMEPOW

### Type of the formal statement
Theorem

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
  ASM_MESON_TAC[PRIME_0; PRIME_1])
```

### Informal statement
For all functions `f`, prime numbers `p`, and natural numbers `k`, if `p` is prime, then the sum of `c` over all divisors `m` of `p` raised to the power of `k` is equal to the sum from `0` to `k` of `c` applied to `p` raised to the power of `i`.

### Informal sketch
* The proof starts by assuming `p` is a prime number and `k` is a natural number.
* It then applies various simplification and rewriting rules, including `STRIP_TAC`, `ASM_SIMP_TAC`, and `GEN_REWRITE_TAC`, to transform the statement into a more manageable form.
* The `VSUM_IMAGE` theorem is used to equate the sum over divisors with a sum over a finite segment of natural numbers.
* Further simplifications are applied using `ASM_SIMP_TAC` and `ASM_MESON_TAC`, leveraging properties of prime numbers, divisibility, and exponentiation.
* Key HOL Light terms involved include `DIVIDES_PRIMEPOW`, `SET_RULE`, `GSYM`, `o_DEF`, `NUMSEG_LE`, `VSUM_IMAGE`, `IN_ELIM_THM`, `EQ_EXP`, `FINITE_NUMSEG_LE`, `PRIME_0`, and `PRIME_1`.

### Mathematical insight
This theorem relates the sum of a function `c` over divisors of a prime power to a simpler sum over powers of the prime, exploiting properties of prime numbers and divisibility. It is a useful result in number theory, providing a way to simplify computations involving divisors of prime powers.

### Dependencies
* Theorems:
  + `DIVIDES_PRIMEPOW`
  + `VSUM_IMAGE`
  + `IN_ELIM_THM`
  + `EQ_EXP`
  + `FINITE_NUMSEG_LE`
  + `PRIME_0`
  + `PRIME_1`
* Definitions:
  + `prime`
  + `divides`
  + `vsum`
  + `EXP`
* Rules:
  + `SET_RULE`
  + `GSYM`
  + `o_DEF`
  + `NUMSEG_LE`

---

## DIRICHLET_CHARACTER_DIVISORSUM_EQ_1

### Name of formal statement
DIRICHLET_CHARACTER_DIVISORSUM_EQ_1

### Type of the formal statement
Theorem

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
  ASM_MESON_TAC[COPRIME_SYM; PRIME_COPRIME_EQ])
```

### Informal statement
For all `d`, `c`, `p`, and `k`, if `dirichlet_character d c` holds, `p` is prime, and `p` divides `d`, then the sum of `c` over all divisors `m` of `p` raised to the power of `k` equals 1.

### Informal sketch
* The proof starts by assuming the premises: `dirichlet_character d c`, `prime p`, and `p divides d`.
* It then applies `EQ_TRANS` to introduce an intermediate step in the equality proof, involving the sum of `c` over a singleton set.
* The proof proceeds by showing that this singleton sum equals 1, using `DIRICHLET_CHARACTER_EQ_1`.
* Next, it applies `VSUM_SUPERSET` to extend the sum to all divisors of `p` raised to the power of `k`.
* The proof then simplifies using various properties of divisibility, primality, and coprimality, including `DIVIDES_PRIMEPOW`, `COPRIME_SYM`, and `PRIME_COPRIME_EQ`.
* It also uses `ASM_CASES_TAC` to handle the case when `i = 0` separately.
* The final steps involve simplifying the expression using `COMPLEX_VEC_0` and applying `DIRICHLET_CHARACTER_EQ_0` to reach the conclusion.

### Mathematical insight
This theorem provides a key property of Dirichlet characters, which are crucial in number theory. The statement relates the character's value to the sum of its values over divisors of a prime power, showcasing a fundamental aspect of how these characters interact with prime numbers and their powers.

### Dependencies
#### Theorems
* `DIRICHLET_CHARACTER_EQ_1`
* `EQ_TRANS`
* `VSUM_SUPERSET`
* `DIRICHLET_CHARACTER_EQ_0`
#### Definitions
* `dirichlet_character`
* `prime`
* `divides`
* `vsum`
* `Cx`
#### Other
* `COMPLEX_VEC_0`
* `COPRIME_SYM`
* `PRIME_COPRIME_EQ`
* `DIVIDES_PRIMEPOW`

---

## DIRICHLET_CHARACTER_REAL_CASES

### Name of formal statement
DIRICHLET_CHARACTER_REAL_CASES

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DIRICHLET_CHARACTER_REAL_CASES = prove
 (`!d c. dirichlet_character d c /\ (!n. real(c n))
         ==> !n. c n = --Cx(&1) \/ c n = Cx(&0) \/ c n = Cx(&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP DIRICHLET_CHARACTER_NORM) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[REAL_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` SUBST1_TAC) THEN
  REWRITE_TAC[COMPLEX_NORM_CX; GSYM CX_NEG; CX_INJ] THEN REAL_ARITH_TAC)
```

### Informal statement
For all `d` and `c`, if `c` is a Dirichlet character modulo `d` and for all natural numbers `n`, `c(n)` is real, then for all `n`, `c(n)` is equal to either `1`, `0`, or `-1`.

### Informal sketch
* Start with the assumption that `c` is a Dirichlet character modulo `d` and `c(n)` is real for all `n`.
* Apply the `DIRICHLET_CHARACTER_NORM` theorem to `c` and `n` to derive properties of `c(n)`.
* Use the `REAL_EXISTS` theorem to introduce a real number `t` such that `c(n) = t`.
* Substitute `t` into the expression for `c(n)` and simplify using `COMPLEX_NORM_CX`, `GSYM CX_NEG`, and `CX_INJ`.
* Apply `REAL_ARITH_TAC` to conclude that `c(n)` must be `1`, `0`, or `-1`.

### Mathematical insight
This theorem provides a crucial characterization of Dirichlet characters with real values, showing that they can only take on the values `1`, `0`, or `-1`. This is a fundamental property in number theory, particularly in the study of Dirichlet characters and their applications to analytic continuation and the distribution of prime numbers.

### Dependencies
* `DIRICHLET_CHARACTER_NORM`
* `REAL_EXISTS`
* `COMPLEX_NORM_CX`
* `GSYM CX_NEG`
* `CX_INJ`

### Porting notes
When translating this theorem to another proof assistant, pay close attention to the handling of real and complex numbers, as well as the properties of Dirichlet characters. The `REAL_ARITH_TAC` tactic may need to be replaced with a similar tactic or a manual proof step, depending on the target system's capabilities. Additionally, the `DIRICHLET_CHARACTER_NORM` theorem and other dependencies may need to be ported or re-proven in the target system.

---

## DIRICHLET_CHARACTER_DIVISORSUM_PRIMEPOW_POS

### Name of formal statement
DIRICHLET_CHARACTER_DIVISORSUM_PRIMEPOW_POS

### Type of the formal statement
Theorem

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
  REAL_ARITH_TAC)
```

### Informal statement
For all `d`, `c`, `p`, and `k`, if `c` is a Dirichlet character modulo `d`, `c(n)` is real for all `n`, and `p` is prime, then the real part of the sum of `c(m)` over all `m` that divide `p` to the power of `k` is non-negative.

### Informal sketch
* The proof starts by assuming the premises: `dirichlet_character d c`, `!n. real(c n)`, and `prime p`.
* It then applies various simplification tactics, including `ASM_SIMP_TAC` with `RE_VSUM`, `FINITE_DIVISORS`, `EXP_EQ_0`, and `PRIME_IMP_NZ`, to establish a base case.
* The `FIRST_ASSUM` and `SIMP_TAC` with `MATCH_MP DIRICHLET_CHARACTER_POW` are used to apply the `DIRICHLET_CHARACTER_POW` theorem.
* The proof then proceeds by cases, using `MP_TAC` with `DIRICHLET_CHARACTER_REAL_CASES`, and further simplifications with `ASM_REWRITE_TAC` and `REAL_ARITH_TAC`.
* The `INDUCT_TAC` is used for an inductive step, considering the parity of `k` and applying `MATCH_MP_TAC` with a real arithmetic statement.
* The `COND_CASES_TAC` and subsequent `ASM_REWRITE_TAC` steps handle different cases based on the properties of complex numbers and the `RE_CX` function.

### Mathematical insight
This theorem provides a property of Dirichlet characters, specifically regarding the non-negativity of the real part of a sum of character values over divisors of a prime power. This is likely used in the context of number theory, particularly in the study of Dirichlet series and their applications.

### Dependencies
* Theorems:
	+ `DIRICHLET_CHARACTER_POW`
	+ `DIRICHLET_CHARACTER_REAL_CASES`
	+ `RE_VSUM`
	+ `FINITE_DIVISORS`
	+ `EXP_EQ_0`
	+ `PRIME_IMP_NZ`
	+ `REAL_ARITH`
* Definitions:
	+ `dirichlet_character`
	+ `real`
	+ `prime`
	+ `vsum`
	+ `divides`
	+ `EXP`
	+ `RE_CX`
	+ `complex_pow`
	+ `SUM_POS_LE_NUMSEG`
	+ `REAL_POW_LE`
	+ `REAL_POS`

---

## DIRICHLET_CHARACTER_DIVISORSUM_POS

### Name of formal statement
DIRICHLET_CHARACTER_DIVISORSUM_POS

### Type of the formal statement
Theorem

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
               ARITH_RULE `1 < n ==> ~(n = 0)`; REAL_LE_MUL])
```

### Informal statement
For all `d`, `c`, and `n`, if `c` is a Dirichlet character modulo `d`, `c(n)` is real for all `n`, and `n` is not equal to 0, then the real part of the sum of `c(m)` over all `m` that divide `n` is greater than or equal to 0.

### Informal sketch
* The proof starts by considering two cases for `n`: `n = 1` and `n > 1`.
* For `n = 1`, it simplifies the sum to a single term `c(1)`, which is 1, hence the real part is 1, satisfying the inequality.
* For `n > 1`, it applies induction using `INDUCT_COPRIME_STRONG` to consider the cases where `n` is a product of two coprime numbers `a` and `b`.
* It then uses the `REAL_MULTIPLICATIVE_DIVISORSUM` property to express the sum over divisors of `n` in terms of sums over divisors of `a` and `b`.
* The proof leverages properties of Dirichlet characters, such as `DIRICHLET_CHARACTER_MUL`, to simplify expressions and establish the non-negativity of the real part of the sum.
* Key steps involve recognizing the multiplicative nature of `c` over coprime numbers and applying the `REAL_LE_MUL` rule to conclude the inequality.

### Mathematical insight
This theorem provides a crucial property of Dirichlet characters, which are essential in number theory, particularly in the study of Dirichlet series and L-functions. The statement ensures that for any non-zero `n`, the real part of the sum of the Dirichlet character `c` applied to the divisors of `n` is non-negative. This has implications for the analytic properties of L-functions associated with these characters.

### Dependencies
#### Theorems
* `DIRICHLET_CHARACTER_EQ_1`
* `REAL_MULTIPLICATIVE_DIVISORSUM`
* `DIRICHLET_CHARACTER_DIVISORSUM_PRIMEPOW_POS`
* `INDUCT_COPRIME_STRONG`
#### Definitions
* `dirichlet_character`
* `real`
* `Re`
* `vsum`

---

## lemma

### Name of formal statement
lemma

### Type of the formal statement
Theorem

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
  SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LE_SQUARE])
```

### Informal statement
For all real numbers `x` and natural numbers `n`, if `0` is less than or equal to `x` and `x` is less than or equal to `1`, then `1 - n * x` is less than or equal to `(1 - x)` raised to the power of `n`.

### Informal sketch
* The proof starts with a `REWRITE_TAC` using `RIGHT_FORALL_IMP_THM` to set up the implication, followed by `GEN_TAC` and `DISCH_TAC` to manage the assumptions.
* It then proceeds with `INDUCT_TAC` for induction, and `REWRITE_TAC[real_pow]` to expand the power term, handling the base case with `REAL_ARITH_TAC`.
* The proof continues by applying `MATCH_MP_TAC REAL_LE_TRANS` to establish a transitive inequality, introducing an intermediate term `(&1 - x) * (&1 - &n * x)` via `EXISTS_TAC`.
* Key simplifications are made using `ASM_SIMP_TAC` with various real arithmetic properties, and further application of `MATCH_MP_TAC` with a real arithmetic statement to derive the final inequality.
* The `REAL_ARITH` and `SIMP_TAC` tactics are crucial for manipulating real number inequalities and simplifying expressions.

### Mathematical insight
This theorem provides an inequality involving a power term, which can be useful in various real analysis contexts, such as bounding functions or proving convergence. The condition `0 <= x <= 1` restricts the domain, making the inequality applicable in specific scenarios like probability or when dealing with normalized values.

### Dependencies
#### Theorems
* `RIGHT_FORALL_IMP_THM`
* `REAL_LE_TRANS`
* `REAL_ARITH`
#### Definitions
* `real_pow`

### Porting notes
When translating this into another proof assistant, pay attention to how real numbers and their arithmetic are handled, as well as the specifics of the induction and transitive inequality tactics (`INDUCT_TAC`, `MATCH_MP_TAC REAL_LE_TRANS`). The use of `REAL_ARITH_TAC` and `SIMP_TAC` with specific properties may need to be adapted based on the target system's capabilities for automated reasoning about real numbers.

---

## LFUNCTION_NONZERO_REAL

### LFUNCTION_NONZERO_REAL
- This is a theorem.

### Type of the formal statement
Theorem.

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
For all `d` and `c`, if `c` is a Dirichlet character modulo `d` and `c` is not the principal character modulo `d`, and for all `n`, `c(n)` is real, then the `L`-function of `c` is not equal to the constant function `Cx(&0)`.

### Informal sketch
The proof of `LFUNCTION_NONZERO_REAL` involves several key steps:
* It first uses the `DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL` theorem to establish that `c` is non-trivial.
* Then, it proves that the series `∑[c(n) * z^n / (1 - z^n)]` is summable for `|z| < 1`.
* The proof then proceeds by assuming that the `L`-function of `c` is equal to `Cx(&0)`, and derives a contradiction by showing that this assumption implies the set of values of the `L`-function on the unit disk is unbounded.
* To derive this contradiction, the proof uses properties of Dirichlet characters, including the fact that the sum of `c(d)` over divisors `d` of `n` is equal to `1` if `n` is a power of `p`, and `0` otherwise.
* The proof also uses results on the boundedness of partial sums of the `L`-function, as well as properties of limits and summability.

### Mathematical insight
The `LFUNCTION_NONZERO_REAL` theorem provides insight into the properties of `L`-functions associated with Dirichlet characters. Specifically, it shows that the `L`-function of a non-principal Dirichlet character is not identically zero, which is an important property in number theory.

### Dependencies
* `DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL`
* `BOUNDED_LFUNCTION_PARTIAL_SUMS`
* `DIRICHLET_CHARACTER_DIVISORSUM_POS`
* `DIRICHLET_CHARACTER_DIVISORSUM_EQ_1`
* `REAL_ARCH_POW_INV`
* `REAL_ARCH_SIMPLE`
* `PRIME_FACTOR`
* `SUMMABLE_FROM_ELSEWHERE`
* `SUMMABLE_EQ`
* `SERIES_COMPARISON_COMPLEX`
* `SERIES_SUB`
* `LIM_TRANSFORM`
* `LIM_NULL_COMPARISON_COMPLEX`
* `LIM_NULL_COMPLEX_LMUL`
* `REAL_LE_INV2`
* `REAL_POW_MONO_INV`
* `REAL_POW_LE2_REV`
* `AGM_SPECIAL`
* `REAL_LE_MUL2`

---

## BOUNDED_DIFF_LOGMUL

### Name of formal statement
BOUNDED_DIFF_LOGMUL

### Type of the formal statement
Theorem

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
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT]])
```

### Informal statement
For all functions `f` and complex numbers `a`, if the set `{f(x) - Cx(log(x)) * a | x ∈ ℕ}` is bounded and for all `x`, the real part of `f(x)` is non-negative, then the real part of `a` is non-negative.

### Informal sketch
* The proof starts by assuming the set `{f(x) - Cx(log(x)) * a | x ∈ ℕ}` is bounded, which implies the existence of a real number `B` such that for all `x`, `|f(x) - Cx(log(x)) * a|` is less than or equal to `B`.
* It then uses the `REAL_ARCH_SIMPLE` theorem to find a natural number `n` such that `exp((B + 1) / -Re(a))` is less than `n`.
* The proof proceeds by showing that `|Re(f(n) - Cx(log(n)) * a)|` is less than or equal to `B`, using the `COMPLEX_NORM_GE_RE_IM` and `REAL_LE_TRANS` theorems.
* It then applies the `REAL_ARITH` theorem to establish a relationship between `B`, `f(n)`, and `a`.
* The proof concludes by using the `LOG_MONO_LE_IMP` theorem to show that `Re(a)` is non-negative.

### Mathematical insight
This theorem provides a condition under which the real part of a complex number `a` is guaranteed to be non-negative, based on the boundedness of a set involving a function `f` and the logarithmic function. The result has implications for the study of non-vanishing characters, particularly in number theory.

### Dependencies
* Theorems:
  + `REAL_ARCH_SIMPLE`
  + `COMPLEX_NORM_GE_RE_IM`
  + `REAL_LE_TRANS`
  + `REAL_ARITH`
  + `LOG_MONO_LE_IMP`
* Definitions:
  + `BOUNDED_POS`
  + `SIMPLE_IMAGE`
  + `FORALL_IN_IMAGE`
  + `IN_UNIV`
  + `Cx`
  + `log`
  + `exp`
  + `Re` 

### Porting notes
When translating this theorem into other proof assistants, special attention should be paid to the handling of complex numbers, logarithmic functions, and the `REAL_ARCH_SIMPLE` theorem, which may have different implementations or requirements in other systems. Additionally, the use of `MATCH_MP_TAC` and `ASM_MESON_TAC` tactics may need to be adapted to the target proof assistant's tactic language.

---

## LFUNCTION_NONZERO_NONPRINCIPAL

### Name of formal statement
LFUNCTION_NONZERO_NONPRINCIPAL

### Type of the formal statement
Theorem

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
  ASM_SIMP_TAC[CNJ_EQ_CX] THEN REAL_ARITH_TAC)
```

### Informal statement
For all `d` and `c`, if `c` is a Dirichlet character modulo `d` and `c` is not the principal character `chi_0`, then the L-function of `c` is not equal to `Cx(&0)`.

### Informal sketch
* The proof starts by considering the case when `d = 0` and uses the `DIRICHLET_CHARACTER_0` theorem to handle this case.
* It then uses the `BOUNDED_SUMS_IMAGES` theorem to establish a bound on a sum involving the Dirichlet characters.
* The proof proceeds by considering cases based on whether `c` is the principal character `chi_0` and whether the L-function of `c` is equal to `Cx(&0)`.
* It uses various properties of Dirichlet characters, such as `BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL` and `BOUNDED_DIRICHLET_MANGOLDT_NONZERO`, to establish the desired result.
* The proof also uses the `LFUNCTION_CNJ` theorem to relate the L-function of `c` to the L-function of its conjugate.
* The final steps of the proof involve using real arithmetic properties, such as `REAL_LE_MUL` and `REAL_ARITH`, to establish the desired inequality.

### Mathematical insight
This theorem provides a key property of L-functions of Dirichlet characters, namely that they are not equal to `Cx(&0)` for non-principal characters. This property is important in number theory, particularly in the study of Dirichlet series and their applications to problems in analytic number theory.

### Dependencies
* Theorems:
	+ `DIRICHLET_CHARACTER_0`
	+ `BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL`
	+ `BOUNDED_DIRICHLET_MANGOLDT_NONZERO`
	+ `LFUNCTION_CNJ`
	+ `REAL_LE_MUL`
	+ `REAL_ARITH`
* Definitions:
	+ `dirichlet_character`
	+ `chi_0`
	+ `Lfunction`
	+ `Cx`
	+ `mangoldt`
	+ `cnj`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the properties of Dirichlet characters and L-functions are properly defined and used. In particular, the `BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL` and `BOUNDED_DIRICHLET_MANGOLDT_NONZERO` theorems may require special attention, as they involve subtle properties of Dirichlet characters. Additionally, the use of real arithmetic properties, such as `REAL_LE_MUL` and `REAL_ARITH`, may need to be adapted to the specific proof assistant being used.

---

## BOUNDED_DIRICHLET_MANGOLDT_NONPRINCIPAL

### Name of formal statement
BOUNDED_DIRICHLET_MANGOLDT_NONPRINCIPAL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let BOUNDED_DIRICHLET_MANGOLDT_NONPRINCIPAL = prove
 (`!d c.
      dirichlet_character d c /\ ~(c = chi_0 d)
      ==> bounded { vsum(1..x) (\n. c n * Cx(mangoldt n / &n)) | x IN (:num)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BOUNDED_DIRICHLET_MANGOLDT_NONZERO THEN
  EXISTS_TAC `d:num` THEN
  ASM_MESON_TAC[LFUNCTION_NONZERO_NONPRINCIPAL])
```

### Informal statement
For all `d` and `c`, if `c` is a Dirichlet character modulo `d` and `c` is not the principal character `chi_0` modulo `d`, then the set of sums from 1 to `x` of `c(n) * Cx(mangoldt(n) / n)` for all natural numbers `x` is bounded.

### Informal sketch
* The proof starts by assuming the existence of a Dirichlet character `c` modulo `d` that is not the principal character `chi_0`.
* It then uses the `BOUNDED_DIRICHLET_MANGOLDT_NONZERO` theorem to establish a bound for the sum of `c(n) * Cx(mangoldt(n) / n)` over all natural numbers `n` up to `x`.
* The `EXISTS_TAC` tactic is used to introduce the modulus `d` as a witness, which is necessary for applying the `BOUNDED_DIRICHLET_MANGOLDT_NONZERO` theorem.
* The `ASM_MESON_TAC` tactic is then used to discharge the remaining proof obligations, using the `LFUNCTION_NONZERO_NONPRINCIPAL` property to establish that the character `c` is indeed non-principal.

### Mathematical insight
This theorem establishes a boundedness result for a specific sum involving Dirichlet characters and the Mangoldt function. The result is important because it provides a foundation for further analysis of the properties of Dirichlet characters and their relationships to other number-theoretic functions. The use of the `BOUNDED_DIRICHLET_MANGOLDT_NONZERO` theorem and the `LFUNCTION_NONZERO_NONPRINCIPAL` property highlights the connection between the boundedness of this sum and the non-principal nature of the Dirichlet character.

### Dependencies
* Theorems:
	+ `BOUNDED_DIRICHLET_MANGOLDT_NONZERO`
* Definitions:
	+ `dirichlet_character`
	+ `chi_0`
	+ `mangoldt`
	+ `Cx`
* Properties:
	+ `LFUNCTION_NONZERO_NONPRINCIPAL`

### Porting notes
When translating this theorem into other proof assistants, care should be taken to ensure that the Dirichlet character and Mangoldt function are defined and handled correctly. Additionally, the `BOUNDED_DIRICHLET_MANGOLDT_NONZERO` theorem and the `LFUNCTION_NONZERO_NONPRINCIPAL` property may need to be ported or re-proven in the target system. The use of `EXISTS_TAC` and `ASM_MESON_TAC` tactics may also require special attention, as their behavior may differ between proof assistants.

---

## BOUNDED_SUM_OVER_DIRICHLET_CHARACTERS

### Name of formal statement
BOUNDED_SUM_OVER_DIRICHLET_CHARACTERS

### Type of the formal statement
Theorem

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
    REAL_ARITH_TAC])
```

### Informal statement
For all `d` and `l` such that `1 <= d` and `l` and `d` are coprime, the set of values of the expression `vsum {c | dirichlet_character d c} (\c. c(l) * vsum(1..x) (\n. c n * Cx (mangoldt n / &n))) - Cx(log(&x))` for all `x` in the set of natural numbers is bounded.

### Informal sketch
* The proof starts by rewriting the expression using the `SUBGOAL_THEN` tactic to introduce a new subgoal.
* It then uses `REWRITE_TAC` and `SIMP_TAC` to simplify the expression and apply properties of Dirichlet characters.
* The `MATCH_MP_TAC` tactic is used to apply the `BOUNDED_SUMS_IMAGES` theorem.
* The proof then proceeds by cases, considering whether `c` is equal to `chi_0 d` or not.
* In the case where `c = chi_0 d`, the proof uses the `BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL` theorem.
* In the case where `c ≠ chi_0 d`, the proof uses the `BOUNDED_DIRICHLET_MANGOLDT_NONPRINCIPAL` theorem and applies properties of complex numbers and norms.
* The proof concludes by applying the `REAL_LE_MUL2` theorem and simplifying the expression.

### Mathematical insight
This theorem provides a boundedness result for a sum involving Dirichlet characters and the Mangoldt function. The result is important in number theory, particularly in the study of the distribution of prime numbers. The theorem shows that the sum in question is bounded, which has implications for the behavior of the Mangoldt function and the distribution of prime numbers.

### Dependencies
* Theorems:
	+ `BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL`
	+ `BOUNDED_DIRICHLET_MANGOLDT_NONPRINCIPAL`
	+ `BOUNDED_SUMS_IMAGES`
	+ `REAL_LE_MUL2`
* Definitions:
	+ `dirichlet_character`
	+ `chi_0`
	+ `mangoldt`
	+ `Cx`
* Properties:
	+ `FINITE_DIRICHLET_CHARACTERS`
	+ `IN_ELIM_THM`
	+ `VSUM_DELTA`
	+ `GSYM COMPLEX_VEC_0`
	+ `DIRICHLET_CHARACTER_NORM`

---

## DIRICHLET_MANGOLDT

### Name of formal statement
DIRICHLET_MANGOLDT

### Type of the formal statement
Theorem

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
    COND_CASES_TAC THEN ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_VEC_0]])
```

### Informal statement
For all positive integers `d` and `k` such that `1 <= d` and `k` and `d` are coprime, the set `{Cx(&(phi d)) * vsum {n | n IN 1..x /\ (n == k) (mod d)} (\n. Cx(mangoldt n / &n)) - Cx(log(&x)) | x IN (:num)}` is bounded.

### Informal sketch
* The proof starts by assuming `1 <= d` and `k` and `d` are coprime.
* It then applies the `SUBGOAL_THEN` tactic to find an `l` such that `(k * l == 1) (mod d)`.
* The `BOUNDED_SUM_OVER_DIRICHLET_CHARACTERS` theorem is applied to establish a bound on a sum involving Dirichlet characters.
* The proof proceeds with a series of simplifications and applications of various theorems, including `EQ_IMP`, `SET_RULE`, and `VSUM_EQ_NUMSEG`.
* Key steps involve manipulating sums and products of Dirichlet characters, using properties of congruences and the `mangoldt` function.
* The `COND_CASES_TAC` and `ASM_REWRITE_TAC` tactics are used to handle cases and simplify expressions.

### Mathematical insight
The `DIRICHLET_MANGOLDT` theorem appears to be related to the distribution of prime numbers and the properties of Dirichlet characters. The use of the `mangoldt` function, which is related to the von Mangoldt function, suggests a connection to the study of prime numbers and their distribution. The theorem may be used to establish bounds on certain sums involving Dirichlet characters, which could have implications for number theoretic applications.

### Dependencies
* Theorems:
	+ `BOUNDED_SUM_OVER_DIRICHLET_CHARACTERS`
	+ `EQ_IMP`
	+ `SET_RULE`
	+ `VSUM_EQ_NUMSEG`
	+ `DIRICHLET_CHARACTER_MUL`
	+ `DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS`
* Definitions:
	+ `Cx`
	+ `mangoldt`
	+ `phi`
	+ `log`
	+ `coprime`

---

## DIRICHLET_MANGOLDT_EXPLICIT

### Name of formal statement
DIRICHLET_MANGOLDT_EXPLICIT

### Type of the formal statement
Theorem

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
               LE_1; PHI_LOWERBOUND_1_STRONG; REAL_OF_NUM_EQ])
```

### Informal statement
For all positive integers `d` and `k` such that `1 <= d` and `k` and `d` are coprime, there exists a positive real number `B` such that for all positive integers `x`, the absolute difference between the sum of `mangoldt(n) / n` over all `n` from 1 to `x` that are congruent to `k` modulo `d`, and `log(x) / phi(d)`, is less than or equal to `B`.

### Informal sketch
* The proof starts by assuming `1 <= d` and `k` and `d` are coprime.
* It then applies the `DIRICHLET_MANGOLDT` theorem to establish a bound on the sum.
* The proof involves simplifying the expression using various properties of real numbers, such as `REAL_LT_DIV`, `REAL_OF_NUM_LT`, and `PHI_LOWERBOUND_1_STRONG`.
* The `DISCH_THEN` and `EXISTS_TAC` tactics are used to manage assumptions and introduce the constant `B`.
* The final steps involve simplifying the expression using properties of absolute value, multiplication, and division.
* Key HOL Light terms used include `mangoldt`, `phi`, and `coprime`.

### Mathematical insight
This theorem provides an explicit bound on the error term in the approximation of the sum of `mangoldt(n) / n` over all `n` from 1 to `x` that are congruent to `k` modulo `d`, in terms of `log(x) / phi(d)`. The `DIRICHLET_MANGOLDT` theorem is a key component of this proof, and the `mangoldt` function is a crucial object of study in number theory.

### Dependencies
* Theorems:
	+ `DIRICHLET_MANGOLDT`
* Definitions:
	+ `mangoldt`
	+ `phi`
	+ `coprime`
* Inductive rules: None

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the properties of real numbers, such as `REAL_LT_DIV` and `REAL_OF_NUM_LT`, are properly translated. Additionally, the `mangoldt` function and `phi` function should be defined and implemented correctly. The `coprime` relation should also be properly defined and used. The use of `DISCH_THEN` and `EXISTS_TAC` tactics may need to be adapted to the target proof assistant's syntax and semantics.

---

## DIRICHLET_STRONG

### Name of formal statement
DIRICHLET_STRONG

### Type of the formal statement
Theorem

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
  SIMP_TAC[SUBSET; IN_ELIM_THM] THEN REWRITE_TAC[CONJ_ACI])
```

### Informal statement
For all positive integers `d` and `k` such that `1 <= d` and `k` and `d` are coprime, there exists a positive real number `B` such that for all positive integers `x`, the absolute difference between the sum of the terms `log(p) / p` for all prime numbers `p` less than or equal to `x` and congruent to `k` modulo `d`, and the term `log(x) / phi(d)`, is less than or equal to `B`.

### Informal sketch
* The proof starts by assuming the existence of `d` and `k` satisfying the given conditions.
* It then uses the `DIRICHLET_MANGOLDT_EXPLICIT` theorem to establish the existence of a positive real number `B`.
* The proof then proceeds by cases, using `EXISTS_TAC` to introduce `B + 3` as a candidate for `B`.
* The main logical stages involve:
 + Using `MERTENS_MANGOLDT_VERSUS_LOG` to relate the sum of logarithmic terms to `log(x) / phi(d)`.
 + Applying `REAL_ARITH` to establish the desired inequality.
 + Using `SUBSET` and `IN_ELIM_THM` to simplify the expression.
* The `X_GEN_TAC` and `FIRST_X_ASSUM` tactics are used to introduce and manipulate variables.

### Mathematical insight
The `DIRICHLET_STRONG` theorem provides a strong form of the Dirichlet's theorem, which is a fundamental result in number theory. The theorem establishes a bound on the error term in the approximation of the sum of logarithmic terms by `log(x) / phi(d)`. This bound is crucial in many applications, including the study of prime numbers and the distribution of prime numbers in arithmetic progressions.

### Dependencies
* Theorems:
 + `DIRICHLET_MANGOLDT_EXPLICIT`
 + `MERTENS_MANGOLDT_VERSUS_LOG`
 + `REAL_ARITH`
* Definitions:
 + `coprime`
 + `prime`
 + `phi` (Euler's totient function)
 + `log` (natural logarithm)

### Porting notes
When porting this theorem to other proof assistants, care should be taken to ensure that the `coprime` and `prime` predicates are defined correctly. Additionally, the `DIRICHLET_MANGOLDT_EXPLICIT` and `MERTENS_MANGOLDT_VERSUS_LOG` theorems may need to be ported separately, as they are likely to be non-trivial results in their own right. The use of `REAL_ARITH` and `SUBSET` tactics may also require special attention, as the handling of real arithmetic and set theory can vary between proof assistants.

---

## DIRICHLET

### Name of formal statement
DIRICHLET

### Type of the formal statement
Theorem

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
  GEN_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[] THEN ASM_ARITH_TAC)
```

### Informal statement
For all `d` and `k` such that `1` is less than or equal to `d` and `k` and `d` are coprime, the set of all prime numbers `p` such that `p` is congruent to `k` modulo `d` is infinite.

### Informal sketch
* The proof starts by assuming the negation of the statement, i.e., the set of primes `p` such that `p` is congruent to `k` modulo `d` is finite.
* It then uses the `UPPER_BOUND_FINITE_SET` theorem to derive a contradiction.
* The `DIRICHLET_STRONG` theorem is used to establish a lower bound on the number of primes less than or equal to `n`.
* The proof then uses real analysis, specifically the `REAL_ARCH_SIMPLE` theorem, to derive a contradiction.
* Key steps involve using `REWRITE_TAC` to simplify expressions, `MP_TAC` to apply theorems, and `ASM_SIMP_TAC` to simplify assumptions.
* The `EXP_LOG` and `PHI_LOWERBOUND_1_STRONG` theorems are used to establish bounds on exponential and logarithmic expressions.

### Mathematical insight
The Dirichlet's theorem states that for any two coprime numbers `d` and `k`, there are infinitely many prime numbers `p` such that `p` is congruent to `k` modulo `d`. This theorem is a fundamental result in number theory and has far-reaching implications in many areas of mathematics.

### Dependencies
* Theorems:
	+ `UPPER_BOUND_FINITE_SET`
	+ `DIRICHLET_STRONG`
	+ `REAL_ARCH_SIMPLE`
	+ `EXP_LOG`
	+ `PHI_LOWERBOUND_1_STRONG`
	+ `REAL_ARITH`
* Definitions:
	+ `coprime`
	+ `prime`
	+ `INFINITE`
	+ `IN_ELIM_THM`
	+ `NOT_EXISTS_THM`
	+ `REAL_MAX_LE`
	+ `REAL_OF_NUM_LE`

### Porting notes
When porting this theorem to other proof assistants, special attention should be paid to the handling of real analysis and the `REAL_ARCH_SIMPLE` theorem. Additionally, the use of `MP_TAC` and `MATCH_MP` tactics may need to be adapted to the target proof assistant's tactic language. The `AP_TERM_TAC` and `AP_THM_TAC` tactics may also require special handling.

---

