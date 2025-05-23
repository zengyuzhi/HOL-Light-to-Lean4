# gcd.ml

## Overview

Number of statements: 3

The `gcd.ml` file implements the Euclidean GCD algorithm, providing a formalization of the greatest common divisor concept. It relies on the `prime.ml` library, suggesting a connection to number theory. The file likely contains definitions, theorems, and constructions related to the GCD algorithm, serving as a foundation for further mathematical developments. Its purpose is to establish a rigorous framework for computing and reasoning about greatest common divisors within the HOL Light system.

## EGCD_INVARIANT

### Name of formal statement
EGCD_INVARIANT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let EGCD_INVARIANT = prove
 (`!m n d. d divides egcd(m,n) <=> d divides m /\ d divides n`,
  GEN_TAC THEN GEN_TAC THEN WF_INDUCT_TAC `m + n` THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[egcd] THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[DIVIDES_0] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[DIVIDES_0] THEN
  COND_CASES_TAC THEN
  (W(fun (asl,w) -> FIRST_X_ASSUM(fun th ->
    MP_TAC(PART_MATCH (lhs o snd o dest_forall o rand) th (lhand w)))) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  ASM_MESON_TAC[DIVIDES_SUB; DIVIDES_ADD; SUB_ADD; LE_CASES])
```

### Informal statement
For all integers `m`, `n`, and `d`, `d` divides the greatest common divisor of `m` and `n` if and only if `d` divides `m` and `d` divides `n`.

### Informal sketch
* The proof starts by assuming `m` and `n` and proceeds by well-founded induction on `m + n`.
* It then considers cases based on whether `m` or `n` is zero and applies the definition of `egcd` and properties of divisibility.
* The proof uses `COND_CASES_TAC` to handle different conditions and `ASM_MESON_TAC` to apply relevant theorems about divisibility and arithmetic properties.
* Key steps involve recognizing the base cases when `m` or `n` is zero and using the inductive definition of `egcd` to reduce the problem size.
* The use of `PART_MATCH` and `MP_TAC` suggests a strategic application of previously proven statements to the current goal.

### Mathematical insight
This theorem provides a fundamental property of the greatest common divisor (`egcd`) function, linking it with the concept of divisibility. It's crucial for establishing the correctness of the Euclidean algorithm and has implications for number theory, demonstrating how the `egcd` of two numbers relates to their common divisors.

### Dependencies
* `egcd`
* `DIVIDES_SUB`
* `DIVIDES_ADD`
* `SUB_ADD`
* `LE_CASES`
* `DIVIDES_0`

### Porting notes
When translating this into another proof assistant, pay special attention to how the system handles well-founded induction, case analysis, and the application of previously proven theorems. The strategic use of `PART_MATCH` and `MP_TAC` might need to be adapted based on the target system's mechanisms for applying hypotheses and theorems. Additionally, ensure that the definitions of `egcd` and divisibility are correctly ported, as they are fundamental to the proof.

---

## EGCD_GCD

### Name of formal statement
EGCD_GCD

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let EGCD_GCD = prove
 (`!m n. egcd(m,n) = gcd(m,n)`,
  ONCE_REWRITE_TAC[GSYM GCD_UNIQUE] THEN
  MESON_TAC[EGCD_INVARIANT; DIVIDES_REFL]);;
```

### Informal statement
For all integers `m` and `n`, the `egcd` of `m` and `n` is equal to the greatest common divisor (`gcd`) of `m` and `n`.

### Informal sketch
* The proof starts with the statement `!m n. egcd(m,n) = gcd(m,n)`, which asserts the equality between `egcd` and `gcd` for all integers `m` and `n`.
* The `ONCE_REWRITE_TAC` tactic is applied with `GSYM GCD_UNIQUE`, suggesting a unique characterization of the greatest common divisor is used to rewrite the goal.
* The `MESON_TAC` tactic is then applied with `EGCD_INVARIANT` and `DIVIDES_REFL` to deduce the equality, likely leveraging properties of the `egcd` function and reflexive properties of divisibility.

### Mathematical insight
This theorem establishes the equivalence between the `egcd` function and the traditional greatest common divisor (`gcd`) for all integers, ensuring that `egcd` behaves as expected and computes the correct greatest common divisor.

### Dependencies
#### Theorems
* `GCD_UNIQUE`
* `EGCD_INVARIANT`
* `DIVIDES_REFL`

### Porting notes
When translating this theorem into another proof assistant, ensure that the `egcd` function and `gcd` are defined and their properties (like `EGCD_INVARIANT` and `GCD_UNIQUE`) are established. Note that the `ONCE_REWRITE_TAC` and `MESON_TAC` tactics may have analogs in other systems (e.g., `rewrite` and `meson` tactics in other proof assistants), but their exact application may vary depending on the target system's automation and tactic language.

---

## EGCD

### Name of formal statement
EGCD

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let EGCD = prove
 (`!a b. (egcd (a,b) divides a /\ egcd (a,b) divides b) /\
         (!e. e divides a /\ e divides b ==> e divides egcd (a,b))`,
  REWRITE_TAC[EGCD_GCD; GCD])
```

### Informal statement
For all integers `a` and `b`, the greatest common divisor (`egcd`) of `a` and `b` divides both `a` and `b`, and for any integer `e` that divides both `a` and `b`, `e` also divides the `egcd` of `a` and `b`.

### Informal sketch
* The theorem `EGCD` asserts the fundamental property of the greatest common divisor (`egcd`) of two integers `a` and `b`.
* It first states that `egcd(a, b)` divides both `a` and `b`.
* Then, it claims that any common divisor `e` of `a` and `b` must also divide `egcd(a, b)`, establishing `egcd(a, b)` as the greatest among all common divisors.
* The proof involves rewriting using `EGCD_GCD` and `GCD`, suggesting a strategic application of definitions and properties related to the greatest common divisor.

### Mathematical insight
The `EGCD` theorem encapsulates the defining characteristics of the greatest common divisor in a way that is both intuitive and foundational for number theory. It ensures that `egcd(a, b)` is indeed the greatest common divisor by verifying its divisibility of `a` and `b` and its relationship with other common divisors.

### Dependencies
* `EGCD_GCD`
* `GCD`

### Porting notes
When translating this theorem into another proof assistant, ensure that the definitions of `egcd` and `divides` are correctly ported and that the `REWRITE_TAC` strategy is appropriately replaced with equivalent rewriting or simplification tactics available in the target system. Pay special attention to how the target system handles quantifiers and binder syntax, as these may differ from HOL Light.

---

