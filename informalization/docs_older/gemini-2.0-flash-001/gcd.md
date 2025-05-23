# gcd.ml

## Overview

Number of statements: 3

`gcd.ml` formalizes the Euclidean algorithm for computing the greatest common divisor. The file likely contains definitions related to GCD, such as the GCD function itself, and theorems establishing its properties. It depends on `prime.ml`, suggesting it might also include results connecting GCD with prime numbers.


## EGCD_INVARIANT

### Name of formal statement
EGCD_INVARIANT

### Type of the formal statement
theorem

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
  ASM_MESON_TAC[DIVIDES_SUB; DIVIDES_ADD; SUB_ADD; LE_CASES]);;
```

### Informal statement
For all natural numbers `m`, `n`, and `d`, `d` divides `egcd(m, n)` if and only if `d` divides `m` and `d` divides `n`.

### Informal sketch
The theorem states that a number `d` is a divisor of the greatest common divisor of `m` and `n` if and only if it is a divisor of both `m` and `n`.

- The proof proceeds by induction on `m + n` (using `WF_INDUCT_TAC`).

- The base cases and inductive steps consider the definition of `egcd(m, n)` which involves cases for `m = 0`, `n = 0`, `m <= n`, and `m > n`.

- The cases `m = 0` and `n = 0` are handled directly by rewriting with `DIVIDES_0`, which states that every number divides 0.

- In the inductive step, the definitions of `egcd` as well as the properties of divisibility (`DIVIDES_SUB`, `DIVIDES_ADD`, and `SUB_ADD`) and inequalities (`LE_CASES`) are used.

- Specifically, in the case where `m <= n` and both are non-zero, the goal `d divides egcd(m, n-m) <=> d divides m /\ d divides (n-m)` has the inductive hypothesis `!m n. m + n < ... ==> d divides egcd(m,n) <=> d divides m /\ d divides n` available. We must show `d divides egcd(m, n) <=> d divides m /\ d divides n`. The left-hand side simplifies to `d divides egcd(m, n-m)`.  By the inductive hypothesis, we have `d divides egcd(m, n-m) <=> d divides m /\ d divides (n-m)`. Thus, it suffices to show `(d divides m /\ d divides (n-m)) <=> (d divides m /\ d divides n)`.  If `d divides m` and `d divides (n-m)`, then `d` divides `m + (n-m)` by `DIVIDES_ADD`, so `d` divides `n`. If `d divides m` and `d divides n`, then `d` divides `n - m` by `DIVIDES_SUB`.

### Mathematical insight
This theorem expresses a fundamental property of the greatest common divisor. The definition of `egcd` is based on repeated subtraction, which is an inefficient but valid method for computing the GCD. This theorem connects that particular implementation with the fundamental characterization of the GCD in terms of divisibility.

### Dependencies
- `Library/prime.ml`
- `egcd`
- `DIVIDES_0`
- `DIVIDES_SUB`
- `DIVIDES_ADD`
- `SUB_ADD`
- `LE_CASES`


---

## EGCD_GCD

### Name of formal statement
EGCD_GCD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EGCD_GCD = prove
 (`!m n. egcd(m,n) = gcd(m,n)`,
  ONCE_REWRITE_TAC[GSYM GCD_UNIQUE] THEN
  MESON_TAC[EGCD_INVARIANT; DIVIDES_REFL]);;
```

### Informal statement
For all natural numbers `m` and `n`, the result of the extended Euclidean algorithm `egcd(m, n)` is equal to the greatest common divisor `gcd(m, n)`.

### Informal sketch
The proof proceeds as follows:
- Initially, we rewrite the goal using `GSYM GCD_UNIQUE`, which likely expresses a uniqueness property of the greatest common divisor. This rewrite is done in the `ONCE_REWRITE_TAC` tactic, indicating that it is applied only once at the top level.
- Subsequently, we apply the `MESON_TAC` tactic, which is an automated theorem prover, using `EGCD_INVARIANT` and `DIVIDES_REFL`. This indicates that the automated prover utilizes the `EGCD_INVARIANT` theorem, which probably asserts an invariant property of the extended Euclidean algorithm ensuring that the result remains a common divisor of the inputs, and `DIVIDES_REFL`, which states that any number divides itself.

### Mathematical insight
The theorem `EGCD_GCD` establishes a fundamental connection between the extended Euclidean algorithm and the greatest common divisor. It asserts that the algorithm, which may also compute Bézout coefficients, ultimately computes the greatest common divisor. This justifies using the extended Euclidean algorithm as a method for effectively calculate the GCD.

### Dependencies
- Theorems: `GCD_UNIQUE`, `EGCD_INVARIANT`, `DIVIDES_REFL`


---

## EGCD

### Name of formal statement
EGCD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EGCD = prove
 (`!a b. (egcd (a,b) divides a /\ egcd (a,b) divides b) /\
         (!e. e divides a /\ e divides b ==> e divides egcd (a,b))`,
  REWRITE_TAC[EGCD_GCD; GCD]);;
```
### Informal statement
For all integers `a` and `b`, it is the case that: the extended greatest common divisor `egcd(a, b)` divides `a`, and `egcd(a, b)` divides `b`; and for every integer `e`, if `e` divides `a` and `e` divides `b`, then `e` divides `egcd(a, b)`.

### Informal sketch
The proof is a rewriting of the goal using the theorem `EGCD_GCD` and the theorem `GCD`.
- First, it is shown that `egcd(a, b)` satisfies the definition of gcd.
- Then, the definition of greatest common divisor `GCD` is applied.

### Mathematical insight
This theorem establishes that the result of the `egcd` computation, namely `egcd(a, b)`, indeed satisfies the definition of the greatest common divisor of `a` and `b`. It asserts both that `egcd(a, b)` divides both `a` and `b`, and that any common divisor `e` of `a` and `b` also divides `egcd(a, b)`. This confirms that `egcd` correctly computes the greatest common divisor.

### Dependencies
- Theorems: `EGCD_GCD`, `GCD`


---

