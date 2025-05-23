# birthday.ml

## Overview

Number of statements: 9

`birthday.ml` formalizes the birthday problem, a classic probability problem concerning the likelihood of shared birthdays in a group. The file likely contains definitions related to probability, sets, and counting, and theorems that establish the probability of at least two people sharing a birthday in a group of a given size. Being a standalone file (no imports), it probably develops the necessary probability background from scratch.


## FUNSPACE_EMPTY

### Name of formal statement
FUNSPACE_EMPTY

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FUNSPACE_EMPTY = prove
 (`({} --> t) = {(\x. @y. T)}`,
  REWRITE_TAC[EXTENSION; IN_SING; funspace; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  REWRITE_TAC[FUN_EQ_THM]);;
```
### Informal statement
The set of functions from the empty set to `t` is equal to the set containing only the function that maps every element to an arbitrary element of type `T`.

### Informal sketch
The proof shows that the set `{}` `-->` `t` (functions from empty set to `t`) is the singleton set containing the function `\x. @y. T`. The theorem is proved by:
- Rewriting with `EXTENSION`: Two sets are equal iff they have the same elements.
- Rewriting with `IN_SING`: Reduce `x IN {(\x. @y. T)}` to `x = (\x. @y. T)`.
- Rewriting with `funspace`: Expand the restricted function space definition `(s --> t)`.
- Rewriting with `IN_ELIM_THM`: Eliminate the membership test.
- Rewriting with `NOT_IN_EMPTY`: Simplify `~(x IN {})` to `T`.
- Rewriting with `FUN_EQ_THM`: Two functions are equal if they agree on all inputs.

### Mathematical insight
This theorem characterizes the function space when the domain is the empty set. It essentially states that there's only one function from the empty set to any other set, which maps every element (vacuously) to an arbitrary chosen element. This is a simple but crucial property when dealing with function spaces, especially in type theory.

### Dependencies
- Definitions: `funspace`
- Theorems/Rules: `EXTENSION`, `IN_SING`, `IN_ELIM_THM`, `NOT_IN_EMPTY`, `FUN_EQ_THM`


---

## HAS_SIZE_FUNSPACE

### Name of formal statement
HAS_SIZE_FUNSPACE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HAS_SIZE_FUNSPACE = prove
 (`!s:A->bool t:B->bool m n.
        s HAS_SIZE m /\ t HAS_SIZE n ==> (s --> t) HAS_SIZE (n EXP m)`,
  REWRITE_TAC[HAS_SIZE; GSYM CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_RULES; FUNSPACE_EMPTY; NOT_IN_EMPTY] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    ASM_REWRITE_TAC[EXP; ARITH];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM HAS_SIZE] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(x INSERT s) --> t =
        IMAGE (\(y:B,g) u:A. if u = x then y else g(u))
              {y,g | y IN t /\ g IN s --> t}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; funspace; IN_ELIM_THM] THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b /\ c) /\ d <=> d /\ a /\ b /\ c`] THEN
    REWRITE_TAC[PAIR_EQ; EXISTS_PAIR_THM; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    X_GEN_TAC `f:A->B` THEN EQ_TAC THENL
     [STRIP_TAC THEN MAP_EVERY EXISTS_TAC
       [`(f:A->B) x`; `\u. if u = x then @y. T else (f:A->B) u`] THEN
      REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[IN_INSERT];
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`y:B`; `g:A->B`] THEN
      STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      ASM_MESON_TAC[IN_INSERT]];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ d <=> d /\ a /\ b`] THEN
    REWRITE_TAC[PAIR_EQ; EXISTS_PAIR_THM; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    REWRITE_TAC[FUN_EQ_THM; funspace; IN_ELIM_THM] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
    X_GEN_TAC `u:A` THEN ASM_CASES_TAC `u:A = x` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_SIMP_TAC[CARD_CLAUSES; EXP] THEN
  MATCH_MP_TAC HAS_SIZE_PRODUCT THEN ASM_MESON_TAC[]);;
```

### Informal statement
For all sets `s` of type `A -> bool` and `t` of type `B -> bool`, and for all natural numbers `m` and `n`, if `s` has size `m` and `t` has size `n`, then the function space `s --> t` (the set of all functions from `s` to `t`) has size `n EXP m` (n to the power of m).

### Informal sketch
The proof proceeds by strong induction on the finiteness of the set `s`.
- Base Case: If the set `s` is empty, then `s --> t` is a singleton set containing the empty function, and `n EXP 0` is 1, so the base case holds using `FUNSPACE_EMPTY` and `HAS_SIZE`.
- Inductive Step: Assume the theorem holds for all finite subsets of `A` with size less than the size of `s`. Let `x` be an element of `s`, and let `s'` be `s` without `x`. Then `s = x INSERT s'`. We need to show that `(x INSERT s') --> t` has size `n EXP m`.
 - The key step is to show that the function space `(x INSERT s') --> t` is in bijection with the image of some mapping over the product of `t` and `s' --> t`. Namely with: `IMAGE (\(y:B,g) u:A. if u = x then y else g(u)) {y,g | y IN t /\ g IN s' --> t}`.
 - We prove the set equality `(x INSERT s) --> t = IMAGE (\(y:B,g) u:A. if u = x then y else g(u)) {y,g | y IN t /\ g IN s --> t}`. This requires expanding definitions using `EXTENSION`, `IN_IMAGE`, `funspace`, `IN_ELIM_THM`, `PAIR_EQ`, `EXISTS_PAIR_THM` and `FUN_EQ_THM` and some beta reduction.
 - Show that the mapping `f` from `t # (s' --> t)` to `(x INSERT s') --> t` is injective.
 - Then, by the inductive hypothesis, `s'` has size `m - 1`, so `s' --> t` has size `n EXP (m - 1)`.
 - Since `t` has size `n`, the product `t # (s' --> t)` has size `n * (n EXP (m - 1))` by `HAS_SIZE_PRODUCT`.
 - Since `n * (n EXP (m - 1)) = n EXP m`, it follows that `(x INSERT s') --> t` has size `n EXP m`.

### Mathematical insight
This theorem formalizes the cardinal arithmetic of function spaces. It states that the number of functions from a set of size `m` to a set of size `n` is `n^m`. This is a fundamental result in combinatorics and set theory. The proof relies on the inductive definition of set size and the decomposition of a function space into a base case (empty domain) and an inductive step (adding one element to the domain).

### Dependencies
- Definitions:
  - `HAS_SIZE`
- Theorems:
  - `FINITE_INDUCT_STRONG`
  - `HAS_SIZE_IMAGE_INJ`
  - `HAS_SIZE_PRODUCT`
  - `CARD_CLAUSES`
  - `FINITE_RULES`
  - `FUNSPACE_EMPTY`
  - `NOT_IN_EMPTY`
  - `IN_ELIM_THM`
  - `PAIR_EQ`
  - `EXISTS_PAIR_THM`
  - `EXTENSION`
  - `FUN_EQ_THM`

### Porting notes (optional)
- The proof uses the `FINITE_INDUCT_STRONG` theorem, which relies on a strong induction principle for finite sets. This theorem or its equivalent should be available in other proof assistants.
- The `HAS_SIZE` predicate and related theorems are central. Porting these concepts accurately is crucial.
- The handling of sets and function spaces might require adjustments depending on the target proof assistant's foundational axioms.


---

## FACT_DIVIDES

### Name of formal statement
FACT_DIVIDES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FACT_DIVIDES = prove
 (`!m n. m <= n ==> ?d. FACT(n) = d * FACT(m)`,
  REWRITE_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `m:num` THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  SIMP_TAC[LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; FACT] THEN
  ASM_MESON_TAC[MULT_AC; MULT_CLAUSES]);;
```

### Informal statement
For all natural numbers `m` and `n`, if `m` is less than or equal to `n`, then there exists a natural number `d` such that `FACT(n)` equals `d` multiplied by `FACT(m)`.

### Informal sketch
The proof proceeds by induction on `n`.

- The base case involves rewriting and simplification to show that the theorem holds when `n` is zero.
- The inductive step assumes that the theorem holds for some `n` and then proves that it holds for `SUC n`. This involves rewriting the inductive hypothesis and applying properties of multiplication and the definition of the factorial function `FACT`. Specifically, the inductive step starts with assuming `m <= SUC n` and assuming the inductive hypothesis `FACT(n) = d * FACT(m)` for some `d`. Then we want to show that there is a `d'` such that `FACT(SUC n) = d' * FACT(m)`. Because `FACT(SUC n) = SUC n * FACT(n)` because of the definition of `FACT`, we have `FACT(SUC n) = SUC n * d * FACT(m)`, which equals to `d' * FACT(m)` where `d' = SUC n * d`.
- These manipulations are performed using rewriting, simplification, and the application of the inductive hypothesis and the definition of `FACT`. Finally apply `ASM_MESON_TAC`.

### Mathematical insight
This theorem states that if `m` is less than or equal to `n`, then `FACT(m)` divides `FACT(n)`. This makes intuitive sense because `FACT(n)` is the product of all integers from 1 to `n`, so if `m <= n` then `FACT(m)` must be a factor of `FACT(n)`.

### Dependencies
- `LE_EXISTS`
- `LEFT_IMP_EXISTS_THM`
- `SWAP_FORALL_THM`
- `LEFT_FORALL_IMP_THM`
- `EXISTS_REFL`
- `ADD_CLAUSES`
- `FACT`
- `MULT_AC`
- `MULT_CLAUSES`


---

## FACT_DIV_MULT

### Name of formal statement
FACT_DIV_MULT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FACT_DIV_MULT = prove
 (`!m n. m <= n ==> FACT n = (FACT(n) DIV FACT(m)) * FACT(m)`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP FACT_DIVIDES) THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
  ASM_SIMP_TAC[DIV_MULT; GSYM LT_NZ; FACT_LT]);;
```

### Informal statement
For all natural numbers `m` and `n`, if `m` is less than or equal to `n`, then `FACT n` is equal to `(FACT n) DIV (FACT m)` multiplied by `FACT m`.

### Informal sketch
The proof proceeds as follows:
- Assume `m <= n`.
- Apply the theorem `FACT_DIVIDES`, which states that if `m <= n` then `FACT m` divides `FACT n`. This gives us a witness `k` such that `FACT n = k * FACT m`.
- Rewrite using the assumption to replace `FACT n` with `k * FACT m`.
- Rewrite using symmetry of multiplication (`MULT_SYM`).
- Simplify using the theorem `DIV_MULT` (which states that `(m * n) DIV n = m` if `0 < n`), the theorem `LT_NZ` (in its reversed form `GSYM LT_NZ`, stating that `0 < n` if `n < m + 1`), and the theorem `FACT_LT` (stating that `n < m + 1` if `FACT n < FACT (m + 1)`). These simplifications reduce `(k * FACT m) DIV FACT m` to `k`. This completes the proof, showing `FACT n = k * FACT m` and `k * FACT m = k * FACT m`.

### Mathematical insight
This theorem expresses a fundamental divisibility property of the factorial function. It states that the factorial of a larger number is always divisible by the factorial of a smaller or equal number, and expresses the quotient explicitly. This is useful in combinatorial arguments and reasoning about binomial coefficients.

### Dependencies
- `FACT_DIVIDES`
- `DIV_MULT`
- `LT_NZ`
- `FACT_LT`
- `MULT_SYM`


---

## HAS_SIZE_FUNSPACE_INJECTIVE

### Name of formal statement
HAS_SIZE_FUNSPACE_INJECTIVE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HAS_SIZE_FUNSPACE_INJECTIVE = prove
 (`!s:A->bool t:B->bool m n.
        s HAS_SIZE m /\ t HAS_SIZE n
        ==> {f | f IN (s --> t) /\
                 (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)}
            HAS_SIZE (if n < m then 0 else (FACT n) DIV (FACT(n - m)))`,
  REWRITE_TAC[HAS_SIZE; GSYM CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_RULES; FUNSPACE_EMPTY; NOT_IN_EMPTY] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    REWRITE_TAC[SET_RULE `{x | x IN s} = s`] THEN
    ASM_SIMP_TAC[FINITE_RULES; CARD_CLAUSES; FACT] THEN
    SIMP_TAC[NOT_IN_EMPTY; LT; SUB_0; DIV_REFL; GSYM LT_NZ; FACT_LT] THEN
    REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM HAS_SIZE] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{f | f IN (x INSERT s) --> t /\
    (!u v. u IN (x INSERT s) /\ v IN (x INSERT s) /\ f u = f v ==> u = v)} =
        IMAGE (\(y:B,g) u:A. if u = x then y else g(u))
              {y,g | y IN t /\
                     g IN {f | f IN (s --> (t DELETE y)) /\
                               !u v. u IN s /\ v IN s /\ f u = f v ==> u = v}}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; funspace; IN_ELIM_THM] THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b /\ c) /\ d <=> d /\ a /\ b /\ c`] THEN
    REWRITE_TAC[PAIR_EQ; EXISTS_PAIR_THM; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    X_GEN_TAC `f:A->B` THEN EQ_TAC THENL
     [REWRITE_TAC[IN_INSERT; IN_DELETE] THEN
      STRIP_TAC THEN MAP_EVERY EXISTS_TAC
       [`(f:A->B) x`; `\u. if u = x then @y. T else (f:A->B) u`] THEN
      REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[];
      REWRITE_TAC[IN_INSERT; IN_DELETE; LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`y:B`; `g:A->B`] THEN
      STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ d <=> d /\ a /\ b`] THEN
    REWRITE_TAC[PAIR_EQ; EXISTS_PAIR_THM; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    REWRITE_TAC[FUN_EQ_THM; funspace; IN_ELIM_THM; IN_INSERT; IN_DELETE] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
    X_GEN_TAC `u:A` THEN ASM_CASES_TAC `u:A = x` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_SIMP_TAC[CARD_CLAUSES; EXP] THEN
  SUBGOAL_THEN
   `(if n < SUC (CARD s) then 0 else FACT n DIV FACT (n - SUC (CARD s))) =
    n * (if (n - 1) < CARD(s:A->bool) then 0
         else FACT(n - 1) DIV FACT (n - 1 - CARD s))`
  SUBST1_TAC THENL
   [ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; LT_0] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> (n - 1 < m <=> n < SUC m)`] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `n - SUC(m) = n - 1 - m`] THEN
    UNDISCH_TAC `~(n = 0)` THEN SPEC_TAC(`n:num`,`n:num`) THEN
    INDUCT_TAC THEN REWRITE_TAC[FACT; SUC_SUB1] THEN DISCH_TAC THEN
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[ADD_CLAUSES; FACT_LT; GSYM MULT_ASSOC] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC FACT_DIV_MULT THEN ARITH_TAC;
    MATCH_MP_TAC HAS_SIZE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
    ASM_SIMP_TAC[HAS_SIZE; FINITE_DELETE; CARD_DELETE]]);;
```

### Informal statement
For all sets `s` of type `A -> bool` and `t` of type `B -> bool`, and for all natural numbers `m` and `n`, if `s` has size `m` and `t` has size `n`, then the set of injective functions from `s` to `t` (i.e., the set of functions `f` such that `f` is in the function space from `s` to `t` and for all `x` and `y` in `s`, if `f x = f y`, then `x = y`) has size equal to `0` if `n < m` and `FACT n / FACT (n - m)` otherwise.

### Informal sketch
The proof proceeds by strong induction on the cardinality of the set `s`.

- Base Case: `s` is empty. The cardinality of the set of injective functions from the empty set to `t` is 1 if `n >= 0` and `0` otherwise.
- Inductive Step: Assume the theorem holds for all sets `s'` with cardinality less than the cardinality of `s`. Let `s` be `x INSERT s'`.
  - Show that the set of injective functions from `x INSERT s'` to `t` is in bijection with the set of pairs `(y, g)` where `y` is in `t` and `g` is an injective function from `s'` to `t DELETE y`. This bijection maps `(y, g)` to the function that maps `x` to `y` and any `u` in `s'` to `g u`.
  - Apply `HAS_SIZE_IMAGE_INJ` to determine the size of the set.
  - Simplify further to arrive at an equation involving factorials, and the conditional `if n < SUC (CARD s) then 0 else FACT n DIV FACT (n - SUC (CARD s)))`.
  - Prove `(if n < SUC (CARD s) then 0 else FACT n DIV FACT (n - SUC (CARD s))) = n * (if (n - 1) < CARD(s:A->bool) then 0 else FACT(n - 1) DIV FACT (n - 1 - CARD s))`. This is done by cases on `n = 0`, and induction.
  - The cardinality of injective function space follows by induction hypothesis.

### Mathematical insight
The theorem formalizes the standard combinatorial result for the number of injective functions between two finite sets. Specifically, if `|s| = m` and `|t| = n`, the number of injective functions from `s` to `t` is `n! / (n-m)!` if `n >= m`, and 0 otherwise. This is number of m-permutations in a set of size n.

### Dependencies
- `HAS_SIZE`
- `CONJ_ASSOC`
- `IMP_CONJ`
- `RIGHT_FORALL_IMP_THM`
- `FINITE_INDUCT_STRONG`
- `CARD_CLAUSES`
- `FINITE_RULES`
- `FUNSPACE_EMPTY`
- `NOT_IN_EMPTY`
- `SET_RULE`
- `LT`
- `SUB_0`
- `DIV_REFL`
- `GSYM LT_NZ`
- `FACT_LT`
- `ARITH`
- `EXTENSION`
- `IN_IMAGE`
- `funspace`
- `IN_ELIM_THM`
- `TAUT`
- `PAIR_EQ`
- `EXISTS_PAIR_THM`
- `RIGHT_EXISTS_AND_THM`
- `UNWIND_THM1`
- `GEN_BETA_CONV`
- `FUN_EQ_THM`
- `IN_INSERT`
- `IN_DELETE`
- `LEFT_IMP_EXISTS_THM`
- `HAS_SIZE_IMAGE_INJ`
- `FORALL_PAIR_THM`
- `EXP`
- `MULT_CLAUSES`
- `LT_0`
- `ADD_CLAUSES`
- `FACT`
- `SUC_SUB1`
- `DIV_UNIQ`
- `GSYM MULT_ASSOC`
- `FACT_DIV_MULT`
- `HAS_SIZE_PRODUCT_DEPENDENT`
- `FINITE_DELETE`
- `CARD_DELETE`

### Porting notes (optional)
- The proof involves significant manipulation of set cardinality and factorials. Target proof assistants should have strong support for these concepts.
- `FINITE_INDUCT_STRONG` is key for the induction step. Other systems probably provides similar induction scheme for sets.
- HOL Light's rewriting tactics (`REWRITE_TAC`, `ONCE_REWRITE_TAC`, `ASM_REWRITE_TAC`) may need to be translated into more explicit term rewriting in other systems.


---

## HAS_SIZE_DIFF

### Name of formal statement
HAS_SIZE_DIFF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HAS_SIZE_DIFF = prove
 (`!s t:A->bool m n.
        s SUBSET t /\ s HAS_SIZE m /\ t HAS_SIZE n
        ==> (t DIFF s) HAS_SIZE (n - m)`,
  SIMP_TAC[HAS_SIZE; FINITE_DIFF] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (SET_RULE
   `s SUBSET t ==> t = s UNION (t DIFF s)`)) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
  ASM_SIMP_TAC[CARD_UNION; FINITE_DIFF; ADD_SUB2;
               SET_RULE `s INTER (t DIFF s) = {}`]);;
```
### Informal statement
For all sets `s` and `t` of type `A->bool`, and natural numbers `m` and `n`, if `s` is a subset of `t`, `s` has size `m`, and `t` has size `n`, then the set difference `t DIFF s` has size `n - m`.

### Informal sketch
The proof proceeds as follows:
- Assume `s SUBSET t`, `s HAS_SIZE m`, and `t HAS_SIZE n`.
- Rewrite `s HAS_SIZE m` to `CARD s = m` and `t HAS_SIZE n` to `CARD t = n` using `HAS_SIZE`.
- Rewrite `FINITE (t DIFF s)` if possible.
- Use the subset relation `s SUBSET t` to deduce `t = s UNION (t DIFF s)`.
- Rewrite the union using `CARD_UNION` to obtain `CARD t = CARD s + CARD (t DIFF s) - CARD (s INTER (t DIFF s))`.
- Since `s INTER (t DIFF s) = {}`, deduce `CARD (s INTER (t DIFF s)) = 0`.
- Simplify using `ADD_SUB2` and rewrite the equations for `CARD t` and `CARD s` using `HAS_SIZE` to obtain `(t DIFF s) HAS_SIZE (n - m)`.

### Mathematical insight
This theorem establishes a fundamental property of set sizes and set difference. It states that if we have a set `t` and remove a subset `s` of size `m`, then the remaining set `t DIFF s` will have size `n - m`. This result is intuitive and crucial for reasoning about cardinalities of sets.

### Dependencies
- `HAS_SIZE`
- `FINITE_DIFF`
- `CARD_UNION`
- `ADD_SUB2`


---

## BIRTHDAY_THM

### Name of formal statement
BIRTHDAY_THM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BIRTHDAY_THM = prove
 (`!s:A->bool t:B->bool m n.
        s HAS_SIZE m /\ t HAS_SIZE n
        ==> {f | f IN (s --> t) /\
                 ?x y. x IN s /\ y IN s /\ ~(x = y) /\ f(x) = f(y)}
            HAS_SIZE (if m <= n then (n EXP m) - (FACT n) DIV (FACT(n - m))
                      else n EXP m)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SET_RULE
   `{f:A->B | f IN (s --> t) /\
              ?x y. x IN s /\ y IN s /\ ~(x = y) /\ f(x) = f(y)} =
    (s --> t) DIFF
    {f | f IN (s --> t) /\
                 (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)}`] THEN
  REWRITE_TAC[ARITH_RULE
   `(if a <= b then x - y else x) = x - (if b < a then 0 else y)`] THEN
  MATCH_MP_TAC HAS_SIZE_DIFF THEN
  ASM_SIMP_TAC[HAS_SIZE_FUNSPACE_INJECTIVE; HAS_SIZE_FUNSPACE] THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM]);;
```
### Informal statement
For all sets `s` of type `A` and `t` of type `B`, and natural numbers `m` and `n`, if `s` has size `m` and `t` has size `n`, then the set of functions from `s` to `t` that are not injective (i.e., there exist distinct elements `x` and `y` in `s` such that `f(x) = f(y)`) has size `n^m - n!/(n-m)!` if `m <= n` and `n^m` otherwise.

### Informal sketch
The proof proceeds by:
- Rewriting the set of non-injective functions as the difference between the set of all functions from `s` to `t` and the set of injective functions from `s` to `t`. This is done using the theorem `SET_RULE` which states that a set of functions that are not injective is equal to the set of all functions minus the set of injective functions.
- Simplifying the conditional expression `(if a <= b then x - y else x)` to `x - (if b < a then 0 else y)`.
- Applying `HAS_SIZE_DIFF` which states that the size of the difference between two sets is the difference of their sizes by proving that the injective functions are a subset of the set of all functions.
- Using `HAS_SIZE_FUNSPACE_INJECTIVE` and `HAS_SIZE_FUNSPACE` to determine the sizes of the set of injective functions and the set of all functions, respectively. The size of the set of all functions from `s` to `t` is `n^m`, and the size of the set of injective functions is `n!/(n-m)!` if `m <= n` and `0` otherwise.
- Simplifying using `SUBSET` and `IN_ELIM_THM`.
### Mathematical insight
The theorem formalizes the "birthday paradox," which states that in a set of randomly chosen people, a surprisingly small number of people is needed before there is a high probability that two of them will have the same birthday.
The result is derived by finding the total number of functions and subtracting the number of injections.

### Dependencies
- `SET_RULE`
- `ARITH_RULE`
- `HAS_SIZE_DIFF`
- `HAS_SIZE_FUNSPACE_INJECTIVE`
- `HAS_SIZE_FUNSPACE`
- `SUBSET`
- `IN_ELIM_THM`


---

## FACT_DIV_SIMP

### Name of formal statement
FACT_DIV_SIMP

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FACT_DIV_SIMP = prove
 (`!m n. m < n
         ==> (FACT n) DIV (FACT m) = n * FACT(n - 1) DIV FACT(m)`,
  GEN_TAC THEN REWRITE_TAC[LT_EXISTS; LEFT_IMP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  SIMP_TAC[LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  REWRITE_TAC[ARITH_RULE `(m + SUC d) - 1 - m = d`] THEN
  REWRITE_TAC[ARITH_RULE `(m + SUC d) - 1 = m + d`; ADD_SUB2] THEN
  GEN_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
  REWRITE_TAC[FACT_LT; ARITH_RULE `x + 0 = x`] THEN REWRITE_TAC[FACT] THEN
  SIMP_TAC[GSYM MULT_ASSOC; GSYM FACT_DIV_MULT; LE_ADD] THEN
  REWRITE_TAC[ADD_CLAUSES; FACT]);;
```

### Informal statement
For all natural numbers `m` and `n`, if `m` is less than `n`, then `(FACT n) DIV (FACT m)` is equal to `n * (FACT (n - 1)) DIV (FACT m)`.

### Informal sketch
The proof proceeds as follows:
- The initial goal is `!m n. m < n ==> FACT n DIV FACT m = n * (FACT (n - 1)) DIV FACT m`.
- Express `m < n` as `EXISTS d. n = m + SUC d` using `LT_EXISTS`.
- Skolemize `m` and `n` and simplify to remove universal quantifiers and existential quantifiers arising from `LT_EXISTS`.
- Rewrite using rules regarding arithmetic simplifications such as `(m + SUC d) - 1 - m = d` and `(m + SUC d) - 1 = m + d` along with `ADD_SUB2`.
- Apply `DIV_UNIQ` which states that `!x y z. z * x = z * y /\ z != 0 ==> x = y` to reduce the goal to proving `FACT n = n * (FACT (n - 1))` under the assumption that `FACT m` is not zero.
- Instantiate the existential from `DIV_UNIQ` with `0` and rewrite using `FACT_LT` (which states `!(n:num). 0 < n ==> 0 < FACT n), `x + 0 = x` and then `FACT` which is `!(n:num). FACT(SUC n) = SUC n * FACT n`
- Simplify using associativity of multiplication, `FACT_DIV_MULT` and `LE_ADD`
- Rewrite using `ADD_CLAUSES` and `FACT`.

### Mathematical insight
This theorem provides a simplification rule for division of factorials. It states that when dividing `FACT n` by `FACT m`, where `m < n`, we can rewrite `FACT n` as `n * FACT (n - 1)`, effectively pulling out `n` from the factorial and reducing the expression. This can be useful in simplifying combinatorial expressions.

### Dependencies
- `LT_EXISTS`
- `LEFT_IMP_EXISTS_THM`
- `SWAP_FORALL_THM`
- `LEFT_FORALL_IMP_THM`
- `EXISTS_REFL`
- `DIV_UNIQ`
- `FACT_LT`
- `FACT`
- `MULT_ASSOC`
- `FACT_DIV_MULT`
- `LE_ADD`
- `ADD_CLAUSES`
- `ARITH_RULE`
- `ADD_SUB2`


---

## BIRTHDAY_THM_EXPLICIT

### Name of formal statement
BIRTHDAY_THM_EXPLICIT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BIRTHDAY_THM_EXPLICIT = prove
 (`!s t. s HAS_SIZE 23 /\ t HAS_SIZE 365
         ==> 2 * CARD {f | f IN (s --> t) /\
                           ?x y. x IN s /\ y IN s /\ ~(x = y) /\ f(x) = f(y)}
             >= CARD (s --> t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BIRTHDAY_THM) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HAS_SIZE_FUNSPACE) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
  REPEAT(CHANGED_TAC
   (SIMP_TAC[FACT_DIV_SIMP; ARITH_LE; ARITH_LT] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV))) THEN
  SIMP_TAC[DIV_REFL; GSYM LT_NZ; FACT_LT] THEN
  REWRITE_TAC[HAS_SIZE] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;
```

### Informal statement
For all sets `s` and `t`, if the cardinality of `s` is 23 and the cardinality of `t` is 365, then twice the cardinality of the set of functions `f` from `s` to `t` such that there exist distinct elements `x` and `y` in `s` with `f(x) = f(y)` is greater than or equal to the cardinality of the set of all functions from `s` to `t`.

### Informal sketch
The theorem states the explicit form of the birthday problem.

- First, discharge the assumptions regarding `s` and `t`.
- Then, apply the more general `BIRTHDAY_THM`.
- Use `HAS_SIZE_FUNSPACE` to rewrite the cardinality of the function space.
- Simplify using arithmetic rewriting rules and the definition of `HAS_SIZE`.
- Finally, reduce the expression to a normal form using arithmetic conversion.

### Mathematical insight
The theorem is an explicit version of the birthday problem, which states that in a set of 23 people, the probability that two or more of them will have the same birthday exceeds 50%. By showing that twice the cardinality of functions with at least one collision is greater than or equal to the total number of functions, we demonstrate that more than half of the functions exhibit a collision. This is because having at least one collision in the birthday problem means that there should be at least two `x` and `y` inputs, such that `f(x) = f(y)`.

### Dependencies
- Theorems: `BIRTHDAY_THM`
- Definitions: `HAS_SIZE`, `HAS_SIZE_FUNSPACE`


---

