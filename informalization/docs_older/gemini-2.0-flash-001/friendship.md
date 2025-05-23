# friendship.ml

## Overview

Number of statements: 23

`friendship.ml` formalizes the friendship theorem, a result in combinatorics. The proof is based on an argument found on MathOlymp.com and attributed to J. Q. Longyear and T. D. Parsons. It imports `prime.ml` and `pocklington.ml`, suggesting the proof may involve number-theoretic reasoning or primality tests.


## GCD_INDUCT

### Name of formal statement
GCD_INDUCT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let GCD_INDUCT = prove
 (`!P. (!m n. P m /\ P (m + n) ==> P n)
       ==> !m n. P m /\ P n ==> P (gcd(m,n))`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  WF_INDUCT_TAC `m + n:num` THEN REPEAT(POP_ASSUM MP_TAC) THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`n:num`; `m:num`] THEN
  MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL
   [REWRITE_TAC[CONJ_ACI; GCD_SYM; ADD_SYM]; REPEAT STRIP_TAC] THEN
  ASM_CASES_TAC `m = 0` THENL [ASM_MESON_TAC[GCD_0]; ALL_TAC] THEN
  UNDISCH_TAC `!m n:num. P m /\ P (m + n) ==> P n` THEN
  DISCH_THEN(MP_TAC o SPECL [`m:num`; `n - m:num`]) THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_SIMP_TAC[SUB_ADD; LT_IMP_LE] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `n - m:num`]) THEN
  REWRITE_TAC[IMP_IMP] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LE_EXISTS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC) THEN
  REWRITE_TAC[ADD_SUB2; GCD_ADD]);;
```
### Informal statement
For all predicates `P` over the natural numbers, if for all natural numbers `m` and `n`, `P(m)` and `P(m + n)` imply `P(n)`, then for all natural numbers `m` and `n`, `P(m)` and `P(n)` imply `P(gcd(m, n))`.

### Informal sketch
The theorem states an induction principle to prove properties about the greatest common divisor (`gcd`). The proof proceeds by well-founded induction on `m + n`, where `m` and `n` are natural numbers.

- Assume the inductive hypothesis: `!m n. P m /\ P (m + n) ==> P n`. Our goal is to prove `!m n. P m /\ P n ==> P (gcd(m,n))`.
- By well-founded induction on `m + n`, we assume `!x y. x + y < m + n ==> (P x /\ P y ==> P (gcd(x, y)))`.
- We can also assume, without loss of generality, that `m <= n`.
- We consider the case where `m = 0`. In this case, `gcd(m, n) = n`, so `P m /\ P n` becomes `P 0 /\ P n`, and we need to show `P n`, which is handled by `GCD_0`.
- Otherwise, `m > 0` and `m <= n`, hence `0 < m <= n` and `n - m < n`, so `m + (n - m) = n < m + n`. We want to prove `P (gcd(m, n))`, given `P m` and `P n`. We apply the induction hypothesis `!m n. P m /\ P (m + n) ==> P n` with `m` and `n - m`, which yields `P m /\ P (m + (n - m)) ==> P (n - m)`, which simplifies to `P m /\ P n ==> P (n - m)`.  Because we assumed the premise `P m` and `P n`, we can conclude `P (n - m)`.
- From `P m` and `P (n-m)`, and since `m + (n-m) < m + n`, we can conclude,  by the well-founded induction hypothesis, that `P (gcd(m, n - m))`.
- Since `gcd(m, n) = gcd(m, n - m)`, it follows that `P (gcd(m, n))`. The final step uses `GCD_ADD` and the existence of a `d` such that `n = m + d`.

### Mathematical insight
This theorem provides an induction principle tailored for proving properties of the greatest common divisor. The key idea is to reduce the problem to smaller arguments using the properties of `gcd`, particularly the property that `gcd(m, n) = gcd(m, n - m)`. Using well-founded induction on `m + n` allows us to establish the inductive step because `m + (n-m) < m + n` when `m > 0` and `m <= n`.

### Dependencies
- `Library/prime.ml`
- `Library/pocklington.ml`
- `CONJ_ACI`
- `GCD_SYM`
- `ADD_SYM`
- `GCD_0`
- `SUB_ADD`
- `LT_IMP_LE`
- `LE_EXISTS`
- `ADD_SUB2`
- `GCD_ADD`

### Porting notes (optional)
- The well-founded induction (`WF_INDUCT_TAC`) might be tricky to port directly. Other proof assistants may have slightly different ways to perform well-founded induction or may require explicit construction of the well-founded relation.
- The automatic tactics like `ASM_ARITH_TAC` will need to be replaced by equivalent tactics or manual proof steps in other systems.
- The tactics that manipulate assumptions (`POP_ASSUM MP_TAC`, etc.) need to be translated to equivalent assumption management techniques.


---

## LOOP_GCD

### Name of formal statement
LOOP_GCD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LOOP_GCD = prove
 (`!x m n. (!i. x(i + m) = x(i)) /\ (!i. x(i + n) = x(i))
           ==> !i. x(i + gcd(m,n)) = x(i)`,
  GEN_TAC THEN MATCH_MP_TAC GCD_INDUCT THEN MESON_TAC[ADD_AC]);;
```

### Informal statement
For any sequence `x` indexed by natural numbers, and for any natural numbers `m` and `n`, if `x` is periodic with period `m` (i.e., `x(i + m) = x(i)` for all `i`) and `x` is periodic with period `n` (i.e., `x(i + n) = x(i)` for all `i`), then `x` is periodic with period `gcd(m, n)` (i.e., `x(i + gcd(m, n)) = x(i)` for all `i`).

### Informal sketch
The proof proceeds by induction on `gcd(m, n)`.

- Base Case: If `gcd(m, n) = 0`, then both `m` and `n` must be 0. The hypothesis `x(i + m) = x(i)` and `x(i + n) = x(i)` becomes `x(i + 0) = x(i)`, which simplifies to `x(i) = x(i)`, and the conclusion `x(i + gcd(m, n)) = x(i)` simplifies to `x(i + 0) = x(i)`, or `x(i) = x(i)`. The theorem is thus trivial in this case.
- Inductive Step: Assume the theorem holds for all `k < gcd(m, n)`. We need to show it for `gcd(m, n)`.  Using the property that  `gcd(m, n) = gcd(n, m mod n)`, we transform the problem into proving the periodicity of `x` with `gcd(n, m mod n)`.  The inductive hypothesis becomes applicable because `gcd(n, m mod n) < gcd(m, n)` if `m mod n != 0`.  The `ADD_AC` theorem (commutativity and associativity of addition) may be used for rewriting.

### Mathematical insight
This theorem formalizes the intuitive notion that if a sequence has two periods, it must also have a period equal to the greatest common divisor of those two periods. This is useful when analyzing the long-term behavior of sequences or functions with multiple periodic constraints.

### Dependencies
- `GCD_INDUCT` (induction principle for `gcd`)
- `ADD_AC` (associativity and commutativity of addition).


---

## LOOP_COPRIME

### Name of formal statement
LOOP_COPRIME

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LOOP_COPRIME = prove
 (`!x m n. (!i. x(i + m) = x(i)) /\ (!i. x(i + n) = x(i)) /\ coprime(m,n)
           ==> !i. x i = x 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ADD1] THEN
  ASM_MESON_TAC[LOOP_GCD; COPRIME_GCD]);;
```

### Informal statement
For any function `x` from natural numbers to some type, and any natural numbers `m` and `n`, if `x` is periodic with period `m` (i.e., `x(i + m) = x(i)` for all `i`), and `x` is periodic with period `n` (i.e., `x(i + n) = x(i)` for all `i`), and `m` and `n` are coprime, then `x` is constant (i.e., `x(i) = x(0)` for all `i`).

### Informal sketch
The proof proceeds by induction on `i`.
- Base case: When `i = 0`, the statement `x 0 = x 0` is trivially true.
- Inductive step: Assume `x i = x 0`. We need to show that `x (i + 1) = x 0`. Since `m` and `n` are coprime, there exist integers `a` and `b` such that `a * m + b * n = 1` (Bezout's identity). Therefore, `i + 1 = i + a * m + b * n`.
From the periodicity of `x` with periods `m` and `n`, we have `x (i + m) = x i` and `x (i + n) = x i`.
Then, `x (i + 1) = x (i + a * m + b * n) = x (i + b * n + a * m) = x (i + a * m) = x i`. By the inductive hypothesis, `x i = x 0`, so `x (i + 1) = x 0`. The steps essentially use the periodicity to reduce the argument `i + 1` to `i`, leveraging the fact that `coprime(m, n)` implies linear combination `a*m + b*n = 1` for some `a`, `b`.
The tactic `ASM_MESON_TAC[LOOP_GCD; COPRIME_GCD]` uses `LOOP_GCD` to establish periodicity with gcd of `m` and `n`, and `COPRIME_GCD` to show the gcd is `1`, thus `x(i+1) = x(i)`.

### Mathematical insight
This theorem captures the intuition that if a function is periodic with two coprime periods, then it must be constant. The coprimality condition is essential; otherwise, the function could exhibit periodicity with the greatest common divisor of the two periods.

### Dependencies
- `ADD1` (Addition of 1)
- `LOOP_GCD` (Periodicity of a function implies periodicity with the GCD of the periods)
- `COPRIME_GCD` (Coprime numbers have a GCD of 1)

### Porting notes (optional)
- The proof relies on the properties of coprime numbers and their linear combination equaling 1. Other proof assistants should have similar libraries or tactics to handle this.
- The crucial step involves applying Bezout's identity, which might require a separate lemma in other systems.


---

## EQUIVALENCE_UNIFORM_PARTITION

### Name of formal statement
EQUIVALENCE_UNIFORM_PARTITION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EQUIVALENCE_UNIFORM_PARTITION = prove
 (`!R s k. FINITE s /\
           (!x. x IN s ==> R x x) /\
           (!x y. R x y ==> R y x) /\
           (!x y z. R x y /\ R y z ==> R x z) /\
           (!x:A. x IN s ==> CARD {y | y IN s /\ R x y} = k)
           ==> k divides (CARD s)`,
  REPEAT GEN_TAC THEN
  WF_INDUCT_TAC `CARD(s:A->bool)` THEN
  ASM_CASES_TAC `s:A->bool = {}` THENL
   [ASM_MESON_TAC[CARD_CLAUSES; DIVIDES_0]; REPEAT STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:A`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `{y:A | y IN s /\ ~(R (a:A) y)}`) THEN
  REWRITE_TAC[IMP_IMP] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[IN_ELIM_THM; FINITE_RESTRICT] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_PSUBSET THEN
      ASM_SIMP_TAC[PSUBSET; SUBSET; EXTENSION; IN_ELIM_THM] THEN
      ASM_MESON_TAC[];
      GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (ANTE_RES_THEN MP_TAC) ASSUME_TAC) THEN
      DISCH_TAC THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      AP_TERM_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `CARD(s) = CARD {y | y IN s /\ (R:A->A->bool) a y} +
                          CARD {y | y IN s /\ ~(R a y)}`
   (fun th -> ASM_SIMP_TAC[th; DIVIDES_ADD; DIVIDES_REFL]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_UNION_EQ THEN ASM SET_TAC[]);;
```
### Informal statement
For any set `s` of type `A`, and any relation `R` on `A`, and any natural number `k`, if the following conditions hold:
1. `s` is finite,
2. `R` is reflexive on `s` (i.e., for all `x` in `s`, `R x x`),
3. `R` is symmetric (i.e., for all `x` and `y`, if `R x y` then `R y x`),
4. `R` is transitive (i.e., for all `x`, `y`, and `z`, if `R x y` and `R y z` then `R x z`),
5. every element `x` in `s` is related by `R` to exactly `k` elements in `s` (i.e. the cardinality of the set `{y | y IN s /\ R x y}` is `k`)
then `k` divides the cardinality of `s`.

### Informal sketch
The proof proceeds by induction on the cardinality of the set `s`.

- Base case: `s` is empty.  Then `CARD s = 0`, and `k` divides 0.
- Inductive step: Assume the theorem holds for all sets of cardinality less than `CARD s`. Since `s` is finite, if it is not empty, we can pick an element `a` from `s`.

  *   Consider the set `{y | y IN s /\ ~(R a y)}`, denote this set `s'`. This set is the elements of `s` that are *not* R-related to `a`. We split into the case where this set is empty or non-empty. If its empty, `a` is R-related to everything, use `CARD_UNION_EQ` and `CARD_PSUBSET`
  * We show that the theorem holds for the set `s \ s'`, (i.e. the elements of `s` that *are* related to `a`). This proof shows `CARD(s) = CARD {y | y IN s /\ (R:A->A->bool) a y} + CARD {y | y IN s /\ ~(R a y)}`
  * Now, by the cardinality constraint, `{y | y IN s /\ R x y}` has cardinality `k`. Therefore `k` divides `CARD{y | y IN s /\ R x y}`. And also we know that `k` divides `CARD {y | y IN s /\ ~(R a y)}`, then we can deduce `k` divides `CARD(s)`

### Mathematical insight
The theorem states that if a set `s` is partitioned into equivalence classes of equal size `k` (under some equivalence relation `R`), then `k` must divide the cardinality of `s`. This is a standard result in elementary set theory and combinatorics. It connects the notion of equivalence relations, partitions, and divisibility.

### Dependencies
- `FINITE`, `CARD`, `IN`, `DIVIDES`
- `CARD_CLAUSES`, `DIVIDES_0`
- `MEMBER_NOT_EMPTY`, `CARD_PSUBSET`, `PSUBSET`, `SUBSET`, `EXTENSION` , `IN_ELIM_THM`
- `IMP_IMP`, `FINITE_RESTRICT`, `EQ_IMP`
- `DIVIDES_ADD`, `DIVIDES_REFL`, `CARD_UNION_EQ`

### Porting notes (optional)
The proof relies on induction on the cardinality of a finite set, which is standard in most proof assistants. The key will be to have appropriate libraries for finite sets, cardinality, and divisibility, and to correctly encode the notion of an equivalence relation. You would likely need to introduce a `FINITE` predicate, as HOL Light's finiteness is based on the absence of injections from natural numbers. Also, be mindful of potential differences in how the cardinality of sets (especially subsets defined by predicates) is handled.


---

## EQUIVALENCE_UNIFORM_PARTITION_RESTRICT

### Name of formal statement
EQUIVALENCE_UNIFORM_PARTITION_RESTRICT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EQUIVALENCE_UNIFORM_PARTITION_RESTRICT = prove
 (`!R s k. FINITE s /\
           (!x. x IN s ==> R x x) /\
           (!x y. x IN s /\ y IN s /\ R x y ==> R y x) /\
           (!x y z. x IN s /\ y IN s /\ z IN s /\ R x y /\ R y z ==> R x z) /\
           (!x:A. x IN s ==> CARD {y | y IN s /\ R x y} = k)
           ==> k divides (CARD s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQUIVALENCE_UNIFORM_PARTITION THEN
  EXISTS_TAC `\x y:A. x IN s /\ y IN s /\ R x y` THEN
  SIMP_TAC[] THEN ASM_REWRITE_TAC[CONJ_ASSOC] THEN ASM_MESON_TAC[]);;
```
### Informal statement
For all relations `R` of type `A -> A -> bool` and for all sets `s` of type `A -> bool` and for all natural numbers `k`, if the following conditions hold:
1. `s` is a finite set, and
2. for all `x`, if `x` is in `s` then `R x x` holds, and
3. for all `x` and `y`, if `x` is in `s` and `y` is in `s` and `R x y` holds then `R y x` holds, and
4. for all `x`, `y`, and `z`, if `x` is in `s` and `y` is in `s` and `z` is in `s` and `R x y` and `R y z` hold then `R x z` holds, and
5. for all `x` of type `A`, if `x` is in `s` then the cardinality of the set of all `y` such that `y` is in `s` and `R x y` holds, is equal to `k`,
then `k` divides the cardinality of `s`.

### Informal sketch
The proof proceeds as follows:
- First, the theorem `EQUIVALENCE_UNIFORM_PARTITION` is matched to introduce assumptions relating to equivalence relations and uniform partitions.
- Then, it's showen that there exist x and y such that x is in s, y is in s and R x y holds.
- Next, the goal is simplified using basic simplification rules.
- Finally, `ASM_MESON_TAC` is used with the assumptions to automatically complete the proof.

### Mathematical insight
This theorem states that if a relation `R` is reflexive, symmetric, and transitive on a finite set `s` (i.e., `R` is an equivalence relation on `s`), and if each element in `s` is related via `R` to exactly `k` elements of `s`, then `k` must divide the total number of elements in `s`. This shows a relationship between the size of the equivalence classes and the size of the set.

### Dependencies
- `EQUIVALENCE_UNIFORM_PARTITION`
- `FINITE`
- `CARD`
- `divides`

### Porting notes (optional)
- The `ASM_MESON_TAC` tactic call relies on the MESON prover, which is a powerful automated theorem prover within HOL Light. In other proof assistants, you may need to use a similar automated tactic or unfold definitions and apply the lemmas manually.


---

## ELEMENTS_PAIR_UP

### Name of formal statement
ELEMENTS_PAIR_UP

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ELEMENTS_PAIR_UP = prove
 (`!s r. FINITE s /\
         (!x. x IN s ==> ~(r x x)) /\
         (!x y. x IN s /\ y IN s /\ r x y ==> r y x) /\
         (!x:A. x IN s ==> ?!y. y IN s /\ r x y)
         ==> EVEN(CARD s)`,
  REPEAT GEN_TAC THEN WF_INDUCT_TAC `CARD(s:A->bool)` THEN
  STRIP_TAC THEN ASM_CASES_TAC `s:A->bool = {}` THEN
  ASM_REWRITE_TAC[CARD_CLAUSES; ARITH] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:A`) THEN
  MP_TAC(ASSUME `!x:A. x IN s ==> (?!y:A. y IN s /\ r x y)`) THEN
  DISCH_THEN(MP_TAC o SPEC `a:A`) THEN REWRITE_TAC[ASSUME `a:A IN s`] THEN
  DISCH_THEN(MP_TAC o EXISTENCE) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s DELETE (a:A) DELETE b`) THEN
  REWRITE_TAC[IMP_IMP] THEN ANTS_TAC THENL
   [ALL_TAC;
    DISCH_TAC THEN
    SUBGOAL_THEN `s = (a:A) INSERT b INSERT (s DELETE a DELETE b)`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_DELETE; FINITE_INSERT] THEN
    REWRITE_TAC[IN_INSERT; IN_DELETE] THEN ASM_MESON_TAC[EVEN]] THEN
  ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CARD_PSUBSET THEN ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  MP_TAC(ASSUME `!x:A. x IN s ==> (?!y. y IN s /\ r x y)`) THEN
  DISCH_THEN(MP_TAC o SPEC `x:A`) THEN REWRITE_TAC[ASSUME `x:A IN s`] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `y:A` THEN EQ_TAC THEN SIMP_TAC[] THEN ASM_MESON_TAC[]);;
```

### Informal statement
For any set `s` of type `A`, if `s` is finite, and if the relation `r` on `A` is irreflexive on `s` (i.e., for all `x` in `s`, `r x x` is false), symmetric on `s` (i.e., for all `x` and `y` in `s`, if `r x y` holds, then `r y x` holds), and every element `x` in `s` is related by `r` to some element `y` in `s` (i.e., for all `x` in `s`, there exists a `y` in `s` such that `r x y` holds), then the cardinality of `s` is even.

### Informal sketch
The proof proceeds by induction on the cardinality of `s`.

- **Base case:** If the cardinality of `s` is 0 (i.e., `s` is empty), then `CARD s` is 0 which is even by definition.

- **Inductive step:** Assume the theorem holds for all sets of cardinality less than `CARD s`.

    - Since `s` is finite and non-empty (because every `x` in `s` is related to some `y`), we can choose an element `a` from `s`.  By assumption there exists `b` such that `r a b`.
    - Now, consider the set `s DELETE a DELETE b`. This set is obtained by removing `a` and `b` from `s`.
    - The goal is to apply the induction hypothesis to the set `s DELETE a DELETE b`.
    - It remains to show that `s DELETE a DELETE b` satisfies the hypotheses: it must be finite, irreflexive and symmetric with respect to `r`, and every element `x` in `s DELETE a DELETE b` should be related via `r` to some other element in `s DELETE a DELETE b`.
    - If these are indeed satisfied, the induction hypothesis implies that `CARD (s DELETE a DELETE b)` is even.
    - Since `CARD s = CARD (s DELETE a DELETE b) + 2`,  `CARD s` is also even.
    - The proof uses `ANTS_TAC` to discharge the assumptions relating to the inductive hypothesis and `ASM_MESON_TAC` to perform automated reasoning using the assumptions in the context including irreflexivity, symmetry and existence of related elements.

- To show that every element `x` in `s DELETE a DELETE b` is related by `r` to some `y` in `s DELETE a DELETE b` the proof proceeds by contradiction.
    - Assume `x` in `s DELETE a DELETE b`. 
    - By assumption exists `y` such that `y IN s /\ r x y`.
    - It is then shown that it's not possible for `y` to be `a` or `b`.

### Mathematical insight
The theorem captures the idea that if every element in a finite set is "paired up" with another element via a symmetric and irreflexive relation, then the set must have an even number of elements. The irreflexivity condition ensures that an element cannot be paired with itself, and symmetry ensures the pairing goes both ways. The core idea is that the existence of the relation forces a pairing off of distinct elements.

### Dependencies
- `FINITE` (finiteness)
- `CARD` (cardinality)
- `IN` (set membership)
- `EVEN` (even number predicate)
- `DELETE` (set deletion)
- `INSERT` (set insertion)
- `MEMBER_NOT_EMPTY`
- `CARD_CLAUSES`
- `ARITH`
- `GSYM`
- `EXISTENCE`
- `IMP_IMP`
- `FINITE_DELETE`
- `FINITE_INSERT`
- `IN_INSERT`
- `IN_DELETE`
- `CARD_PSUBSET`
- `EQ_IMP`
- `FUN_EQ_THM`

### Porting notes (optional)
- The proof relies heavily on rewriting with set-theoretic identities and arithmetic facts.
- Automating the reasoning about set membership and cardinality is important for porting this theorem.
- The tactic `ASM_MESON_TAC` is used for automated reasoning and may need to be replaced with equivalent automation in other provers.


---

## cycle

### Name of formal statement
cycle

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let cycle = new_definition
 `cycle r k x <=> (!i. r (x i) (x(i + 1))) /\ (!i. x(i + k) = x(i))`;;
```

### Informal statement
The predicate `cycle r k x` holds if and only if for all `i`, the relation `r` holds between `x i` and `x (i + 1)`, and for all `i`, `x (i + k)` is equal to `x i`.

### Informal sketch
The definition introduces a predicate `cycle r k x` to characterize cyclic sequences. It states two conditions: 
- Adjacency via `r`: Each element `x i` is related to the next element `x (i + 1)` by the relation `r`.
- Periodicity: The sequence `x` repeats every `k` elements, i.e., `x (i + k) = x i`.
The definition is a direct formalization of the notion of a cycle.

### Mathematical insight
The definition of `cycle` formalizes the concept of a cycle of length `k` within a sequence `x` with respect to a relation `r`. The relation `r` defines the "edges" of the cycle. This definition is important for reasoning about cycles in graphs or other relational structures. The integer `k` represents the length of the cycle.

### Dependencies
None specified.

### Porting notes (optional)
When porting this definition, ensure that the target proof assistant supports reasoning about functions (sequences) and relations. The quantifiers and equality should be straightforward to translate.


---

## path

### Name of formal statement
path

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let path = new_definition
 `path r k x <=> (!i. i < k ==> r (x i) (x(i + 1))) /\
                 (!i. k < i ==> x(i) = @x. T)`;;
```

### Informal statement
The predicate `path r k x` holds if and only if: for all `i` less than `k`, the relation `r` holds between `x i` and `x (i + 1)`; and for all `i` greater than `k`, `x i` is equal to some choice term `@x. T`.

### Informal sketch
The definition introduces a predicate `path r k x`, where `r` is a relation, `k` is a natural number representing the path length, and `x` is a function representing the path. The path condition is split into two parts:
- The first part asserts that the relation `r` holds between consecutive elements `x i` and `x (i + 1)` for all `i` less than `k`. This ensures that elements along the path are correctly related.
- The second part specifies that for all `i` greater than `k`, the path `x i` becomes a constant, namely the choice term `@x. T`, which is essentially an arbitrary element. This truncates the path after length `k`.

### Mathematical insight
This definition formalizes the notion of a path of length `k` with respect to a relation `r`. The `path` predicate captures the essence of a sequence of elements related by `r`. The second part, where `x i` becomes a choice term for `i > k`, ensures that the path is well-defined beyond its specified length `k`. This is useful when dealing with paths of varying lengths, as it provides a default value for elements beyond the active part of the path.

### Dependencies
None

### Porting notes (optional)
- The choice operator `@` may need to be handled specifically depending on the target proof assistant. In systems with native support for choice, the translation is direct. Otherwise, an axiom of choice or a suitable replacement may be necessary.
- The handling of function types and quantification should be straightforward in most proof assistants like Coq, Lean, or Isabelle/HOL.


---

## CYCLE_OFFSET

### Name of formal statement
CYCLE_OFFSET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CYCLE_OFFSET = prove
 (`!r k x:num->A. cycle r k x ==> !i m. x(m * k + i) = x(i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cycle] THEN STRIP_TAC THEN GEN_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  ASM_MESON_TAC[ADD_AC]);;
```
### Informal statement
For any function `x` from natural numbers to a type `A`, if `x` is a cycle with period `k` and offset `r`, then for all natural numbers `i` and `m`, `x(m * k + i)` is equal to `x(i)`.

### Informal sketch
- The proof proceeds by induction on `m`.
- Base case: `m = 0`. Then `x(0 * k + i) = x(i)` simplifies to `x(i) = x(i)`, which is trivially true.
- Inductive step: Assume `x(m * k + i) = x(i)`. We need to prove `x((m + 1) * k + i) = x(i)`.
- We have `x((m + 1) * k + i) = x(m * k + k + i) = x(k + m * k + i)`.
- Since `x` is a `cycle` with period `k` and offset `r`, `cycle r k x` holds, which implies `x(k + n) = x(n` for any `n >= r`.
- The theorem `ADD_AC` states that addition is associative and commutative and `MULT_CLAUSES` contains simplifications for multiplication.
Using the assumption `x(m * k + i) = x(i)` and the property of `cycle` we obtain `x((m + 1) * k + i) = x(i)`.
- Therefore, by induction, for all `i` and `m`, `x(m * k + i) = x(i)`.

### Mathematical insight
This theorem states a fundamental property of cyclic functions: shifting by an integer multiple of the period `k` does not change the value of the function. The statement leverages the definition of `cycle` and basic arithmetic properties to establish this invariance.

### Dependencies
- `cycle` (definition of a cyclic function)
- `ADD_CLAUSES` (simplifications for addition)
- `MULT_CLAUSES` (simplifications for multiplication)
- `ADD_AC` (associativity and commutativity of addition)


---

## CYCLE_MOD

### Name of formal statement
CYCLE_MOD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CYCLE_MOD = prove
 (`!r k x:num->A. cycle r k x /\ ~(k = 0) ==> !i. x(i MOD k) = x(i)`,
  MESON_TAC[CYCLE_OFFSET; DIVISION]);;
```
### Informal statement
For any function `x` from numbers to `A`, if `x` is periodic with period `k` and offset `r`, and `k` is not equal to 0, then for all numbers `i`, `x(i MOD k)` is equal to `x(i)`.

### Informal sketch
The proof uses the following steps:
- Assume `cycle r k x` and `~(k = 0)`.
- Instantiate the definition of `cycle r k x`, replacing `i` with `i MOD k` and `i` with `i` in the universally quantified statement `!i. x(i + k) = x(i)`.
- The `CYCLE_OFFSET` theorem is likely used to rewrite `x(i MOD k + k)` to `x(i + k MOD k)`, then use the result of `division` to rewrite  `k MOD k` to `0` and thus `x(i + 0)` to `x(i)`.
- Simplify the equation and apply transitivity.

### Mathematical insight
This theorem states that if a function `x` is periodic with period `k`, then evaluating `x` at `i MOD k` will give the same result as evaluating `x` at `i`. This is a standard property of periodic functions and the modulo operator. It formalizes the intuition that the value of a periodic function repeats every `k` units, so taking the argument modulo `k` does not change the value.

### Dependencies
- Theorems: `CYCLE_OFFSET`, `DIVISION`


---

## PATHS_MONO

### Name of formal statement
PATHS_MONO

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PATHS_MONO = prove
 (`(!x y. r x y ==> s x y) ==> {x | path r k x} SUBSET {x | path s k x}`,
  REWRITE_TAC[path; IN_ELIM_THM; SUBSET] THEN MESON_TAC[]);;
```

### Informal statement
If for all `x` and `y`, `r x y` implies `s x y`, then the set of all `x` such that there exists a path from a given start point `k` to `x` using the relation `r` is a subset of the set of all `x` such that there exists a path from `k` to `x` using the relation `s`.

### Informal sketch
The proof proceeds as follows:
- Assume that the relation `r` is a subset of `s`, meaning that if `r x y` holds, then `s x y` holds.
- Show that if there is a path from `k` to `x` using the relation `r`, then there is a path from `k` to `x` using the relation `s`.
- The theorem `path` expressing reachability is expanded using its definition.
- Rewrite using `IN_ELIM_THM` and `SUBSET` to simplify the set membership and subset relation conditions.
- Apply `MESON_TAC` to automatically discharge the remaining proof obligation using first-order logic.

### Mathematical insight
This theorem states that if a relation `r` is contained within another relation `s`, then any point reachable from a starting point `k` via `r` is also reachable from `k` via `s`. In other words, a weaker reachability relation will allow for a wider (or same) set of reachable points versus a more strict reachability relation. This theorem captures a fundamental property of reachability and is useful in reasoning about the effects of changing the underlying relation on the set of reachable states.

### Dependencies
- Definitions: `path`
- Theorems: `IN_ELIM_THM`

### Porting notes (optional)
The proof relies on the automated theorem prover `MESON_TAC`. When porting to another proof assistant, one may need to explicitly provide the inductive argument to prove the reachability. The definition of `path` should also be ported carefully to ensure that it matches the intended semantics in HOL Light. The definition and properties of sets may need adjustment based on the details of the target proof assistant.


---

## HAS_SIZE_PATHS

### Name of formal statement
HAS_SIZE_PATHS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HAS_SIZE_PATHS = prove
 (`!N m r k. (:A) HAS_SIZE N /\ (!x. {y | r x y} HAS_SIZE m)
             ==> {x:num->A | path r k x} HAS_SIZE (N * m EXP k)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[EXP; MULT_CLAUSES] THENL
   [SUBGOAL_THEN `{x:num->A | path r 0 x} =
                  IMAGE (\a i. if i = 0 then a else @x. T) (:A)`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_UNIV; path; LT] THEN
      REWRITE_TAC[FUN_EQ_THM; LT_NZ] THEN MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_REWRITE_TAC[IN_UNIV] THEN
    REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x:num->A | path r (SUC k) x} =
    IMAGE (\(x,a) i. if i = SUC k then a else x i)
          {x,a | x IN {x | path r k x} /\ a IN {u | r (x k) u}}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; EXISTS_PAIR_THM] THEN
    X_GEN_TAC `x:num->A` THEN REWRITE_TAC[PAIR_EQ] THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b`] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    REWRITE_TAC[FUN_EQ_THM; path; LT] THEN EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `\i. if i = SUC k then @x. T else x(i):A` THEN
      EXISTS_TAC `x(SUC k):A` THEN SIMP_TAC[] THEN
      CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
      SIMP_TAC[ARITH_RULE `~(k = SUC k) /\ (i < k ==> ~(i = SUC k))`] THEN
      ASM_SIMP_TAC[ADD1; ARITH_RULE `i < k ==> ~(i + 1 = SUC k)`] THEN
      ASM_MESON_TAC[ARITH_RULE `k < i /\ ~(i = k + 1) ==> SUC k < i`];
      ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`z:num->A`; `a:A`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[ARITH_RULE `i = k \/ i < k ==> ~(i = SUC k)`] THEN
    REWRITE_TAC[ARITH_RULE `i + 1 = SUC k <=> i = k`] THEN
    ASM_MESON_TAC[ARITH_RULE `SUC k < i ==> ~(i = SUC k) /\ k < i`];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `N * m * m EXP k = (N * m EXP k) * m`] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_ELIM_THM] THEN
    REWRITE_TAC[FUN_EQ_THM; path; PAIR_EQ] THEN REPEAT GEN_TAC THEN
    STRIP_TAC THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i = SUC k` THEN
    ASM_MESON_TAC[ARITH_RULE `k < SUC k`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[HAS_SIZE_PRODUCT_DEPENDENT]);;
```

### Informal statement
For all natural numbers `N`, `m`, `r`, and `k`, if the set `(:A)` has size `N` and for all `x`, the set `{y | r x y}` has size `m`, then the set `{x:num->A | path r k x}` has size `N * m EXP k`.

### Informal sketch
The proof proceeds by induction on `k`.

- Base case (`k = 0`): Show that `{x:num->A | path r 0 x}` is equal to `IMAGE (\a i. if i = 0 then a else @x. T) (:A)`. Then, apply `HAS_SIZE_IMAGE_INJ` and use the fact that the set `(:A)` has size `N` to show that `IMAGE (\a i. if i = 0 then a else @x. T) (:A)` has size `N`.

- Inductive step (`k = SUC k`): Show that `{x:num->A | path r (SUC k) x}` is equal to `IMAGE (\(x,a) i. if i = SUC k then a else x i) {x,a | x IN {x | path r k x} /\ a IN {u | r (x k) u}}`. Apply `HAS_SIZE_IMAGE_INJ`, and then use `HAS_SIZE_PRODUCT_DEPENDENT` together with the inductive hypothesis to show that the sets `{x | path r k x}` and `{u | r (x k) u}` have sizes `N * m EXP k` and `m` respectively.
  Then `N * m EXP k * m = N * m EXP (SUC k)`.

### Mathematical insight
This theorem provides a way to calculate the size of the set of paths of a certain length, given the size of the set of starting points and the size of the set of possible next steps from any given point.

### Dependencies
- `RIGHT_FORALL_IMP_THM`
- `EXP`
- `MULT_CLAUSES`
- `EXTENSION`
- `IN_ELIM_THM`
- `IN_IMAGE`
- `IN_UNIV`
- `path`
- `LT`
- `FUN_EQ_THM`
- `LT_NZ`
- `HAS_SIZE_IMAGE_INJ`
- `EXISTS_PAIR_THM`
- `PAIR_EQ`
- `RIGHT_EXISTS_AND_THM`
- `UNWIND_THM1`
- `ADD1`
- `FORALL_PAIR_THM`
- `IN_ELIM_PAIR_THM`
- `HAS_SIZE_PRODUCT_DEPENDENT`


---

## FINITE_PATHS

### Name of formal statement
FINITE_PATHS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FINITE_PATHS = prove
 (`!r k. FINITE(:A) ==> FINITE {x:num->A | path r k x}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{x:num->A | path (\a b. T) k x}` THEN SIMP_TAC[PATHS_MONO] THEN
  MP_TAC(ISPECL [`CARD(:A)`; `CARD(:A)`; `\a:A b:A. T`; `k:num`]
                HAS_SIZE_PATHS) THEN
  ANTS_TAC THEN ASM_SIMP_TAC[HAS_SIZE; SET_RULE `{y | T} = (:A)`]);;
```

### Informal statement
For all `r` and `k`, if the type `:A` is finite, then the set of paths from `:num` to `:A` of length `k` with respect to the relation `r` is finite.

### Informal sketch
The proof proceeds as follows:
- Strip the quantifiers and assumption using `REPEAT STRIP_TAC`.
- Apply `MATCH_MP_TAC FINITE_SUBSET` to reduce the goal to proving that the set `{x:num->A | path r k x}` is a subset of a finite set.
- Exhibit the set `{x:num->A | path (\a b. T) k x}` using `EXISTS_TAC`.
- Simplify using `PATHS_MONO` to show that `{x:num->A | path r k x}` is a subset of `{x:num->A | path (\a b. T) k x}`.
- Instantiate `HAS_SIZE_PATHS` with  `CARD(:A)`; `CARD(:A)`; `\a:A b:A. T`; `k:num` using `ISPECL` and prove it.
- Discharge the assumptions using `ANTS_TAC`.
- Simplify using `HAS_SIZE` and the set rule `{y | T} = (:A)` using `ASM_SIMP_TAC`.

### Mathematical insight
The theorem establishes that if the type `:A` is finite, then the set of paths of a fixed length `k` in `:A` is also finite. This is important because it allows us to reason about the finiteness of various path-related structures. The proof relies on the fact that the set of all possible paths of length `k` is finite when `:A` is finite, and then shows that any specific set of paths defined by a relation `r` is a subset of this finite set.

### Dependencies
- `FINITE`
- `FINITE_SUBSET`
- `path`
- `PATHS_MONO`
- `HAS_SIZE_PATHS`
- `HAS_SIZE`
- `SET_RULE` (specifically, `{y | T} = (:A)`)


---

## HAS_SIZE_CYCLES

### Name of formal statement
HAS_SIZE_CYCLES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HAS_SIZE_CYCLES = prove
 (`!r k. FINITE(:A) /\ ~(k = 0)
         ==> {x:num->A | cycle r k x} HAS_SIZE
             CARD{x:num->A | path r k x /\ x(k) = x(0)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{x:num->A | cycle r k x} =
    IMAGE (\x i. x(i MOD k)) {x | path r k x /\ x(k) = x(0)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:num->A` THEN EQ_TAC THENL
     [DISCH_TAC THEN
      EXISTS_TAC `\i. if i <= k then x(i):A else @x. T` THEN
      REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[FUN_EQ_THM; LT_IMP_LE; DIVISION] THEN
        ASM_MESON_TAC[CYCLE_MOD];
        SIMP_TAC[path; LT_IMP_LE] THEN REWRITE_TAC[GSYM NOT_LT] THEN
        SIMP_TAC[ARITH_RULE `i < k ==> ~(k < i + 1)`] THEN
        ASM_MESON_TAC[cycle];
        REWRITE_TAC[LE_0; LE_REFL] THEN ASM_MESON_TAC[cycle; ADD_CLAUSES]];
      REWRITE_TAC[LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `y:num->A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[cycle] THEN CONJ_TAC THEN X_GEN_TAC `i:num` THENL
       [ALL_TAC;
        AP_TERM_TAC THEN MATCH_MP_TAC MOD_EQ THEN EXISTS_TAC `1` THEN
        REWRITE_TAC[MULT_CLAUSES]] THEN
      SUBGOAL_THEN `y((i + 1) MOD k):A = y(i MOD k + 1)` SUBST1_TAC THENL
       [ALL_TAC; ASM_MESON_TAC[path; DIVISION]] THEN
      SUBGOAL_THEN `(i + 1) MOD k = (i MOD k + 1) MOD k` SUBST1_TAC THENL
       [MATCH_MP_TAC MOD_EQ THEN EXISTS_TAC `i DIV k` THEN
        REWRITE_TAC[ARITH_RULE `i + 1 = (m + 1) + ik <=> i = ik + m`] THEN
        ASM_MESON_TAC[DIVISION];
        ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT2 o SPEC `i:num` o MATCH_MP DIVISION) THEN
      SPEC_TAC(`i MOD k`,`j:num`) THEN GEN_TAC THEN
      ONCE_REWRITE_TAC[ARITH_RULE `j < k <=> j + 1 < k \/ j + 1 = k`] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN
      UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[HAS_SIZE] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{x:num->A | path r k x}` THEN
    ASM_SIMP_TAC[FINITE_PATHS] THEN SET_TAC[]] THEN
  MAP_EVERY X_GEN_TAC [`x:num->A`; `y:num->A`] THEN SIMP_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[path; FUN_EQ_THM] THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (SPECL [`i:num`; `k:num`] LT_CASES)
  THENL [ASM_MESON_TAC[MOD_LT]; ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
  ASM_MESON_TAC[MOD_0]);;
```

### Informal statement
For any relation `r` and any non-zero natural number `k`, if the type `:A` is finite then the set of `r`-cycles of length `k` has size equal to the cardinality of the set of `r`-paths of length `k` that start and end at the same point. Here, an `r`-cycle of length `k` is a function from `num` to `A` such that for all `i`, `r(x(i))(x((i + 1) MOD k))`. An `r`-path of length `k` is a function from `num` to `A` such that for all `i < k`, `r(x(i))(x(i + 1))`.

### Informal sketch
The proof proceeds as follows:
- First, the goal is reduced to showing that the set of `r`-cycles of length `k` is equal to the image of the set of cyclical `r`-paths of length `k` under the mapping that takes a path `x` and an index `i` to `x(i MOD k)`. The cyclical `r`-paths of length `k` are those finite paths of length `k` whose last element is equal to the first element so that `x(k) = x(0)`.
- This set equality is demonstrated by showing containment in both directions.
    - To show that any cycle is in the image, we define a path which agrees with the cycle up to `k`, and arbitrarily otherwise to show that there is a cyclical path that maps to the cycle itself.
    - To show that any element in the image is a cycle, use the definitions of `path` and `cycle` and properties of the modulo function. This requires proving `y((i+1) MOD k) = y(i MOD k + 1)` and `(i + 1) MOD k = (i MOD k + 1) MOD k` under the assumption that `y` is a cyclical path.
- Then, injectivity of the `IMAGE` operator with the function `\x i. x(i MOD k)` is used, so that the size of the cycles is then equal to the size of the cyclical paths.
- Finally, it is shown that the set of cyclical paths is finite, given the assumption that the underlying type `:A` is finite.

### Mathematical insight
This theorem relates the number of cycles to the number of cyclical paths in a finite space by showing that each cycle corresponds to an equivalence class of cyclical paths. This makes clear the combinatorial relationship between paths and cycles, which is an important insight when using relations to model state transition systems.

### Dependencies
- `EXTENSION`
- `IN_IMAGE`
- `IN_ELIM_THM`
- `FUN_EQ_THM`
- `LT_IMP_LE`
- `DIVISION`
- `CYCLE_MOD`
- `path`
- `cycle`
- `LE_0`
- `LE_REFL`
- `ADD_CLAUSES`
- `LEFT_AND_EXISTS_THM`
- `LEFT_IMP_EXISTS_THM`
- `MOD_EQ`
- `MULT_CLAUSES`
- `HAS_SIZE_IMAGE_INJ`
- `HAS_SIZE`
- `FINITE_SUBSET`
- `FINITE_PATHS`
- `LT_CASES`
- `MOD_LT`
- `MOD_UNIQ`
- `MOD_0`


---

## FINITE_CYCLES

### Name of formal statement
FINITE_CYCLES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FINITE_CYCLES = prove
 (`!r k. FINITE(:A) /\ ~(k = 0) ==> FINITE {x:num->A | cycle r k x}`,
  MESON_TAC[HAS_SIZE_CYCLES; HAS_SIZE]);;
```
### Informal statement
For all types `A`, and natural numbers `k`, if the set of elements of type `A` is finite and `k` is not equal to zero, then the set of functions from natural numbers to `A` which are cyclic with period `k` with respect to `r` (where `r` is some function from `A` to `A`) is finite.

### Informal sketch
The proof uses the `MESON_TAC` tactic along with the theorems `HAS_SIZE_CYCLES` and `HAS_SIZE`.
- The theorem `HAS_SIZE_CYCLES` states that the cardinality of cyclic functions with period `k` with respect to `r` is at most `(|A|^k)`.
- The theorem `HAS_SIZE` states that a set `S` is finite if it has a cardinality.
- The finiteness of the space of cyclic functions with period `k` then follows from the finiteness of `A` and `k` not being 0.

### Mathematical insight
This theorem formalizes the intuition that if a set `A` is finite, then the set of cyclic functions from natural numbers to `A`, with a fixed period `k`, is also finite. It is useful in situations where one needs to reason about the finiteness of state spaces in cyclic systems.

### Dependencies
- Theorems: `HAS_SIZE_CYCLES`, `HAS_SIZE`


---

## CARD_PATHCYCLES_STEP

### Name of formal statement
CARD_PATHCYCLES_STEP

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CARD_PATHCYCLES_STEP = prove
 (`!N m r k.
     (:A) HAS_SIZE N /\ ~(k = 0) /\ ~(m = 0) /\
     (!x:A. {y | r x y} HAS_SIZE m) /\
     (!x y. r x y ==> r y x) /\
     (!x y. ~(x = y) ==> ?!z. r x z /\ r z y)
     ==> {x | path r (k + 2) x /\ x(k + 2) = x(0)} HAS_SIZE
         (m * CARD {x | path r k x /\ x(k) = x(0)} +
          CARD {x | path r (k) x /\ ~(x(k) = x(0))})`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SET_RULE
   `{x | path r (k + 2) x /\ x(k + 2) = x(0)} =
    {x | path r (k + 2) x /\ x k = x 0 /\ x(k + 2) = x(0)} UNION
    {x | path r (k + 2) x /\ ~(x k = x 0) /\ x(k + 2) = x(0)}`] THEN
  MATCH_MP_TAC HAS_SIZE_UNION THEN GEN_REWRITE_TAC I [CONJ_ASSOC] THEN
  CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `{x:num->A | path r (k + 2) x /\ x k = x 0 /\ x (k + 2) = x 0} =
      IMAGE (\(x,a) i. if i = k + 1 then a
                     else if i = k + 2 then x(0)
                     else x(i))
            {x,a | x IN {x | path r k x /\ x(k) = x(0)} /\
                   a IN {u | r (x k) u}}`
    SUBST1_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
       [REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
        REWRITE_TAC[IN_ELIM_THM; FUN_EQ_THM; PAIR_EQ] THEN
        MAP_EVERY X_GEN_TAC [`y:num->A`; `a:A`; `z:num->A`; `b:A`] THEN
        DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th THENL
         [ALL_TAC; MESON_TAC[]]) THEN
        REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN(fun th -> X_GEN_TAC `i:num` THEN MP_TAC th) THEN
        DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC(SPEC `0` th)) THEN
        REWRITE_TAC[ARITH_RULE `~(0 = k + 1) /\ ~(0 = k + 2)`] THEN
        DISCH_TAC THEN ASM_CASES_TAC `k:num < i` THENL
         [ASM_MESON_TAC[path]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
        ASM_MESON_TAC[ARITH_RULE `k < k + 1 /\ k < k + 2`];
        ALL_TAC] THEN
      ONCE_REWRITE_TAC[MULT_SYM] THEN
      MATCH_MP_TAC HAS_SIZE_PRODUCT_DEPENDENT THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[HAS_SIZE] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{x:num->A | path r k x}` THEN CONJ_TAC THENL
       [ALL_TAC; SET_TAC[]] THEN
      ASM_MESON_TAC[HAS_SIZE; FINITE_PATHS]] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
    REWRITE_TAC[EXISTS_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC[FUN_EQ_THM; IN_ELIM_THM] THEN
    X_GEN_TAC `x:num->A` THEN EQ_TAC THENL
     [STRIP_TAC THEN
      EXISTS_TAC `\i. if i <= k then x(i):A else @x. T` THEN
      EXISTS_TAC `(x:num->A) (k + 1)` THEN
      REWRITE_TAC[IN_ELIM_THM; LE_REFL; LE_0] THEN
      ASM_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
       [ALL_TAC; ASM_MESON_TAC[path; ARITH_RULE `k < k + 2`]] THEN
      CONJ_TAC THENL
       [ALL_TAC;
        UNDISCH_TAC `path r (k + 2) (x:num->A)` THEN
        SIMP_TAC[path; LT_IMP_LE; ARITH_RULE `i < k ==> i + 1 <= k`] THEN
        SIMP_TAC[GSYM NOT_LT] THEN
        MESON_TAC[ARITH_RULE `i < k ==> i < k + 2`]] THEN
      X_GEN_TAC `i:num` THEN
      ASM_CASES_TAC `i = k + 1` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `i = k + 2` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [path]) THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT2) THEN
      ASM_REWRITE_TAC[ARITH_RULE
       `k + 2 < i <=> ~(i <= k) /\ ~(i = k + 1) /\ ~(i = k + 2)`];
      ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`z:num->A`; `b:A`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC(SPEC `0` th)) THEN
    REWRITE_TAC[COND_ID; ARITH_RULE `~(0 = k + 1)`] THEN DISCH_TAC THEN
    REWRITE_TAC[CONJ_ASSOC] THEN DISCH_THEN(LABEL_TAC "*") THEN CONJ_TAC THENL
     [ALL_TAC; REMOVE_THEN "*" (MP_TAC o SPEC `k + 2`) THEN
      ASM_REWRITE_TAC[ARITH_RULE `~(k + 2 = k + 1)`]] THEN
    CONJ_TAC THENL
     [ALL_TAC; REMOVE_THEN "*" (MP_TAC o SPEC `k:num`) THEN
      ASM_REWRITE_TAC[ARITH_RULE `~(k = k + 2) /\ ~(k = k + 1)`]] THEN
    UNDISCH_TAC `path r k (z:num->A)` THEN ASM_REWRITE_TAC[path] THEN
    SIMP_TAC[ARITH_RULE
     `k + 2 < i ==> k < i /\ ~(i = k + 1) /\ ~(i = k + 2)`] THEN
    STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `i < k + 2 ==> ~(i = k + 2)`] THEN
    REWRITE_TAC[ARITH_RULE `i + 1 = k + 2 <=> i = k + 1`] THEN
    ASM_CASES_TAC `i = k + 1` THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[ARITH_RULE `~(x + 1 = x)`]; ALL_TAC] THEN
    REWRITE_TAC[EQ_ADD_RCANCEL] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[ARITH_RULE `i < k + 2 /\ ~(i = k) /\ ~(i = k + 1)
                              ==> i < k`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x:num->A | path r (k + 2) x /\ ~(x k = x 0) /\ x (k + 2) = x 0} =
    IMAGE (\x i. if i = k + 1 then @z. r (x k) z /\ r z (x 0)
               else if i = k + 2 then x(0)
               else x(i))
        {x | path r k x /\ ~(x(k) = x(0))}`
  SUBST1_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[HAS_SIZE] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{x:num->A | path r k x}` THEN CONJ_TAC THENL
       [ALL_TAC; SET_TAC[]] THEN
      ASM_MESON_TAC[HAS_SIZE; FINITE_PATHS]] THEN
    MAP_EVERY X_GEN_TAC [`x:num->A`; `y:num->A`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
    ASM_CASES_TAC `k:num < i` THENL
     [ASM_MESON_TAC[path]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
    ASM_MESON_TAC[ARITH_RULE `k < k + 1 /\ k < k + 2`]] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `x:num->A` THEN REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
   [STRIP_TAC THEN
    EXISTS_TAC `\i. if i <= k then x(i):A else @x. T` THEN
    ASM_REWRITE_TAC[LE_REFL; LE_0] THEN CONJ_TAC THENL
     [ALL_TAC;
      UNDISCH_TAC `path r (k + 2) (x:num->A)` THEN
      SIMP_TAC[path; LT_IMP_LE; ARITH_RULE `i < k ==> i + 1 <= k`] THEN
      SIMP_TAC[GSYM NOT_LT] THEN
      MESON_TAC[ARITH_RULE `i < k ==> i < k + 2`]] THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
    ASM_CASES_TAC `i = k + 1` THEN ASM_REWRITE_TAC[] THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SELECT_UNIQUE THEN
      UNDISCH_TAC `path r (k + 2) (x:num->A)` THEN REWRITE_TAC[path] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      DISCH_THEN(fun th -> MP_TAC(SPEC `k:num` th) THEN
                           MP_TAC(SPEC `k + 1` th)) THEN
      REWRITE_TAC[ARITH_RULE `k < k + 2 /\ k + 1 < k + 2`] THEN
      REWRITE_TAC[GSYM ADD_ASSOC; ARITH] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `i = k + 2` THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `path r (k + 2) (x:num->A)` THEN REWRITE_TAC[path] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    ASM_MESON_TAC[ARITH_RULE `~(i <= k) /\ ~(i = k + 1) /\ ~(i = k + 2)
                              ==> k + 2 < i`];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:num->A` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[ARITH_RULE
   `~(k + 2 = k + 1) /\ ~(0 = k + 1) /\ ~(0 = k + 2) /\ ~(k = k + 1) /\
    ~(k = k + 2)`] THEN
  REWRITE_TAC[path] THEN CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THENL
   [REWRITE_TAC[ARITH_RULE `i + 1 = k + 2 <=> i = k + 1`] THEN
    ASM_CASES_TAC `i = k + 1` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[ARITH_RULE `(k + 1) + 1 = k + 1 <=> F`] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < k + 2 ==> ~(i = k + 2)`] THEN
    REWRITE_TAC[EQ_ADD_RCANCEL] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `path r k (y:num->A)` THEN REWRITE_TAC[path] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    MAP_EVERY UNDISCH_TAC [`~(i:num = k)`; `~(i = k + 1)`; `i < k + 2`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `k + 2 < i ==> ~(i = k + 1) /\ ~(i = k + 2)`] THEN
  ASM_MESON_TAC[path; ARITH_RULE `k + 2 < i ==> k < i`]);;
```

### Informal statement
For any type `A`, natural number `N`, and natural numbers `m`, `r`, and `k`, if the set `A` has size `N`, `k` is not zero, `m` is not zero, for all `x` in `A` the set of `y` such that `r x y` holds has size `m`, for all `x` and `y`, if `r x y` then `r y x`, and for all `x` and `y` such that `x` is not equal to `y`, there exists a `z` such that `r x z` and `r z y`, then the set of `x` such that `path r (k + 2) x` and `x(k + 2) = x(0)` has size `m * CARD {x | path r k x /\ x(k) = x(0)} + CARD {x | path r (k) x /\ ~(x(k) = x(0))}`.

### Informal sketch
The proof proceeds by induction. The main idea is to decompose the set of paths of length `k + 2` that start and end at the same point (`x(k+2) = x(0)`) into two disjoint subsets:

- Paths of length `k + 2` such that `x(k) = x(0)` and `x(k + 2) = x(0)`.
- Paths of length `k + 2` such that `x(k) != x(0)` and `x(k + 2) = x(0)`.

The proof establishes the size of each set separately and then combines the results using the `HAS_SIZE_UNION` theorem.

- The size of the first set is obtained by creating an image via a function that extends a path of length `k` that returns to its starting point, `x(k) = x(0)`, by two steps. Specifically, the path `x` is transformed to a path where `x(k+1)` is `a` when `r (x k) a`, `x(k+2)` is `x(0)`, and `x(i)` remains the same for the rest. It continues by showing that this function forms an injection and then applies the `HAS_SIZE_IMAGE_INJ` theorem.
- The size of the second set is obtained similarly to the first set, by again using an image that adds the necessary extra steps. However, this time we are concerned with paths that do not return to their original point after `k` steps. Using the premise `(!x y. ~(x = y) ==> ?!z. r x z /\ r z y)`, we can establish that there exists elements `z` when `r (x k) z /\ r z (x 0)`. We map the path `x` to the `k + 1` path where `x(k + 1)` is set to the `z` value, `x(k + 2) = x(0)`, and `x(i)` is unchanged otherwise. Again, we show that this is an injection and use `HAS_SIZE_IMAGE_INJ`.

### Mathematical insight
This theorem is a key step in calculating the number of cycles of a given length in a graph. It provides a recursive formula for counting cycles of length `k + 2` based on the number of paths of length `k` that either return to the starting point or don't. The conditions on the relation `r` (symmetry and existence of a path of length 2 between any two distinct points) ensure that the graph is sufficiently connected for the counting argument to work.

### Dependencies
- `HAS_SIZE`
- `HAS_SIZE_UNION`
- `HAS_SIZE_IMAGE_INJ`
- `HAS_SIZE_PRODUCT_DEPENDENT`
- `FINITE_SUBSET`
- `FINITE_PATHS`
- `path`
- `SET_RULE` (for set rewriting)
- `EXTENSION`
- `IN_IMAGE`
- `IN_ELIM_PAIR_THM`
- `FUN_EQ_THM`
- `PAIR_EQ`
- `IN_ELIM_THM`
- `LEFT_IMP_EXISTS_THM`

### Porting notes (optional)
- The proof relies heavily on rewriting with set-theoretic identities and manipulation of lambda expressions. Proof assistants with strong automation for these tasks (e.g., Coq with `lia` or Isabelle with `simp`) will be beneficial.
- The `path` definition and its properties are crucial; ensure that an equivalent definition is available in the target proof assistant.
- `EXISTS_TAC` and `@` (Hilbert Choice) translate into existential introduction and choice principles, respectively; be mindful of how these are handled in the target assistant.


---

## shiftable

### Name of formal statement
shiftable

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let shiftable = new_definition
 `shiftable x y <=> ?k. !i. x(i) = y(i + k)`;;
```

### Informal statement
Two functions `x` and `y` are `shiftable` if there exists an integer `k` such that for all integers `i`, `x(i)` is equal to `y(i + k)`.

### Informal sketch
This is a definitional statement. It introduces the concept of `shiftable` functions. The definition simply states the condition under which two functions are considered `shiftable`: the existence of a shift `k` that makes the functions equal for all integer inputs.

### Mathematical insight
The definition captures the idea that two functions are essentially the same if one is a shifted version of the other. This is useful when dealing with periodic functions or sequences where the specific starting point is irrelevant. The shift `k` represents the amount by which one function is displaced relative to the other.

### Dependencies
None


---

## SHIFTABLE_REFL

### Name of formal statement
SHIFTABLE_REFL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SHIFTABLE_REFL = prove
 (`!x. shiftable x x`,
  REWRITE_TAC[shiftable] THEN MESON_TAC[ADD_CLAUSES]);;
```

### Informal statement
For all `x`, `x` is shiftable to itself.

### Informal sketch
- The proof proceeds by rewriting using the definition of `shiftable`.
- Then automatically discharges the goal by MESON.

### Mathematical insight
The theorem `SHIFTABLE_REFL` states a fundamental property of the `shiftable` relation: it is reflexive. Reflexivity is a basic property often expected of relations resembling an "identity" or "equality" in some sense.

### Dependencies
- Definitions: `shiftable`
- Theorems: `ADD_CLAUSES`


---

## SHIFTABLE_TRANS

### Name of formal statement
SHIFTABLE_TRANS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SHIFTABLE_TRANS = prove
 (`!x y z. shiftable x y /\ shiftable y z ==> shiftable x z`,
  REWRITE_TAC[shiftable] THEN MESON_TAC[ADD_ASSOC]);;
```

### Informal statement
For all `x`, `y`, and `z`, if `x` is shiftable to `y` and `y` is shiftable to `z`, then `x` is shiftable to `z`.

### Informal sketch
- The proof proceeds by first rewriting using the definition of `shiftable`.
- Then, it uses a Meson-based automatic proof search including the axiom `ADD_ASSOC` (associativity of addition), to complete the proof which then automatically discharges the transitivity property.

### Mathematical insight
The theorem establishes the transitivity of the `shiftable` relation. This means that if one can transform an object `x` to `y` via a shift, and then transform `y` to `z` via another shift, the combined operation is equivalent to a single shift from `x` to `z`. This is a fundamental property for reasoning about transformations and equivalence relations, particularly in contexts where shift operations have meaning.

### Dependencies
- Definition: `shiftable`
- Theorem: `ADD_ASSOC`


---

## SHIFTABLE_LOCAL

### Name of formal statement
SHIFTABLE_LOCAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SHIFTABLE_LOCAL = prove
 (`!x y p r. cycle r p x /\ cycle r p y /\ ~(p = 0)
             ==> (shiftable x y <=> ?k. k < p /\ !i. x(i) = y(i + k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[shiftable] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN EXISTS_TAC `k MOD p` THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o MATCH_MP DIVISION) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC
   (BINDER_CONV o LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
  ASM_MESON_TAC[CYCLE_OFFSET; ADD_AC]);;
```
### Informal statement
For all `x`, `y`, `p`, and `r`, if `cycle r p x` and `cycle r p y` and `not (p = 0)`, then `shiftable x y` if and only if there exists a `k` such that `k < p` and for all `i`, `x(i) = y(i + k)`.

### Informal sketch
The proof proceeds as follows:
- First, rewrite using the definition of `shiftable`.
- Then, consider the two directions of the equivalence separately.
- For the forward direction, assuming `shiftable x y` holds, choose a `k` such that `!i. x(i) = y(i+k)`.
  -  We want to show the existence of a `k` such that `k < p /\ !i. x(i) = y(i+k)`.
  -  Use the fact that `k` can be written as `k MOD p + p * (k DIV p)`.
  -  Then show that `k MOD p` satisfies the condition. This uses congruence properties of `MOD` operation and relies on the `cycle` property to show that `y(i+k)` is equivalent to `y(i + k MOD p)`.
- For the backward direction, assuming there exists such a `k < p`, we must show there exists a `k` such that `!i. x(i) = y(i + k)`. This is immediate, as `k < p` satisfies this condition.
- The proof uses properties of `CYCLE_OFFSET` and `ADD_AC` to rewrite the expressions involving `cycle` and addition, respectively.

### Mathematical insight
This theorem provides a local characterization of the `shiftable` predicate when dealing with cyclic arrays. It demonstrates that if two arrays `x` and `y` are cyclic with period `p`, then `x` is shiftable to `y` if and only if there is a shift `k` smaller than `p` that relates elements of the arrays `x` and `y`. The fact is that checking for shiftability can be done by considering only shifts that are strictly less than the period.

### Dependencies
- Definitions: `shiftable`
- Theorems/Axioms: `CYCLE_OFFSET`, `ADD_AC`, `DIVISION`


---

## SHIFTABLE_SYM

### Name of formal statement
SHIFTABLE_SYM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SHIFTABLE_SYM = prove
 (`!x y p r. cycle r p x /\ cycle r p y /\ ~(p = 0) /\ shiftable x y
             ==> shiftable y x`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d <=> (a /\ b /\ c) /\ d`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP SHIFTABLE_LOCAL) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[shiftable] THEN EXISTS_TAC `p - k:num` THEN
  ASM_SIMP_TAC[ARITH_RULE `k < p ==> (i + (p - k)) + k = i + p:num`] THEN
  ASM_MESON_TAC[cycle]);;
```
### Informal statement
For all numbers `x`, `y`, `p`, and `r`, if `x` is in cycle of length `p` with rotation `r`, and `y` is in cycle of length `p` with rotation `r`, and `p` is not equal to `0`, and `x` is shiftable to `y`, then `y` is shiftable to `x`.

### Informal sketch
The proof proceeds as follows:
- Assume the premises: `cycle r p x`, `cycle r p y`, `~(p = 0)`, and `shiftable x y`.
- Apply the local version of the `shiftable` definition (`SHIFTABLE_LOCAL`).
- Existentially eliminate the `k` from `shiftable x y` to obtain a specific `k:num` such that `x + k = y mod p`.
- Expand the definition of `shiftable`.
- Existentially quantify over `p - k:num`.
- Simplify using arithmetic reasoning to show `k < p ==> (i + (p - k)) + k = i + p:num`.
- Apply the theorem `cycle` to discharge the goal.

### Mathematical insight
This theorem establishes the symmetry of the `shiftable` relation under the given conditions. Essentially it states that if `x` and `y` are elements within the same cycle, the shiftable relation between them is symmetric, provided the cycle has a length greater than 0. This justifies that the notion of shiftability to some other element `y` within the cycle does not depend on the starting point `x`.

### Dependencies
- Theorems: `TAUT`, `ARITH_RULE`
- Definitions: `cycle`, `shiftable`
- Axioms: `SHIFTABLE_LOCAL`


---

## CYCLES_PRIME_LEMMA

### Name of formal statement
CYCLES_PRIME_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CYCLES_PRIME_LEMMA = prove
 (`!r p x. FINITE(:A) /\ prime p /\ (!x. ~(r x x))
           ==> p divides CARD {x:num->A | cycle r p x}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[PRIME_0] THEN
  STRIP_TAC THEN MATCH_MP_TAC EQUIVALENCE_UNIFORM_PARTITION_RESTRICT THEN
  EXISTS_TAC `shiftable:(num->A)->(num->A)->bool` THEN
  ASM_SIMP_TAC[IN_ELIM_THM; FINITE_CYCLES] THEN
  CONJ_TAC THENL [MESON_TAC[SHIFTABLE_REFL]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SHIFTABLE_SYM]; ALL_TAC] THEN
  CONJ_TAC THENL [MESON_TAC[SHIFTABLE_TRANS]; ALL_TAC] THEN
  X_GEN_TAC `x:num->A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `{y:num->A | cycle r p y /\ shiftable x y} HAS_SIZE p`
   (fun th -> MESON_TAC[HAS_SIZE; th]) THEN
  SUBGOAL_THEN `{y:num->A | cycle r p y /\ shiftable x y} =
                IMAGE (\k i. x(i + k)) {k | k < p}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `y:num->A` THEN REWRITE_TAC[FUN_EQ_THM] THEN EQ_TAC THENL
     [ASM_MESON_TAC[SHIFTABLE_LOCAL; SHIFTABLE_SYM]; ALL_TAC] THEN
    REPEAT STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [cycle]) THEN
      ASM_REWRITE_TAC[cycle] THEN MESON_TAC[ADD_AC];
      ALL_TAC] THEN
    MATCH_MP_TAC SHIFTABLE_SYM THEN
    MAP_EVERY EXISTS_TAC [`p:num`; `r:A->A->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [cycle]) THEN
    ASM_REWRITE_TAC[cycle; shiftable] THEN MESON_TAC[ADD_AC];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN REWRITE_TAC[HAS_SIZE_NUMSEG_LT] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC WLOG_LE THEN
  REWRITE_TAC[FUN_EQ_THM] THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `l:num`] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `!i. x(i):A = x(0)` MP_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[cycle]] THEN
  MATCH_MP_TAC LOOP_COPRIME THEN EXISTS_TAC `p:num` THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[cycle]; ALL_TAC] THEN
  EXISTS_TAC `l + (p - k):num` THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN
    ONCE_REWRITE_TAC[ARITH_RULE `i + l + pk = (i + pk) + l:num`] THEN
    ASSUM_LIST(REWRITE_TAC o map GSYM) THEN
    SIMP_TAC[ARITH_RULE `k < p ==> (i + p - k) + k = i + p:num`;
             ASSUME `k < p:num`] THEN
    ASM_MESON_TAC[cycle];
    ALL_TAC] THEN
  SUBGOAL_THEN `l + p - k = p + l - k:num` SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`k < p:num`; `k <= l:num`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[NUMBER_RULE `coprime(p,p + d) <=> coprime(d,p)`] THEN
  MATCH_MP_TAC PRIME_COPRIME_LT THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;
```

### Informal statement
For all relations `r` over a type `:A`, all prime numbers `p`, and all functions `x` from natural numbers to `:A`, if the set of `:A` is finite, `p` is prime, and `r` is irreflexive (i.e., `~(r x x)` for all `x`), then `p` divides the cardinality of the set of functions `x` from natural numbers to `:A` such that `cycle r p x` holds.

### Informal sketch
The proof proceeds by assuming `p` is non-zero initially. Then, one utilizes the uniform partition induced by equivalence relation to form the partition of `finite` sets. We define an equivalence relation `shiftable` such that two functions `x` and `y` are equivalent if one is a cyclic shift of the other. We then show that `shiftable` is reflexive, symmetric, and transitive.

Then the goal becomes to show that each equivalence class `{y:num->A | cycle r p y /\ shiftable x y}` has size `p`, where `x` is a function from `num` to `:A`. We establish that `{y:num->A | cycle r p y /\ shiftable x y}` is equal to `IMAGE (\k i. x(i + k)) {k | k < p}`. We then use the theorem `HAS_SIZE_IMAGE_INJ` and the fact that `{k | k < p}` has size `p`.

We then consider the case where `k < p` and `l < p` and `(\i. x(i + k) = x(i + l))`. We show that if `k \neq l` implies that `x(i) = x(0)` for all `i`. Applying `LOOP_COPRIME` which states that if `cycle r p x` holds and for all `i`, `x(i) = x(0)`, then `p = 1`. Thus we show `k = l`.

If `k <= l` is assumed without loss of generality, then we conclude that `coprime(p, p + d)` is equivalent to `coprime(d, p)`. Then, by `PRIME_COPRIME_LT` with `p` is prime, and `k < p`, we have `coprime k p`.

### Mathematical insight
The lemma relates the concept of cycles and prime numbers within a finite set context. It highlights that if a relation `r` induces cycles of prime length `p` on functions from natural numbers to a finite set `A`, then the number of such functions is divisible by `p`. This indicates a structural relationship within the set of functions based on the chosen relation and the prime number. The essence of the `cycle r p x` being used with shiftable functions will be a partition of the entire finite set into sets of size `p` or `1`, where the sets of size `1` have `x(i) = x(0)` for all `i`.

### Dependencies
- `PRIME_0`
- `EQUIVALENCE_UNIFORM_PARTITION_RESTRICT`
- `IN_ELIM_THM`
- `FINITE_CYCLES`
- `SHIFTABLE_REFL`
- `SHIFTABLE_SYM`
- `SHIFTABLE_TRANS`
- `HAS_SIZE`
- `EXTENSION`
- `IN_IMAGE`
- `FUN_EQ_THM`
- `SHIFTABLE_LOCAL`
- `cycle`
- `ADD_AC`
- `HAS_SIZE_IMAGE_INJ`
- `HAS_SIZE_NUMSEG_LT`
- `WLOG_LE`
- `LOOP_COPRIME`
- `RIGHT_EXISTS_AND_THM`
- `ARITH_RULE: i + l + pk = (i + pk) + l:num`
- `ARITH_RULE: k < p ==> (i + p - k) + k = i + p:num`
- `NUMBER_RULE: coprime(p,p + d) <=> coprime(d,p)`
- `PRIME_COPRIME_LT`

### Porting notes (optional)
- The `ASM_CASES_TAC \`p = 0\`` introduces a case split based on whether `p` is zero, which may require explicit case handling in other provers.
- The use of `MESON_TAC` suggests reliance on a first-order automatic theorem prover; replicating this level of automation might require configuring a similar tool in the target environment.
- The `ARITH_TAC` and `ASM_ARITH_TAC` calls may need to be replaced by appropriate arithmetic reasoning tactics or decision procedures in the target prover.
- The definition of `cycle` and `shiftable` must be provided along with their relevant properties.


---

## FRIENDSHIP

### Name of formal statement
FRIENDSHIP

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FRIENDSHIP = prove
 (`!friend:person->person->bool.
      FINITE(:person) /\
      (!x. ~(friend x x)) /\
      (!x y. friend x y ==> friend y x) /\
      (!x y. ~(x = y) ==> ?!z. friend x z /\ friend y z)
      ==> ?u. !v. ~(v = u) ==> friend u v`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC
   `!x y:person. ~(x = y) ==> ?!z:person. friend x z /\ friend y z` THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
  REWRITE_TAC[TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM; RIGHT_IMP_FORALL_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_TAC `mutualfriend:person->person->person`) THEN
  SUBGOAL_THEN `!s:person->bool. FINITE s` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_UNIV; FINITE_SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `degree = \p:person. CARD {q:person | friend p q}` THEN
  SUBGOAL_THEN `!x y:person. ~(friend x y) ==> degree(x):num <= degree(y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:person = y` THENL
     [ASM_MESON_TAC[LE_REFL]; ALL_TAC] THEN
    EXPAND_TAC "degree" THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD(IMAGE (\u. (mutualfriend:person->person->person) u y)
                           {q | friend (x:person) q})` THEN
    CONJ_TAC THENL
     [ALL_TAC; MATCH_MP_TAC CARD_SUBSET THEN ASM SET_TAC[]] THEN
    MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`u1:person`; `u2:person`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`x:person`; `(mutualfriend:person->person->person) u1 y`;
      `u1:person`; `u2:person`]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y:person. ~(friend x y) ==> degree x:num = degree y`
  ASSUME_TAC THENL [ASM_MESON_TAC[LE_ANTISYM]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~ p`] THEN
  GEN_REWRITE_TAC RAND_CONV [NOT_EXISTS_THM] THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
  SUBGOAL_THEN `?m:num. !x:person. degree(x) = m` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `b:person` STRIP_ASSUME_TAC o
      SPEC `a:person`) THEN
    ABBREV_TAC `c = (mutualfriend:person->person->person) a b` THEN
    ABBREV_TAC `k = (degree:person->num) a` THEN EXISTS_TAC `k:num` THEN
    SUBGOAL_THEN `(degree:person->num)(b) = k /\ ~(friend a b) /\
                  friend a c /\ friend b c`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `!x:person. ~(x = c) ==> degree x = (k:num)` ASSUME_TAC THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p:person. {q:person | friend p q} HAS_SIZE m`
  ASSUME_TAC THENL [ASM_MESON_TAC[HAS_SIZE]; ALL_TAC] THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `!p:person. {q:person | friend p q} HAS_SIZE m` THEN
    ASM_REWRITE_TAC[HAS_SIZE_0; EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `EVEN(m)` ASSUME_TAC THENL
   [UNDISCH_TAC `!x:person. degree x = (m:num)` THEN
    DISCH_THEN(SUBST1_TAC o SYM o SPEC `a:person`) THEN
    EXPAND_TAC "degree" THEN MATCH_MP_TAC ELEMENTS_PAIR_UP THEN
    EXISTS_TAC `\x y:person. friend a x /\ friend a y /\ friend x y` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[HAS_SIZE];
    ALL_TAC] THEN
  ABBREV_TAC `N = CARD(:person)` THEN
  SUBGOAL_THEN `N = m * (m - 1) + 1` ASSUME_TAC THENL
   [ABBREV_TAC `t = {q:person | friend (a:person) q}` THEN
    SUBGOAL_THEN `FINITE(t:person->bool) /\ CARD t = m` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[HAS_SIZE]; ALL_TAC] THEN
    ABBREV_TAC
     `u = \b:person. {c:person | friend b c /\ ~(c IN (a INSERT t))}` THEN
    EXPAND_TAC "N" THEN
    SUBGOAL_THEN `(:person) = (a INSERT t) UNION UNIONS {u(b) | b IN t}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INSERT; IN_UNIV; IN_UNION; IN_UNIONS] THEN
      MAP_EVERY EXPAND_TAC ["t"; "u"] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `x:person` THEN
      MATCH_MP_TAC(TAUT `(~a /\ ~b ==> c) ==> (a \/ b) \/ c`) THEN
      STRIP_TAC THEN REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
      ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c <=> b /\ a /\ c`] THEN
      ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM2] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_INSERT; DE_MORGAN_THM] THEN
      EXISTS_TAC `mutualfriend (a:person) (x:person) :person` THEN
      EXPAND_TAC "t" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `m * (m - 1) + 1 = (m + 1) + m * (m - 2)` SUBST1_TAC THENL
     [SIMP_TAC[ARITH_RULE `a + 1 = (m + 1) + m * c <=> a = m * (1 + c)`] THEN
      AP_TERM_TAC THEN UNDISCH_TAC `EVEN m` THEN
      ASM_CASES_TAC `m = 1` THEN ASM_REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
      MAP_EVERY UNDISCH_TAC [`~(m = 0)`; `~(m = 1)`] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `m + 1 = CARD((a:person) INSERT t)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[CARD_CLAUSES; ADD1] THEN EXPAND_TAC "t" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `UNIONS {u b :person->bool | (b:person) IN t} HAS_SIZE m * (m - 2)`
    MP_TAC THENL
     [MATCH_MP_TAC HAS_SIZE_UNIONS THEN CONJ_TAC THENL
       [ASM_MESON_TAC[HAS_SIZE]; ALL_TAC] THEN
      CONJ_TAC THENL
       [ALL_TAC;
        EXPAND_TAC "u" THEN REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER] THEN
        REWRITE_TAC[NOT_IN_EMPTY; IN_ELIM_THM; IN_INSERT] THEN
        EXPAND_TAC "t" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]] THEN
      REPEAT STRIP_TAC THEN
      MP_TAC(ASSUME `(b:person) IN t`) THEN EXPAND_TAC "t" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `u (b:person) =
        {q:person | friend q b} DELETE a DELETE (mutualfriend a b)`
      SUBST1_TAC THENL
       [MAP_EVERY EXPAND_TAC ["u"; "t"] THEN
        REWRITE_TAC[EXTENSION; IN_INSERT; IN_DELETE; IN_ELIM_THM] THEN
        X_GEN_TAC `x:person` THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`a:person`; `b:person`;
         `(mutualfriend:person->person->person) a b`; `x:person`]) THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[CARD_DELETE; HAS_SIZE] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_DELETE] THEN
      COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
      SUBGOAL_THEN `{q:person | friend q (b:person)} = {q | friend b q}`
      SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[ARITH_RULE `m - 1 - 1 = m - 2`] THEN
      ASM_MESON_TAC[HAS_SIZE];
      ALL_TAC] THEN
    REWRITE_TAC[HAS_SIZE] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
    MATCH_MP_TAC CARD_UNION THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_INSERT; IN_INTER; NOT_IN_EMPTY; IN_UNIONS] THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c <=> b /\ a /\ c`] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM2] THEN
    MAP_EVERY EXPAND_TAC ["u"; "t"] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(m = 2)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    SUBGOAL_THEN `(:person) HAS_SIZE 3` MP_TAC THENL
     [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:person`; `b:person`; `c:person`] THEN
    REWRITE_TAC[EXTENSION; IN_UNIV; IN_INSERT; NOT_IN_EMPTY] THEN
    STRIP_TAC THEN
    UNDISCH_TAC `!u:person. ?v:person. ~(v = u) /\ ~friend u v` THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_EXISTS_THM] THEN
    EXISTS_TAC `a:person` THEN
    UNDISCH_TAC `!p:person. {q:person | friend p q} HAS_SIZE 2` THEN
    DISCH_THEN(MP_TAC o SPEC `a:person`) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:person`; `y:person`] THEN
    STRIP_TAC THEN X_GEN_TAC `z:person` THEN
    UNDISCH_TAC `!x:person. x = a \/ x = b \/ x = c` THEN
    DISCH_THEN(fun th -> MAP_EVERY (fun x -> MP_TAC(SPEC x th))
     [`x:person`; `y:person`; `z:person`]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `m - 1` PRIME_FACTOR) THEN ANTS_TAC THENL
   [UNDISCH_TAC `~(m = 2)` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(p divides 1)` MP_TAC THENL
   [ASM_MESON_TAC[DIVIDES_ONE; PRIME_1]; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(NUMBER_RULE
   `!x. p divides (x + 1) /\ p divides x ==> p divides 1`) THEN
  EXISTS_TAC `m - 1` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(m = 0) ==> m - 1 + 1 = m`] THEN
  MATCH_MP_TAC PRIME_DIVEXP THEN EXISTS_TAC `p - 2` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(NUMBER_RULE
   `!q c K1 K2.
        p divides q /\ p divides c /\
        c = (q + 1) * K1 + K2 /\
        K1 + K2 = ((q + 1) * q + 1) * nep2
        ==> p divides nep2`) THEN
  MAP_EVERY EXISTS_TAC
   [`m - 1`; `CARD {x:num->person | cycle friend p x}`;
    `CARD {x:num->person | path friend (p-2) x /\ x (p-2) = x 0}`;
    `CARD {x:num->person | path friend (p-2) x /\ ~(x (p-2) = x 0)}`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CYCLES_PRIME_LEMMA THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `3 <= p` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `2 <= p /\ ~(p = 2) ==> 3 <= p`) THEN
    ASM_SIMP_TAC[PRIME_GE_2] THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM DIVIDES_2]) THEN
    MP_TAC(DIVIDES_CONV `2 divides 1`) THEN REWRITE_TAC[CONTRAPOS_THM] THEN
    MATCH_MP_TAC(NUMBER_RULE
     `!q. t divides q /\ m = q + 1 ==> t divides m ==> t divides w`) THEN
    EXISTS_TAC `m - 1` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(m = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(m = 0) ==> m - 1 + 1 = m`] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL[`friend:person->person->bool`; `p:num`] HAS_SIZE_CYCLES) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
    SIMP_TAC[HAS_SIZE] THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC HAS_SIZE_CARD THEN
    SUBGOAL_THEN `p = (p - 2) + 2` (fun th ->
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
    THENL [ASM_MESON_TAC[PRIME_GE_2; SUB_ADD]; ALL_TAC] THEN
    MATCH_MP_TAC CARD_PATHCYCLES_STEP THEN EXISTS_TAC `N:num` THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[HAS_SIZE]; ALL_TAC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    UNDISCH_TAC `3 <= p` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`N:num`; `m:num`; `friend:person->person->bool`; `p - 2`]
               HAS_SIZE_PATHS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[HAS_SIZE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[HAS_SIZE] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  MATCH_MP_TAC CARD_UNION_EQ THEN ASM_SIMP_TAC[FINITE_PATHS] THEN SET_TAC[]);;
```
### Informal statement
For any irreflexive and symmetric binary relation `friend` on elements of type `person` such that the set of `person` is finite and for any two distinct `person`s, there exists a `person` that is a `friend` to both, there exists a `person` `u` such that every other `person` `v` is a `friend` of `u`.

### Informal sketch
The theorem states that under the given friendship assumptions (finite set of people, irreflexivity, symmetry, and the existence of a mutual friend for any two distinct people), there exists a person who is friends with everyone else.

*   The proof begins by assuming that if `x` and `y` are not friends, then the degree of `x` is less than or equal to the degree of `y`.
*   Then, it is shown that if `x` and `y` are not friends, then the degree of `x` is equal to the degree of `y`.
*   Using the fact that degrees of all persons are equal, it is shown that there exists a number `m` such that for all `x`, the degree of `x` is `m` and `m` is not equal to `0`.
*   It is then shown that `m` is even, therefore, `N=m*(m-1)+1`.
*   `N` is defined as the cardinality of `:person`.
*   Then is is assumed that `m != 2`, and a contradiction is derived.
*   After discharging the assumption a prime factorization argument is used to show the result.
*   Finally, using `HAS_SIZE_PATHS`, the statement is proved.

### Mathematical insight
The theorem asserts the existence of a universal "friend" within a network satisfying certain conditions. The proof relies on a careful combinatorial analysis of the friendship relation and the degrees of individuals in the network, utilizing prime factorization techniques.

### Dependencies
*   `EXISTS_UNIQUE_THM`
*   `TAUT`
*   `FORALL_AND_THM`
*   `RIGHT_IMP_FORALL_THM`
*   `RIGHT_IMP_EXISTS_THM`
*   `SKOLEM_THM`
*   `IMP_IMP`
*   `GSYM CONJ_ASSOC`
*   `SUBSET_UNIV`
*   `FINITE_SUBSET`
*   `LE_REFL`
*   `LE_TRANS`
*   `EQ_IMP_LE`
*   `CARD_IMAGE_INJ`
*   `IN_ELIM_THM`
*   `LE_ANTISYM`
*   `NOT_EXISTS_THM`
*   `NOT_FORALL_THM`
*   `NOT_IMP`
*   `HAS_SIZE`
*   `HAS_SIZE_0`
*   `EXTENSION`
*   `NOT_IN_EMPTY`
*   `ELEMENTS_PAIR_UP`
*   `CARD_CLAUSES`
*   `ADD1`
*   `CARD_SUBSET`
*   `DE_MORGAN_THM`
*   `CARD_UNION`
*   `CARD_DELETE`
*   `DISJOINT`
*   `IN_INTER`
*   `PRIME_FACTOR`
*   `DIVIDES_ONE`
*   `PRIME_1`
*   `NUMBER_RULE`
*   `PRIME_DIVEXP`
*   `CYCLES_PRIME_LEMMA`
*   `PRIME_GE_2`
*   `DIVIDES_2`
*   `HAS_SIZE_CYCLES`
*   `CARD_PATHCYCLES_STEP`
*   `HAS_SIZE_PATHS`
*   `FINITE_PATHS`
### Porting notes (optional)
*   The frequent use of tactics `ASM_MESON_TAC` suggests reliance on automated first-order reasoning, which may need to be replicated in other provers using appropriate automation.
*   The proof relies heavily on arithmetic simplification (`ARITH_RULE`), implying that the target system needs similar capabilities.
*   Pay attention to how `FINITE` is defined and handled in the target system, as well as the properties of `CARD` on finite sets.
*   The use of `X_CHOOSE_TAC` and `STRIP_ASSUME_TAC` indicates a Skolemization process. Ensure the target system handles Skolemization correctly.


---

