# subsequence.ml

## Overview

Number of statements: 5

The file `subsequence.ml` formalizes the Erdos-Szekeres theorem. This theorem concerns the existence of either ascending or descending subsequences of a certain length within a sequence of numbers. The file provides definitions and proofs related to this theorem.


## lemma

### Name of formal statement
lemma

### Type of the formal statement
theorem

### Formal Content
```ocaml
let lemma = prove
 (`!f s. s = UNIONS (IMAGE (\a. {x | x IN s /\ f(x) = a}) (IMAGE f s))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN GEN_TAC THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_IMAGE] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  GEN_REWRITE_TAC RAND_CONV [SWAP_EXISTS_THM] THEN
  REWRITE_TAC[UNWIND_THM2; GSYM CONJ_ASSOC; IN_ELIM_THM] THEN SET_TAC[]);;
```

### Informal statement
For any function `f` and set `s`, `s` is equal to the union of the images, under `f`, of the sets `{x | x IN s /\ f(x) = a}` for all `a` in the image of `f` on `s`.

### Informal sketch
The proof demonstrates that a set `s` can be decomposed into a union of subsets, each containing elements of `s` that map to a specific value under the function `f`.

- Start by generalizing the goal to assume an arbitrary function `f` and set `s`.
- Expand the definition of set equality using `EXTENSION` to show mutual inclusion.
- Introduce an arbitrary element `x`.
- Rewrite using `IN_UNIONS`, `IN_ELIM_THM`, and `IN_IMAGE` to expand definitions of set membership in unions and images.
- Manipulate existential quantification using `LEFT_AND_EXISTS_THM` and `SWAP_EXISTS_THM`.
- Unwind definitions using `UNWIND_THM2`, `GSYM CONJ_ASSOC`, and `IN_ELIM_THM`.
- Use `SET_TAC` to complete the proof using set-theoretic reasoning.

### Mathematical insight
This lemma expresses a fundamental decomposition of a set `s` based on the function `f`. It states that `s` can be reconstructed by partitioning it into sets of elements sharing the same image under `f`, then taking the union of these sets. This is a crucial step in theories involving functions and sets, providing a way to analyze sets based on their values under a given function.

### Dependencies
- `EXTENSION`
- `IN_UNIONS`
- `IN_ELIM_THM`
- `IN_IMAGE`
- `LEFT_AND_EXISTS_THM`
- `SWAP_EXISTS_THM`
- `UNWIND_THM2`
- `CONJ_ASSOC`

### Porting notes (optional)
This theorem relies heavily on rewriting and set-theoretic tactics. When porting to other provers, ensure that the definitions related to sets, images, and unions are consistent. The handling of existential quantifiers might also require careful attention.


---

## PIGEONHOLE_LEMMA

### Name of formal statement
PIGEONHOLE_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PIGEONHOLE_LEMMA = prove
 (`!f:A->B s n.
        FINITE s /\ (n - 1) * CARD(IMAGE f s) < CARD s
        ==> ?t a. t SUBSET s /\ t HAS_SIZE n /\ (!x. x IN t ==> f(x) = a)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MP_TAC(ISPECL [`f:A->B`; `s:A->bool`] lemma) THEN DISCH_THEN(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o funpow 2 RAND_CONV) [th]) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[NOT_LT] THEN
  STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN MATCH_MP_TAC
   (REWRITE_RULE[SET_RULE `{t x | x IN s} = IMAGE t s`] CARD_UNIONS_LE) THEN
  ASM_SIMP_TAC[HAS_SIZE; FINITE_IMAGE] THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:A->bool` THEN
    ASM_SIMP_TAC[SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC(ARITH_RULE `~(n <= x) ==> x <= n - 1`) THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPEC `{y | y IN s /\ (f:A->B) y = f x}` CHOOSE_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]);;
```

### Informal statement
For any function `f` from a type `A` to a type `B`, for any set `s` of type `A`, and for any natural number `n`, if `s` is finite and `(n - 1)` times the cardinality of the image of `s` under `f` is strictly less than the cardinality of `s`, then there exists a set `t` which is a subset of `s`, has size `n`, and such that for all `x` in `t`, `f(x)` is equal to some value `a`.

### Informal sketch
The proof proceeds by assuming the antecedent, that `s` is finite and `(n - 1) * CARD(IMAGE f s) < CARD s`.
- Use the assumption `(n - 1) * CARD(IMAGE f s) < CARD s` and rewrite it to `~(CARD s <= (n - 1) * CARD(IMAGE f s))`.
- From the inequality, derive that there exists an `x` such that `CARD {y | y IN s /\ f y = f x} >= n` using `CHOOSE_SUBSET`.
- Construct the subset `t` of `s` of size `n` such that for all `x` in `t` we have `f(x) = a`.
- Apply `MONO_EXISTS` to make sure desired set exists.
- The goal is then solved by set tactics.

### Mathematical insight
The pigeonhole principle states that if you have more pigeons than pigeonholes, then at least one pigeonhole must contain more than one pigeon. This lemma gives a quantitative version of pigeonhole principle. If the size of domain is much bigger than the image of the domain, then there is a fiber (pre-image of singletons) containing at least `n` items. 

### Dependencies
- `FINITE`
- `CARD`
- `IMAGE`
- `SUBSET`
- `HAS_SIZE`
- `CHOOSE_SUBSET`
- `CARD_UNIONS_LE`
- `FINITE_IMAGE`
- `FORALL_IN_IMAGE`
- `SUBSET`
- `IN_ELIM_THM`
- `MONO_EXISTS`


---

## mono_on

### Name of formal statement
mono_on

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let mono_on = define
 `mono_on (f:num->real) r s <=>
    !i j. i IN s /\ j IN s /\ i <= j ==> r (f i) (f j)`;;
```

### Informal statement
The function `mono_on` is defined such that `mono_on f r s` holds if and only if for all natural numbers `i` and `j`, if `i` is in the set `s` and `j` is in the set `s` and `i` is less than or equal to `j`, then `r (f i) (f j)` holds. Here, `f` is a function from natural numbers to real numbers, `r` is a relation on real numbers, and `s` is a set of natural numbers.

### Informal sketch
The definition introduces the concept of monotonicity of a function `f` on a set `s` with respect to a relation `r`.
- The right-hand side of the definition expresses that for any two elements `i` and `j` in the set `s` such that `i <= j`, the relation `r` holds between `f i` and `f j`.
- This captures the essence of monotonicity: as the input increases (from `i` to `j`), the output (according to `f`) maintains a consistent ordering as defined by `r`.

### Mathematical insight
The `mono_on` definition formalizes the notion of monotonicity of a function `f` with respect to a relation `r` when restricted to elements of a set `s`. This is a fundamental concept used in analysis and other areas where it is important to reason about the ordering of function values. The flexibility of using a general relation `r` allows us to express various types of monotonicity (increasing, decreasing, non-decreasing, non-increasing), depending on the specific relation used. This definition provides a concise and general way to capture monotonicity on a specific domain.

### Dependencies
- `IN` (set membership)
- `<=` (less than or equal, on natural numbers)

### Porting notes (optional)
- When porting, ensure that the target proof assistant supports defining relations and functions with the specified types (natural numbers and real numbers). Also, ensure that the set membership operator (`IN`) and the less than or equal to operator are defined and behave as expected. Pay attention to how real numbers are defined in the target system, and the relation `r` will need to conform to this real number system.


---

## MONO_ON_SUBSET

### Name of formal statement
MONO_ON_SUBSET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MONO_ON_SUBSET = prove
 (`!s t. t SUBSET s /\ mono_on f r s ==> mono_on f r t`,
  REWRITE_TAC[mono_on; SUBSET] THEN MESON_TAC[]);;
```
### Informal statement
For all sets `s` and `t`, if `t` is a subset of `s` and `f` is monotonic on `s` with respect to relation `r`, then `f` is monotonic on `t` with respect to relation `r`.

### Informal sketch
The proof proceeds by rewriting the definition of `mono_on` and `SUBSET`, and then using a MESON-based automated theorem prover to discharge the resulting goal.
- The definition of `mono_on` is expanded, yielding a goal involving universal quantification over elements `x` and `y` in `t`.
- The assumption that `t` is a subset of `s` is used to show that `x` and `y` are also elements of `s`.
- The assumption that `f` is monotonic on `s` is then applied.
- Automated theorem proving (via `MESON_TAC`) completes the remainder of the proof.

### Mathematical insight
This theorem states a fundamental property of monotonicity. If a function is monotonic on a set, it is also monotonic on any subset of that set. This is a natural and useful property, as it allows one to deduce monotonicity on smaller domains when it has already been established on a larger domain.

### Dependencies
Definitions:
- `mono_on`
- `SUBSET`
Theorems:
- None

### Porting notes (optional)
The main challenge in porting this theorem is likely to be automating the final step of the proof. The `MESON_TAC` tactic in HOL Light is a powerful automated theorem prover, and it may be necessary to use a similar automated tactic (e.g., `auto` in Isabelle, `lia` or `omega` in Coq, or `smt` in Lean) to complete the proof in another system. Alternatively, the proof could be completed by manually applying the appropriate introduction and elimination rules for quantifiers and implications. The definitions of `mono_on` and `SUBSET` should be straightforward to translate.


---

## ERDOS_SZEKERES

### Name of formal statement
ERDOS_SZEKERES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ERDOS_SZEKERES = prove
 (`!f:num->real m n.
        (?s. s SUBSET (1..m*n+1) /\ s HAS_SIZE (m + 1) /\ mono_on f (<=) s) \/
        (?s. s SUBSET (1..m*n+1) /\ s HAS_SIZE (n + 1) /\ mono_on f (>=) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. i IN (1..m*n+1)
        ==> ?k. (?s. s SUBSET (1..m*n+1) /\ s HAS_SIZE k /\
                     mono_on f (<=) s /\ i IN s /\ (!j. j IN s ==> i <= j)) /\
                (!l. (?s. s SUBSET (1..m*n+1) /\ s HAS_SIZE l /\
                     mono_on f (<=) s /\ i IN s /\ (!j. j IN s ==> i <= j))
                     ==> l <= k)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM num_MAX] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`1`; `{i:num}`] THEN
      ASM_SIMP_TAC[SUBSET; IN_SING; LE_REFL; HAS_SIZE; FINITE_INSERT] THEN
      SIMP_TAC[FINITE_RULES; CARD_CLAUSES; NOT_IN_EMPTY; ARITH] THEN
      SIMP_TAC[mono_on; IN_SING; REAL_LE_REFL];
      EXISTS_TAC `CARD(1..m*n+1)` THEN
      ASM_MESON_TAC[CARD_SUBSET; FINITE_NUMSEG; HAS_SIZE]];
    REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:num->num` (LABEL_TAC "*" ))] THEN
  ASM_CASES_TAC `?i. i IN (1..m*n+1) /\ m + 1 <= t(i)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:num->bool` STRIP_ASSUME_TAC o CONJUNCT1) THEN
    MP_TAC(ISPEC `s:num->bool` CHOOSE_SUBSET) THEN
    ASM_MESON_TAC[HAS_SIZE; MONO_ON_SUBSET; SUBSET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN (1..m*n+1) ==> 1 <= t i /\ t i <= m` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> MP_TAC th THEN MATCH_MP_TAC MONO_FORALL) THEN
    X_GEN_TAC `i:num` THEN DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `1` o CONJUNCT2) THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[ARITH_RULE `~(m + 1 <= n) ==> n <= m`]] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `{i:num}` THEN
    ASM_SIMP_TAC[SUBSET; IN_SING; LE_REFL; HAS_SIZE; FINITE_INSERT] THEN
    SIMP_TAC[FINITE_RULES; CARD_CLAUSES; NOT_IN_EMPTY; ARITH] THEN
    SIMP_TAC[mono_on; IN_SING; REAL_LE_REFL];
    ALL_TAC] THEN
  DISJ2_TAC THEN
  SUBGOAL_THEN
   `?s k:num. s SUBSET (1..m*n+1) /\ s HAS_SIZE (n + 1) /\
              !i. i IN s ==> t(i) = k`
  MP_TAC THENL
   [MATCH_MP_TAC PIGEONHOLE_LEMMA THEN
    REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG_1; ADD_SUB] THEN
    MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `n * CARD(1..m)` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[CARD_NUMSEG_1] THEN ARITH_TAC] THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[IN_NUMSEG];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:num->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[mono_on] THEN MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
  REWRITE_TAC[LE_LT; real_ge] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  REMOVE_THEN "*" (fun th ->
    MP_TAC(SPEC `i:num` th) THEN MP_TAC(SPEC `j:num` th)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num->bool` STRIP_ASSUME_TAC o CONJUNCT1) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `k + 1` o CONJUNCT2) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(k + 1 <= k)`; GSYM REAL_NOT_LT] THEN
  REWRITE_TAC[CONTRAPOS_THM] THEN
  DISCH_TAC THEN EXISTS_TAC `(i:num) INSERT s` THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    REWRITE_TAC[HAS_SIZE_CLAUSES; GSYM ADD1] THEN ASM_MESON_TAC[NOT_LT];
    ALL_TAC;
    REWRITE_TAC[IN_INSERT];
    ASM_MESON_TAC[IN_INSERT; LE_REFL; LT_IMP_LE; LE_TRANS]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mono_on]) THEN
  REWRITE_TAC[mono_on; IN_INSERT] THEN
  ASM_MESON_TAC[REAL_LE_REFL; REAL_LE_TRANS; REAL_LT_IMP_LE; NOT_LE;
                LT_REFL; LE_TRANS]);;
```

### Informal statement
For all functions `f` from natural numbers to real numbers, and for all natural numbers `m` and `n`, either there exists a set `s` which is a subset of the natural numbers from 1 to `m*n+1`, and `s` has size `m+1`, and `f` is monotonically increasing on `s` with respect to the less than or equal to relation, or there exists a set `s` which is a subset of the natural numbers from 1 to `m*n+1`, and `s` has size `n+1`, and `f` is monotonically decreasing on `s` with respect to the greater than or equal to relation.

### Informal sketch
The proof proceeds by induction and contradiction, using the pigeonhole principle.
- First, a subgoal is set up to show that for every `i` in the range `1..m*n+1`, there exists a `k` such that there exists a set `s` which is a subset of `1..m*n+1` with size `k`, `f` is monotonically increasing on `s`, `i` is in `s`, and `i` is the smallest element in `s`. Furthermore, `k` is the largest such size. This is achieved by induction and simplification tactics.
-  Next, we consider two cases based on the assumption `?i. i IN (1..m*n+1) /\ m + 1 <= t(i)`, where `t(i)` is the largest size of a monotone increasing subset of `1..m*n+1` ending at `i`.
    -  Case 1: `?i. i IN (1..m*n+1) /\ m + 1 <= t(i)`. In this case, we apply `CHOOSE_SUBSET` and use subset and monotonicity properties.
    -  Case 2: `!i. i IN (1..m*n+1) ==> 1 <= t i /\ t i <= m`.  Here, we establish bounds on `t i`.
- Now, a subgoal is introduced expressing the existence of an `s` and `k` such that `s` is a subset of `1..m*n+1`, `s` has size `n+1`, and for all `i` in `s`, `t(i) = k`. This makes it possible to use the pigeonhole principle.
- `PIGEONHOLE_LEMMA` is applied. Some rewriting is done, and inequalities are manipulated.
- `MONO_EXISTS` is applied, and after instantiation, simplification establishes the needed properties using the definition of `mono_on`.
- Finally, contradictions are derived and existential witnesses are constructed through manipulation of `s` and `k`, with the help of monotonicity and other lemmas.

### Mathematical insight
The Erdos-Szekeres theorem guarantees the existence of a monotone subsequence of a certain length in any sufficiently long sequence. This theorem is a foundational result in combinatorics and has applications in various areas of mathematics. It essentially states that in any sequence of `m*n + 1` distinct numbers, there must be either an increasing subsequence of length `m + 1` or a decreasing subsequence of length `n + 1`.

### Dependencies
- `SUBSET`
- `HAS_SIZE`
- `mono_on`
- `num_MAX`
- `IN_SING`
- `LE_REFL`
- `FINITE_INSERT`
- `FINITE_RULES`
- `CARD_CLAUSES`
- `NOT_IN_EMPTY`
- `ARITH`
- `REAL_LE_REFL`
- `CARD_SUBSET`
- `FINITE_NUMSEG`
- `RIGHT_IMP_EXISTS_THM`
- `SKOLEM_THM`
- `MONO_ON_SUBSET`
- `SUBSET_TRANS`
- `MONO_FORALL`
- `PIGEONHOLE_LEMMA`
- `CARD_NUMSEG_1`
- `ADD_SUB`
- `LE_MULT_LCANCEL`
- `FORALL_IN_IMAGE`
- `IN_NUMSEG`
- `MONO_EXISTS`
- `LE_LT`
- `real_ge`
- `REAL_LE_REFL`
- `HAS_SIZE_CLAUSES`
- `ADD1`
- `NOT_LT`
- `IN_INSERT`
- `LE_TRANS`
- `REAL_LE_TRANS`
- `REAL_LT_IMP_LE`
- `NOT_LE`
- `LT_REFL`

### Porting notes (optional)
The proof makes heavy use of the `ASM_MESON_TAC` tactic for automation, which may need to be replaced by explicit reasoning steps in other proof assistants. The use of choice functions (via `SKOLEM_THM` and `X_CHOOSE_THEN`) might require care in systems with different approaches to dependent types or choice.


---

