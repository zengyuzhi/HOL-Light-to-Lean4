# inclusion_exclusion.ml

## Overview

Number of statements: 16

`inclusion_exclusion.ml` formalizes the inclusion-exclusion principle in HOL Light, including both the standard and generalized forms. The file also contains basic set theory lemmas required for the main proofs. It imports definitions and theorems from `Library/products.ml`.


## SUBSET_INSERT_EXISTS

### Name of formal statement
SUBSET_INSERT_EXISTS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUBSET_INSERT_EXISTS = prove
 (`!s x:A t. s SUBSET (x INSERT t) <=>
                s SUBSET t \/ ?u. u SUBSET t /\ s = x INSERT u`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  MATCH_MP_TAC(TAUT `(a /\ ~b ==> c) ==> a ==> b \/ c`) THEN
  DISCH_TAC THEN EXISTS_TAC `s DELETE (x:A)` THEN ASM SET_TAC[]);;
```
### Informal statement
For all sets `s` and `t` of type `A`, and for all elements `x` of type `A`, `s` is a subset of `x INSERT t` if and only if `s` is a subset of `t` or there exists a set `u` such that `u` is a subset of `t` and `s` is equal to `x INSERT u`.

### Informal sketch
The proof proceeds by:
- Applying equality reasoning (`EQ_TAC`) to the top-level equivalence.
- Handling the forward direction (`s SUBSET (x INSERT t) ==> s SUBSET t \/ (?u. u SUBSET t /\ s = x INSERT u)`) automatically using `SET_TAC[]`.
- For the reverse direction (`(s SUBSET t \/ (?u. u SUBSET t /\ s = x INSERT u)) ==> s SUBSET (x INSERT t)`), we use a tautology to re-arrange the goal.
- Discharging the assumption.
- Introducing an existential variable `s DELETE x` as a witness for `u`.
- Applying set tactics (`ASM SET_TAC[]`) to complete the proof.

### Mathematical insight
This theorem relates the subset relation with the insertion of an element into a set. It states that if a set `s` is a subset of `x INSERT t`, then either `s` is already a subset of `t`, or `s` can be formed by inserting `x` into a subset `u` of `t`. It is a fundamental result for reasoning about set inclusion and constructions involving set insertion.

### Dependencies
- `SUBSET`
- `INSERT`
- `DELETE`


---

## FINITE_SUBSETS_RESTRICT

### Name of formal statement
FINITE_SUBSETS_RESTRICT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FINITE_SUBSETS_RESTRICT = prove
 (`!s:A->bool p. FINITE s ==> FINITE {t | t SUBSET s /\ p t}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{t:A->bool | t SUBSET s}` THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[]);;
```
### Informal statement
For any set `s` of type `A -> bool`, if `s` is finite, then the set of subsets `t` of `s` such that `p t` (where `p` is a predicate on sets of type `A -> bool`) holds is also finite.

### Informal sketch
The proof relies on the theorem that the set of subsets of a finite set is finite (`FINITE_SUBSET`).
- Assume `s` is a finite set.
- Show that the set `{t | t SUBSET s /\ p t}` is a subset of the power set of `s` (`{t:A->bool | t SUBSET s}`).
- Apply the theorem `FINITE_POWERSET`, which states that the power set of a finite set is finite.
- Then use `FINITE_SUBSET` to conclude that `{t | t SUBSET s /\ p t}` is also finite because it is a subset of a finite set.

### Mathematical insight
This theorem establishes that if we take a finite set `s` and filter its subsets based on some property `p`, the resulting set of subsets that satisfy `p` will also be finite. This result is useful for reasoning about finiteness in situations where we restrict the subsets under consideration.

### Dependencies
- Theorems: `FINITE_SUBSET`, `FINITE_POWERSET`


---

## INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED

### Name of formal statement
INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED = prove
 (`!P (f:(A->bool)->real) (A:I->bool) (x:I->(A->bool)).
        (!s t. P s /\ P t /\ DISJOINT s t
               ==> f(s UNION t) = f(s) + f(t)) /\
        P {} /\
        (!s t. P s /\ P t ==> P(s INTER t) /\ P(s UNION t) /\ P(s DIFF t)) /\
        FINITE A /\ (!a. a IN A ==> P(x a))
        ==> f(UNIONS(IMAGE x A)) =
            sum {B | B SUBSET A /\ ~(B = {})}
                (\B. (-- &1) pow (CARD B + 1) * f(INTERS(IMAGE x B)))`,
  let lemma = prove
   (`{t | t SUBSET (a INSERT s) /\ P t} =
     {t | t SUBSET s /\ P t} UNION
     {a INSERT t |t| t SUBSET s /\ P(a INSERT t)}`,
    REWRITE_TAC[SUBSET_INSERT_EXISTS] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNION] THEN MESON_TAC[]) in
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_FORALL_THM] THEN
  REWRITE_TAC[IMP_IMP] THEN STRIP_TAC THEN
  MATCH_MP_TAC(MESON[HAS_SIZE]
   `(!n s. s HAS_SIZE n ==> P s) ==> (!s. FINITE s ==> P s)`) THEN
  MATCH_MP_TAC num_WF THEN MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[HAS_SIZE_CLAUSES; LEFT_IMP_EXISTS_THM] THEN CONJ_TAC THENL
   [DISCH_THEN(K ALL_TAC) THEN GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[UNIONS_0; IMAGE_CLAUSES; SUBSET_EMPTY; TAUT `~(p /\ ~p)`] THEN
    ASM_REWRITE_TAC[EMPTY_GSPEC; SUM_CLAUSES] THEN REPEAT STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPECL [`{}:A->bool`; `{}:A->bool`])) THEN
    ASM_SIMP_TAC[UNION_EMPTY; DISJOINT_EMPTY] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`A0:I->bool`; `a:I`; `A:I->bool`] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN SUBST1_TAC THEN X_GEN_TAC  `x:I->A->bool` THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN STRIP_TAC THEN
  REWRITE_TAC[IMAGE_CLAUSES; UNIONS_INSERT] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `(f(x a) + f(UNIONS (IMAGE (x:I->(A->bool)) A))) -
              f(x a INTER UNIONS (IMAGE x A)):real` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `P(x a) /\ P(UNIONS(IMAGE (x:I->(A->bool)) A))`
    MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `!b. b IN A ==> P((x:I->(A->bool)) b)` THEN
      SUBGOAL_THEN `FINITE(A:I->bool)` MP_TAC THENL
       [ASM_MESON_TAC[HAS_SIZE]; ALL_TAC] THEN
      SPEC_TAC(`A:I->bool`,`u:I->bool`) THEN
      MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
      ASM_SIMP_TAC[IMAGE_CLAUSES; UNIONS_0; UNIONS_INSERT; FORALL_IN_INSERT];
      SPEC_TAC(`UNIONS(IMAGE (x:I->(A->bool)) A)`,`t:A->bool`) THEN
      SPEC_TAC(`(x:I->(A->bool)) a`,`s:A->bool`) THEN
      REPEAT STRIP_TAC THEN
      UNDISCH_TAC `!s t:A->bool. P s /\ P t /\ DISJOINT s t
                                 ==> f(s UNION t):real = f(s) + f(t)` THEN
      DISCH_THEN(fun th ->
     MP_TAC(ISPECL [`s INTER t:A->bool`; `t DIFF s:A->bool`] th) THEN
     MP_TAC(ISPECL [`s:A->bool`; `t DIFF s:A->bool`] th)) THEN
     ASM_SIMP_TAC[SET_RULE `s UNION (t DIFF s) = s UNION t`;
                  SET_RULE `(s INTER t) UNION (t DIFF s) = t`] THEN
     REPEAT(ANTS_TAC THENL [SET_TAC[]; DISCH_TAC]) THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[INTER_UNIONS; SIMPLE_IMAGE; GSYM IMAGE_o; o_DEF] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LT] THEN
  DISCH_THEN(MP_TAC o SPEC `A:I->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th ->
    MP_TAC(ISPEC `\s. (x:I->(A->bool)) a INTER x s` th) THEN
    MP_TAC(ISPEC `x:I->(A->bool)` th)) THEN
  ASM_SIMP_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [HAS_SIZE]) THEN
  REWRITE_TAC[lemma] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_UNION o rand o snd) THEN
  ANTS_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    ASM_SIMP_TAC[FINITE_SUBSETS_RESTRICT; FINITE_IMAGE] THEN
    REWRITE_TAC[GSYM SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC[IN_DISJOINT; EXISTS_IN_GSPEC] THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN
    REWRITE_TAC[EXISTS_IN_GSPEC] THEN ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; REAL_ARITH
   `(fa + s) - fas:real = s + s' <=> fa - fas = s'`] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `f((x:I->(A->bool)) a) +
              sum {B | B SUBSET A /\ ~(B = {})}
                  (\B. --(&1) pow (CARD B) *
                       f(INTERS(IMAGE x (a INSERT B))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_ARITH `x - a:real = x + b <=> b = --a`] THEN
    REWRITE_TAC[GSYM SUM_NEG] THEN MATCH_MP_TAC SUM_EQ THEN
    REWRITE_TAC[IMAGE_CLAUSES; INTERS_INSERT; o_DEF; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; REAL_MUL_RNEG; REAL_MUL_LNEG] THEN
    REWRITE_TAC[REAL_NEG_NEG; REAL_MUL_RID] THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[INTERS_IMAGE] THEN ASM SET_TAC[];
    REWRITE_TAC[SET_RULE `{s | P s /\ ~(s = e)} = {s | P s} DELETE e`] THEN
    ASM_SIMP_TAC[SUM_DELETE_CASES; GSYM DELETE; FINITE_POWERSET] THEN
    REWRITE_TAC[IN_ELIM_THM; EMPTY_SUBSET; IMAGE_CLAUSES] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SIMPLE_IMAGE_GEN] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o rand o snd) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[o_DEF; INTERS_1; CARD_CLAUSES; real_pow; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_SUB_ADD2] THEN MATCH_MP_TAC SUM_EQ THEN
    REWRITE_TAC[FORALL_IN_GSPEC; REAL_POW_ADD; REAL_POW_1] THEN
    X_GEN_TAC `B:I->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `FINITE(B:I->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; REAL_POW_ADD; real_pow] THEN
    COND_CASES_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IMAGE_CLAUSES; real_pow] THEN REAL_ARITH_TAC]);;
```

### Informal statement
For any type `I` and `A: I -> bool`, any function `f` mapping sets of type `(A -> bool)` to real numbers, and any function `x` mapping elements of type `I` to sets of type `(A -> bool)`; if the following conditions hold:
1. For any sets `s` and `t` of type `(A -> bool)`, if `P s`, `P t`, and `s` and `t` are disjoint, then `f(s UNION t) = f(s) + f(t)`.
2. `P` holds for the empty set.
3. For any sets `s` and `t` of type `(A -> bool)`, if `P s` and `P t`, then `P(s INTER t)`, `P(s UNION t)`, and `P(s DIFF t)`.
4. `A` is a finite set.
5. For all `a` of type `I`, if `a IN A`, then `P(x a)`.
Then, `f` applied to the union of the images of `x` over `A` is equal to the sum over all non-empty subsets `B` of `A`, of `(-1)^(cardinality of B + 1) * f` applied to the intersection of the images of `x` over `B`.

### Informal sketch
The proof proceeds by induction on the size of the set `A`.
- **Base Case:** When `A` is empty, the union of `IMAGE x A` is the empty set, and the sum over non-empty subsets of `A` is zero. The additivity property of `f` is used.
- **Inductive Step:** Assume the theorem holds for all sets of size `n`. We want to show that it holds for a set `A` of size `n+1`.
  - Let `A` be `a INSERT s`, where `a` is an element and `s` is a set of size `n`.
  - Decompose `UNIONS(IMAGE x A)` into `x a UNION UNIONS(IMAGE x s)`.
  - Apply the additivity property of `f` to `f(x a UNION UNIONS(IMAGE x s))`, giving `f(x a) + f(UNIONS(IMAGE x s)) - f(x a INTER UNIONS(IMAGE x s))`.
  - Apply the inductive hypothesis to `f(UNIONS(IMAGE x s))`.
  - Rewrite `x a INTER UNIONS(IMAGE x s)` using distribution laws and `IMAGE`.
  - Apply the inductive hypothesis again to the term involving the intersection.
  - Manipulate the resulting sums using combinatorial identities like `lemma`, which rewrites subsets of `a INSERT s` into the union of subsets of `s` and subsets of `a INSERT t` for `t` subset `s`, and the binomial theorem to obtain the desired result.

### Mathematical insight
This theorem is a generalization of the inclusion-exclusion principle for real-valued functions. The inclusion-exclusion principle is a counting technique that generalizes the familiar method of obtaining the size of a union of two sets: to find the size of `A UNION B`, add the sizes of `A` and `B`, and then subtract the size of `A INTER B` to correct for double counting. The theorem here extends this to functions `f` that are additive on disjoint sets, and to unions that may not be disjoint but satisfy condition `P`.

### Dependencies
- `SUBSET_INSERT_EXISTS`
- `EXTENSION`
- `IN_ELIM_THM`
- `IN_UNION`
- `HAS_SIZE`
- `num_WF`
- `num_INDUCTION`
- `HAS_SIZE_CLAUSES`
- `LEFT_IMP_EXISTS_THM`
- `UNIONS_0`
- `IMAGE_CLAUSES`
- `SUBSET_EMPTY`
- `TAUT \`~(p /\ ~p)\``
- `EMPTY_GSPEC`
- `SUM_CLAUSES`
- `UNION_EMPTY`
- `DISJOINT_EMPTY`
- `FORALL_IN_INSERT`
- `IMAGE_CLAUSES`
- `UNIONS_INSERT`
- `EQ_TRANS`
- `FINITE_INDUCT_STRONG`
- `INTER_UNIONS`
- `SIMPLE_IMAGE`
- `GSYM IMAGE_o`
- `o_DEF`
- `LT`
- `lemma`
- `SUM_UNION`
- `SIMPLE_IMAGE_GEN`
- `FINITE_SUBSETS_RESTRICT`
- `FINITE_IMAGE`
- `IN_DISJOINT`
- `EXISTS_IN_GSPEC`
- `CONJ_SYM`
- `NOT_INSERT_EMPTY`
- `SUM_NEG`
- `SUM_EQ`
- `INTERS_INSERT`
- `REAL_POW_ADD`
- `REAL_POW_1`
- `REAL_MUL_RNEG`
- `REAL_MUL_LNEG`
- `REAL_NEG_NEG`
- `REAL_MUL_RID`
- `INTERS_IMAGE`
- `SET_RULE \`{s | P s /\ ~(s = e)} = {s | P s} DELETE e\``
- `SUM_DELETE_CASES`
- `GSYM DELETE`
- `FINITE_POWERSET`
- `EMPTY_SUBSET`
- `INTERS_1`
- `CARD_CLAUSES`
- `real_pow`
- `REAL_MUL_LID`
- `REAL_SUB_ADD2`
- `FINITE_SUBSET`

### Porting notes (optional)
- The proof relies heavily on rewriting and arithmetic simplification using `REAL_ARITH_TAC`. Ensure that the target proof assistant has similar capabilities for handling real arithmetic and set theory efficiently.
- The tactic `MESON` is used for automated reasoning with set theory, implication, and quantifiers. This may need replacement by more explicit tactics in other systems.
- The use of `GSPEC` and related set operations requires a well-developed set theory library in the target assistant.


---

## INCLUSION_EXCLUSION_REAL_RESTRICTED

### Name of formal statement
INCLUSION_EXCLUSION_REAL_RESTRICTED

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INCLUSION_EXCLUSION_REAL_RESTRICTED = prove
 (`!P (f:(A->bool)->real) (A:(A->bool)->bool).
        (!s t. P s /\ P t /\ DISJOINT s t
               ==> f(s UNION t) = f(s) + f(t)) /\
        P {} /\
        (!s t. P s /\ P t ==> P(s INTER t) /\ P(s UNION t) /\ P(s DIFF t)) /\
        FINITE A /\ (!a. a IN A ==> P(a))
        ==> f(UNIONS A) =
            sum {B | B SUBSET A /\ ~(B = {})}
                (\B. (-- &1) pow (CARD B + 1) * f(INTERS B))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`P:(A->bool)->bool`; `f:(A->bool)->real`;
                 `A:(A->bool)->bool`; `\x:A->bool. x`]
        INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED) THEN
  ASM_REWRITE_TAC[IMAGE_ID]);;
```

### Informal statement
For any predicate `P` on sets of type `A->bool`, any function `f` from sets of type `A->bool` to real numbers, and any set of sets `A` of type `(A->bool)->bool`, if the following conditions hold:
1.  For all sets `s` and `t`, if `P s`, `P t`, and `s` and `t` are disjoint, then `f(s UNION t) = f(s) + f(t)`.
2.  `P {}` holds (the empty set has property `P`).
3.  For all sets `s` and `t`, if `P s` and `P t`, then `P(s INTER t)`, `P(s UNION t)`, and `P(s DIFF t)` all hold.
4.  `A` is a finite set of sets.
5.  For all `a`, if `a IN A`, then `P a` holds.

Then `f(UNIONS A)` is equal to the sum over all non-empty subsets `B` of `A` of `(-- &1) pow (CARD B + 1) * f(INTERS B)`.

### Informal sketch
The proof proceeds by:
- Stripping the quantifiers and assumptions.
- Applying the indexed version of the Inclusion-Exclusion principle (`INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED`) specialized to the given predicate `P`, function `f`, set of sets `A`, and using the identity function `\x:A->bool. x` as the index.
- Rewriting using the expansion of `IMAGE_ID`, likely to simplify the instantiation of the indexed theorem.

### Mathematical insight
This theorem provides a restricted version of the Inclusion-Exclusion Principle for real-valued functions defined on sets. The restriction involves a predicate `P` that must be satisfied by the sets involved, and enforces properties such as closure under intersection, union, and difference. The theorem expresses the value of the function `f` applied to the union of a finite set of sets `A` (i.e., `UNIONS A`) as a sum involving the values of `f` applied to the intersection of the subsets of `A` and the cardinality of these subsets, reminiscent of the standard Inclusion-Exclusion formula, but weighted by `(-- &1) pow (CARD B + 1)`.

### Dependencies
- `INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED`
- `IMAGE_ID` (definition)
- `CARD`
- `UNIONS`
- `INTERS`
- `UNION`
- `INTER`
- `DIFF`
- `SUBSET`
- `IN`
- `pow`


---

## INCLUSION_EXCLUSION_REAL_INDEXED

### Name of formal statement
INCLUSION_EXCLUSION_REAL_INDEXED

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INCLUSION_EXCLUSION_REAL_INDEXED = prove
 (`!(f:(A->bool)->real) (A:I->bool) (x:I->(A->bool)).
        (!s t. DISJOINT s t ==> f(s UNION t) = f(s) + f(t)) /\ FINITE A
        ==> f(UNIONS(IMAGE x A)) =
            sum {B | B SUBSET A /\ ~(B = {})}
                (\B. (-- &1) pow (CARD B + 1) * f(INTERS(IMAGE x B)))`,
  MP_TAC(ISPEC
   `\x:A->bool. T` INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED) THEN
  REWRITE_TAC[]);;
```
### Informal statement
For any function `f` from sets of type `A` to real numbers, any function `A` from type `I` to booleans, and any function `x` from type `I` to sets of elements of type `A`, the following holds: If `f` is disjointly additive (i.e., for all sets `s` and `t`, if `s` and `t` are disjoint, then `f(s UNION t) = f(s) + f(t)`) and the set `A` is finite, then `f(UNIONS(IMAGE x A))` is equal to the sum over all non-empty subsets `B` of `A` of `(-1)` to the power of `CARD B + 1` times `f(INTERS(IMAGE x B))`.

### Informal sketch
The proof uses the theorem `INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED` by specializing a variable. Specifically, it instantiates `INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED` with `\x:A->bool. T`. Then, the goal is rewritten using the instantiated theorem. This simplifies the original inclusion-exclusion principle with a trivial restriction.

### Mathematical insight
This theorem generalizes the inclusion-exclusion principle to unrestrictedly additive functions. It provides a formula for calculating the function value of the union of sets, using the function values of the intersections of subsets of the index set. This is a generalization of the standard inclusion-exclusion principle for counting elements in a union of sets and is applicable in situations where the function `f` satisfies a form of additivity over disjoint sets.

### Dependencies
- `INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED`

### Porting notes (optional)
The main challenge in porting this theorem lies in ensuring that the concepts of `DISJOINT`, `UNION`, `FINITE`, `UNIONS`, `IMAGE`, `SUBSET`, `CARD`, `INTERS`, and `sum` over subsets are appropriately defined and that the discharging of the assumption `DISJOINT s t ==> f(s UNION t) = f(s) + f(t)` can be done efficiently by rewriting, or other suitable methods provided by the target proof assistant. Handling power function for real numbers may also require attention.


---

## INCLUSION_EXCLUSION_REAL

### Name of formal statement
INCLUSION_EXCLUSION_REAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INCLUSION_EXCLUSION_REAL = prove
 (`!(f:(A->bool)->real) (A:(A->bool)->bool).
        (!s t. DISJOINT s t ==> f(s UNION t) = f(s) + f(t)) /\ FINITE A
        ==> f(UNIONS A) =
            sum {B | B SUBSET A /\ ~(B = {})}
                (\B. (-- &1) pow (CARD B + 1) * f(INTERS B))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:(A->bool)->real`; `A:(A->bool)->bool`; `\x:A->bool. x`]
        INCLUSION_EXCLUSION_REAL_INDEXED) THEN
  ASM_REWRITE_TAC[IMAGE_ID]);;
```

### Informal statement
For any function `f` from sets of type `A` to real numbers (where sets of type `A` are represented as boolean predicates over type `A`), and for any finite set `A` of sets of type `A` (where `A` is represented as a boolean predicate over sets of type `A`), if `f` is additive over disjoint sets (i.e., for all sets `s` and `t`, if `s` and `t` are disjoint, then `f(s UNION t) = f(s) + f(t)`), then `f(UNIONS A)` equals the sum over all non-empty subsets `B` of `A` of `(-1)` raised to the power of `CARD B + 1` times `f(INTERS B)`.

### Informal sketch
- The proof proceeds by stripping the quantifiers and assumptions.
- It then applies `INCLUSION_EXCLUSION_REAL_INDEXED`, specializing it to `f`, `A`, and the identity function `\x:A->bool. x`.
- Finally, it rewrites using `IMAGE_ID`. This step likely simplifies the expression after applying `INCLUSION_EXCLUSION_REAL_INDEXED` using the identity function. The core idea is to reduce the problem to the indexed version of the inclusion-exclusion principle.

### Mathematical insight
The theorem expresses the inclusion-exclusion principle for real-valued functions that are additive over disjoint sets. It relates the value of the function on the union of a finite collection of sets to a sum involving the function applied to the intersection of all non-empty subsets of the collection.  This principle is a fundamental tool in combinatorics and probability theory, allowing to precisely calculate the size of a union of sets by accounting for overlaps.

### Dependencies
- `INCLUSION_EXCLUSION_REAL_INDEXED`
- `DISJOINT`
- `UNION`
- `FINITE`
- `UNIONS`
- `SUBSET`
- `CARD`
- `INTERS`
- `IMAGE_ID`

### Porting notes (optional)
- The representation of sets as boolean predicates may need adaptation depending on the target proof assistant.
- The `IMAGE_ID` rewrite suggests a simplification step relying on properties of the identity function and set operations. Ensure that the target system has similar rewrite capabilities.


---

## INCLUSION_EXCLUSION

### Name of formal statement
INCLUSION_EXCLUSION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INCLUSION_EXCLUSION = prove
 (`!s:(A->bool)->bool.
        FINITE s /\ (!k. k IN s ==> FINITE k)
        ==> &(CARD(UNIONS s)) =
                sum {t | t SUBSET s /\ ~(t = {})}
                    (\t. (-- &1) pow (CARD t + 1) * &(CARD(INTERS t)))`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`\s:A->bool. FINITE s`; `\s:A->bool. &(CARD s)`;
    `s:(A->bool)->bool`] INCLUSION_EXCLUSION_REAL_RESTRICTED) THEN
  ASM_SIMP_TAC[FINITE_INTER; FINITE_UNION; FINITE_DIFF; FINITE_EMPTY] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  SIMP_TAC[CARD_UNION; DISJOINT; REAL_OF_NUM_ADD]);;
```
### Informal statement
For any set `s` of sets such that `s` is finite and every element `k` of `s` is finite, the cardinality of the union of all sets in `s` is equal to the sum, over all non-empty subsets `t` of `s`, of `(-1)^(cardinality of t + 1)` multiplied by the cardinality of the intersection of all sets in `t`.

### Informal sketch
*   The proof starts by stripping the quantifiers and assumptions using `REPEAT STRIP_TAC`.
*   It then applies a special case of the inclusion-exclusion principle for real-valued functions, `INCLUSION_EXCLUSION_REAL_RESTRICTED`, to the cardinality function. This is achieved by specializing `INCLUSION_EXCLUSION_REAL_RESTRICTED` to the finite set `s` and the chosen function `\s:A->bool. &(CARD s)`.
*   Simplification is then performed using finiteness properties of intersection, union, difference, and the empty set (`FINITE_INTER`, `FINITE_UNION`, `FINITE_DIFF`, `FINITE_EMPTY`).
*   The discharged assumption is then matched and applied using `DISCH_THEN MATCH_MP_TAC`.
*   Finally, further simplification is applied, using the cardinality of a union (`CARD_UNION`), the definition of disjoint sets (`DISJOINT`), and the addition of real numbers representing cardinalities (`REAL_OF_NUM_ADD`).

### Mathematical insight
This is a version of the inclusion-exclusion principle, a fundamental result in combinatorics. It relates the cardinality of a union of sets to the cardinalities of intersections of its subsets. The theorem provides an explicit formula for calculating the size of the union by summing over the sizes of the intersections, with alternating signs to correct for overcounting.

### Dependencies
*   `INCLUSION_EXCLUSION_REAL_RESTRICTED`
*   `FINITE_INTER`
*   `FINITE_UNION`
*   `FINITE_DIFF`
*   `FINITE_EMPTY`
*   `CARD_UNION`
*   `DISJOINT`
*   `REAL_OF_NUM_ADD`


---

## INCLUSION_EXCLUSION_USUAL

### Name of formal statement
INCLUSION_EXCLUSION_USUAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INCLUSION_EXCLUSION_USUAL = prove
 (`!s:(A->bool)->bool.
        FINITE s /\ (!k. k IN s ==> FINITE k)
        ==> &(CARD(UNIONS s)) =
                sum (1..CARD s) (\n. (-- &1) pow (n + 1) *
                                     sum {t | t SUBSET s /\ t HAS_SIZE n}
                                         (\t. &(CARD(INTERS t))))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[INCLUSION_EXCLUSION] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) (ISPEC `CARD` SUM_IMAGE_GEN) o
     lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_SUBSETS_RESTRICT] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(MESON[] `s = t /\ sum t f = sum t g ==> sum s f = sum t g`) THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_IMAGE; IN_NUMSEG; IN_ELIM_THM] THEN
    REWRITE_TAC[ARITH_RULE `1 <= a <=> ~(a = 0)`] THEN
    ASM_MESON_TAC[CHOOSE_SUBSET; CARD_SUBSET; FINITE_SUBSET; CARD_EQ_0;
                  HAS_SIZE];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_NUMSEG] THEN
  STRIP_TAC THEN REWRITE_TAC[SUM_LMUL] THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[IN_ELIM_THM; HAS_SIZE] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_MESON_TAC[CARD_EQ_0; ARITH_RULE `~(1 <= 0)`; FINITE_SUBSET]);;
```

### Informal statement
For any set `s` of sets, where `s` is finite and every element `k` of `s` is finite, the cardinality of the union of all sets in `s` equals the sum from 1 to the cardinality of `s` of the following expression indexed by `n`: `(-- &1)` raised to the power of `(n + 1)`, multiplied by the sum over all subsets `t` of `s` that have size `n`, of the cardinality of the intersection of all sets in `t`.

### Informal sketch
The proof proceeds as follows:
- Apply the `INCLUSION_EXCLUSION` theorem.
- Rewrite using `SUM_IMAGE_GEN`, `FINITE_SUBSETS_RESTRICT`.
- Use a congruence rule to rewrite the sum over `s` to a sum over `t`.
- Split into two subgoals and prove them separately, one using `EXTENSION`, `IN_IMAGE`, `IN_NUMSEG`, `ARITH_RULE`, `CHOOSE_SUBSET`, `CARD_SUBSET`, `FINITE_SUBSET`, `CARD_EQ_0`, and `HAS_SIZE`, and the other using `SUM_EQ`, `IN_NUMSEG`, `SUM_LMUL`, `IN_ELIM_THM`, `HAS_SIZE`, `EXTENSION`, `CARD_EQ_0`, `ARITH_RULE`, and `FINITE_SUBSET`.

### Mathematical insight
This theorem provides a conventional form of the inclusion-exclusion principle. It states that the cardinality of a union of finitely many finite sets can be computed by summing terms that involve the cardinalities of intersections of subfamilies of these sets. The inclusion-exclusion principle is a fundamental result in combinatorics with wide-ranging applications.

### Dependencies
- `INCLUSION_EXCLUSION`
- `FINITE_SUBSETS_RESTRICT`
- `SUM_IMAGE_GEN`
- `EXTENSION`
- `IN_IMAGE`
- `IN_NUMSEG`
- `IN_ELIM_THM`
- `ARITH_RULE`
- `CHOOSE_SUBSET`
- `CARD_SUBSET`
- `FINITE_SUBSET`
- `CARD_EQ_0`
- `HAS_SIZE`
- `SUM_EQ`
- `SUM_LMUL`


---

## FINITE_SUBSETS_RESTRICT

### Name of formal statement
FINITE_SUBSETS_RESTRICT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FINITE_SUBSETS_RESTRICT = prove
 (`!s:A->bool p. FINITE s ==> FINITE {t | t SUBSET s /\ p t}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{t:A->bool | t SUBSET s}` THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[]);;
```

### Informal statement
For any set `s` of type `A -> bool`, if `s` is finite, then the set of subsets `t` of `s` that satisfy the predicate `p` is finite, where `p` is a function of type `(A -> bool) -> bool`.

### Informal sketch
The proof proceeds as follows:
- Assume that `s` is a finite set.
- Apply `FINITE_SUBSET` to reduce the problem to showing that the set `{t | t SUBSET s /\ p t}` is a subset of the power set of `s`.
- Instantiate an existential quantifier with the set `{t:A->bool | t SUBSET s}`.
- Simplify using `FINITE_POWERSET` to show that the power set of `s` is finite.
- Use `SET_TAC[]` to discharge the set theory conditions.

### Mathematical insight
This theorem states that if we have a finite set `s`, then the set of all subsets of `s` that satisfy some predicate `p` is also finite. This is a basic combinatorial result arising from the fact that a finite set only has finitely many subsets.

### Dependencies
- Theorems: `FINITE_SUBSET`, `FINITE_POWERSET`


---

## CARD_ADJUST_LEMMA

### Name of formal statement
CARD_ADJUST_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CARD_ADJUST_LEMMA = prove
 (`!f:A->B s x y.
        FINITE s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        x = y + CARD (IMAGE f s)
        ==> x = y + CARD s`,
  MESON_TAC[CARD_IMAGE_INJ]);;
```
### Informal statement
For any function `f` from set `A` to set `B`, and any sets `s`, `x`, and `y`, if `s` is finite and `f` is injective on `s` (i.e., for all `x` and `y` in `s`, if `f(x) = f(y)` then `x = y`) and `x = y + CARD (IMAGE f s)`, then `x = y + CARD s`.

### Informal sketch
The proof uses the theorem `CARD_IMAGE_INJ`.

*   The main idea is that since `f` is injective on `s`, the cardinality of the image of `s` under `f` is the same as the cardinality of `s`.
*   We are given `x = y + CARD (IMAGE f s)`.
*   Because `f` is injective on `s`, we know that `CARD (IMAGE f s) = CARD s`.  This is exactly what `CARD_IMAGE_INJ` says in this context.
*   Substituting, we get `x = y + CARD s`.

### Mathematical insight
The theorem states that if we have a finite set `s` and a function `f` that is injective on `s`, and `x` is equal to `y` plus the cardinality of the image of `s` under `f`, then `x` is also equal to `y` plus the cardinality of `s`. It connects size of a set and its image under an injective function.

### Dependencies
- Theorems: `CARD_IMAGE_INJ`


---

## CARD_SUBSETS_STEP

### Name of formal statement
CARD_SUBSETS_STEP

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CARD_SUBSETS_STEP = prove
 (`!x:A s. FINITE s /\ ~(x IN s) /\ u SUBSET s
           ==> CARD {t | t SUBSET (x INSERT s) /\ u SUBSET t /\ ODD(CARD t)} =
                 CARD {t | t SUBSET s /\ u SUBSET t /\ ODD(CARD t)} +
                 CARD {t | t SUBSET s /\ u SUBSET t /\ EVEN(CARD t)} /\
               CARD {t | t SUBSET (x INSERT s) /\ u SUBSET t /\ EVEN(CARD t)} =
                 CARD {t | t SUBSET s /\ u SUBSET t /\ EVEN(CARD t)} +
                 CARD {t | t SUBSET s /\ u SUBSET t /\ ODD(CARD t)}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(INST_TYPE[`:A`,`:B`] CARD_ADJUST_LEMMA) THEN
  EXISTS_TAC `\u. (x:A) INSERT u` THEN
  ASM_SIMP_TAC[FINITE_SUBSETS_RESTRICT] THEN
  (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
   CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_UNION_EQ THEN
   ASM_SIMP_TAC[FINITE_SUBSETS_RESTRICT; FINITE_INSERT] THEN CONJ_TAC THENL
    [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER] THEN
     REWRITE_TAC[TAUT `~(a /\ b) <=> b ==> ~a`; FORALL_IN_IMAGE] THEN
     ASM SET_TAC[];
     ALL_TAC] THEN
   GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t:A->bool` THEN
   REWRITE_TAC[IN_ELIM_THM; IN_UNION; SUBSET_INSERT_EXISTS] THEN
   REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
   REWRITE_TAC[RIGHT_OR_DISTRIB; LEFT_AND_EXISTS_THM] THEN AP_TERM_TAC THEN
   AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
   X_GEN_TAC `v:A->bool` THEN
   ASM_CASES_TAC `t = (x:A) INSERT v` THEN ASM_REWRITE_TAC[] THEN
   ASM_CASES_TAC `(v:A->bool) SUBSET s` THEN ASM_REWRITE_TAC[] THEN
   BINOP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
   ASM_MESON_TAC[CARD_CLAUSES; EVEN; NOT_ODD; FINITE_SUBSET; SUBSET] THEN
   ASM_MESON_TAC[CARD_CLAUSES; EVEN; NOT_ODD; FINITE_SUBSET; SUBSET]));;
```

### Informal statement
For any set `x` of type `A`, and any sets `s` and `u` of type `A`, if `s` is finite, `x` is not an element of `s`, and `u` is a subset of `s`, then the cardinality of the set of subsets `t` of `x INSERT s` such that `u` is a subset of `t` and `CARD t` is odd, is equal to the sum of the cardinality of the set of subsets `t` of `s` such that `u` is a subset of `t` and `CARD t` is odd, and the cardinality of the set of subsets `t` of `s` such that `u` is a subset of `t` and `CARD t` is even; and the cardinality of the set of subsets `t` of `x INSERT s` such that `u` is a subset of `t` and `CARD t` is even, is equal to the sum of the cardinality of the set of subsets `t` of `s` such that `u` is a subset of `t` and `CARD t` is even, and the cardinality of the set of subsets `t` of `s` such that `u` is a subset of `t` and `CARD t` is odd.

### Informal sketch
The proof proceeds as follows:
- The theorem establishes a recurrence relation expressing the number of odd and even cardinality subsets of `x INSERT s` containing `u` in terms of odd and even cardinality subsets of `s` containing `u`.
- Start by stripping the quantifiers and assumptions.
- Apply `CARD_ADJUST_LEMMA` after instantiating the type variables
- Use `EXISTS_TAC` to introduce an existential quantifier.
- Simplify using `FINITE_SUBSETS_RESTRICT`.
- Split the goal into two subgoals using `CONJ_TAC`, addressing the odd and even cardinality cases separately.
- For the first subgoal (odd cardinality), rewrite by symmetry and apply `CARD_UNION_EQ`. Simplify using `FINITE_SUBSETS_RESTRICT` and `FINITE_INSERT`.
- Split the goal again using `CONJ_TAC`.
- Simplify using set theory lemmas like `EXTENSION`, `NOT_IN_EMPTY`, `IN_INTER` and `FORALL_IN_IMAGE`.
- Generalize using `EXTENSION` and `X_GEN_TAC`.
- Rewrite using `IN_ELIM_THM`, `IN_UNION`, `SUBSET_INSERT_EXISTS`, `IN_IMAGE`, `RIGHT_OR_DISTRIB`, and `LEFT_AND_EXISTS_THM`. Apply `AP_TERM_TAC` twice then `FUN_EQ_THM`.
- Consider the two cases where `t` equals `x INSERT v` where `v` is a boolean function.
- Case split where `v` is subset of `s`.
- Apply binomial theorems and other set theory lemmas with `ASM_MESON_TAC` to prove that the statement is true.

### Mathematical insight
This theorem decomposes the count of odd and even cardinality subsets of a set, constrained to contain a specific subset `u`, into the counts of odd and even cardinality subsets of a smaller set. The underlying idea is that each subset of `x INSERT s` either contains `x` or does not. By conditioning on whether `x` is in a given subset `t`, the problem reduces to counting subsets of `s`. This is a standard combinatorial technique.

### Dependencies

- `CARD_ADJUST_LEMMA`
- `FINITE_SUBSETS_RESTRICT`
- `CARD_UNION_EQ`
- `FINITE_INSERT`
- `EXTENSION`
- `NOT_IN_EMPTY`
- `IN_INTER`
- `FORALL_IN_IMAGE`
- `IN_ELIM_THM`
- `IN_UNION`
- `SUBSET_INSERT_EXISTS`
- `IN_IMAGE`
- `RIGHT_OR_DISTRIB`
- `LEFT_AND_EXISTS_THM`
- `FUN_EQ_THM`
- `CARD_CLAUSES`
- `EVEN`
- `NOT_ODD`
- `FINITE_SUBSET`
- `SUBSET`

### Porting notes (optional)
The proof relies heavily on MESON and set rewriting. Ensure the target proof assistant has similar automation for set theory reasoning. The handling of boolean functions representing sets might also require some adaptation depending on the specific features of the target system. The binomial reasoning should be straightforward in most systems.


---

## CARD_SUBSUPERSETS_EVEN_ODD

### Name of formal statement
CARD_SUBSUPERSETS_EVEN_ODD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CARD_SUBSUPERSETS_EVEN_ODD = prove
 (`!s u:A->bool.
        FINITE u /\ s PSUBSET u
        ==> CARD {t | s SUBSET t /\ t SUBSET u /\ EVEN(CARD t)} =
            CARD {t | s SUBSET t /\ t SUBSET u /\ ODD(CARD t)}`,
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> b /\ a /\ c`] THEN
  REPEAT GEN_TAC THEN WF_INDUCT_TAC `CARD(u:A->bool)` THEN
  REWRITE_TAC[PSUBSET_ALT] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (SET_RULE
   `x IN s ==> s = x INSERT (s DELETE x)`)) THEN
  MP_TAC(SET_RULE `~((x:A) IN (u DELETE x))`) THEN
  ABBREV_TAC `v:A->bool = u DELETE x` THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE v /\ (s:A->bool) SUBSET v` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[FINITE_INSERT]; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_SUBSETS_STEP] THEN ASM_CASES_TAC `s:A->bool = v` THENL
   [REWRITE_TAC[CONJ_ASSOC; SUBSET_ANTISYM_EQ] THEN MATCH_ACCEPT_TAC ADD_SYM;
    ASM_SIMP_TAC[CARD_CLAUSES; LT; PSUBSET]]);;
```

### Informal statement
For any predicate `s` and `u` over a type `A`, if `u` is finite and `s` is a proper subset of `u`, then the cardinality of the set of all predicates `t` such that `s` is a subset of `t`, `t` is a subset of `u`, and the cardinality of `t` is even, is equal to the cardinality of the set of all predicates `t` such that `s` is a subset of `t`, `t` is a subset of `u`, and the cardinality of `t` is odd.

### Informal sketch
The proof proceeds by induction on the cardinality of `u`.

- **Base Case:** When the cardinality of `u` is 0, `u` is the empty set. Since `s` is a proper subset of `u`, `s` must also be the empty set. The sets `{t | s SUBSET t /\ t SUBSET u /\ EVEN(CARD t)}` and `{t | s SUBSET t /\ t SUBSET u /\ ODD(CARD t)}` both contain only the empty set, where the cardinality is 0 which is even. Therefore, both sets contain only one element (the empty set `empty:A->bool`), and their cardinalities are equal (1 = 1).

- **Inductive Step:** Assume that the theorem holds for all `u` with cardinality `n`. We need to show that it holds for `u` with cardinality `n+1`. Let `u` be a finite set with cardinality `n+1`, and let `s` be a proper subset of `u`. Choose an element `x` in `u` but not in `s`. Consider `v = u DELETE x`. We have `FINITE v` and `s SUBSET v`.
  - Case `s = v`: The tactic `ASM_SIMP_TAC[CARD_CLAUSES]` deals with the case when `s = v`. In this case it can be seen that the numbers of even and odd super-sets are equal.
  - Case `s` is a *proper* subset of `v`: By the inductive hypothesis, the theorem holds for `v` and `s`. We can relate the subsets of `u` that contain `s` to the subsets of `v` that contain `s`. Specifically, each subset `t` of `v` that contains `s` corresponds to two subsets of `u` that contain `s`: `t` itself and `t INSERT x` (i.e. `t` union `{x}`). If `CARD t` is even then `CARD (t INSERT x)` is odd, and vice versa. Therefore, the number of even-cardinality subsets of `u` that contain `s` is equal to the number of odd-cardinality subsets of `u` that contain `s`.

### Mathematical insight
The theorem states that if `s` is a proper subset of a finite set `u`, then the number of subsets of `u` that contain `s` and have even cardinality is equal to the number of subsets of `u` that contain `s` and have odd cardinality. It highlights a symmetry in the distribution of even and odd sized subsets bounded by `s` and `u`.

### Dependencies
- `FINITE`
- `PSUBSET`
- `SUBSET`
- `EVEN`
- `ODD`
- `CARD`
- `INSERT`
- `DELETE`
- `ONCE_REWRITE_TAC`
- `TAUT`
- `GEN_TAC`
- `WF_INDUCT_TAC`
- `PSUBSET_ALT`
- `CONJUNCTS_THEN2`
- `ASSUME_TAC`
- `MP_TAC`
- `X_CHOOSE_THEN`
- `STRIP_ASSUME_TAC`
- `SET_RULE`
- `ABBREV_TAC`
- `STRIP_TAC`
- `SUBGOAL_THEN`
- `ASM SET_TAC`
- `FINITE_INSERT`
- `ASM_SIMP_TAC`
- `CARD_SUBSETS_STEP`
- `ASM_CASES_TAC`
- `REWRITE_TAC`
- `CONJ_ASSOC`
- `SUBSET_ANTISYM_EQ`
- `ADD_SYM`
- `CARD_CLAUSES`
- `LT`


---

## SUM_ALTERNATING_CANCELS

### Name of formal statement
SUM_ALTERNATING_CANCELS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_ALTERNATING_CANCELS = prove
 (`!s:A->bool f.
        FINITE s /\
        CARD {x | x IN s /\ EVEN(f x)} = CARD {x | x IN s /\ ODD(f x)}
        ==> sum s (\x. (-- &1) pow (f x)) = &0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {x | x IN s /\ EVEN(f x)} (\x. (-- &1) pow (f x)) +
              sum {x:A | x IN s /\ ODD(f x)} (\x. (-- &1) pow (f x))` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_UNION_EQ THEN
    ASM_SIMP_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_UNION; NOT_IN_EMPTY] THEN
    REWRITE_TAC[GSYM NOT_EVEN] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_POW_NEG; REAL_POW_ONE; GSYM NOT_EVEN; SUM_CONST;
               FINITE_RESTRICT; REAL_ARITH `x * &1 + x * -- &1 = &0`]);;
```
### Informal statement
For any set `s` of type `A` and any function `f` from `A` to boolean, if `s` is finite and the cardinality of elements `x` in `s` where `f x` is even equals the cardinality of elements `x` in `s` where `f x` is odd, then the sum over `s` of `(-- &1)` raised to the power of `f x` is equal to `&0`.

### Informal sketch
The proof proceeds as follows:
- Rewrite the sum over `s` as the sum over the elements of `s` where `f x` is even plus the sum over the elements of `s` where `f x` is odd. This is done via `SUM_UNION_EQ`. The conditions for using `SUM_UNION_EQ` (i.e., that the sets `{x | x IN s /\ EVEN(f x)}` and `{x:A | x IN s /\ ODD(f x)}` are disjoint and their union is `s`) need to be established, which is done using set-theoretic reasoning.
- Simplify both sums. Use the fact that `(-- &1) pow (f x)` is `&1` when `f x` is even and `-- &1` when `f x` is odd. Hence the sum over even `f x` values becomes `&1` summed over the set `{x | x IN s /\ EVEN(f x)}` and the sum over odd values becomes `-- &1` summed over the set `{x:A | x IN s /\ ODD(f x)}`. Apply `SUM_CONST` to rewrite these sums using cardinalities: `CARD {x | x IN s /\ EVEN(f x)} * &1 + CARD {x | x IN s /\ ODD(f x)} * -- &1`.
- Use the assumption `CARD {x | x IN s /\ EVEN(f x)} = CARD {x | x IN s /\ ODD(f x)}` to show that the result is `&0`.

### Mathematical insight
The theorem states that if a finite set `s` can be partitioned into two subsets of equal cardinality, where one subset is mapped to even numbers by `f` and the other to odd numbers, then the sum of `&1` to the power `f x` over `s` is zero. This relies on the contributions from `&1` and `--&1` cancelling each other out due to the equal cardinalities. The formalization highlights the crucial role of the `FINITE` condition, without which summation may be ill-defined.

### Dependencies
- `FINITE`
- `CARD`
- `EVEN`
- `ODD`
- `sum`
- `REAL_POW_NEG`
- `REAL_POW_ONE`
- `SUM_CONST`
- `FINITE_RESTRICT`
- `SUM_UNION_EQ`
- `EXTENSION`
- `IN_ELIM_THM`
- `IN_INTER`
- `IN_UNION`
- `NOT_IN_EMPTY`
- `NOT_EVEN`

### Porting notes (optional)
- Proof assistants that have weaker automation for real arithmetic may require more manual steps to discharge the goal `x * &1 + x * -- &1 = &0`.
- The use of `MESON_TAC` suggests that several background facts regarding set theory and equality are used implicitly. A porter should ensure that their target system has comparable automation or be ready to supply additional lemmas during the proof.


---

## INCLUSION_EXCLUSION_SYMMETRIC

### Name of formal statement
INCLUSION_EXCLUSION_SYMMETRIC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INCLUSION_EXCLUSION_SYMMETRIC = prove
 (`!f g:(A->bool)->real.
    (!s. FINITE s
         ==> g(s) = sum {t | t SUBSET s} (\t. (-- &1) pow (CARD t) * f(t)))
    ==> !s. FINITE s
            ==> f(s) = sum {t | t SUBSET s} (\t. (-- &1) pow (CARD t) * g(t))`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {t:A->bool | t SUBSET s}
                  (\t. (-- &1) pow (CARD t) *
                       sum {u | u IN {u | u SUBSET s} /\ u SUBSET t}
                           (\u. (-- &1) pow (CARD u) * f(u)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM; SET_RULE
     `s SUBSET t ==> (u SUBSET t /\ u SUBSET s <=> u SUBSET s)`] THEN
    ASM_MESON_TAC[FINITE_SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SUM_RESTRICT o lhs o snd) THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[SUM_RMUL; IN_ELIM_THM] THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `sum {u | u SUBSET s} (\u:A->bool. if u = s then f(s) else &0)` THEN
  CONJ_TAC THENL [ALL_TAC; SIMP_TAC[SUM_DELTA; IN_ELIM_THM; SUBSET_REFL]] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `u:A->bool` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[SUBSET_ANTISYM_EQ; SET_RULE `{x | x = a} = {a}`] THEN
    REWRITE_TAC[SUM_SING; REAL_MUL_ASSOC; GSYM REAL_POW_ADD] THEN
    REWRITE_TAC[REAL_POW_NEG; EVEN_ADD; REAL_POW_ONE; REAL_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ENTIRE] THEN REPEAT DISJ1_TAC THEN
  MATCH_MP_TAC SUM_ALTERNATING_CANCELS THEN
  ASM_SIMP_TAC[FINITE_SUBSETS_RESTRICT; IN_ELIM_THM] THEN
  ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c <=> b /\ a /\ c`] THEN
  MATCH_MP_TAC CARD_SUBSUPERSETS_EVEN_ODD THEN ASM SET_TAC[]);;
```

### Informal statement
For any functions `f` and `g` mapping sets of type `A` to real numbers, if for all sets `s`, the finiteness of `s` implies that `g(s)` is equal to the sum over all subsets `t` of `s` of `(-1)` raised to the power of the cardinality of `t` times `f(t)`, then for all sets `s`, the finiteness of `s` implies that `f(s)` is equal to the sum over all subsets `t` of `s` of `(-1)` raised to the power of the cardinality of `t` times `g(t)`.

### Informal sketch
The proof demonstrates the symmetric inclusion-exclusion principle.

- Assume `g(s) = sum {t | t SUBSET s} (\t. (-- &1) pow (CARD t) * f(t))` for all finite sets `s`.
- The goal is to show `f(s) = sum {t | t SUBSET s} (\t. (-- &1) pow (CARD t) * g(t))` for all finite sets `s`.
- Substitute the definition of `g(t)` into the right-hand side of the goal. This results in nested summations.
- Manipulate the summations, using `SUM_LMUL` and `SUM_SUM_RESTRICT`, to obtain a sum over subsets `u` of `s`. The summand involves summing `(-- &1) pow (CARD t)` over `t` where `u SUBSET t SUBSET s`.
- Simplify using `FINITE_POWERSET` to reduce the double summation into single summation.
- The inner sum telescopes to 0 unless `u = s`. Express the entire sum as a `SUM_DELTA` term that isolates the case where `u = s`.
- Use `SUM_ALTERNATING_CANCELS` and `CARD_SUBSUPERSETS_EVEN_ODD` to show that the telescoping summation is zero if `u=s`. Combine and simplify.

### Mathematical insight
This theorem expresses a symmetric form of the inclusion-exclusion principle, frequently referred to as "Moebius inversion." It states that if a function `g` is defined as a sum of a weighted version of `f` over subsets, then `f` can be similarly expressed as a sum of a weighted version of `g` over subsets, with the same alternating signs dependent on subset size. This principle has diverse applications in combinatorics, probability, and number theory.

### Dependencies
**Theorems:**
- `IN_ELIM_THM`
- `SET_RULE`
- `FINITE_SUBSET`
- `SUM_EQ`
- `SUM_LMUL`
- `SUM_SUM_RESTRICT`
- `FINITE_POWERSET`
- `SUM_RMUL`
- `SUM_DELTA`
- `SUBSET_REFL`
- `SUBSET_ANTISYM_EQ`
- `{x | x = a} = {a}`
- `REAL_MUL_ASSOC`
- `GSYM REAL_POW_ADD`
- `REAL_POW_NEG`
- `EVEN_ADD`
- `REAL_POW_ONE`
- `REAL_MUL_LID`
- `REAL_ENTIRE`
- `SUM_ALTERNATING_CANCELS`
- `FINITE_SUBSETS_RESTRICT`
- `TAUT (a /\ b) /\ c <=> b /\ a /\ c`
- `CARD_SUBSUPERSETS_EVEN_ODD`

### Porting notes (optional)
- The proof makes extensive use of rewriting and simplification with set-theoretic identities (`IN_ELIM_THM`, `SET_RULE`), and identities about sums (`SUM_LMUL`, `SUM_RMUL`, `SUM_SUM_RESTRICT`, `SUM_DELTA`). A target proof assistant must have similar automation for manipulating sums and sets.
- The tactic `ONCE_REWRITE_TAC[TAUT (a /\ b) /\ c <=> b /\ a /\ c]` exploits the tautology `(a /\ b) /\ c <=> b /\ a /\ c`. This may require using an explicit call to a tautology checker or boolean simplifier in other proof assistants.


---

## INCLUSION_EXCLUSION_MOBIUS

### Name of formal statement
INCLUSION_EXCLUSION_MOBIUS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INCLUSION_EXCLUSION_MOBIUS = prove
 (`!f g:(A->bool)->real.
        (!s. FINITE s ==> g(s) = sum {t | t SUBSET s} f)
        ==> !s. FINITE s
                ==> f(s) = sum {t | t SUBSET s}
                               (\t. (-- &1) pow (CARD s - CARD t) * g(t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\t. -- &1 pow CARD(t:A->bool) * f t`; `g:(A->bool)->real`]
                INCLUSION_EXCLUSION_SYMMETRIC) THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_ADD] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[EVEN_ADD; REAL_POW_ONE; REAL_POW_NEG; REAL_MUL_LID; ETA_AX];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s:A->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `(*) ((-- &1) pow (CARD(s:A->bool)))`) THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_ADD; GSYM MULT_2] THEN
  REWRITE_TAC[GSYM REAL_POW_POW] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `u:A->bool` THEN REWRITE_TAC[IN_ELIM_THM; REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_POW_SUB; REAL_ARITH `~(-- &1 = &0)`; CARD_SUBSET] THEN
  REWRITE_TAC[REAL_POW_NEG; REAL_POW_ONE] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN REAL_ARITH_TAC);;
```

### Informal statement
For any functions `f` and `g` from sets of type `A` to real numbers, the following holds:
If for every finite set `s` of type `A`, `g(s)` is equal to the sum of `f(t)` for all subsets `t` of `s`, then for every finite set `s` of type `A`, `f(s)` is equal to the sum of `(--1)^(CARD s - CARD t) * g(t)` for all subsets `t` of `s`.

### Informal sketch
The proof proceeds as follows:
- Use the theorem `INCLUSION_EXCLUSION_SYMMETRIC` with appropriate instantiation.
- Rewrite using associativity of real multiplication, and rewrite the reverse of `REAL_POW_ADD`.
- Discharge the assumptions of the resulting implication.
- Simplify using arithmetic facts like `EVEN_ADD`, `REAL_POW_ONE`, `REAL_POW_NEG`, `REAL_MUL_LID`, and eta-reduction.
- Discharge the assumption `s:A->bool` and rewrite the goal using assumptions.
- Apply the term `(*) ((-- &1) pow (CARD(s:A->bool)))`
- Rewrite with rearrangements of real powers, and reduce the power with `REAL_RAT_REDUCE_CONV`.
- Again rewrite and reduce.
- Perform substitution via `SUBST1_TAC`.
- Rewrite using `GSYM SUM_LMUL`, then match with `SUM_EQ`.
- Generalize with `u:A->bool`, and rewrite.
- Simplify using properties of cardinality and arithmetic.
- Reduce the rewritten powers.
- Perform conditional case splitting and final real arithmetic.

### Mathematical insight
This theorem states the Inclusion-Exclusion principle, also known as Möbius inversion, in a specific form where the functions `f` and `g` are related by summation over subsets. It provides a way to invert the relationship between `f` and `g`: if we know how `g` is computed from `f` by summing over subsets, we can compute `f` from `g` by a similar summation with alternating signs.

### Dependencies
- `INCLUSION_EXCLUSION_SYMMETRIC`
- `REAL_MUL_ASSOC`
- `REAL_POW_ADD`
- `EVEN_ADD`
- `REAL_POW_ONE`
- `REAL_POW_NEG`
- `REAL_MUL_LID`
- `MULT_2`
- `REAL_POW_POW`
- `REAL_RAT_REDUCE_CONV`
- `SUM_LMUL`
- `SUM_EQ`
- `IN_ELIM_THM`
- `REAL_POW_SUB`
- `CARD_SUBSET`
- `REAL_ARITH` (for `~(-- &1 = &0)`)


---

## INCLUSION_EXCLUSION_REAL_FUNCTION

### Name of formal statement
INCLUSION_EXCLUSION_REAL_FUNCTION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INCLUSION_EXCLUSION_REAL_FUNCTION = prove
 (`!f s:A->bool.
        FINITE s
        ==> product s (\x. &1 - f x) =
            sum {t | t SUBSET s} (\t. (-- &1) pow (CARD t) * product t f)`,
  let lemma = prove
   (`{t | ?u. u SUBSET s /\ t = x INSERT u} =
     IMAGE (\s. x INSERT s) {t | t SUBSET s}`,
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
    MESON_TAC[]) in
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; SUBSET_EMPTY; SUM_SING; CARD_CLAUSES; real_pow;
           SET_RULE `{x | x = a} = {a}`; REAL_MUL_RID] THEN
  REWRITE_TAC[SUBSET_INSERT_EXISTS] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `s:A->bool`] THEN STRIP_TAC THEN
  REWRITE_TAC[SET_RULE `{t | p t \/ q t} = {t | p t} UNION {t | q t}`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_UNION o rand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_POWERSET; lemma; FINITE_IMAGE] THEN
    REWRITE_TAC[GSYM lemma] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL; REAL_SUB_RDISTRIB; REAL_MUL_LID; real_sub] THEN
  AP_TERM_TAC THEN REWRITE_TAC[lemma] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o rand o snd) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM SUM_NEG] THEN MATCH_MP_TAC SUM_EQ THEN
  SIMP_TAC[o_THM; IN_ELIM_THM] THEN X_GEN_TAC `t:A->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(t:A->bool) /\ ~(x IN t)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; FINITE_SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES; CARD_CLAUSES; real_pow] THEN REAL_ARITH_TAC);;
```

### Informal statement
For all `f` from `A` to boolean, and all `s` from `A` to boolean, if `s` is finite, then the product over `s` of the function that maps `x` to 1 - `f x` is equal to the sum over all subsets `t` of `s` of the function that maps `t` to (-1) to the power of the cardinality of `t`, multiplied by the product over `t` of `f`.

### Informal sketch
The proof proceeds by strong induction on the finiteness of the set `s`.
- Base case: `s` is empty. The product over the empty set is 1 and the sum is also 1 since the only subset is the empty set which makes the exponent zero.
- Inductive step: Assume the theorem holds for all subsets of `s`. We want to prove it for `s INSERT x` where `x` is not in `s`.
  - Rewrite the sum over subsets of `s INSERT x` as the sum over subsets of `s` plus the sum over subsets of the form `x INSERT t` where `t` is a subset of `s`.
  - Apply the inductive hypothesis to the sum over subsets of `s`.
  - Manipulate the sum over subsets of the form `x INSERT t`.  Note that `CARD (x INSERT t) = CARD t + 1`. Thus factoring a negative one permits the inductive hypothesis to be applied.
  - Use properties of real number arithmetic, such as distributivity, to simplify the resulting expression.
  - Use the lemma stating that `{t | ?u. u SUBSET s /\ t = x INSERT u} = IMAGE (\s. x INSERT s) {t | t SUBSET s}`.
  - Finally, perform arithmetic simplifications to derive the desired result.

### Mathematical insight
The theorem expresses the principle of inclusion-exclusion for real-valued functions on sets. It relates the product of `1 - f(x)` over a set to a sum over subsets involving the function `f`. The principle is useful in combinatorics and probability theory.

### Dependencies
- `FINITE`
- `SUBSET`
- `product`
- `sum`
- `CARD`
- `real_pow`
- `PRODUCT_CLAUSES`
- `SUBSET_EMPTY`
- `SUM_SING`
- `CARD_CLAUSES`
- `SET_RULE`
- `SUBSET_INSERT_EXISTS`
- `SUM_UNION`
- `FINITE_POWERSET`
- `FINITE_IMAGE`
- `SUM_LMUL`
- `REAL_SUB_RDISTRIB`
- `REAL_MUL_LID`
- `real_sub`
- `SUM_IMAGE`
- `SUM_NEG`
- `SUM_EQ`
- `IN_ELIM_THM`

### Porting notes (optional)
- The proof relies heavily on rewriting and simplification with real arithmetic rules. A proof assistant with strong support for these tactics is recommended.
- The set comprehension notation `{x | p x}` may need to be translated using appropriate set builder notation in the target proof assistant.
- The handling of finiteness of sets might vary between proof assistants; ensure the correct definitions and lemmas are available.


---

