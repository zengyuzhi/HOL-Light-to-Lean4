# inclusion_exclusion.ml

## Overview

Number of statements: 16

The `inclusion_exclusion.ml` file formalizes the inclusion-exclusion principle in both its usual and generalized forms. It provides simple set theory lemmas, building upon concepts from the `products.ml` library. The file's key content includes definitions and proofs related to set theory, focusing on the principles of inclusion and exclusion. Its purpose is to establish a foundation for reasoning about sets and their intersections within the HOL Light system.

## SUBSET_INSERT_EXISTS

### Name of formal statement
SUBSET_INSERT_EXISTS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SUBSET_INSERT_EXISTS = prove
 (`!s x:A t. s SUBSET (x INSERT t) <=> 
                s SUBSET t \/ ?u. u SUBSET t /\ s = x INSERT u`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  MATCH_MP_TAC(TAUT `(a /\ ~b ==> c) ==> a ==> b \/ c`) THEN
  DISCH_TAC THEN EXISTS_TAC `s DELETE (x:A)` THEN ASM SET_TAC[])
```

### Informal statement
For all sets `s`, `t`, and element `x` of type `A`, `s` is a subset of the set resulting from inserting `x` into `t` if and only if `s` is a subset of `t` or there exists a set `u` such that `u` is a subset of `t` and `s` is equal to the set resulting from inserting `x` into `u`.

### Informal sketch
* The proof starts by considering the equivalence `s SUBSET (x INSERT t) <=> s SUBSET t \/ ?u. u SUBSET t /\ s = x INSERT u`.
* It uses `EQ_TAC` to split the equivalence into two separate implications.
* For the forward direction, it aims to show that if `s` is a subset of `x INSERT t`, then either `s` is a subset of `t` or there exists a `u` such that `u` is a subset of `t` and `s` equals `x INSERT u`.
* The `MATCH_MP_TAC` with the tautology `(a /\ ~b ==> c) ==> a ==> b \/ c` helps in deriving the existence of `u` under certain conditions.
* The `EXISTS_TAC `s DELETE (x:A)`` introduces a witness for `u`, which is `s` with `x` removed, facilitating the construction of `u` as a subset of `t` that satisfies the required conditions.
* `ASM SET_TAC` is used to discharge any remaining set-theoretic subgoals.

### Mathematical insight
This theorem formalizes a fundamental property relating subset inclusion and set insertion, which is crucial in various set-theoretic arguments and constructions. It provides a way to reason about how inserting an element into a set affects subset relationships, offering a basis for more complex set manipulations and proofs.

### Dependencies
* `SUBSET`
* `INSERT`
* `TAUT`

### Porting notes
When translating this theorem into another proof assistant like Lean, Coq, or Isabelle, pay special attention to how each system handles set theory, subset relations, and existential quantification. The `EXISTS_TAC` and `MATCH_MP_TAC` with a specific tautology may require careful handling, as the exact mechanisms for introducing witnesses and applying logical rules can vary significantly between proof assistants. Additionally, consider the differences in how set operations like `INSERT` and `DELETE` are defined and used in the target system.

---

## FINITE_SUBSETS_RESTRICT

### Name of formal statement
FINITE_SUBSETS_RESTRICT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let FINITE_SUBSETS_RESTRICT = prove
 (`!s:A->bool p. FINITE s ==> FINITE {t | t SUBSET s /\ p t}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{t:A->bool | t SUBSET s}` THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[]);;
```

### Informal statement
For all sets `s` of type `A->bool` and all predicates `p`, if `s` is finite, then the set of all subsets `t` of `s` such that `p t` holds is also finite.

### Informal sketch
* The proof starts by assuming `s` is finite and a predicate `p` is given.
* It then applies the `FINITE_SUBSET` theorem to establish that any subset of `s` is finite.
* The `EXISTS_TAC` tactic introduces a specific subset of `s`, namely `{t:A->bool | t SUBSET s}`, which contains all subsets of `s`.
* The `ASM_SIMP_TAC` with `FINITE_POWERSET` simplifies the goal by leveraging the fact that the power set of a finite set is finite.
* Finally, `SET_TAC` is used to discharge any remaining set-theoretic goals.

### Mathematical insight
This theorem is important because it shows that the finiteness of a set is preserved under the operation of taking subsets that satisfy a given predicate. This is a fundamental property in set theory and has numerous applications in various areas of mathematics.

### Dependencies
* Theorems:
  * `FINITE_SUBSET`
* Definitions:
  * `FINITE`
  * `SUBSET`

### Porting notes
When translating this theorem into other proof assistants, pay attention to how they handle finite sets and subset relations. Specifically, ensure that the target system's `FINITE` and `SUBSET` definitions align with those in HOL Light. Additionally, the use of `EXISTS_TAC` and `ASM_SIMP_TAC` may need to be adapted, as different systems may have different tactics for introducing existential witnesses and simplifying goals.

---

## INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED

### Name of formal statement
INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED

### Type of the formal statement
Theorem

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
    REWRITE_TAC[IMAGE_CLAUSES; real_pow] THEN REAL_ARITH_TAC])
```

### Informal statement
For all predicates `P` on subsets of `A`, all functions `f` from subsets of `A` to real numbers, all subsets `A` of `I`, and all functions `x` from `I` to subsets of `A`, if the following conditions hold:
- For all subsets `s` and `t` of `A`, if `P(s)` and `P(t)` and `s` and `t` are disjoint, then `f(s ∪ t) = f(s) + f(t)`.
- `P(∅)` holds.
- For all subsets `s` and `t` of `A`, if `P(s)` and `P(t)`, then `P(s ∩ t)`, `P(s ∪ t)`, and `P(s \ t)` also hold.
- `A` is finite.
- For all `a` in `A`, `P(x(a))` holds.
Then, the following equation holds: `f(∪{x(a) | a ∈ A}) = ∑{B | B ⊆ A, B ≠ ∅} ((-1)^(|B| + 1) * f(∩{x(b) | b ∈ B}))`.

### Informal sketch
The proof of `INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED` involves several key steps:
* Establishing the base case for induction, where `A` is empty.
* Assuming `A` has `n` elements and proving the statement for `n` by considering an element `a` in `A` and the set `A0 = A \ {a}`.
* Using the `DISJOINT` property to show that `f(x(a) ∪ ∪{x(b) | b ∈ A0}) = f(x(a)) + f(∪{x(b) | b ∈ A0})`.
* Applying the induction hypothesis to `A0` and using the properties of `P` and `f` to simplify the expression for `f(∪{x(b) | b ∈ A})`.
* Employing the `lemma` to rewrite the summation over subsets of `A` and applying properties of `SUM` and `IMAGE` to simplify the expression.
* Using `REAL_ARITH` and other arithmetic properties to further simplify and establish the final equation.

### Mathematical insight
The `INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED` theorem provides a generalization of the inclusion-exclusion principle for real-valued functions defined on subsets of a set `A`, under certain conditions on the function and the subsets. This principle is essential in combinatorics and measure theory, allowing for the calculation of the measure of a union of sets while avoiding double counting of intersections.

### Dependencies
* `SUBSET_INSERT_EXISTS`
* `EXTENSION`
* `IN_ELIM_THM`
* `IN_UNION`
* `IMP_CONJ`
* `RIGHT_FORALL_IMP_THM`
* `IMP_IMP`
* `GSYM CONJ_ASSOC`
* `RIGHT_IMP_FORALL_THM`
* `HAS_SIZE`
* `FINITE_INDUCT_STRONG`
* `UNIONS_0`
* `IMAGE_CLAUSES`
* `SUBSET_EMPTY`
* `TAUT`
* `EMPTY_GSPEC`
* `SUM_CLAUSES`
* `REAL_ARITH`
* `SET_RULE`
* `DISJOINT`
* `DISJOINT_EMPTY`
* `UNION_EMPTY`
* `INTER_UNIONS`
* `SIMPLE_IMAGE`
* `GSYM IMAGE_o`
* `o_DEF`
* `FINITE_SUBSETS_RESTRICT`
* `FINITE_IMAGE`
* `IN_DISJOINT`
* `EXISTS_IN_GSPEC`
* `CONJ_SYM`
* `REAL_POW_ADD`
* `REAL_POW_1`
* `REAL_MUL_RNEG`
* `REAL_MUL_LNEG`
* `REAL_NEG_NEG`
* `REAL_MUL_RID`
* `INTERS_IMAGE`
* `SET_RULE`
* `SUM_DELETE_CASES`
* `GSYM DELETE`
* `FINITE_POWERSET`
* `IN_ELIM_THM`
* `EMPTY_SUBSET`
* `IMAGE_CLAUSES`
* `RAND_CONV`
* `ONCE_DEPTH_CONV`
* `SIMPLE_IMAGE_GEN`
* `PART_MATCH`
* `SUM_UNION`
* `RAND`
* `SND`
* `ANTS_TAC`
* `SET_TAC`
* `DISCH_THEN`
* `SUBST1_TAC`
* `REAL_SUB_ADD2`
* `SUM_EQ`
* `FORALL_IN_GSPEC`
* `REAL_POW_ADD`
* `REAL_POW_1`
* `X_GEN_TAC`
* `DISCH_TAC`
* `SUBGOAL_THEN`
* `ASSUME_TAC`
* `ALL_TAC`
* `ASM_MESON_TAC`
* `FINITE_SUBSET`
* `COND_CASES_TAC`
* `ASM_SET_TAC`

### Porting notes
When porting this theorem to another proof assistant, pay special attention to:
* The handling of `SUBSET` and `DISJOINT` properties, as these may be defined differently.
* The use of `REAL_ARITH` and other arithmetic properties, which may require specific libraries or modules.
* The `FINITE_INDUCT_STRONG` tactic, which may need to be replaced with an equivalent induction principle.
* The `PART_MATCH` tactic, which may require a different syntax or approach.
* The use of `SUM` and `IMAGE`, which may have different notations or properties in the target system.

---

## INCLUSION_EXCLUSION_REAL_RESTRICTED

### Name of formal statement
INCLUSION_EXCLUSION_REAL_RESTRICTED

### Type of the formal statement
Theorem

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
  ASM_REWRITE_TAC[IMAGE_ID])
```

### Informal statement
For all predicates `P` on subsets of `A`, and for all functions `f` from subsets of `A` to the real numbers, and for all subsets `A` of the power set of some set, if the following conditions hold:
- For any subsets `s` and `t` of `A`, if `P(s)` and `P(t)` and `s` and `t` are disjoint, then `f(s UNION t) = f(s) + f(t)`.
- `P` holds for the empty set.
- For any subsets `s` and `t` of `A`, if `P(s)` and `P(t)`, then `P` also holds for the intersection, union, and difference of `s` and `t`.
- `A` is finite and `P` holds for every element of `A`.
Then, the value of `f` on the union of all elements of `A` equals the sum over all non-empty subsets `B` of `A` of `(-1)^(CARD B + 1)` times `f` applied to the intersection of all elements of `B`.

### Informal sketch
* The proof involves using the `INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED` theorem with specific instantiations for `P`, `f`, and `A`.
* It starts by applying `REPEAT STRIP_TAC` to simplify the goal, followed by `MP_TAC` to apply the instantiated theorem.
* The `ASM_REWRITE_TAC` with `IMAGE_ID` is then applied to further simplify the expression.
* The key logical stages involve:
  - Establishing the conditions under which `f` behaves additively over disjoint sets.
  - Ensuring `P` holds for basic set operations (union, intersection, difference) and for the empty set.
  - Utilizing the finiteness of `A` and the property of `P` holding for all elements of `A`.
  - Applying the principle of inclusion-exclusion to compute `f` over the union of all elements of `A`.

### Mathematical insight
This theorem formalizes the principle of inclusion-exclusion for a real-valued function `f` defined on subsets of a set `A`, under certain conditions on `f` and a predicate `P`. It's crucial for counting and measuring in various mathematical contexts, providing a way to calculate the value of `f` over a complex set by considering its values over simpler subsets.

### Dependencies
- `INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED`
- `IMAGE_ID`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles:
- Binders and quantifiers, especially in the context of higher-order logic.
- Subset and set operations, ensuring consistency with HOL Light's definitions.
- The principle of inclusion-exclusion, which might be formulated differently or require additional lemmas.
- Automation tactics and their equivalents in the target system, as direct translations of tactics like `REPEAT STRIP_TAC` or `MP_TAC` might not be straightforward.

---

## INCLUSION_EXCLUSION_REAL_INDEXED

### Name of formal statement
INCLUSION_EXCLUSION_REAL_INDEXED

### Type of the formal statement
Theorem

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
For all functions `f` from sets of type `A->bool` to real numbers, for all sets `A` of type `I->bool`, and for all functions `x` of type `I->(A->bool)`, if `f` is additive (i.e., `f(s UNION t) = f(s) + f(t)` whenever `s` and `t` are disjoint) and `A` is finite, then the value of `f` on the union of the images of `x` over `A` is equal to the sum over all non-empty subsets `B` of `A` of `(-1)^(CARD B + 1)` times the value of `f` on the intersection of the images of `x` over `B`.

### Informal sketch
* The proof starts by assuming the additivity of `f` and the finiteness of `A`.
* It then applies the `INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED` theorem, which is specialized for the constant function `T` of type `A->bool`.
* The `MP_TAC` tactic is used to apply the theorem, and then `REWRITE_TAC` is applied to simplify the resulting expression.
* The key idea is to express the value of `f` on the union of the images of `x` over `A` as a sum over subsets of `A`, using the inclusion-exclusion principle.
* The `DISJOINT` condition ensures that the subsets are disjoint, allowing the additivity of `f` to be applied.

### Mathematical insight
The `INCLUSION_EXCLUSION_REAL_INDEXED` theorem is a generalization of the inclusion-exclusion principle for finite sets, adapted to functions that take sets as input and produce real numbers as output. The theorem provides a way to compute the value of such a function on a union of sets, by summing over subsets and applying the inclusion-exclusion principle. This is useful in a variety of mathematical contexts, such as combinatorics and measure theory.

### Dependencies
* `INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED`
* `DISJOINT`
* `FINITE`
* `UNIONS`
* `IMAGE`
* `INTERS`
* `SUBSET`
* `CARD`
* `sum`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the `INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED` theorem is properly specialized and applied. The `MP_TAC` and `REWRITE_TAC` tactics may need to be replaced with equivalent tactics in the target system. Additionally, the handling of binders and quantifiers may differ between systems, requiring careful attention to ensure that the theorem is correctly translated.

---

## INCLUSION_EXCLUSION_REAL

### Name of formal statement
INCLUSION_EXCLUSION_REAL

### Type of the formal statement
Theorem

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
  ASM_REWRITE_TAC[IMAGE_ID])
```

### Informal statement
For all functions `f` from subsets of `A` to real numbers and for all subsets `A` of a set, if `f` satisfies the property that for any disjoint subsets `s` and `t` of `A`, `f(s UNION t)` equals `f(s) + f(t)`, and if `A` is finite, then the value of `f` on the union of all subsets in `A` equals the sum over all non-empty subsets `B` of `A` of `(-1)^(CARD B + 1)` times `f` applied to the intersection of all sets in `B`.

### Informal sketch
* The theorem starts by assuming a function `f` that maps subsets of `A` to real numbers and a set `A` that is finite.
* It then applies the principle of inclusion-exclusion by considering all possible subsets of `A` and their contributions to the total sum.
* The proof involves using the `INCLUSION_EXCLUSION_REAL_INDEXED` theorem with specific instantiations for `f`, `A`, and a lambda function that simply returns its input.
* The `REPEAT STRIP_TAC` and `MP_TAC` tactics are used to apply the theorem and manage the proof state.
* Finally, `ASM_REWRITE_TAC` with `IMAGE_ID` is applied to simplify the conclusion.

### Mathematical insight
This theorem formalizes the principle of inclusion-exclusion for a finite set `A` and a function `f` that assigns real numbers to subsets of `A`. The principle is fundamental in combinatorics and probability theory, allowing for the calculation of the size of a union of sets by considering their intersections.

### Dependencies
#### Theorems
* `INCLUSION_EXCLUSION_REAL_INDEXED`
#### Definitions
* `DISJOINT`
* `UNIONS`
* `SUBSET`
* `FINITE`
* `CARD`
* `INTERS`
* `IMAGE_ID`

### Porting notes
When translating this theorem into another proof assistant, special attention should be paid to the handling of subset operations, the representation of the function `f`, and the implementation of the principle of inclusion-exclusion. The use of `REPEAT STRIP_TAC` and `MP_TAC` may need to be adapted based on the target system's tactic language. Additionally, the `INCLUSION_EXCLUSION_REAL_INDEXED` theorem, which is used in the proof, will also need to be ported or proven in the target system.

---

## INCLUSION_EXCLUSION

### Name of formal statement
INCLUSION_EXCLUSION

### Type of the formal statement
Theorem

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
  SIMP_TAC[CARD_UNION; DISJOINT; REAL_OF_NUM_ADD])
```

### Informal statement
For all sets `s` of subsets of `A` such that `s` is finite and every element `k` of `s` is also finite, the cardinality of the union of all sets in `s` is equal to the sum over all non-empty subsets `t` of `s` of `(-1)^(|t| + 1)` times the cardinality of the intersection of all sets in `t`.

### Informal sketch
* The proof starts by assuming `s` is a finite set of subsets of `A`, where each subset is also finite.
* It then applies the `INCLUSION_EXCLUSION_REAL_RESTRICTED` theorem with specific instantiations to establish a relationship between the cardinality of the union of sets in `s` and the sum over subsets of `s`.
* The proof involves simplifying the expression using `ASM_SIMP_TAC` with various finite set properties (`FINITE_INTER`, `FINITE_UNION`, `FINITE_DIFF`, `FINITE_EMPTY`) and then applying `DISCH_THEN MATCH_MP_TAC` to match the pattern and simplify further.
* Key steps involve calculating the cardinality of the union and intersections using `CARD_UNION`, `DISJOINT`, and `REAL_OF_NUM_ADD`, highlighting the use of `-- &1` for handling the alternating series in the inclusion-exclusion principle.

### Mathematical insight
The `INCLUSION_EXCLUSION` theorem formalizes the principle of inclusion-exclusion, a fundamental combinatorial technique for counting the elements in the union of multiple sets by considering their intersections. This principle is crucial in various areas of mathematics, including combinatorics, probability, and algebra. The theorem's importance lies in its ability to generalize the counting process for any finite collection of finite sets, providing a systematic way to calculate the cardinality of their union.

### Dependencies
* Theorems:
  + `INCLUSION_EXCLUSION_REAL_RESTRICTED`
* Definitions:
  + `FINITE`
  + `CARD`
  + `UNIONS`
  + `SUBSET`
  + `INTERS`
  + `DISJOINT`
  + `REAL_OF_NUM_ADD`
* Properties:
  + `FINITE_INTER`
  + `FINITE_UNION`
  + `FINITE_DIFF`
  + `FINITE_EMPTY`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles finite sets, cardinalities, and the principle of inclusion-exclusion. Differences in notation and built-in support for combinatorial principles may require adjustments in the proof strategy, particularly in how the `INCLUSION_EXCLUSION_REAL_RESTRICTED` theorem and its instantiations are handled. Additionally, consider the treatment of alternating sums and how `-- &1` is interpreted in the context of the inclusion-exclusion principle.

---

## INCLUSION_EXCLUSION_USUAL

### Name of formal statement
INCLUSION_EXCLUSION_USUAL

### Type of the formal statement
Theorem

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
  ASM_MESON_TAC[CARD_EQ_0; ARITH_RULE `~(1 <= 0)`; FINITE_SUBSET])
```

### Informal statement
For all sets `s` of subsets of a set `A`, if `s` is finite and every element `k` of `s` is also finite, then the cardinality of the union of all sets in `s` is equal to the sum, for all positive integers `n` from 1 to the cardinality of `s`, of `(-1)` raised to the power of `n+1` times the sum, over all subsets `t` of `s` with `n` elements, of the cardinality of the intersection of all sets in `t`.

### Informal sketch
* The proof begins by assuming the premise: `s` is finite and every `k` in `s` is finite.
* It then applies the `INCLUSION_EXCLUSION` theorem and simplifies using `ASM_SIMP_TAC`.
* The proof involves a case analysis and the use of `MATCH_MP_TAC` to apply a relevant theorem about sum equality.
* Key steps involve rewriting expressions using `GEN_REWRITE_TAC`, `REWRITE_TAC`, and applying `ASM_MESON_TAC` to derive conclusions from given premises and previously established facts.
* The use of `AP_TERM_TAC` and `AP_THM_TAC` suggests applying theorems to specific terms and propositions.
* The proof concludes by showing that the cardinality of the union of sets in `s` can be expressed as a sum involving subsets of `s` and their intersections, utilizing principles of finite sets and arithmetic.

### Mathematical insight
This theorem formalizes the principle of inclusion-exclusion, a fundamental concept in combinatorics and set theory. It allows for the calculation of the size of a set by adding the sizes of its subsets and then adjusting for overcounts by considering intersections. The theorem is crucial in various mathematical and computational contexts, providing a systematic way to count elements in unions of sets.

### Dependencies
* Theorems:
  + `INCLUSION_EXCLUSION`
  + `SUM_IMAGE_GEN`
  + `FINITE_SUBSETS_RESTRICT`
  + `SUM_EQ`
* Definitions:
  + `CARD` (cardinality)
  + `UNIONS` (union of sets)
  + `INTERS` (intersection of sets)
  + `SUBSET` (subset relation)
  + `HAS_SIZE` (predicate for sets of a certain size)
  + `FINITE` (predicate for finite sets)

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles set operations, finite sets, and the principle of inclusion-exclusion. Note that the `INCLUSION_EXCLUSION_USUAL` theorem relies on specific tactics and theorems (`INCLUSION_EXCLUSION`, `SUM_IMAGE_GEN`, etc.) that may need to be reformulated or replaced with equivalent constructs in the target system. Additionally, consider the differences in how binders and quantifiers are handled, as well as the level of automation provided by the target proof assistant.

---

## FINITE_SUBSETS_RESTRICT

### Name of formal statement
FINITE_SUBSETS_RESTRICT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let FINITE_SUBSETS_RESTRICT = prove
 (`!s:A->bool p. FINITE s ==> FINITE {t | t SUBSET s /\ p t}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{t:A->bool | t SUBSET s}` THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[]);;
```

### Informal statement
For all sets `s` of type `A->bool` and for all predicates `p`, if `s` is finite, then the set of all subsets `t` of `s` such that `p` holds for `t` is also finite.

### Informal sketch
* The proof starts by assuming `s` is finite and `p` is a predicate.
* It then applies the `FINITE_SUBSET` theorem to establish that any subset of `s` is finite if `s` is finite.
* The `EXISTS_TAC` tactic is used to introduce a specific subset of `s`, namely the set of all subsets `t` of `s`, which is shown to be finite using `FINITE_POWERSET`.
* The proof concludes by simplifying the expression using `ASM_SIMP_TAC` and applying `SET_TAC` to finalize the set-theoretic argument.

### Mathematical insight
This theorem provides a combinatorial lemma about subsets of a finite set, which is crucial in various mathematical contexts, especially in combinatorics and set theory. It ensures that if we start with a finite set and consider all its subsets that satisfy a certain property, the collection of these subsets is also finite. This is important because it allows for the application of finite methods and arguments to what might initially seem like infinite or unbounded problems.

### Dependencies
* Theorems:
  * `FINITE_SUBSET`
  * `FINITE_POWERSET`
* Definitions:
  * `FINITE`
  * `SUBSET`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles finite sets, subsets, and predicates. The `REPEAT STRIP_TAC` and `MATCH_MP_TAC` tactics might need to be replaced with equivalent tactics or strategies in the target system. Additionally, the handling of `EXISTS_TAC` and `ASM_SIMP_TAC` may vary, requiring careful consideration of how existential quantification and simplification are managed in the new context.

---

## CARD_ADJUST_LEMMA

### Name of formal statement
CARD_ADJUST_LEMMA

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CARD_ADJUST_LEMMA = prove
 (`!f:A->B s x y.
        FINITE s /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        x = y + CARD (IMAGE f s)
        ==> x = y + CARD s`,
  MESON_TAC[CARD_IMAGE_INJ])
```

### Informal statement
For all functions `f` from set `A` to set `B`, and for all sets `s` and elements `x` and `y`, if `s` is finite and `f` is injective on `s` (i.e., for all `x` and `y` in `s`, if `f(x) = f(y)` then `x = y`), and if `x` equals `y` plus the cardinality of the image of `f` on `s`, then `x` equals `y` plus the cardinality of `s`.

### Informal sketch
* The theorem starts by assuming `s` is a finite set and `f` is a function that is injective on `s`.
* It then assumes an equation relating `x`, `y`, and the cardinality of the image of `f` on `s`.
* The proof involves using the `CARD_IMAGE_INJ` theorem, which likely relates the cardinality of the image of an injective function on a set to the cardinality of the set itself.
* The `MESON_TAC` tactic is used, which is a tactical in HOL Light for proving theorems using meson, a resolution-based theorem prover.
* The key logical stage is recognizing that since `f` is injective on `s`, the cardinality of the image of `f` on `s` equals the cardinality of `s` itself, thus allowing the conclusion that `x = y + CARD s`.

### Mathematical insight
This theorem provides a way to reason about the cardinalities of sets and their images under injective functions. It's essentially a statement about how the cardinality of a set is preserved under an injective mapping, which is a fundamental property in set theory and is crucial in various mathematical proofs, especially those involving combinatorics and cardinal arithmetic.

### Dependencies
* `FINITE`
* `CARD`
* `IMAGE`
* `CARD_IMAGE_INJ`

### Porting notes
When translating this theorem into another proof assistant, pay special attention to how injectivity is represented and used, as well as how cardinalities of sets and their images are handled. The `MESON_TAC` tactic and the `CARD_IMAGE_INJ` theorem may need to be replaced with equivalent constructs in the target system. Additionally, differences in how binders and quantifiers are handled between HOL Light and the target system may require careful consideration.

---

## CARD_SUBSETS_STEP

### Name of formal statement
CARD_SUBSETS_STEP

### Type of the formal statement
Theorem

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
   ASM_MESON_TAC[CARD_CLAUSES; EVEN; NOT_ODD; FINITE_SUBSET; SUBSET])
```

### Informal statement
For all `x` and `s` such that `s` is finite, `x` is not in `s`, and `u` is a subset of `s`, the following holds: 
The cardinality of the set of all subsets `t` of `x` inserted into `s` such that `u` is a subset of `t` and the cardinality of `t` is odd is equal to the cardinality of the set of all subsets `t` of `s` such that `u` is a subset of `t` and the cardinality of `t` is odd plus the cardinality of the set of all subsets `t` of `s` such that `u` is a subset of `t` and the cardinality of `t` is even. 
Additionally, the cardinality of the set of all subsets `t` of `x` inserted into `s` such that `u` is a subset of `t` and the cardinality of `t` is even is equal to the cardinality of the set of all subsets `t` of `s` such that `u` is a subset of `t` and the cardinality of `t` is even plus the cardinality of the set of all subsets `t` of `s` such that `u` is a subset of `t` and the cardinality of `t` is odd.

### Informal sketch
* The proof begins by applying `REPEAT STRIP_TAC` to remove the universal quantifier and implications from the statement.
* It then uses `MATCH_MP_TAC` with `CARD_ADJUST_LEMMA` to introduce a new variable `u` defined as `(x:A) INSERT u`.
* The `ASM_SIMP_TAC` with `FINITE_SUBSETS_RESTRICT` simplifies the finite subset restrictions.
* The proof then proceeds with a series of case analyses and rewrites using various theorems and definitions, including `CARD_UNION_EQ`, `EXTENSION`, `IN_ELIM_THM`, and `SUBSET_INSERT_EXISTS`.
* Key steps involve recognizing the parity (even or odd) of the cardinality of subsets and applying `CARD_CLAUSES`, `EVEN`, `NOT_ODD`, `FINITE_SUBSET`, and `SUBSET` to derive the desired equalities.

### Mathematical insight
This theorem provides a relationship between the cardinalities of sets of subsets with certain properties, specifically regarding the parity of their cardinalities when an element is inserted into the base set. It is a foundational result in combinatorial set theory, crucial for reasoning about the sizes of sets of subsets under specific conditions.

### Dependencies
* Theorems:
  - `CARD_ADJUST_LEMMA`
  - `CARD_UNION_EQ`
  - `CARD_CLAUSES`
  - `EVEN`
  - `NOT_ODD`
  - `FINITE_SUBSET`
  - `SUBSET`
* Definitions:
  - `FINITE_SUBSETS_RESTRICT`
  - `FINITE_INSERT`
  - `SUBSET_INSERT_EXISTS`
  - `IN_ELIM_THM`
  - `EXTENSION`
  - `IN_IMAGE`
  - `IN_INTER`
  - `RIGHT_OR_DISTRIB`
  - `LEFT_AND_EXISTS_THM`
  - `FUN_EQ_THM`

---

## CARD_SUBSUPERSETS_EVEN_ODD

### Name of formal statement
CARD_SUBSUPERSETS_EVEN_ODD

### Type of the formal statement
Theorem

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
    ASM_SIMP_TAC[CARD_CLAUSES; LT; PSUBSET]])
```

### Informal statement
For all subsets `s` and `u` of a non-empty set `A`, if `u` is finite and `s` is a proper subset of `u`, then the cardinality of the set of all subsets `t` of `u` that contain `s` and have an even cardinality is equal to the cardinality of the set of all subsets `t` of `u` that contain `s` and have an odd cardinality.

### Informal sketch
* The proof starts by assuming `s` and `u` are subsets of `A` with `u` finite and `s` a proper subset of `u`.
* It uses well-founded induction on the cardinality of `u` to establish the claim.
* The base case involves rewriting the subset relation using `PSUBSET_ALT` and applying `SET_RULE` to handle the case when `x` is in `s`.
* The inductive step involves choosing an element `x` in `s`, removing it from `u` to form `v`, and then using `CARD_SUBSETS_STEP` to relate the cardinalities of subsets of `u` and `v`.
* The proof then proceeds by cases, considering whether `s` equals `v` or not, and uses properties of even and odd cardinalities to establish the equality.

### Mathematical insight
This theorem provides insight into the combinatorial properties of subsets of a finite set. Specifically, it shows that when considering all possible supersets of a given subset `s` within a finite set `u`, the number of such supersets with even cardinality is equal to the number with odd cardinality, provided `s` is a proper subset of `u`. This has implications for counting arguments in combinatorics and can be useful in proofs involving parity arguments.

### Dependencies
* `FINITE`
* `PSUBSET`
* `CARD`
* `EVEN`
* `ODD`
* `SET_RULE`
* `CARD_SUBSETS_STEP`
* `WF_INDUCT_TAC`
* `TAUT`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, special attention should be paid to the handling of subset relations, finite sets, and the well-founded induction principle. The `WF_INDUCT_TAC` tactic in HOL Light corresponds to well-founded induction, which may need to be explicitly invoked in other systems. Additionally, the use of `SET_RULE` and `CARD_SUBSETS_STEP` may require equivalent rules or lemmas in the target system, potentially involving different names or formulations.

---

## SUM_ALTERNATING_CANCELS

### Name of formal statement
SUM_ALTERNATING_CANCELS

### Type of the formal statement
Theorem

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
               FINITE_RESTRICT; REAL_ARITH `x * &1 + x * -- &1 = &0`])
```

### Informal statement
For all sets `s` and functions `f`, if `s` is finite and the number of elements `x` in `s` for which `f(x)` is even is equal to the number of elements `x` in `s` for which `f(x)` is odd, then the sum of `(-1)^(f(x))` over all `x` in `s` is equal to 0.

### Informal sketch
* The proof starts by assuming the premises: `s` is finite and the cardinality of the set of `x` in `s` where `f(x)` is even is equal to the cardinality of the set of `x` in `s` where `f(x)` is odd.
* It then applies the `EQ_TRANS` tactic to introduce an intermediate expression: the sum of `(-1)^(f(x))` over the set of `x` in `s` where `f(x)` is even, plus the sum of `(-1)^(f(x))` over the set of `x` in `s` where `f(x)` is odd.
* The proof proceeds by simplifying this expression using properties of sum and the fact that `(-1)^x + (-1)^x = 0` when `x` is odd.
* Key steps involve using `SUM_UNION_EQ` to combine the sums, and `REAL_POW_NEG` and `REAL_POW_ONE` to simplify the expressions involving `(-1)^(f(x))`.
* The `CONJ_TAC` and `ASM_SIMP_TAC` tactics are used to manage the proof state and apply simplifications.

### Mathematical insight
This theorem provides a condition under which an alternating sum over a finite set reduces to zero. The condition is that the number of terms with even and odd exponents must be equal, which leads to pairwise cancellations of terms.

### Dependencies
* Theorems:
  + `SUM_UNION_EQ`
  + `REAL_POW_NEG`
  + `REAL_POW_ONE`
  + `FINITE_RESTRICT`
  + `REAL_ARITH`
* Definitions:
  + `EVEN`
  + `ODD`
  + `SUM`
  + `CARD`

### Porting notes
When translating this theorem into another proof assistant, pay attention to how the system handles finite sets, summations, and the properties of `(-1)^x`. In particular, ensure that the target system has equivalents for `SUM_UNION_EQ`, `REAL_POW_NEG`, and `REAL_POW_ONE`, and that it can handle the `CONJ_TAC` and `ASM_SIMP_TAC` tactics or their equivalents. Additionally, consider how the target system represents and manipulates finite sets and their cardinalities.

---

## INCLUSION_EXCLUSION_SYMMETRIC

### Name of formal statement
INCLUSION_EXCLUSION_SYMMETRIC

### Type of the formal statement
Theorem

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
  MATCH_MP_TAC CARD_SUBSUPERSETS_EVEN_ODD THEN ASM SET_TAC[])
```

### Informal statement
For all functions `f` and `g` from subsets of `A` to real numbers, if for every finite subset `s` of `A`, `g(s)` is equal to the sum over all subsets `t` of `s` of `(-1)^|t| * f(t)`, then for every finite subset `s` of `A`, `f(s)` is equal to the sum over all subsets `t` of `s` of `(-1)^|t| * g(t)`.

### Informal sketch
* The proof starts by assuming the given condition for `g(s)` and aiming to prove the corresponding statement for `f(s)`.
* It involves using the `EQ_TRANS` tactic to introduce an intermediate expression that will help in transforming the sum involving `f` into a sum involving `g`.
* The `SUM_EQ` theorem is applied to equate the sum over subsets of `s` of expressions involving `f` and `g`, utilizing properties of finite subsets and the `IN_ELIM_THM` to simplify the conditions under which the sums are taken.
* The proof further involves manipulating the sums using properties of real numbers, such as distribution and the behavior of `(-1)^|t|`, and applying specific tactics like `MATCH_MP_TAC` and `ASM_MESON_TAC` to derive the desired equality.
* Key steps include recognizing the application of `SUM_ALTERNATING_CANCELS` and leveraging the `CARD_SUBSUPERSETS_EVEN_ODD` property to conclude the proof.

### Mathematical insight
This theorem provides a symmetric form of the inclusion-exclusion principle, allowing for the transformation between two functions `f` and `g` that are related through a specific summation formula involving subsets and their cardinalities. The principle is essential in combinatorics and has applications in various areas of mathematics, including probability theory and number theory. The symmetric form, as mentioned, is attributed to Ira Gessel.

### Dependencies
* Theorems:
  + `SUM_EQ`
  + `IN_ELIM_THM`
  + `FINITE_SUBSET`
  + `SUM_ALTERNATING_CANCELS`
  + `CARD_SUBSUPERSETS_EVEN_ODD`
* Definitions:
  + `SUM`
  + `SUBSET`
  + `CARD`
  + `FINITE`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, special attention should be given to the handling of subset relations, finite sets, and the properties of real numbers. The `SUM` function and its properties, as well as the `CARD` function for calculating the cardinality of a set, need to be defined or imported appropriately. Additionally, the tactics used, such as `MATCH_MP_TAC` and `ASM_MESON_TAC`, may have equivalents in the target system, but their application and the overall proof strategy might require adjustments due to differences in the underlying logic or proof assistant's capabilities.

---

## INCLUSION_EXCLUSION_MOBIUS

### Name of formal statement
INCLUSION_EXCLUSION_MOBIUS

### Type of the formal statement
Theorem

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
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN REAL_ARITH_TAC)
```

### Informal statement
For all functions `f` and `g` from subsets of `A` to real numbers, if for every finite subset `s` of `A`, `g(s)` equals the sum of `f(t)` over all subsets `t` of `s`, then for every finite subset `s` of `A`, `f(s)` equals the sum of `(-1)^(|s| - |t|) * g(t)` over all subsets `t` of `s`.

### Informal sketch
* The proof starts by assuming the given condition about `g(s)` and `f(t)` for finite subsets `s` and their subsets `t`.
* It then applies the `INCLUSION_EXCLUSION_SYMMETRIC` theorem with specific instantiations to transform the expression involving `f` and `g`.
* The proof involves several rewriting steps using properties of real numbers and set operations, including `REAL_MUL_ASSOC`, `GSYM REAL_POW_ADD`, and `CARD_SUBSET`.
* It uses `ANTS_TAC` and `ASM_SIMP_TAC` to simplify and rearrange terms, leveraging properties like `EVEN_ADD`, `REAL_POW_ONE`, and `REAL_MUL_LID`.
* The `DISCH_THEN` and `MP_TAC` tactics are used to apply theorems and lemmas, specifically `INCLUSION_EXCLUSION_SYMMETRIC`, to the current goal.
* The proof also involves case analysis and arithmetic reasoning, culminating in the application of `REAL_ARITH_TAC` to finalize the proof.

### Mathematical insight
This theorem is a version of the inclusion-exclusion principle, which is a fundamental concept in combinatorics and set theory. It relates the values of two functions, `f` and `g`, defined on subsets of a set `A`, where `g` is defined in terms of the sums of `f` over subsets. The principle allows for the computation of `f(s)` for any finite subset `s` of `A` by considering the contributions of all its subsets, weighted by a term involving the cardinalities of `s` and its subsets. This principle is crucial in various counting arguments and has numerous applications in mathematics and computer science.

### Dependencies
#### Theorems
* `INCLUSION_EXCLUSION_SYMMETRIC`
#### Definitions and Axioms
* `FINITE`
* `SUBSET`
* `CARD`
* `SUM`
* `REAL_POW`
* `REAL_MUL_ASSOC`
* `GSYM REAL_POW_ADD`
* `EVEN_ADD`
* `REAL_POW_ONE`
* `REAL_MUL_LID`
* `ETA_AX`
* `REAL_ARITH`

---

## INCLUSION_EXCLUSION_REAL_FUNCTION

### Name of formal statement
INCLUSION_EXCLUSION_REAL_FUNCTION

### Type of the formal statement
Theorem

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
  ASM_SIMP_TAC[PRODUCT_CLAUSES; CARD_CLAUSES; real_pow] THEN REAL_ARITH_TAC)
```

### Informal statement
For all functions `f` from a non-empty set `s` to the boolean values and such that `s` is finite, the product over `s` of `1 - f(x)` is equal to the sum over all subsets `t` of `s` of `(-1)^|t| * product t f`, where `|t|` denotes the cardinality of `t`.

### Informal sketch
* The proof proceeds by strong induction on the finiteness of `s`.
* The base case is established using `FINITE_INDUCT_STRONG`.
* The inductive step involves using `SUBSET_INSERT_EXISTS` and manipulating sums and products over subsets.
* A key intermediate result `lemma` is used, which relates subsets and their images under insertion.
* The proof employs various tactics such as `GEN_REWRITE_TAC`, `REWRITE_TAC`, `MATCH_MP_TAC`, and `REAL_ARITH_TAC` to simplify and rearrange terms.
* The `SUM_UNION` and `SUM_IMAGE` properties are used to handle sums over unions and images of sets.

### Mathematical insight
This theorem formalizes the principle of inclusion-exclusion for real-valued functions over finite sets. It provides a way to compute the product of a function over a set by summing over all subsets, taking into account the cardinality of each subset. This principle is fundamental in combinatorics and has numerous applications in mathematics and computer science.

### Dependencies
* Theorems:
	+ `FINITE_INDUCT_STRONG`
	+ `SUM_UNION`
	+ `SUM_IMAGE`
	+ `PRODUCT_CLAUSES`
	+ `SUBSET_EMPTY`
	+ `SUM_SING`
	+ `CARD_CLAUSES`
	+ `real_pow`
	+ `SET_RULE`
	+ `REAL_MUL_RID`
	+ `REAL_SUB_RDISTRIB`
	+ `REAL_MUL_LID`
	+ `real_sub`
* Definitions:
	+ `FINITE`
	+ `SUBSET`
	+ `CARD`
	+ `product`
	+ `sum`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of finite sets, boolean functions, and the principle of inclusion-exclusion. The use of strong induction and various properties of sums and products may require careful adaptation to the target system's libraries and tactics. Additionally, the `REAL_ARITH_TAC` tactic may need to be replaced with equivalent arithmetic reasoning in the target system.

---

