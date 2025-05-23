# inclusion_exclusion.ml

## Overview

Number of statements: 16

This file formalizes the inclusion-exclusion principle in both standard and generalized forms, building on basic set theory. It provides theorems for calculating the cardinality of unions of finite sets by accounting for overlaps through alternating sums of intersections. The implementation depends on the products library, suggesting it leverages product operations for working with set families and indexed collections.

## SUBSET_INSERT_EXISTS

### SUBSET_INSERT_EXISTS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
For sets $s, t$ and an element $x$ of type $A$, we have:
$s \subseteq (x \cup t) \iff s \subseteq t \lor \exists u.(u \subseteq t \land s = x \cup u)$

Where:
- $\subseteq$ denotes the subset relation
- $\cup$ denotes set union (where $x$ is treated as a singleton set $\{x\}$)
- $\lor$ is logical disjunction
- $\exists$ is existential quantification

### Informal proof
We prove both directions of the equivalence:

- ($\Rightarrow$): Assume $s \subseteq (x \cup t)$. We need to prove $s \subseteq t \lor \exists u.(u \subseteq t \land s = x \cup u)$.
  
  We use a proof by cases: If $s \subseteq t$, then the first disjunct is true. If $s \not\subseteq t$, we need to find a suitable $u$.
  
  Let $u = s \setminus \{x\}$ (i.e., $s$ with $x$ removed). We claim that:
  1. $u \subseteq t$: For any element in $u$, it must be in $s$ and not equal to $x$. Since $s \subseteq (x \cup t)$ and the element is not $x$, it must be in $t$.
  2. $s = x \cup u$: This follows from elementary set theory, as we've defined $u = s \setminus \{x\}$.

- ($\Leftarrow$): This direction follows directly from set-theoretic reasoning:
  - If $s \subseteq t$, then clearly $s \subseteq (x \cup t)$ since $t \subseteq (x \cup t)$.
  - If $\exists u.(u \subseteq t \land s = x \cup u)$, then every element of $s$ is either $x$ or in $u$. Since $u \subseteq t$, every element of $s$ is either $x$ or in $t$, meaning $s \subseteq (x \cup t)$.

### Mathematical insight
This theorem characterizes when a set is a subset of another set that has the form of a singleton union. It gives a precise condition in terms of either:
1. The set being a subset of the non-singleton part, or
2. The set being expressible as a union of the singleton and some subset of the non-singleton part.

This result is particularly useful for proofs that involve manipulating sets and analyzing their inclusion relationships, especially when dealing with insertions of elements into sets.

### Dependencies
No explicit dependencies are listed, but the proof uses:
- `SET_TAC`: A set theory decision procedure in HOL Light
- `TAUT`: A tautology checker for propositional logic
- Standard set operations (SUBSET, INSERT, DELETE)

### Porting notes
When porting this theorem:
- Ensure the target system has good support for set operations, particularly set difference (DELETE in HOL Light)
- The proof relies on automated set reasoning (SET_TAC[]); you might need manual expansion of set-theoretic arguments in systems with less automation
- Pay attention to notation differences - HOL Light uses INSERT for adding an element to a set (equivalent to $\{x\} \cup s$ in standard mathematics)

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
For any set $s$ of type $A \to \text{bool}$ and any predicate $p$ on sets, if $s$ is finite, then the collection of all subsets $t$ of $s$ that satisfy the predicate $p$ is also finite.

Formally: $\forall s: A \to \text{bool}, \forall p. \text{FINITE}(s) \Rightarrow \text{FINITE}(\{t \mid t \subseteq s \land p(t)\})$

### Informal proof
The proof proceeds by applying the result that any subset of a finite set is finite:

1. We first apply the theorem `FINITE_SUBSET`, which states that if a set is a subset of a finite set, then it is finite.

2. We need to find a finite set that contains $\{t \mid t \subseteq s \land p(t)\}$. We choose the power set of $s$, i.e., $\{t \mid t \subseteq s\}$.

3. The set $\{t \mid t \subseteq s \land p(t)\}$ is clearly a subset of $\{t \mid t \subseteq s\}$ since we're just adding an additional constraint $p(t)$.

4. The power set of a finite set is finite (theorem `FINITE_POWERSET`), and since $s$ is finite by assumption, $\{t \mid t \subseteq s\}$ is finite.

5. Therefore, $\{t \mid t \subseteq s \land p(t)\}$ is finite.

### Mathematical insight
This theorem extends the well-known result that the power set of a finite set is finite. It states that any collection of subsets of a finite set that satisfy some predicate is also finite.

This is useful in many contexts where we need to work with specific collections of subsets that satisfy certain properties. The theorem ensures that such collections remain finite if the original set is finite, which is important for algorithmic applications and inductive reasoning on set structures.

### Dependencies
- **Theorems**:
  - `FINITE_SUBSET`: If a set is a subset of a finite set, then it is finite
  - `FINITE_POWERSET`: The power set of a finite set is finite
  - Set theory tactics (`SET_TAC`)

### Porting notes
When porting to other systems:
1. Ensure the dependent theorems `FINITE_SUBSET` and `FINITE_POWERSET` are available
2. This proof relies on set theory automation (through `SET_TAC`), so the target system needs similar capabilities or an explicit proof for the set-theoretic reasoning step
3. The representation of sets and predicates on sets might differ between systems, but the mathematical content should translate directly

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
Let $I$ and $A$ be types, $P$ be a predicate on sets of type $A$, $f$ be a function from sets of type $A$ to real numbers, $A$ be a finite set of elements of type $I$, and $x$ be a function mapping elements of type $I$ to sets of type $A$. 

If the following conditions hold:
- $f$ is additive on disjoint sets satisfying $P$: For all sets $s$ and $t$ such that $P(s)$, $P(t)$, and $s \cap t = \emptyset$, we have $f(s \cup t) = f(s) + f(t)$
- The empty set satisfies $P$: $P(\emptyset)$
- $P$ is closed under set operations: For all sets $s$ and $t$ where $P(s)$ and $P(t)$, we have $P(s \cap t)$, $P(s \cup t)$, and $P(s \setminus t)$
- The set $A$ is finite
- For all $a \in A$, we have $P(x(a))$

Then the following inclusion-exclusion principle holds:
$$f\left(\bigcup_{a \in A} x(a)\right) = \sum_{B \subseteq A, B \neq \emptyset} (-1)^{|B|+1} \cdot f\left(\bigcap_{b \in B} x(b)\right)$$

### Informal proof
The proof proceeds by induction on the size of the set $A$.

First, we prove a helpful lemma stating that for any set $s$, element $a$, and predicate $P$:
$$\{t \mid t \subseteq (a \cup s) \wedge P(t)\} = \{t \mid t \subseteq s \wedge P(t)\} \cup \{a \cup t \mid t \subseteq s \wedge P(a \cup t)\}$$

**Base Case**: When $A$ is empty.
- When $A = \emptyset$, we have $\bigcup_{a \in A} x(a) = \emptyset$.
- The sum on the right-hand side is empty (since there are no non-empty subsets of $\emptyset$).
- Using the property that $f(\emptyset) = 0$ (derived from the additivity of $f$ with $f(\emptyset \cup \emptyset) = f(\emptyset) + f(\emptyset)$), both sides equal zero.

**Inductive Case**: Assume the theorem holds for any set of size $n$. 
- For a set $A_0$ of size $n+1$, we can write $A_0 = \{a\} \cup A$ where $A$ has size $n$.
- We have $\bigcup_{a' \in A_0} x(a') = x(a) \cup \bigcup_{b \in A} x(b)$
- Using the properties of $f$ and $P$, we can write:
  $$f\left(x(a) \cup \bigcup_{b \in A} x(b)\right) = f(x(a)) + f\left(\bigcup_{b \in A} x(b)\right) - f\left(x(a) \cap \bigcup_{b \in A} x(b)\right)$$
- By applying the distributive law, we have:
  $$x(a) \cap \bigcup_{b \in A} x(b) = \bigcup_{b \in A} (x(a) \cap x(b))$$
- By the inductive hypothesis, we can express both $f\left(\bigcup_{b \in A} x(b)\right)$ and $f\left(\bigcup_{b \in A} (x(a) \cap x(b))\right)$ using the inclusion-exclusion formula.
- After algebraic manipulations and carefully regrouping terms, we arrive at the desired inclusion-exclusion formula for $A_0$.

### Mathematical insight
The inclusion-exclusion principle is a fundamental counting technique in combinatorics that extends to measure theory and probability. This theorem generalizes the principle to any real-valued function that satisfies additivity on certain subsets.

The key insight is that the principle works not only for set cardinality but for any "measure-like" function that is additive on disjoint sets. The parameter $P$ allows for restricting the domain to sets where the additivity property holds, making it applicable to a wider range of scenarios such as probability measures on measurable sets.

The indexed version of the formula makes it particularly useful for applications where we need to work with collections of sets indexed by some other set, which is common in probability theory and measure theory.

### Dependencies
- Basic set theory operations (union, intersection, set difference)
- Properties of finite sets
- Basic arithmetic operations and properties of real numbers
- Mathematical induction

### Porting notes
- The theorem uses a strong induction technique with a separate base case and inductive step.
- The proof relies on manipulating sums over sets, which might require different approaches in other proof assistants.
- The notation `{B | B SUBSET A /\ ~(B = {})}` for "all non-empty subsets of A" might need different syntax in other systems.
- The power notation `pow` for exponentiation and the representation of alternating signs might differ between systems.

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
For any predicate $P$ on sets of type $A$, a function $f$ mapping sets of type $A$ to real numbers, and a collection $A$ of sets, if:
- For any sets $s$ and $t$ where $P(s)$ and $P(t)$ hold and $s$ and $t$ are disjoint, we have $f(s \cup t) = f(s) + f(t)$
- $P(\emptyset)$ holds
- For any sets $s$ and $t$ where $P(s)$ and $P(t)$ hold, we also have $P(s \cap t)$, $P(s \cup t)$, and $P(s \setminus t)$
- $A$ is a finite collection of sets
- For every set $a \in A$, $P(a)$ holds

Then, the following inclusion-exclusion formula holds:
$$f\left(\bigcup A\right) = \sum_{B \subset A, B \neq \emptyset} (-1)^{|B|+1} \cdot f\left(\bigcap B\right)$$

where the sum is taken over all non-empty subsets $B$ of the collection $A$.

### Informal proof
The proof applies the theorem `INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED` with specific parameters:
- The predicate $P$ (unchanged)
- The function $f$ (unchanged) 
- The collection $A$ (unchanged)
- The identity function `\x:A->bool. x` for the indexing function

After applying this theorem, the proof is completed by simplifying with the lemma `IMAGE_ID`, which states that the image of a set under the identity function is the set itself. This simplification step transforms the indexed version of the formula to the desired form stated in the theorem.

### Mathematical insight
This theorem provides a restricted version of the inclusion-exclusion principle for real-valued functions on sets. The principle is fundamental in combinatorics and probability theory.

The key insight is that for functions that behave additively on disjoint sets (satisfying $f(s \cup t) = f(s) + f(t)$ when $s \cap t = \emptyset$), we can express the value of the function on a union of sets in terms of its values on various intersections of those sets.

The restrictions imposed by the predicate $P$ are important as they ensure the function $f$ behaves well on all the relevant set operations (union, intersection, and set difference) that appear in the inclusion-exclusion formula.

This version differs from the general inclusion-exclusion principle by having the restricted domain specified by predicate $P$ and by working specifically with real-valued functions.

### Dependencies
- `INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED`: A more general version of the inclusion-exclusion principle that allows for indexed sets
- `IMAGE_ID`: States that the image of a set under the identity function is the set itself

### Porting notes
When porting this theorem:
1. Ensure that the target system has a well-developed theory of finite sets with operations like UNION, INTER, SUBSET, etc.
2. The power operation on real numbers, specifically $(-1)^n$, should be properly defined for natural number exponents
3. The summation over set comprehension might need to be adapted depending on how the target system handles set iteration
4. The handling of the predicate $P$ as a constraint on sets may require special attention in systems with different type systems

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
For any function $f : \mathcal{P}(A) \to \mathbb{R}$ (where $\mathcal{P}(A)$ is the power set of $A$), any finite set $A \subseteq I$, and any function $x : I \to \mathcal{P}(A)$, if:
1. $f$ is additive on disjoint sets (i.e., $\forall s, t. s \cap t = \emptyset \Rightarrow f(s \cup t) = f(s) + f(t)$), and
2. $A$ is finite,

then the following equality holds:
$$f\left(\bigcup_{i \in A} x(i)\right) = \sum_{B \subseteq A, B \neq \emptyset} (-1)^{|B|+1} \cdot f\left(\bigcap_{i \in B} x(i)\right)$$

where the sum ranges over all non-empty subsets $B$ of $A$.

### Informal proof
This theorem is derived directly from the `INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED` theorem with a specific instantiation.

The proof applies the `INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED` theorem with the predicate $\lambda x. T$ (the always true predicate), which effectively removes any restrictions on the sets involved.

The instantiation of the predicate to $\lambda x. T$ makes the restricted version equivalent to the unrestricted version stated in this theorem, as the restriction becomes trivially satisfied for all sets.

### Mathematical insight
This theorem provides a generalized, indexed form of the Inclusion-Exclusion Principle for real-valued functions that are additive on disjoint sets. The principle is a fundamental counting technique in combinatorics that allows computing the measure (here represented by function $f$) of a union of sets by considering the measures of their various intersections.

The indexing by a set $A$ and function $x$ makes this formulation more general than the standard inclusion-exclusion principle, allowing it to be applied in various contexts where we have a family of sets indexed by elements of another set.

The alternating sign pattern in the formula (determined by $(-1)^{|B|+1}$) is characteristic of inclusion-exclusion formulas, where intersections of an odd number of sets contribute positively and intersections of an even number of sets contribute negatively.

### Dependencies
- `INCLUSION_EXCLUSION_REAL_RESTRICTED_INDEXED`: The restricted version of this theorem that allows for additional predicates on the sets involved.

### Porting notes
When porting this theorem:
- Ensure the target system has a well-defined notion of finite sets, subset relation, and cardinality.
- The powering operation on $-1$ needs careful handling to ensure the correct alternating sign pattern.
- The summation over subsets needs to be properly formalized in the target system, especially the restriction to non-empty subsets.
- The formal representation of function additivity on disjoint sets might need adaptation based on how set operations are defined in the target system.

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
For any function $f$ mapping sets of type $A \to \text{bool}$ to real numbers, and for any finite family $A$ of sets (i.e., $A$ is a set of sets), if $f$ is additive on disjoint sets (that is, $\forall s, t. \text{DISJOINT}(s, t) \Rightarrow f(s \cup t) = f(s) + f(t)$), then:

$$f\left(\bigcup_{s \in A} s\right) = \sum_{B \subseteq A, B \neq \emptyset} (-1)^{|B|+1} \cdot f\left(\bigcap_{s \in B} s\right)$$

Where:
- $\text{UNIONS}~A$ represents the union of all sets in the family $A$
- The sum is over all non-empty subsets $B$ of $A$
- $\text{CARD}~B$ is the cardinality of $B$
- $\text{INTERS}~B$ represents the intersection of all sets in the family $B$

### Informal proof
This theorem is proved by applying the more general theorem `INCLUSION_EXCLUSION_REAL_INDEXED` with specific parameters:
- $f$ is the given function of type $(A \to \text{bool}) \to \text{real}$
- $A$ is the given finite family of sets
- The indexing function is the identity function $\lambda x. x$

After applying this more general theorem with these parameters, the proof is completed by simplifying the expression using the fact that the image of a set under the identity function is the set itself (`IMAGE_ID`).

### Mathematical insight
This theorem represents the Inclusion-Exclusion Principle for real-valued functions on sets. It generalizes the classic combinatorial principle to functions that are finitely additive on disjoint sets.

The Inclusion-Exclusion Principle is a fundamental counting technique in combinatorics that allows us to compute the cardinality of the union of multiple sets. This theorem extends that concept to any real-valued function that respects additivity on disjoint sets.

The formula alternates signs based on the size of the subsets being considered, which is characteristic of the Inclusion-Exclusion Principle. The case where $|B|=1$ gives positive terms, $|B|=2$ gives negative terms, and so on, creating the alternating pattern.

This result is pivotal in measure theory, probability, and various areas of discrete mathematics where set functions need to be computed over unions of sets.

### Dependencies
- **Theorems**:
  - `INCLUSION_EXCLUSION_REAL_INDEXED`: A more general version of the inclusion-exclusion principle for real-valued functions
  - `IMAGE_ID`: States that the image of a set under the identity function is the set itself

### Porting notes
When porting this theorem:
1. Ensure the target system has an appropriate representation of finite sets and families of sets
2. Verify that the target system has corresponding notions for UNIONS (union of a family of sets) and INTERS (intersection of a family of sets)
3. The use of power notation for (-1)^n might need special handling in some systems
4. The sum over subsets might require careful formalization, particularly the filtering condition "B SUBSET A /\ ~(B = {})"

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
For any finite set $s$ of finite sets of type $A$, the cardinality of the union of all sets in $s$ is given by:

$$\text{CARD}(\bigcup_{k \in s} k) = \sum_{t \subseteq s, t \neq \emptyset} (-1)^{|t|+1} \cdot \text{CARD}(\bigcap_{k \in t} k)$$

where:
- $s$ is a finite collection of finite sets
- $\text{CARD}$ denotes the cardinality of a set
- $\bigcup$ denotes the union of a collection of sets
- $\bigcap$ denotes the intersection of a collection of sets
- The sum is taken over all non-empty subsets $t$ of $s$

### Informal proof
This theorem is a special case of a more general inclusion-exclusion principle `INCLUSION_EXCLUSION_REAL_RESTRICTED`. The proof applies this general theorem with specific parameters:

- We use the predicate $P(s) = \text{FINITE}(s)$ to ensure we're working with finite sets
- We use the measure function $f(s) = \text{CARD}(s)$ which returns the cardinality of a set as a real number
- We verify the required conditions for applying the general theorem:
  * The intersection of finite sets is finite
  * The union of finite sets is finite
  * The difference of finite sets is finite
  * The empty set is finite
  * The cardinality of a disjoint union equals the sum of the cardinalities: $\text{CARD}(A \cup B) = \text{CARD}(A) + \text{CARD}(B)$ when $A \cap B = \emptyset$

The result then follows directly from the general inclusion-exclusion principle.

### Mathematical insight
The inclusion-exclusion principle is a fundamental counting technique in combinatorics. It provides a systematic way to count the elements in a union of sets when there are overlaps between these sets.

The formula works by first adding the cardinalities of all individual sets, which counts elements in multiple sets multiple times. It then subtracts the cardinalities of all pairwise intersections, adds back the cardinalities of all three-way intersections, and so on, with alternating signs.

This specific version deals with set cardinalities (the most common application), whereas HOL Light also has more general versions of the principle for arbitrary measure functions.

### Dependencies
- `INCLUSION_EXCLUSION_REAL_RESTRICTED`: The more general inclusion-exclusion principle that this theorem specializes
- `FINITE_INTER`: The intersection of finite sets is finite
- `FINITE_UNION`: The union of finite sets is finite  
- `FINITE_DIFF`: The difference of finite sets is finite
- `FINITE_EMPTY`: The empty set is finite
- `CARD_UNION`: The cardinality of a disjoint union equals the sum of the cardinalities
- `DISJOINT`: Definition of disjoint sets
- `REAL_OF_NUM_ADD`: The real representation of the sum of natural numbers equals the sum of their real representations

### Porting notes
When porting this theorem:
1. Ensure the target system has a well-defined notion of finite sets and cardinality
2. Check if the target system has a more general inclusion-exclusion principle that can be specialized 
3. The recursive structure of how subsets and intersections are handled might require careful attention in systems with different set theory foundations
4. The alternating sign pattern (via the power of -1) might need special handling in type systems that strictly separate integers from other number types

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
For any finite family $s$ of finite sets, the cardinality of the union of sets in $s$ is given by:

$$|{\bigcup}_{k \in s} k| = \sum_{n=1}^{|s|} (-1)^{n+1} \sum_{\substack{t \subseteq s \\ |t| = n}} |{\bigcap}_{k \in t} k|$$

where $s$ is a finite collection of finite sets.

### Informal proof
This theorem proves the standard form of the inclusion-exclusion principle. The proof proceeds as follows:

- We start by applying the more general `INCLUSION_EXCLUSION` theorem.
- Then we use `SUM_IMAGE_GEN` with `CARD` to transform the sum over subsets into a sum over cardinalities.
- We need to show that the domain of the sum is equivalent to the expected range from 1 to CARD(s).
  - This is done by proving the sets are extensionally equal.
  - We use that non-empty subsets correspond exactly to cardinalities from 1 to |s|.
- For each n in the range, we need to show the summands are equal.
  - We extract the constant factor $(-1)^{n+1}$ using `SUM_LMUL`.
  - Then we prove that the sets being summed over are the same (subsets of size n).
- The proof is completed using various arithmetic and set-theoretic facts about cardinality.

### Mathematical insight
The inclusion-exclusion principle is a fundamental counting technique that provides a way to calculate the cardinality of a union of sets. This theorem presents the principle in its most commonly used form, summing over subsets of different sizes.

The alternating signs in the formula (given by $(-1)^{n+1}$) reflect the over-counting that occurs when simply adding cardinalities of sets. For example, elements that appear in two sets are counted twice when adding cardinalities, so we need to subtract the cardinalities of pairwise intersections, and so on.

This formulation is particularly useful in combinatorial problems where we need to count elements satisfying at least one of several conditions.

### Dependencies
No explicit dependencies were provided, but the proof uses:
- `INCLUSION_EXCLUSION`: The more general form of the inclusion-exclusion principle
- `SUM_IMAGE_GEN`: A theorem for transforming sums over images
- `FINITE_SUBSETS_RESTRICT`: Property of finiteness for restricted subsets
- `SUM_EQ`: Extensionality principle for sums
- `SUM_LMUL`: Distributivity of multiplication over finite sums
- Various basic set theory and arithmetic facts

### Porting notes
When porting to other systems:
- Ensure the target system has a more general inclusion-exclusion principle already implemented.
- The formulation uses powers of -1 with alternating signs, which might require careful handling in systems with different treatment of integer powers.
- The proof manipulates finite sums extensively, so check how the target system handles sum indexing and transformation.
- The handling of set operations (unions, intersections) and the `HAS_SIZE` predicate might differ across systems.

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
For any set $s: A \to \text{bool}$ and predicate $p$, if $s$ is finite, then the collection of all subsets $t$ of $s$ that satisfy predicate $p$ is also finite:

$$\forall s: A \to \text{bool}, p. \text{FINITE}(s) \Rightarrow \text{FINITE}(\{t \mid t \subseteq s \land p(t)\})$$

### Informal proof
The proof follows from the fact that the power set of a finite set is finite.

* First, we show that the set $\{t \mid t \subseteq s \land p(t)\}$ is a subset of the power set of $s$, which is $\{t \mid t \subseteq s\}$.
* Since $s$ is finite, by `FINITE_POWERSET`, the power set $\{t \mid t \subseteq s\}$ is also finite.
* Since our target set $\{t \mid t \subseteq s \land p(t)\}$ is a subset of a finite set, it is also finite by `FINITE_SUBSET`.

### Mathematical insight
This theorem is a standard result in set theory and combinatorics, stating that if we filter the power set of a finite set using any predicate, the resulting collection remains finite. This is useful in many combinatorial arguments where we need to work with specific families of subsets that satisfy certain properties.

The result follows naturally from two fundamental properties:
1. The power set of a finite set is finite
2. Any subset of a finite set is finite

### Dependencies
- Theorems:
  - `FINITE_SUBSET`: If a set is a subset of a finite set, then it is finite
  - `FINITE_POWERSET`: The power set of a finite set is finite

### Porting notes
When porting this theorem:
- Ensure that the target system has corresponding theorems about finiteness of power sets and subsets of finite sets
- The proof is straightforward and should be relatively easy to port to any system with basic set theory support
- The use of `SET_TAC[]` in HOL Light automatically handles the set-theoretic reasoning; in other systems, you might need to explicitly prove that the set we're considering is indeed a subset of the power set

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
For any function $f: A \to B$, any set $s \subseteq A$, and any numbers $x$ and $y$, if:
- $s$ is finite
- $f$ is injective on $s$ (i.e., for all $x, y \in s$, if $f(x) = f(y)$ then $x = y$)
- $x = y + \text{card}(f(s))$ where $f(s) = \{f(z) : z \in s\}$ is the image of $s$ under $f$

then $x = y + \text{card}(s)$.

### Informal proof
This theorem follows directly from the theorem `CARD_IMAGE_INJ`, which states that if a function is injective on a finite set, then the cardinality of the image equals the cardinality of the original set.

Given the premises:
- $s$ is finite
- $f$ is injective on $s$
- $x = y + \text{card}(f(s))$

By `CARD_IMAGE_INJ`, we know that $\text{card}(f(s)) = \text{card}(s)$ since $f$ is injective on the finite set $s$.

Substituting this equality into $x = y + \text{card}(f(s))$, we get $x = y + \text{card}(s)$, which is the desired conclusion.

### Mathematical insight
This lemma establishes that injective functions preserve cardinality when applied to finite sets. The result may appear trivial, but it's an important building block in cardinal arithmetic and set theory.

The lemma is particularly useful in formal proofs where we need to manipulate expressions involving cardinalities of sets, especially when working with bijections or injections between sets. It allows us to substitute the cardinality of an image of a set with the cardinality of the original set when the function is injective.

### Dependencies
- Theorems:
  - `CARD_IMAGE_INJ`: If $f$ is injective on a finite set $s$, then $\text{card}(f(s)) = \text{card}(s)$

### Porting notes
When porting this theorem to other systems:
- Ensure that the target system has a comparable notion of finite sets and cardinality
- Check that the system has an equivalent theorem about the cardinality of images under injective functions
- The proof is straightforward and should translate easily to most proof assistants

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
For any element $x$ of type $A$, and any finite set $s$ of type $A$, if $x \notin s$ and $u \subseteq s$, then:

1. $|\{t \mid t \subseteq (x \cup s) \wedge u \subseteq t \wedge |t| \text{ is odd}\}| = |\{t \mid t \subseteq s \wedge u \subseteq t \wedge |t| \text{ is odd}\}| + |\{t \mid t \subseteq s \wedge u \subseteq t \wedge |t| \text{ is even}\}|$

2. $|\{t \mid t \subseteq (x \cup s) \wedge u \subseteq t \wedge |t| \text{ is even}\}| = |\{t \mid t \subseteq s \wedge u \subseteq t \wedge |t| \text{ is even}\}| + |\{t \mid t \subseteq s \wedge u \subseteq t \wedge |t| \text{ is odd}\}|$

Where $|t|$ denotes the cardinality of set $t$.

### Informal proof
The proof establishes a bijection between certain subsets of $s$ and subsets of $x \cup s$ that contain $u$:

- We apply `CARD_ADJUST_LEMMA` with the function that maps a set $u$ to $x \cup u$.

- First, we verify this function is injective on the relevant domain using set-theoretic reasoning.

- Then we show that the union of sets satisfying the constraints is disjoint:
  - For subsets of $s$ containing $u$ with odd cardinality and their images under our mapping
  - For subsets of $s$ containing $u$ with even cardinality and their images under our mapping

- We establish that a set $t$ is in the appropriate collection of subsets of $x \cup s$ containing $u$ if and only if either:
  - $t$ is a subset of $s$ containing $u$ with the appropriate parity, or
  - $t = x \cup v$ for some subset $v$ of $s$ containing $u$ with the opposite parity

- The key observation is that adding element $x$ changes the parity of the cardinality:
  - If $v$ has odd cardinality, then $x \cup v$ has even cardinality
  - If $v$ has even cardinality, then $x \cup v$ has odd cardinality

- This is formalized using the cardinality properties from `CARD_CLAUSES` and the definitions of `EVEN` and `ODD`.

### Mathematical insight
This theorem establishes a recursive relationship between the number of subsets of different parities when adding a new element to a set. When we add a new element $x$ to a set $s$, each subset of $s$ produces a new subset (by including $x$), and this operation flips the parity of the cardinality.

This result is particularly useful in combinatorial counting problems and can be seen as a step in establishing properties of the power set structure, especially when tracking subset cardinality parity. It shows how the counts of odd-cardinality and even-cardinality subsets relate when extending the base set.

The theorem also demonstrates a fundamental property of set cardinality: adding a single element to a set increases its cardinality by exactly 1, which changes even cardinality to odd and vice versa.

### Dependencies
- `CARD_ADJUST_LEMMA`: Used to establish cardinality relationships via bijections
- `FINITE_SUBSETS_RESTRICT`: Shows that the set of subsets satisfying certain restrictions is finite
- `CARD_UNION_EQ`: Used to calculate the cardinality of unions
- `CARD_CLAUSES`: Provides facts about cardinality of sets
- `SUBSET_INSERT_EXISTS`: Characterizes subsets of inserted elements
- Set-theoretic tactics and conversions: `SET_TAC`, `ASM_SIMP_TAC`, `STRIP_TAC`

### Porting notes
When porting this theorem:
- Ensure the target system has a well-developed library for finite sets and cardinality
- The proof relies heavily on set-theoretic automation (via `SET_TAC`), which might need different approaches in systems with less powerful set automation
- The parity concepts (`EVEN`, `ODD`) should be properly defined in the target system
- The bijection argument might need to be made more explicit in systems like Lean or Coq

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
For any finite set $u$ and a proper subset $s \subset u$, the number of subsets $t$ such that $s \subseteq t \subseteq u$ and $|t|$ is even equals the number of subsets $t$ such that $s \subseteq t \subseteq u$ and $|t|$ is odd.

Formally, if $u$ is a finite set and $s$ is a proper subset of $u$, then:
$$|\{t \mid s \subseteq t \subseteq u \text{ and } |t| \text{ is even}\}| = |\{t \mid s \subseteq t \subseteq u \text{ and } |t| \text{ is odd}\}|$$

### Informal proof
The proof uses well-founded induction on the cardinality of $u$.

1. Start with sets $s \subset u$ where $u$ is finite.
2. Since $s$ is a proper subset of $u$, we know there exists an element $x \in u \setminus s$.
3. Define $v = u \setminus \{x\}$.
4. Observe that $s \subseteq v$, and $v$ is finite.
5. Now consider the subsets $t$ such that $s \subseteq t \subseteq u$:
   - For each subset $t$ with $s \subseteq t \subseteq v$, we have $s \subseteq t \subseteq u$.
   - For each subset $t$ with $s \subseteq t \subseteq v$, we can also consider $t \cup \{x\}$, which satisfies $s \subseteq t \cup \{x\} \subseteq u$.
   - These two cases partition all subsets $t$ where $s \subseteq t \subseteq u$.

6. We analyze two cases:
   - Case 1: If $s = v$, then we have equal numbers of even and odd cardinality subsets between $s$ and $u$.
   - Case 2: If $s \subset v$, then by the induction hypothesis, the number of even-sized sets $t$ with $s \subseteq t \subseteq v$ equals the number of odd-sized sets with the same property.
   
7. Additionally, for any set $t$ with $s \subseteq t \subseteq v$:
   - If $|t|$ is even, then $|t \cup \{x\}|$ is odd.
   - If $|t|$ is odd, then $|t \cup \{x\}|$ is even.
   
8. This creates a perfect pairing between even and odd cardinality sets, proving the equation.

### Mathematical insight
This theorem represents a combinatorial result about the distribution of even and odd-sized sets in the collection of all sets that contain a given set $s$ and are contained in another set $u$. It demonstrates that when we have a proper subset relation, the even and odd subsets are perfectly balanced.

The result is related to a more general principle in combinatorics that when considering all subsets of a finite set, exactly half have even cardinality and half have odd cardinality. This theorem extends that idea to a constrained setting where we only consider subsets between two fixed sets $s$ and $u$.

The proof technique illustrates a common strategy in combinatorics: partitioning a collection based on whether an element belongs to a set, and using this to establish bijections between different collections.

### Dependencies
- `CARD_SUBSETS_STEP` - Theorem about cardinality of subsets when adding an element
- `PSUBSET_ALT` - Alternative characterization of proper subset relation
- `FINITE_INSERT` - Theorem about finiteness of sets with insertion
- `CARD_CLAUSES` - Properties of cardinality function

### Porting notes
When porting to other proof assistants:
- Ensure that the target system has appropriate library support for finite sets, cardinality, and even/odd predicates.
- The proof relies on well-founded induction on the cardinality of sets, which may require specific setup in other systems.
- The bijection between even and odd cardinality sets is established implicitly through algebraic manipulations in HOL Light, but might need to be made more explicit in other systems.

---

## SUM_ALTERNATING_CANCELS

### SUM_ALTERNATING_CANCELS
- `SUM_ALTERNATING_CANCELS`

### Type of the formal statement
- theorem

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
For any set $s$ of type $A$ and any function $f$, if:
- $s$ is finite, and
- The number of elements $x \in s$ where $f(x)$ is even is equal to the number of elements where $f(x)$ is odd

Then:
$$\sum_{x \in s} (-1)^{f(x)} = 0$$

### Informal proof
The proof shows that the sum of $(-1)^{f(x)}$ over all $x \in s$ equals zero when the number of elements with even $f(x)$ equals the number with odd $f(x)$.

1. First, we split the sum into two parts:
   $$\sum_{x \in s} (-1)^{f(x)} = \sum_{x \in s \land \text{EVEN}(f(x))} (-1)^{f(x)} + \sum_{x \in s \land \text{ODD}(f(x))} (-1)^{f(x)}$$
   
   This is justified by using the theorem `SUM_UNION_EQ` since the sets $\{x \in s : \text{EVEN}(f(x))\}$ and $\{x \in s : \text{ODD}(f(x))\}$ form a partition of $s$.

2. Next, we simplify the expressions:
   - For even values $f(x)$, $(-1)^{f(x)} = 1$ (since $(-1)^{2n} = 1$ for any integer $n$)
   - For odd values $f(x)$, $(-1)^{f(x)} = -1$ (since $(-1)^{2n+1} = -1$ for any integer $n$)

3. Therefore:
   $$\sum_{x \in s \land \text{EVEN}(f(x))} (-1)^{f(x)} = \sum_{x \in s \land \text{EVEN}(f(x))} 1 = |E|$$
   $$\sum_{x \in s \land \text{ODD}(f(x))} (-1)^{f(x)} = \sum_{x \in s \land \text{ODD}(f(x))} (-1) = -|O|$$
   
   Where $|E|$ and $|O|$ are the cardinalities of the even and odd sets respectively.

4. Since $|E| = |O|$ (given as a hypothesis), we have:
   $$\sum_{x \in s} (-1)^{f(x)} = |E| + (-|O|) = |E| - |O| = 0$$

### Mathematical insight
This theorem provides a simple cancellation property for alternating sums. It formalizes the intuitive idea that when you have an equal number of elements with $f(x)$ being even and odd, the corresponding terms $(-1)^{f(x)}$ will precisely balance each other out (with even values contributing 1 and odd values contributing -1).

This result can be useful in combinatorial proofs, parity arguments, or when working with alternating series. It represents a special case of a more general principle: when terms can be paired in a way that they cancel each other out, their sum is zero.

### Dependencies
- `SUM_UNION_EQ`: Theorem for splitting a sum over the union of two disjoint sets
- `REAL_POW_NEG`: Theorem about powers of negative numbers
- `REAL_POW_ONE`: Theorem about powers of 1
- `SUM_CONST`: Theorem for summing constant functions
- `FINITE_RESTRICT`: Theorem about finiteness of restricted sets
- Various basic arithmetic and set-theoretic operations

### Porting notes
When porting this theorem:
- Ensure that your target system has the necessary infrastructure for working with finite sums
- Check how even/odd predicates are defined in your target system and adjust accordingly
- The proof relies on set partitioning and cardinality arguments, which should be available in most proof assistants

---

## INCLUSION_EXCLUSION_SYMMETRIC

### INCLUSION_EXCLUSION_SYMMETRIC
- `INCLUSION_EXCLUSION_SYMMETRIC`

### Type of the formal statement
- theorem

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
For any functions $f, g : \mathcal{P}(A) \to \mathbb{R}$ (where $\mathcal{P}(A)$ is the power set of $A$), if:

$$\forall s. \text{ FINITE}(s) \Rightarrow g(s) = \sum_{t \subseteq s} (-1)^{|t|} \cdot f(t)$$

then:

$$\forall s. \text{ FINITE}(s) \Rightarrow f(s) = \sum_{t \subseteq s} (-1)^{|t|} \cdot g(t)$$

This is a symmetric form of the Möbius inversion formula, specifically for the inclusion-exclusion principle.

### Informal proof
The proof establishes that we can invert the relationship between functions $f$ and $g$:

* Apply symmetry conversion and transitivity to show equality through an intermediate expression.
* The key intermediate step is to express $f(s)$ as:
  $$\sum_{t \subseteq s} (-1)^{|t|} \cdot \sum_{u \subseteq t, u \subseteq s} (-1)^{|u|} \cdot f(u)$$

* We simplify the nested summation using theorems about sums and subsets.
* The proof then shows this intermediate expression equals:
  $$\sum_{u \subseteq s} \left(\sum_{t : u \subseteq t \subseteq s} (-1)^{|t|}\right) \cdot (-1)^{|u|} \cdot f(u)$$

* For any $u \neq s$, the inner sum $\sum_{t : u \subseteq t \subseteq s} (-1)^{|t|}$ equals zero, using the principle that alternating sums over an even/odd classification cancel.
* When $u = s$, the inner sum equals 1, resulting in exactly $f(s)$.
* Therefore, the entire expression reduces to $f(s)$ as required.

### Mathematical insight
This theorem presents the symmetric form of the inclusion-exclusion principle, which is also known as Möbius inversion on the Boolean lattice. The key insight is that the relationship between functions $f$ and $g$ defined by the inclusion-exclusion formula is symmetric: if $g$ can be expressed as a certain alternating sum involving $f$ over subsets, then $f$ can be expressed the same way in terms of $g$.

This symmetry is particularly elegant and useful in combinatorial mathematics. It allows us to convert between different ways of counting objects, especially when dealing with sets and their properties. The result is due to Ira Gessel, who called it "Symmetric Inclusion-Exclusion."

The theorem can be seen as a special case of Möbius inversion on a partially ordered set (specifically the Boolean lattice of subsets), showing that certain transformations on functions defined over sets are invertible.

### Dependencies
- `SUM_EQ` - Equality of sums when corresponding terms are equal
- `SUM_LMUL`, `SUM_RMUL` - Properties of multiplication distributing over sums
- `SUM_SUM_RESTRICT` - Reordering of nested sums
- `FINITE_POWERSET`, `FINITE_SUBSET`, `FINITE_SUBSETS_RESTRICT` - Finiteness properties of sets
- `SUM_DELTA` - Sum of a function that is zero except at one point
- `SUM_ALTERNATING_CANCELS` - Cancellation in alternating sums
- `CARD_SUBSUPERSETS_EVEN_ODD` - Parity properties of subset cardinalities

### Porting notes
When porting this theorem:
- The proof relies heavily on set-theoretic manipulation and properties of finite sets, which may require different approaches in other systems.
- The alternating sum cancellation property (`SUM_ALTERNATING_CANCELS`) and the parity properties of subset cardinalities are key lemmas that might need to be established separately.
- The theorem is particularly relevant for combinatorial mathematics and may connect to Möbius inversion in other systems.
- The proof structure involves establishing an intermediate equality and showing that most terms in a double summation vanish, which is a common pattern in combinatorial proofs.

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
For any functions $f, g: \mathcal{P}(A) \to \mathbb{R}$ (where $\mathcal{P}(A)$ is the power set of $A$), if:

$$\forall s. \text{FINITE}(s) \Rightarrow g(s) = \sum_{t \subseteq s} f(t)$$

Then for any finite set $s$:

$$f(s) = \sum_{t \subseteq s} (-1)^{|s| - |t|} \cdot g(t)$$

Where $|s|$ and $|t|$ denote the cardinality of sets $s$ and $t$ respectively.

### Informal proof
This theorem is the Möbius inversion formula for the inclusion-exclusion principle. The proof leverages the symmetric version of inclusion-exclusion:

- We apply the symmetric version of inclusion-exclusion principle (theorem `INCLUSION_EXCLUSION_SYMMETRIC`) with the function $t \mapsto (-1)^{|t|} \cdot f(t)$ and the given function $g$.
- First, we verify that the premise of the symmetric version is satisfied, using the assumption about $g$.
- Then, for a finite set $s$, we multiply both sides of the resulting equation by $(-1)^{|s|}$.
- We simplify powers of $-1$ using properties of exponents, noting that $(-1)^{2n} = 1$ for even $n$.
- Through algebraic manipulations involving $(-1)^{|s| - |t|}$, we obtain the desired formula for $f(s)$.
- The proof uses several arithmetic properties of real numbers and powers, along with theorems about set cardinality and subset relationships.

### Mathematical insight
The Möbius inversion formula provides a way to recover the function $f$ from the function $g$ when $g$ is defined as a sum of values of $f$ over all subsets. This is a fundamental result in combinatorics and is equivalent to the inclusion-exclusion principle.

While the symmetric version (which this theorem builds upon) expresses a relationship between two functions with sums over all subsets, this version gives a more direct inversion formula that allows reconstructing $f$ from $g$. The alternating signs in the formula (represented by the powers of $-1$) are characteristic of the Möbius function for the Boolean lattice of subsets.

This result has applications in probability theory, number theory, and combinatorial counting problems where inclusion-exclusion is used.

### Dependencies
- Theorems:
  - `INCLUSION_EXCLUSION_SYMMETRIC`: The symmetric version of the inclusion-exclusion principle
  - `EVEN_ADD`: Properties of even numbers under addition
  - `REAL_POW_ONE`: Properties of powers of 1
  - `REAL_POW_NEG`: Properties of powers of negative numbers
  - `REAL_MUL_LID`: Left identity property of multiplication
  - `CARD_SUBSET`: Theorem about cardinality of subsets
  - Various arithmetic theorems for real numbers and powers

### Porting notes
When porting this theorem:
- Ensure your target system has a well-developed theory of finite sets with subset relations
- The proof relies heavily on properties of exponentiation, specifically with base $-1$
- The target system should have good automation for algebraic manipulations of real numbers
- Be careful with the handling of sums over sets defined by predicates (like `{t | t SUBSET s}`) as different proof assistants handle this in different ways

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
For any real-valued function $f$ defined on a finite set $s$ of type $A$, the following identity holds:

$$\prod_{x \in s} (1 - f(x)) = \sum_{t \subseteq s} (-1)^{|t|} \cdot \prod_{x \in t} f(x)$$

where:
- $\prod_{x \in s} (1 - f(x))$ denotes the product of $(1 - f(x))$ for all $x \in s$
- The sum is taken over all subsets $t$ of $s$
- $|t|$ (denoted as CARD $t$ in HOL Light) represents the cardinality of set $t$
- $\prod_{x \in t} f(x)$ denotes the product of $f(x)$ for all $x \in t$

### Informal proof
The proof proceeds by strong induction on the finite set $s$:

* Base case: When $s = \emptyset$
  - The left side is $\prod_{x \in \emptyset} (1 - f(x)) = 1$ (empty product)
  - On the right side, the only subset of the empty set is itself
  - So we get $\sum_{t \subseteq \emptyset} (-1)^{|t|} \cdot \prod_{x \in t} f(x) = (-1)^0 \cdot \prod_{x \in \emptyset} f(x) = 1 \cdot 1 = 1$

* Inductive step: For a non-empty set with $x \in s$, we assume the identity holds for all smaller sets
  - We partition the subsets of $s' = \{x\} \cup s$ into:
    1. Subsets not containing $x$: $\{t \mid t \subseteq s\}$
    2. Subsets containing $x$: $\{t \mid t = \{x\} \cup u \text{ for some } u \subseteq s\}$
  
  - The product on the left side can be written as:
    $$\prod_{y \in s'} (1 - f(y)) = (1 - f(x)) \cdot \prod_{y \in s} (1 - f(y))$$

  - Using the induction hypothesis for the second factor:
    $$\prod_{y \in s} (1 - f(y)) = \sum_{t \subseteq s} (-1)^{|t|} \cdot \prod_{y \in t} f(y)$$

  - Substituting this, we get:
    $$(1 - f(x)) \cdot \sum_{t \subseteq s} (-1)^{|t|} \cdot \prod_{y \in t} f(y)$$

  - Distributing $(1 - f(x))$, we have:
    $$\sum_{t \subseteq s} (-1)^{|t|} \cdot \prod_{y \in t} f(y) - f(x) \cdot \sum_{t \subseteq s} (-1)^{|t|} \cdot \prod_{y \in t} f(y)$$

  - The second term can be rewritten as:
    $$f(x) \cdot \sum_{t \subseteq s} (-1)^{|t|} \cdot \prod_{y \in t} f(y) = \sum_{t \subseteq s} (-1)^{|t|} \cdot f(x) \cdot \prod_{y \in t} f(y) = \sum_{t \subseteq s} (-1)^{|t|} \cdot \prod_{y \in \{x\} \cup t} f(y)$$

  - Using the key lemma that $\{t \mid t = \{x\} \cup u \text{ for some } u \subseteq s\} = \{\{x\} \cup t \mid t \subseteq s\}$, and noting that $|\{x\} \cup t| = |t| + 1$ when $x \notin t$
  
  - This gives us:
    $$\sum_{t \subseteq s} (-1)^{|t|} \cdot \prod_{y \in t} f(y) - \sum_{t \subseteq s} (-1)^{|t|} \cdot \prod_{y \in \{x\} \cup t} f(y) = \sum_{t \subseteq s} (-1)^{|t|} \cdot \prod_{y \in t} f(y) + \sum_{t \subseteq s} (-1)^{|t|+1} \cdot \prod_{y \in \{x\} \cup t} f(y)$$

  - Which combines to exactly the sum over all subsets of $s'$, completing the proof.

### Mathematical insight
This theorem provides a combinatorial identity that is a function-based version of the principle of inclusion-exclusion. It gives a way to express a product of terms of the form $(1-f(x))$ as a sum of products, with appropriate signs. 

The result is fundamental in combinatorial mathematics and has applications in probability theory (particularly when computing the probability of the complement of a union of events), number theory, and other areas where the inclusion-exclusion principle is applicable.

This function-based version is particularly useful when working with generating functions or when computing certain probabilistic quantities where multiplicative structures need to be converted to additive ones.

### Dependencies
No explicit dependencies were provided, but the proof uses standard facts about:
- Finite sets and induction on finite sets
- Set operations and properties
- Basic real arithmetic

### Porting notes
When porting this theorem to other systems:
- Ensure that the notion of product over a set is well-defined in your target system
- The proof relies on strong induction on finite sets, which should be available in most proof assistants
- Pay attention to how empty products are handled (typically defined as 1)
- The manipulation of set comprehensions is central to the proof strategy

---

