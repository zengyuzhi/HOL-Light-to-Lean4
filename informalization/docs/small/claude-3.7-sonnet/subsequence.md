# subsequence.ml

## Overview

Number of statements: 5

This file formalizes the Erdos-Szekeres theorem, which states that any sequence of length at least (r-1)(s-1)+1 contains either an ascending subsequence of length r or a descending subsequence of length s. The implementation includes definitions of increasing and decreasing subsequences, along with the necessary lemmas to prove the main theorem. No external imports are needed as the file is self-contained, focusing specifically on this combinatorial result about sequence properties.

## lemma

### lemma

### Type of the formal statement
- theorem

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
For any function $f$ and set $s$, the set $s$ equals the union of all sets $\{x \in s \mid f(x) = a\}$ where $a$ ranges over the image of $f$ on $s$. Formally:

$$\forall f, s.\ s = \bigcup_{a \in f(s)} \{x \in s \mid f(x) = a\}$$

### Informal proof
This theorem is proven through set-theoretic reasoning:

1. The proof begins by reducing the goal to showing extensional equality of sets (using `EXTENSION`), so we need to prove that for all elements $x$, $x \in s$ if and only if $x$ is in the union on the right side.

2. We rewrite the right side using:
   - `IN_UNIONS`: $x \in \bigcup S \iff \exists t.\ t \in S \land x \in t$
   - `IN_ELIM_THM`: $x \in \{y \mid P(y)\} \iff P(x)$
   - `IN_IMAGE`: $y \in \{f(x) \mid x \in s\} \iff \exists x.\ x \in s \land y = f(x)$

3. After these rewrites, the goal involves conjunctions and existential quantifiers that are manipulated using:
   - `LEFT_AND_EXISTS_THM`: $(\exists x. P(x)) \land Q \iff \exists x. P(x) \land Q$ (when $x$ is not free in $Q$)
   - `SWAP_EXISTS_THM`: $\exists x. \exists y. P(x, y) \iff \exists y. \exists x. P(x, y)$
   - `UNWIND_THM2`: Simplifies nested existential quantifiers
   - `GSYM CONJ_ASSOC`: Regroups conjunctions using associativity

4. Finally, the proof is completed using `SET_TAC[]` which provides automated reasoning for set-theoretic goals.

### Mathematical insight
This theorem provides a fundamental method for partitioning a set into disjoint subsets based on a function. It expresses that any set can be decomposed into the union of preimages under a function.

The result is essentially the observation that a function $f$ partitions a set $s$ into equivalence classes, where two elements are equivalent if they map to the same value under $f$. The theorem states that the original set is precisely the union of these equivalence classes.

This decomposition is fundamental in set theory and is widely used in mathematics, particularly in analysis and abstract algebra. It's a key principle underlying the concept of a partition of a set and is related to the fiber of a function.

### Dependencies
- `EXTENSION`: Set extensionality theorem
- `IN_UNIONS`: Membership criteria for set unions 
- `IN_ELIM_THM`: Membership criteria for set comprehensions
- `IN_IMAGE`: Membership criteria for function images
- `LEFT_AND_EXISTS_THM`: Logical manipulation of existential quantifiers
- `SWAP_EXISTS_THM`: Reordering of existential quantifiers
- `UNWIND_THM2`: Simplification of nested existentials
- `GSYM CONJ_ASSOC`: Associativity of conjunction
- `SET_TAC[]`: Automated set-theoretic reasoning tactic

### Porting notes
When porting to other systems, this proof should be relatively straightforward as it relies on standard set-theoretic principles. The main considerations are:

1. Ensure that set comprehension notation is properly supported in the target system
2. Check how set unions and function images are defined
3. The automated `SET_TAC[]` might need to be replaced with explicit reasoning in systems with different automation capabilities

---

## PIGEONHOLE_LEMMA

### PIGEONHOLE_LEMMA

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
For any function $f : A \to B$, any finite set $s \subseteq A$, and any natural number $n$, if 
$$(n - 1) \cdot |f(s)| < |s|$$
where $f(s)$ denotes the image of $s$ under $f$ and $|\cdot|$ denotes cardinality, then there exists a subset $t \subseteq s$ with exactly $n$ elements and a value $a \in B$ such that $f(x) = a$ for all $x \in t$.

In other words, if a finite set has more elements than $(n-1)$ times the cardinality of its image under some function, then there must exist a subset of size $n$ where all elements map to the same value under that function.

### Informal proof
The proof uses a partitioning argument based on the values of $f$:

- First, we use the `lemma` which states that any set $s$ can be expressed as the union of subsets $\{x \in s \mid f(x) = a\}$ for all $a \in f(s)$.

- We proceed by contraposition: assume that there is no subset $t \subseteq s$ of size $n$ such that all elements of $t$ map to the same value under $f$.

- This means that for every value $a \in f(s)$, the set $\{x \in s \mid f(x) = a\}$ has cardinality less than $n$.

- Since $s$ is the union of these sets and none can have cardinality $n$ or higher, we have:
  $$|s| \leq \sum_{a \in f(s)} |\{x \in s \mid f(x) = a\}| \leq (n-1) \cdot |f(s)|$$

- This contradicts our original assumption that $(n-1) \cdot |f(s)| < |s|$.

- To formally complete the proof, we use the fact that if there's no subset of size $n$ with constant $f$-value, then all sets $\{x \in s \mid f(x) = a\}$ must have size at most $n-1$.

- Using the `CHOOSE_SUBSET` theorem, we can select a subset with exactly $n$ elements from any set with cardinality at least $n$, which leads to our desired conclusion.

### Mathematical insight
This theorem is a generalized form of the pigeonhole principle, which states that if you have more objects (pigeons) than containers (holes), at least one container must contain more than one object. Here, we're looking for $n$ objects that all map to the same value.

The condition $(n-1) \cdot |f(s)| < |s|$ can be understood as saying: "if we were to put at most $n-1$ elements in each 'bin' corresponding to a value in the image of $f$, we couldn't fit all elements of $s$." Therefore, at least one bin must contain at least $n$ elements.

This result is fundamental in combinatorics and has many applications in discrete mathematics, including the analysis of algorithms, graph theory, and number theory.

### Dependencies
- Theorems:
  - `lemma`: Expresses a set as a union of subsets based on function values
  - `CARD_UNIONS_LE`: Upper bound on cardinality of union of sets
  - `CHOOSE_SUBSET`: Ability to choose a subset of specified size
  - `FINITE_SUBSET`, `FINITE_IMAGE`: Properties of finite sets
  - `HAS_SIZE`: Definition relating to set cardinality

### Porting notes
When implementing this theorem in other proof assistants:
- Ensure the target system has a well-developed library for finite sets and their cardinality
- Pay attention to how the target system handles set comprehensions and image sets
- The contrapositive reasoning pattern may require different tactical approaches in other systems
- The `SET_TAC` tactic in HOL Light handles several set-theoretic simplifications automatically; these steps might need explicit proof in other systems

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
A function $f: \mathbb{N} \to \mathbb{R}$ is monotonic on a set $s$ with respect to an ordering relation $r$ if and only if for all indices $i, j \in s$ such that $i \leq j$, the relation $r(f(i), f(j))$ holds.

Formally:
$$\text{mono\_on}(f, r, s) \iff \forall i, j. (i \in s \land j \in s \land i \leq j) \Rightarrow r(f(i), f(j))$$

### Informal proof
This is a definition, not a theorem, so no proof is provided.

### Mathematical insight
This definition generalizes the concept of monotonicity for sequences (functions from natural numbers). The key aspects of this definition are:

1. It allows monotonicity to be restricted to a subset $s$ of natural numbers, rather than requiring monotonicity on the entire domain.
2. It parameterizes the ordering relation $r$, making it flexible enough to represent:
   - Non-decreasing sequences when $r$ is $\leq$
   - Strictly increasing sequences when $r$ is $<$
   - Non-increasing sequences when $r$ is $\geq$
   - Strictly decreasing sequences when $r$ is $>$

This generalized definition is particularly useful in analysis when working with subsequences or when analyzing the behavior of sequences on specific subsets of their domains.

### Dependencies
#### Definitions
- `real`: Defines a complex number to be real if its imaginary part is zero.

### Porting notes
When porting this definition:
1. Ensure the target system has a way to represent functions from natural numbers to real numbers.
2. The relation parameter $r$ should be a binary relation on real numbers.
3. The definition uses the HOL Light's membership relation `IN`, which should be translated to the appropriate set membership notation in the target system.
4. Note that this definition assumes the natural ordering on natural numbers ($\leq$) but parameterizes the ordering on real numbers.

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
For any sets $s$ and $t$, if $t \subseteq s$ and the function $f: \mathbb{N} \rightarrow \mathbb{R}$ is monotone on $s$ with respect to the relation $r$, then $f$ is also monotone on $t$ with respect to $r$.

Formally, $\forall s, t. t \subseteq s \land \text{mono\_on}(f, r, s) \Rightarrow \text{mono\_on}(f, r, t)$, where $\text{mono\_on}(f, r, s)$ means that for all $i, j \in s$ such that $i \leq j$, we have $r(f(i), f(j))$.

### Informal proof
The proof follows directly from the definitions:

1. We start by expanding the definitions of `mono_on` and `SUBSET` in the goal.
   
2. After expansion, the goal becomes: 
   $$\forall s, t. (\forall x. x \in t \Rightarrow x \in s) \land (\forall i, j. i \in s \land j \in s \land i \leq j \Rightarrow r(f(i), f(j))) \Rightarrow (\forall i, j. i \in t \land j \in t \land i \leq j \Rightarrow r(f(i), f(j)))$$
   
3. This is a straightforward logical consequence, as any $i, j$ that are in $t$ are also in $s$ (by the subset relation), and therefore the monotonicity condition for elements in $s$ applies to them as well.

4. The automated theorem prover (MESON) completes the proof.

### Mathematical insight
This theorem establishes the intuitive property that monotonicity is preserved when restricting to a subset of the domain. It shows that monotonicity is a "hereditary" property with respect to set inclusion - if a function behaves monotonically on a larger set, it will continue to behave monotonically when we only consider a smaller subset of elements.

This is a fundamental property used in many proofs involving monotone functions, as it allows us to transfer monotonicity properties from a larger domain to a smaller one, which is often needed when working with subsequences or restricted domains.

### Dependencies
#### Definitions
- `mono_on` - Defines when a function is monotone on a set with respect to a relation
- `SUBSET` - Set inclusion relation

#### Theorems
None explicitly used beyond standard logic and set theory

### Porting notes
This theorem should be straightforward to port to other proof assistants as it relies only on basic set theory and the definition of monotonicity on a set. The definition of `mono_on` might need to be adapted to match the target system's typing conventions, particularly regarding the handling of function types and relations.

---

## ERDOS_SZEKERES

### ERDOS_SZEKERES

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
The Erdős–Szekeres theorem states that for any function $f : \mathbb{N} \to \mathbb{R}$ and any natural numbers $m$ and $n$, at least one of the following holds:
- There exists a subset $s$ of $\{1, 2, \ldots, m \cdot n + 1\}$ with cardinality $m + 1$ such that $f$ is monotonically increasing on $s$ (i.e., for all $i, j \in s$ with $i \leq j$, we have $f(i) \leq f(j)$).
- There exists a subset $s$ of $\{1, 2, \ldots, m \cdot n + 1\}$ with cardinality $n + 1$ such that $f$ is monotonically decreasing on $s$ (i.e., for all $i, j \in s$ with $i \leq j$, we have $f(i) \geq f(j)$).

Where $mono\_on\,f\,r\,s$ means that for all $i, j \in s$ with $i \leq j$, the relation $r$ holds between $f(i)$ and $f(j)$.

### Informal proof
The proof proceeds as follows:

- For each $i \in \{1, 2, \ldots, m \cdot n + 1\}$, we define $t(i)$ to be the maximum length of an increasing subsequence starting at $i$. More precisely, $t(i)$ is defined as the maximum $k$ such that there exists a subset $s$ of $\{1, 2, \ldots, m \cdot n + 1\}$ of size $k$ where:
  - $s$ contains $i$
  - $f$ is monotonically increasing on $s$
  - All elements in $s$ are $\geq i$

- We then check if there exists an $i$ with $t(i) \geq m + 1$. If so, we have found an increasing subsequence of length $m + 1$, and we're done with the first case.

- If no such $i$ exists, then we know that $1 \leq t(i) \leq m$ for all $i \in \{1, 2, \ldots, m \cdot n + 1\}$. Since $t$ maps from a set of size $m \cdot n + 1$ to $\{1, 2, \ldots, m\}$, by the Pigeonhole Principle (specifically using `PIGEONHOLE_LEMMA`), there must exist a subset $u$ of size $n + 1$ and a value $k$ such that $t(i) = k$ for all $i \in u$.

- We then prove that $f$ is monotonically decreasing on $u$. Consider any $i, j \in u$ with $i \leq j$. We need to show $f(i) \geq f(j)$.

- We prove this by contradiction. If $f(i) < f(j)$, then any increasing subsequence starting at $j$ could be prepended with $i$ to form a longer increasing subsequence starting at $i$. This would make $t(i) > t(j)$, contradicting our assumption that $t(i) = t(j) = k$ for all elements in $u$.

Therefore, either we have an increasing subsequence of length $m + 1$ or a decreasing subsequence of length $n + 1$.

### Mathematical insight
The Erdős–Szekeres theorem is a fundamental result in Ramsey theory. It states that any sequence of distinct real numbers of length at least $(m-1)(n-1)+1$ contains either an increasing subsequence of length $m$ or a decreasing subsequence of length $n$. 

The theorem presented here is a slight variation where the sequence length is $m \cdot n + 1$ and the subsequence lengths are $m+1$ and $n+1$ respectively.

This result has applications in various areas of mathematics including combinatorics and discrete geometry. Intuitively, it shows that in any sufficiently large sequence, some structure (in this case, monotonicity) must emerge - complete disorder is impossible beyond certain sizes.

The proof cleverly uses the pigeonhole principle, defining a function that maps each element to the length of the longest increasing subsequence starting at that element. When no increasing subsequence of the desired length exists, the pigeonhole principle forces many elements to have the same value under this function, which can then be shown to form a decreasing subsequence.

### Dependencies
- **Theorems:**
  - `PIGEONHOLE_LEMMA`: Core theorem used in the proof, applying the pigeonhole principle.
  - `MONO_ON_SUBSET`: Shows that monotonicity is preserved on subsets.
  - `REAL_NOT_LT`: Equivalence between $\neg(x < y)$ and $y \leq x$.
  - `REAL_LE_REFL`: Reflexivity of $\leq$ on reals.
  - `REAL_LT_IMP_LE`: Implication from $<$ to $\leq$.
  - `REAL_LE_TRANS`: Transitivity of $\leq$ on reals.

- **Definitions:**
  - `mono_on`: Defines monotonicity on a set with respect to a relation.

### Porting notes
When porting this theorem:
1. Make sure the supporting definition of `mono_on` is properly implemented.
2. The proof relies heavily on the pigeonhole principle, specifically through `PIGEONHOLE_LEMMA`, which should be ported first.
3. This proof builds a function through a complex existential construction - systems with dependent types might handle this differently than HOL Light does.
4. The proof uses multiple set-theoretic manipulations; ensure the target system has sufficient set theory support.

---

