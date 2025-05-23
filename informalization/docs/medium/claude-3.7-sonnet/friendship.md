# friendship.ml

## Overview

Number of statements: 23

This file formalizes the Friendship Theorem, which states that in a party where any two people have exactly one common friend, there must exist a universal friend (someone who is friends with everyone else). The proof follows the approach presented in "Combinatorics Tutorial 2: Friendship Theorem" by MathOlymp.com, attributed to J. Q. Longyear and T. D. Parsons. The formalization relies on number theory and combinatorial concepts, leveraging definitions from prime.ml and pocklington.ml.

## GCD_INDUCT

### GCD_INDUCT
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
The GCD_INDUCT theorem provides an induction principle for proofs involving the greatest common divisor (gcd). It states:

For any predicate $P$, if:
- For all natural numbers $m$ and $n$, $P(m) \land P(m+n) \Rightarrow P(n)$

Then for all natural numbers $m$ and $n$:
- $P(m) \land P(n) \Rightarrow P(\text{gcd}(m,n))$

### Informal proof
The proof uses well-founded induction on the sum $m + n$ and proceeds by cases:

- We use well-founded induction on the sum $m + n$.
- We apply the "without loss of generality" principle to assume $m \leq n$.
- Case 1: If $m = 0$, then $\text{gcd}(m,n) = \text{gcd}(0,n) = n$ (by GCD_0).
  Since we know $P(n)$ by assumption, we're done.
- Case 2: If $m > 0$, we apply our premise "$P(m) \land P(m+n) \Rightarrow P(n)$" with the values $m$ and $n-m$:
  - We know $P(m)$ by assumption
  - We know $P(m + (n-m))$ which simplifies to $P(n)$, which we know by assumption
  - Therefore, we get $P(n-m)$
- Then we apply the induction hypothesis to $\text{gcd}(m, n-m)$
  - We know $P(m)$ and $P(n-m)$ from above
  - Since $m > 0$ and $m \leq n$, we have $m + (n-m) < m + n$, so induction applies
  - Therefore, $P(\text{gcd}(m, n-m))$
- Finally, we use the identity $\text{gcd}(m, n) = \text{gcd}(m, n-m)$ (from GCD_ADD)
- This completes the proof.

### Mathematical insight
This theorem provides a powerful inductive principle specifically tailored for proofs about greatest common divisors. It reduces proving properties of GCD to proving a simpler property about natural numbers.

The key insight is that we can use the Euclidean algorithm's recursion pattern to establish properties of GCD. The condition "$P(m) \land P(m+n) \Rightarrow P(n)$" captures a fundamental number-theoretic relationship that, when satisfied, allows properties to descend through the GCD operation.

This induction principle is particularly useful for proving that GCD preserves certain properties of numbers, such as various number-theoretic invariants.

### Dependencies
- `GCD_0`: For all $a$, $\text{gcd}(0,a) = a$ and $\text{gcd}(a,0) = a$
- `GCD_ADD`: States that $\text{gcd}(a+b,b) = \text{gcd}(a,b)$, $\text{gcd}(b+a,b) = \text{gcd}(a,b)$, $\text{gcd}(a,a+b) = \text{gcd}(a,b)$, and $\text{gcd}(a,b+a) = \text{gcd}(a,b)$
- `GCD_SYM`: For all $a$ and $b$, $\text{gcd}(a,b) = \text{gcd}(b,a)$

### Porting notes
When porting this theorem:
- Ensure your system has a well-founded induction principle on natural numbers
- The proof relies on the symmetry of GCD and the properties of GCD with addition, so these relationships need to be established first
- The "without loss of generality" tactic (WLOG_LE) can be implemented using case analysis on $m \leq n$ vs $n < m$

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
For any sequence $x$ and natural numbers $m$ and $n$, if $x$ is periodic with period $m$ (i.e., $\forall i. x(i + m) = x(i)$) and also periodic with period $n$ (i.e., $\forall i. x(i + n) = x(i)$), then $x$ is periodic with period $\gcd(m,n)$ (i.e., $\forall i. x(i + \gcd(m,n)) = x(i)$).

### Informal proof
This theorem is proved by induction on the structure of the greatest common divisor (GCD).

* The proof uses `GCD_INDUCT`, which is a principle that allows reduction of the problem to simpler cases based on the Euclidean algorithm for computing GCD.

* By the properties of GCD, if $m = n \cdot q + r$ where $r < n$, then $\gcd(m,n) = \gcd(n,r)$.

* The proof then uses the periodicity of the sequence with periods $m$ and $n$ to establish that it must also be periodic with period $r = m - n \cdot q$.

* Since $\gcd(m,n) = \gcd(n,r)$, the sequence must also be periodic with period $\gcd(m,n)$.

* The final step uses `MESON_TAC[ADD_AC]` to handle the algebraic manipulations involving addition, using the associativity and commutativity properties of addition.

### Mathematical insight
This theorem formalizes the well-known result that if a sequence has two periods, then it also has their greatest common divisor as a period. This is a fundamental result in number theory and has applications in various areas including string periodicity problems, pattern matching, and discrete signal processing.

The result is intuitive: if you can shift the sequence by $m$ positions and get the same sequence, and also shift by $n$ positions for the same effect, then you can construct a shift by $\gcd(m,n)$ using a linear combination of shifts by $m$ and $n$, due to Bézout's identity: $\gcd(m,n) = sm + tn$ for some integers $s$ and $t$.

### Dependencies
- Theorems:
  - `GCD_INDUCT`: Induction principle for greatest common divisor
  - `ADD_AC`: Associativity and commutativity of addition

### Porting notes
When porting this theorem:
1. Ensure the target system has a suitable induction principle for GCD similar to `GCD_INDUCT`
2. The proof relies on automated reasoning with `MESON_TAC`, so in systems with less powerful automation, you might need to provide more explicit steps for the arithmetic reasoning
3. The theorem assumes sequences are represented as functions from natural numbers, make sure your target system supports this representation or adapt accordingly

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
For any function $x: \mathbb{N} \to \alpha$ and natural numbers $m$ and $n$, if:
- $x(i + m) = x(i)$ for all $i$
- $x(i + n) = x(i)$ for all $i$
- $m$ and $n$ are coprime (i.e., $\gcd(m,n) = 1$)

Then $x(i) = x(0)$ for all $i$.

### Informal proof
This theorem shows that if a sequence is periodic with two periods $m$ and $n$ that are coprime, then the sequence is constant.

The proof uses induction on $i$:

- Base case: For $i = 0$, trivially $x(0) = x(0)$.
- Inductive step: Assume the result holds for some $i$, we show it holds for $i+1$.
  
The proof leverages two key theorems:
1. `LOOP_GCD`: If a sequence has periods $m$ and $n$, then it also has period $\gcd(m,n)$
2. `COPRIME_GCD`: Two numbers $m$ and $n$ are coprime if and only if $\gcd(m,n) = 1$

Since $m$ and $n$ are coprime, $\gcd(m,n) = 1$, which means the sequence has period 1. This implies $x(i+1) = x(i)$ for all $i$, and combined with the induction hypothesis that $x(i) = x(0)$, we get $x(i+1) = x(0)$, completing the induction.

### Mathematical insight
This theorem is a fundamental result in the theory of periodic sequences. It establishes that when a sequence has two periods that are coprime, the sequence must be constant. The result has applications in various fields including number theory, combinatorics, and the study of recurrence relations.

Intuitively, this makes sense because if a sequence repeats every $m$ steps and every $n$ steps where $\gcd(m,n) = 1$, then by the Chinese remainder theorem, we can reach any offset from any other offset, making all values in the sequence equal.

This is a discrete version of a more general principle that applies to functions with multiple periods.

### Dependencies
##### Theorems
- `LOOP_GCD`: If a sequence has periods $m$ and $n$, then it also has period $\gcd(m,n)$
- `COPRIME_GCD`: Two numbers $m$ and $n$ are coprime if and only if $\gcd(m,n) = 1$

### Porting notes
When implementing this in other systems:
1. Ensure that the dependency theorems, especially `LOOP_GCD`, are properly defined first
2. Depending on the system, you may need to explicitly consider the type of the function $x$, which in HOL Light can be polymorphic
3. The use of `ASM_MESON_TAC` indicates that the final step uses automated reasoning - in other systems, you may need to provide more explicit steps for the inductive case

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
Let $R$ be a relation on a finite set $s$. If:
- $R$ is reflexive on $s$: for all $x \in s$, we have $R(x,x)$
- $R$ is symmetric on $s$: for all $x, y$, if $R(x,y)$ then $R(y,x)$
- $R$ is transitive on $s$: for all $x, y, z$, if $R(x,y)$ and $R(y,z)$ then $R(x,z)$
- All equivalence classes have the same size $k$: for all $x \in s$, $|\{y \in s \mid R(x,y)\}| = k$

Then $k$ divides $|s|$ (the cardinality of set $s$).

### Informal proof
We prove this by induction on the cardinality of $s$.

**Base case**: If $s = \emptyset$, then $|s| = 0$, and since $k$ divides 0 for any $k$ (by the theorem `DIVIDES_0`), the result holds.

**Inductive step**: Assume $s \neq \emptyset$ and the result holds for all sets with cardinality less than $|s|$.

Let $a$ be an element of $s$. Consider the set $\{y \in s \mid \neg R(a,y)\}$, which is the complement of $a$'s equivalence class in $s$.

We can apply the induction hypothesis to this set if:
1. It is finite - which follows from being a subset of finite set $s$
2. It is a proper subset of $s$ - which is true because $a$ is in $s$ but not in this set (since $R(a,a)$ by reflexivity)
3. The relation $R$ remains an equivalence relation on this subset
4. Each equivalence class in this subset still has size $k$

For condition 4, we need to show that for any element $x \in \{y \in s \mid \neg R(a,y)\}$, its equivalence class within this subset has size $k$. This follows because if $R(x,z)$ then either $R(x,a)$ or $\neg R(x,a)$. If $R(x,a)$ were true, then by symmetry $R(a,x)$ would be true, contradicting the definition of our subset. So $\neg R(x,a)$ must hold. By transitivity, for any $y$ with $R(x,y)$, we must have $\neg R(a,y)$ (otherwise, if $R(a,y)$ and $R(y,x)$ were true, then $R(a,x)$ would follow). Thus, the equivalence class of $x$ in our subset equals its equivalence class in $s$.

Therefore, by the induction hypothesis, $k$ divides $|\{y \in s \mid \neg R(a,y)\}|$.

Now, $|s| = |\{y \in s \mid R(a,y)\}| + |\{y \in s \mid \neg R(a,y)\}| = k + |\{y \in s \mid \neg R(a,y)\}|$. 

Since $k$ divides itself (by `DIVIDES_REFL`) and $k$ divides $|\{y \in s \mid \neg R(a,y)\}|$ (by the induction hypothesis), $k$ divides their sum, which is $|s|$.

### Mathematical insight
This theorem establishes a fundamental property of equivalence relations on finite sets: when all equivalence classes have the same size, that size must divide the cardinality of the entire set. 

This is a natural extension of Lagrange's theorem in group theory, which states that the order of a subgroup divides the order of the group. In this more general setting, we're working with equivalence classes rather than cosets of a subgroup, but the underlying combinatorial principle is the same.

The result is useful in various counting arguments in combinatorics, group theory, and other areas of discrete mathematics where partitioning sets into equal-sized classes is relevant.

### Dependencies
#### Theorems:
- `DIVIDES_0`: For all $x$, $x$ divides 0
- `DIVIDES_REFL`: For all $x$, $x$ divides $x$

### Porting notes
When porting this theorem, consider:
1. Many proof assistants have built-in notions of equivalence relations, which might simplify the statement.
2. The well-founded induction on the cardinality of a set is a common pattern, but the specific implementation may vary between systems.
3. The majority of the proof involves set-theoretic reasoning about equivalence classes, which might need different tactics in other systems.

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
Let $R$ be a relation on a finite set $s$ of type $A$ such that:
- $R$ is reflexive on $s$: $\forall x \in s, R(x, x)$
- $R$ is symmetric on $s$: $\forall x, y \in s, R(x, y) \implies R(y, x)$
- $R$ is transitive on $s$: $\forall x, y, z \in s, R(x, y) \land R(y, z) \implies R(x, z)$
- For each $x \in s$, the cardinality of the set $\{y \mid y \in s \land R(x, y)\}$ equals $k$

Then $k$ divides the cardinality of $s$.

### Informal proof
The proof uses the theorem `EQUIVALENCE_UNIFORM_PARTITION`, which states that if an equivalence relation on a set has equivalence classes of uniform size $k$, then $k$ divides the cardinality of the set.

We need to create an equivalence relation from $R$ that satisfies the conditions of `EQUIVALENCE_UNIFORM_PARTITION`. 

- We define a new relation $R'$ by restricting $R$ to the set $s$: 
  $R'(x, y) \iff x \in s \land y \in s \land R(x, y)$
- The relation $R'$ is an equivalence relation by the given properties of $R$ on $s$
- For any $x \in s$, the equivalence class of $x$ under $R'$ has cardinality $k$, as given in the assumptions
- By applying `EQUIVALENCE_UNIFORM_PARTITION` to $R'$, we conclude that $k$ divides the cardinality of $s$

The proof is completed by using `ASM_MESON_TAC[]` to handle the logical details of showing that $R'$ satisfies all the required properties.

### Mathematical insight
This theorem addresses equivalence relations that are restricted to a subset. It shows that the uniform size property of equivalence classes forces a divisibility relationship with the set size.

The key insight is that an equivalence relation with uniform-sized classes partitions a set into equal-sized blocks, and therefore the size of each class must divide the total set size.

This is a restricted version of `EQUIVALENCE_UNIFORM_PARTITION` where we explicitly handle a relation that might not be a proper equivalence relation on the whole type, but only behaves as an equivalence relation when restricted to the set $s$.

### Dependencies
- `EQUIVALENCE_UNIFORM_PARTITION`: The main theorem used here, which states that if an equivalence relation has classes of uniform size $k$, then $k$ divides the cardinality of the set.

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
For any set $s$ and relation $r$, if:
1. $s$ is finite,
2. $r$ is irreflexive on $s$ (i.e., $\forall x \in s, \neg r(x,x)$),
3. $r$ is symmetric on $s$ (i.e., $\forall x,y \in s, r(x,y) \Rightarrow r(y,x)$), and
4. Every element in $s$ has a unique partner related by $r$ (i.e., $\forall x \in s, \exists! y \in s$ such that $r(x,y)$),

then the cardinality of $s$ is even (i.e., $\text{CARD}(s)$ is even).

### Informal proof
We proceed by well-founded induction on the cardinality of set $s$.

* **Base case**: If $s = \emptyset$, then $\text{CARD}(s) = 0$, which is even.

* **Inductive case**: Assume $s \neq \emptyset$. Then there exists some element $a \in s$.
  - By assumption 4, $a$ has a unique partner $b \in s$ such that $r(a,b)$.
  - Consider the set $s' = s \setminus \{a,b\}$.
  - We claim that $s'$ satisfies all the conditions of our theorem:
    - $s'$ is finite (as it's a subset of the finite set $s$)
    - $s'$ has strictly smaller cardinality than $s$
    - The relation $r$ remains irreflexive and symmetric when restricted to $s'$
    - Every element in $s'$ still has a unique partner in $s'$ related by $r$
      (This is because if $x \in s'$ had its partner $y$ among $\{a,b\}$, then 
      by symmetry of $r$, either $a$ or $b$ would have two distinct partners, 
      contradicting uniqueness)
  
  - By the induction hypothesis, $\text{CARD}(s')$ is even.
  - Since $s = \{a\} \cup \{b\} \cup s'$ and $a \neq b$, we have $\text{CARD}(s) = 2 + \text{CARD}(s')$.
  - Therefore, $\text{CARD}(s)$ is even.

### Mathematical insight
This theorem formalizes the intuition that if every element in a set has a unique partner under a symmetric relation, then the elements must naturally pair up, resulting in an even number of elements. The relation $r$ effectively creates a perfect matching on the set.

This is a fundamental result in combinatorics and graph theory. The relation $r$ can be viewed as defining the edges of an undirected graph where each vertex has exactly one incident edge (a perfect matching). Such a graph must have an even number of vertices.

The result is important for many applications in mathematics where pairing of elements occurs, such as in the theory of permutations, matchings in graphs, and certain algebraic structures.

### Dependencies
This theorem relies on basic set theory properties and cardinality theorems in HOL Light, particularly involving finite sets and their cardinality.

### Porting notes
When porting this theorem:
- Ensure the target system has appropriate notions of finite sets, cardinality, and unique existence.
- The proof uses well-founded induction on the cardinality, which may need to be handled differently in systems with different induction principles.
- The set operations (particularly deletion of elements) should be carefully translated according to the target system's conventions.
- Some systems might have existing libraries about matchings in graphs that could simplify this proof.

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
Let $r$ be a binary relation and $k$ be a positive integer. A sequence $x$ is a cycle of length $k$ under the relation $r$ if and only if:
- For all indices $i$, $r(x(i), x(i+1))$ holds (i.e., consecutive elements in the sequence are related by $r$)
- For all indices $i$, $x(i+k) = x(i)$ (i.e., the sequence repeats with period $k$)

Formally, $\text{cycle}(r, k, x) \iff (\forall i.\ r(x(i), x(i+1))) \land (\forall i.\ x(i+k) = x(i))$

### Informal proof
This is a definition, so no proof is required.

### Mathematical insight
The `cycle` definition formalizes the concept of a cyclic sequence with respect to a relation. This is a fundamental concept in graph theory, where a cycle is a path that starts and ends at the same vertex.

Key aspects of this definition:
- It represents a cycle as a function $x$ from indices to elements
- The periodicity condition $x(i+k) = x(i)$ ensures the cycle has length $k$
- The relation $r$ connects consecutive elements in the cycle

This definition is useful for formalizing properties of graphs, especially when studying cycles in directed or undirected graphs, or when analyzing periodic behaviors in various mathematical structures.

### Dependencies
- None (this is a basic definition)

### Porting notes
When porting this definition:
- Ensure the target system can handle functions representing sequences
- Pay attention to how the target system represents unbounded indices (the definition quantifies over all indices $i$)
- Consider whether the target system might need additional well-formedness conditions (e.g., ensuring $k > 0$)

---

## path

### path
- `path`

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let path = new_definition
 `path r k x <=> (!i. i < k ==> r (x i) (x(i + 1))) /\
                 (!i. k < i ==> x(i) = @x. T)`;;
```

### Informal statement
Given a relation $r$, a natural number $k$, and a function $x : \mathbb{N} \rightarrow \alpha$, the predicate $\text{path}(r, k, x)$ holds if and only if:
- For all $i < k$, the relation $r$ holds between consecutive elements $x(i)$ and $x(i+1)$
- For all $i > k$, the function $x(i)$ equals an arbitrary value (specifically, the value given by the Hilbert choice operator $\epsilon x. \top$)

### Informal proof
This is a definition, not a theorem, so there is no proof to explain.

### Mathematical insight
The `path` definition formalizes the concept of a finite path in a graph or relation. The function $x$ represents a sequence of elements, and the relation $r$ defines what makes consecutive elements connected. 

The key features of this definition are:
- It requires the relation $r$ to hold between each consecutive pair of elements up to index $k$.
- After index $k$, the function values are defined to be arbitrary but fixed (using Hilbert's choice operator).

This concept is useful for reasoning about paths in graphs, sequences with specific properties, or transition systems. The definition allows for finite paths while still having $x$ defined as a total function on natural numbers by giving arbitrary values past the end of the actual path.

### Dependencies
This definition doesn't explicitly depend on other theorems or definitions besides standard logical operators and Hilbert's choice operator.

### Porting notes
When porting this definition to other proof assistants:
- The use of Hilbert's choice operator (`@x. T`) to give arbitrary values past the end of the path may need to be handled differently in systems that don't support choice operators directly.
- Some systems might prefer to use an option type or a partial function instead of assigning arbitrary values after index $k$.
- Alternatively, you could define paths as finite sequences up to length $k$ rather than infinite sequences with arbitrary values after $k$.

---

## CYCLE_OFFSET

### CYCLE_OFFSET
- `CYCLE_OFFSET`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let CYCLE_OFFSET = prove
 (`!r k x:num->A. cycle r k x ==> !i m. x(m * k + i) = x(i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cycle] THEN STRIP_TAC THEN GEN_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  ASM_MESON_TAC[ADD_AC]);;
```

### Informal statement
For any relation $r$, natural number $k$, and function $x: \mathbb{N} \to A$, if $x$ forms a cycle of length $k$ under relation $r$ (i.e., $\text{cycle}~r~k~x$ holds), then for all natural numbers $i$ and $m$:
$$x(m \cdot k + i) = x(i)$$

This means that the values of $x$ repeat with period $k$.

### Informal proof
The proof proceeds as follows:

* Start by expanding the definition of `cycle` according to the rewrite tactic.
* The definition of `cycle` implies that $\forall n.~ r(x(n), x(n+k))$ holds.
* For any $i$, we need to show that $x(m \cdot k + i) = x(i)$ for all $m$.
* We use induction on $m$:
  * Base case ($m = 0$): $x(0 \cdot k + i) = x(i)$, which is trivially true.
  * Inductive step: Assume $x(m \cdot k + i) = x(i)$ for some $m$.
  * We need to show $x((m+1) \cdot k + i) = x(i)$.
  * Using arithmetic properties, $(m+1) \cdot k + i = m \cdot k + k + i$.
  * By associativity and commutativity of addition (represented by `ADD_AC`), 
    we have the desired result.
* The proof uses `ASM_MESON_TAC` with addition properties to complete the reasoning.

### Mathematical insight
This theorem establishes a fundamental property of cyclic sequences - that values repeat with the cycle length as the period. It shows that if a sequence cycles with length $k$, then the elements at positions that are congruent modulo $k$ are equal.

This result is important for any context dealing with periodic structures or functions, providing a formal characterization of how values propagate in a cycle. It's a canonical result that would be expected in any formalization of cyclic sequences or periodic behaviors.

### Dependencies
- **Definitions**: `cycle` 
- **Theorems**: `ADD_CLAUSES`, `MULT_CLAUSES`, `ADD_AC`

### Porting notes
When porting this theorem:
1. Ensure that the `cycle` definition is properly implemented first, as the theorem directly builds on it
2. The proof uses natural number arithmetic properties, so corresponding theorems about addition and multiplication will be needed
3. The automation level is moderate - a simpler proof using more explicit steps might be easier to port to systems with different automated reasoning capabilities

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
For any relation $r$, natural number $k$, and function $x: \mathbb{N} \rightarrow A$, if $x$ is a cycle of length $k$ with respect to relation $r$ (i.e., $\text{cycle}(r, k, x)$) and $k \neq 0$, then for all indices $i \in \mathbb{N}$, we have $x(i \bmod k) = x(i)$.

### Informal proof
The theorem is proved using `MESON_TAC` with the theorems `CYCLE_OFFSET` and `DIVISION`. The proof relies on these key facts:

- From `CYCLE_OFFSET`, we know that if $x$ is a cycle of length $k$ with respect to relation $r$, then for any offset $p$, $x(i+p) = x(i \bmod k + p \bmod k)$.
- From `DIVISION`, we have the division theorem which relates division, modulo, and remainders.

The proof shows that if $x$ is a cycle of length $k$, then $x(i) = x(i \bmod k)$ for all $i$. This follows because:

- For any $i$, we can write $i = qk + r$ where $0 \leq r < k$ (division theorem)
- Then $i \bmod k = r$
- By the cycle property (via `CYCLE_OFFSET`), $x(i) = x(qk + r) = x(r) = x(i \bmod k)$

### Mathematical insight
This theorem establishes that a cyclic sequence of length $k$ is completely determined by its first $k$ values, and any access to the sequence can be simplified by using the modulo operation. This is a fundamental property of cyclic structures and is widely used in combinatorial and algorithmic contexts.

The result provides a convenient way to index into a cyclic sequence without worrying about index bounds, as all indices are effectively "wrapped around" using modulo arithmetic to access the underlying $k$ values that define the cycle.

### Dependencies
- `CYCLE_OFFSET`: Theorem about accessing cycles with offsets
- `DIVISION`: Division theorem relating division, modulo, and remainders

### Porting notes
When porting this theorem to another system, ensure that:
- The `cycle` predicate is properly defined to express a cyclic sequence
- The modulo operation (`MOD`) is correctly implemented, especially for the case of non-zero moduli
- The automation employed by `MESON_TAC` may need to be replaced with more explicit reasoning steps in systems with different automated proof capabilities

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
If for all $x$ and $y$, $r(x, y)$ implies $s(x, y)$, then $\{x \mid \text{path}(r, k, x)\} \subseteq \{x \mid \text{path}(s, k, x)\}$.

This theorem states that the set of points reachable via paths in relation $r$ starting from $k$ is a subset of the set of points reachable via paths in relation $s$ starting from $k$, provided that relation $r$ is a subset of relation $s$.

### Informal proof
The proof proceeds by:

- First, we rewrite the theorem statement using the definitions of `path`, `IN_ELIM_THM`, and `SUBSET`.
- After rewriting, we have a statement about set inclusion where one set contains elements that satisfy the path relation for $r$, and the other contains elements that satisfy the path relation for $s$.
- Then we use the MESON automated prover to complete the proof.

The key insight is that if $r \subseteq s$ (i.e., $r(x,y)$ implies $s(x,y)$ for all $x,y$), then any path that exists using relation $r$ must also exist using relation $s$. This follows directly from the inductive definition of paths, where a path using relation $r$ either means:
- $x = k$ (the base case)
- Or, there exists a $y$ such that $r(y,x)$ and there is a path from $k$ to $y$ using $r$

In both cases, if we replace $r$ with a superset relation $s$, the path still exists.

### Mathematical insight
This theorem establishes a monotonicity property for paths with respect to the underlying relations. It formalizes the intuitive notion that expanding a relation (i.e., adding more edges to a graph) can only expand, never reduce, the set of points reachable from a given starting point.

This property is fundamental in graph theory and reachability analysis. It's particularly useful when analyzing approximations or abstractions of systems, where a coarser relation might be used to over-approximate reachability.

### Dependencies
- Definition: `path` - Defines when a path exists in a relation from a starting point to an endpoint
- Theorem: `IN_ELIM_THM` - Relates set membership to the defining predicate
- Theorem: `SUBSET` - Definition of subset relation

### Porting notes
When porting this theorem:
- Ensure that the `path` relation is defined inductively in your target system
- The proof is mostly automated in HOL Light, but may require more explicit induction in systems with weaker automation
- The core argument relies on a straightforward substitution of relations in the path definition, which should work similarly in most proof assistants

---

## HAS_SIZE_PATHS

### HAS_SIZE_PATHS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
For any natural numbers $N$, $m$, $r$, and $k$, if the universal set $A$ has size $N$ and for each element $x \in A$, the set $\{y \mid r(x,y)\}$ has size $m$, then the set of all paths of length $k$ in the relation $r$, denoted by $\{x: \mathbb{N} \to A \mid \text{path}(r, k, x)\}$, has size $N \cdot m^k$.

Here, $\text{path}(r, k, x)$ means that $x$ is a function from natural numbers to $A$ that forms a path of length $k$ in the relation $r$, where $x(i+1)$ is related to $x(i)$ by $r$ for all $i < k$.

### Informal proof

The proof proceeds by induction on $k$:

* **Base case** ($k = 0$):
  - For $k = 0$, a path of length 0 consists of just a single element from $A$.
  - We show that $\{x: \mathbb{N} \to A \mid \text{path}(r, 0, x)\}$ is equal to the image of $A$ under the function $\lambda a. \lambda i. \text{ if } i = 0 \text{ then } a \text{ else some arbitrary value}$.
  - This function is injective on $A$, so the size of this set is $N = N \cdot m^0$.

* **Inductive step** ($k \to k+1$):
  - We prove that the set of paths of length $k+1$ is equal to the image of the set of pairs $(x,a)$, where $x$ is a path of length $k$ and $a$ is related to the last element of $x$ by $r$.
  - Specifically, we show:
    $$\{x: \mathbb{N} \to A \mid \text{path}(r, k+1, x)\} = \text{Image}(\lambda(x,a). \lambda i. \text{ if } i = k+1 \text{ then } a \text{ else } x(i), \{(x,a) \mid x \in \{x \mid \text{path}(r,k,x)\} \land a \in \{u \mid r(x(k),u)\}\})$$
  - The mapping function is injective, so we can use the theorem about the size of images under injective functions.
  - By the induction hypothesis, the set of paths of length $k$ has size $N \cdot m^k$.
  - For each such path, there are $m$ possible elements that can extend it (since each $\{y \mid r(x(k),y)\}$ has size $m$).
  - Therefore, the number of paths of length $k+1$ is $(N \cdot m^k) \cdot m = N \cdot m^{k+1}$.

### Mathematical insight
This theorem provides a precise count of the number of paths of a given length in a graph with a constant out-degree. It shows that if we have a graph with $N$ nodes, each with exactly $m$ outgoing edges, then the number of distinct paths of length $k$ is $N \cdot m^k$. 

The intuition is clear: we have $N$ choices for the starting point, and at each of the $k$ steps along the path, we have $m$ choices for the next node, giving a total of $N \cdot m^k$ possible paths.

This result is fundamental in graph theory, combinatorics, and probability theory (particularly for Markov chains), as it helps analyze the growth of reachability sets in directed graphs with regular structure.

### Dependencies
- `HAS_SIZE_IMAGE_INJ` - Theorem about the size of the image of a set under an injective function
- `HAS_SIZE_PRODUCT_DEPENDENT` - Theorem about the size of a dependent product of sets
- Various arithmetic and logical operations and properties

### Porting notes
When porting to other systems:
- Ensure that the `path` relation is properly defined (where a path of length $k$ is a sequence where consecutive elements are related by $r$ up to index $k$)
- Pay attention to the handling of function updates in other systems, which may differ from HOL Light's approach
- The extensive use of `MESON_TAC` and other automated tactics may require different automation strategies in other provers

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
For any relation $r$ and natural number $k$, if the type $A$ is finite, then the set of all paths of length $k$ in relation $r$ is also finite:

$$\forall r~k.~\text{FINITE}(:A) \Rightarrow \text{FINITE}(\{x : \mathbb{N} \to A \mid \text{path}~r~k~x\})$$

where $\text{path}~r~k~x$ means that $x$ is a path of length $k$ following relation $r$.

### Informal proof
The proof proceeds as follows:

* We apply `FINITE_SUBSET` to show that if a subset of a finite set is finite, then the subset is also finite.
* The key insight is to consider the set of all possible sequences of length $k$ from $A$, regardless of whether they follow relation $r$. This is represented by $\{x : \mathbb{N} \to A \mid \text{path}~(\lambda a~b.~\text{T})~k~x\}$, where the relation $(\lambda a~b.~\text{T})$ always returns true, thus accepting all possible pairs.
* We show that the set of paths following relation $r$ is a subset of all possible sequences using `PATHS_MONO`.
* We then use `HAS_SIZE_PATHS` with the cardinality of type $A$ to establish that the set of all possible sequences is finite.
* The application of `HAS_SIZE` and set simplification completes the proof.

### Mathematical insight
This theorem establishes that if we have a finite type $A$, then the set of all paths of length $k$ following any relation $r$ is also finite. This is an important result for reasoning about graph traversal, automata theory, and other areas where finite path enumeration is needed.

The key insight is to recognize that the set of paths following a specific relation is a subset of all possible sequences of length $k$ from $A$, which is finite when $A$ is finite.

### Dependencies
- `FINITE_SUBSET` - Theorem stating that a subset of a finite set is finite
- `PATHS_MONO` - Theorem about monotonicity of paths with respect to relations
- `HAS_SIZE_PATHS` - Theorem relating the size of the set of paths to the cardinality of the type
- `HAS_SIZE` - Definition relating finiteness to cardinality
- `SET_RULE` - Tactic for set-theoretic simplifications

### Porting notes
When porting this theorem, ensure that your target system has:
1. A formalized notion of finiteness for sets
2. Support for functions from natural numbers to a type (representing sequences)
3. A definition of paths following a relation

The proof relies on establishing that paths following a specific relation form a subset of all possible sequences, which is a general approach that should translate well to other formal systems.

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
For any relation $r$ on a type $A$ and any positive natural number $k$, if $A$ is finite, then the set of all $k$-cycles in $r$ has size equal to the cardinality of the set of all $k$-paths in $r$ where the end point equals the start point.

Formally: For all relations $r$ and natural numbers $k$, if $A$ is a finite type and $k \neq 0$, then:
$$\{x : \mathbb{N} \to A \mid \text{cycle}(r, k, x)\} \text{ HAS_SIZE } |\{x : \mathbb{N} \to A \mid \text{path}(r, k, x) \land x(k) = x(0)\}|$$

where $\text{cycle}(r, k, x)$ means $x$ describes a $k$-length cycle in relation $r$, and $\text{path}(r, k, x)$ means $x$ describes a $k$-length path in relation $r$.

### Informal proof
The proof establishes that there's a bijection between cycles and paths whose endpoints coincide:

1. First, we show that the set of all cycles can be expressed as an image:
   $$\{x : \mathbb{N} \to A \mid \text{cycle}(r, k, x)\} = \text{IMAGE}(\lambda x\,i. x(i \bmod k))(\{x \mid \text{path}(r, k, x) \land x(k) = x(0)\})$$

   This is proven by showing the two sets have the same elements:
   - For the forward direction: Given a cycle $x$, we can create a path $y$ that matches $x$ on the interval $[0,k]$ and arbitrary elsewhere.
   - For the reverse direction: Given a path $y$ where $y(k) = y(0)$, we show that $\lambda i. y(i \bmod k)$ is a cycle.

2. To apply `HAS_SIZE_IMAGE_INJ`, we need to show:
   - The function $\lambda x\,i. x(i \bmod k)$ is injective on the set $\{x \mid \text{path}(r, k, x) \land x(k) = x(0)\}$
   - The set $\{x \mid \text{path}(r, k, x) \land x(k) = x(0)\}$ is finite

3. For finiteness, we use the fact that $\{x \mid \text{path}(r, k, x)\}$ is finite (by `FINITE_PATHS`) when $A$ is finite.

4. For injectivity, we show that if two paths map to the same function under our map, they must be equal. This follows from the definition of the map and the properties of modular arithmetic.

### Mathematical insight
This theorem establishes a fundamental relationship between cycles and paths in a finite relation. While cycles are infinite objects (functions defined on all natural numbers), this theorem shows that we can count them by counting certain finite paths.

The key insight is that a cycle is completely determined by its behavior over a single period. By using the modulo operation, we can "wrap" a finite path of length $k$ into an infinite cycle, creating a bijection between $k$-cycles and $k$-paths that loop back to their starting point.

This result is important in graph theory and the analysis of state transition systems, as it allows us to count cycles by counting certain paths, which are often easier to enumerate.

### Dependencies
- `cycle`: Definition of a cycle in a relation
- `path`: Definition of a path in a relation
- `FINITE_PATHS`: Theorem stating that the set of paths of length k in a finite type is finite
- `HAS_SIZE_IMAGE_INJ`: Theorem about the size of the image of an injective function
- `MOD_LT`: Properties of modular arithmetic
- `MOD_EQ`: Properties of modular arithmetic
- `MOD_UNIQ`: Properties of modular arithmetic
- `DIVISION`: Properties of division with remainder

### Porting notes
When porting this theorem:
1. Ensure that the definitions of `cycle` and `path` are properly translated, as they are fundamental to this theorem.
2. The proof relies heavily on properties of modular arithmetic - make sure these are available in the target system.
3. The handling of functions like `λx i. x(i MOD k)` might require careful attention in systems with different function representation.
4. The theorem uses `HAS_SIZE` which represents that a set has exactly a certain cardinality - ensure this concept is properly translated to the target system.

---

## FINITE_CYCLES

### FINITE_CYCLES
- FINITE_CYCLES

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FINITE_CYCLES = prove
 (`!r k. FINITE(:A) /\ ~(k = 0) ==> FINITE {x:num->A | cycle r k x}`,
  MESON_TAC[HAS_SIZE_CYCLES; HAS_SIZE]);;
```

### Informal statement
The theorem states:

For all relations $r$ and natural numbers $k$, if the type $A$ is finite and $k \neq 0$, then the set of all $k$-cycles $\{x : \mathbb{N} \to A \mid \text{cycle}~r~k~x\}$ is finite.

Here, $\text{cycle}~r~k~x$ means that $x$ is a function that represents a cycle of length $k$ in relation $r$.

### Informal proof
The proof uses the `MESON_TAC` tactic with two theorems:

* `HAS_SIZE_CYCLES`: This theorem likely states that for a finite type $A$ and non-zero $k$, the set of $k$-cycles in relation $r$ has a specific size.
* `HAS_SIZE`: This theorem likely relates the concept of a set having a specific size to the set being finite.

The automated theorem prover combines these results to establish that if $A$ is finite and $k$ is non-zero, then the set of all $k$-cycles in relation $r$ must be finite.

### Mathematical insight
This theorem establishes a fundamental finiteness property: when working with finite sets, the collection of cycles of any non-zero length must also be finite. This result is important for analyzing cyclic structures in finite domains.

The requirement that $k \neq 0$ is necessary because a "0-cycle" would be an ambiguous concept, and including it might lead to an infinite set of such cycles.

This result allows us to reason about cycles in finite structures without worrying about dealing with infinite collections of cycles, which is essential for algorithms that enumerate or count cycles in finite graphs or relations.

### Dependencies
- `HAS_SIZE_CYCLES`: Likely relates to the size of the set of cycles
- `HAS_SIZE`: Relates having a specific size to finiteness

### Porting notes
When porting this theorem to other systems:

1. Ensure that the target system has similar notions of cycles in relations.
2. The concept of `HAS_SIZE` might be represented differently in other systems - some might directly use cardinality functions instead.
3. The automated reasoning in `MESON_TAC` might need to be replaced with more explicit proof steps in systems with different automation capabilities.

---

## CARD_PATHCYCLES_STEP

### CARD_PATHCYCLES_STEP
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
Let $N$, $m$, $r$, and $k$ be variables such that:
- Set $A$ has size $N$
- $k \neq 0$ and $m \neq 0$
- For every $x \in A$, the set $\{y \mid r(x,y)\}$ has size $m$
- The relation $r$ is symmetric: for all $x,y$, if $r(x,y)$ then $r(y,x)$
- For any distinct $x,y$, there exists a unique $z$ such that $r(x,z)$ and $r(z,y)$

Then the set $\{x \mid \text{path}(r, k+2, x) \land x(k+2) = x(0)\}$ has size:
$m \cdot |\{x \mid \text{path}(r, k, x) \land x(k) = x(0)\}| + |\{x \mid \text{path}(r, k, x) \land x(k) \neq x(0)\}|$

where $\text{path}(r, n, x)$ means $x$ is a path of length $n$ with respect to relation $r$.

### Informal proof
This theorem describes the relationship between paths of length $k+2$ that form cycles (ending at the starting point) and paths of length $k$.

The proof proceeds as follows:

- We first split the set of paths of length $k+2$ that form cycles into two disjoint sets:
  * Paths where $x(k) = x(0)$ and $x(k+2) = x(0)$
  * Paths where $x(k) \neq x(0)$ and $x(k+2) = x(0)$

- For the first set (where $x(k) = x(0)$), we establish a bijection with pairs $(x,a)$ where:
  * $x$ is a path of length $k$ forming a cycle ($x(k) = x(0)$)
  * $a$ is an element adjacent to $x(k)$

  This bijection maps $(x,a)$ to a path $z$ defined by:
  $z(i) = \begin{cases}
  a & \text{if } i = k+1 \\
  x(0) & \text{if } i = k+2 \\
  x(i) & \text{otherwise}
  \end{cases}$
  
  The size of this set is therefore $m \cdot |\{x \mid \text{path}(r, k, x) \land x(k) = x(0)\}|$.

- For the second set (where $x(k) \neq x(0)$), we establish a bijection with all paths $x$ of length $k$ that don't form cycles.

  This bijection maps each path $x$ to a path $z$ defined by:
  $z(i) = \begin{cases}
  z & \text{if } i = k+1, \text{where $z$ is the unique element such that $r(x(k),z)$ and $r(z,x(0))$} \\
  x(0) & \text{if } i = k+2 \\
  x(i) & \text{otherwise}
  \end{cases}$
  
  The uniqueness of this $z$ is guaranteed by the condition that for distinct elements, there exists a unique intermediary element.

- Since these two sets are disjoint and their union is the entire set of $(k+2)$-length cycles, the total size is the sum of their individual sizes.

### Mathematical insight
This theorem provides a recursive relationship for counting cycles in a graph with specific properties. The relation $r$ represents adjacency in a graph, and the theorem relates cycles of length $k+2$ to cycles and paths of length $k$.

The key insight is that cycles of length $k+2$ can be broken down into two types:
1. Those that "visit" the starting point at step $k$, then make a detour for two more steps before returning
2. Those that don't visit the starting point at step $k$, but need exactly two more steps to return

This decomposition allows us to recursively count cycles of larger lengths based on information about shorter cycles. The relationship is particularly useful in combinatorial enumeration problems related to graph theory.

### Dependencies
No specific dependencies were listed in the provided information.

### Porting notes
When porting this theorem, pay attention to:
- The representation of paths as functions from natural numbers to the vertex set
- The definition of a path with respect to a relation $r$
- How symmetric relations and uniqueness properties are defined in the target system

The concept of a path being a function from indices to vertices might be different in other proof assistants, which could use a list-based representation instead.

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
Let $x$ and $y$ be sequences (functions from integers to some type). We say that $x$ is **shiftable** to $y$, denoted by $\text{shiftable}(x, y)$, if and only if there exists an integer $k$ such that for all integers $i$, $x(i) = y(i + k)$.

### Informal proof
This is a definition, so it does not have a proof.

### Mathematical insight
The `shiftable` relation captures the notion that one sequence is a shifted version of another. This concept is often important in areas such as:

- Sequence analysis and pattern matching
- Periodic functions and signals
- Cyclic structures

The definition essentially states that two sequences are considered equivalent up to a constant shift. This shift-invariant property allows us to identify sequences that have the same pattern but might start at different positions.

The definition is parametric in the type of sequence elements, making it applicable to sequences over any HOL Light type.

### Dependencies
None explicitly mentioned in the provided metadata.

### Porting notes
When porting this definition:
- Ensure that your target system supports functions over integers as the proper representation of sequences
- The quantification pattern with an existential followed by a universal quantifier is standard and should translate directly to most systems
- Consider whether your target system has a standard library notion of sequence shifts that could be used instead

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
For all real numbers $x$, $x$ is shiftable to $x$.

Where "shiftable" refers to the property that a number can be shifted to another by adding a natural number. Formally, $\text{shiftable}(x, y)$ means $\exists n \in \mathbb{N}, y = x + n$.

### Informal proof
The proof proceeds as follows:

1. First, we rewrite using the definition of `shiftable`.
2. Then, we use the meson theorem prover with `ADD_CLAUSES` (a collection of basic addition facts).

To prove $\text{shiftable}(x, x)$, we need to show that $\exists n \in \mathbb{N}, x = x + n$. 

This is satisfied by taking $n = 0$, since $x = x + 0$ for any real number $x$ (which is part of the addition identities contained in `ADD_CLAUSES`).

### Mathematical insight
This theorem establishes the reflexivity property of the "shiftable" relation. It essentially states that any number can be considered as shifted from itself by adding 0.

This property is a fundamental characteristic of the "shiftable" relation and forms part of its basic properties. While seemingly trivial, it's an important base case for reasoning about number shifts in various contexts.

### Dependencies
- **Definitions**:
  - `shiftable` - Definition that states when one number is shiftable to another
- **Theorems**:
  - `ADD_CLAUSES` - Collection of basic addition properties, including the property that $x + 0 = x$

### Porting notes
When porting this theorem:
- Ensure that the definition of "shiftable" is correctly implemented in the target system
- The proof should be straightforward in most proof assistants with basic arithmetic support
- This is a simple case of existential instantiation with the value 0

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
For all real numbers $x$, $y$, and $z$, if $x$ is shiftable to $y$ and $y$ is shiftable to $z$, then $x$ is shiftable to $z$. Formally:

$$\forall x, y, z. \text{shiftable}(x, y) \land \text{shiftable}(y, z) \Rightarrow \text{shiftable}(x, z)$$

Where $\text{shiftable}(a, b)$ means there exists some real number $d$ such that $a + d = b$.

### Informal proof
The proof follows by:

- First, we rewrite the goal using the definition of `shiftable`, which expands to: 
  $$\forall x, y, z. (\exists d_1. x + d_1 = y) \land (\exists d_2. y + d_2 = z) \Rightarrow (\exists d_3. x + d_3 = z)$$

- Then, using the `MESON_TAC` tactic with the associativity of addition (`ADD_ASSOC`), the proof is completed automatically.

- The key insight is that if $x + d_1 = y$ and $y + d_2 = z$, then $x + (d_1 + d_2) = z$ by substitution and associativity of addition.

### Mathematical insight
This theorem establishes the transitivity property of the "shiftable" relation. If we can shift $x$ to get $y$, and shift $y$ to get $z$, then we can shift $x$ directly to get $z$. The shift required is simply the sum of the individual shifts.

This is a fundamental property that helps establish "shiftable" as an equivalence relation (assuming reflexivity and symmetry are also proven separately). In mathematical terms, it's showing that translation in a space forms a transitive relation.

The proof leverages the associativity of addition, which is essential for combining the two shifts into a single shift.

### Dependencies
- Definitions:
  - `shiftable`: Definition that states $x$ is shiftable to $y$ if there exists a value $d$ such that $x + d = y$

- Theorems:
  - `ADD_ASSOC`: The associativity of addition, $(x + y) + z = x + (y + z)$

### Porting notes
When porting this theorem:
- Ensure the definition of "shiftable" is properly established first
- The proof is quite straightforward and should translate easily to other proof assistants
- The automation level in other systems might require more explicit steps than just invoking MESON_TAC

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
For all functions $x$, $y$, and natural numbers $p$ and $r$, if $x$ is cyclic with period $p$ and relation $r$, and $y$ is also cyclic with the same period $p$ and relation $r$, and $p \neq 0$, then:

$x$ is shiftable to $y$ if and only if there exists a natural number $k$ such that $k < p$ and for all indices $i$, $x(i) = y(i + k)$.

### Informal proof
The proof establishes the equivalence between two notions of being "shiftable":

* First, we use the definition of `shiftable` as the starting point for the equivalence.
* For the direction ($\Rightarrow$):
  * Assume that $x$ is shiftable to $y$, which means there exists some shift $k$ such that for all $i$, $x(i) = y(i + k)$.
  * We need to find a $k' < p$ that satisfies the same property.
  * Using the division theorem (`DIVISION`), we know that for any $k$ there exist $q$ and $r$ such that $k = q \cdot p + r$ where $r < p$.
  * We claim that $k' = k \bmod p = r$ is the required value.
  * When we substitute $k = q \cdot p + r$ into the equality $x(i) = y(i + k)$, we get:
    $x(i) = y(i + q \cdot p + r) = y(i + r)$
  * The last equality follows from the fact that $y$ is cyclic with period $p$, so $y(i + q \cdot p + r) = y(i + r)$ (using `CYCLE_OFFSET`).
  * Therefore, $k' = k \bmod p$ satisfies both $k' < p$ and $\forall i. x(i) = y(i + k')$

* For the direction ($\Leftarrow$):
  * This direction is trivial, as having a $k < p$ with the property $\forall i. x(i) = y(i + k)$ directly satisfies the definition of `shiftable`.
  * This is handled by the `MESON_TAC[]` step in the HOL Light proof.

### Mathematical insight
This theorem characterizes when two cyclic functions are related by a shift. It shows that if two functions are cyclic with the same period, then checking if one is a shifted version of the other only requires checking shifts within one period (i.e., shifts less than $p$).

This is intuitive since any shift can be decomposed into a multiple of the period plus a remainder, and shifting by a multiple of the period doesn't change the values of a cyclic function.

The result simplifies checking for "shiftability" by restricting the search space of possible shifts from infinitely many to just finitely many (less than $p$).

### Dependencies
- Theorems:
  - `DIVISION`: Division theorem stating that any natural number can be written as a multiple of another plus a remainder
  - `CYCLE_OFFSET`: Property about shifting cyclic functions
  - `ADD_AC`: Associativity and commutativity of addition
- Definitions:
  - `shiftable`: Definition of when one function is a shift of another
  - `cycle`: Definition of cyclicity for a function with respect to a period and relation

### Porting notes
When porting this theorem:
- Ensure that the definitions of `shiftable` and `cycle` are consistently implemented
- The proof relies on the modular arithmetic properties of cyclic functions, which should be available in most proof assistants
- The use of `MESON_TAC[]` suggests automated reasoning is effective for part of this proof, but explicit decomposition of the statements might be needed in systems with less powerful automation

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
The theorem states that: 

For all $x$, $y$, $p$, and $r$, if $r$ forms a cycle of length $p$ containing both $x$ and $y$ (i.e., $\text{cycle}(r,p,x)$ and $\text{cycle}(r,p,y)$), the cycle length $p$ is non-zero ($p \neq 0$), and $x$ is shiftable to $y$ (i.e., $\text{shiftable}(x,y)$), then $y$ is also shiftable to $x$ (i.e., $\text{shiftable}(y,x)$).

In other words, the "shiftable" relation is symmetric within a non-trivial cycle.

### Informal proof
The proof proceeds as follows:

- We start with the assumptions that $\text{cycle}(r,p,x)$, $\text{cycle}(r,p,y)$, $p \neq 0$, and $\text{shiftable}(x,y)$.

- By the theorem `SHIFTABLE_LOCAL`, the property $\text{shiftable}(x,y)$ means there exists some $k$ such that $k < p$ and $y = r^{k}(x)$, where $r^{k}$ denotes $k$ applications of $r$.

- To show that $\text{shiftable}(y,x)$, we need to find a number of steps that takes $y$ back to $x$.

- We choose $p-k$ as this number of steps. Since $k < p$ (from the earlier step), we have $p-k > 0$.

- Using arithmetic, we can show that $(i + (p-k)) + k = i + p$ for any $i$. In the context of applying the relation $r$ repeatedly, this means that going forward $p-k$ steps from $y$ (which is already $k$ steps ahead of $x$) brings us to the same position as going $p$ steps from $x$.

- Since $r$ forms a cycle of length $p$ containing $x$, going $p$ steps from $x$ brings us back to $x$. Therefore, going $p-k$ steps from $y$ also brings us to $x$.

- This establishes that $\text{shiftable}(y,x)$.

### Mathematical insight
This theorem establishes the symmetry of the "shiftable" relation within a cycle. Intuitively, if we can reach $y$ from $x$ by following the relation $r$ repeatedly within a cycle, then we can also reach $x$ from $y$ by continuing to follow $r$ until we complete the cycle.

The proof cleverly uses the modular arithmetic nature of cycles: if $y$ is $k$ steps ahead of $x$ in a cycle of length $p$, then $x$ is $(p-k)$ steps ahead of $y$ in the same cycle.

This symmetry property is fundamental when working with cyclic structures and is particularly useful in reasoning about permutations or cyclic groups.

### Dependencies
- Theorems:
  - `SHIFTABLE_LOCAL`: Relates the shiftable relation to explicit cycle positions
  - `ARITH_RULE`: Used for arithmetic reasoning
- Definitions:
  - `cycle`: Defines when a relation forms a cycle of a given length containing an element
  - `shiftable`: Defines when one element can be shifted to another within a cycle

### Porting notes
When porting this theorem:
- Ensure the definitions of `cycle` and `shiftable` are correctly implemented first
- The proof relies on modular arithmetic properties of cycles, which should be made explicit in other systems
- The arithmetic reasoning (`ARITH_RULE`) might need to be expanded or replaced with equivalent tactics in the target system

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
For any relation $r$ on a finite type $A$, any prime number $p$, and any function $x: \mathbb{N} \to A$, if $r$ is irreflexive (i.e., $\forall x. \lnot(r \, x \, x)$), then $p$ divides the cardinality of the set $\{x: \mathbb{N} \to A \mid \text{cycle} \, r \, p \, x\}$.

### Informal proof
We prove that when $p$ is prime, $p$ divides the cardinality of the set of functions that form $p$-cycles under relation $r$.

- First, we handle the case where $p = 0$, which is trivial since 0 is not prime (by `PRIME_0`).

- We then apply `EQUIVALENCE_UNIFORM_PARTITION_RESTRICT` with "shiftable" as our equivalence relation. This theorem states that if we have a finite set partitioned by an equivalence relation, and each partition has the same size, then the size of each partition divides the size of the set.

- We prove that "shiftable" is an equivalence relation:
  * Reflexivity: `SHIFTABLE_REFL`
  * Symmetry: `SHIFTABLE_SYM`
  * Transitivity: `SHIFTABLE_TRANS`

- For any function $x$ in our set, we show that its equivalence class under "shiftable" has size $p$.
  * We establish that the equivalence class equals $\{\lambda i. x(i + k) \mid k < p\}$ (all cyclic shifts of $x$ by $k < p$).
  * We prove this set has size $p$ by showing the mapping $k \mapsto \lambda i. x(i + k)$ is injective on $\{k \mid k < p\}$.

- For injectivity, we use "without loss of generality" (`WLOG_LE`) to consider $k \leq l < p$. 
  * If $\lambda i. x(i + k) = \lambda i. x(i + l)$ then $x(i) = x(0)$ for all $i$.
  * This would make $x$ constant, contradicting that it forms a $p$-cycle.
  * The key step uses `LOOP_COPRIME` with $l + (p - k)$, which is coprime to $p$ because $p$ is prime (by `PRIME_COPRIME_LT`).

Therefore, each equivalence class has size exactly $p$, so $p$ divides the cardinality of the entire set.

### Mathematical insight
This lemma demonstrates a fundamental group-theoretic property of cycles under prime-length permutations. It shows that when working with $p$-cycles (where $p$ is prime), the set of all cycles has a cardinality divisible by $p$. This is analogous to Fermat's Little Theorem or the orbit-stabilizer theorem in group theory.

The key insight is that for each cycle, there are exactly $p$ ways to represent it by starting at different points in the cycle. These $p$ representations form equivalence classes under the "shiftable" relation, which partitions the set of all functions forming $p$-cycles.

This result is important for analyzing the structure of permutation groups and has applications in computational group theory, combinatorial enumeration, and cycle decompositions.

### Dependencies
#### Theorems
- `PRIME_0`: Proves that 0 is not a prime number
- `PRIME_COPRIME_LT`: For any prime $p$ and integer $x$ where $0 < x < p$, $x$ and $p$ are coprime
- `EQUIVALENCE_UNIFORM_PARTITION_RESTRICT`: If an equivalence relation partitions a finite set into classes of equal size, then the class size divides the set size
- `SHIFTABLE_REFL`, `SHIFTABLE_SYM`, `SHIFTABLE_TRANS`: Establish that the "shiftable" relation is an equivalence relation
- `LOOP_COPRIME`: A theorem about how coprime numbers force cycles to be non-constant
- `FINITE_CYCLES`: Shows that the set of cycles is finite
- `HAS_SIZE_IMAGE_INJ`: Size preservation under injective mappings 
- `HAS_SIZE_NUMSEG_LT`: The set $\{k \mid k < p\}$ has size $p$

#### Definitions
- `cycle`: Defines a $p$-cycle under relation $r$
- `shiftable`: Two functions are "shiftable" if one is a cyclic shift of the other

### Porting notes
When porting this theorem:
- The "shiftable" relation between functions is crucial and needs to be properly defined
- Handling of function equality and cyclic shifts might require different approaches in other systems
- The proof makes use of arithmetic simplifications and modular arithmetic properties of prime numbers
- The `WLOG` (without loss of generality) technique might need alternative implementations in other systems

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
This theorem proves a property of friendship relations in a finite set of people. Specifically, it shows that if a friendship relation satisfies these properties:
1. The set of all people is finite
2. No person is friends with themselves
3. Friendship is symmetric (if $x$ is friends with $y$, then $y$ is friends with $x$)
4. For any two distinct people $x$ and $y$, there exists a unique person $z$ who is friends with both of them

Then there must exist a person who is friends with everyone else.

Formally, for a binary relation $\text{friend}: \text{person} \to \text{person} \to \text{bool}$:
$$\forall \text{friend}. (\text{FINITE}(:\text{person}) \land (\forall x. \lnot(\text{friend}\ x\ x)) \land (\forall x,y. \text{friend}\ x\ y \Rightarrow \text{friend}\ y\ x) \land (\forall x,y. \lnot(x = y) \Rightarrow \exists! z. \text{friend}\ x\ z \land \text{friend}\ y\ z)) \Rightarrow \exists u. \forall v. \lnot(v = u) \Rightarrow \text{friend}\ u\ v$$

### Informal proof
We prove this theorem about friendship graphs through a series of steps involving graph theory and number theory:

* First, define the "mutual friend" function, which for any two distinct people returns their unique mutual friend.

* Define the "degree" of a person $p$ as the number of people they are friends with.

* Prove that if two people are not friends, they must have the same degree.

* Deduce that all people must have the same degree, which we'll call $m$.

* Show that $m > 0$ since the mutual friend property requires connections.

* Prove that $m$ must be even by using a pairing argument on the friendship relations.

* Establish a relationship between the total number of people $N$ and $m$: $N = m(m-1)+1$.

* Show $m \neq 2$ using the constraints of the problem.

* Use number theory: for $m-1 > 1$, find a prime factor $p$ that divides $m-1$.

* Analyze cycle structures in the friendship graph to show that $p$ must divide 1, which is impossible.

* This contradiction proves that the assumption must be false, and there must exist a universal friend.

The proof relies heavily on counting arguments about the structure of the friendship graph, combined with number theoretic results about prime factors, to reach a contradiction that forces the existence of a universal friend.

### Mathematical insight
This theorem provides a famous result in extremal graph theory known as the "Friendship Theorem" or sometimes the "Friendship Paradox." The result states that in a finite graph where any two vertices have exactly one common neighbor, there must exist a vertex adjacent to all others.

The key insight is that such a graph must have a very specific structure - it must be a "windmill graph" consisting of triangles that all share a single vertex (the universal friend). The proof is non-trivial and combines techniques from graph theory, combinatorics, and number theory. In particular, it establishes that in a friendship graph, everyone must have the same number of friends, and this constraint, along with the other properties, forces the existence of a universal friend.

This result has applications in social network theory and demonstrates how global structure can emerge from local constraints on relationships.

### Dependencies
- Theorems:
  - `DIVIDES_2` - Relates divisibility by 2 to the EVEN predicate
  - `PRIME_0` - Shows that 0 is not a prime number
  - `PRIME_1` - Shows that 1 is not a prime number
  - `PRIME_GE_2` - Shows that all prime numbers are at least 2
  - `PRIME_FACTOR` - States that any number greater than 1 has a prime factor
  - `PRIME_DIVEXP` - A number divides a power only if it divides the base
  - `DIVIDES_CONV` - Conversion for divisibility claims

### Porting notes
When porting this theorem:
1. The proof relies on several specialized lemmas about friendship graphs that aren't listed in the dependencies but would need to be ported first (`CYCLES_PRIME_LEMMA`, `HAS_SIZE_CYCLES`, `CARD_PATHCYCLES_STEP`, `HAS_SIZE_PATHS`, etc.).
2. The proof uses number theory and graph theory, requiring libraries for both.
3. Be prepared to adapt the sequence of steps involving the `ABBREV_TAC` tactic, which introduces abbreviations for expressions.
4. Graph-theoretic concepts like cycles and paths need careful translation into the target system.

---

