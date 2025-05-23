# wilson.ml

## Overview

Number of statements: 6

This file contains the formalization and proof of Wilson's theorem in number theory, which states that for any prime number p, (p-1)! ≡ -1 (mod p). The implementation builds on prime number theory, utilizing definitions and results from the prime and pocklington libraries. The file includes the formal statement of the theorem along with supporting lemmas and the complete proof structure.

## FACT_NPRODUCT

### FACT_NPRODUCT
- `FACT_NPRODUCT`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FACT_NPRODUCT = prove
 (`!n. FACT(n) = nproduct(1..n) (\i. i)`,
  INDUCT_TAC THEN
  REWRITE_TAC[FACT; NUMSEG_CLAUSES; ARITH; NPRODUCT_CLAUSES] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= SUC n`; NPRODUCT_CLAUSES; FINITE_NUMSEG] THEN
  REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC);;
```

### Informal statement
For any natural number $n$, the factorial of $n$ equals the product of numbers from $1$ to $n$, that is:
$$\text{FACT}(n) = \prod_{i=1}^{n} i$$

### Informal proof
The proof proceeds by mathematical induction on $n$:

- **Base case** ($n = 0$):
  - By definition, $\text{FACT}(0) = 1$
  - The product $\prod_{i=1}^{0} i$ is an empty product (since the range $1..0$ is empty), which equals $1$ by convention
  - Therefore, the statement holds for $n = 0$

- **Inductive step**:
  - Assume the statement holds for some natural number $n$
  - We need to prove it for $n+1$
  - By definition, $\text{FACT}(n+1) = (n+1) \cdot \text{FACT}(n)$
  - By the induction hypothesis, $\text{FACT}(n) = \prod_{i=1}^{n} i$
  - Therefore, $\text{FACT}(n+1) = (n+1) \cdot \prod_{i=1}^{n} i$
  - This equals $\prod_{i=1}^{n+1} i$ as required, since the product from $1$ to $n+1$ can be split into the product from $1$ to $n$ multiplied by $n+1$

The formal proof uses `NPRODUCT_CLAUSES` to handle the product operations, and arithmetic simplifications to verify the necessary conditions.

### Mathematical insight
This theorem establishes the equivalence between the recursive definition of factorial and its representation as a product. While this relationship is fundamental and often taken as the definition of factorial in mathematical contexts, in formal systems like HOL Light, factorial is typically defined recursively as:
- $\text{FACT}(0) = 1$
- $\text{FACT}(n+1) = (n+1) \cdot \text{FACT}(n)$

This theorem bridges the recursive and product-based definitions, which is useful for further theorems about factorial, particularly in number theory contexts. The result is particularly relevant for Wilson's theorem (as suggested by the comment), which states that for any prime number $p$, $(p-1)! \equiv -1 \pmod{p}$.

### Dependencies
- **Definitions**:
  - `FACT`: Factorial function
  - `nproduct`: Product of a function over a finite set of natural numbers
  - `NUMSEG_CLAUSES`: Properties of number segments
- **Theorems**:
  - `NPRODUCT_CLAUSES`: Rules for computing products
  - `FINITE_NUMSEG`: Finiteness of number segments
  - `IN_NUMSEG`: Membership in number segments

### Porting notes
When porting this theorem:
- Ensure the factorial function is defined recursively
- Verify that the product operation correctly handles empty ranges
- Make sure arithmetic simplification tactics can handle the simple inequalities used in the proof

---

## FACT_NPRODUCT_ALT

### Name of formal statement
FACT_NPRODUCT_ALT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FACT_NPRODUCT_ALT = prove
 (`!n. FACT(n) = nproduct(2..n) (\i. i)`,
  GEN_TAC THEN REWRITE_TAC[FACT_NPRODUCT] THEN
  DISJ_CASES_TAC(ARITH_RULE `n = 0 \/ 1 <= n`) THEN
  ASM_REWRITE_TAC[num_CONV `1`; NUMSEG_CLAUSES] THEN
  REWRITE_TAC[ARITH; NPRODUCT_CLAUSES; FACT] THEN
  ASM_SIMP_TAC[GSYM NUMSEG_LREC] THEN
  SIMP_TAC[NPRODUCT_CLAUSES; FINITE_NUMSEG; IN_NUMSEG; MULT_CLAUSES] THEN
  ARITH_TAC);;
```

### Informal statement
For any natural number $n$, the factorial of $n$ can be expressed as the product of all integers from $2$ to $n$:

$$\text{FACT}(n) = \prod_{i=2}^{n} i$$

### Informal proof
This theorem provides an alternative way to express the factorial function as a product starting from 2 rather than 1.

The proof proceeds as follows:
- Start by rewriting using `FACT_NPRODUCT`, which expresses factorial as the product from 1 to n
- Split into two cases: $n = 0$ or $n \geq 1$
- For the $n = 0$ case:
  - Apply the definition of factorial to show $\text{FACT}(0) = 1$
  - The product over an empty range (2..0) is 1 by definition of `NPRODUCT_CLAUSES`
- For the $n \geq 1$ case:
  - Apply the property that for $n \geq 1$, the product from 1 to n equals 1 times the product from 2 to n
  - Rewrite using `NUMSEG_LREC` to express the range 2..n recursively
  - Simplify the product using `NPRODUCT_CLAUSES`
  - Complete the proof using arithmetic simplification

### Mathematical insight
This theorem provides an alternative representation of the factorial function as a product starting from 2 instead of the standard definition that starts from 1. This is useful in some combinatorial contexts and simplifies certain calculations by avoiding the trivial multiplication by 1.

The result might seem simple, but it's a convenient form that is often needed in combinatorial proofs and calculations. For example, when dealing with binomial coefficients and other combinatorial identities, it's sometimes more natural to work with products that start from 2.

### Dependencies
- Theorems:
  - `FACT_NPRODUCT`: The standard representation of factorial as product from 1 to n
  - `NUMSEG_CLAUSES`: Properties of numerical ranges
  - `NPRODUCT_CLAUSES`: Properties of products over numerical ranges
  - `GSYM NUMSEG_LREC`: Recursive representation of numerical ranges
  - `ARITH_RULE`: Automated arithmetic reasoning
  - `ARITH`: Automated arithmetic simplification

### Porting notes
When porting this theorem:
- Ensure that the target system has a well-defined notation for products over ranges
- The proof relies heavily on automated arithmetic reasoning, which may need to be expanded in systems with less powerful automation
- The representation of numerical ranges (like 2..n) might differ in other systems and may require explicit translation

---

## NPRODUCT_PAIRUP_INDUCT

### Name of formal statement
NPRODUCT_PAIRUP_INDUCT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NPRODUCT_PAIRUP_INDUCT = prove
 (`!f r n s. FINITE s /\ CARD s = n /\
             (!x:A. x IN s ==> ?!y. y IN s /\ ~(y = x) /\
                                    (f(x) * f(y) == 1) (mod r))
             ==> (nproduct s f == 1) (mod r)`,
  GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `s:A->bool` THEN ASM_CASES_TAC `s:A->bool = {}` THEN
  ASM_REWRITE_TAC[NPRODUCT_CLAUSES; CONG_REFL] THEN STRIP_TAC THEN
  ASM_CASES_TAC `n = 0` THENL [ASM_MESON_TAC[CARD_EQ_0]; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `a:A` o
    GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `n - 2`) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> n - 2 < n`] THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:A`) THEN REWRITE_TAC[ASSUME `(a:A) IN s`] THEN
  REWRITE_TAC[EXISTS_UNIQUE] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `(s DELETE a) DELETE (b:A)`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_DELETE] THEN
    SIMP_TAC[FINITE_DELETE; ASSUME `FINITE(s:A->bool)`; CARD_DELETE] THEN
    ASM_REWRITE_TAC[IN_DELETE] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x:A) IN s`)) THEN
    REWRITE_TAC[EXISTS_UNIQUE] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `y:A` THEN STRIP_TAC THEN CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[MULT_SYM]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(b:A) IN s`)) THEN
    REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`a:A`; `x:A`] o CONJUNCT2) THEN
    ASM_MESON_TAC[MULT_SYM];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `s = (a:A) INSERT (b INSERT (s DELETE a DELETE b))`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SIMP_TAC[NPRODUCT_CLAUSES; FINITE_INSERT; FINITE_DELETE;
           ASSUME `FINITE(s:A->bool)`] THEN
  ASM_REWRITE_TAC[IN_INSERT; IN_DELETE; MULT_CLAUSES] THEN
  REWRITE_TAC[MULT_ASSOC] THEN
  ONCE_REWRITE_TAC[SYM(NUM_REDUCE_CONV `1 * 1`)] THEN
  MATCH_MP_TAC CONG_MULT THEN ASM_REWRITE_TAC[]);;
```

### Informal statement
For all functions $f$ and integers $r, n$, if $s$ is a finite set with cardinality $n$, and for every $x \in s$, there exists a unique $y \in s$ such that $y \neq x$ and $(f(x) \cdot f(y) \equiv 1) \pmod{r}$, then $\prod_{x \in s} f(x) \equiv 1 \pmod{r}$.

In other words, if every element in a finite set can be uniquely paired with another element such that their function values multiply to give 1 modulo $r$, then the product of all function values is also 1 modulo $r$.

### Informal proof
We prove this by induction on the cardinality $n$ of the set $s$.

* **Base case**: If $s = \emptyset$, then $\prod_{x \in s} f(x) = 1$ by definition, so the result holds trivially.

* **Inductive case**: Suppose $s$ is non-empty and $n > 0$.
  - Choose an element $a \in s$.
  - By our assumption, there exists a unique $b \in s$ such that $b \neq a$ and $(f(a) \cdot f(b) \equiv 1) \pmod{r}$.
  - Consider the set $s' = s \setminus \{a, b\}$. Note that $|s'| = n - 2 < n$.
  - We need to show that the pairing property still holds for $s'$.
  - For any $x \in s'$, let $y$ be the unique element in $s$ such that $y \neq x$ and $(f(x) \cdot f(y) \equiv 1) \pmod{r}$.
  - We need to verify that $y \in s'$. If $y = a$, then $f(x) \cdot f(a) \equiv 1 \pmod{r}$, implying $f(x) \equiv f(b) \pmod{r}$ (since $f(a) \cdot f(b) \equiv 1$), which contradicts uniqueness. Similarly, $y \neq b$.
  - So the pairing property holds for $s'$, and by induction, $\prod_{x \in s'} f(x) \equiv 1 \pmod{r}$.
  - Finally, $\prod_{x \in s} f(x) = f(a) \cdot f(b) \cdot \prod_{x \in s'} f(x) \equiv 1 \cdot 1 \equiv 1 \pmod{r}$.

### Mathematical insight
This theorem provides a powerful tool for modular arithmetic problems involving products. It shows that when elements can be paired in a specific way where each pair's product is congruent to 1, the entire product is also congruent to 1.

The result has applications in number theory, particularly in problems involving residues and congruences. It's especially useful in contexts like the Pocklington primality test or Wilson's theorem, where we need to analyze products modulo a number.

The theorem essentially formalizes the intuition that if we can partition a set into pairs, where each pair contributes a factor congruent to 1, then the entire product must also be congruent to 1.

### Dependencies
#### Theorems
- `CONG_MULT`: If $(x \equiv x') \pmod{n}$ and $(y \equiv y') \pmod{n}$, then $(x \cdot y \equiv x' \cdot y') \pmod{n}$
- `num_WF`: Well-foundedness of natural numbers (used for induction)
- `NPRODUCT_CLAUSES`: Basic properties of the product operator
- `CARD_DELETE`, `CARD_EQ_0`: Properties of cardinality of sets
- `FINITE_DELETE`, `FINITE_INSERT`: Properties of finite sets

### Porting notes
When porting this theorem:
1. Ensure your system has a modular arithmetic library with congruence relations
2. Check how set operations and finite product operations are represented in your target system
3. The proof relies heavily on reasoning about unique pairs within sets, so make sure your system can handle this type of reasoning
4. The induction is on the cardinality of the set rather than a more typical induction on natural numbers, which might require special handling

---

## NPRODUCT_PAIRUP

### Name of formal statement
NPRODUCT_PAIRUP

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NPRODUCT_PAIRUP = prove
 (`!f r s. FINITE s /\
           (!x:A. x IN s ==> ?!y. y IN s /\ ~(y = x) /\
                                  (f(x) * f(y) == 1) (mod r))
           ==> (nproduct s f == 1) (mod r)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NPRODUCT_PAIRUP_INDUCT THEN
  EXISTS_TAC `CARD(s:A->bool)` THEN ASM_REWRITE_TAC[]);;
```

### Informal statement
For any function $f$, modulus $r$, and finite set $s$ of type $A$, if for every element $x \in s$ there exists a unique element $y \in s$ such that:
- $y \neq x$
- $f(x) \cdot f(y) \equiv 1 \pmod{r}$

Then the product of $f$ over all elements in $s$ is congruent to 1 modulo $r$:
$\prod_{x \in s} f(x) \equiv 1 \pmod{r}$

### Informal proof
The proof applies an induction principle specifically designed for this kind of "pairing up" scenario:

- The theorem is proved by applying the induction principle `NPRODUCT_PAIRUP_INDUCT`
- We use the cardinality of the set $s$ as the induction parameter
- The assumptions in the theorem statement provide exactly the conditions needed for the induction principle

The core insight is that when elements can be paired such that each pair's product is congruent to 1 modulo $r$, then the product over all elements must also be congruent to 1 modulo $r$.

### Mathematical insight
This theorem captures an important property of modular arithmetic when applied to products over finite sets. The key insight is that if elements in a set can be uniquely paired such that each pair's product is congruent to 1 modulo $r$, then the entire product collapses to 1 modulo $r$.

This result is particularly useful in number theory and group theory, especially when dealing with:
- Proving properties of modular products
- Working with quadratic residues
- Analyzing special structures in finite groups

The "pairing up" property essentially creates a collection of self-canceling pairs in the modular multiplication context.

### Dependencies
- `NPRODUCT_PAIRUP_INDUCT`: An induction principle for proving properties about products of paired elements
- `CARD`: Function that gives the cardinality of a finite set
- `nproduct`: Function that computes the product of a function over a finite set

### Porting notes
When porting this theorem:
- Ensure the target system has a proper notion of modular arithmetic
- Check that the target system has a corresponding function for taking products over finite sets
- The induction principle `NPRODUCT_PAIRUP_INDUCT` might need to be ported first as it seems to be a specialized induction principle not commonly found in standard libraries
- The proof relies on the uniqueness of the pairing, which must be properly formalized in the target system

---

## WILSON

### WILSON
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let WILSON = prove
 (`!p. prime(p) ==> (FACT(p - 1) == p - 1) (mod p)`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `p = 0` THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  ASM_CASES_TAC `p = 1` THENL [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
  ASM_CASES_TAC `p = 2` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[CONG_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `FACT(p - 1) = FACT(p - 2) * (p - 1)` SUBST1_TAC THENL
   [SUBGOAL_THEN `p - 1 = SUC(p - 2)`
     (fun th -> REWRITE_TAC[th; FACT; MULT_AC]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `x = 1 * x`] THEN
  MATCH_MP_TAC CONG_MULT THEN REWRITE_TAC[CONG_REFL] THEN
  REWRITE_TAC[FACT_NPRODUCT_ALT] THEN MATCH_MP_TAC NPRODUCT_PAIRUP THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `x:num` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `x:num`] CONG_UNIQUE_INVERSE_PRIME) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM] THEN MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
   [MATCH_MP_TAC MONO_EXISTS;
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC] THEN
  X_GEN_TAC `y:num` THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `y = 1` THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 <= y <=> 0 < y /\ ~(y = 1)`] THEN
    UNDISCH_TAC `(x * y == 1) (mod p)` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
    ASM_SIMP_TAC[CONG; MOD_LT; ARITH_RULE `x <= p - 2 /\ ~(p = 0) ==> x < p`;
                 ARITH_RULE `~(p = 0) /\ ~(p = 1) ==> 1 < p`] THEN
    UNDISCH_TAC `2 <= x` THEN ARITH_TAC;
    MATCH_MP_TAC(ARITH_RULE `y < p /\ ~(y = p - 1) ==> y <= p - 2`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `(x * y == 1) (mod p)` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN SUBGOAL_THEN `(x + 1 == 0) (mod p)` MP_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[CONG_0] THEN DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
      MAP_EVERY UNDISCH_TAC [`2 <= x`; `x <= p - 2`] THEN ARITH_TAC] THEN
    MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC `x * p:num` THEN CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC[CONG_0] THEN MESON_TAC[divides; MULT_SYM]] THEN
    SUBGOAL_THEN `x * p = x + x * (p - 1)` SUBST1_TAC THENL
     [REWRITE_TAC[LEFT_SUB_DISTRIB; MULT_CLAUSES] THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_MP_TAC(GSYM SUB_ADD) THEN
      GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `x = x * 1`] THEN
      ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN
      UNDISCH_TAC `~(p = 0)` THEN ARITH_TAC;
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[CONG_SYM] THEN MATCH_MP_TAC CONG_ADD THEN
    ASM_REWRITE_TAC[CONG_REFL];
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `((x + 1) * (x - 1) == 0) (mod p)` MP_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[CONG_0] THEN
      DISCH_THEN(MP_TAC o CONJ (ASSUME `prime p`)) THEN
      DISCH_THEN(MP_TAC o MATCH_MP PRIME_DIVPROD) THEN
      DISCH_THEN(DISJ_CASES_THEN (MP_TAC o MATCH_MP DIVIDES_LE)) THEN
      MAP_EVERY UNDISCH_TAC
        [`2 <= x`; `x <= p - 2`; `~(p = 1)`; `~(p = 0)`] THEN
      ARITH_TAC] THEN
    ONCE_REWRITE_TAC[GSYM(SPEC `1` CONG_ADD_LCANCEL_EQ)] THEN
    SUBGOAL_THEN `1 + (x + 1) * (x - 1) = x * x`
     (fun th -> ASM_REWRITE_TAC[th; ARITH]) THEN
    REWRITE_TAC[LEFT_SUB_DISTRIB] THEN
    MATCH_MP_TAC(ARITH_RULE
     `(x + 1) * 1 <= (x + 1) * x
      ==> 1 + (x + 1) * x - (x + 1) * 1 = x * x`) THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN UNDISCH_TAC `2 <= x` THEN ARITH_TAC]);;
```

### Informal statement
Wilson's theorem states that for any prime number $p$:

$$\text{FACT}(p - 1) \equiv p - 1 \pmod{p}$$

where $\text{FACT}(n)$ represents the factorial of $n$.

### Informal proof
The proof proceeds by cases on the prime $p$:

- If $p = 0$, we get a contradiction since 0 is not prime (using `PRIME_0`).
- If $p = 1$, we get a contradiction since 1 is not prime (using `PRIME_1`).
- If $p = 2$, then $(2-1)! = 1! = 1 \equiv 1 \pmod{2}$, which is true.

For $p > 2$, the main proof:

1. First, we rewrite $\text{FACT}(p-1) = \text{FACT}(p-2) \cdot (p-1)$.

2. We need to prove $(p-1)! \equiv p-1 \pmod{p}$, which we rewrite as $1 \cdot (p-1)! \equiv 1 \cdot (p-1) \pmod{p}$.

3. Using the congruence of multiplication (`CONG_MULT`), we need to show:
   - $1 \equiv 1 \pmod{p}$ (trivial)
   - $\text{FACT}(p-2) \equiv 1 \pmod{p}$

4. We express $\text{FACT}(p-2)$ as a product of numbers from 1 to $p-2$.

5. The key insight is to pair up multiplicands in this factorial. For each $x$ where $2 \leq x \leq p-2$, we can find a unique $y$ such that:
   - $1 \leq y \leq p-1$
   - $x \cdot y \equiv 1 \pmod{p}$

6. Using `CONG_UNIQUE_INVERSE_PRIME`, we show that for each $x$ in the range, there exists a unique modular multiplicative inverse $y$ such that $x \cdot y \equiv 1 \pmod{p}$.

7. We prove that for each $x$ in the range, its inverse $y$ is also in the range $[1,p-2]$:
   - If $y = 1$, then $x \equiv 1 \pmod{p}$, which contradicts $2 \leq x \leq p-2$.
   - If $y = p-1$, we get a contradiction by showing that $(x+1) \cdot (x-1) \equiv 0 \pmod{p}$, which is impossible given our constraints on $x$.

8. Since each element in $[2,p-2]$ can be paired with its unique inverse in the same range, their product is $\equiv 1 \pmod{p}$.

9. Therefore, $\text{FACT}(p-2) \equiv 1 \pmod{p}$ and thus $(p-1)! \equiv p-1 \pmod{p}$.

### Mathematical insight
Wilson's theorem provides a necessary and sufficient condition for a number to be prime: $p > 1$ is prime if and only if $(p-1)! \equiv -1 \pmod{p}$.

The key idea in the proof is the pairing property of modular multiplicative inverses in a prime modulus. In a multiplicative group modulo a prime, every element (except 1 and p-1) pairs with exactly one other element to give a product congruent to 1. The elements 1 and p-1 are their own inverses. This pairing explains why the factorial has the specific residue of p-1 modulo p.

Wilson's theorem has applications in number theory and is often used in theoretical proofs, though it's not practical for primality testing due to the computational complexity of calculating large factorials.

### Dependencies
- **Theorems**:
  - `CONG_MULT`: Congruence property for multiplication
  - `CONG_ADD_LCANCEL_EQ`: Left cancellation for addition in congruences
  - `CONG_UNIQUE_INVERSE_PRIME`: Uniqueness of multiplicative inverse modulo a prime
  - `PRIME_0`: 0 is not prime
  - `PRIME_1`: 1 is not prime
  - `PRIME_DIVPROD`: Prime divisor of a product divides at least one factor

### Porting notes
When porting this theorem:
1. Ensure your system has a well-established theory of modular arithmetic, especially modular multiplicative inverses.
2. Make sure the factorial function is appropriately defined.
3. The pairing argument in the middle of the proof is the most intricate part and requires careful handling of the ranges for the inverse elements.

---

## WILSON_EQ

### Name of formal statement
WILSON_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WILSON_EQ = prove
 (`!p. ~(p = 1) ==> (prime p <=> (FACT(p - 1) == p - 1) (mod p))`,
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN EQ_TAC THEN SIMP_TAC[WILSON] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP PRIME_FACTOR) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[CONG_MOD_0] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[LE_LT] THEN ASM_CASES_TAC `n:num = p` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE `x < y ==> x <= y - 1`)) THEN
  ASM_SIMP_TAC[GSYM DIVIDES_FACT_PRIME] THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  SUBGOAL_THEN `p divides FACT(n - 1) <=> p divides (n - 1)` SUBST1_TAC THENL
   [MATCH_MP_TAC CONG_DIVIDES THEN
    MATCH_MP_TAC CONG_DIVIDES_MODULUS THEN EXISTS_TAC `n:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN SUBGOAL_THEN `p divides 1` MP_TAC THENL
   [MATCH_MP_TAC DIVIDES_ADD_REVR THEN EXISTS_TAC `n - 1` THEN
    ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> n - 1 + 1 = n`];
    REWRITE_TAC[DIVIDES_ONE] THEN ASM_MESON_TAC[PRIME_1]]);;
```

### Informal statement
For any natural number $p \neq 1$, $p$ is prime if and only if $(p-1)! \equiv p-1 \pmod{p}$, where $(p-1)!$ denotes the factorial of $p-1$.

### Informal proof
The proof establishes the equivalence between a number being prime and satisfying Wilson's theorem. The proof proceeds as follows:

* The forward direction (if $p$ is prime, then $(p-1)! \equiv p-1 \pmod{p}$) is directly handled by the existing theorem `WILSON`.

* For the reverse direction, we show that if $(p-1)! \equiv p-1 \pmod{p}$, then $p$ must be prime:
  * We use `PRIME_FACTOR` to show that any $n \neq 1$ has a prime factor $p$ that divides $n$.
  * By `DIVIDES_LE`, we know that $p \leq n$.
  * We handle the case $n = 0$ separately (showing it's false).
  * If $n = p$, then $n$ is prime and we're done.
  * Otherwise, $p < n$, which means $p \leq n-1$.
  * By `DIVIDES_FACT_PRIME`, this implies that $p$ divides $(n-1)!$.
  * Using `CONG_DIVIDES_MODULUS` and `CONG_DIVIDES`, we can show that $p$ divides $(n-1)!$ if and only if $p$ divides $(n-1)$.
  * If $p$ divides both $(n-1)!$ and $(n-1)$, then by the congruence assumption and arithmetic, $p$ must divide $1$.
  * But this contradicts $p$ being prime (as shown by `PRIME_1`), unless $p = n$, confirming that $n$ is prime.

### Mathematical insight
This theorem provides a complete characterization of primality using Wilson's theorem, which states that for a prime $p$, $(p-1)! \equiv p-1 \pmod{p}$. The result shows that this condition is not only necessary but also sufficient for primality.

Wilson's theorem is a classic result in number theory that gives an elegant (though impractical for computation) primality test. The equivalence proven here shows that this criterion fully characterizes prime numbers, providing a deeper understanding of the relationship between factorials, congruences, and prime numbers.

### Dependencies
#### Theorems
- `WILSON`: The forward direction of Wilson's theorem (if $p$ is prime, then $(p-1)! \equiv p-1 \pmod{p}$)
- `PRIME_FACTOR`: Every number greater than 1 has a prime factor
- `DIVIDES_LE`: If $p$ divides $n$ and $p > 0$, then $p \leq n$
- `DIVIDES_FACT_PRIME`: A prime $p$ divides $n!$ if and only if $p \leq n$
- `CONG_DIVIDES_MODULUS`: If $x \equiv y \pmod{m}$ and $n$ divides $m$, then $x \equiv y \pmod{n}$
- `CONG_DIVIDES`: If $x \equiv y \pmod{n}$, then $n$ divides $x$ if and only if $n$ divides $y$
- `PRIME_1`: $1$ is not prime

### Porting notes
When porting this theorem, ensure that:
1. The factorial function is properly defined
2. Modular arithmetic and congruence relations are properly set up
3. The various dependency theorems about divisibility and primality are available
4. The ported proof system has sufficient number theory automation to handle the arithmetic reasoning

---

