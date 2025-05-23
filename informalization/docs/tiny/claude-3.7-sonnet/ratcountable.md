# ratcountable.ml

## Overview

Number of statements: 6

This file formalizes the countability of rational numbers (Theorem 3), demonstrating that the set of rational numbers has the same cardinality as the natural numbers. It builds on the cardinality theory from the card.ml library to establish a bijection between rationals and naturals. The file includes the formal proof that the set of rational numbers is countable, a fundamental result in set theory and the theory of cardinality.

## rational

### Name of formal statement
rational

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let rational = new_definition
  `rational(r) <=> ?p q. ~(q = 0) /\ (abs(r) = &p / &q)`;;
```

### Informal statement
A real number $r$ is rational if and only if there exist natural numbers $p$ and $q$ such that $q \neq 0$ and $|r| = \frac{p}{q}$.

In mathematical notation:
$$\text{rational}(r) \iff \exists p, q \in \mathbb{N} \text{ such that } q \neq 0 \land |r| = \frac{p}{q}$$

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
This definition characterizes rational numbers in terms of their representation as fractions of natural numbers. The key aspects of this definition are:

1. It uses the absolute value $|r|$ rather than $r$ directly, which means we only need to represent the magnitude of the number as a fraction, simplifying the handling of negative rationals.

2. It requires $q \neq 0$ to avoid division by zero.

3. The definition uses natural numbers ($p$ and $q$) rather than integers. This is a slight variation from the common definition where $p$ and $q$ are integers with $\gcd(p,q)=1$. Using natural numbers simplifies some formal proofs.

4. This definition is foundational for proving the countability of rational numbers, as indicated in the comment.

This definition is part of a development toward showing that rational numbers form a countable set, which is a fundamental result in set theory and the theory of cardinality.

### Dependencies
No explicit dependencies are shown in the provided information.

### Porting notes
When porting this definition to other proof assistants:

1. Ensure that the target system has appropriate definitions of natural numbers, real numbers, and absolute value.

2. Be aware that some systems might already have built-in definitions of rational numbers that could differ slightly from this one.

3. If the system prefers to use integers rather than natural numbers in the definition, you may need to adjust the definition accordingly.

4. The comment suggests this is part of a development about countability of rationals, so you may also need to port related definitions and theorems about cardinality.

---

## countable

### Name of formal statement
countable

### Type of formal statement
new_definition

### Formal Content
```ocaml
let countable = new_definition
  `countable s <=> s <=_c (UNIV:num->bool)`;;
```

### Informal statement
A set $s$ is countable if and only if the cardinality of $s$ is at most the cardinality of the power set of natural numbers. Formally:

$$\text{countable}(s) \iff s \leq_c (\text{UNIV}:num\to bool)$$

Where $\leq_c$ represents the cardinal comparison relation "less than or equal to", and $(\text{UNIV}:num\to bool)$ represents the universal set of type $num\to bool$, which consists of all functions from natural numbers to booleans (equivalent to the power set of natural numbers).

### Informal proof
This is a definition, so no proof is required.

### Mathematical insight
This definition captures the standard mathematical notion of countability. A set is countable if it can be put into a one-to-one correspondence with either the set of natural numbers or a subset of the natural numbers.

In HOL Light, the definition uses the cardinal comparison operator (`<=_c`) to express that there exists an injection from the set `s` to the universal set of type `num->bool` (which represents the power set of natural numbers). This is equivalent to saying that the cardinality of `s` is at most the cardinality of the natural numbers.

This definition is fundamental in set theory and the theory of cardinality, providing a foundation for distinguishing between different sizes of infinite sets.

### Dependencies
None specified in the provided dependency list.

### Porting notes
When porting this definition to other proof assistants:
1. Ensure the target system has a notion of cardinal comparison (≤ₖ) between sets
2. The universal set notation might differ across systems - in some systems, you might need to explicitly define it as the set of all objects of a certain type
3. If the target system uses a different representation of sets than HOL Light, adjust the definition accordingly

---

## COUNTABLE_RATIONALS

### Name of formal statement
COUNTABLE_RATIONALS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COUNTABLE_RATIONALS = prove
 (`countable { x:real | rational(x)}`,
  REWRITE_TAC[countable] THEN TRANS_TAC CARD_LE_TRANS
   `{ x:real | ?p q. x = &p / &q } *_c (UNIV:num->bool)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LE_C; EXISTS_PAIR_THM; mul_c] THEN
    EXISTS_TAC `\(x,b). if b = 0 then x else --x` THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[IN_ELIM_THM; rational; IN_UNIV; PAIR_EQ] THEN
    MESON_TAC[REAL_ARITH `(abs(x) = a) ==> (x = a) \/ x = --a`];
    ALL_TAC] THEN
  MATCH_MP_TAC CARD_MUL_ABSORB_LE THEN REWRITE_TAC[num_INFINITE] THEN
  TRANS_TAC CARD_LE_TRANS `(UNIV *_c UNIV):num#num->bool` THEN CONJ_TAC THENL
   [REWRITE_TAC[LE_C; EXISTS_PAIR_THM; mul_c; IN_UNIV] THEN
    EXISTS_TAC `\(p,q). &p / &q` THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[IN_ELIM_THM; rational] THEN MESON_TAC[];
    MESON_TAC[CARD_MUL_ABSORB_LE; CARD_LE_REFL; num_INFINITE]]);;
```

### Informal statement
The set of rational real numbers is countable, formally stated as:
$$\text{countable} \{ x \in \mathbb{R} \mid \text{rational}(x) \}$$

### Informal proof
The proof shows that the set of rational numbers is countable by establishing cardinality relationships.

* First, we rewrite using the definition of countability and establish a cardinality relationship through transitivity:
  $$\{ x \in \mathbb{R} \mid \text{rational}(x) \} \leq_c \{ x \in \mathbb{R} \mid \exists p,q.\ x = \frac{p}{q} \} \times_c \mathbb{N}$$

* For the first part of the transitivity, we need to show that the set of rational numbers is in bijection with the product of the set of fractions and natural numbers:
  * We define an injection $f(x,b) = \begin{cases} x & \text{if}\ b = 0 \\ -x & \text{otherwise} \end{cases}$
  * This maps every rational number to either itself or its negative, establishing that each rational number can be represented as either a positive fraction or a negative fraction, covering the entire set of rational numbers.

* For the second part, we show that $\{ x \in \mathbb{R} \mid \exists p,q.\ x = \frac{p}{q} \} \times_c \mathbb{N} \leq_c \mathbb{N}$:
  * First, we establish that $\{ x \in \mathbb{R} \mid \exists p,q.\ x = \frac{p}{q} \} \leq_c \mathbb{N} \times_c \mathbb{N}$ by defining a function that maps each fraction to its numerator-denominator pair.
  * We use the fact that $\mathbb{N}$ is infinite and apply the theorem `CARD_MUL_ABSORB_LE` to conclude that $\mathbb{N} \times_c \mathbb{N} \leq_c \mathbb{N}$.
  * Through transitivity, we establish that the set of rational numbers is at most countable.

### Mathematical insight
This theorem establishes the fundamental result that the set of rational numbers is countable, which contrasts with the uncountability of real numbers (Cantor's theorem). The proof uses a standard approach of showing that the rationals can be put in one-to-one correspondence with a subset of natural numbers.

The key insight is decomposing the rational numbers into positive and negative parts, and then showing that the set of fractions can be mapped to pairs of natural numbers (numerator and denominator). Since the Cartesian product of countable sets is countable, and the natural numbers are infinite, we can conclude that rationals are countable.

### Dependencies
#### Theorems
- `CARD_LE_REFL`: For any set s, s ≤ₖ s (reflexivity of cardinality comparison)
- `CARD_LE_TRANS`: For sets s, t, u, if s ≤ₖ t and t ≤ₖ u, then s ≤ₖ u (transitivity of cardinality comparison)
- `CARD_MUL_ABSORB_LE`: For sets s and t, if t is infinite and s ≤ₖ t, then s ×ₖ t ≤ₖ t

#### Definitions
- `mul_c`: Defines the Cartesian product of sets: s ×ₖ t = {(x,y) | x ∈ s ∧ y ∈ t}

### Porting notes
When porting this proof to other systems:
1. The definition of "countable" might vary across systems - in HOL Light it essentially means "at most countable" (can be put in bijection with a subset of natural numbers).
2. The handling of rational numbers may differ. Some systems might have built-in types for rational numbers, while others might represent them as pairs of integers or other equivalent representations.
3. Pay attention to how the Cartesian product is defined in the target system, as the definition of `mul_c` is crucial for this proof.

---

## denumerable

### Name of formal statement
denumerable

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let denumerable = new_definition
  `denumerable s <=> s =_c (UNIV:num->bool)`;;
```

### Informal statement
A set $s$ is denumerable if and only if it has the same cardinality as the set of natural numbers, i.e., $s =_c \mathbb{N}$.

Here, $=_c$ represents cardinal equality (having the same cardinality), and `UNIV:num->bool` represents the universal set of natural numbers.

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
This definition formalizes the concept of denumerability, which is a fundamental notion in set theory and the theory of cardinality. A set is denumerable (also commonly called "countably infinite") if there exists a bijection between it and the set of natural numbers.

Denumerable sets represent the smallest infinite cardinality (ℵ₀) and play a crucial role in distinguishing between different sizes of infinity. Many important sets in mathematics are denumerable, such as the integers and rational numbers, while others like the real numbers are not.

In the context of formal mathematics, having a precise definition of denumerability allows for clearer statements and proofs about cardinality and set-theoretic properties.

### Dependencies
This definition uses cardinal equality (=_c), which would have been defined elsewhere in the formalization.

### Porting notes
When porting this definition to another proof assistant:
1. Ensure that cardinal equality (=_c) is already defined in the target system
2. Verify how the universal set of natural numbers is represented in the target system (e.g., in Lean it might be `ℕ`)
3. The notion of denumerability may already exist in some form in standard libraries of other proof assistants, possibly under names like "countably infinite" or "equinumerous with naturals"

---

## DENUMERABLE_RATIONALS

### Name of formal statement
DENUMERABLE_RATIONALS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DENUMERABLE_RATIONALS = prove
 (`denumerable { x:real | rational(x)}`,
  REWRITE_TAC[denumerable; GSYM CARD_LE_ANTISYM] THEN
  REWRITE_TAC[GSYM countable; COUNTABLE_RATIONALS] THEN
  REWRITE_TAC[le_c] THEN EXISTS_TAC `&` THEN
  SIMP_TAC[IN_ELIM_THM; IN_UNIV; REAL_OF_NUM_EQ; rational] THEN
  X_GEN_TAC `p:num` THEN MAP_EVERY EXISTS_TAC [`p:num`; `1`] THEN
  REWRITE_TAC[REAL_DIV_1; REAL_ABS_NUM; ARITH_EQ]);;
```

### Informal statement
The set of rational real numbers is denumerable. Formally, $\{x \in \mathbb{R} \mid x \text{ is rational}\}$ is denumerable.

### Informal proof
To prove that the set of rational real numbers is denumerable, we need to show that it has the same cardinality as the natural numbers.

- We begin by using the definition of denumerable and applying the antisymmetry of cardinal ordering (`CARD_LE_ANTISYM`), reducing our goal to proving that the set of rationals is both countable and that the natural numbers can be injected into it.

- For the first part, we use `COUNTABLE_RATIONALS` which states that the rational numbers are countable.

- For the second part, we need to show there exists an injection from natural numbers to rationals. We construct this injection by mapping each natural number $p$ to itself as a real number (using `&`).

- For any natural number $p$, we show that $p$ is rational by representing it as $\frac{p}{1}$, which satisfies the definition of a rational number.

- The natural number $p$ maps to the real number $p$ which equals $\frac{p}{1}$, proving that our constructed function is indeed an injection from natural numbers to rational numbers.

### Mathematical insight
This theorem establishes that the set of rational numbers has the same cardinality as the set of natural numbers, making it denumerable (countably infinite). This is a fundamental result in set theory and the theory of cardinality.

The key insight is that while the rational numbers might seem "more numerous" than natural numbers since they are dense in the real line, they can actually be put in one-to-one correspondence with the natural numbers. This contrasts with the real numbers, which are uncountable.

The proof uses a two-way approach: showing both that the rationals are countable (which typically involves constructing an enumeration of all rationals) and that the natural numbers can be injected into the rationals (which is straightforward since every natural number is a rational).

### Dependencies
- **Theorems**:
  - `CARD_LE_ANTISYM`: Antisymmetry of cardinal ordering: $s ≤_c t ∧ t ≤_c s ⟺ s =_c t$
  - `COUNTABLE_RATIONALS`: The set of rational numbers is countable

### Porting notes
When porting this theorem to other proof assistants:
1. Make sure the target system has a definition of rationals, countability, and cardinality
2. The injection from natural numbers to rationals is simple (each n maps to n/1), but expressing this function may differ in syntax
3. The proof relies on both directions of the cardinality relationship, which might need to be approached differently depending on how cardinality is defined in the target system

---

## DENUMERABLE_RATIONALS_EXPAND

### Name of formal statement
DENUMERABLE_RATIONALS_EXPAND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DENUMERABLE_RATIONALS_EXPAND = prove
 (`?rat:num->real. (!n. rational(rat n)) /\
                   (!x. rational x ==> ?!n. x = rat n)`,
  MP_TAC DENUMERABLE_RATIONALS THEN REWRITE_TAC[denumerable] THEN
  ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN REWRITE_TAC[eq_c] THEN
  REWRITE_TAC[IN_UNIV; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[]);;
```

### Informal statement
There exists a function $\text{rat}: \mathbb{N} \to \mathbb{R}$ such that:
1. For all $n \in \mathbb{N}$, $\text{rat}(n)$ is a rational number.
2. For any rational number $x \in \mathbb{R}$, there exists a unique natural number $n$ such that $x = \text{rat}(n)$.

In other words, the theorem states that there exists an enumeration of all rational numbers.

### Informal proof
The proof starts from the theorem `DENUMERABLE_RATIONALS`, which states that the set of rational numbers is denumerable. 

- First, we rewrite using the definition of `denumerable`, which states that a set is denumerable if it has the same cardinality as the natural numbers.
- Then, we apply the symmetry of cardinal equality (`CARD_EQ_SYM`), which allows us to switch the order in the cardinality comparison.
- We then rewrite with the definition of cardinal equality (`eq_c`), which involves the existence of a bijection.
- The expressions `IN_UNIV` and `IN_ELIM_THM` are used to simplify the characteristic functions involved in the bijection.
- Finally, we use `MONO_EXISTS` and the automated theorem prover `MESON_TAC` to conclude the proof.

In essence, the proof translates the statement "the rational numbers are denumerable" into the equivalent statement "there exists an enumeration function for the rational numbers."

### Mathematical insight
This theorem provides an explicit formulation of the countability of rational numbers, expressing it in terms of an enumeration function rather than using cardinal comparisons. This formulation is often more convenient for further mathematical development since it gives us a concrete way to refer to rational numbers by natural number indices.

The result is a fundamental fact in set theory and analysis, establishing that despite being dense in the real numbers, the rational numbers form a countable set.

### Dependencies
- Theorems:
  - `DENUMERABLE_RATIONALS`: States that the rational numbers are denumerable
  - `CARD_EQ_SYM`: Cardinal equality is symmetric
  - `eq_c`: Definition of cardinal equality
  - `IN_UNIV`: Membership in the universal set
  - `IN_ELIM_THM`: Simplification of set membership

### Porting notes
When porting this theorem, ensure that:
1. The target system has a definition of rational numbers and associated predicates
2. Cardinal equality and denumerability concepts are properly defined
3. The target system has appropriate tactics for handling existential quantifiers and equality reasoning

---

