# realsuncountable.ml

## Overview

Number of statements: 12

This file formalizes the proof that the real numbers are uncountable (non-denumerable), also known as Cantor's theorem on the uncountability of the continuum. It builds on the HOL Light cardinal number theory and analysis libraries to establish that there is no surjection from the natural numbers to the reals. The proof likely uses Cantor's diagonal argument or a related technique to demonstrate that the cardinality of the reals exceeds that of the natural numbers.

## countable

### Name of formal statement
countable

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let countable = new_definition
  `countable s <=> s <=_c (UNIV:num->bool)`;;
```

### Informal statement
A set $s$ is countable if and only if it is in bijection with a subset of the natural numbers.

Formally, $\text{countable}(s) \iff s \leq_c \text{UNIV}$, where:
- $s \leq_c \text{UNIV}$ means that $s$ is in bijection with some subset of the universal set of natural numbers
- $\text{UNIV}$ specifically refers to the set of all natural numbers (type `num->bool` in HOL Light)
- $\leq_c$ is the "has cardinality less than or equal to" relation

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
This definition formalizes the standard mathematical concept of countability - a set is countable if it can be put in one-to-one correspondence with either the set of natural numbers or a subset of it.

The definition uses the cardinal comparison operator ($\leq_c$) which was likely defined earlier in the HOL Light library. It captures both finite and countably infinite sets:
- Finite sets are countable because they can be put in bijection with finite subsets of natural numbers
- Countably infinite sets (like integers or rationals) are countable because they can be put in bijection with the natural numbers themselves

This definition is important as it establishes a foundation for cardinality arguments in set theory. The comment indicates this definition is being used as part of proving the non-denumerability of the continuum (i.e., uncountability of real numbers), which is a classical result in set theory.

### Dependencies
No explicit dependencies were provided, but the definition appears to rely on:
- Cardinal comparison operator ($\leq_c$) from the card.ml library
- The universal set (UNIV) of natural numbers (type num->bool)

### Porting notes
When porting to other proof assistants, consider:
1. How the target system represents cardinal comparisons ($\leq_c$ relation)
2. Whether the target system has a built-in notion of countability
3. How the universal set of natural numbers is represented in the target system

In some systems, you might need to explicitly define countability using injections or bijections with natural numbers rather than using a cardinal comparison.

---

## repeating

### Name of formal statement
repeating

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let repeating = new_definition
 `repeating = {s:num->bool | ?n. !m. m >= n ==> s m}`;;
```

### Informal statement
The set `repeating` is defined as:
$$\text{repeating} = \{s \subseteq \mathbb{N} \mid \exists n \in \mathbb{N}. \forall m \in \mathbb{N}. m \geq n \Rightarrow s(m)\}$$

This defines the set of all subsets $s$ of natural numbers where, from some point onwards, all larger natural numbers are included in $s$ (i.e., there exists some threshold $n$ such that every natural number $m \geq n$ belongs to $s$).

### Informal proof
This is a definition, so no proof is provided.

### Mathematical insight
This definition captures the notion of sets of natural numbers that eventually include all sufficiently large natural numbers. Specifically, it characterizes subsets of natural numbers that eventually stabilize to complete inclusion - meaning that after some point $n$, all larger natural numbers are in the set.

In terms of characteristic functions (where a set is represented by a function that maps elements to true/false indicating membership), these are precisely the functions that eventually become constantly true.

This concept is important in the study of countability and cardinality. As suggested by the comment, this definition is likely used to prove that the collection of all such sets is countable, unlike the collection of all subsets of natural numbers which is uncountable.

In the context of formal set theory, this definition provides a canonical example of a countably infinite collection of subsets of the natural numbers.

### Dependencies
None specified in the provided dependency list.

### Porting notes
When porting this definition:
- Be aware that in HOL Light, sets are represented as predicates (functions to bool)
- The notation `s m` means that `m` is a member of set `s`
- In other systems, you might need to explicitly use a membership relation or characteristic function depending on how sets are represented
- The quantifier ordering is important: "there exists some point after which all larger natural numbers are included in the set"

---

## BINARY_BOUND

### BINARY_BOUND

### Type of the formal statement
- theorem (proved with `prove`)

### Formal Content
```ocaml
let BINARY_BOUND = prove
(`!n. nsum(0..n) (\i. if b(i) then 2 EXP i else 0) < 2 EXP (n + 1)`,
  INDUCT_TAC THEN REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THENL
   [COND_CASES_TAC THEN REWRITE_TAC[ARITH]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[LE_0; EXP_ADD; EXP_1; EXP] THEN
  ARITH_TAC);;
```

### Informal statement
For any natural number $n$, the sum $\sum_{i=0}^{n} 2^i \cdot [b(i)]$ is strictly less than $2^{n+1}$, where $b(i)$ is a boolean function and $[b(i)]$ equals 1 if $b(i)$ is true and 0 if $b(i)$ is false.

In other words, if we consider a binary representation where the digit at position $i$ is either $2^i$ or $0$ depending on the boolean value $b(i)$, then the resulting sum is always strictly less than $2^{n+1}$.

### Informal proof
We prove this by induction on $n$.

**Base case ($n = 0$):**
- The sum for $n = 0$ is either $2^0 = 1$ (if $b(0)$ is true) or $0$ (if $b(0)$ is false)
- In either case, this value is less than $2^{0+1} = 2$

**Inductive step:**
- Assume the result holds for some $n$, so: $\sum_{i=0}^{n} 2^i \cdot [b(i)] < 2^{n+1}$
- We need to prove that $\sum_{i=0}^{n+1} 2^i \cdot [b(i)] < 2^{(n+1)+1} = 2^{n+2}$
- Using the definition of the sum over a range:
  $\sum_{i=0}^{n+1} 2^i \cdot [b(i)] = \sum_{i=0}^{n} 2^i \cdot [b(i)] + 2^{n+1} \cdot [b(n+1)]$
- By the induction hypothesis: $\sum_{i=0}^{n} 2^i \cdot [b(i)] < 2^{n+1}$
- If $b(n+1)$ is false, then $2^{n+1} \cdot [b(n+1)] = 0$ and clearly $\sum_{i=0}^{n+1} 2^i \cdot [b(i)] < 2^{n+2}$
- If $b(n+1)$ is true, then $2^{n+1} \cdot [b(n+1)] = 2^{n+1}$
- Therefore $\sum_{i=0}^{n+1} 2^i \cdot [b(i)] = \sum_{i=0}^{n} 2^i \cdot [b(i)] + 2^{n+1} < 2^{n+1} + 2^{n+1} = 2 \cdot 2^{n+1} = 2^{n+2}$

### Mathematical insight
This theorem establishes an important property of binary representations of numbers: the sum of powers of 2 up to $2^n$ (with some powers potentially omitted) is always less than $2^{n+1}$. 

This is essentially equivalent to stating that any natural number less than $2^{n+1}$ can be uniquely represented as a sum of distinct powers of 2, where each power is at most $2^n$. This is the fundamental principle behind binary representation of numbers.

The result is useful in binary arithmetic, computer science algorithms, and serves as a foundation for understanding binary encodings and their bounds.

### Dependencies
- The proof relies on basic arithmetic properties and the recursive definition of summation over ranges.

### Porting notes
This theorem should be relatively straightforward to port to other systems. The main aspects to consider are:
- The representation of the summation over ranges
- The handling of the conditional inside the summation
- The expression of the binary exponential function

Many systems have built-in libraries for these concepts that can be leveraged.

---

## BINARY_DIV_POW2

### Name of formal statement
BINARY_DIV_POW2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BINARY_DIV_POW2 = prove
 (`!n. (nsum(0..n) (\i. if b(i) then 2 EXP i else 0)) DIV (2 EXP (SUC n)) = 0`,
  SIMP_TAC[ADD1; DIV_LT; BINARY_BOUND]);;
```

### Informal statement
Let $b(i)$ be a binary function (i.e., a function that returns either true or false). For any natural number $n$, the following holds:

$$\left(\sum_{i=0}^{n} \left(\text{if}\ b(i)\ \text{then}\ 2^i\ \text{else}\ 0\right)\right) \div 2^{n+1} = 0$$

where $\div$ represents integer division.

### Informal proof
This theorem states that the sum of powers of 2 (up to $2^n$) selected according to a binary function $b(i)$ will always be less than $2^{n+1}$, thus giving 0 when divided by $2^{n+1}$.

The proof is straightforward:
- By applying `ADD1` to rewrite $(\text{SUC}\ n)$ as $n+1$
- Then using `DIV_LT` which states that if $a < b$ and $b > 0$, then $a \div b = 0$
- The theorem `BINARY_BOUND` establishes that $\sum_{i=0}^{n} \left(\text{if}\ b(i)\ \text{then}\ 2^i\ \text{else}\ 0\right) < 2^{n+1}$

Therefore, the division results in 0.

### Mathematical insight
This theorem demonstrates a fundamental property of binary (base-2) representations of numbers. It shows that any number represented by selecting powers of $2$ up to $2^n$ will always be strictly less than $2^{n+1}$. 

This result is important for binary arithmetic and can be interpreted as stating that a binary number with $n+1$ digits (from $2^0$ to $2^n$) is always less than the next power of 2 (namely $2^{n+1}$), and therefore dividing it by $2^{n+1}$ always gives 0.

This property is particularly useful in algorithms dealing with binary representations of numbers and binary arithmetic operations.

### Dependencies
- `ADD1`: Rewrites SUC n as n+1
- `DIV_LT`: States that if a < b and b > R 0, then a DIV b = 0
- `BINARY_BOUND`: States that the sum of selected powers of 2 up to n is bounded by $2^{n+1}$

---

## PLUS_MOD_REFL

### PLUS_MOD_REFL
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PLUS_MOD_REFL = prove
 (`!a b. ~(b = 0) ==> (a + b) MOD b = a MOD b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_EQ THEN MESON_TAC[MULT_CLAUSES]);;
```

### Informal statement
For all integers $a$ and $b$, if $b \neq 0$, then $(a + b) \bmod b = a \bmod b$.

### Informal proof
The proof proceeds as follows:

- We first apply the theorem `MOD_EQ` which states that if two numbers give the same remainder when divided by a non-zero $b$, then their modulo values are equal.
- For any integers $a$ and $b$ with $b \neq 0$, we have:
  - $(a + b) = a + 1 \cdot b$
  - This means $(a + b)$ and $a$ differ by a multiple of $b$
  - Therefore, by `MOD_EQ`, we have $(a + b) \bmod b = a \bmod b$
- The `MESON_TAC[MULT_CLAUSES]` step uses the basic multiplication properties to establish that $1 \cdot b = b$, which confirms that $a + b$ and $a$ differ by exactly $b$, which is a multiple of $b$.

### Mathematical insight
This theorem captures the fundamental property of modular arithmetic that adding the modulus to a number doesn't change its remainder when divided by that modulus. In other words, adding $b$ to any number results in a number that is congruent modulo $b$ to the original number.

This property is used frequently in number theory, cryptography, and computer algorithms dealing with modular arithmetic. It reflects the cyclic nature of the modulo operation and forms the basis for many more complex modular arithmetic identities.

### Dependencies
- `MOD_EQ`: A theorem that establishes when two numbers have the same modulo value
- `MULT_CLAUSES`: Basic properties of multiplication, including that $1 \cdot b = b$

### Porting notes
When implementing this in other proof assistants:
- Ensure that the modulo operation is defined in the same way as HOL Light (remainder after division)
- Some systems may have built-in lemmas for modular arithmetic that could simplify the proof
- In many systems, this could be proved by arithmetic decision procedures or simplifiers without needing an explicit proof

---

## BINARY_PLUS_DIV_POW2

### Name of formal statement
BINARY_PLUS_DIV_POW2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BINARY_PLUS_DIV_POW2 = prove
 (`!n. (nsum(0..n) (\i. if b(i) then 2 EXP i else 0) + 2 EXP (SUC n))
       DIV (2 EXP (SUC n)) = 1`,
  GEN_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `nsum(0..n) (\i. if b(i) then 2 EXP i else 0)` THEN
  ASM_REWRITE_TAC[BINARY_BOUND; ADD1] THEN
  REWRITE_TAC[ADD_AC; MULT_CLAUSES]);;
```

### Informal statement
For any natural number $n$, the following equation holds:
$$\frac{\sum_{i=0}^{n} (b(i) \cdot 2^i) + 2^{n+1}}{2^{n+1}} = 1$$

where $b(i)$ is a binary function (returning either 0 or 1), and $b(i) \cdot 2^i$ equals $2^i$ if $b(i)$ is true and 0 otherwise.

### Informal proof
The proof uses the division uniqueness theorem (`DIV_UNIQ`) to establish the result:

- Apply `DIV_UNIQ` to show that when dividing a sum by $2^{n+1}$, if the remainder is $\sum_{i=0}^{n} (b(i) \cdot 2^i)$ and the quotient is 1, then the equation holds.
- Establish that $\sum_{i=0}^{n} (b(i) \cdot 2^i) < 2^{n+1}$ using the `BINARY_BOUND` theorem, which ensures the remainder is valid.
- Use algebraic properties of addition (`ADD_AC`) and multiplication (`MULT_CLAUSES`) to simplify the expressions.
- The proof verifies that $\sum_{i=0}^{n} (b(i) \cdot 2^i) + 2^{n+1} = 1 \cdot 2^{n+1} + \sum_{i=0}^{n} (b(i) \cdot 2^i)$, confirming that the quotient is 1 with the specified remainder.

### Mathematical insight
This theorem establishes a fundamental property of binary representations: when adding $2^{n+1}$ to a binary number with digits up to position $n$, then dividing by $2^{n+1}$, the result is exactly 1. This corresponds to the intuition that adding $2^{n+1}$ "carries over" to the $(n+1)$-st bit position.

The result is particularly important in the context of binary arithmetic and can be used in proofs about binary representations, computer arithmetic, or formalization of algorithms involving powers of 2.

### Dependencies
- **Theorems:**
  - `DIV_UNIQ` - Division uniqueness theorem
  - `BINARY_BOUND` - Bound on binary representation sums
  - `ADD_AC` - Associativity and commutativity of addition
  - `MULT_CLAUSES` - Basic multiplication properties
  - `ADD1` - Properties of adding 1

### Porting notes
When porting this theorem:
- Ensure the target system has appropriate definitions for binary functions and summation over ranges.
- The proof relies on division uniqueness properties, so verify those are available in the target system.
- The binary representation bound (`BINARY_BOUND`) might need to be separately ported or proven.

---

## BINARY_UNIQUE_LEMMA

### Name of formal statement
BINARY_UNIQUE_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BINARY_UNIQUE_LEMMA = prove
 (`!n. nsum(0..n) (\i. if b(i) then 2 EXP i else 0) =
       nsum(0..n) (\i. if c(i) then 2 EXP i else 0)
       ==> !i. i <= n ==> (b(i) <=> c(i))`,
  INDUCT_TAC THEN REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THENL
   [SIMP_TAC[LE] THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH]);
    REWRITE_TAC[LE_0]] THEN
  REWRITE_TAC[LE] THEN REPEAT STRIP_TAC THENL
   [UNDISCH_THEN `i = SUC n` SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x DIV (2 EXP (SUC n))`) THEN
    REPEAT COND_CASES_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; BINARY_DIV_POW2; BINARY_PLUS_DIV_POW2] THEN
    REWRITE_TAC[ARITH_EQ];
    FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x MOD (2 EXP (SUC n))`) THEN
    REPEAT COND_CASES_TAC THEN
    SIMP_TAC[ADD_CLAUSES; BINARY_BOUND; MOD_LT; PLUS_MOD_REFL; EXP_EQ_0; ARITH;
             ADD1] THEN
    ASM_MESON_TAC[LE_REFL]]);;
```

### Informal statement
For all natural numbers $n$, if
$$\sum_{i=0}^{n} \begin{cases} 2^i & \text{if } b(i) \\ 0 & \text{otherwise} \end{cases} = \sum_{i=0}^{n} \begin{cases} 2^i & \text{if } c(i) \\ 0 & \text{otherwise} \end{cases}$$

then for all $i \leq n$, we have $b(i) \Leftrightarrow c(i)$.

This theorem states that if two binary representations (using functions $b$ and $c$ to indicate which bits are set) produce the same number, then the corresponding bits must be identical.

### Informal proof
The proof proceeds by induction on $n$.

**Base case** ($n = 0$):
- We need to show that if $b(0)$ and $c(0)$ give the same sum, then $b(0) \Leftrightarrow c(0)$.
- This is straightforward because the hypothesis simplifies to:
  - If $b(0)$ then $2^0 = 1$ else $0$ equals if $c(0)$ then $2^0 = 1$ else $0$
- By case analysis on $b(0)$ and $c(0)$, we can determine that $b(0) \Leftrightarrow c(0)$ must hold.

**Inductive case**:
- Assume the theorem holds for $n$.
- For $n+1$, we have:
  $$\sum_{i=0}^{n+1} \begin{cases} 2^i & \text{if } b(i) \\ 0 & \text{otherwise} \end{cases} = \sum_{i=0}^{n+1} \begin{cases} 2^i & \text{if } c(i) \\ 0 & \text{otherwise} \end{cases}$$
- We need to prove that $b(i) \Leftrightarrow c(i)$ for all $i \leq n+1$.
- The proof divides into two cases:
  1. For $i = n+1$:
     - Apply division by $2^{n+1}$ to both sides of the equation.
     - After division, the term with $i = n+1$ becomes either 1 or 0, and all lower-order terms become 0.
     - This isolates the $(n+1)$-th bit, showing $b(n+1) \Leftrightarrow c(n+1)$.
  
  2. For $i \leq n$:
     - Apply modulo $2^{n+1}$ to both sides of the equation.
     - This removes the influence of the $(n+1)$-th bit.
     - The resulting equation matches our induction hypothesis.
     - By the induction hypothesis, $b(i) \Leftrightarrow c(i)$ for all $i \leq n$.

Thus, $b(i) \Leftrightarrow c(i)$ for all $i \leq n+1$, completing the proof.

### Mathematical insight
This theorem establishes the uniqueness of binary representations of natural numbers. It demonstrates that a number can have only one binary representation when expressed as a sum of powers of 2, which is a fundamental property of positional number systems.

The proof cleverly isolates bits through division and modulo operations:
- Division by $2^{n+1}$ isolates the highest-order bit
- Modulo $2^{n+1}$ eliminates the highest-order bit to handle the lower-order bits

This theorem is particularly important in number theory and computer science, as it confirms that the binary representation of a number is canonical, which is essential for digital systems.

### Dependencies
#### Theorems
- `NSUM_CLAUSES_NUMSEG`: Provides recursive equations for numerical sums over ranges
- `BINARY_DIV_POW2`: Relates to division of binary numbers by powers of 2
- `BINARY_PLUS_DIV_POW2`: Relates to division of binary sums by powers of 2
- `BINARY_BOUND`: Provides bounds on binary representation values
- `MOD_LT`: Relates to modular arithmetic with strict inequalities
- `PLUS_MOD_REFL`: Relates to modular addition
- `EXP_EQ_0`: Conditions for when an exponential equals zero

### Porting notes
- This proof relies heavily on properties of binary representation, division, and modular arithmetic.
- When porting, ensure that the target system has equivalent theorems about binary arithmetic, particularly division and modulo by powers of 2.
- The proof technique uses arithmetic manipulations (division and modulo) to isolate specific bits, which may need different tactics in other systems.
- In systems with native binary representations, there might be more direct ways to express the result.

---

## COUNTABLE_REPEATING

### Name of formal statement
COUNTABLE_REPEATING

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COUNTABLE_REPEATING = prove
 (`countable repeating`,
  REWRITE_TAC[countable] THEN
  TRANS_TAC CARD_LE_TRANS `(UNIV:num->bool) *_c (UNIV:num->bool)` THEN
  CONJ_TAC THENL
    [ALL_TAC;
     MATCH_MP_TAC CARD_EQ_IMP_LE THEN REWRITE_TAC[CARD_SQUARE_NUM]] THEN
  REWRITE_TAC[le_c] THEN EXISTS_TAC
   `\s:num->bool. let n = minimal n. !m. m >= n ==> s m in
                  n,nsum(0..n) (\i. if s(i) then 2 EXP i else 0)` THEN
  REWRITE_TAC[repeating; IN_ELIM_THM] THEN CONJ_TAC THENL
   [GEN_TAC THEN LET_TAC THEN REWRITE_TAC[mul_c; IN_ELIM_THM; IN_UNIV] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:num->bool`; `t:num->bool`] THEN
  ONCE_REWRITE_TAC[MINIMAL] THEN
  ABBREV_TAC `k = minimal n. !m. m >= n ==> s m` THEN
  ABBREV_TAC `l = minimal n. !m. m >= n ==> t m` THEN
  ASM_REWRITE_TAC[LET_DEF; LET_END_DEF; PAIR_EQ] THEN
  REPEAT(POP_ASSUM(K ALL_TAC)) THEN
  ASM_CASES_TAC `l:num = k` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[FUN_EQ_THM; GE] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP BINARY_UNIQUE_LEMMA) THEN
  ASM_MESON_TAC[LE_CASES]);;
```

### Informal statement
The set of all repeating sequences of booleans is countable.

Formally, the theorem states that the set of all repeating boolean sequences (where a sequence is considered repeating if it eventually becomes constant) is countably infinite, meaning there exists an injection from this set into the natural numbers.

### Informal proof
We prove that the set of repeating boolean sequences is countable by showing it can be injected into the natural numbers.

* First, we use the definition of countability as $\text{repeating} \leq_c \mathbb{N}$, where $\leq_c$ denotes "has cardinality less than or equal to".

* We establish this by using transitivity of the cardinality relation with $\mathbb{N} \times \mathbb{N}$ as an intermediate set:
  $\text{repeating} \leq_c \mathbb{N} \times \mathbb{N} \leq_c \mathbb{N}$

* For the second inequality, we use the fact that $\mathbb{N} \times \mathbb{N} =_c \mathbb{N}$, meaning the cartesian product of natural numbers has the same cardinality as the natural numbers themselves (from `CARD_SQUARE_NUM`).

* For the first inequality, we construct an explicit injection from repeating sequences to $\mathbb{N} \times \mathbb{N}$:
  - For any repeating sequence $s$, let $n$ be the minimal index such that for all $m \geq n$, $s(m)$ is constant.
  - Map $s$ to the pair $(n, \sum_{i=0}^{n} 2^i \cdot [s(i)])$ where $[s(i)] = 1$ if $s(i)$ is true and $0$ otherwise.

* To prove this function is injective, assume two repeating sequences $s$ and $t$ map to the same pair.
  - Let $k$ be the minimal index where $s$ becomes constant
  - Let $l$ be the minimal index where $t$ becomes constant
  - If they map to the same pair, then $k = l$ and the sum is the same
  - Using the uniqueness of binary representation (from `BINARY_UNIQUE_LEMMA`), we can conclude that $s = t$.

Therefore, repeating sequences can be injected into $\mathbb{N}$, making them countable.

### Mathematical insight
This theorem shows that despite being an infinite set, the set of repeating boolean sequences is only countably infinite. The key insight is finding an injection that encodes each repeating sequence using two natural numbers: the point at which the sequence stabilizes and a number representing the finite initial segment.

The construction cleverly handles the infinite nature of sequences by leveraging their eventually constant behavior. This result is important in computability theory and set theory, as it helps classify different infinite sets and has implications for what can be effectively enumerated or computed.

### Dependencies
- Theorems:
  - `CARD_LE_TRANS`: Transitivity of the cardinality relation
  - `CARD_EQ_IMP_LE`: Equality of cardinality implies less-than-or-equal cardinality
  - `CARD_SQUARE_NUM`: The cartesian product of natural numbers has the same cardinality as natural numbers
  - `BINARY_UNIQUE_LEMMA`: Uniqueness of binary representation (referenced but not listed in dependencies)

- Definitions:
  - `mul_c`: Definition of the cartesian product for sets
  - `countable`: Definition of countability (not explicitly shown)
  - `repeating`: Definition of repeating sequences (not explicitly shown)
  - `le_c`: Definition of cardinality comparison (not explicitly shown)

### Porting notes
When porting this theorem:
1. Ensure the target system has equivalent definitions for countability and repeating sequences
2. The injection function uses a minimality operator (`minimal`), which may need special attention
3. The binary representation lemma (`BINARY_UNIQUE_LEMMA`) will need an equivalent in the target system
4. The proof relies on the Cantor pairing function (`NUMPAIR`) to establish that $\mathbb{N} \times \mathbb{N} =_c \mathbb{N}$, which might require explicit construction in other systems

---

## canonical

### Name of formal statement
canonical

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let canonical = new_definition
 `canonical = {s:num->bool | !n. ?m. m >= n /\ ~(s m)}`;;
```

### Informal statement
The definition `canonical` represents the set of all sequences $s : \mathbb{N} \to \mathbb{B}$ (where $\mathbb{B}$ is the Boolean domain) such that for every natural number $n$, there exists a natural number $m \geq n$ where $s(m)$ is false.

In set notation:
$$\text{canonical} = \{s : \mathbb{N} \to \mathbb{B} \mid \forall n \in \mathbb{N}, \exists m \in \mathbb{N}, m \geq n \land \lnot s(m)\}$$

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
This definition captures the concept of a "canonical" sequence of boolean values (represented as a set of natural numbers where membership indicates "true"). A sequence is canonical if it has infinitely many "false" values (or equivalently, if the set excludes infinitely many natural numbers).

The term "canonical" is used because these sequences are often used in diagonal arguments to prove uncountability results. These sequences cannot be "trapped" into having all true values after some point, which makes them useful in various diagonalization constructions.

This definition is particularly important in the context of proving that certain sets are uncountable, such as the set of all infinite binary sequences. The comment mentions "Canonical digits and their uncountability," suggesting this definition will be used in an uncountability proof, likely using Cantor's diagonal argument or a similar approach.

### Dependencies
No explicit dependencies in the provided information.

### Porting notes
When porting this definition to other proof assistants:
- Ensure the target system can handle sets of functions or predicates
- In type-theoretic systems like Coq or Lean, this might be represented as a predicate on functions from natural numbers to booleans
- In systems without built-in boolean types, you might need to use `{0,1}` or define a boolean type

---

## UNCOUNTABLE_CANONICAL

### Name of formal statement
UNCOUNTABLE_CANONICAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let UNCOUNTABLE_CANONICAL = prove
 (`~countable canonical`,
  REWRITE_TAC[countable] THEN STRIP_TAC THEN
  MP_TAC (INST_TYPE [`:num`,`:A`] CANTOR_THM_UNIV) THEN
  REWRITE_TAC[CARD_NOT_LT] THEN
  MP_TAC(ISPECL [`canonical`; `repeating`] CARD_DISJOINT_UNION) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_ELIM_THM;
                canonical; repeating; GE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `canonical UNION repeating = UNIV` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM;
                canonical; repeating; GE; IN_UNIV] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN TRANS_TAC CARD_LE_TRANS `canonical +_c repeating` THEN
  ASM_SIMP_TAC[CARD_EQ_IMP_LE] THEN
  TRANS_TAC CARD_LE_TRANS `(UNIV:num->bool) +_c (UNIV:num->bool)` THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[countable; COUNTABLE_REPEATING; CARD_LE_ADD];
    MATCH_MP_TAC CARD_ADD_ABSORB_LE THEN
    REWRITE_TAC[num_INFINITE; CARD_LE_REFL]]);;
```

### Informal statement
The set of canonical real numbers is uncountable.

Here, a real number is considered canonical if it has no repeating decimal expansion.

### Informal proof
We prove that the set of canonical real numbers is not countable by contradiction.

* Assume that the set of canonical real numbers is countable.
* From Cantor's theorem, we know that $\text{UNIV}:\text{num} \to \text{bool} <_c \text{UNIV}:(\text{num} \to \text{bool}) \to \text{bool}$, where $<_c$ denotes "has strictly smaller cardinality than".
* Using the contrapositive of this relation (`CARD_NOT_LT`), we get that the power set of natural numbers is not smaller or equal in cardinality to the natural numbers.
* The set of real numbers can be partitioned into two disjoint sets: canonical numbers and repeating numbers.
* By the disjoint union property (`CARD_DISJOINT_UNION`), we have $\text{canonical} \cup \text{repeating} =_c \text{canonical} +_c \text{repeating}$.
* We know that $\text{canonical} \cup \text{repeating} = \text{UNIV}$ (the set of all real numbers).
* By transitivity of cardinality relations (`CARD_LE_TRANS`), we have:
  * $\text{UNIV} =_c \text{canonical} +_c \text{repeating}$
  * Since both canonical and repeating numbers are assumed countable, we have $\text{canonical} +_c \text{repeating} \leq_c \aleph_0 +_c \aleph_0$, where $\aleph_0$ represents the cardinality of natural numbers.
  * For infinite sets such as natural numbers, we have $\aleph_0 +_c \aleph_0 \leq_c \aleph_0$ (from `CARD_ADD_ABSORB_LE`).
  * This means $\text{UNIV} \leq_c \aleph_0$, which contradicts Cantor's theorem.
* Therefore, the set of canonical real numbers cannot be countable.

### Mathematical insight
This theorem establishes that the set of real numbers with non-repeating decimal expansions is uncountable. It uses Cantor's theorem and properties of cardinal arithmetic to reach this conclusion.

The key insight is that:
1. The set of all real numbers can be partitioned into those with repeating decimal expansions (which are countable) and those with non-repeating expansions (canonical).
2. Since the set of all real numbers is uncountable (by Cantor's theorem), and the union of canonical and repeating numbers equals the set of all reals, the set of canonical numbers must be uncountable.

This result is important in understanding the cardinality of different subsets of real numbers and highlights the fact that "most" real numbers have non-repeating decimal expansions.

### Dependencies
#### Theorems
- `CARD_LE_REFL`: For any set s, s ≤ₖ s (reflexivity of cardinal comparison)
- `CARD_LE_TRANS`: If s ≤ₖ t and t ≤ₖ u, then s ≤ₖ u (transitivity of cardinal comparison)
- `CARD_EQ_IMP_LE`: If s =ₖ t, then s ≤ₖ t
- `CARD_NOT_LT`: ~(s <ₖ t) ⟺ t ≤ₖ s
- `CARD_LE_ADD`: If s ≤ₖ s' and t ≤ₖ t', then s +ₖ t ≤ₖ s' +ₖ t'
- `CARD_DISJOINT_UNION`: If s ∩ t = ∅, then s ∪ t =ₖ s +ₖ t
- `CARD_ADD_ABSORB_LE`: If t is infinite and s ≤ₖ t, then s +ₖ t ≤ₖ t
- `CANTOR_THM_UNIV`: UNIV:A->bool <ₖ UNIV:(A->bool)->bool (Universe of type A has strictly smaller cardinality than its power set)

#### Definitions
- `countable`: A set is countable if its cardinality is less than or equal to that of natural numbers
- `canonical`: Real numbers with non-repeating decimal expansions
- `repeating`: Real numbers with repeating decimal expansions

### Porting notes
When porting this theorem:
1. Ensure that the definitions of canonical and repeating real numbers are properly established in your target system.
2. Careful attention should be paid to how cardinal arithmetic is formalized in your system.
3. Cantor's theorem is fundamental to this proof, so make sure it's available or can be proved in your target system.
4. The proof uses several properties of cardinal arithmetic with infinite sets, which may need different approaches depending on the foundational setup of your target system.

---

## SUMINF_INJ_LEMMA

### Name of formal statement
SUMINF_INJ_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUMINF_INJ_LEMMA = prove
 (`!s t n. ~(s n) /\ t n /\
           (!m. m < n ==> (s(m) <=> t(m))) /\
           (!n. ?m. m >= n /\ ~(s m))
           ==> suminf(\n. if s n then inv (&2 pow n) else &0)
                < suminf(\n. if t n then inv (&2 pow n) else &0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `sum(0,n+1) (\n. if t n then inv (&2 pow n) else &0)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SEQ_LE THEN MAP_EVERY EXISTS_TAC
     [`\k:num. sum(0,n+1) (\n. if t n then inv (&2 pow n) else &0)`;
      `\n:num. sum(0,n) (\n. if t n then inv (&2 pow n) else &0)`] THEN
    REWRITE_TAC[SEQ_CONST; GSYM sums; SUMS_BINSEQUENCE] THEN
    EXISTS_TAC `n + 1` THEN X_GEN_TAC `m:num` THEN
    REWRITE_TAC[GE; LE_EXISTS] THEN DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
    REWRITE_TAC[GSYM ADD1] THEN
    REWRITE_TAC[GSYM SUM_SPLIT; REAL_LE_ADDR; SUM_BINSEQUENCE_LBOUND]] THEN
  ASM_REWRITE_TAC[GSYM SUM_SPLIT; SUM_1; ADD_CLAUSES] THEN
  UNDISCH_THEN `!n:num. ?m. m >= n /\ ~s m` (MP_TAC o SPEC `n + 1`) THEN
  REWRITE_TAC[GE] THEN DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC
    `sum(0,m) (\n. if s n then inv (&2 pow n) else &0) + inv(&2 pow m)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SEQ_LE THEN MAP_EVERY EXISTS_TAC
     [`\n:num. sum(0,n) (\n. if s n then inv (&2 pow n) else &0)`;
      `\k:num. sum(0,m) (\n. if s n then inv(&2 pow n) else &0) +
               inv(&2 pow m)`] THEN
    REWRITE_TAC[SEQ_CONST; GSYM sums; SUMS_BINSEQUENCE] THEN
    EXISTS_TAC `m:num` THEN REWRITE_TAC[GE; LE_REFL] THEN
    X_GEN_TAC `r:num` THEN REWRITE_TAC[LE_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:num` SUBST_ALL_TAC) THEN
    REWRITE_TAC[GSYM SUM_SPLIT; REAL_LE_LADD; ADD_CLAUSES] THEN
    DISJ_CASES_THEN SUBST_ALL_TAC (ARITH_RULE `p = 0 \/ p = 1 + PRE p`) THEN
    SIMP_TAC[sum; REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS] THEN
    ONCE_REWRITE_TAC[GSYM SUM_SPLIT] THEN
    ASM_REWRITE_TAC[SUM_1; REAL_ADD_LID] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 / &2 pow (m + 1)` THEN
    REWRITE_TAC[SUM_BINSEQUENCE_UBOUND_LE] THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LE_EXISTS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num` SUBST_ALL_TAC) THEN
  REWRITE_TAC[GSYM SUM_SPLIT] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; SUM_1; REAL_ADD_RID] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b /\ c < e - d ==> (a + c) + d < b + e`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[LE_0; ADD_CLAUSES]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `&2 / &2 pow (n + 1) - &2 / &2 pow ((n + 1) + r)` THEN
  REWRITE_TAC[SUM_BINSEQUENCE_UBOUND_SHARP] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b /\ d < c ==> a - c < b - d`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC(REAL_FIELD `&0 < inv(x) ==> inv(x) < &2 / x`) THEN
    SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH]]);;
```

### Informal statement
Let $s$ and $t$ be predicates on natural numbers, and let $n$ be a natural number such that:
1. $\lnot s(n)$ and $t(n)$ (i.e., $s(n)$ is false and $t(n)$ is true)
2. $\forall m < n, s(m) \Leftrightarrow t(m)$ (i.e., $s$ and $t$ agree for all indices less than $n$)
3. $\forall n, \exists m \geq n, \lnot s(m)$ (i.e., for any index, there exists a larger or equal index where $s$ is false)

Then:
$$\sum_{i=0}^{\infty} \left\{\begin{array}{ll} \frac{1}{2^i} & \text{if } s(i) \\ 0 & \text{otherwise} \end{array}\right\} < \sum_{i=0}^{\infty} \left\{\begin{array}{ll} \frac{1}{2^i} & \text{if } t(i) \\ 0 & \text{otherwise} \end{array}\right\}$$

### Informal proof
We want to show that the infinite sum for sequence $s$ is strictly less than the infinite sum for sequence $t$, where $s$ and $t$ differ at position $n$ (with $\lnot s(n)$ and $t(n)$) but agree below $n$.

The proof proceeds as follows:

* We establish a transitive relation via the finite sum:
  $$\text{suminf}(\lambda n. \text{if } s(n) \text{ then } \frac{1}{2^n} \text{ else } 0) < \sum_{i=0}^{n} (\text{if } t(i) \text{ then } \frac{1}{2^i} \text{ else } 0)$$

* The second inequality ($\sum_{i=0}^{n} (\ldots) \leq \text{suminf}(\ldots)$) is established by using `SEQ_LE` with constant sequences. This follows from the fact that the finite sum is always less than or equal to the infinite sum, as proven in `SUMS_BINSEQUENCE`.

* For the first inequality, we need to show:
  $$\text{suminf}(\lambda n. \text{if } s(n) \text{ then } \frac{1}{2^n} \text{ else } 0) < \sum_{i=0}^{n} (\text{if } t(i) \text{ then } \frac{1}{2^i} \text{ else } 0)$$

* We decompose the sums to focus on the difference at position $n$. Since $s$ and $t$ agree for $i < n$, and $s(n) = \text{false}, t(n) = \text{true}$, the difference at position $n$ is exactly $\frac{1}{2^n}$.

* We use the third hypothesis to find an $m \geq n+1$ such that $\lnot s(m)$.

* We establish an upper bound for the infinite sum of $s$ by showing:
  $$\text{suminf}(\lambda n. \text{if } s(n) \text{ then } \frac{1}{2^n} \text{ else } 0) < \sum_{i=0}^{m-1} (\text{if } s(i) \text{ then } \frac{1}{2^i} \text{ else } 0) + \frac{1}{2^m}$$

* Through algebraic manipulation and using the properties of the sums of binary sequences (from `SUM_BINSEQUENCE_UBOUND_SHARP`), we show that the difference between the sums is at least:
  $$\frac{1}{2^n} - \left(\frac{2}{2^{n+1}} - \frac{2}{2^{n+1+r}}\right) > 0$$

* This confirms that the infinite sum for $s$ is strictly less than the infinite sum for $t$.

### Mathematical insight
This lemma establishes a rigorous connection between binary representations and real numbers. The summation $\sum_{i=0}^{\infty} \frac{s(i)}{2^i}$ can be viewed as converting a binary sequence into its corresponding real number in $[0,1]$.

The key insight is that changing a 0 to a 1 at position $n$ (while keeping earlier digits the same) produces a strictly larger number. This is exactly what happens when comparing $s$ and $t$: they match at all positions below $n$, but $t$ has a 1 where $s$ has a 0 at position $n$.

The third condition (that $s$ has infinitely many zeros) is needed to ensure proper handling of the binary representation, avoiding issues with the non-uniqueness of binary representations (like 0.1000... = 0.0111...).

This lemma is fundamental for establishing an injection from binary sequences into real numbers, which has applications in various areas including computability theory and measure theory.

### Dependencies
- **Theorems**:
  - `REAL_LTE_TRANS`: Transitivity of < and <= for reals
  - `REAL_LE_TRANS`: Transitivity of <= for reals
  - `REAL_LE_LADD`: Addition preserves <= for reals
  - `REAL_POS`: Natural numbers are non-negative as reals
  - `sum`: Properties of finite summation
  - `SUM_EQ`: Equality of sums when components are equal
  - `SUM_SPLIT`: Splitting sums at a given index
  - `SEQ_CONST`: Constant sequences converge to their value
  - `SEQ_LE`: Sequence ordering implies limit ordering

- **Definitions**:
  - `suminf`: Infinite sum defined using the Hilbert epsilon operator

- **Background lemmas**:
  - `SUM_BINSEQUENCE_LBOUND`: Lower bound for binary sequence sums
  - `SUM_BINSEQUENCE_UBOUND_SHARP`: Upper bound for binary sequence sums
  - `SUM_BINSEQUENCE_UBOUND_LE`: Simplified upper bound for binary sequence sums
  - `SUMS_BINSEQUENCE`: Convergence of binary sequence sums

### Porting notes
When porting this to other systems:
1. The binary representation of real numbers might be handled differently in other systems.
2. The use of the Hilbert epsilon operator in the definition of `suminf` might require alternative formulations in systems that don't support it directly.
3. The various lemmas about bounds on binary sequence sums may need to be ported first or developed within the target system.
4. The theorem uses a mix of sequence properties (convergence, ordering) with specific properties of binary representations, so care should be taken to ensure all aspects are correctly captured.

---

## UNCOUNTABLE_REALS

### Name of formal statement
UNCOUNTABLE_REALS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let UNCOUNTABLE_REALS = prove
 (`~countable(UNIV:real->bool)`,
  MP_TAC UNCOUNTABLE_CANONICAL THEN REWRITE_TAC[CONTRAPOS_THM] THEN
  REWRITE_TAC[countable] THEN DISCH_TAC THEN
  TRANS_TAC CARD_LE_TRANS `UNIV:real->bool` THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM(K ALL_TAC) THEN REWRITE_TAC[le_c] THEN
  EXISTS_TAC `\s. suminf(\n. if s(n) then inv(&2 pow n) else &0)` THEN
  REWRITE_TAC[IN_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`s:num->bool`; `t:num->bool`] THEN
  REWRITE_TAC[canonical; IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN
  GEN_REWRITE_TAC I [MESON[] `(!x. P x) <=> ~(?x. ~P x)`] THEN
  ONCE_REWRITE_TAC[MINIMAL] THEN
  ABBREV_TAC `n = minimal x. ~(s x <=> t x)` THEN
  FIRST_X_ASSUM(K ALL_TAC o check (is_var o rhs o concl)) THEN
  ASM_CASES_TAC `(t:num->bool) n` THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SYM) THENL
   [MATCH_MP_TAC(REAL_ARITH `b < a ==> a = b ==> F`);
    MATCH_MP_TAC(REAL_ARITH `a < b ==> a = b ==> F`)] THEN
  MATCH_MP_TAC SUMINF_INJ_LEMMA THEN ASM_MESON_TAC[]);;
```

### Informal statement
The set of all real numbers is uncountable.

In formal notation: $\neg \text{countable}(\text{UNIV}:\text{real}\to\text{bool})$, where $\text{UNIV}$ represents the universal set of real numbers.

### Informal proof
The proof proceeds by contradiction using Cantor's diagonal argument:

1. We start with the theorem `UNCOUNTABLE_CANONICAL` which states that the canonical interval $[0,1]$ is uncountable, and apply contraposition to our goal.

2. Assuming that the set of all real numbers is countable, we aim to derive a contradiction.

3. By transitivity of cardinality (using `CARD_LE_TRANS`), if we can establish that the canonical interval is less than or equal in cardinality to all reals (which is true), and all reals are countable (our assumption), then the canonical interval would be countable.

4. We define an injective function from sets of natural numbers to real numbers:
   $f(s) = \sum_{n=0}^{\infty} \begin{cases} \frac{1}{2^n} & \text{if}\ s(n) \\ 0 & \text{otherwise} \end{cases}$

5. We then show that this function is injective:
   - For any two different sets of natural numbers $s$ and $t$, let $n$ be the minimal index where they differ
   - Without loss of generality, assume $s(n)$ and $\neg t(n)$
   - This implies that $f(s)$ and $f(t)$ differ by at least $\frac{1}{2^n}$, making them distinct
   
6. The existence of this injection contradicts the uncountability of the canonical interval, completing the proof.

### Mathematical insight
This theorem establishes the fundamental result in set theory that the real numbers are uncountable. It's a pivotal mathematical fact with far-reaching consequences in analysis, set theory, and foundations of mathematics.

The proof uses the binary representation of real numbers and Cantor's diagonal argument, showing that any attempted enumeration of the reals must be incomplete. This uncountability result creates a hierarchy of infinite sets and demonstrates that not all infinities are the same size.

The injection used in the proof maps each set of natural numbers to a unique real number in the interval $[0,1]$ by constructing a binary decimal, which effectively demonstrates that the powerset of natural numbers has the same cardinality as the real numbers.

### Dependencies
- Theorems:
  - `UNCOUNTABLE_CANONICAL`: States that the canonical interval $[0,1]$ is uncountable
  - `CONTRAPOS_THM`: The contrapositive theorem
  - `CARD_LE_TRANS`: Transitivity of cardinality relation
  - `SUMINF_INJ_LEMMA`: A lemma about the injectivity of infinite sums
  - Various theorems about reals and cardinality

- Definitions:
  - `countable`: Definition of countability
  - `le_c`: Less than or equal relation for cardinality
  - `suminf`: Infinite sum definition
  - `minimal`: The minimal element satisfying a condition

### Porting notes
When porting this theorem:
1. Ensure that the target system has a well-defined notion of countability and cardinality
2. The proof relies on binary representations of reals, which should be handled appropriately in the target system
3. The infinite sum notation might need to be adapted to the target system's conventions
4. Cantor's diagonal argument is implemented differently across systems, so adjustments may be needed

---

