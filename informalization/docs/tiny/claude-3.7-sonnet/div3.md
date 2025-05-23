# div3.ml

## Overview

Number of statements: 3

This file formalizes the divisibility by 3 rule, which states that a natural number is divisible by 3 if and only if the sum of its digits is divisible by 3. It proves the rule's correctness in a formal setting, likely building on prime number theory given its imports of prime.ml and pocklington.ml. The file's implementation likely includes definitions and theorems for digital sums and their relationship to divisibility properties.

## EXP_10_CONG_3

### Name of formal statement
EXP_10_CONG_3

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EXP_10_CONG_3 = prove
 (`!n. (10 EXP n == 1) (mod 3)`,
  INDUCT_TAC THEN REWRITE_TAC[EXP; CONG_REFL] THEN
  MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC `10 * 1` THEN CONJ_TAC THEN
  ASM_SIMP_TAC[CONG_MULT; CONG_REFL] THEN
  SIMP_TAC[CONG; ARITH] THEN CONV_TAC NUM_REDUCE_CONV);;
```

### Informal statement
For all natural numbers $n$, we have $10^n \equiv 1 \pmod{3}$.

### Informal proof
We prove this by induction on $n$:

* Base case ($n = 0$): 
  $10^0 = 1 \equiv 1 \pmod{3}$, which is trivially true.

* Inductive step: 
  Assume that $10^n \equiv 1 \pmod{3}$ for some $n$.
  We need to prove that $10^{n+1} \equiv 1 \pmod{3}$.
  
  By definition of exponentiation, $10^{n+1} = 10 \cdot 10^n$.
  
  By the inductive hypothesis, $10^n \equiv 1 \pmod{3}$.
  
  Using the congruence property for multiplication (CONG_MULT), we have:
  $10 \cdot 10^n \equiv 10 \cdot 1 \pmod{3}$.
  
  Now $10 \cdot 1 = 10 \equiv 1 \pmod{3}$ since $10 = 9 + 1$ and $9 \equiv 0 \pmod{3}$.
  
  By transitivity of congruence, we conclude that $10^{n+1} \equiv 1 \pmod{3}$.

### Mathematical insight
This theorem establishes that powers of 10 always leave remainder 1 when divided by 3. This is a basic result in modular arithmetic that has applications in number theory and is particularly useful in divisibility tests. This property follows from the fact that $10 \equiv 1 \pmod{3}$, and therefore by the properties of modular exponentiation, any power of 10 will also be congruent to 1 modulo 3.

### Dependencies
#### Theorems
- `CONG_MULT`: If $x \equiv x' \pmod{n}$ and $y \equiv y' \pmod{n}$, then $x \cdot y \equiv x' \cdot y' \pmod{n}$
- `CONG_REFL`: Reflexive property of congruence: $x \equiv x \pmod{n}$
- `CONG_TRANS`: Transitive property of congruence: If $x \equiv y \pmod{n}$ and $y \equiv z \pmod{n}$, then $x \equiv z \pmod{n}$
- `EXP`: Definition of exponentiation for natural numbers

### Porting notes
When porting this theorem:
1. Ensure that your system has appropriate definitions for modular congruence and exponentiation.
2. The proof relies on basic properties of modular arithmetic (reflexivity, transitivity, and congruence with respect to multiplication).
3. In some proof assistants, you might need to handle the base case and inductive step separately and more explicitly.

---

## SUM_CONG_3

### Name of formal statement
SUM_CONG_3

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_CONG_3 = prove
 (`!d n. (nsum(0..n) (\i. 10 EXP i * d(i)) == nsum(0..n) (\i. d i)) (mod 3)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THENL
   [REWRITE_TAC[EXP; MULT_CLAUSES; CONG_REFL]; ALL_TAC] THEN
  REWRITE_TAC[LE_0] THEN MATCH_MP_TAC CONG_ADD THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV) [ARITH_RULE `d = 1 * d`] THEN
  MATCH_MP_TAC CONG_MULT THEN REWRITE_TAC[CONG_REFL; EXP_10_CONG_3]);;
```

### Informal statement
For any function $d$ and any natural number $n$, the sum $\sum_{i=0}^{n} 10^i \cdot d(i)$ is congruent to $\sum_{i=0}^{n} d(i)$ modulo 3.

Formally, $\sum_{i=0}^{n} 10^i \cdot d(i) \equiv \sum_{i=0}^{n} d(i) \pmod{3}$.

### Informal proof
We prove this theorem by induction on $n$.

**Base case** ($n = 0$): 
- We need to show $10^0 \cdot d(0) \equiv d(0) \pmod{3}$
- Since $10^0 = 1$, we have $1 \cdot d(0) = d(0)$
- Therefore, $10^0 \cdot d(0) \equiv d(0) \pmod{3}$ by reflexivity of congruence

**Induction step**:
- Assume the statement holds for some $n$: $\sum_{i=0}^{n} 10^i \cdot d(i) \equiv \sum_{i=0}^{n} d(i) \pmod{3}$
- We need to prove it for $n+1$: $\sum_{i=0}^{n+1} 10^i \cdot d(i) \equiv \sum_{i=0}^{n+1} d(i) \pmod{3}$
- Using the definition of summation: 
  $\sum_{i=0}^{n+1} 10^i \cdot d(i) = \sum_{i=0}^{n} 10^i \cdot d(i) + 10^{n+1} \cdot d(n+1)$
  $\sum_{i=0}^{n+1} d(i) = \sum_{i=0}^{n} d(i) + d(n+1)$
- By the induction hypothesis, $\sum_{i=0}^{n} 10^i \cdot d(i) \equiv \sum_{i=0}^{n} d(i) \pmod{3}$
- We know that $10^{n+1} \equiv 1 \pmod{3}$ (using the theorem `EXP_10_CONG_3`)
- Therefore $10^{n+1} \cdot d(n+1) \equiv 1 \cdot d(n+1) = d(n+1) \pmod{3}$ by the congruence of multiplication (`CONG_MULT`)
- By the congruence of addition (`CONG_ADD`), we can add these congruences to get:
  $\sum_{i=0}^{n} 10^i \cdot d(i) + 10^{n+1} \cdot d(n+1) \equiv \sum_{i=0}^{n} d(i) + d(n+1) \pmod{3}$
- Which gives us $\sum_{i=0}^{n+1} 10^i \cdot d(i) \equiv \sum_{i=0}^{n+1} d(i) \pmod{3}$ as required.

### Mathematical insight
This theorem establishes that the sum of digits of a number in base 10 gives the same remainder when divided by 3 as the number itself. This is a well-known divisibility rule for 3: "a number is divisible by 3 if and only if the sum of its digits is divisible by 3."

The proof exploits the fact that $10^i \equiv 1 \pmod{3}$ for all $i \geq 0$. This is because $10 \equiv 1 \pmod{3}$, and raising both sides to the power of $i$ preserves the congruence.

This result is foundational for number theory and is one of the standard divisibility tests taught in elementary mathematics.

### Dependencies
- Theorems:
  - `CONG_MULT`: If $x \equiv x' \pmod{n}$ and $y \equiv y' \pmod{n}$, then $x \cdot y \equiv x' \cdot y' \pmod{n}$
  - `CONG_ADD` (implied): If $a \equiv b \pmod{n}$ and $c \equiv d \pmod{n}$, then $a + c \equiv b + d \pmod{n}$  
  - `CONG_REFL` (implied): $a \equiv a \pmod{n}$ (reflexivity of congruence)
  - `EXP_10_CONG_3` (implied): $10^n \equiv 1 \pmod{3}$ for all natural numbers $n$
  - `NSUM_CLAUSES_NUMSEG` (implied): Definition/properties of summation over numeric ranges
  - `ARITH_RULE` (implied): A rule for arithmetic simplification

### Porting notes
When porting this theorem:
- Ensure that the underlying congruence relation is properly defined in your target system
- The proof relies on the fact that $10 \equiv 1 \pmod{3}$, which might need to be established first
- The summation notation might differ between systems; make sure to use the appropriate summation operation
- This is a specific case of a more general property about digit sums and modular arithmetic

---

## DIVISIBILITY_BY_3

### Name of formal statement
DIVISIBILITY_BY_3

### Type of formal statement
theorem

### Formal Content
```ocaml
let DIVISIBILITY_BY_3 = prove
 (`3 divides (nsum(0..n) (\i. 10 EXP i * d(i))) <=>
   3 divides (nsum(0..n) (\i. d i))`,
  MATCH_MP_TAC CONG_DIVIDES THEN REWRITE_TAC[SUM_CONG_3]);;
```

### Informal statement
For any natural number $n$ and function $d$ mapping natural numbers to natural numbers, we have:

$3$ divides $\sum_{i=0}^{n} 10^i \cdot d(i)$ if and only if $3$ divides $\sum_{i=0}^{n} d(i)$

This theorem states that a number is divisible by 3 if and only if the sum of its decimal digits is divisible by 3.

### Informal proof
The proof uses the fact that $10 \equiv 1 \pmod{3}$, which means that $10^i \equiv 1 \pmod{3}$ for all $i \geq 0$.

1. Apply the theorem `CONG_DIVIDES` which states that if $x \equiv y \pmod{n}$, then $n$ divides $x$ if and only if $n$ divides $y$.
2. Use `SUM_CONG_3` to establish that $\sum_{i=0}^{n} 10^i \cdot d(i) \equiv \sum_{i=0}^{n} d(i) \pmod{3}$.
3. The result follows immediately by combining these facts.

### Mathematical insight
This theorem formalizes the familiar "divisibility rule for 3" from elementary number theory: a number is divisible by 3 if and only if the sum of its decimal digits is divisible by 3.

The key insight is that $10 \equiv 1 \pmod{3}$, so each power of 10 contributes nothing to the remainder when divided by 3. This means that when checking divisibility by 3, we only need to consider the sum of the digits themselves.

The theorem expresses this idea formally for numbers written in the form $\sum_{i=0}^{n} 10^i \cdot d(i)$ where $d(i)$ represents the digit in the $i$-th position.

### Dependencies
- **Theorems**:
  - `CONG_DIVIDES`: If $x \equiv y \pmod{n}$, then $n$ divides $x$ if and only if $n$ divides $y$.
  - `SUM_CONG_3` (implicitly): States that the sum of powers of 10 multiplied by digits is congruent modulo 3 to the sum of those digits.

### Porting notes
When implementing this theorem in other systems, ensure that:
1. The system has a proper representation of congruence relations
2. The system has the prerequisite theorem about congruent sums modulo 3
3. The notation for finite sums may need adjustment based on the target system's conventions

---

