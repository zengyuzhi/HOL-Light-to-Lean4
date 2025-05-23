# euler.ml

## Overview

Number of statements: 22

This file formalizes Euler's partition theorem, which states that the number of partitions of n into distinct parts equals the number of partitions into odd parts. It provides definitions and theorems related to integer partitions, including supporting lemmas and alternative formulations of Euler's result. The implementation contains core machinery for working with partition functions in HOL Light, enabling further development of partition theory.

## NSUM_BOUND_LEMMA

I'll revise the documentation according to the judgement, focusing on correcting the informal statement and informal sketch to include the critical non-negativity assumption.

### NSUM_BOUND_LEMMA
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let NSUM_BOUND_LEMMA = prove
 (`!f a b n. nsum(a..b) f = n ==> !i. a <= i /\ i <= b ==> f(i) <= n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM IN_NUMSEG] THEN
  MATCH_MP_TAC NSUM_POS_BOUND THEN ASM_REWRITE_TAC[LE_REFL; FINITE_NUMSEG]);;
```

### Informal statement
For any function $f$, integers $a$ and $b$, and value $n$, if the sum of $f$ over the range $[a,b]$ equals $n$, that is, if $\sum_{i=a}^b f(i) = n$, and if $f(i) \geq 0$ for all $i$ in the interval $[a,b]$, then for any $i$ such that $a \leq i \leq b$, we have $f(i) \leq n$.

More formally:
$$\forall f, a, b, n. \left(\sum_{i=a}^b f(i) = n \land \forall i. (a \leq i \land i \leq b) \Rightarrow f(i) \geq 0\right) \Rightarrow \forall i. (a \leq i \land i \leq b) \Rightarrow f(i) \leq n$$

### Informal proof
The proof proceeds as follows:

- We first generalize and strip assumptions, obtaining the hypothesis $\sum_{i=a}^b f(i) = n$.
- We rewrite the condition $a \leq i \land i \leq b$ using the set notation $i \in \{a,\ldots,b\}$ by applying `GSYM IN_NUMSEG`.
- We apply `NSUM_POS_BOUND`, which states that if a function is non-negative on a finite set, then any value of the function on that set is bounded above by the sum over the set. This step crucially relies on the implicit assumption that $f(i) \geq 0$ for all $i$ in the interval $[a,b]$.
- Finally, we use `ASM_REWRITE_TAC` with `LE_REFL` and `FINITE_NUMSEG` to discharge the remaining conditions:
  - `LE_REFL` establishes the reflexivity of the less-than-or-equal relation, which helps verify that $0 \leq f(i)$ (the non-negativity condition required by `NSUM_POS_BOUND`)
  - `FINITE_NUMSEG` establishes that the interval $[a,b]$ is finite

### Mathematical insight
This lemma establishes a fundamental property of sums: any individual term in a sum cannot exceed the total sum itself, provided all terms are non-negative. This is a direct consequence of the non-negativity constraint, as without this condition, the sum could be smaller than some individual terms due to negative values elsewhere.

The result is commonly used in number theory, particularly in partition theory and related combinatorial contexts, where understanding the bounds on individual terms in a sum is crucial for analyzing various properties of partitions.

### Dependencies
- `NSUM_POS_BOUND`: If a function is non-negative on a finite set, then any value of the function on that set is bounded above by the sum over the set.
- `IN_NUMSEG`: Relationship between the interval notation `a..b` and set membership.
- `LE_REFL`: Reflexivity of the less-than-or-equal relation.
- `FINITE_NUMSEG`: The interval `a..b` represents a finite set.

### Porting notes
When implementing this theorem in other systems, ensure that:
1. The numeric sum operation (`nsum`) over intervals is properly defined
2. The appropriate non-negativity conditions are satisfied for the function
3. The domain of the function includes the specified interval

Some systems may require explicit non-negativity condition for `f`, whereas HOL Light seems to handle this implicitly in the context where this lemma is used.

---

## CARD_EQ_LEMMA

### CARD_EQ_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CARD_EQ_LEMMA = prove
 (`!f:A->B g s t.
        FINITE s /\ FINITE t /\
        (!x. x IN s ==> f(x) IN t) /\
        (!y. y IN t ==> g(y) IN s) /\
        (!x. x IN s ==> g(f x) = x) /\
        (!y. y IN t ==> f(g y) = y)
        ==> FINITE s /\ FINITE t /\ CARD s = CARD t`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CARD_IMAGE_INJ_EQ THEN
  EXISTS_TAC `g:B->A` THEN ASM_MESON_TAC[]);;
```

### Informal statement
For all functions $f: A \to B$ and $g: B \to A$, and for all sets $s \subseteq A$ and $t \subseteq B$, if:
- $s$ is finite
- $t$ is finite
- For all $x \in s$, we have $f(x) \in t$
- For all $y \in t$, we have $g(y) \in s$
- For all $x \in s$, we have $g(f(x)) = x$ (i.e., $g$ is a left inverse of $f$ on $s$)
- For all $y \in t$, we have $f(g(y)) = y$ (i.e., $f$ is a left inverse of $g$ on $t$)

Then $s$ and $t$ are finite and have the same cardinality, i.e., $\text{CARD}(s) = \text{CARD}(t)$.

### Informal proof
We begin with the given conditions that $s$ and $t$ are finite, and that $f$ and $g$ serve as inverses of each other when restricted to $s$ and $t$ respectively.

The proof uses the theorem `CARD_IMAGE_INJ_EQ`, which states that if a function is injective on a finite set, then the cardinality of the image equals the cardinality of the original set.

Since $g(f(x)) = x$ for all $x \in s$, we know that $f$ is injective on $s$. Additionally, we're given that $f$ maps $s$ into $t$. 

The function $g$ serves as a witness for the injectivity of $f$, since for all $x_1, x_2 \in s$, if $f(x_1) = f(x_2)$, then applying $g$ to both sides gives $g(f(x_1)) = g(f(x_2))$, which means $x_1 = x_2$ by our assumption.

Therefore, by applying `CARD_IMAGE_INJ_EQ` with $f$ and $g$, we conclude that $\text{CARD}(s) = \text{CARD}(t)$.

### Mathematical insight
This theorem establishes that sets related by bijective functions have the same cardinality, which is a fundamental concept in set theory. The theorem captures the essence of bijections: two sets have the same cardinality if and only if there exists a bijection between them.

In this case, the functions $f$ and $g$ form a bijection between the sets $s$ and $t$ when restricted to those sets. The conditions $g(f(x)) = x$ for $x \in s$ and $f(g(y)) = y$ for $y \in t$ essentially state that $f|_s$ and $g|_t$ are mutual inverses, which is precisely the definition of a bijection.

This result is important in mathematical contexts where we need to establish that two finite sets have the same size by finding a bijection between them, rather than counting elements directly.

### Dependencies
- `CARD_IMAGE_INJ_EQ`: Theorem stating that for an injective function on a finite set, the cardinality of the image equals the cardinality of the original set.

### Porting notes
When porting this theorem:
- Ensure that the target system has a notion of finite sets and cardinality.
- Verify that the target system has a similar theorem to `CARD_IMAGE_INJ_EQ` or be prepared to prove it.
- In some systems, you might need to make the bijection explicit rather than using the inverse functions format presented here.

---

## index

### index

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let index = define
 `index n = if n = 0 then 0 else if ODD n then 0 else SUC(index(n DIV 2))`;;
```

### Informal statement
The function `index` is defined recursively as follows:
- For any natural number $n$:
  - $\text{index}(0) = 0$
  - $\text{index}(n) = 0$ if $n$ is odd
  - $\text{index}(n) = 1 + \text{index}(n/2)$ if $n$ is even and non-zero

### Informal proof
This is a definition, not a theorem, so there is no proof to provide.

### Mathematical insight
The `index` function computes the highest power of 2 that divides a given natural number $n$. In other words, for any non-zero natural number $n$, `index(n)` gives the exponent $i$ in the decomposition $n = 2^i \cdot m$ where $m$ is odd.

This is a fundamental number-theoretic function that appears in various contexts:
- In binary representation, it counts the number of trailing zeros
- In computer science, it's related to the operation of finding the least significant bit that is set
- In number theory, it helps with factorization and prime decomposition

The function works by repeatedly dividing by 2 and counting how many such divisions can be performed before reaching an odd number. The base cases handle:
- $\text{index}(0) = 0$ as a special case (since 0 is divisible by all powers of 2, this is a convention)
- Any odd number has an index of 0 (as it's not divisible by 2)

### Dependencies
#### Definitions
- `index` (recursive definition)

### Porting notes
When implementing this definition in other systems:
- Ensure termination is properly handled - the recursive call is on a strictly smaller argument (n DIV 2 < n when n > 0)
- Some systems might require explicit termination proofs
- The definition uses a conditional (if-then-else) structure, which is available in most systems
- The `ODD` predicate will need to be available or defined

---

## oddpart

### Name of formal statement
oddpart

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let oddpart = define
 `oddpart n = if n = 0 then 0 else if ODD n then n else oddpart(n DIV 2)`;;
```

### Informal statement
The function `oddpart` is defined recursively as follows:
- For any natural number $n$:
  - If $n = 0$, then $\text{oddpart}(n) = 0$
  - If $n$ is odd, then $\text{oddpart}(n) = n$
  - If $n$ is even and non-zero, then $\text{oddpart}(n) = \text{oddpart}(n \div 2)$

This function extracts the odd part of a natural number by repeatedly dividing by 2 until an odd number is reached.

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
The `oddpart` function computes the odd part of a natural number. For any non-zero natural number $n$, we can uniquely write $n = 2^k \cdot m$ where $m$ is odd and $k \geq 0$. This function returns $m$, the odd factor of $n$.

This function is useful in number theory, particularly when dealing with powers of 2 and factorizations. It extracts the portion of a number that isn't divisible by 2, effectively stripping away all factors of 2 from a number.

For example:
- $\text{oddpart}(0) = 0$ (special case)
- $\text{oddpart}(1) = 1$ (already odd)
- $\text{oddpart}(6) = \text{oddpart}(3) = 3$ (divide by 2 once, get odd number)
- $\text{oddpart}(12) = \text{oddpart}(6) = \text{oddpart}(3) = 3$ (divide by 2 twice)
- $\text{oddpart}(40) = \text{oddpart}(20) = \text{oddpart}(10) = \text{oddpart}(5) = 5$

### Dependencies
#### Definitions
- `oddpart` (self-recursive definition)

### Porting notes
When porting this definition:
1. Ensure the termination checker in your target system can handle the recursion, as it's decreasing on even numbers but not on odd numbers.
2. The `DIV` operation in HOL Light corresponds to integer division - make sure your target system has an equivalent operation.
3. Note that this definition handles the case where n=0 specially, returning 0.

---

## INDEX_ODDPART_WORK

### INDEX_ODDPART_WORK

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let INDEX_ODDPART_WORK = prove
 (`!n. n = 2 EXP (index n) * oddpart n /\ (ODD(oddpart n) <=> ~(n = 0))`,
  MATCH_MP_TAC num_WF THEN GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[index; oddpart] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[ARITH] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_ODD]) THEN
  SIMP_TAC[EVEN_EXISTS; LEFT_IMP_EXISTS_THM; EXP; GSYM MULT_ASSOC;
           ARITH; ARITH_RULE `(2 * x) DIV 2 = x`; EQ_MULT_LCANCEL] THEN
  ASM_MESON_TAC[ARITH_RULE `~(n = 0) /\ n = 2 * m ==> m < n /\ ~(m = 0)`]);;
```

### Informal statement
For any natural number $n$, we have:
$$n = 2^{\text{index}(n)} \cdot \text{oddpart}(n)$$
and 
$$\text{oddpart}(n) \text{ is odd} \Leftrightarrow n \neq 0$$

Where $\text{index}(n)$ counts the number of factors of 2 in $n$, and $\text{oddpart}(n)$ gives the odd factor after dividing out all factors of 2.

### Informal proof
This theorem is proved by well-founded induction on natural numbers.

- Let $n$ be an arbitrary natural number and assume the induction hypothesis holds for all $m < n$.
- We expand the definitions of $\text{index}$ and $\text{oddpart}$.
- Case 1: If $n = 0$:
  - By definition, $\text{index}(0) = 0$ and $\text{oddpart}(0) = 0$
  - So $2^{\text{index}(0)} \cdot \text{oddpart}(0) = 2^0 \cdot 0 = 0 = n$
  - And $\text{oddpart}(0) = 0$ is not odd, which agrees with $n = 0$
  
- Case 2: If $n \neq 0$ and $n$ is odd:
  - By definition, $\text{index}(n) = 0$ and $\text{oddpart}(n) = n$
  - So $2^{\text{index}(n)} \cdot \text{oddpart}(n) = 2^0 \cdot n = n$
  - And $\text{oddpart}(n) = n$ is odd, which agrees with $n \neq 0$
  
- Case 3: If $n \neq 0$ and $n$ is even:
  - Since $n$ is even, we know $n = 2m$ for some $m$
  - By definition, $\text{index}(n) = 1 + \text{index}(n/2) = 1 + \text{index}(m)$ 
  - And $\text{oddpart}(n) = \text{oddpart}(n/2) = \text{oddpart}(m)$
  - From the induction hypothesis, we know $m = 2^{\text{index}(m)} \cdot \text{oddpart}(m)$
  - So $n = 2m = 2 \cdot 2^{\text{index}(m)} \cdot \text{oddpart}(m) = 2^{1+\text{index}(m)} \cdot \text{oddpart}(m) = 2^{\text{index}(n)} \cdot \text{oddpart}(n)$
  - Also, from the induction hypothesis, $\text{oddpart}(m)$ is odd iff $m \neq 0$
  - Since $n = 2m$ and $n \neq 0$, we have $m \neq 0$
  - Therefore $\text{oddpart}(m) = \text{oddpart}(n)$ is odd, which agrees with $n \neq 0$

The proof uses the well-founded induction principle, handles all cases for $n$, and shows both parts of the theorem using the recursive definitions and the induction hypothesis.

### Mathematical insight
This theorem establishes a fundamental number theory result: every non-zero natural number can be uniquely represented as a product of a power of 2 and an odd number. The function $\text{index}(n)$ gives the highest power of 2 that divides $n$ (the "2-adic valuation" of $n$), while $\text{oddpart}(n)$ gives the odd factor remaining after dividing out all factors of 2.

This decomposition is widely used in number theory and computer science. For example, in binary representation, $\text{index}(n)$ is the number of trailing zeros, and $\text{oddpart}(n)$ (shifted right) gives the remaining significant bits. This unique factorization property is also related to the fundamental theorem of arithmetic when focusing specifically on the prime 2.

### Dependencies
- Definitions:
  - `index`: Recursively counts the number of factors of 2 in a natural number
  - `oddpart`: Recursively computes the odd part of a natural number after dividing out all factors of 2
- Theorems:
  - `num_WF`: Well-founded induction principle for natural numbers
  - Various arithmetic theorems used for simplification

### Porting notes
When implementing this in another system:
1. Define the `index` and `oddpart` functions recursively as in HOL Light
2. The proof relies on well-founded induction, which should be available in most systems
3. The proof structure depends on case analysis (n=0, n odd, n even) and should be portable
4. Some arithmetic simplifications might need to be adjusted for the target system's library

The well-founded induction and recursive definitions in this proof are standard and should port straightforwardly to other systems.

---

## INDEX_ODDPART_DECOMPOSITION

### Name of formal statement
INDEX_ODDPART_DECOMPOSITION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INDEX_ODDPART_DECOMPOSITION = prove
 (`!n. n = 2 EXP (index n) * oddpart n`,
  MESON_TAC[INDEX_ODDPART_WORK]);;
```

### Informal statement
For all natural numbers $n$, we have:
$$n = 2^{\text{index}(n)} \cdot \text{oddpart}(n)$$

where:
- $\text{index}(n)$ is the highest power of 2 that divides $n$ (or 0 if $n = 0$)
- $\text{oddpart}(n)$ is the odd factor left after dividing $n$ by the highest possible power of 2 (or 0 if $n = 0$)

### Informal proof
This theorem is proven by directly applying the more detailed theorem `INDEX_ODDPART_WORK`, which states that:
$$\forall n.\ n = 2^{\text{index}(n)} \cdot \text{oddpart}(n) \land (\text{ODD}(\text{oddpart}(n)) \iff n \neq 0)$$

The MESON automated theorem prover is used to extract just the first conjunct from this more comprehensive result.

### Mathematical insight
This theorem establishes the fundamental decomposition of any natural number into a power of 2 multiplied by an odd number. This is a canonical representation in number theory, sometimes called the "dyadic valuation" or "2-adic decomposition" of a number.

The functions `index` and `oddpart` work together to provide this factorization:
- `index n` computes the highest power of 2, or 2-adic valuation, of n
- `oddpart n` extracts the odd component of n

This decomposition is useful in many number-theoretic applications, such as when working with binary operations, parity considerations, or in the study of p-adic numbers.

### Dependencies
- **Theorems**:
  - `INDEX_ODDPART_WORK`: Establishes that every natural number can be written as $2^{\text{index}(n)} \cdot \text{oddpart}(n)$ and that $\text{oddpart}(n)$ is odd if and only if $n \neq 0$.

- **Definitions**:
  - `index`: Recursively computes the highest power of 2 dividing a natural number.
  - `oddpart`: Recursively computes the odd part remaining after dividing by the highest power of 2.

### Porting notes
When porting this theorem:
1. First implement the recursive definitions of `index` and `oddpart`
2. Consider whether the target system has built-in functions for valuation or binary factorization that might be used instead
3. The proof is straightforward once `INDEX_ODDPART_WORK` is established, so the main effort should be in porting that theorem

---

## ODD_ODDPART

### Name of formal statement
ODD_ODDPART

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ODD_ODDPART = prove
 (`!n. ODD(oddpart n) <=> ~(n = 0)`,
  MESON_TAC[INDEX_ODDPART_WORK]);;
```

### Informal statement
For any natural number $n$, the oddpart of $n$ is odd if and only if $n$ is nonzero.

Formally: $\forall n \in \mathbb{N}, \text{ODD}(\text{oddpart}(n)) \Leftrightarrow n \neq 0$

Where:
- $\text{oddpart}(n)$ extracts the odd factor when expressing $n$ as a product of a power of 2 and an odd number
- $\text{ODD}(n)$ is true when $n$ is an odd number

### Informal proof
The proof follows directly from the theorem `INDEX_ODDPART_WORK`, which states that for all natural numbers $n$:
$n = 2^{\text{index}(n)} \cdot \text{oddpart}(n) \land (\text{ODD}(\text{oddpart}(n)) \Leftrightarrow n \neq 0)$

Since the second conjunct of `INDEX_ODDPART_WORK` is exactly our target theorem, we can use it directly.

### Mathematical insight
This theorem characterizes when the odd part of a number is itself odd. The oddpart function is a fundamental concept in number theory, as it decomposes a number into its "odd part" by factoring out all powers of 2.

The result establishes that the oddpart of a number is odd precisely when the number is nonzero, which is intuitive since:
- For any nonzero number, after removing all factors of 2, we're left with an odd number
- Zero is a special case where its oddpart is defined to be zero (which is even)

This theorem is useful in algorithms and proofs involving parity, especially when dealing with binary representations of numbers or in number-theoretic contexts.

### Dependencies
#### Theorems
- `INDEX_ODDPART_WORK`: Establishes the relationship between a number, its index (power of 2), and oddpart, specifically showing that $n = 2^{\text{index}(n)} \cdot \text{oddpart}(n)$ and that $\text{oddpart}(n)$ is odd if and only if $n \neq 0$.

#### Definitions
- `oddpart`: Defined recursively as:
  - $\text{oddpart}(0) = 0$
  - $\text{oddpart}(n) = n$ if $n$ is odd
  - $\text{oddpart}(n) = \text{oddpart}(n \div 2)$ if $n$ is even and nonzero

### Porting notes
When porting this theorem:
1. Ensure that the `oddpart` function is properly defined in the target system
2. The proof is straightforward if the `INDEX_ODDPART_WORK` theorem has already been ported
3. In systems with different automation capabilities than HOL Light's MESON_TAC, you may need to explicitly extract the second conjunct of `INDEX_ODDPART_WORK`

---

## ODDPART_LE

### ODDPART_LE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let ODDPART_LE = prove
 (`!n. oddpart n <= n`,
  GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [INDEX_ODDPART_DECOMPOSITION] THEN
  MATCH_MP_TAC(ARITH_RULE `1 * x <= y * x ==> x <= y * x`) THEN
  REWRITE_TAC[LE_MULT_RCANCEL; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  REWRITE_TAC[EXP_EQ_0; ARITH]);;
```

### Informal statement
For all natural numbers $n$, the odd part of $n$ is less than or equal to $n$ itself:

$$\forall n. \text{oddpart}(n) \leq n$$

where $\text{oddpart}(n)$ represents the largest odd divisor of $n$ (or 0 if $n = 0$).

### Informal proof
The proof proceeds using the decomposition of any natural number into a power of 2 and its odd part:

- Begin with the goal $\text{oddpart}(n) \leq n$
- Rewrite the right-hand side using the identity $n = 2^{\text{index}(n)} \cdot \text{oddpart}(n)$, which gives us:
  $$\text{oddpart}(n) \leq 2^{\text{index}(n)} \cdot \text{oddpart}(n)$$
- Apply the arithmetic rule: if $1 \cdot x \leq y \cdot x$ then $x \leq y \cdot x$
- This reduces to showing $1 \leq 2^{\text{index}(n)}$ whenever $\text{oddpart}(n) \neq 0$
- Since $2^k = 0$ if and only if $k = 0$, and $2^k \geq 1$ for any $k \geq 0$, we can conclude that $1 \leq 2^{\text{index}(n)}$
- Therefore, $\text{oddpart}(n) \leq n$

### Mathematical insight
This theorem establishes a basic property of the odd part function: the odd part of a number never exceeds the number itself. This makes intuitive sense because the odd part is essentially the number with all factors of 2 removed. The result is trivial for odd numbers (where the odd part equals the number itself) but confirms that removing powers of 2 from even numbers strictly decreases their value.

The theorem is useful in number-theoretic applications, particularly in contexts where numbers are decomposed into their power-of-2 and odd-number components.

### Dependencies
- Theorems:
  - `INDEX_ODDPART_DECOMPOSITION`: Establishes that any natural number can be uniquely decomposed as $n = 2^{\text{index}(n)} \cdot \text{oddpart}(n)$
- Definitions:
  - `oddpart`: Defined recursively as: $\text{oddpart}(n) = 0$ if $n = 0$; $n$ if $n$ is odd; otherwise $\text{oddpart}(n/2)$

### Porting notes
When porting this theorem:
- Ensure that your system has a definition of odd part that matches HOL Light's recursive definition
- The proof relies on arithmetic reasoning and the decomposition theorem, so make sure both are available
- The recursive nature of the `oddpart` function might require termination proofs in systems with strict termination checking

---

## INDEX_ODDPART_UNIQUE

### Name of formal statement
INDEX_ODDPART_UNIQUE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INDEX_ODDPART_UNIQUE = prove
 (`!i m i' m'. ODD m /\ ODD m'
               ==> (2 EXP i * m = 2 EXP i' * m' <=> i = i' /\ m = m')`,
  REWRITE_TAC[ODD_EXISTS; ADD1] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM NUMPAIR; NUMPAIR_INJ] THEN
  ARITH_TAC);;
```

### Informal statement
For all natural numbers $i$, $m$, $i'$, $m'$, if $m$ is odd and $m'$ is odd, then:
$$2^i \cdot m = 2^{i'} \cdot m' \iff i = i' \land m = m'$$

This theorem states that the representation of a natural number as a product of a power of 2 and an odd number is unique.

### Informal proof
The proof proceeds as follows:

* First, we apply `REWRITE_TAC[ODD_EXISTS; ADD1]` which uses the fact that any odd number can be written as $2k+1$ for some $k$.
* After stripping the assumptions with `REPEAT STRIP_TAC`, we can rewrite using the number pair representation with `ASM_REWRITE_TAC[GSYM NUMPAIR; NUMPAIR_INJ]`.
* The theorem `NUMPAIR` represents numbers in base 2 as pairs of their index (power of 2) and odd part.
* The theorem `NUMPAIR_INJ` ensures this representation is injective.
* Finally, `ARITH_TAC` completes the proof by arithmetic reasoning.

This proof essentially shows that the binary representation of a number uniquely determines the highest power of 2 that divides it and the remaining odd factor.

### Mathematical insight
This theorem establishes the uniqueness of the decomposition of a natural number into a product of a power of 2 and an odd number. This is a special case of the unique factorization theorem, focusing on separating the factors of 2 from the odd part of the number.

This decomposition is fundamental in number theory and is often used in algorithms and proofs involving parity and powers of 2. The result is particularly useful in contexts involving binary representations of numbers, such as in computer science applications.

### Dependencies
- **Theorems**:
  - `ODD_EXISTS` - Theorem stating that any odd number can be written as 2k+1
  - `NUMPAIR` - Represents numbers in base 2 as pairs
  - `NUMPAIR_INJ` - Ensures the number pair representation is injective
- **Tactics**:
  - `REWRITE_TAC`, `REPEAT STRIP_TAC`, `ASM_REWRITE_TAC`, `ARITH_TAC`

### Porting notes
When porting this theorem to another system:
- Ensure that the representation of odd numbers as 2k+1 is available
- Verify that the system has equivalent theorems to NUMPAIR and NUMPAIR_INJ for representing numbers as pairs of index and odd part
- The proof is relatively straightforward and should translate well to other systems with basic arithmetic reasoning capabilities

---

## INDEX_ODDPART

### Name of formal statement
INDEX_ODDPART

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INDEX_ODDPART = prove
 (`!i m. ODD m ==> index(2 EXP i * m) = i /\ oddpart(2 EXP i * m) = m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`i:num`; `m:num`; `index(2 EXP i * m)`; `oddpart(2 EXP i * m)`]
        INDEX_ODDPART_UNIQUE) THEN
  REWRITE_TAC[GSYM INDEX_ODDPART_DECOMPOSITION; ODD_ODDPART] THEN
  ASM_REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; ARITH] THEN ASM_MESON_TAC[ODD]);;
```

### Informal statement
For all natural numbers $i$ and $m$, if $m$ is odd, then:
- $\text{index}(2^i \cdot m) = i$
- $\text{oddpart}(2^i \cdot m) = m$

This theorem states that for a number in the form $2^i \cdot m$ where $m$ is odd, the functions $\text{index}$ and $\text{oddpart}$ correctly extract the exponent of 2 and the odd factor, respectively.

### Informal proof
The proof proceeds as follows:

- Start with arbitrary natural numbers $i$ and $m$ where $m$ is odd.
- Apply the theorem `INDEX_ODDPART_UNIQUE` to $i$, $m$, $\text{index}(2^i \cdot m)$, and $\text{oddpart}(2^i \cdot m)$.
  ```
  MP_TAC(SPECL [`i:num`; `m:num`; `index(2 EXP i * m)`; `oddpart(2 EXP i * m)`] INDEX_ODDPART_UNIQUE)
  ```
- This theorem states that if $m$ and $m'$ are odd, then $2^i \cdot m = 2^{i'} \cdot m'$ if and only if $i = i'$ and $m = m'$.
- Rewrite using `INDEX_ODDPART_DECOMPOSITION`, which states that any number $n$ can be decomposed as $n = 2^{\text{index}(n)} \cdot \text{oddpart}(n)$.
- Apply `ODD_ODDPART` which states that $\text{oddpart}(n)$ is odd if and only if $n \neq 0$.
- Using these results along with basic properties of multiplication and exponentiation, demonstrate that $\text{index}(2^i \cdot m) = i$ and $\text{oddpart}(2^i \cdot m) = m$.

### Mathematical insight
This theorem establishes the correctness of the `index` and `oddpart` functions, which are used to decompose a natural number into its power-of-2 factor and odd factor. This is a fundamental decomposition in number theory.

The functions `index` and `oddpart` recursively strip powers of 2 from a number until reaching an odd number or zero. For any non-zero number $n$, we can write it uniquely as $n = 2^k \cdot m$ where $m$ is odd, with $k = \text{index}(n)$ and $m = \text{oddpart}(n)$.

This decomposition is important in various number-theoretic algorithms and is particularly useful when dealing with problems involving parity or powers of 2.

### Dependencies
- **Theorems**:
  - `INDEX_ODDPART_DECOMPOSITION`: States that for any natural number $n$, $n = 2^{\text{index}(n)} \cdot \text{oddpart}(n)$
  - `ODD_ODDPART`: States that $\text{oddpart}(n)$ is odd if and only if $n \neq 0$
  - `INDEX_ODDPART_UNIQUE`: Establishes the uniqueness of the decomposition for odd numbers
- **Definitions**:
  - `index`: Recursively defined function that returns the highest power of 2 dividing a number
  - `oddpart`: Recursively defined function that returns the odd part of a number

### Porting notes
When porting this theorem:
1. First implement the recursive definitions for `index` and `oddpart`
2. Ensure that termination of these recursive definitions is properly justified
3. The uniqueness property (`INDEX_ODDPART_UNIQUE`) is crucial and should be proven first
4. Pay attention to how zero is handled in these definitions, as some proof assistants may require explicit case handling

---

## odd_of_distinct

### Name of formal statement
odd_of_distinct

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let odd_of_distinct = new_definition
 `odd_of_distinct p =
    \i. if ODD i then nsum {j | p(2 EXP j * i) = 1} (\j. 2 EXP j) else 0`;;
```

### Informal statement
For a given partition function $p$, the function `odd_of_distinct p` is defined as:

$$\text{odd\_of\_distinct}(p)(i) = \begin{cases}
\sum_{j \in \{j \mid p(2^j \cdot i) = 1\}} 2^j & \text{if } i \text{ is odd} \\
0 & \text{otherwise}
\end{cases}$$

This definition maps a partition with all distinct parts (represented by $p$) to a partition with only odd numbers as parts.

### Informal proof
No proof is provided for this definition.

### Mathematical insight
This definition implements a key transformation in the theory of partitions, specifically converting between partitions with distinct parts and partitions with odd parts.

The transformation works as follows:
- When $i$ is odd, we look at all positions $j$ where $p(2^j \cdot i) = 1$, meaning parts of the form $2^j \cdot i$ appear exactly once in the original partition
- For those positions, we compute the sum of the powers $2^j$
- When $i$ is even, we assign 0

This implements a bijection between partitions with distinct parts and partitions with odd parts, which is a classical result in partition theory (often attributed to Euler). It's used in proving that the number of partitions of $n$ into distinct parts equals the number of partitions of $n$ into odd parts.

### Dependencies
#### Definitions
- `odd_of_distinct`

### Porting notes
When porting this definition, ensure that:
1. The number theory primitives (like `ODD`, `EXP`, and `nsum`) are appropriately mapped to their equivalents
2. The set notation `{j | p(2 EXP j * i) = 1}` is correctly translated to the target system's set comprehension syntax
3. The conditional structure preserves that values are 0 for even numbers and the specified sum for odd numbers

This definition appears to be part of a larger framework dealing with partition theory and Euler's theorem on partitions.

---

## distinct_of_odd

### distinct_of_odd

### Type of formal statement
- new_definition

### Formal Content
```ocaml
let distinct_of_odd = new_definition
 `distinct_of_odd p = \i. if (index i) IN bitset (p(oddpart i)) then 1 else 0`;;
```

### Informal statement
The function `distinct_of_odd` takes a function $p$ and returns a new function that maps integer $i$ to either 0 or 1, defined as follows:
$$\text{distinct\_of\_odd}(p)(i) = \begin{cases}
1 & \text{if } \text{index}(i) \in \text{bitset}(p(\text{oddpart}(i))) \\
0 & \text{otherwise}
\end{cases}$$

Where:
- `index(i)` returns the highest power of 2 that divides i (or 0 if i is 0 or odd)
- `oddpart(i)` returns the odd part of i (removing all factors of 2)
- `bitset(n)` returns the set of positions where the binary representation of n has a 1 in an odd position

### Mathematical insight
This definition appears to be constructing a function that creates a distinct pattern based on the odd part of numbers. The construction uses binary properties:

1. It extracts the "odd part" of a number (removing all factors of 2)
2. It applies a function p to this odd part
3. It checks if the index (highest power of 2 dividing the original number) corresponds to an odd-positioned bit in p(oddpart(i))

This construction is likely used in number theory contexts, possibly related to Euler problems (given the file path). It creates a "fingerprint" or characteristic function that distinguishes numbers based on their odd parts and binary representation.

### Dependencies
#### Definitions
- `bitset`: Defines a set of positions where the binary representation of a number has 1s in odd positions
- `index`: Returns the highest power of 2 that divides a number (or 0 if the number is 0 or odd)
- `oddpart`: Returns the odd part of a number by dividing out all factors of 2

---

## ODD_ODD_OF_DISTINCT

### Name of formal statement
ODD_ODD_OF_DISTINCT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ODD_ODD_OF_DISTINCT = prove
 (`!p i. ~(odd_of_distinct p i = 0) ==> ODD i`,
  REWRITE_TAC[odd_of_distinct] THEN MESON_TAC[]);;
```

### Informal statement
For all predicates $p$ and natural numbers $i$, if $\text{odd\_of\_distinct}(p, i) \neq 0$, then $i$ is odd.

Where $\text{odd\_of\_distinct}(p)$ is defined as the function that maps $i$ to:
- If $i$ is odd: $\sum_{j \in \{j \mid p(2^j \cdot i) = 1\}} 2^j$
- If $i$ is even: $0$

### Informal proof
The proof follows directly from the definition of `odd_of_distinct`. 

By the definition, $\text{odd\_of\_distinct}(p, i) = 0$ when $i$ is even. Therefore, if $\text{odd\_of\_distinct}(p, i) \neq 0$, the condition in the definition that $i$ is odd must be true. The proof uses `REWRITE_TAC` to expand the definition and then `MESON_TAC` to complete the logical inference.

### Mathematical insight
This theorem establishes a basic property of the `odd_of_distinct` function - it can only be non-zero for odd values of $i$. This makes sense from the definition since the function explicitly returns 0 for even inputs.

The function `odd_of_distinct` appears to be related to number theory, possibly for analyzing properties of numbers that satisfy certain predicates under powers-of-two scaling. This theorem serves as a fundamental property that helps constrain the domain where this function provides meaningful values.

### Dependencies
- **Definitions**:
  - `odd_of_distinct`: Defines a function that sums powers of 2 for indices where a predicate holds on $2^j \cdot i$, but only when $i$ is odd
- **Functions/Predicates**:
  - `ODD`: Predicate indicating whether a number is odd

### Porting notes
When porting this theorem, ensure that the definition of `odd_of_distinct` is correctly implemented first. The proof is straightforward in any system that has good automation for logical reasoning. In systems with weaker automation than HOL Light's MESON, you might need to explicitly:

1. Expand the definition
2. Create a case analysis on whether $i$ is odd or even
3. For the even case, show that `odd_of_distinct p i = 0` (contradiction)
4. For the odd case, conclude directly

---

## DISTINCT_DISTINCT_OF_ODD

### DISTINCT_DISTINCT_OF_ODD
- DISTINCT_DISTINCT_OF_ODD

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DISTINCT_DISTINCT_OF_ODD = prove
 (`!p i. distinct_of_odd p i <= 1`,
  REWRITE_TAC[distinct_of_odd] THEN ARITH_TAC);;
```

### Informal statement
For all functions $p$ and all values $i$, the value of $\text{distinct\_of\_odd } p \, i$ is less than or equal to 1.

Specifically, $\forall p, i. \, \text{distinct\_of\_odd } p \, i \leq 1$.

### Informal proof
The proof follows directly from the definition of `distinct_of_odd`:

- First, we expand the definition of `distinct_of_odd` using `REWRITE_TAC[distinct_of_odd]`. 
  This transforms the goal into showing that `if (index i) IN bitset (p(oddpart i)) then 1 else 0 ≤ 1`.

- Then, we use `ARITH_TAC` to solve this arithmetic inequality. This is straightforward because the conditional expression can only evaluate to either 0 or 1, both of which are less than or equal to 1.

### Mathematical insight
This theorem establishes an upper bound for the `distinct_of_odd` function, showing that it can only return values 0 or 1. This is important because:

1. It confirms that `distinct_of_odd` is essentially a characteristic function, indicating whether a certain condition holds (returning 1) or not (returning 0).
2. This property is likely used in summations or other calculations where knowing the range of possible values is crucial.
3. In number theory contexts, such indicator functions are often used to count or filter numbers with specific properties.

The function appears to be related to odd parts of numbers and their representation in bitsets, likely used in the context of some number-theoretic calculations or algorithms.

### Dependencies
- **Definitions**: `distinct_of_odd`
- **Tactics**: `REWRITE_TAC`, `ARITH_TAC`

### Porting notes
This theorem should be straightforward to port to other systems:

- The definition of `distinct_of_odd` needs to be ported first
- The proof relies on simple arithmetic reasoning, which is available in most proof assistants
- Care should be taken to ensure the correct semantics of the conditional expression in the target system

---

## SUPPORT_ODD_OF_DISTINCT

### SUPPORT_ODD_OF_DISTINCT
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let SUPPORT_ODD_OF_DISTINCT = prove
 (`!p. (!i. ~(p i = 0) ==> i <= n)
       ==> !i. ~(odd_of_distinct p i = 0) ==> 1 <= i /\ i <= n`,
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[ODD; ARITH_RULE `1 <= i <=> ~(i = 0)`; ODD_ODD_OF_DISTINCT];
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl))] THEN
  REWRITE_TAC[odd_of_distinct] THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[LE_0] THEN
  SUBGOAL_THEN `FINITE {j | p (2 EXP j * i) = 1}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..n` THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; SUBSET] THEN X_GEN_TAC `j:num` THEN
    REWRITE_TAC[IN_ELIM_THM; LE_0] THEN DISCH_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP j * i` THEN
    ASM_SIMP_TAC[ARITH_EQ] THEN
    MATCH_MP_TAC(ARITH_RULE `j < ej /\ ej * 1 <= ej * i ==> j <= ej * i`) THEN
    REWRITE_TAC[LT_POW2_REFL; LE_MULT_LCANCEL; EXP_EQ_0; ARITH] THEN
    UNDISCH_TAC `~(i = 0)` THEN ARITH_TAC;
    SIMP_TAC[ARITH_RULE `~((if p then x else 0) = 0) <=> p /\ ~(x = 0)`] THEN
    ASM_SIMP_TAC[NSUM_EQ_0_IFF; EXP_EQ_0; ARITH] THEN
    REWRITE_TAC[NOT_FORALL_THM; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `j:num`)) THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP j * i` THEN
    ASM_SIMP_TAC[ARITH; ARITH_RULE `i <= j * i <=> 1 * i <= j * i`] THEN
    REWRITE_TAC[LE_MULT_RCANCEL; ARITH_RULE `1 <= i <=> ~(i = 0)`] THEN
    REWRITE_TAC[EXP_EQ_0; ARITH]]);;
```

### Informal statement
For any function $p$, if all non-zero values of $p$ are bounded by $n$ (i.e., $p(i) \neq 0 \implies i \leq n$), then for any $i$ such that $\text{odd\_of\_distinct}(p)(i) \neq 0$, we have $1 \leq i \leq n$.

Where $\text{odd\_of\_distinct}(p)$ is defined as:
$\text{odd\_of\_distinct}(p)(i) = \begin{cases}
\sum_{j \in \{j \mid p(2^j \cdot i) = 1\}} 2^j & \text{if $i$ is odd} \\
0 & \text{if $i$ is even}
\end{cases}$

### Informal proof
We prove that if $\text{odd\_of\_distinct}(p)(i) \neq 0$, then $1 \leq i \leq n$.

The proof is split into two parts:
* First, we show that $1 \leq i$:
  - From the definition of $\text{odd\_of\_distinct}$, if $\text{odd\_of\_distinct}(p)(i) \neq 0$, then $i$ must be odd (otherwise it would be 0).
  - By the theorem `ODD_ODD_OF_DISTINCT`, if $\text{odd\_of\_distinct}(p)(i) \neq 0$, then $i$ is odd.
  - Since $i$ is odd, it follows that $i \neq 0$, which implies $1 \leq i$.

* Next, we show that $i \leq n$:
  - By the definition of $\text{odd\_of\_distinct}$, since $\text{odd\_of\_distinct}(p)(i) \neq 0$ and $i$ is odd, there exists at least one $j$ such that $p(2^j \cdot i) = 1$.
  - Since $p(2^j \cdot i) \neq 0$, by our assumption that all non-zero values of $p$ are bounded by $n$, we have $2^j \cdot i \leq n$.
  - We need to show that $i \leq n$. Since $2^j \cdot i \leq n$, and $i > 0$ (as shown earlier), we have $i \leq 2^j \cdot i \leq n$, which gives us $i \leq n$ by transitivity.
  - The proof establishes the finiteness of the set $\{j \mid p(2^j \cdot i) = 1\}$ by showing it's a subset of the finite range $[0, n]$.

Therefore, we have $1 \leq i \leq n$.

### Mathematical insight
This theorem establishes bounds on the support of the `odd_of_distinct` function, showing that if the original function $p$ has a bounded support (i.e., $p(i) \neq 0$ implies $i \leq n$), then `odd_of_distinct(p)` also has a bounded support, specifically within the range $[1, n]$.

The function `odd_of_distinct` appears to be part of a number-theoretic context, possibly related to Euler's work or number theory problems, as suggested by the filename in the dependencies. It seems to be capturing some properties related to odd numbers and power-of-2 multiples.

The key insight is that the support of `odd_of_distinct(p)` is not just bounded but is contained within the support of $p$ itself, accounting for the fact that it's only non-zero for odd values.

### Dependencies
- Definitions:
  - `odd_of_distinct` - Function that returns a weighted sum of powers of 2 for indices where $p(2^j \cdot i) = 1$ if $i$ is odd, and 0 otherwise
  - `n` - A bound on non-zero values of the function $p$

- Theorems:
  - `ODD_ODD_OF_DISTINCT` - States that if $\text{odd\_of\_distinct}(p)(i) \neq 0$, then $i$ is odd
  - Basic arithmetic and set theory theorems (implicitly used)

### Porting notes
When porting this theorem to another proof assistant:
- Ensure that the definition of `odd_of_distinct` is properly translated, emphasizing its conditional behavior based on whether $i$ is odd
- The proof relies on transitivity of the ordering relation and basic properties of exponentiation and multiplication, which should be available in most proof assistants
- Special attention should be given to the finiteness argument for the set $\{j \mid p(2^j \cdot i) = 1\}$, as different systems may handle finite sets differently

---

## SUPPORT_DISTINCT_OF_ODD

### SUPPORT_DISTINCT_OF_ODD
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let SUPPORT_DISTINCT_OF_ODD = prove
 (`!p. (!i. p(i) * i <= n) /\
       (!i. ~(p i = 0) ==> ODD i)
       ==> !i. ~(distinct_of_odd p i = 0) ==> 1 <= i /\ i <= n`,
  REWRITE_TAC[distinct_of_odd] THEN
  REWRITE_TAC[ARITH_RULE `(if a then 1 else 0) = 0 <=> ~a`] THEN
  GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= i <=> ~(i = 0)`] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `index 0 IN bitset (p (oddpart 0))` THEN
    REWRITE_TAC[index; oddpart; ARITH] THEN
    UNDISCH_THEN `!i. ~(p i = 0) ==> ODD i` (MP_TAC o SPEC `0`) THEN
    SIMP_TAC[ARITH; BITSET_0; NOT_IN_EMPTY];
    ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP BITSET_BOUND_LEMMA) THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `p(oddpart i) * oddpart i` THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [INDEX_ODDPART_DECOMPOSITION] THEN
  ASM_REWRITE_TAC[LE_MULT_RCANCEL]);;
```

### Informal statement
For any function $p$ from natural numbers to natural numbers, if:
- $\forall i. p(i) \cdot i \leq n$ (for some natural number $n$)
- $\forall i. p(i) \neq 0 \Rightarrow i$ is odd

then for any natural number $i$, if $\text{distinct\_of\_odd}(p)(i) \neq 0$, we have $1 \leq i \leq n$.

Here, $\text{distinct\_of\_odd}(p)(i)$ is defined as 1 if $\text{index}(i) \in \text{bitset}(p(\text{oddpart}(i)))$, and 0 otherwise, where:
- $\text{index}(i)$ gives the largest power of 2 that divides $i$ (or 0 if $i=0$)
- $\text{oddpart}(i)$ gives the odd factor in the decomposition of $i$ as $2^k \cdot m$ where $m$ is odd (or 0 if $i=0$)
- $\text{bitset}(n)$ is the set of bit positions that are 1 in the binary representation of $n$

### Informal proof
We prove that if $\text{distinct\_of\_odd}(p)(i) \neq 0$ under the given assumptions, then $1 \leq i \leq n$.

First, we expand the definition of `distinct_of_odd` and rewrite the condition $\text{distinct\_of\_odd}(p)(i) \neq 0$ to $\text{index}(i) \in \text{bitset}(p(\text{oddpart}(i)))$.

We then split the proof into two cases:

1. **Proving $1 \leq i$**: 
   - We show this by proving $i \neq 0$ by contradiction.
   - Assume $i = 0$. Then we have $\text{index}(0) \in \text{bitset}(p(\text{oddpart}(0)))$.
   - By definition, $\text{index}(0) = 0$ and $\text{oddpart}(0) = 0$.
   - Since we know that $p(i) \neq 0 \Rightarrow i$ is odd, if $p(0) \neq 0$, then 0 would need to be odd, which is false.
   - Moreover, $\text{bitset}(0) = \{\}$ (the empty set).
   - Therefore, $\text{index}(0) \in \text{bitset}(p(\text{oddpart}(0)))$ is false, which contradicts our assumption.

2. **Proving $i \leq n$**:
   - From the lemma `BITSET_BOUND_LEMMA`, if $j \in \text{bitset}(m)$, then $2^j \leq m$.
   - Since $\text{index}(i) \in \text{bitset}(p(\text{oddpart}(i)))$, we have $2^{\text{index}(i)} \leq p(\text{oddpart}(i))$.
   - By the decomposition theorem `INDEX_ODDPART_DECOMPOSITION`, we know $i = 2^{\text{index}(i)} \cdot \text{oddpart}(i)$.
   - Therefore:
     - $i = 2^{\text{index}(i)} \cdot \text{oddpart}(i) \leq p(\text{oddpart}(i)) \cdot \text{oddpart}(i)$
     - By our assumption, $p(\text{oddpart}(i)) \cdot \text{oddpart}(i) \leq n$
     - Thus, by transitivity, $i \leq n$

### Mathematical insight
This theorem establishes support bounds for the `distinct_of_odd` function. It shows that if a function `p` satisfies certain properties (domain bound and mapping only to odd numbers), then the non-zero values of `distinct_of_odd(p)` are confined to the range $[1,n]$.

The theorem is useful in number-theoretic contexts, particularly when working with binary representations of integers and their decomposition into powers of 2 and odd factors. The construction involving `distinct_of_odd` appears to be related to manipulating the bit patterns of integers in a way that preserves certain properties.

The heart of the proof relies on the fact that any natural number has a unique decomposition as a power of 2 multiplied by an odd number, and exploits the relationship between this decomposition and the binary representation of numbers.

### Dependencies
**Theorems:**
- `BITSET_BOUND_LEMMA`: If $i \in \text{bitset}(n)$, then $2^i \leq n$
- `BITSET_0`: $\text{bitset}(0) = \{\}$ (empty set)
- `INDEX_ODDPART_DECOMPOSITION`: For any $n$, $n = 2^{\text{index}(n)} \cdot \text{oddpart}(n)$

**Definitions:**
- `bitset`: Defines $\text{bitset}(n)$ as the set of bit positions that are 1 in the binary representation of $n$
- `index`: The largest power of 2 that divides a number (or 0 if the number is 0)
- `oddpart`: The odd factor in the decomposition of a number as $2^k \cdot m$ where $m$ is odd (or 0 if the number is 0)
- `distinct_of_odd`: A function that outputs 1 if $\text{index}(i) \in \text{bitset}(p(\text{oddpart}(i)))$, and 0 otherwise

### Porting notes
When porting this theorem:
1. Ensure that the definitions of `bitset`, `index`, `oddpart`, and `distinct_of_odd` are properly translated first.
2. The proof relies heavily on the unique decomposition of integers as powers of 2 multiplied by odd numbers, so ensure that this decomposition is well-defined in the target system.
3. Be careful with the handling of edge cases, particularly around 0, as they are crucial to the proof.

---

## ODD_OF_DISTINCT_OF_ODD

### ODD_OF_DISTINCT_OF_ODD
- ODD_OF_DISTINCT_OF_ODD

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let ODD_OF_DISTINCT_OF_ODD = prove
 (`!p. (!i. ~(p(i) = 0) ==> ODD i)
       ==> odd_of_distinct (distinct_of_odd p) = p`,
  REWRITE_TAC[IN_ELIM_THM; odd_of_distinct; distinct_of_odd] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  ASM_SIMP_TAC[INDEX_ODDPART] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM BINARYSUM_BITSET] THEN
  REWRITE_TAC[binarysum] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ]);;
```

### Informal statement
For any function $p$ on natural numbers, if $p(i) \neq 0$ implies $i$ is odd for all $i$, then $\text{odd\_of\_distinct}(\text{distinct\_of\_odd}(p)) = p$.

In other words, if $p$ is zero on all even numbers, then applying the transformation $\text{distinct\_of\_odd}$ followed by $\text{odd\_of\_distinct}$ returns the original function $p$.

### Informal proof
The proof shows that the composition of the two transformations $\text{odd\_of\_distinct} \circ \text{distinct\_of\_odd}$ is the identity for functions that are zero on even numbers.

- First, we expand the definitions of `odd_of_distinct` and `distinct_of_odd`.
- We need to show that for all $i$, $(odd\_of\_distinct(distinct\_of\_odd(p)))(i) = p(i)$.
- Case 1: If $i$ is odd:
  - By definition, $odd\_of\_distinct$ at $i$ equals the binary sum of $j$ where $distinct\_of\_odd(p)(2^j \cdot i) = 1$.
  - Using `INDEX_ODDPART`, we know that for odd $m$, $\text{index}(2^i \cdot m) = i$ and $\text{oddpart}(2^i \cdot m) = m$.
  - This allows us to simplify the expression for $distinct\_of\_odd(p)$.
  - We apply `BINARYSUM_BITSET` which states that $\text{binarysum}(\text{bitset}(n)) = n$.
  - Through set extensions, we establish that the binary sum equals $p(i)$.
- Case 2: If $i$ is even:
  - By the hypothesis, $p(i) = 0$ for even $i$.
  - By definition, $odd\_of\_distinct(p)(i) = 0$ for even $i$.
  - Therefore, $(odd\_of\_distinct(distinct\_of\_odd(p)))(i) = 0 = p(i)$.

### Mathematical insight
This theorem establishes an important relationship between the functions `odd_of_distinct` and `distinct_of_odd`. These functions appear to be inverses of each other when restricted to the domain of functions that are zero on even numbers. 

The theorem is part of a broader context dealing with binary representations and odd/even number properties. The functions `distinct_of_odd` and `odd_of_distinct` provide a way to encode and decode information between different representations, where one focuses on distinct indices and the other on odd numbers.

This result is important for problems involving binary representation and parity, potentially in number theory applications or computational contexts where such transformations are needed.

### Dependencies
- **Theorems**:
  - `BINARYSUM_BITSET`: Establishes that `binarysum (bitset n) = n`
  - `INDEX_ODDPART`: For odd $m$, `index(2 EXP i * m) = i` and `oddpart(2 EXP i * m) = m`

- **Definitions**:
  - `binarysum`: Defined as `binarysum s = nsum s (λi. 2 EXP i)`
  - `odd_of_distinct`: Defined as `odd_of_distinct p = λi. if ODD i then nsum {j | p(2 EXP j * i) = 1} (λj. 2 EXP j) else 0`
  - `distinct_of_odd`: Defined as `distinct_of_odd p = λi. if (index i) IN bitset (p(oddpart i)) then 1 else 0`

### Porting notes
When porting this theorem to other systems:
- Ensure that the definitions of `odd_of_distinct` and `distinct_of_odd` are properly translated.
- The proof relies on properties of binary representation and parity, which should be available in most proof assistants.
- Pay attention to how set extensions and function equality are handled in the target system.
- The `bitset` function and its properties are crucial for this proof.

---

## DISTINCT_OF_ODD_OF_DISTINCT

### DISTINCT_OF_ODD_OF_DISTINCT
- DISTINCT_OF_ODD_OF_DISTINCT

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DISTINCT_OF_ODD_OF_DISTINCT = prove
 (`!p. (!i. ~(p i = 0) ==> 1 <= i /\ i <= n) /\ (!i. p(i) <= 1)
       ==> distinct_of_odd (odd_of_distinct p) = p`,
  REWRITE_TAC[distinct_of_odd; odd_of_distinct; IN_ELIM_THM] THEN
  REWRITE_TAC[partitions; ODD_ODDPART] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[BITSET_0; NOT_IN_EMPTY] THENL
   [ASM_MESON_TAC[ARITH_RULE `~(1 <= 0)`]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {j | p (2 EXP j * oddpart i) = 1}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..n` THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[LE_0] THEN
    MATCH_MP_TAC(ARITH_RULE `!x. y <= x /\ 1 <= x /\ x <= n ==> y <= n`) THEN
    EXISTS_TAC `2 EXP j * oddpart i` THEN ASM_SIMP_TAC[ARITH] THEN
    MATCH_MP_TAC(ARITH_RULE `j < ej /\ 1 * ej <= i * ej ==> j <= ej * i`) THEN
    REWRITE_TAC[LT_POW2_REFL; LE_MULT_RCANCEL] THEN
    ASM_MESON_TAC[ODD_ODDPART; ODD; ARITH_RULE `1 <= n <=> ~(n = 0)`];
    ASM_SIMP_TAC[BITSET_BINARYSUM; GSYM binarysum; IN_ELIM_THM] THEN
    REWRITE_TAC[GSYM INDEX_ODDPART_DECOMPOSITION] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
    ASM_MESON_TAC[ARITH_RULE `i <= 1 ==> i = 0 \/ i = 1`]]);;
```

### Informal statement
For any function $p$ where:
- For all $i$, if $p(i) \neq 0$, then $1 \leq i \leq n$
- For all $i$, $p(i) \leq 1$

Then $\text{distinct\_of\_odd}(\text{odd\_of\_distinct}(p)) = p$.

This theorem demonstrates that the functions `distinct_of_odd` and `odd_of_distinct` are inverses of each other when applied to a function $p$ that satisfies the given constraints (essentially a function that takes values 0 or 1, with non-zero values only for indices between 1 and n).

### Informal proof
We begin by expanding the definitions of `distinct_of_odd`, `odd_of_distinct`, and related concepts, and then proceed to show that the functions are inverses.

- First, we rewrite using the definitions of `distinct_of_odd`, `odd_of_distinct`, and related concepts. We also use the fact that `ODD(oddpart n) ⟺ n ≠ 0`.

- To show functional equality, we need to prove that for all indices $i$: $\text{distinct\_of\_odd}(\text{odd\_of\_distinct}(p))(i) = p(i)$.

- Case $i = 0$:
  - We know `BITSET_0` implies $\text{bitset}(0) = \emptyset$, and nothing is in the empty set.
  - From the constraint that if $p(i) \neq 0$, then $1 \leq i$, we conclude $p(0) = 0$.
  - Therefore, at $i = 0$, we have equality.

- Case $i \neq 0$:
  - First, we prove the set $\{j \mid p(2^j \cdot \text{oddpart}(i)) = 1\}$ is finite.
  - We show this set is a subset of $\{0, 1, ..., n\}$ by proving that if $p(2^j \cdot \text{oddpart}(i)) = 1$, then $j \leq n$.
  - This is established using properties of powers of 2, the oddpart function, and the constraints on $p$.

  - Next, we apply the identity `BITSET_BINARYSUM`: for a finite set $s$, $\text{bitset}(\text{binarysum}(s)) = s$.
  - We also use `INDEX_ODDPART_DECOMPOSITION`: $n = 2^{\text{index}(n)} \cdot \text{oddpart}(n)$.
  
  - Finally, since $p(i) \leq 1$ for all $i$, $p(i)$ is either 0 or 1.
  - We handle both cases and complete the proof showing that the function values match.

### Mathematical insight
This theorem establishes a bijection between two classes of functions:

1. Functions that map numbers to 0 or 1, with non-zero values only for indices between 1 and $n$
2. Functions that represent a specific way of encoding partitions using odd numbers

The functions `odd_of_distinct` and `distinct_of_odd` provide a way to transform between these representations. This is useful in combinatorics, particularly in counting problems related to partitions of integers.

The proof uses several key properties of binary representations and the decomposition of numbers into powers of 2 multiplied by odd components, which is a fundamental technique in number theory.

### Dependencies
#### Definitions
- `distinct_of_odd`: Maps a function to another function by checking if the index of a number is in the bitset of the function applied to the oddpart
- `odd_of_distinct`: Maps a function to another function by summing powers of 2 for certain indices
- `oddpart`: Extracts the odd factor of a number by dividing by 2 until odd
- `partitions`: Defines when a function represents a partition of a number
- `binarysum`: Computes the sum of powers of 2 indexed by elements of a set

#### Theorems
- `BITSET_0`: Establishes that the bitset of 0 is empty
- `BITSET_BINARYSUM`: Shows that bitset and binarysum are inverses for finite sets
- `INDEX_ODDPART_DECOMPOSITION`: Shows that every number can be decomposed as a power of 2 times an odd number
- `ODD_ODDPART`: Establishes that the oddpart of a number is odd iff the number is non-zero

### Porting notes
When porting this theorem, pay attention to:
1. The specific definitions of bitset, binarysum, index, and oddpart, which may have different implementations in other systems
2. The representation of functions as partitions, which might require additional setup in some proof assistants
3. The use of arithmetical reasoning about powers of 2 and odd numbers, which might require different tactics in other systems

---

## NSUM_DISTINCT_OF_ODD

### Name of formal statement
NSUM_DISTINCT_OF_ODD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NSUM_DISTINCT_OF_ODD = prove
 (`!p. (!i. ~(p i = 0) ==> 1 <= i /\ i <= n) /\
       (!i. p(i) * i <= n) /\
       (!i. ~(p(i) = 0) ==> ODD i)
       ==> nsum(1..n) (\i. distinct_of_odd p i * i) =
           nsum(1..n) (\i. p i * i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[distinct_of_odd] THEN
  GEN_REWRITE_TAC (RAND_CONV o BINDER_CONV o LAND_CONV)
   [GSYM BINARYSUM_BITSET] THEN
  REWRITE_TAC[binarysum] THEN REWRITE_TAC[GSYM NSUM_RMUL] THEN
  SIMP_TAC[NSUM_NSUM_PRODUCT; FINITE_BITSET; FINITE_NUMSEG] THEN
  CONV_TAC SYM_CONV THEN ONCE_REWRITE_TAC[GSYM NSUM_SUPPORT] THEN
  REWRITE_TAC[support; NEUTRAL_ADD] THEN
  SUBGOAL_THEN
   `{x | x IN {i,j | i IN 1..n /\ j IN bitset(p i)} /\
         ~((\(i,j). 2 EXP j * i) x = 0)} =
    {i,j | i IN 1..n /\ j IN bitset(p i)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_ELIM_THM] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[IN_NUMSEG; EXP_EQ_0; MULT_EQ_0; ARITH] THEN
    MESON_TAC[ARITH_RULE `~(1 <= 0)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN 1 .. n /\
         ~((if index x IN bitset (p (oddpart x)) then 1 else 0) * x = 0)} =
    {i | i IN 1..n /\ (index i) IN bitset (p(oddpart i))}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; MULT_EQ_0] THEN
    REWRITE_TAC[IN_NUMSEG; ARITH_RULE `(if p then 1 else 0) = 0 <=> ~p`] THEN
    MESON_TAC[ARITH_RULE `~(1 <= 0)`];
    ALL_TAC] THEN
  MATCH_MP_TAC NSUM_EQ_GENERAL THEN
  EXISTS_TAC `\(i,b). 2 EXP b * i` THEN
  SIMP_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[ARITH_RULE
   `(if p then 1 else 0) * x * y = (if p then x * y else 0)`] THEN
  GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV) [IN_ELIM_THM] THEN
  ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c <=> a /\ b /\ (b ==> c)`] THEN
  SIMP_TAC[] THEN REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
  REWRITE_TAC[FORALL_PAIR_THM; EXISTS_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG] THEN
  SUBGOAL_THEN `!i j. j IN bitset(p i) ==> ODD i` ASSUME_TAC THENL
   [ASM_MESON_TAC[BITSET_0; NOT_IN_EMPTY]; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `m:num` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`oddpart m`; `index m`] THEN
      ASM_REWRITE_TAC[GSYM INDEX_ODDPART_DECOMPOSITION] THEN
      ASM_MESON_TAC[ODDPART_LE; LE_TRANS; ARITH_RULE `1 <= x <=> ~(x = 0)`;
                    ODD_ODDPART; ODD];
      ASM_MESON_TAC[INDEX_ODDPART_UNIQUE]];
    MAP_EVERY X_GEN_TAC [`m:num`; `i:num`] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[INDEX_ODDPART]] THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`] THEN
      REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; ARITH] THEN
      ASM_MESON_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`];
      ASM_MESON_TAC[BITSET_BOUND_LEMMA; LE_MULT_RCANCEL; LE_TRANS]]]);;
```

### Informal statement
For any function $p: \mathbb{N} \to \mathbb{N}$ that satisfies:
1. For all $i$, if $p(i) \neq 0$, then $1 \leq i \leq n$.
2. For all $i$, $p(i) \cdot i \leq n$.
3. For all $i$, if $p(i) \neq 0$, then $i$ is odd.

Then:
$$\sum_{i=1}^{n} \operatorname{distinct\_of\_odd}(p)(i) \cdot i = \sum_{i=1}^{n} p(i) \cdot i$$

Where $\operatorname{distinct\_of\_odd}(p)(i) = \begin{cases} 1 & \text{if } \operatorname{index}(i) \in \operatorname{bitset}(p(\operatorname{oddpart}(i))) \\ 0 & \text{otherwise} \end{cases}$

### Informal proof
The proof establishes that the sums of $\operatorname{distinct\_of\_odd}(p)(i) \cdot i$ and $p(i) \cdot i$ over the range $1$ to $n$ are equal, using the following steps:

- We start by expanding the definition of $\operatorname{distinct\_of\_odd}$.

- We use the identity $\operatorname{binarysum}(\operatorname{bitset}(n)) = n$ to rewrite parts of the expression.

- The proof then manipulates nested sums and uses properties of $\operatorname{nsum}$, including $\operatorname{nsum}\_\operatorname{nsum}\_\operatorname{product}$ and $\operatorname{nsum}\_\operatorname{support}$.

- We establish the equality between two set expressions:
  * $\{x \mid x \in \{(i,j) \mid i \in 1..n \land j \in \operatorname{bitset}(p(i))\} \land (λ(i,j).\ 2^j \cdot i)(x) \neq 0\}$
  * $\{(i,j) \mid i \in 1..n \land j \in \operatorname{bitset}(p(i))\}$

- Similarly, we show:
  * $\{x \mid x \in 1..n \land ((\text{if } \operatorname{index}(x) \in \operatorname{bitset}(p(\operatorname{oddpart}(x))) \text{ then } 1 \text{ else } 0) \cdot x \neq 0)\}$
  * $= \{i \mid i \in 1..n \land \operatorname{index}(i) \in \operatorname{bitset}(p(\operatorname{oddpart}(i)))\}$

- We apply $\operatorname{NSUM\_EQ\_GENERAL}$ with the function $λ(i,b).\ 2^b \cdot i$ to establish our main result.

- The proof uses the index-oddpart decomposition: any number $m$ can be uniquely expressed as $m = 2^{\operatorname{index}(m)} \cdot \operatorname{oddpart}(m)$, where $\operatorname{oddpart}(m)$ is odd when $m \neq 0$.

- Throughout, we handle several cases involving the properties of odd numbers and the definitions of $\operatorname{index}$ and $\operatorname{oddpart}$.

### Mathematical insight
This theorem establishes an equality between two different ways of summing weighted values. The function $\operatorname{distinct\_of\_odd}$ essentially extracts a "binary signature" from arguments of $p$ using the bitset representation, the index of powers of 2, and odd parts of numbers.

The result is important for number theory applications where we need to transform sums involving odd numbers into equivalent forms using binary representation. It shows that under certain conditions, sums using the original weighting function $p$ can be replaced with sums using the transformation through $\operatorname{distinct\_of\_odd}$.

The key insight is that numbers can be uniquely decomposed as products of powers of 2 and odd numbers, a fundamental fact in number theory often used in binary and digital representations.

### Dependencies
- Theorems:
  - `BITSET_BOUND_LEMMA`: If $i \in \operatorname{bitset}(n)$, then $2^i \leq n$
  - `FINITE_BITSET`: The set $\operatorname{bitset}(n)$ is finite
  - `BITSET_0`: $\operatorname{bitset}(0) = \emptyset$
  - `BINARYSUM_BITSET`: $\operatorname{binarysum}(\operatorname{bitset}(n)) = n$
  - `INDEX_ODDPART_DECOMPOSITION`: $n = 2^{\operatorname{index}(n)} \cdot \operatorname{oddpart}(n)$
  - `ODD_ODDPART`: $\operatorname{oddpart}(n)$ is odd if and only if $n \neq 0$
  - `ODDPART_LE`: $\operatorname{oddpart}(n) \leq n$
  - `INDEX_ODDPART_UNIQUE`: If $m$ and $m'$ are odd, then $2^i \cdot m = 2^{i'} \cdot m'$ if and only if $i = i'$ and $m = m'$
  - `INDEX_ODDPART`: If $m$ is odd, then $\operatorname{index}(2^i \cdot m) = i$ and $\operatorname{oddpart}(2^i \cdot m) = m$

- Definitions:
  - `bitset n`: The set of indices $i$ such that the $i$-th bit of $n$ is 1 (where $\operatorname{ODD}(n \text{ DIV } 2^i)$)
  - `binarysum s`: The sum $\sum_{i \in s} 2^i$
  - `index n`: Number of factors of 2 in $n$
  - `oddpart n`: The odd part remaining when all factors of 2 are removed from $n$
  - `distinct_of_odd p`: Function that maps $i$ to 1 if $\operatorname{index}(i) \in \operatorname{bitset}(p(\operatorname{oddpart}(i)))$ and 0 otherwise

### Porting notes
When porting this theorem:
1. First implement the necessary binary representation functions (`bitset`, `binarysum`, `index`, `oddpart`).
2. Ensure your system has appropriate sum theory (finite sums over sets).
3. The proof relies heavily on HOL Light's set manipulation tactics and might need adaptation depending on how sets are handled in your system.
4. The binary decomposition of numbers is central to the proof - make sure your system has similar theorems about expressing numbers as products of powers of 2 and odd numbers.

---

## DISTINCT_OF_ODD

### Name of formal statement
DISTINCT_OF_ODD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DISTINCT_OF_ODD = prove
 (`!p. p IN {p | p partitions n /\ !i. ~(p(i) = 0) ==> ODD i}
       ==> (distinct_of_odd p) IN {p | p partitions n /\ !i. p(i) <= 1}`,
  GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM; partitions] THEN STRIP_TAC THEN
  REWRITE_TAC[DISTINCT_DISTINCT_OF_ODD] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUPPORT_DISTINCT_OF_ODD;
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC NSUM_DISTINCT_OF_ODD] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `(p:num->num) i = 0` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; LE_0] THEN
  ASM_MESON_TAC[NSUM_BOUND_LEMMA]);;
```

### Informal statement
For any function $p$ that is a partition of $n$ where all non-zero parts have odd indices (i.e., $p \in \{p \mid p \text{ partitions } n \wedge \forall i. p(i) \neq 0 \Rightarrow \text{ODD}(i)\}$), the function `distinct_of_odd p` is a partition of $n$ where all parts are at most 1 (i.e., `distinct_of_odd p` $\in \{p \mid p \text{ partitions } n \wedge \forall i. p(i) \leq 1\}$).

Here, a function $p$ partitions $n$ if:
1. The support of $p$ is contained in $\{1, 2, \ldots, n\}$ (i.e., $\forall i. p(i) \neq 0 \Rightarrow 1 \leq i \leq n$)
2. The sum $\sum_{i=1}^{n} p(i) \cdot i = n$

### Informal proof
The proof proceeds as follows:

- We start by rewriting the set membership notation into its explicit form using the definition of `partitions`.
- We use the theorem `DISTINCT_DISTINCT_OF_ODD` which states $\forall p, i. \text{distinct_of_odd}(p)(i) \leq 1$.
- We need to prove two conditions:
  1. The support condition: $\forall i. \text{distinct_of_odd}(p)(i) \neq 0 \Rightarrow 1 \leq i \leq n$. 
     This is established using the theorem `SUPPORT_DISTINCT_OF_ODD`.
  
  2. The sum condition: $\sum_{i=1}^{n} \text{distinct_of_odd}(p)(i) \cdot i = n$.
     For this, we use `NSUM_DISTINCT_OF_ODD`, which states that under our conditions:
     $\sum_{i=1}^{n} \text{distinct_of_odd}(p)(i) \cdot i = \sum_{i=1}^{n} p(i) \cdot i$
     
     Since $p$ partitions $n$, we already know that $\sum_{i=1}^{n} p(i) \cdot i = n$.

- For the case where $p(i) = 0$, we trivially have $p(i) \cdot i = 0 \leq n$.
- For the case where $p(i) \neq 0$, we use `NSUM_BOUND_LEMMA` to establish that $p(i) \cdot i \leq n$.

### Mathematical insight
This theorem establishes a transformation between two specific types of integer partitions:
1. Partitions where all non-zero parts have odd indices
2. Partitions where each part is at most 1 (i.e., distinct parts of size 1)

The function `distinct_of_odd` provides a bijection between these two partition classes. This is part of a broader mathematical result related to Euler's pentagonal number theorem and the study of partition functions. The transformation maps partitions with odd-indexed parts to partitions into distinct parts, maintaining the total sum.

The definition of `distinct_of_odd` uses the concepts of `oddpart` (extracting the odd part of a number) and `index` (extracting the power of 2) to decompose numbers and rearrange the partition in a specific way.

### Dependencies
- Definitions:
  - `partitions`: Definition of when a function represents an integer partition
  - `distinct_of_odd`: Definition of the transformation function

- Theorems:
  - `DISTINCT_DISTINCT_OF_ODD`: Shows that all values in the transformed partition are at most 1
  - `SUPPORT_DISTINCT_OF_ODD`: Ensures the support condition for the transformed partition
  - `NSUM_DISTINCT_OF_ODD`: Proves that the sum is preserved under the transformation
  - `NSUM_BOUND_LEMMA`: Used to establish bounds on individual terms in the sum

### Porting notes
When porting this theorem:
1. Ensure the underlying definitions of integer partitions are consistent with the target system
2. The `distinct_of_odd` function involves bit manipulation through `index`, `oddpart`, and `bitset` - these functions may need careful implementation in other systems
3. The proof relies heavily on properties of sums and integer partitions, which are likely to have different automation approaches in other systems

---

## ODD_OF_DISTINCT

### ODD_OF_DISTINCT
- ODD_OF_DISTINCT

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let ODD_OF_DISTINCT = prove
 (`!p. p IN {p | p partitions n /\ !i. p(i) <= 1}
       ==> (odd_of_distinct p) IN
           {p | p partitions n /\ !i. ~(p(i) = 0) ==> ODD i}`,
  GEN_TAC THEN REWRITE_TAC[partitions; IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[ODD_ODD_OF_DISTINCT] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SUPPORT_ODD_OF_DISTINCT]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `nsum(1..n) (\i. distinct_of_odd(odd_of_distinct p) i * i)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    AP_TERM_TAC THEN ABS_TAC THEN AP_THM_TAC THEN
    ASM_MESON_TAC[DISTINCT_OF_ODD_OF_DISTINCT]] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC NSUM_DISTINCT_OF_ODD THEN
  REWRITE_TAC[ODD_ODD_OF_DISTINCT] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SUPPORT_ODD_OF_DISTINCT]; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[odd_of_distinct] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LE_0; MULT_CLAUSES] THEN
  REWRITE_TAC[GSYM NSUM_RMUL] THEN
  SUBGOAL_THEN `FINITE {i:num | p(i) = 1}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `1..n` THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN
    ASM_MESON_TAC[ARITH_RULE `~(1 = 0)`];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM(REWRITE_CONV[o_DEF]
   `(\j. j) o (\j. 2 EXP j * i)`)] THEN
  ASM_SIMP_TAC[GSYM NSUM_IMAGE; INDEX_ODDPART_UNIQUE] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `nsum {i | p(i) = 1} (\j. j)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_SUBSET_SIMPLE THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `nsum {i | p(i) = 1} (\j. p(j) * j)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN MATCH_MP_TAC NSUM_EQ THEN
    SIMP_TAC[IN_ELIM_THM; MULT_CLAUSES];
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC NSUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN
    ASM_MESON_TAC[ARITH_RULE `~(1 = 0)`]]);;
```

### Informal statement
Let $p$ be a partition function such that $p \in \{p \mid p \text{ partitions } n \text{ and } \forall i, p(i) \leq 1\}$. Then $\text{odd\_of\_distinct}(p) \in \{p \mid p \text{ partitions } n \text{ and } \forall i, p(i) \neq 0 \implies i \text{ is odd}\}$.

Here, a partition function $p$ partitions $n$ if:
1. For all $i$ such that $p(i) \neq 0$, we have $1 \leq i \leq n$
2. $\sum_{i=1}^n p(i) \cdot i = n$

The function $\text{odd\_of\_distinct}$ is defined as:
$\text{odd\_of\_distinct}(p)(i) = \begin{cases} 
\sum_{j \in \{j \mid p(2^j \cdot i) = 1\}} 2^j & \text{if } i \text{ is odd} \\
0 & \text{otherwise}
\end{cases}$

### Informal proof
We need to show that if $p$ is a partition of $n$ with parts having multiplicity at most 1 (i.e., a distinct partition), then $\text{odd\_of\_distinct}(p)$ is a partition of $n$ with only odd parts.

The proof proceeds in several steps:

- First, we use the theorem `ODD_ODD_OF_DISTINCT` which establishes that for any non-zero value of $\text{odd\_of\_distinct}(p)(i)$, the index $i$ must be odd.

- For the partitioning aspect, we need to show two things:
  1. The support of $\text{odd\_of\_distinct}(p)$ is bounded by $n$ (which follows from `SUPPORT_ODD_OF_DISTINCT`)
  2. The sum $\sum_{i=1}^n \text{odd\_of\_distinct}(p)(i) \cdot i = n$

- For the second point, we employ a key transformation: we show that
  $\sum_{i=1}^n \text{distinct\_of\_odd}(\text{odd\_of\_distinct}(p))(i) \cdot i = \sum_{i=1}^n p(i) \cdot i$
  where $\text{distinct\_of\_odd}$ is the inverse transformation of $\text{odd\_of\_distinct}$.

- Using `DISTINCT_OF_ODD_OF_DISTINCT`, we establish that $\text{distinct\_of\_odd}(\text{odd\_of\_distinct}(p)) = p$ under our conditions.

- We apply `NSUM_DISTINCT_OF_ODD` to establish that 
  $\sum_{i=1}^n \text{distinct\_of\_odd}(\text{odd\_of\_distinct}(p))(i) \cdot i = \sum_{i=1}^n \text{odd\_of\_distinct}(p)(i) \cdot i$

- For the last part, we need to show that $\text{odd\_of\_distinct}(p)(i) \cdot i \leq n$ for all $i$. This is done by:
  1. Using the definition of $\text{odd\_of\_distinct}$
  2. For odd $i$, converting summations and applying several numeric inequalities
  3. Showing the sum is bounded by the running sum of integers where $p(i)=1$
  4. Applying transitivity of $\leq$ to establish the bound

This completes the proof that $\text{odd\_of\_distinct}(p)$ is a valid partition with only odd parts.

### Mathematical insight
This theorem establishes a bijection between partitions with distinct parts and partitions with odd parts. Given a partition with distinct parts (where each part appears at most once), the `odd_of_distinct` function constructs a corresponding partition with only odd parts.

The transformation works by decomposing each number as $2^j \times i$ where $i$ is odd, and grouping the powers of 2 in a clever way. This result is part of Euler's famous theorem that the number of partitions with distinct parts equals the number of partitions with odd parts.

The bijection transforms the constraint "parts must be distinct" into the constraint "parts must be odd," which demonstrates a fundamental relationship in partition theory and number theory.

### Dependencies
- Theorems:
  - `ODD_ODD_OF_DISTINCT`: Shows that non-zero values in the result of `odd_of_distinct` correspond to odd indices.
  - `SUPPORT_ODD_OF_DISTINCT`: Establishes bounds on the support of `odd_of_distinct`.
  - `DISTINCT_OF_ODD_OF_DISTINCT`: Shows that `distinct_of_odd` is the inverse of `odd_of_distinct`.
  - `NSUM_DISTINCT_OF_ODD`: Relates sums involving `distinct_of_odd` to the original sums.
  - `INDEX_ODDPART_UNIQUE`: Provides uniqueness for the index-oddpart decomposition.

- Definitions:
  - `partitions`: Defines when a function partitions a number.
  - `odd_of_distinct`: Transforms a distinct partition into an odd partition.
  - `distinct_of_odd`: Transforms an odd partition into a distinct partition.

### Porting notes
When porting this theorem:
1. First implement the necessary number theory background, particularly around partitions and odd/even number properties.
2. Carefully implement the transformations `odd_of_distinct` and `distinct_of_odd`.
3. The proof relies heavily on manipulating finite sums, so ensure your target system has good support for sum operations.
4. The numerical decomposition into powers of 2 times odd numbers is a key insight - ensure this decomposition is properly formalized.
5. This result is part of a bigger theory about partition bijections, so consider porting related theorems together.

---

## EULER_PARTITION_THEOREM

### Name of formal statement
EULER_PARTITION_THEOREM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_PARTITION_THEOREM = prove
 (`FINITE {p | p partitions n /\ !i. p(i) <= 1} /\
   FINITE {p | p partitions n /\ !i. ~(p(i) = 0) ==> ODD i} /\
   CARD {p | p partitions n /\ !i. p(i) <= 1} =
   CARD {p | p partitions n /\ !i. ~(p(i) = 0) ==> ODD i}`,
  MATCH_MP_TAC CARD_EQ_LEMMA THEN REWRITE_TAC[FINITE_SUBSET_PARTITIONS] THEN
  MAP_EVERY EXISTS_TAC [`odd_of_distinct`; `distinct_of_odd`] THEN
  REWRITE_TAC[ODD_OF_DISTINCT; DISTINCT_OF_ODD] THEN
  CONJ_TAC THEN X_GEN_TAC `p:num->num` THEN
  REWRITE_TAC[IN_ELIM_THM; partitions] THEN STRIP_TAC THENL
   [MATCH_MP_TAC DISTINCT_OF_ODD_OF_DISTINCT;
    MATCH_MP_TAC ODD_OF_DISTINCT_OF_ODD] THEN
  ASM_REWRITE_TAC[]);;
```

### Informal statement
Euler's Partition Theorem states that for any natural number $n$:

1. The set of partitions of $n$ into distinct parts (where each part appears at most once) is finite.
2. The set of partitions of $n$ into odd parts (where each part is an odd number) is finite.
3. The cardinality of these two sets is equal.

More formally:
$|\{p \mid p \text{ partitions } n \land \forall i. p(i) \leq 1\}| = |\{p \mid p \text{ partitions } n \land \forall i. p(i) \neq 0 \Rightarrow \text{ODD}(i)\}|$

where $p$ partitions $n$ means that:
- $p$ is a function from natural numbers to natural numbers
- All non-zero values of $p$ are at indices between 1 and $n$ inclusive
- The sum $\sum_{i=1}^{n} p(i) \cdot i = n$

### Informal proof
The proof establishes a bijection between the two sets of partitions, which implies that they have the same cardinality.

- We apply the `CARD_EQ_LEMMA` which states that if two finite sets have bijections between them, then they have the same cardinality.
- We first establish that both sets are finite using the theorem `FINITE_SUBSET_PARTITIONS`.
- We define the bijection using two functions:
  * `odd_of_distinct` which maps partitions with distinct parts to partitions with odd parts
  * `distinct_of_odd` which maps partitions with odd parts to partitions with distinct parts
- We prove that these functions map elements from one set to the other using the theorems `ODD_OF_DISTINCT` and `DISTINCT_OF_ODD`.
- Finally, we show that these functions are inverses of each other:
  * For any partition `p` with distinct parts, `distinct_of_odd(odd_of_distinct(p)) = p` using `DISTINCT_OF_ODD_OF_DISTINCT`.
  * For any partition `p` with odd parts, `odd_of_distinct(distinct_of_odd(p)) = p` using `ODD_OF_DISTINCT_OF_ODD`.

This establishes a bijection between the two sets of partitions, proving that they have the same cardinality.

### Mathematical insight
Euler's Partition Theorem is a fundamental result in number theory and combinatorics. It establishes a surprising connection between two seemingly unrelated properties of partitions:

1. Partitions with distinct parts (where no number appears more than once)
2. Partitions with only odd parts (where every part is an odd number)

For example, the partitions of 4 with distinct parts are:
- 4
- 3+1
- 2+1+1 (not valid as 1 appears twice)
- 1+1+1+1 (not valid as 1 appears four times)

The partitions of 4 with odd parts are:
- 3+1
- 1+1+1+1

Both sets have exactly 2 members.

The theorem provides insight into the intricate structure of partitions and has connections to generating functions and other areas of mathematics. The bijection between these two types of partitions can be elegantly explained using binary representations of numbers and is related to Euler's pentagonal number theorem.

### Dependencies
- Definitions:
  - `partitions`: Defines when a function represents a partition of a number
  - `odd_of_distinct`: Function that maps partitions with distinct parts to partitions with odd parts
  - `distinct_of_odd`: Function that maps partitions with odd parts to partitions with distinct parts

- Theorems:
  - `CARD_EQ_LEMMA`: Theorem about equality of cardinalities
  - `FINITE_SUBSET_PARTITIONS`: Shows that subsets of partitions are finite
  - `ODD_OF_DISTINCT`: Shows that `odd_of_distinct` maps to partitions with odd parts
  - `DISTINCT_OF_ODD`: Shows that `distinct_of_odd` maps to partitions with distinct parts
  - `DISTINCT_OF_ODD_OF_DISTINCT`: Shows that `distinct_of_odd ∘ odd_of_distinct` is identity
  - `ODD_OF_DISTINCT_OF_ODD`: Shows that `odd_of_distinct ∘ distinct_of_odd` is identity

### Porting notes
When porting this theorem:
1. First define the concept of a partition of a number, which may require formalizing multisets or functions with finite support.
2. Define the bijections between partitions with distinct parts and partitions with odd parts.
3. The proof relies heavily on these bijections being inverses of each other, which may require careful handling of the binary representations of numbers.
4. The implementation of `odd_of_distinct` and `distinct_of_odd` involves binary operations that might need special attention in the target system.

---

