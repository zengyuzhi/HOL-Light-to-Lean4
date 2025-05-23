# liouville.ml

## Overview

Number of statements: 22

This file formalizes the Liouville approximation theorem, which establishes bounds on how closely algebraic numbers can be approximated by rational numbers. It builds on floor functions and polynomial theory from the imported modules to develop the necessary machinery for proving Liouville's theorem. The file likely includes definitions of algebraic numbers, formalization of their approximation properties, and the main theorem showing that transcendental numbers can be better approximated by rationals than algebraic numbers.

## algebraic

### Name of formal statement
algebraic

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let algebraic = new_definition
 `algebraic(x) <=> ?p. ALL integer p /\ ~(poly p = poly []) /\ poly p x = &0`;;
```

### Informal statement
A real number $x$ is algebraic if there exists a non-zero polynomial $p$ with integer coefficients such that $p(x) = 0$.

Formally:
$$\text{algebraic}(x) \iff \exists p. \text{integer}(p) \land \lnot(p = []) \land p(x) = 0$$

Where:
- $\text{integer}(p)$ indicates that the polynomial $p$ has integer coefficients
- $\lnot(p = [])$ ensures that $p$ is not the zero polynomial (empty list of coefficients)
- $p(x) = 0$ means that $x$ is a root of the polynomial $p$

### Informal proof
This is a definition rather than a theorem, so there is no proof.

### Mathematical insight
This definition formalizes the standard mathematical concept of algebraic numbers - those that are roots of non-zero polynomials with integer coefficients. 

The complement of the set of algebraic numbers is the set of transcendental numbers, which are real numbers that are not algebraic. Famous examples of transcendental numbers include $\pi$ and $e$.

Algebraic numbers are fundamental in number theory and algebra. They form a countable set, while transcendental numbers are uncountable. This definition serves as the foundation for proving various properties of algebraic and transcendental numbers, including Liouville's theorem on the approximation of algebraic numbers by rationals.

### Dependencies
None specified in the provided dependency list.

### Porting notes
When porting this definition:
- Ensure that the target system has a suitable representation of polynomials with integer coefficients.
- The `poly` function in HOL Light evaluates a polynomial at a given point.
- Consider how the target system handles the evaluation of polynomials, as this might require additional setup.
- The notation `&0` in HOL Light represents the real number 0, so ensure proper type conversion in the target system.

---

## transcendental

### Name of formal statement
transcendental

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let transcendental = new_definition
 `transcendental(x) <=> ~(algebraic x)`;;
```

### Informal statement
A real number $x$ is transcendental if and only if it is not algebraic.

In mathematical notation:
$$\text{transcendental}(x) \iff \neg\text{algebraic}(x)$$

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
The definition introduces the concept of transcendental numbers as the complement of algebraic numbers within the real number system. Algebraic numbers are those that are roots of non-zero polynomial equations with integer coefficients. Therefore, transcendental numbers cannot be expressed as solutions to such equations.

This is a fundamental distinction in number theory. While algebraic numbers form a countable set, transcendental numbers form an uncountable set. Famous examples of transcendental numbers include $\pi$ and $e$. The transcendence of these numbers was historically significant and difficult to prove.

This definition establishes a clear binary classification of all real numbers: every real number is either algebraic or transcendental, and no number can be both.

### Dependencies
- Definitions:
  - `algebraic`: The definition of an algebraic number, which this definition complements.

### Porting notes
When porting this definition to other proof assistants:
- Ensure that the `algebraic` predicate is already defined
- This definition is straightforward and should translate directly to any system that supports negation and has a notion of algebraic numbers
- No special handling necessary as this is a simple negation-based definition

---

## REAL_INTEGER_EQ_0

### Name of formal statement
REAL_INTEGER_EQ_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_INTEGER_EQ_0 = prove
 (`!x. integer x /\ abs(x) < &1 ==> x = &0`,
  MESON_TAC[REAL_ABS_INTEGER_LEMMA; REAL_NOT_LE]);;
```

### Informal statement
For any real number $x$, if $x$ is an integer and $|x| < 1$, then $x = 0$.

### Informal proof
The proof uses the theorem `REAL_ABS_INTEGER_LEMMA`, which states that for any integer $x$, if $x \neq 0$, then $|x| \geq 1$.

By contrapositive reasoning, if $x$ is an integer and $|x| < 1$, then $x$ must be 0. This follows because:
- If $x$ were non-zero, then by `REAL_ABS_INTEGER_LEMMA`, we would have $1 \leq |x|$
- But this contradicts our assumption that $|x| < 1$
- The `REAL_NOT_LE` theorem is used to formalize this contradiction

Therefore, $x = 0$ is the only possibility.

### Mathematical insight
This theorem formalizes the basic property that the smallest positive integer is 1, and thus any integer with absolute value less than 1 must be 0. This is a fundamental property of integers that is often used in number theory and analysis when reasoning about integer values.

The statement provides a simple criterion for determining when an integer must be zero based on its absolute value.

### Dependencies
#### Theorems
- `REAL_ABS_INTEGER_LEMMA`: If $x$ is an integer and $x \neq 0$, then $|x| \geq 1$
- `REAL_NOT_LE`: Used to handle contradictions involving real number inequalities

### Porting notes
This theorem should be straightforward to port to other proof assistants as it relies on basic properties of integers and absolute values. The main requirement is having a definition of "integer" as a property of real numbers (as opposed to a distinct type) and the standard properties of absolute value.

---

## FACT_LE_REFL

### Name of formal statement
FACT_LE_REFL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FACT_LE_REFL = prove
 (`!n. n <= FACT n`,
  INDUCT_TAC THEN REWRITE_TAC[FACT; ARITH] THEN
  MATCH_MP_TAC(ARITH_RULE `x * 1 <= a ==> x <= a`) THEN
  REWRITE_TAC[LE_MULT_LCANCEL; NOT_SUC; FACT_LT;
              ARITH_RULE `1 <= n <=> 0 < n`]);;
```

### Informal statement
For all natural numbers $n$, we have:
$$n \leq n!$$

### Informal proof
We prove this by induction on $n$.

**Base case**: When $n = 0$, we need to show $0 \leq 0!$. Since $0! = 1$ by definition, and $0 \leq 1$ is true arithmetically, the base case holds.

**Inductive case**: Assume $n \leq n!$ for some natural number $n$. We need to show that $(n+1) \leq (n+1)!$.

By definition, $(n+1)! = (n+1) \cdot n!$

To prove the result, it suffices to show that $(n+1) \leq (n+1) \cdot n!$.

This can be rewritten as showing that $(n+1) \cdot 1 \leq (n+1) \cdot n!$, which follows if $1 \leq n!$.

For $n \geq 1$, we know that $n! > 0$, so $1 \leq n!$ holds when $n \geq 1$.

Since $n+1 \geq 1$ for all natural numbers $n$, we have $1 \leq n!$, which completes the proof.

### Mathematical insight
This theorem establishes a fundamental property of the factorial function: any natural number is less than or equal to its factorial. This is intuitive because factorial grows very quickly - each number multiplies all previous numbers.

The theorem is simple but useful in various combinatorial contexts where factorial appears in the denominator of expressions (like in combinations or permutations), as it helps establish certain inequalities.

### Dependencies
No explicit dependencies are listed, but the proof relies on:
- The definition of `FACT` (factorial)
- Basic arithmetic (`ARITH`) theorems
- The fact that factorial is positive for positive arguments (`FACT_LT`)

### Porting notes
This theorem is straightforward to port to other systems since factorial is a standard function in most mathematical libraries. The proof is a simple induction argument with basic arithmetic reasoning.

---

## EXP_LE_REFL

### Name of formal statement
EXP_LE_REFL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EXP_LE_REFL = prove
 (`!a. 1 < a ==> !n. n <= a EXP n`,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC[EXP; ARITH] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
   `n <= x ==> 1 * x < y ==> SUC n <= y`)) THEN
  REWRITE_TAC[LT_MULT_RCANCEL; EXP_EQ_0] THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;
```

### Informal statement
For all $a > 1$ and for all natural numbers $n$, we have $n \leq a^n$.

### Informal proof
The proof proceeds by induction on $n$:

* **Base case** ($n = 0$): 
  We need to show $0 \leq a^0$. By definition of exponential, $a^0 = 1$, and since $0 \leq 1$, the base case holds.

* **Inductive step**: 
  Assume $n \leq a^n$ holds for some $n$. We need to show that $(n+1) \leq a^{n+1}$.
  
  By definition of exponentiation, $a^{n+1} = a \cdot a^n$.
  
  Using the induction hypothesis $n \leq a^n$ and the assumption $1 < a$, we have:
  $1 \cdot a^n < a \cdot a^n = a^{n+1}$. 
  
  Since $1 \cdot a^n = a^n$, this means $a^n < a^{n+1}$.
  
  From the induction hypothesis $n \leq a^n$ and $a^n < a^{n+1}$, we can conclude that $n+1 \leq a^{n+1}$.

### Mathematical insight
This theorem establishes a fundamental property of exponential functions: for bases greater than 1, the exponential function $a^n$ grows faster than the identity function $n$. This is a basic result that helps establish the asymptotic growth rate of exponential functions compared to polynomials.

The intuition is straightforward: when $a > 1$, each multiplication by $a$ increases the value by more than just adding 1, so the exponentiation $a^n$ will always exceed or equal the exponent $n$ itself.

### Dependencies
- Theorems:
  - `EXP`: Definition of exponentiation
  - `ARITH`: Arithmetic reasoning
  - `LT_MULT_RCANCEL`: Cancellation law for multiplication with strict inequality
  - `EXP_EQ_0`: Condition for when exponential equals zero

### Porting notes
This theorem should be straightforward to port to other systems. The proof uses standard induction on natural numbers and basic properties of exponentiation and inequalities.

---

## MVT_INEQ

### Name of formal statement
MVT_INEQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MVT_INEQ = prove
 (`!f f' a d M.
        &0 < M /\ &0 < d /\
        (!x. abs(x - a) <= d ==> (f diffl f'(x)) x /\ abs(f' x) < M)
        ==> !x. abs(x - a) <= d ==> abs(f x - f a) < M * d`,
  REWRITE_TAC[TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  REPEAT STRIP_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (REAL_ARITH `x = a \/ x < a \/ a < x`)
  THENL
   [ASM_SIMP_TAC[REAL_SUB_REFL; REAL_ABS_NUM; REAL_LT_MUL];
    MP_TAC(SPECL [`f:real->real`; `f':real->real`; `x:real`; `a:real`]
                 MVT_ALT);
    MP_TAC(SPECL [`f:real->real`; `f':real->real`; `a:real`; `x:real`]
                 MVT_ALT)] THEN
  (ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC;
     ALL_TAC]) THEN
  STRIP_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ABS_SUB]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `d * abs(f'(z:real))` THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_RMUL;
     MATCH_MP_TAC REAL_LT_LMUL THEN
     ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC]) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC);;
```

### Informal statement
For any function $f: \mathbb{R} \to \mathbb{R}$ with derivative $f'$, if there exist positive real numbers $M > 0$ and $d > 0$ such that for all $x$ with $|x - a| \leq d$:
1. $f$ is differentiable at $x$ with derivative $f'(x)$
2. $|f'(x)| < M$

Then for all $x$ with $|x - a| \leq d$:
$|f(x) - f(a)| < M \cdot d$

This simply means that if a function has bounded derivative in a neighborhood, then the function's change is bounded by the derivative bound times the size of the neighborhood.

### Informal proof
The proof begins by breaking down the goal and separating it into cases based on the relationship between $x$ and $a$:

* **Case 1**: $x = a$
  
  If $x = a$, then $f(x) - f(a) = 0$, so $|f(x) - f(a)| = 0 < M \cdot d$ since $M > 0$ and $d > 0$.

* **Case 2**: $x < a$
  
  Apply the Mean Value Theorem (specifically `MVT_ALT`) to $f$ on the interval $[x, a]$. The theorem guarantees there exists a point $z \in (x, a)$ such that:
  $f(x) - f(a) = f'(z) \cdot (x - a)$

  Since $z$ is between $x$ and $a$, we have $|z - a| \leq d$, so $|f'(z)| < M$ by our assumptions.

  Therefore:
  $|f(x) - f(a)| = |f'(z) \cdot (x - a)| = |f'(z)| \cdot |x - a| < M \cdot |x - a| \leq M \cdot d$

  The last inequality holds because $|x - a| \leq d$ by assumption.

* **Case 3**: $a < x$
  
  Apply Mean Value Theorem to $f$ on the interval $[a, x]$ to get a point $z \in (a, x)$ such that:
  $f(x) - f(a) = f'(z) \cdot (x - a)$
  
  Similar to Case 2, since $z$ is between $a$ and $x$, we have $|z - a| \leq d$, so:
  $|f(x) - f(a)| = |f'(z)| \cdot |x - a| < M \cdot |x - a| \leq M \cdot d$

Thus, in all cases we have $|f(x) - f(a)| < M \cdot d$.

### Mathematical insight
This theorem provides a quantitative bound on the change of a function in terms of the bounds on its derivative. It is essentially an inequality form of the Mean Value Theorem. While the standard Mean Value Theorem establishes the existence of a point where the derivative equals the average rate of change, this result provides a practical bound that is useful in many applications, including:

1. Error estimation in numerical methods
2. Proofs of function approximation
3. Establishing Lipschitz continuity

The theorem is particularly useful in analysis when we need to bound the difference between function values. It can be viewed as a special case of the more general Lipschitz property of functions with bounded derivatives.

### Dependencies
- `MVT_ALT`: Mean Value Theorem (alternate formulation)
- Standard HOL Light tactics and theorems for real arithmetic

### Porting notes
When porting this theorem, ensure that:
1. The Mean Value Theorem is already available in your target system
2. The target system can handle the case-splitting approach based on the relative positions of points
3. Care should be taken with how absolute value is defined and applied in the target system

---

## POLY_MULTIPLE_INTEGER

### Name of formal statement
POLY_MULTIPLE_INTEGER

### Type of the formal statement
theorem

### Formal Content
```ocaml
let POLY_MULTIPLE_INTEGER = prove
 (`!p q l. ALL integer l ==> integer(&q pow (LENGTH l) * poly l (&p / &q))`,
  GEN_TAC THEN GEN_TAC THEN ASM_CASES_TAC `q = 0` THENL
   [LIST_INDUCT_TAC THEN REWRITE_TAC[poly; REAL_MUL_RZERO; INTEGER_CLOSED] THEN
    ASM_REWRITE_TAC[LENGTH; real_pow; REAL_MUL_LZERO; INTEGER_CLOSED];
    ALL_TAC] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[poly; REAL_MUL_RZERO; INTEGER_CLOSED] THEN
  REWRITE_TAC[LENGTH; real_pow; ALL] THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_ARITH
   `(q * qp) * (h + pq * pol) = q * h * qp + (q * pq) * (qp * pol)`] THEN
  ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ] THEN
  MATCH_MP_TAC(el 1 (CONJUNCTS INTEGER_CLOSED)) THEN
  ASM_SIMP_TAC[INTEGER_CLOSED]);;
```

### Informal statement
For all polynomials with integer coefficients represented by list `l`, and for all integers `p` and `q` where `q ≠ 0`, the product of `q^(LENGTH l)` and the evaluation of the polynomial at the rational value `p/q` is an integer.

In mathematical notation:
$$\forall p, q, l. (\forall a \in l. \text{integer}(a)) \implies \text{integer}(q^{|l|} \cdot \text{poly}(l, p/q))$$

where `poly(l,x)` represents the evaluation of the polynomial with coefficients in list `l` at the point `x`.

### Informal proof
The proof proceeds by induction on the list `l` of coefficients:

* Case: `q = 0`
  - This is a special case handled separately
  - For the empty list, `poly [] (p/0) = 0`, which is an integer
  - For non-empty lists, the result evaluates to 0 due to the `REAL_MUL_LZERO` property, which is also an integer

* Case: `q ≠ 0` (main case)
  - Base case (empty list): `poly [] (p/q) = 0`, which is trivially an integer when multiplied by `q^0 = 1`
  
  - Inductive step: For a list `h::t` where `h` is an integer and all elements of `t` are integers
    - By definition, `poly (h::t) x = h + x * poly t x`
    - So `poly (h::t) (p/q) = h + (p/q) * poly t (p/q)`
    - We need to show `q^(LENGTH (h::t)) * poly (h::t) (p/q)` is an integer
    - This expands to `q^(1+LENGTH t) * (h + (p/q) * poly t (p/q))`
    - Simplifying: `q * q^(LENGTH t) * h + q^(LENGTH t) * p * poly t (p/q)`
    - The first term is an integer because `h` is an integer and integers are closed under multiplication
    - For the second term, by the induction hypothesis, `q^(LENGTH t) * poly t (p/q)` is an integer
    - Since `p` is an integer and integers are closed under multiplication, the second term is also an integer
    - By integer closure under addition, the sum is an integer

The proof relies heavily on the closure properties of integers under basic arithmetic operations, as encapsulated in the `INTEGER_CLOSED` theorem.

### Mathematical insight
This theorem establishes an important property about polynomial evaluation at rational points. When evaluating a polynomial with integer coefficients at a rational point `p/q`, multiplying the result by `q^n` (where `n` is the degree of the polynomial plus one, or the length of the coefficient list) always yields an integer.

This result is related to the concept of "clearing denominators" in polynomial algebra. It shows that while evaluating a polynomial with integer coefficients at a rational point may give a rational result, there is a simple integer multiple that clears all the denominators.

This property has applications in number theory, algebraic geometry, and computational algebra, particularly when studying the behavior of polynomials over different number fields.

### Dependencies
- `INTEGER_CLOSED`: States that integers are closed under various operations including addition, subtraction, multiplication, and exponentiation.

### Porting notes
When porting this theorem to other systems:
- Make sure the target system has a proper representation of polynomials or a similar construct to `poly` in HOL Light
- The definition of `poly` in HOL Light represents a polynomial as a list of coefficients, where evaluation follows the "Horner scheme"
- The proof relies on induction over lists, so ensure the target system supports similar induction principles
- The representation of integers might differ between systems; some may use natural numbers with signs, while others have built-in integer types

---

## SEPARATE_FINITE_SET

### Name of formal statement
SEPARATE_FINITE_SET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SEPARATE_FINITE_SET = prove
 (`!a s. FINITE s
         ==> ~(a IN s) ==> ?d. &0 < d /\ !x. x IN s ==> d <= abs(x - a)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
  CONJ_TAC THENL [MESON_TAC[REAL_LT_01]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `min d (abs(x - a))` THEN
  ASM_REWRITE_TAC[REAL_MIN_LE; REAL_LT_MIN; GSYM REAL_ABS_NZ; REAL_SUB_0] THEN
  ASM_MESON_TAC[REAL_LE_REFL]);;
```

### Informal statement
For any point $a$ and finite set $s$, if $a \notin s$, then there exists a positive real number $d > 0$ such that for all points $x \in s$, the distance between $x$ and $a$ is at least $d$, i.e., $d \leq |x - a|$.

### Informal proof
The proof proceeds by strong induction on the finite set $s$:

* **Base case**: When $s$ is empty, the premise $a \notin s$ is trivially satisfied, and we can choose any positive value for $d$ (such as 1).

* **Inductive step**: Assume the theorem holds for a finite set $s$, and we need to prove it for $s \cup \{x\}$ where $x \notin s$.
  * Given that $a \notin s \cup \{x\}$, we know $a \neq x$ and $a \notin s$.
  * By the induction hypothesis, there exists $d > 0$ such that for all points in $s$, we have $d \leq |y - a|$.
  * Since $a \neq x$, we have $|x - a| > 0$.
  * We choose the new separation value as $\min(d, |x - a|)$, which is positive because both $d$ and $|x - a|$ are positive.
  * This value satisfies our requirement: for any point in $s \cup \{x\}$, the distance from $a$ is at least $\min(d, |x - a|)$.

### Mathematical insight
This theorem establishes an important property about the separation between a point and a finite set: if a point is not in a finite set, there is a minimum positive distance between the point and the set. This is a fundamental result in metric spaces that doesn't hold for infinite sets in general.

The theorem is particularly useful in analysis when reasoning about isolated points, neighborhoods, or when constructing functions that behave differently near specific points versus away from them. In the context of the HOL Light library, the comment suggests this is used for reasoning about root-free zones around a point.

### Dependencies
This theorem uses basic properties of real numbers and set theory, including:
- Finite set induction
- Properties of absolute value and minimum
- Basic real number inequalities

### Porting notes
This theorem should be straightforward to port to other proof assistants. The key requirements are:
- A notion of finite sets and induction on finite sets
- Real number theory with absolute value and minimum operations
- Basic set operations (membership, insertion)

In systems with a more developed library of metric space properties, this might be derivable from more general results about the minimum distance between a point and a closed set.

---

## POLY_ROOT_SEPARATE_LE

### Name of formal statement
POLY_ROOT_SEPARATE_LE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let POLY_ROOT_SEPARATE_LE = prove
 (`!p x. poly p x = &0 /\ ~(poly p = poly [])
         ==> ?d. &0 < d /\
                 !x'. &0 < abs(x' - x) /\ abs(x' - x) < d
                      ==> ~(poly p x' = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `{x | poly p x = &0} DELETE x`]
    SEPARATE_FINITE_SET) THEN
  ASM_SIMP_TAC[POLY_ROOTS_FINITE_SET; FINITE_DELETE; IN_DELETE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[GSYM REAL_ABS_NZ; REAL_SUB_0] THEN MESON_TAC[REAL_NOT_LT]);;
```

### Informal statement
For any polynomial $p$ and real number $x$, if $x$ is a root of $p$ (i.e., $p(x) = 0$) and $p$ is not the zero polynomial (i.e., $p \neq []$), then there exists a positive real number $d > 0$ such that for all $x'$ satisfying $0 < |x' - x| < d$, we have $p(x') \neq 0$.

In other words, every root of a non-zero polynomial is isolated - there exists a neighborhood around the root in which no other roots of the polynomial exist.

### Informal proof
Let $p$ be a polynomial and $x$ be a real number such that $p(x) = 0$ and $p$ is not the zero polynomial.

We need to prove that there exists a positive distance $d$ such that any point $x'$ within distance $d$ of $x$ (but not equal to $x$) is not a root of $p$.

The proof proceeds as follows:
- We apply the theorem `SEPARATE_FINITE_SET` to the point $x$ and the set $\{y \mid p(y) = 0\} \setminus \{x\}$, which represents all roots of $p$ except $x$ itself.
- This set is finite by the theorem `POLY_ROOTS_FINITE_SET` (since $p$ is not the zero polynomial).
- The `SEPARATE_FINITE_SET` theorem tells us that there exists a positive distance $d$ such that every element in the set $\{y \mid p(y) = 0\} \setminus \{x\}$ is at least distance $d$ away from $x$.
- Therefore, any point $x'$ with $0 < |x' - x| < d$ cannot be in the set $\{y \mid p(y) = 0\} \setminus \{x\}$.
- This means that for all $x'$ with $0 < |x' - x| < d$, we have $p(x') \neq 0$.

### Mathematical insight
This theorem establishes an important property of polynomial roots: they are isolated points. Each root of a non-zero polynomial has a neighborhood containing no other roots of the same polynomial. This property distinguishes polynomials from more general analytic functions, which can have accumulation points of zeros.

The result is fundamental in polynomial theory and has many applications, including:
1. Ensuring well-behavior of algorithms that need to isolate or approximate polynomial roots
2. Supporting the theory of multiplicity of roots
3. Contributing to the foundations of complex analysis (when extended to complex polynomials)

This isolation property is closely related to the fact that non-zero polynomials have finitely many roots, which is used directly in the proof.

### Dependencies
- `SEPARATE_FINITE_SET`: A theorem stating that for any point and a finite set not containing that point, there exists a positive distance such that no point in the set is within that distance of the given point.
- `POLY_ROOTS_FINITE_SET`: The theorem that the set of roots of a non-zero polynomial is finite.
- Various basic tactics and conversions from HOL Light's standard library.

### Porting notes
When porting this theorem to other systems:
- Ensure that the polynomial representation in the target system is compatible with HOL Light's `poly` function.
- The representation of polynomials may differ between systems (e.g., list of coefficients vs. more structured types).
- The theorem `SEPARATE_FINITE_SET` about separating a point from a finite set is foundational and likely needs to be ported first if not available in the target system.

---

## POLY_ROOT_SEPARATE_LT

### Name of formal statement
POLY_ROOT_SEPARATE_LT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let POLY_ROOT_SEPARATE_LT = prove
 (`!p x. poly p x = &0 /\ ~(poly p = poly [])
         ==> ?d. &0 < d /\
                 !x'. &0 < abs(x' - x) /\ abs(x' - x) <= d
                      ==> ~(poly p x' = &0)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP POLY_ROOT_SEPARATE_LE) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d / &2` THEN ASM_MESON_TAC[REAL_ARITH
   `&0 < d ==> &0 < d / &2 /\ (x <= d / &2 ==> x < d)`]);;
```

### Informal statement
For any polynomial $p$ and any real number $x$ such that $p(x) = 0$ and $p$ is not the zero polynomial (i.e., $p \neq 0$), there exists a positive real number $d > 0$ such that for all $x'$ where $0 < |x' - x| \leq d$, we have $p(x') \neq 0$.

In other words, around any root of a non-zero polynomial, there exists a punctured neighborhood within which the polynomial has no other roots.

### Informal proof
This theorem follows directly from the similar theorem `POLY_ROOT_SEPARATE_LE`.

* We apply `POLY_ROOT_SEPARATE_LE` to obtain a positive value $d$ such that for all $x'$ with $0 < |x'-x| \leq d$, we have $p(x') \neq 0$.
* We then choose $d/2$ as our new separation distance.
* It's clear that $d/2 > 0$ since $d > 0$.
* For any $x'$ with $0 < |x'-x| \leq d/2$, we have $|x'-x| < d$ (since $x \leq d/2$ implies $x < d$ by basic arithmetic).
* Therefore, by the properties from `POLY_ROOT_SEPARATE_LE`, we have $p(x') \neq 0$ for all such $x'$.

The proof uses basic properties of real numbers, particularly that if $0 < d$ then $0 < d/2$ and $x \leq d/2$ implies $x < d$.

### Mathematical insight
This theorem formalizes an important property of polynomial roots - they are isolated. Unlike other types of functions, a non-zero polynomial cannot have roots that accumulate at a point. This is a fundamental result in polynomial theory.

The theorem gives a "strict" version of polynomial root separation, ensuring there's a punctured neighborhood around any root that contains no other roots. This property is often used in various proofs about polynomials, especially when analyzing their behavior near roots.

The existence of such a separation is what allows us to talk about the multiplicity of a root, and forms the basis for many numerical methods for finding polynomial roots.

### Dependencies
- `POLY_ROOT_SEPARATE_LE`: The non-strict version of this theorem, stating that there exists a neighborhood around any root where there are no other roots.
- Various basic real arithmetic properties

### Porting notes
When porting this theorem, ensure that the underlying polynomial theory is in place, particularly the notion of polynomial evaluation (`poly p x`) and the definition of the zero polynomial (`poly []`). The proof is straightforward and should transfer easily to other systems, as it primarily relies on basic real arithmetic and a previous separation theorem.

---

## POLY_BOUND_INTERVAL

### POLY_BOUND_INTERVAL
- poly_bound_interval

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let POLY_BOUND_INTERVAL = prove
 (`!p d x. ?M. &0 < M /\ !x'. abs(x' - x) <= d ==> abs(poly p x') < M`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`poly p`; `x - d`; `x + d`] CONT_BOUNDED_ABS) THEN
  REWRITE_TAC[REWRITE_RULE[ETA_AX] (SPEC_ALL POLY_CONT)] THEN
  DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN EXISTS_TAC `&1 + abs M` THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `M:real` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN POP_ASSUM MP_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;
```

### Informal statement
For any polynomial $p$, any positive real number $d$, and any real number $x$, there exists a real number $M > 0$ such that for all $x'$ satisfying $|x' - x| \leq d$, we have $|p(x')| < M$.

### Informal proof
The proof establishes that a polynomial is bounded on a closed interval.

- Apply the `CONT_BOUNDED_ABS` theorem to the function `poly p` on the interval $[x-d, x+d]$.
  - This uses the fact that a continuous function on a closed interval is bounded.
  
- Use `POLY_CONT` to establish that the polynomial is continuous.

- This gives us some value $M$ such that $|p(x')| \leq M$ for all $x' \in [x-d, x+d]$.

- Choose $1 + |M|$ as the bound we seek. This ensures:
  1. It's positive (since $1 + |M| > 0$)
  2. It's strictly greater than $|p(x')|$ for all $x'$ in the interval 
  
- For any $x'$ with $|x' - x| \leq d$, we have $x' \in [x-d, x+d]$, so $|p(x')| \leq M < 1 + |M|$.

### Mathematical insight
This theorem establishes a basic property of polynomials: they are bounded on any closed interval. While this follows from the more general fact that continuous functions are bounded on closed intervals, it's particularly useful for polynomials in many applications.

The result is slightly stronger than just boundedness - it provides a strict inequality ($|p(x')| < M$) rather than just $|p(x')| \leq M$. This can be important in some analyses.

This is a fundamental building block for studying polynomial approximation, numerical methods, and various analytic results involving polynomials.

### Dependencies
- `POLY_CONT`: Establishes that polynomials are continuous functions
- `CONT_BOUNDED_ABS`: States that a continuous function is bounded (in absolute value) on a closed interval
- Various basic arithmetic and logical theorems

### Porting notes
When porting this result:
- Ensure your target system has a well-defined concept of polynomials and their evaluation
- Check that you have access to basic theorems about continuity of functions on closed intervals
- The proof uses basic real-number arithmetic properties, which should be available in most systems

---

## LIOUVILLE_INTERVAL

### Name of formal statement
LIOUVILLE_INTERVAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LIOUVILLE_INTERVAL = prove
 (`!p x. poly p x = &0 /\ ~(poly p = poly [])
         ==> ?c. &0 < c /\
                 (!x'. abs(x' - x) <= c
                       ==> abs(poly(poly_diff p) x') < &1 / c) /\
                 (!x'. &0 < abs(x' - x) /\ abs(x' - x) <= c
                       ==> ~(poly p x' = &0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:real list`; `x:real`] POLY_ROOT_SEPARATE_LT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`poly_diff p`; `d:real`; `x:real`] POLY_BOUND_INTERVAL) THEN
  DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN EXISTS_TAC `min d (inv M)` THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_LE_MIN; REAL_LT_INV_EQ] THEN
  X_GEN_TAC `y:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `M:real` THEN
  ASM_SIMP_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN REWRITE_TAC[REAL_MIN_LE; REAL_LT_MIN] THEN
  ASM_REWRITE_TAC[REAL_LT_INV_EQ; REAL_LE_REFL]);;
```

### Informal statement
For any polynomial $p$ and a real number $x$ such that $p(x) = 0$ and $p$ is not the zero polynomial, there exists a positive constant $c$ such that:
1. For all $x'$ with $|x' - x| \leq c$, we have $|p'(x')| < 1/c$ (where $p'$ is the derivative of $p$)
2. For all $x'$ such that $0 < |x' - x| \leq c$, we have $p(x') \neq 0$.

### Informal proof
The proof establishes the existence of a neighborhood around a polynomial root where the derivative is bounded and no other roots exist:

- Start with a polynomial $p$ and a root $x$ such that $p(x) = 0$ and $p$ is not the zero polynomial.
- Apply the theorem `POLY_ROOT_SEPARATE_LT` to $p$ and $x$, which gives us a positive real number $d$ such that there are no other roots of $p$ in the interval $(x-d, x+d)$ except $x$ itself.
- Apply the theorem `POLY_BOUND_INTERVAL` to the derivative polynomial `poly_diff p`, the distance $d$, and point $x$ to get a bound $M$ for the absolute value of the derivative in that interval.
- Choose $c = \min(d, 1/M)$, which is positive because both $d$ and $1/M$ are positive.
- For all $x'$ with $|x' - x| \leq c$:
  * We have $|p'(x')| \leq M$ by the bound from `POLY_BOUND_INTERVAL`
  * Since $c \leq 1/M$, we have $M \leq 1/c$, thus $|p'(x')| < 1/c$
- For all $x'$ with $0 < |x' - x| \leq c$:
  * Since $c \leq d$, we have $|x' - x| \leq d$
  * By our application of `POLY_ROOT_SEPARATE_LT`, we know that $p(x') \neq 0$

### Mathematical insight
This theorem is central to Liouville's approach to algebraic number theory. It establishes a key property of polynomials with real coefficients: around any root, there's a neighborhood where:
1. The derivative is bounded
2. No other roots exist

This result is particularly important for the proof of Liouville's theorem on the approximation of algebraic numbers by rationals. It essentially shows that algebraic numbers (roots of polynomials) have a certain "isolation property" - they can't be arbitrarily close to other roots of the same polynomial.

The bound on the derivative provides a way to control how quickly the polynomial changes in value as we move away from the root, which is crucial for establishing lower bounds on how closely algebraic numbers can be approximated.

### Dependencies
#### Theorems
- `POLY_ROOT_SEPARATE_LT`: Separation theorem for polynomial roots
- `POLY_BOUND_INTERVAL`: Bound on polynomial values in an interval

#### Definitions
- `poly_diff`: Computes the derivative of a polynomial

### Porting notes
When porting this theorem:
- Ensure that polynomials are represented consistently (HOL Light uses lists of coefficients)
- The polynomial derivative function may have different specifications in other systems
- Interval reasoning might have different automated support in other proof assistants
- The zero polynomial check (`~(poly p = poly [])`) might need to be expressed differently depending on how polynomials are represented

---

## LIOUVILLE

### Name of formal statement
LIOUVILLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LIOUVILLE = prove
 (`!x. algebraic x
       ==> ?n c. c > &0 /\
                 !p q. ~(q = 0) ==> &p / &q = x \/
                                    abs(x - &p / &q) > c / &q pow n`,
  GEN_TAC THEN REWRITE_TAC[algebraic; real_gt] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `LENGTH(l:real list)` THEN
  MP_TAC(SPECL [`l:real list`; `x:real`] LIOUVILLE_INTERVAL) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LE] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `&p / &q = x` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN UNDISCH_TAC
   `!x'. &0 < abs(x' - x) /\ abs(x' - x) <= c ==> ~(poly l x' = &0)` THEN
  DISCH_THEN(MP_TAC o SPEC `&p / &q`) THEN REWRITE_TAC[NOT_IMP] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_ABS_NZ; REAL_SUB_0];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `abs(x - y) <= d ==> d <= e ==> abs(y - x) <= e`)) THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; REAL_LE_LDIV_EQ; LT_NZ] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `~(q = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&q pow (LENGTH(l:real list)) * poly l (&p / &q) = &0`
  MP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0; REAL_OF_NUM_EQ]] THEN
  MATCH_MP_TAC REAL_INTEGER_EQ_0 THEN
  ASM_SIMP_TAC[POLY_MULTIPLE_INTEGER] THEN
  MP_TAC(SPECL [`poly l`; `poly(poly_diff l)`; `x:real`;
                `c / &q pow (LENGTH(l:real list))`; `&1 / c`]
               MVT_INEQ) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH; LT_NZ; REAL_POW_LT] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REWRITE_RULE[ETA_AX] (SPEC_ALL POLY_DIFF)] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x <= d ==> d <= e ==> x <= e`)) THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; REAL_LE_LDIV_EQ; LT_NZ] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `~(q = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC; REAL_MUL_LID] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[GSYM real_div] THEN DISCH_THEN(MP_TAC o SPEC `&p / &q`) THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; REAL_LT_RDIV_EQ; LT_NZ] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NUM] THEN
  REWRITE_TAC[REAL_MUL_AC]);;
```

### Informal statement
Liouville's approximation theorem: For any algebraic number $x$, there exist a positive integer $n$ and a positive real number $c$ such that for all integers $p$ and $q$ with $q \neq 0$, either $\frac{p}{q} = x$ or $|x - \frac{p}{q}| > \frac{c}{q^n}$.

In other words, algebraic numbers cannot be approximated "too closely" by rational numbers.

### Informal proof
The proof proceeds as follows:

- Let $x$ be an algebraic number. By definition, there exists a non-zero polynomial $l$ with integer coefficients such that $\text{poly}(l, x) = 0$.
- We set $n = \text{LENGTH}(l)$ (the degree of the polynomial).
- We apply the theorem `LIOUVILLE_INTERVAL` to the polynomial $l$ and number $x$, which gives us a positive constant $c$ such that for any $x'$ with $0 < |x' - x| \leq c$, we have $\text{poly}(l, x') \neq 0$.
- For arbitrary integers $p$ and $q$ with $q \neq 0$, we have two cases:
  - If $\frac{p}{q} = x$, we're done.
  - Otherwise, we want to show $|x - \frac{p}{q}| > \frac{c}{q^n}$.
  
- We prove by contradiction. Assume $|x - \frac{p}{q}| \leq \frac{c}{q^n}$.
  - This would imply that $\text{poly}(l, \frac{p}{q}) \neq 0$ from our application of `LIOUVILLE_INTERVAL`.
  - However, we can show that $q^n \cdot \text{poly}(l, \frac{p}{q})$ is an integer by using `POLY_MULTIPLE_INTEGER`.
  - Using the Mean Value Theorem inequality (`MVT_INEQ`), we can show that $|q^n \cdot \text{poly}(l, \frac{p}{q})|$ must be less than 1.
  - This means $q^n \cdot \text{poly}(l, \frac{p}{q}) = 0$, which implies $\text{poly}(l, \frac{p}{q}) = 0$ since $q \neq 0$.
  - This contradicts our earlier conclusion, completing the proof.

### Mathematical insight
Liouville's theorem is a fundamental result in number theory and Diophantine approximation. It establishes that algebraic numbers cannot be approximated by rational numbers beyond a certain precision. The theorem provides a quantitative measure of how well an algebraic number can be approximated by rational numbers, expressed in terms of the degree of the minimal polynomial.

This result was later generalized by Thue, Siegel, and Roth, culminating in Roth's theorem, which showed that for any algebraic number $\alpha$ and any $\epsilon > 0$, there are only finitely many rationals $\frac{p}{q}$ with $|\alpha - \frac{p}{q}| < \frac{1}{q^{2+\epsilon}}$.

Liouville's theorem has important applications, including the construction of the first examples of transcendental numbers (Liouville numbers), which can be approximated by rational numbers with arbitrary precision.

### Dependencies
- Theorems:
  - `LIOUVILLE_INTERVAL`: Provides a positive constant around an algebraic number where no other root of the polynomial exists
  - `POLY_DIFF`: Relates the derivative of a polynomial function to its coefficient list
  - `POLY_MULTIPLE_INTEGER`: Shows that multiplying a polynomial evaluated at a rational by an appropriate power of the denominator yields an integer
  - `MVT_INEQ`: Mean Value Theorem inequality used for bounding polynomial values

- Definitions:
  - `poly_diff`: The formal differentiation operation on coefficient lists of polynomials
  - `algebraic`: Definition of algebraic numbers as roots of non-zero polynomials with integer coefficients

### Porting notes
When porting this theorem:

1. Ensure your target system has a robust representation of polynomials with coefficient lists, with defined operations for evaluation and differentiation.
2. The Mean Value Theorem for polynomials should be available or established.
3. Some intermediate results like `POLY_MULTIPLE_INTEGER` may need to be proved separately.
4. Note that this proof uses multiple number type coercions (between natural numbers and reals). Some systems might require explicit conversions where HOL Light uses implicit ones.

---

## LIOUVILLE_IRRATIONAL

### Name of formal statement
LIOUVILLE_IRRATIONAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LIOUVILLE_IRRATIONAL = prove
 (`!x. algebraic x /\ ~rational x
       ==> ?n c. c > &0 /\ !p q. ~(q = 0) ==> abs(x - &p / &q) > c / &q pow n`,
  REWRITE_TAC[RATIONAL_ALT] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LIOUVILLE) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  ASM_MESON_TAC[LIOUVILLE; REAL_ABS_DIV; REAL_ABS_NUM]);;
```

### Informal statement
For all real numbers $x$, if $x$ is algebraic but not rational, then there exist a natural number $n$ and a positive real constant $c > 0$ such that for all integers $p$ and $q$ with $q \neq 0$, we have:

$$\left|x - \frac{p}{q}\right| > \frac{c}{q^n}$$

### Informal proof
This theorem is a corollary of Liouville's theorem on the approximation of algebraic numbers.

- We start by using `RATIONAL_ALT` which gives an equivalent definition of rational numbers: $x$ is rational if and only if there exist integers $p$ and $q$ with $q \neq 0$ such that $|x| = \frac{p}{q}$.
- We apply Liouville's theorem (`LIOUVILLE`), which states that for an algebraic irrational number, there exists a bound on how well it can be approximated by rationals.
- The proof applies a series of monotonicity results to transform the statement into the desired form.
- We use the facts that $x$ is algebraic but irrational, which allows us to apply Liouville's theorem directly.
- The properties of absolute values for rational numbers (`REAL_ABS_DIV` and `REAL_ABS_NUM`) are used to complete the proof.

### Mathematical insight
This theorem is a restatement of Liouville's approximation theorem specifically for algebraic irrational numbers. It provides a quantitative measure of how "poorly" algebraic irrationals can be approximated by rational numbers.

The key insight is that irrational algebraic numbers cannot be approximated by rational numbers "too well" - there's a bound on the approximation quality determined by the degree of the minimal polynomial. This is contrary to transcendental numbers (like $e$ or $\pi$), which can be approximated arbitrarily well by rationals.

This theorem is fundamental in number theory and was historically used by Liouville to construct the first examples of transcendental numbers. By constructing numbers that could be approximated by rationals better than this bound allows, Liouville proved they couldn't be algebraic.

### Dependencies
- `RATIONAL_ALT`: Alternative characterization of rational numbers
- `LIOUVILLE`: Liouville's theorem on approximation of algebraic numbers
- `REAL_ABS_DIV`: Property of absolute value of division
- `REAL_ABS_NUM`: Property of absolute value of natural numbers

### Porting notes
When porting this theorem, ensure that:
1. The underlying number theory library has a solid definition of algebraic numbers
2. Liouville's theorem is already implemented
3. The rational number representation is compatible with how algebraic numbers are defined
4. The absolute value operations for rational numbers are properly defined

---

## liouville

### Name of formal statement
liouville

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let liouville = new_definition
 `liouville = suminf (\n. &1 / &10 pow (FACT n))`;;
```

### Informal statement
Liouville's constant is defined as:

$$\text{liouville} = \sum_{n=0}^{\infty} \frac{1}{10^{n!}}$$

where $n!$ represents the factorial of $n$.

### Informal proof
This is a definition, so no proof is required.

### Mathematical insight
Liouville's constant is a famous transcendental number constructed by Joseph Liouville in 1844 as an explicit example of a transcendental (non-algebraic) number. It is the sum of an infinite series where each term is 1 divided by a power of 10, with the exponent being the factorial of the position index.

The constant can be written as:
$$0.110001000000000000000001000...$$ 
where the digit 1 appears at positions 1, 2, 6, 24, 120, etc. (the factorials).

Liouville's constant was historically significant as it provided the first explicit example of a transcendental number. Liouville proved it was transcendental by showing it could be approximated by rational numbers "too well" to be algebraic, according to what is now known as Liouville's theorem on approximation of algebraic numbers.

### Dependencies
Empty dependency list provided.

### Porting notes
When porting to other systems, note that:
1. You'll need to ensure the system has appropriate definitions for infinite sums (`suminf`).
2. The notation `&1` in HOL Light represents the conversion from a natural number to a real number, which might be handled differently in other systems.
3. The notation `&10 pow (FACT n)` represents $10^{n!}$, where `FACT` is the factorial function.

---

## LIOUVILLE_SUM_BOUND

### Name of formal statement
LIOUVILLE_SUM_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LIOUVILLE_SUM_BOUND = prove
 (`!d n. ~(n = 0)
         ==> sum(n..n+d) (\k. &1 / &10 pow FACT k) <= &2 / &10 pow (FACT n)`,
  INDUCT_TAC THEN GEN_TAC THEN DISCH_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; SUM_SING_NUMSEG; real_div] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_OF_NUM_LE; ARITH];
    ALL_TAC] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_ADD] THEN REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= x ==> &1 * x + y <= &2 * x`) THEN
  REWRITE_TAC[ARITH_RULE `n + SUC d = (n + 1) + d`; GSYM real_div] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n + 1`) THEN REWRITE_TAC[ADD_EQ_0; ARITH] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
  SIMP_TAC[GSYM REAL_POW_SUB; REAL_OF_NUM_EQ; ARITH; FACT_MONO; LE_ADD] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&10 pow 1` THEN
  CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC REAL_POW_MONO] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[GSYM ADD1; FACT] THEN
  MATCH_MP_TAC(ARITH_RULE
   `1 * x <= SUC n * x /\ ~(n * x = 0) ==> 1 <= SUC n * x - x`) THEN
  ASM_SIMP_TAC[LE_MULT_RCANCEL; MULT_EQ_0] THEN
  REWRITE_TAC[GSYM LT_NZ; FACT_LT] THEN ARITH_TAC);;
```

### Informal statement
For all natural numbers $d$ and $n$ such that $n \neq 0$, we have:

$$\sum_{k=n}^{n+d} \frac{1}{10^{k!}} \leq \frac{2}{10^{n!}}$$

where $k!$ denotes the factorial of $k$.

### Informal proof
We prove this by induction on $d$.

**Base case ($d = 0$):**
- When $d = 0$, the sum reduces to a single term: $\sum_{k=n}^{n} \frac{1}{10^{k!}} = \frac{1}{10^{n!}}$
- Since $\frac{1}{10^{n!}} \leq \frac{2}{10^{n!}}$ (as $1 \leq 2$), the base case holds.

**Inductive case:**
- Assume the claim holds for some $d$, and consider $d+1$.
- We need to prove: $\sum_{k=n}^{n+(d+1)} \frac{1}{10^{k!}} \leq \frac{2}{10^{n!}}$

- Splitting the sum into two parts:
  $$\sum_{k=n}^{n+(d+1)} \frac{1}{10^{k!}} = \frac{1}{10^{n!}} + \sum_{k=n+1}^{n+(d+1)} \frac{1}{10^{k!}}$$

- Rewriting the second term as $\sum_{k=(n+1)}^{(n+1)+d} \frac{1}{10^{k!}}$
- By the induction hypothesis applied to $n+1$, we have:
  $$\sum_{k=(n+1)}^{(n+1)+d} \frac{1}{10^{k!}} \leq \frac{2}{10^{(n+1)!}}$$

- We need to show: $\frac{1}{10^{n!}} + \frac{2}{10^{(n+1)!}} \leq \frac{2}{10^{n!}}$
- This is equivalent to showing: $\frac{2}{10^{(n+1)!}} \leq \frac{1}{10^{n!}}$
- Since $(n+1)! = (n+1) \cdot n!$, we have $10^{(n+1)!} = (10^{n!})^{n+1} \cdot 10^{n!}$
- Thus, $\frac{2}{10^{(n+1)!}} = \frac{2}{10^{n!} \cdot 10^{n! \cdot n}}$
- It suffices to show that $2 \leq 10^{n! \cdot n} \cdot 10^{n!}$
- Since $n \geq 1$, we have $n! \geq 1$ and thus $10^{n! \cdot n} \geq 10$
- Therefore, $10^{n! \cdot n} \cdot 10^{n!} \geq 10 \cdot 1 = 10 > 2$
- This completes the induction.

### Mathematical insight
This theorem provides an upper bound for the partial sum of the Liouville series $\sum_{k=1}^{\infty} \frac{1}{10^{k!}}$. The bound is important because it shows that the tail of this series decreases very rapidly, which helps establish the convergence of the series and provides a way to estimate the error when truncating the series.

The bound is particularly tight and shows that the sum of all terms starting from index $n$ is at most twice the value of the first term in that range, highlighting the extremely fast convergence of this series due to the factorial growth in the exponent.

This result is useful in the context of Liouville's construction of transcendental numbers and in the study of rapidly converging series in general.

### Dependencies
None explicitly mentioned in the provided information.

### Porting notes
When porting this theorem:
- Be careful with the handling of real division and power operations
- Make sure to use the correct factorial definition
- The proof relies on induction over a natural number and various arithmetic manipulations

---

## LIOUVILLE_PSUM_BOUND

### Name of formal statement
LIOUVILLE_PSUM_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LIOUVILLE_PSUM_BOUND = prove
 (`!n d. ~(n = 0)
         ==> sum(n,d) (\k. &1 / &10 pow FACT k) <= &2 / &10 pow (FACT n)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `d = 0` THEN
  ASM_SIMP_TAC[sum; REAL_LE_DIV; REAL_POW_LE; REAL_POS] THEN
  ASM_SIMP_TAC[PSUM_SUM_NUMSEG] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(d = 0) ==> (n + d) - 1 = n + (d - 1)`] THEN
  ASM_SIMP_TAC[LIOUVILLE_SUM_BOUND]);;
```

### Informal statement
For all natural numbers $n$ and $d$ where $n \neq 0$, the following inequality holds:
$$\sum_{k=n}^{n+d-1} \frac{1}{10^{k!}} \leq \frac{2}{10^{n!}}$$

### Informal proof
The proof proceeds by case analysis on the value of $d$:

- First, we strip the quantifiers and assumptions.
- We consider two cases: $d = 0$ and $d \neq 0$.

For the case when $d = 0$:
- When $d = 0$, the sum is empty, so it evaluates to $0$.
- Since $\frac{2}{10^{n!}} > 0$, the inequality holds trivially.

For the case when $d \neq 0$:
- We rewrite the sum using `PSUM_SUM_NUMSEG` to convert from the notation `sum(n,d)` to a sum over the range $[n, n+d-1]$.
- We apply the arithmetic simplification: if $d \neq 0$, then $(n + d) - 1 = n + (d - 1)$.
- Finally, we apply the theorem `LIOUVILLE_SUM_BOUND` which establishes the bound for the sum from $n$ to $n+d-1$.

### Mathematical insight
This theorem provides an upper bound for a partial sum of the Liouville series $\sum_{k=1}^{\infty} \frac{1}{10^{k!}}$, where we start summing from index $n$ and go up to $n+d-1$. The bound shows that this partial sum is less than or equal to $\frac{2}{10^{n!}}$.

This result is important in the study of transcendental numbers and specifically in the construction of Liouville numbers, which are a class of transcendental numbers that can be approximated "unusually well" by rational numbers. The bound helps establish the transcendence of certain Liouville constants by controlling the magnitude of the tail of the series.

### Dependencies
- `LIOUVILLE_SUM_BOUND`: Likely a theorem that bounds the sum from $n$ to $n+d-1$ of the terms $\frac{1}{10^{k!}}$.
- Various arithmetic and simplification rules:
  - `sum`: Definition of summation
  - `REAL_LE_DIV`: Inequality properties for division of real numbers
  - `REAL_POW_LE`: Inequality properties for powers of real numbers
  - `REAL_POS`: Positivity properties of real numbers
  - `PSUM_SUM_NUMSEG`: Conversion between different summation notations
  - `ARITH_RULE`: Simplifies arithmetic expressions

### Porting notes
When porting this theorem to another proof assistant:
1. Make sure the target system has a compatible definition of factorial and summation.
2. Be aware that the HOL Light notation `sum(n,d)` represents the sum from index $n$ to $n+d-1$, which might differ from summation notations in other systems.
3. The proof relies on `LIOUVILLE_SUM_BOUND`, so that theorem needs to be ported first.
4. The case analysis structure is straightforward and should translate well to most proof assistants.

---

## LIOUVILLE_SUMS

### Name of formal statement
LIOUVILLE_SUMS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LIOUVILLE_SUMS = prove
 (`(\k. &1 / &10 pow FACT k) sums liouville`,
  REWRITE_TAC[liouville] THEN MATCH_MP_TAC SUMMABLE_SUM THEN
  REWRITE_TAC[SER_CAUCHY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `inv(e)` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `2 * N + 1` THEN
  REWRITE_TAC[GE] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `&2 / &10 pow (FACT m)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= a ==> abs x <= a`) THEN
    ASM_SIMP_TAC[SUM_POS; REAL_LE_DIV; REAL_POW_LE; REAL_POS] THEN
    MATCH_MP_TAC LIOUVILLE_PSUM_BOUND THEN
    UNDISCH_TAC `2 * N + 1 <= m` THEN ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `e * &(2 * N + 1)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&1 < (n + &1 / &2) * e ==> &2 < e * (&2 * n + &1)`) THEN
    ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ; real_div; REAL_MUL_LID] THEN
    UNDISCH_TAC `inv(e) <= &N` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `10 EXP m` THEN
  REWRITE_TAC[FACT_LE_REFL; LE_EXP; ARITH] THEN SIMP_TAC[EXP_LE_REFL; ARITH]);;
```

### Informal statement
The theorem states that the infinite series $\sum_{k=0}^{\infty} \frac{1}{10^{k!}}$ converges to Liouville's constant.

More precisely, it states:
$(\lambda k. \frac{1}{10^{k!}})$ sums to $\text{liouville}$

Where "sums" refers to the convergence of the infinite series, and "liouville" refers to Liouville's constant.

### Informal proof
The proof establishes that the sequence of partial sums of $\frac{1}{10^{k!}}$ is Cauchy, which implies convergence to Liouville's constant:

- Start by rewriting using the definition of Liouville's constant
- Apply the theorem `SUMMABLE_SUM` which states that a sequence sums to a value if it is summable
- Rewrite using `SER_CAUCHY` to establish the Cauchy criterion for convergence
- For any arbitrary $ε > 0$:
  - Use the Archimedean property (`REAL_ARCH_SIMPLE`) to find an $N$ such that $\frac{1}{ε} \leq N$
  - Choose $m = 2N+1$ as the index from which the remainder sum is small
  - Show that the remainder sum $\sum_{k=m}^{\infty} \frac{1}{10^{k!}}$ is less than $\frac{2}{10^{m!}}$
  - Show that $\frac{2}{10^{m!}} < ε$, which is done by establishing:
    - $\frac{2}{10^{m!}} < ε \cdot (2N+1)$ (using properties of real numbers)
    - $ε \cdot (2N+1) \leq ε$ (using the fact that $\frac{1}{ε} \leq N$ and arithmetic)
  - By transitivity, the remainder sum is less than $ε$
- Thus the sequence satisfies the Cauchy criterion, completing the proof

The proof relies on bounding the remainder of the series and using the fact that factorials grow faster than exponentials.

### Mathematical insight
Liouville's constant is an important example of a transcendental number, specifically constructed to be transcendental. It is defined as the sum of the infinite series $\sum_{k=0}^{\infty} \frac{1}{10^{k!}}$.

This theorem formally establishes the convergence of this series to the constant. The key insight is that the factorials in the denominators grow so rapidly that the series converges very quickly. In fact, the terms decrease so rapidly that the sum of all terms from any point onward becomes less than any specified positive value.

The construction is important in the theory of transcendental numbers, as Liouville used this and similar constants to provide the first explicit examples of transcendental numbers, showing that not all irrational numbers are algebraic.

### Dependencies
Although the dependency list provided is empty, the proof relies on several HOL Light theorems, including:
- `liouville`: Definition of Liouville's constant
- `SUMMABLE_SUM`: Relating summability to convergence
- `SER_CAUCHY`: The Cauchy criterion for series
- `REAL_ARCH_SIMPLE`: The Archimedean property for reals
- `LIOUVILLE_PSUM_BOUND`: A bound on partial sums for Liouville's constant
- Various arithmetic and real number theorems

### Porting notes
When porting this theorem:
- Ensure the definition of Liouville's constant is consistent with HOL Light's definition
- The proof relies heavily on real analysis results, particularly for series convergence
- Special attention should be paid to how the Cauchy criterion is expressed in the target system
- The handling of factorial and power functions may differ between systems

---

## LIOUVILLE_PSUM_LE

### Name of formal statement
LIOUVILLE_PSUM_LE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LIOUVILLE_PSUM_LE = prove
 (`!n. sum(0,n) (\k. &1 / &10 pow FACT k) <= liouville`,
  GEN_TAC THEN REWRITE_TAC[suminf] THEN MATCH_MP_TAC SEQ_LE THEN
  EXISTS_TAC `\j:num. sum(0,n) (\k. &1 / &10 pow FACT k)` THEN
  EXISTS_TAC `\n:num. sum(0,n) (\k. &1 / &10 pow FACT k)` THEN
  REWRITE_TAC[SEQ_CONST; GSYM sums; LIOUVILLE_SUMS] THEN
  EXISTS_TAC `n:num` THEN X_GEN_TAC `m:num` THEN SIMP_TAC[GE; LE_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC) THEN
  REWRITE_TAC[GSYM SUM_SPLIT; ADD_CLAUSES; REAL_LE_ADDR] THEN
  SIMP_TAC[SUM_POS; REAL_LE_DIV; REAL_POW_LE; REAL_POS]);;
```

### Informal statement
For any natural number $n$, the partial sum of the first $n+1$ terms of the Liouville constant's series is less than or equal to the constant itself:
$$\sum_{k=0}^{n} \frac{1}{10^{k!}} \leq \text{liouville}$$

where "liouville" refers to Liouville's constant $\sum_{k=0}^{\infty} \frac{1}{10^{k!}}$.

### Informal proof
The proof shows that the partial sum is less than or equal to the full infinite sum (Liouville's constant):

* Start by rewriting the goal using the definition of infinite sum (`suminf`).
* Apply the sequence comparison theorem (`SEQ_LE`) to show that if sequence A converges to a value and sequence B converges to another value, and A is always less than or equal to B, then the limit of A is less than or equal to the limit of B.
* For the first sequence, use the constant sequence that always equals the partial sum $\sum_{k=0}^{n} \frac{1}{10^{k!}}$.
* For the second sequence, use the sequence of partial sums for Liouville's constant: $\sum_{k=0}^{m} \frac{1}{10^{k!}}$ where m increases.
* The first sequence trivially converges to the partial sum (by `SEQ_CONST`).
* The second sequence converges to Liouville's constant (by `LIOUVILLE_SUMS`).
* Show that for all $m \geq n$, the first sequence is less than or equal to the second sequence.
* This is true because for $m = n + d$ (for some $d \geq 0$), we can split the sum as:
  $$\sum_{k=0}^{m} \frac{1}{10^{k!}} = \sum_{k=0}^{n} \frac{1}{10^{k!}} + \sum_{k=n+1}^{m} \frac{1}{10^{k!}}$$
* Since each term $\frac{1}{10^{k!}}$ is positive (as $10 > 0$), the second part of the sum is non-negative.
* Therefore, $\sum_{k=0}^{n} \frac{1}{10^{k!}} \leq \sum_{k=0}^{m} \frac{1}{10^{k!}}$, which completes the proof.

### Mathematical insight
This theorem establishes a basic but important property of Liouville's constant: any partial sum provides a lower approximation of the full constant. Liouville's constant is a famous transcendental number constructed specifically to prove the existence of transcendental numbers. It's defined as $\sum_{k=0}^{\infty} \frac{1}{10^{k!}}$, which gives a decimal expansion where the digit at position $k!$ is 1 and all other digits are 0.

The theorem is important because it shows that the partial sums form an increasing sequence that converges to Liouville's constant, which is useful for numerical approximations and for proving properties about the constant itself.

### Dependencies
- `suminf`: Definition of infinite sum
- `SEQ_LE`: Theorem for comparing limits of sequences
- `SEQ_CONST`: Theorem about constant sequences
- `sums`: Definition of sequence summation
- `LIOUVILLE_SUMS`: Theorem stating that the series for Liouville's constant converges
- `SUM_SPLIT`: Theorem for splitting sums at a point
- `SUM_POS`: Theorem about positivity of sums of positive terms
- `REAL_LE_DIV`, `REAL_POW_LE`, `REAL_POS`: Real number theorems about inequalities

### Porting notes
When porting this theorem:
1. Ensure the target system has a suitable definition of Liouville's constant
2. The proof relies on theorems about infinite series convergence and real number properties
3. The factorial function used in the series definition is the standard mathematical factorial
4. The proof structure is fairly standard and should translate well to other proof assistants, though specific tactics for handling real inequalities may differ

---

## LIOUVILLE_PSUM_LT

### Name of formal statement
LIOUVILLE_PSUM_LT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LIOUVILLE_PSUM_LT = prove
 (`!n. sum(0,n) (\k. &1 / &10 pow FACT k) < liouville`,
  GEN_TAC THEN MP_TAC(SPEC `SUC n` LIOUVILLE_PSUM_LE) THEN SIMP_TAC[sum] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < e ==> x + e <= y ==> x < y`) THEN
  SIMP_TAC[REAL_LT_DIV; REAL_POW_LT; REAL_OF_NUM_LT; ARITH]);;
```

### Informal statement
For any natural number $n$, the sum of the first $n+1$ terms of the Liouville series is strictly less than the Liouville constant:

$$\sum_{k=0}^{n} \frac{1}{10^{k!}} < \ell$$

where $\ell$ is the Liouville constant.

### Informal proof
The proof proceeds as follows:

1. Start with theorem `LIOUVILLE_PSUM_LE` applied to `SUC n`, which gives us that:
   $$\sum_{k=0}^{n+1} \frac{1}{10^{k!}} \leq \ell$$

2. Apply the sum property to expand the sum:
   $$\sum_{k=0}^{n} \frac{1}{10^{k!}} + \frac{1}{10^{(n+1)!}} \leq \ell$$

3. Use the fact that $\frac{1}{10^{(n+1)!}} > 0$ to establish strict inequality:
   - $\frac{1}{10^{(n+1)!}} > 0$ because:
     - Division is positive when numerator and denominator are positive
     - $10^{(n+1)!} > 0$ (positive power of a positive number)

4. Therefore, by simple arithmetic, if $x + e \leq y$ and $e > 0$, then $x < y$:
   $$\sum_{k=0}^{n} \frac{1}{10^{k!}} < \ell$$

### Mathematical insight
This theorem establishes an important property of the Liouville constant - that any finite sum of terms in its defining series is strictly less than the constant itself. The Liouville constant is defined as:

$$\ell = \sum_{k=0}^{\infty} \frac{1}{10^{k!}}$$

This result is part of demonstrating that the Liouville constant is irrational and, more specifically, transcendental. The strict inequality is crucial because it shows that there is always a non-zero "remainder" when approximating the Liouville constant with finite sums of its defining series.

### Dependencies
- `LIOUVILLE_PSUM_LE`: States that for any natural number n, the sum of the first n terms of the Liouville series is less than or equal to the Liouville constant.
- `REAL_ARITH`: Real arithmetic simplification
- `REAL_LT_DIV`: Property of inequality for division of real numbers
- `REAL_POW_LT`: Property of inequality for powers of real numbers
- `REAL_OF_NUM_LT`: Conversion of natural number inequality to real number inequality

### Porting notes
When porting this theorem, ensure that:
1. The definition of the Liouville constant is consistent
2. The factorial function is defined appropriately
3. The properties of real number operations, especially regarding inequalities with powers, are available in the target system

---

## LIOVILLE_PSUM_DIFF

### Name of formal statement
LIOVILLE_PSUM_DIFF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LIOVILLE_PSUM_DIFF = prove
 (`!n. ~(n = 0)
       ==> liouville
             <= sum(0,n) (\k. &1 / &10 pow FACT k) + &2 / &10 pow (FACT n)`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SEQ_LE THEN
  EXISTS_TAC `\n. sum(0,n) (\k. &1 / &10 pow FACT k)` THEN
  EXISTS_TAC
    `\j:num. sum (0,n) (\k. &1 / &10 pow FACT k) + &2 / &10 pow FACT n` THEN
  REWRITE_TAC[SEQ_CONST; GSYM sums; LIOUVILLE_SUMS] THEN
  EXISTS_TAC `n:num` THEN X_GEN_TAC `m:num` THEN SIMP_TAC[GE; LE_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC) THEN
  REWRITE_TAC[GSYM SUM_SPLIT; REAL_LE_LADD] THEN
  ASM_SIMP_TAC[ADD_CLAUSES; LIOUVILLE_PSUM_BOUND]);;
```

### Informal statement
For any positive integer $n$ (i.e., $n \neq 0$), the Liouville constant is less than or equal to the sum:

$$\sum_{k=0}^{n} \frac{1}{10^{k!}} + \frac{2}{10^{n!}}$$

### Informal proof
The proof establishes that the Liouville constant is less than or equal to the partial sum plus a specific error term:

- Apply the sequence limit theorem (`SEQ_LE`) to show that if one sequence converges to the Liouville constant, and it's less than or equal to another sequence, then the Liouville constant is less than or equal to the limit of the second sequence.

- Define the first sequence as the partial sums: $\lambda n. \sum_{k=0}^{n} \frac{1}{10^{k!}}$

- Define the second sequence as: $\lambda j. \sum_{k=0}^{n} \frac{1}{10^{k!}} + \frac{2}{10^{n!}}$

- Use the fact that the first sequence converges to the Liouville constant (from `LIOUVILLE_SUMS`).

- The second sequence is constant for all $j \geq n$, so it converges to the same value.

- For any $m \geq n$, we can write $m = n + d$ for some $d$, and then:
  - Split the sum at position $n$
  - Apply the previously proven bound on the partial sum difference (`LIOUVILLE_PSUM_BOUND`)

### Mathematical insight
This theorem provides an explicit upper bound on how far the Liouville constant is from its $n$-term partial sum. The Liouville constant is defined as $\sum_{k=0}^{\infty} \frac{1}{10^{k!}}$, which is a transcendental number. This result gives a concrete error bound of $\frac{2}{10^{n!}}$ when approximating the constant with a finite sum.

The rapid growth of the factorial function means this error term becomes extremely small very quickly, making this a practical way to compute approximations of the Liouville constant to high precision.

### Dependencies
- `SEQ_LE`: Theorem about inequality preservation in sequence limits
- `SEQ_CONST`: Theorem about constant sequences
- `sums`: Definition of infinite series convergence
- `LIOUVILLE_SUMS`: Theorem stating that the series defining the Liouville constant converges
- `LIOUVILLE_PSUM_BOUND`: Theorem bounding the difference between the Liouville constant and its partial sum

### Porting notes
When porting this theorem:
- Ensure that the definition of the Liouville constant is consistent with HOL Light's definition
- The proof relies on properties of real number sequences and convergence, which should be available in most proof assistants
- The factorial function implementation and its properties may need attention, particularly regarding its growth rate

---

## TRANSCENDENTAL_LIOUVILLE

### Name of formal statement
TRANSCENDENTAL_LIOUVILLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TRANSCENDENTAL_LIOUVILLE = prove
 (`transcendental(liouville)`,
  REWRITE_TAC[transcendental] THEN DISCH_THEN(MP_TAC o MATCH_MP LIOUVILLE) THEN
  REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `c:real`] THEN
  REWRITE_TAC[DE_MORGAN_THM; real_gt; REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&10`; `&2 / c`] REAL_ARCH_POW) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  ABBREV_TAC `n = m + k + 1` THEN
  EXISTS_TAC `nsum(0..n-1) (\i. 10 EXP (FACT(n-1) - FACT i))` THEN
  EXISTS_TAC `10 EXP (FACT(n-1))` THEN REWRITE_TAC[EXP_EQ_0; ARITH] THEN
  SUBGOAL_THEN
   `&(nsum(0..n-1) (\i. 10 EXP (FACT(n-1) - FACT i))) / &(10 EXP (FACT(n-1))) =
    sum(0..n-1) (\k. &1 / &10 pow (FACT k))`
  SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_OF_NUM_SUM_NUMSEG; GSYM SUM_LMUL] THEN
    SIMP_TAC[GSYM REAL_OF_NUM_POW; REAL_POW_SUB; REAL_OF_NUM_EQ; ARITH;
             FACT_MONO; real_div; REAL_MUL_ASSOC] THEN
    SIMP_TAC[REAL_MUL_LINV; REAL_OF_NUM_EQ; REAL_POW_EQ_0; ARITH] THEN
    REWRITE_TAC[REAL_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(GEN `f:num->real`
   (SPECL [`f:num->real`; `0`; `m + k + 1`] PSUM_SUM_NUMSEG)) THEN
  REWRITE_TAC[ADD_EQ_0; ARITH; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  SIMP_TAC[LIOUVILLE_PSUM_LT; REAL_LT_IMP_NE] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN
  REWRITE_TAC[REAL_SUB_LE; LIOUVILLE_PSUM_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 / &10 pow (FACT n)` THEN
  REWRITE_TAC[REAL_LE_SUB_RADD] THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LIOVILLE_PSUM_DIFF THEN EXPAND_TAC "n" THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LIOVILLE_PSUM_DIFF] THEN
  REWRITE_TAC[REAL_OF_NUM_POW; GSYM EXP_MULT] THEN
  SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LT_NZ; EXP_EQ_0; ARITH] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&10 pow k` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
  SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; LT_NZ; EXP_EQ_0; ARITH] THEN
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  REWRITE_TAC[GSYM EXP_ADD; LE_EXP; ARITH_EQ] THEN EXPAND_TAC "n" THEN
  REWRITE_TAC[ARITH_RULE `(m + k + 1) - 1 = m + k`] THEN
  REWRITE_TAC[num_CONV `1`; ADD_CLAUSES; FACT] THEN
  REWRITE_TAC[ARITH_RULE
   `k + f * m <= SUC(m + k) * f <=> k <= (k + 1) * f`] THEN
  GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `k = k * 1`] THEN
  MATCH_MP_TAC LE_MULT2 THEN REWRITE_TAC[LE_ADD] THEN
  REWRITE_TAC[FACT_LT; ARITH_RULE `1 <= x <=> 0 < x`]);;
```

### Informal statement
Liouville's constant is transcendental. In mathematical notation:
$$\text{transcendental}(\text{liouville})$$

This means that Liouville's constant (defined as $\sum_{i=1}^{\infty} 10^{-i!}$) is not a root of any non-zero polynomial with integer coefficients.

### Informal proof
We prove that Liouville's constant is transcendental by showing that it satisfies Liouville's irrationality criterion.

- Start by rewriting with the definition of transcendental and proving by contradiction: assume Liouville's constant is algebraic.
- By Liouville's theorem on approximation of algebraic numbers, this implies bounds on how well it can be approximated by rational numbers.
- We rewrite the logical structure and set up to contradict this bound by constructing good rational approximations.
- For any positive reals $c$ and $m$, we choose a large enough $k$ such that $10^k > \frac{2}{c}$.
- Let $n = m + k + 1$ and consider the rational approximation $\frac{p_n}{q_n}$ where:
  - $p_n = \sum_{i=0}^{n-1} 10^{\text{FACT}(n-1) - \text{FACT}(i)}$
  - $q_n = 10^{\text{FACT}(n-1)}$

- We verify that this rational approximation can be rewritten as a partial sum of the Liouville constant:
  $$\frac{p_n}{q_n} = \sum_{i=0}^{n-1} \frac{1}{10^{\text{FACT}(i)}}$$

- Using properties of the Liouville partial sums, we establish that:
  $$\left|\text{liouville} - \frac{p_n}{q_n}\right| < \frac{2}{10^{\text{FACT}(n)}}$$

- We show this approximation is too good for an algebraic number, specifically:
  $$\frac{2}{10^{\text{FACT}(n)}} < \frac{c}{q_n^m}$$

- This contradiction with Liouville's theorem on approximation of algebraic numbers proves that Liouville's constant must be transcendental.

### Mathematical insight
Liouville's constant is a classic example of a transcendental number that was specifically constructed to be transcendental. It was one of the first explicit examples of transcendental numbers, even before more famous numbers like $e$ and $\pi$ were proven to be transcendental.

The key insight of this proof is that Liouville's constant is "extremely well approximated" by rational numbers - in fact, it was designed for this purpose. Algebraic numbers (of degree > 1) cannot be approximated by rational numbers beyond a certain precision (as established by Liouville's theorem on approximation of algebraic numbers). By showing that Liouville's constant can be approximated arbitrarily well by rational numbers, we establish that it cannot be algebraic.

The construction uses partial sums of the Liouville constant, which are rational numbers with denominator $10^{\text{FACT}(n-1)}$. The rate at which these approximations converge to Liouville's constant is faster than would be possible for any algebraic number, proving the transcendence.

### Dependencies
- `transcendental`: Definition of transcendental numbers
- `LIOUVILLE`: Theorem about Liouville's constant
- `REAL_ARCH_POW`: Archimedean property applied to powers
- `PSUM_SUM_NUMSEG`: Relating partial sums and finite sums
- `LIOUVILLE_PSUM_LT`, `LIOUVILLE_PSUM_LE`, `LIOVILLE_PSUM_DIFF`: Properties of partial sums of Liouville's constant

### Porting notes
When porting this proof:
1. The proof relies heavily on properties of Liouville's constant and its partial sums, which would need to be established first.
2. The proof uses a constructive approach to build rational approximations, which should translate well to other proof assistants.
3. Some HOL Light automation like `REAL_RAT_REDUCE_CONV` might need manual calculation in other systems.
4. The nested structure of quantifiers and logical connectives is important to maintain during the port.

---

