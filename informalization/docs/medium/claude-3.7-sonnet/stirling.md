# stirling.ml

## Overview

Number of statements: 32

This file formalizes Stirling's approximation for the factorial function in HOL Light. It provides a rigorous proof of the asymptotic formula n! ~ √(2πn)(n/e)ⁿ, establishing both the basic approximation and precise error bounds. The implementation builds on the analysis and transcendental function libraries to develop the necessary machinery for asymptotic analysis of the factorial function.

## ODDEVEN_INDUCT

### ODDEVEN_INDUCT
- `ODDEVEN_INDUCT`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let ODDEVEN_INDUCT = prove
 (`!P. P 0 /\ P 1 /\ (!n. P n ==> P(n + 2)) ==> !n. P n`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. P n /\ P(n + 1)` (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ADD1; GSYM ADD_ASSOC] THEN
  ASM_SIMP_TAC[ARITH]);;
```

### Informal statement
The theorem `ODDEVEN_INDUCT` states a principle of mathematical induction for proving properties of natural numbers by establishing them for the two base cases 0 and 1, and then showing that the property transfers from $n$ to $n+2$. Specifically:

For any predicate $P$ on natural numbers, if:
1. $P(0)$ holds, and
2. $P(1)$ holds, and
3. For any natural number $n$, if $P(n)$ holds, then $P(n+2)$ holds

Then $P(n)$ holds for all natural numbers $n$.

### Informal proof
The proof proceeds as follows:

- We first establish a stronger claim: for all natural numbers $n$, both $P(n)$ and $P(n+1)$ hold simultaneously.
- This stronger claim is proven by standard induction on $n$:
  - Base case: We need to show $P(0)$ and $P(1)$, which we have as assumptions.
  - Inductive step: Assuming $P(n)$ and $P(n+1)$ for some $n$, we need to show $P(n+1)$ and $P(n+2)$:
    - $P(n+1)$ is already given by the induction hypothesis.
    - $P(n+2)$ follows from $P(n)$ and our third assumption that $P(n) \implies P(n+2)$.
- The proof uses some arithmetic simplifications to handle the addition expressions correctly.
- Once the stronger claim is established, the original statement follows immediately.

### Mathematical insight
This theorem provides an alternative induction principle that is particularly useful for properties that follow a pattern based on the parity of numbers (odd vs even). Instead of proving a property for $n$ and then $n+1$ as in standard induction, this principle allows proving properties separately for even and odd numbers, where each sequence follows its own inductive pattern.

The comment indicates this induction principle was implemented specifically to support Wallis's product formula, which is related to Stirling's approximation for factorials. In such formulas, even and odd terms often follow related but slightly different patterns, making this induction principle particularly convenient.

### Dependencies
No specific dependencies are listed in the provided information. The proof uses standard HOL Light tactics and arithmetic reasoning.

### Porting notes
When porting this theorem:
- This is a straightforward induction principle that should exist in most proof assistants, though possibly under a different name.
- The proof relies on standard induction and arithmetic reasoning, which should be available in any mature proof assistant.
- The implementation might be simpler in systems with built-in support for induction schemes or tactics that can automatically derive custom induction principles.

---

## LN_LIM_BOUND

### Name of formal statement
LN_LIM_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LN_LIM_BOUND = prove
 (`!n. ~(n = 0) ==> abs(&n * ln(&1 + &1 / &n) - &1) <= &1 / (&2 * &n)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`&1 / &n`; `2`] MCLAURIN_LN_POS) THEN
  ASM_SIMP_TAC[SUM_2; REAL_LT_DIV; REAL_OF_NUM_LT; LT_NZ; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[real_div; REAL_INV_0; REAL_MUL_RZERO; REAL_ADD_LID] THEN
  REWRITE_TAC[REAL_POW_1; REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG;
              REAL_NEG_NEG; REAL_MUL_LID; REAL_INV_1; REAL_POW_NEG;
              REAL_POW_ONE; ARITH; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[REAL_OF_NUM_EQ; REAL_FIELD
   `~(x = &0) ==> x * (inv(x) + a) - &1 = x * a`] THEN
  REWRITE_TAC[REAL_ARITH `n * --((i * i) * a) = --((n * i) * a * i)`] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_OF_NUM_EQ; ARITH; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_MUL] THEN
  ONCE_REWRITE_TAC[REAL_INV_MUL] THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[real_div; REAL_MUL_LID; REAL_LE_INV_EQ; REAL_POS] THEN
  REWRITE_TAC[REAL_ABS_INV] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_POS] THEN
  UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC);;
```

### Informal statement
For all natural numbers $n \neq 0$, we have:
$$\left|n \cdot \ln\left(1 + \frac{1}{n}\right) - 1\right| \leq \frac{1}{2n}$$

This theorem gives a bound on how close $n \cdot \ln\left(1 + \frac{1}{n}\right)$ is to $1$ for large values of $n$.

### Informal proof
We apply the MacLaurin series expansion for the natural logarithm from `MCLAURIN_LN_POS` with $x = \frac{1}{n}$ and taking the first two terms of the series (setting the parameter to 2).

Since $n \neq 0$, we know $\frac{1}{n} > 0$, so the theorem applies. It gives us some $t$ with $0 < t < \frac{1}{n}$ such that:
$$\ln\left(1 + \frac{1}{n}\right) = \sum_{m=0}^{1} \frac{-1^{m+1} \cdot (\frac{1}{n})^m}{m} + \frac{-1^{2+1} \cdot (\frac{1}{n})^2}{2 \cdot (1+t)^2}$$

Computing the sum for $m=0$ and $m=1$, and simplifying:
$$\ln\left(1 + \frac{1}{n}\right) = \frac{1}{n} - \frac{1}{2} \cdot \frac{1}{n^2 \cdot (1+t)^2}$$

Multiplying both sides by $n$:
$$n \cdot \ln\left(1 + \frac{1}{n}\right) = 1 - \frac{1}{2n \cdot (1+t)^2}$$

Therefore:
$$n \cdot \ln\left(1 + \frac{1}{n}\right) - 1 = -\frac{1}{2n \cdot (1+t)^2}$$

Taking absolute values:
$$\left|n \cdot \ln\left(1 + \frac{1}{n}\right) - 1\right| = \frac{1}{2n \cdot (1+t)^2}$$

Since $0 < t < \frac{1}{n}$, we have $(1+t)^2 > 1$, so:
$$\frac{1}{(1+t)^2} < 1$$

Therefore:
$$\left|n \cdot \ln\left(1 + \frac{1}{n}\right) - 1\right| = \frac{1}{2n \cdot (1+t)^2} < \frac{1}{2n}$$

Concluding our proof.

### Mathematical insight
This theorem establishes a quantitative bound on how the expression $n \cdot \ln\left(1 + \frac{1}{n}\right)$ converges to 1 as $n$ grows large. The rate of convergence is $O(\frac{1}{n})$.

This result is related to the limit $\lim_{n \to \infty} n \cdot \ln\left(1 + \frac{1}{n}\right) = 1$, which is a standard calculus limit and can be derived using l'Hôpital's rule or series expansions. The theorem provides not just the limit but an explicit bound on the error term.

This type of bound is useful in many analysis contexts, particularly when estimating rates of convergence or when a specific error bound is needed rather than just knowing a limit exists.

### Dependencies
- `MCLAURIN_LN_POS`: Provides the MacLaurin series expansion for $\ln(1+x)$ with a bound on the remainder term
- `REAL_MUL_RID`: $x \cdot 1 = x$
- `REAL_MUL_RINV`: If $x \neq 0$, then $x \cdot \frac{1}{x} = 1$
- `REAL_MUL_RZERO`: $x \cdot 0 = 0$
- `REAL_NEG_NEG`: $-(-x) = x$
- `REAL_POS`: For any natural number $n$, $0 \leq n$
- `ln`: Definition of natural logarithm

### Porting notes
When porting this theorem:
1. Ensure your system has an appropriate MacLaurin series expansion for the natural logarithm function with error bounds
2. The proof relies on algebraic manipulations of real inequalities, which should transfer straightforwardly to other proof assistants
3. Pay attention to how your target system handles reciprocals and absolute value operations

Note that some proof assistants may have more direct ways to establish this limit or might have this result as part of their standard library.

---

## LN_LIM_LEMMA

### Name of formal statement
LN_LIM_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LN_LIM_LEMMA = prove
 (`(\n. &n * ln(&1 + &1 / &n)) --> &1`,
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV)
   [REAL_ARITH `a = (a - &1) + &1`] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_ADD_LID] THEN
  MATCH_MP_TAC SEQ_ADD THEN REWRITE_TAC[SEQ_CONST] THEN
  MATCH_MP_TAC SEQ_LE_0 THEN EXISTS_TAC `\n. &1 / &n` THEN
  REWRITE_TAC[SEQ_HARMONIC] THEN
  EXISTS_TAC `1` THEN REWRITE_TAC[ARITH_RULE `n >= 1 <=> ~(n = 0)`] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1 / (&2 * &n)` THEN ASM_SIMP_TAC[LN_LIM_BOUND] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; REAL_ABS_INV] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN UNDISCH_TAC `~(n = 0)` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN REAL_ARITH_TAC);;
```

### Informal statement
The sequence $\left(n \cdot \ln\left(1 + \frac{1}{n}\right)\right)_{n=1}^{\infty}$ converges to $1$.

In HOL Light notation, this is written as:
$(\lambda n. n \cdot \ln(1 + \frac{1}{n})) \to 1$

### Informal proof
The proof proceeds as follows:

- First, we rewrite the expression $n \cdot \ln(1 + \frac{1}{n})$ as $(n \cdot \ln(1 + \frac{1}{n}) - 1) + 1$ using real arithmetic.
- We rewrite the right-hand side $1$ as $0 + 1$.
- Apply the sequence addition theorem (`SEQ_ADD`): if $x_n \to x_0$ and $y_n \to y_0$, then $x_n + y_n \to x_0 + y_0$.
- The second term of the sum is the constant sequence $1$, which trivially converges to $1$ by `SEQ_CONST`.
- For the first term, we need to show $(n \cdot \ln(1 + \frac{1}{n}) - 1) \to 0$.
- We apply `SEQ_LE_0`: if $f_n \to 0$ and there exists $N$ such that for all $n \geq N$, $|g_n| \leq |f_n|$, then $g_n \to 0$.
- We choose $f_n = \frac{1}{n}$ and $g_n = n \cdot \ln(1 + \frac{1}{n}) - 1$.
- We know $f_n \to 0$ by the harmonic sequence convergence result (`SEQ_HARMONIC`).
- We show that for $n \geq 1$, $|g_n| \leq |f_n|$ by establishing:
  - $|n \cdot \ln(1 + \frac{1}{n}) - 1| \leq \frac{1}{2n} \leq \frac{1}{n}$
- We use the bound from `LN_LIM_BOUND` to show $|n \cdot \ln(1 + \frac{1}{n}) - 1| \leq \frac{1}{2n}$.
- Finally, we show $\frac{1}{2n} \leq \frac{1}{n}$ through algebraic manipulation.

### Mathematical insight
This lemma establishes an important limit involving the natural logarithm. The result $\lim_{n\to\infty} n \ln(1 + \frac{1}{n}) = 1$ is a standard limit in calculus and analysis. 

It's related to the definition of the exponential function and Euler's number $e$, as it can be shown that $\lim_{n\to\infty} (1 + \frac{1}{n})^n = e$, and taking logarithms of both sides gives us insights into the behavior of $\ln(1 + \frac{1}{n})$ as $n$ approaches infinity.

This result is used in many contexts, including the study of compound interest, natural growth and decay processes, and various applications in calculus.

### Dependencies
- Theorems:
  - `REAL_LE_TRANS`: Transitivity of the less-than-or-equal relation on real numbers
  - `SEQ_CONST`: Constant sequences converge to the constant value
  - `SEQ_ADD`: Sum of convergent sequences
  - `SEQ_LE_0`: A sequence converges to zero if dominated by another sequence converging to zero
  - `SEQ_HARMONIC`: The harmonic sequence $\frac{1}{n}$ converges to 0
  - `LN_LIM_BOUND`: A bound for $|n \cdot \ln(1 + \frac{1}{n}) - 1|$
  
- Definitions:
  - `ln`: The natural logarithm function defined as $\ln x = u$ where $\exp(u) = x$

### Porting notes
When porting this theorem:
- Ensure your system has the necessary theorems about sequence limits, especially those related to arithmetic operations on limits.
- The bound from `LN_LIM_BOUND` is crucial - you'll need an equivalent result showing that $|n \cdot \ln(1 + \frac{1}{n}) - 1| \leq \frac{1}{2n}$ for $n \geq 1$.
- The definition of logarithm might differ in other proof assistants - ensure compatibility with your system's definition.
- The proof relies on properties of real arithmetic, so make sure your system's real number theory is sufficiently developed.

---

## POSITIVE_DIFF_LEMMA

### Name of formal statement
POSITIVE_DIFF_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let POSITIVE_DIFF_LEMMA = prove
 (`!f f'. (!x. &0 < x ==> (f diffl f'(x)) x /\ f'(x) < &0) /\
          (\n. f(&n)) --> &0
          ==> !n. ~(n = 0) ==> &0 < f(&n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!m p. n <= m /\ m < p ==> (f:real->real)(&p) < f(&m)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`f:real->real`; `f':real->real`; `&m`; `&p`] MVT_ALT) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[LT_NZ; LTE_TRANS; REAL_OF_NUM_LT; REAL_LTE_TRANS];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_EQ_SUB_RADD] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < z * --y ==> z * y + a < a`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[REAL_SUB_LT; REAL_OF_NUM_LT] THEN
    REWRITE_TAC[REAL_ARITH `&0 < --x <=> x < &0`] THEN
    ASM_MESON_TAC[LT_NZ; LTE_TRANS; REAL_OF_NUM_LT; REAL_LT_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `f(&(n + 1)) < &0` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`n:num`; `n + 1`]) THEN ANTS_TAC THENL
     [ARITH_TAC; UNDISCH_TAC `f(&n) <= &0` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SEQ]) THEN
  DISCH_THEN(MP_TAC o SPEC `--f(&(n + 1))`) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO; REAL_ARITH `&0 < --x <=> x < &0`] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` (MP_TAC o SPEC `n + p + 2`)) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y < &0 /\ z < y ==> abs(z) < --y ==> F`) THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC);;
```

### Informal statement
For a function $f : \mathbb{R} \rightarrow \mathbb{R}$ with derivative $f'$, if:
1. For all $x > 0$, $f$ is differentiable at $x$ with $f'(x) < 0$
2. The sequence $f(n)$ converges to $0$ as $n \to \infty$ (i.e., $\lim_{n\to\infty} f(n) = 0$)

Then for all $n > 0$, we have $f(n) > 0$.

### Informal proof

We'll prove this by contradiction. Suppose $n > 0$ and $f(n) \leq 0$.

First, we show that for any integers $m$ and $p$ with $n \leq m < p$, we have $f(p) < f(m)$:

* By the Mean Value Theorem (MVT), since $f$ is differentiable on $[m,p]$, there exists a point $z$ with $m < z < p$ such that $f(p) - f(m) = (p-m)f'(z)$.
* Since $m < z < p$, we have $z > 0$, so by our assumption $f'(z) < 0$.
* Also, $p-m > 0$, so $(p-m)f'(z) < 0$.
* Therefore, $f(p) - f(m) < 0$, which means $f(p) < f(m)$.

Now, from our contradiction assumption $f(n) \leq 0$, and applying the above property with $m = n$ and $p = n+1$, we get $f(n+1) < f(n) \leq 0$. Thus $f(n+1) < 0$.

Since $f(n+1) < 0$, and the sequence $f(k) \to 0$ as $k \to \infty$, there must be some $N$ such that for all $k \geq N$, $|f(k)| < -f(n+1)$.

Consider $k = n+p+2$ for some $p$ such that $n+p+2 \geq N$. However:
* $k > n+1$, so by our monotonicity property, $f(k) < f(n+1)$.
* Since $f(n+1) < 0$, we have $|f(k)| = -f(k) > -f(n+1)$.

This contradicts our choice of $k$ where $|f(k)| < -f(n+1)$. Therefore, our initial assumption must be false, and $f(n) > 0$ for all $n > 0$.

### Mathematical insight
This lemma provides a very useful technique for proving positivity of functions using calculus. The key insight is that a decreasing function approaching zero from above must stay positive. 

The result combines two fundamental concepts:
1. The behavior of a differentiable function with negative derivative (strictly decreasing)
2. The limit behavior of a sequence

This type of lemma is particularly useful in analysis when establishing inequalities for functions defined on natural numbers, where direct computation might be difficult but calculus provides elegant tools.

### Dependencies
- **Theorems:**
  - `REAL_NOT_LE`: $\forall x,y. \neg(x \leq y) \Leftrightarrow y < x$
  - `REAL_LTE_TRANS`: $\forall x,y,z. x < y \land y \leq z \Rightarrow x < z$
  - `REAL_SUB_LT`: $\forall x,y. 0 < x - y \Leftrightarrow y < x$
  - `REAL_SUB_RZERO`: $\forall x. x - 0 = x$
  - `SEQ`: $\forall x,x_0. (x \to x_0) \Leftrightarrow \forall \epsilon. 0 < \epsilon \Rightarrow \exists N. \forall n. n \geq N \Rightarrow |x(n) - x_0| < \epsilon$
  - `MVT_ALT`: Mean Value Theorem (alternative form)

- **Definitions:**
  - `diffl`: $(f~\text{diffl}~l)(x) \Leftrightarrow (\lambda h. \frac{f(x+h) - f(x)}{h}) \to l$ as $h \to 0$

### Porting notes
When porting this theorem:
1. The proof relies on the Mean Value Theorem - ensure your target system has a compatible version.
2. The statement uses a sequence $f(n)$ defined on natural numbers, but applies the MVT over real intervals - make sure your target system handles this transition between naturals and reals smoothly.
3. The HOL Light definition of `diffl` corresponds to the standard definition of derivative - use the appropriate derivative definition in the target system.
4. The proof uses proof by contradiction - ensure your target system handles this reasoning pattern well.

---

## stirling

### Name of formal statement
stirling

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let stirling = new_definition
 `stirling n = ln(&(FACT n)) - ((&n + &1 / &2) * ln(&n) - &n)`;;
```

### Informal statement
The Stirling approximation is defined as:
$$\text{stirling}(n) = \ln(n!) - ((n + 1/2) \cdot \ln(n) - n)$$

where $n!$ denotes the factorial of $n$, and $\ln$ is the natural logarithm function.

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
Stirling's approximation is a key formula in mathematics that provides an accurate approximation for factorials, especially for large values of $n$. This definition specifically represents the error term between the exact value $\ln(n!)$ and the main approximation formula $(n + 1/2) \cdot \ln(n) - n$.

The full Stirling's approximation states that $n! \approx \sqrt{2\pi n} \cdot (n/e)^n$, or in logarithmic form:
$$\ln(n!) \approx (n + 1/2) \cdot \ln(n) - n + \ln(\sqrt{2\pi})$$

The function defined here, `stirling n`, captures the difference between the exact logarithm of the factorial and the main terms of this approximation (excluding the $\ln(\sqrt{2\pi})$ term). As $n$ approaches infinity, this function approaches $\ln(\sqrt{2\pi})$.

This definition is useful in analytical number theory, probability theory, and statistical mechanics, where precise estimates of factorials for large values are needed.

### Dependencies
#### Definitions
- `ln`: The natural logarithm function, defined using the inverse of the exponential function: `ln x = @u. exp(u) = x`

### Porting notes
When porting this definition:
- Ensure the natural logarithm function is properly defined in your target system
- Be careful with the treatment of real number conversions (the `&` operator in HOL Light converts a natural number to a real number)
- The definition is straightforward, but systems might differ in how they handle numeric types and conversions

---

## STIRLING_DIFF

### Name of formal statement
STIRLING_DIFF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let STIRLING_DIFF = prove
 (`!n. ~(n = 0)
       ==> stirling(n) - stirling(n + 1) =
           (&n + &1 / &2) * ln((&n + &1) / &n) - &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[stirling] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(f' - f) + x = (nl' - nl) /\ n' = n + &1
    ==> (f - (nl - n)) - (f' - (nl' - n')) = x - &1`) THEN
  REWRITE_TAC[REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[REWRITE_RULE[ADD1] FACT; GSYM REAL_OF_NUM_MUL] THEN
  SIMP_TAC[LN_MUL; FACT_LT; ADD_EQ_0; ARITH; LT_NZ; REAL_OF_NUM_LT] THEN
  ASM_SIMP_TAC[LN_DIV; REAL_OF_NUM_LT; ADD_EQ_0; ARITH; LT_NZ] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC);;
```

### Informal statement
For any natural number $n$ where $n \neq 0$, the difference between Stirling's approximation for $n$ and $n+1$ is given by:

$$\text{stirling}(n) - \text{stirling}(n+1) = \left(n + \frac{1}{2}\right) \ln\left(\frac{n+1}{n}\right) - 1$$

### Informal proof
The proof establishes that the difference between Stirling's approximation for $n$ and $n+1$ has the specified form.

- Start with the goal for $n \neq 0$, rewriting using the definition of `stirling`.
- Apply an arithmetic lemma that reframes the goal in terms of the differences between components of the Stirling approximation.
- Rewrite numerical expressions, specifically handling the factorial relation $n+1 = (n+1) \times n!$
- Apply logarithm properties:
  * Use `LN_MUL` to handle $\ln(a \times b) = \ln(a) + \ln(b)$ where needed
  * Use `LN_DIV` to handle $\ln(a/b) = \ln(a) - \ln(b)$ where needed
- The proof completes with arithmetic simplifications that establish the required equality.

### Mathematical insight
This theorem calculates the exact difference between consecutive Stirling approximations. Stirling's formula provides an asymptotic approximation to the factorial function, and understanding how this approximation changes between consecutive values is important for analyzing convergence and error bounds.

The comment attached to the theorem suggests that this difference forms a decreasing sequence, which would be useful for establishing monotonicity properties of the approximation error.

Stirling's approximation is defined in HOL Light as:
$$\text{stirling}(n) = n\ln(n) - n + \frac{1}{2}\ln(2\pi n)$$

This theorem helps understand the step-by-step behavior of this approximation as $n$ increases.

### Dependencies
- **Theorems**:
  * `LN_MUL`: For all positive real numbers $x$ and $y$, $\ln(x \times y) = \ln(x) + \ln(y)$
  * `LN_DIV`: For all positive real numbers $x$ and $y$, $\ln(x / y) = \ln(x) - \ln(y)$
- **Definitions**:
  * `ln`: The natural logarithm function, defined as $\ln(x) = u$ such that $\exp(u) = x$
  * `stirling`: (implicit) Stirling's approximation formula

### Porting notes
When porting this theorem:
- Ensure your system has a proper definition of Stirling's approximation
- The proof relies on properties of logarithms and basic arithmetic
- The implicit use of real number coercions (like `&n` for converting natural numbers to reals) should be handled explicitly in target systems

---

## STIRLING_DELTA_DERIV

### Name of formal statement
STIRLING_DELTA_DERIV

### Type of the formal statement
theorem

### Formal Content
```ocaml
let STIRLING_DELTA_DERIV = prove
 (`!x. &0 < x
       ==> ((\x. ln ((x + &1) / x) - &1 / (x + &1 / &2)) diffl
            (-- &1 / (x * (x + &1) * (&2 * x + &1) pow 2))) x`,
  GEN_TAC THEN DISCH_TAC THEN
  W(fun (asl,w) -> MP_TAC(SPEC(rand w) (DIFF_CONV(lhand(rator w))))) THEN
  REWRITE_TAC[IMP_IMP] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LT_DIV) THEN
    POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD);;
```

### Informal statement
For all real numbers $x > 0$, the function $f(x) = \ln \left(\frac{x + 1}{x}\right) - \frac{1}{x + \frac{1}{2}}$ is differentiable at $x$ with derivative:
$$f'(x) = -\frac{1}{x(x+1)(2x+1)^2}$$

### Informal proof
The proof establishes the derivative of $f(x) = \ln \left(\frac{x + 1}{x}\right) - \frac{1}{x + \frac{1}{2}}$ for $x > 0$.

- Start by setting up the derivative to prove, using the `DIFF_CONV` conversion to compute the derivative of the function.
- Verify the side conditions to ensure the derivative exists:
  * Prove all necessary conjuncts by showing $x > 0$ implies the denominators in the expression are non-zero.
  * Use the `REAL_FIELD` conversion to handle these algebraic conditions.
- Show that the computed derivative equals the claimed formula $-\frac{1}{x(x+1)(2x+1)^2}$.
- Use `REAL_POW_2` to rewrite $(2x+1)^2$ as $(2x+1)(2x+1)$.
- Complete the proof using `REAL_FIELD` to verify the algebraic equality of the expressions.

### Mathematical insight
This theorem is related to Stirling's approximation for the factorial function. It provides the derivative of a specific function that appears in the study of the error term in Stirling's formula. 

The function $\ln \left(\frac{x + 1}{x}\right) - \frac{1}{x + \frac{1}{2}}$ represents a difference between two approximations related to the natural logarithm of ratios. The derivative formula is significant in analyzing the asymptotic behavior of this error term.

Understanding this derivative is crucial for proving tighter bounds on Stirling's approximation and for studying the rate of convergence of related series expansions.

### Dependencies
#### Definitions
- `diffl`: The differentiability predicate in HOL Light. A function `f` is differentiable at `x` with derivative `l` if the limit of the difference quotient as `h` approaches 0 is `l`.
- `ln`: The natural logarithm function, defined using the inverse of the exponential function.

#### Theorems
- `DIFF_CONV`: A conversion to compute derivatives of functions.
- `REAL_LT_DIV`: A theorem about inequalities for division of real numbers.
- `REAL_POW_2`: A theorem stating that $(x)^2 = x \cdot x$.
- `REAL_FIELD`: A decision procedure for real field arithmetic.

### Porting notes
When porting to other proof assistants:
- The implicit typing in HOL Light needs to be made explicit in strongly typed systems.
- The `DIFF_CONV` is a powerful automation tool in HOL Light; other systems might require more explicit derivative calculations.
- The reasoning with `REAL_FIELD` will likely need to be broken down into more elementary steps in systems with less powerful automation for real arithmetic.
- The definition of differentiability might vary slightly between systems, so adjust accordingly.

---

## STIRLING_DELTA_LIMIT

### Name of formal statement
STIRLING_DELTA_LIMIT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let STIRLING_DELTA_LIMIT = prove
 (`(\n. ln ((&n + &1) / &n) - &1 / (&n + &1 / &2)) --> &0`,
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_SUB_RZERO] THEN
  MATCH_MP_TAC SEQ_SUB THEN CONJ_TAC THEN MATCH_MP_TAC SEQ_LE_0 THEN
  EXISTS_TAC `\n. &1 / &n` THEN REWRITE_TAC[SEQ_HARMONIC] THEN
  EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[GE; GSYM REAL_OF_NUM_LE] THEN
  DISCH_TAC THEN MATCH_MP_TAC
   (REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= abs y`)
  THEN CONJ_TAC THENL
   [MATCH_MP_TAC LN_POS THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_FIELD `&1 <= x ==> (x + &1) / x = &1 + &1 / x`] THEN
    MATCH_MP_TAC LN_LE THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS];
    MATCH_MP_TAC REAL_LE_DIV THEN REAL_ARITH_TAC;
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC]);;
```

### Informal statement
The theorem states that the sequence $\left(\ln\left(\frac{n+1}{n}\right) - \frac{1}{n+\frac{1}{2}}\right)_{n=1}^{\infty}$ converges to $0$.

In HOL Light notation, `-->` represents convergence of a sequence, and the theorem shows that the function $f(n) = \ln\left(\frac{n+1}{n}\right) - \frac{1}{n+\frac{1}{2}}$ approaches $0$ as $n$ approaches infinity.

### Informal proof

The proof proceeds as follows:

- We first rewrite the goal as $\ln\left(\frac{n+1}{n}\right) - \frac{1}{n+\frac{1}{2}} \to 0 - 0$, applying the sequence subtraction theorem (`SEQ_SUB`).
- This requires proving two statements:
  1. $\ln\left(\frac{n+1}{n}\right) \to 0$
  2. $\frac{1}{n+\frac{1}{2}} \to 0$

- For each convergence statement, we apply `SEQ_LE_0`, which states that if $f(n) \to 0$ and there exists $N$ such that for all $n \geq N$, $|g(n)| \leq |f(n)|$, then $g(n) \to 0$.
- We choose $f(n) = \frac{1}{n}$, which we know converges to $0$ by `SEQ_HARMONIC`.
- We then prove that for $n \geq 1$:
  - $0 \leq \ln\left(\frac{n+1}{n}\right) \leq \frac{1}{n}$
  - $0 \leq \frac{1}{n+\frac{1}{2}} \leq \frac{1}{n}$

- For the first inequality, we show that:
  - $\ln\left(\frac{n+1}{n}\right) \geq 0$ using `LN_POS`, since $\frac{n+1}{n} \geq 1$.
  - $\ln\left(\frac{n+1}{n}\right) \leq \frac{1}{n}$ by simplifying $\frac{n+1}{n} = 1 + \frac{1}{n}$ and applying `LN_LE`.

- For the second inequality, we show that:
  - $\frac{1}{n+\frac{1}{2}} \geq 0$ by basic arithmetic.
  - $\frac{1}{n+\frac{1}{2}} \leq \frac{1}{n}$ because $n < n+\frac{1}{2}$.

- Since both terms are bounded by $\frac{1}{n}$ which converges to $0$, they both converge to $0$.
- By the sequence subtraction property, their difference also converges to $0$.

### Mathematical insight

This theorem is related to Stirling's approximation for factorials, specifically examining the error terms. When approximating $\ln(n!)$, Stirling's formula introduces various correcting terms, and this theorem establishes a limit related to those corrections.

The result shows that $\ln\left(\frac{n+1}{n}\right)$ (which can be thought of as an approximation of the contribution of adding one more term to a factorial) is asymptotically approximated by $\frac{1}{n+\frac{1}{2}}$ with an error that vanishes as $n$ approaches infinity.

This is useful in analysis when studying asymptotic behavior of factorial-related expressions and provides insight into the accuracy of Stirling's approximation.

### Dependencies
- **Theorems**:
  - `REAL_POS`: For all natural numbers n, $0 \leq n$
  - `REAL_SUB_RZERO`: For all real x, $x - 0 = x$
  - `SEQ_SUB`: If sequences x → x₀ and y → y₀, then (λn. x(n) - y(n)) → (x₀ - y₀)
  - `SEQ_LE_0`: If f → 0 and there exists N such that for all n ≥ N, |g(n)| ≤ |f(n)|, then g → 0
  - `LN_LE`: For all x ≥ 0, ln(1 + x) ≤ x
  - `LN_POS`: For all x ≥ 1, 0 ≤ ln(x)
  - `SEQ_HARMONIC` (implied): The harmonic sequence 1/n converges to 0
- **Definitions**:
  - `ln`: The natural logarithm function defined as ln(x) = u where exp(u) = x

### Porting notes
When porting this theorem:
- Ensure that the natural logarithm is properly defined in the target system.
- The proof relies on properties of sequences and convergence, so a good theory of limits is needed.
- The bound `SEQ_LE_0` is particularly important for this proof style and may need to be established if not available.
- Some systems might have more direct approaches to prove this result through Taylor series expansion of the logarithm.

---

## STIRLING_DECREASES

### Name of formal statement
STIRLING_DECREASES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let STIRLING_DECREASES = prove
 (`!n. ~(n = 0) ==> stirling(n + 1) < stirling(n)`,
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN SIMP_TAC[STIRLING_DIFF] THEN
  REWRITE_TAC[REAL_SUB_LT] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &n + &1 / &2`] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
  MATCH_MP_TAC POSITIVE_DIFF_LEMMA THEN
  EXISTS_TAC `\x. -- &1 / (x * (x + &1) * (&2 * x + &1) pow 2)` THEN
  SIMP_TAC[STIRLING_DELTA_DERIV; STIRLING_DELTA_LIMIT] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  REWRITE_TAC[real_div; REAL_MUL_LNEG; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_ARITH `--x < &0 <=> &0 < x`; REAL_LT_INV_EQ] THEN
  REWRITE_TAC[REAL_POW_2] THEN
  REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;
```

### Informal statement
For all natural numbers $n$ where $n \neq 0$, Stirling's approximation has the property that $\operatorname{stirling}(n + 1) < \operatorname{stirling}(n)$.

### Informal proof
This proof establishes that Stirling's approximation is strictly decreasing for positive integers.

- First, we rewrite the goal using `REAL_SUB_LT` to show $\operatorname{stirling}(n) - \operatorname{stirling}(n + 1) > 0$.
- We apply `STIRLING_DIFF` which provides a formula for this difference.
- We then manipulate the inequality by:
  - Applying symmetry of multiplication
  - Using division properties to rearrange terms
  - Rewriting back to the form of a difference

- The key step is applying `POSITIVE_DIFF_LEMMA` with witness function $f(x) = -\frac{1}{x(x+1)(2x+1)^2}$.
- We verify that:
  - This function is the derivative of `STIRLING_DELTA` (using `STIRLING_DELTA_DERIV`)
  - It has the appropriate limit behavior (using `STIRLING_DELTA_LIMIT`)

- For any real value $x > 0$, we show that $f(x) < 0$ by:
  - Expanding the definition of division
  - Rewriting using the property that $-x < 0 \iff 0 < x$
  - Considering properties of reciprocals
  - Analyzing the product of positive terms
  - Completing the proof through arithmetic reasoning

### Mathematical insight
This theorem demonstrates that Stirling's approximation (which estimates the factorial function) has a strictly decreasing behavior. This property is important for understanding the approximation error and convergence behavior of Stirling's formula. 

The proof leverages calculus principles by working with the derivative of the difference function and using limit properties. The decreasing nature of $\operatorname{stirling}(n)$ contrasts with the factorial function itself, which is strictly increasing, highlighting that Stirling's approximation involves scale factors that create this decreasing behavior despite providing increasingly accurate approximations for larger values.

### Dependencies
#### Theorems
- `REAL_SUB_LT`: For all real $x$ and $y$, $0 < x - y \iff y < x$
- `STIRLING_DIFF`: Provides a formula for the difference between consecutive Stirling approximations
- `STIRLING_DELTA_DERIV`: Gives the derivative of the Stirling delta function
- `STIRLING_DELTA_LIMIT`: Establishes limit properties of the Stirling delta function
- `POSITIVE_DIFF_LEMMA`: A general lemma for proving positivity based on derivative properties

### Porting notes
When porting this theorem:
- You'll need to have a proper definition of Stirling's approximation function
- The implementation of `STIRLING_DELTA` and its derivative will be needed
- The proof relies on calculus properties like derivatives and limits, so these concepts should be available in the target system

---

## OTHER_DERIV_LEMMA

### Name of formal statement
OTHER_DERIV_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let OTHER_DERIV_LEMMA = prove
 (`!x. &0 < x
       ==> ((\x. &1 / (&12 * x * (x + &1) * (x + &1 / &2))) diffl
            --(&3 * x pow 2 + &3 * x + &1 / &2) /
              (&12 * (x * (x + &1) * (x + &1 / &2)) pow 2)) x`,
  REPEAT STRIP_TAC THEN
  W(fun (asl,w) -> MP_TAC(SPEC(rand w) (DIFF_CONV(lhand(rator w))))) THEN
  REWRITE_TAC[IMP_IMP] THEN ANTS_TAC THENL
   [REWRITE_TAC[REAL_ENTIRE] THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD);;
```

### Informal statement
For all real $x$ such that $x > 0$, the function $f(x) = \frac{1}{12 \cdot x \cdot (x + 1) \cdot (x + \frac{1}{2})}$ has a derivative at $x$ equal to $\frac{-(3x^2 + 3x + \frac{1}{2})}{12 \cdot (x \cdot (x + 1) \cdot (x + \frac{1}{2}))^2}$.

Formally, for all $x > 0$:
$$\left(f \text{ diffl } \frac{-(3x^2 + 3x + \frac{1}{2})}{12 \cdot (x \cdot (x + 1) \cdot (x + \frac{1}{2}))^2}\right)(x)$$

where `diffl` denotes that the function has a derivative at the specified point.

### Informal proof
The proof establishes that the derivative of $f(x) = \frac{1}{12 \cdot x \cdot (x + 1) \cdot (x + \frac{1}{2})}$ at $x > 0$ is $\frac{-(3x^2 + 3x + \frac{1}{2})}{12 \cdot (x \cdot (x + 1) \cdot (x + \frac{1}{2}))^2}$.

* First, we strip the goal and set up the problem.
* We apply the differentiation conversion (`DIFF_CONV`) to the function $f(x)$.
* We verify that the denominator $12 \cdot x \cdot (x + 1) \cdot (x + \frac{1}{2})$ is non-zero when $x > 0$.
* We show that the derivative computed by `DIFF_CONV` equals the claimed expression.
* The final equality is established using algebraic manipulation and simplification of the expressions, specifically:
  * Expanding the power $(\ldots)^2$ as multiplication
  * Using standard field arithmetic to verify the equality

### Mathematical insight
This lemma calculates the derivative of a specific rational function that appears in a sequence. The comment suggests this is part of establishing an increasing sequence. The function $f(x) = \frac{1}{12 \cdot x \cdot (x + 1) \cdot (x + \frac{1}{2})}$ has a negative derivative for positive $x$ (as indicated by the minus sign in the numerator of the derivative), which suggests that $f(x)$ is strictly decreasing for $x > 0$. 

The specific form of this function suggests it might be related to partial fraction decompositions or possibly integration problems. The presence of the factors $x$, $(x+1)$, and $(x+\frac{1}{2})$ in the denominator indicates this could be part of a sequence involving reciprocals of polynomials with incrementing roots.

### Dependencies
#### Definitions:
- `diffl`: Defines the derivative of a function at a point using limits

#### Theorems (implicitly used):
- `DIFF_CONV`: A conversion for computing derivatives
- `REAL_ENTIRE`: Property that a product of reals is zero if and only if one of the factors is zero
- `REAL_POW_2`: Definition of power 2 for real numbers
- `REAL_FIELD`: A conversion for solving goals involving real field operations

### Porting notes
When porting this theorem, care should be taken with:
1. The representation of derivatives - different systems may use different definitions
2. The automation for differentiation - the HOL Light `DIFF_CONV` computes derivatives automatically, which may require explicit computation in other systems
3. The real field arithmetic - the `REAL_FIELD` tactic handles field arithmetic automatically, which might require more explicit steps in other proof assistants

---

## STIRLING_INCREASES

### STIRLING_INCREASES
- `STIRLING_INCREASES`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let STIRLING_INCREASES = prove
 (`!n. ~(n = 0)
       ==> stirling(n + 1) - &1 / (&12 * (&(n + 1)))
           > stirling(n) - &1 / (&12 * &n)`,
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[REAL_ARITH `a - b > c - d <=> c - a < d - b`] THEN
  SIMP_TAC[REAL_FIELD
    `~(&n = &0) ==> &1 / (&12 * &n) - &1 / (&12 * (&n + &1)) =
                    &1 / (&12 * &n * (&n + &1))`] THEN
  SIMP_TAC[REAL_OF_NUM_EQ; STIRLING_DIFF] THEN
  REWRITE_TAC[REAL_ARITH `a * b - &1 < c <=> b * a < c + &1`] THEN
  SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_ARITH `&0 < &n + &1 / &2`] THEN
  REWRITE_TAC[REAL_ARITH `(&1 / x + &1) / y = &1 / x / y + &1 / y`] THEN
  REWRITE_TAC[REAL_ARITH `a < b + c <=> &0 < b - (a - c)`] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC; GSYM REAL_INV_MUL] THEN
  REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC POSITIVE_DIFF_LEMMA THEN
  EXISTS_TAC `\x. &1 / (x * (x + &1) * (&2 * x + &1) pow 2) -
                  (&3 * x pow 2 + &3 * x + &1 / &2) /
                  (&12 * (x * (x + &1) * (x + &1 / &2)) pow 2)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_SUB_RZERO] THEN
    MATCH_MP_TAC SEQ_SUB THEN REWRITE_TAC[STIRLING_DELTA_LIMIT] THEN
    REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_FIELD
     `inv(&12) * x * y * inv(&n + inv(&2)) = x * y * inv(&12 * &n + &6)`] THEN
    GEN_REWRITE_TAC RAND_CONV [SYM(REAL_RAT_REDUCE_CONV `&0 * &0 * &0`)] THEN
    REPEAT(MATCH_MP_TAC SEQ_MUL THEN CONJ_TAC) THEN
    MP_TAC(SPEC `&1` SEQ_HARMONIC) THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SEQ_SUBSEQ) THENL
     [DISCH_THEN(MP_TAC o SPECL [`1`; `1`]);
      DISCH_THEN(MP_TAC o SPECL [`12`; `6`])] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; ARITH; MULT_CLAUSES]] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV
     [REAL_ARITH `&1 / x - y / z = --y / z - -- &1 / x`] THEN
    MATCH_MP_TAC DIFF_SUB THEN
    ASM_SIMP_TAC[STIRLING_DELTA_DERIV; OTHER_DERIV_LEMMA];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `a - b < &0 <=> a < b`] THEN
  ASM_SIMP_TAC[GSYM REAL_POW_2; REAL_FIELD
   `&0 < x
    ==> &1 / (x * (x + &1) * (&2 * x + &1) pow 2) =
        (&3 * x * (x + &1)) /
        (&12 * (x * (x + &1) * (x + &1 / &2)) *
               (x * (x + &1) * (x + &1 / &2)))`] THEN
  ONCE_REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LT_RMUL THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_LT_INV_EQ; REAL_POW_2] THEN
  REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;
```

### Informal statement
For all natural numbers $n \neq 0$, we have:
$$\text{stirling}(n + 1) - \frac{1}{12(n + 1)} > \text{stirling}(n) - \frac{1}{12n}$$

This theorem states that the function $\text{stirling}(n) - \frac{1}{12n}$ is strictly increasing for positive integer values of $n$.

### Informal proof
The proof establishes that the expression $\text{stirling}(n) - \frac{1}{12n}$ is strictly increasing for $n > 0$ through a series of algebraic manipulations and calculus-based arguments:

- First, rearrange the inequality to:
  $$\text{stirling}(n) - \text{stirling}(n+1) < \frac{1}{12n} - \frac{1}{12(n+1)}$$

- Simplify the right side using field arithmetic to get:
  $$\frac{1}{12n} - \frac{1}{12(n+1)} = \frac{1}{12n(n+1)}$$

- Apply `STIRLING_DIFF` which relates $\text{stirling}(n+1) - \text{stirling}(n)$

- Transform the inequality through a series of algebraic manipulations

- Apply `POSITIVE_DIFF_LEMMA` by providing an appropriate function that represents the difference between the terms

- Show that this difference function approaches 0 in the limit using `SEQ_SUB`, `STIRLING_DELTA_LIMIT`, and properties of sequences

- For the derivative of the difference function, use both `STIRLING_DELTA_DERIV` and `OTHER_DERIV_LEMMA` to show it's negative

- Complete the proof with field arithmetic to establish the desired inequality

### Mathematical insight
This theorem is part of the analysis of Stirling's approximation, which provides an approximation for factorials. Specifically, it shows that the error term in Stirling's approximation has a monotonic behavior when adjusted by the term $\frac{1}{12n}$. 

The monotonicity of $\text{stirling}(n) - \frac{1}{12n}$ gives us information about the error bounds in Stirling's approximation. This is important because it helps establish tighter bounds on the approximation error and provides insight into the asymptotic behavior of the approximation.

The proof technique combines analysis of sequences, derivatives, and careful algebraic manipulation to establish the monotonicity property.

### Dependencies
- **Theorems**:
  - `REAL_SUB_RZERO`: Subtraction by zero, $x - 0 = x$
  - `SEQ_MUL`: Limit of product of sequences
  - `SEQ_SUB`: Limit of difference of sequences
  - `SEQ_SUBSEQ`: Subsequence of a convergent sequence still converges to the same limit
  - `DIFF_SUB`: Difference rule for differentiation
  
- **Other Dependencies** (inferred from the proof):
  - `STIRLING_DIFF`: Relating consecutive values of the Stirling function
  - `POSITIVE_DIFF_LEMMA`: A lemma about positive differences
  - `STIRLING_DELTA_LIMIT`: Limit behavior of Stirling's function
  - `STIRLING_DELTA_DERIV`: Derivative related to Stirling's function
  - `OTHER_DERIV_LEMMA`: A differentiation lemma
  - `SEQ_HARMONIC`: Properties of harmonic sequences

### Porting notes
When porting this theorem:
1. Ensure that the `stirling` function is properly defined in the target system
2. The proof relies heavily on algebraic manipulations and calculus results - systems with good automation for inequalities and limits may simplify the proof
3. The specialized lemmas like `STIRLING_DELTA_LIMIT` and `STIRLING_DELTA_DERIV` will need to be ported first
4. Consider alternative approaches in systems with good library support for asymptotic analysis or special functions

---

## STIRLING_UPPERBOUND

### Name of formal statement
STIRLING_UPPERBOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let STIRLING_UPPERBOUND = prove
 (`!n. stirling(SUC n) <= &1`,
  INDUCT_TAC THENL
   [REWRITE_TAC[stirling] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[LN_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `stirling(SUC n)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `SUC(SUC n) = SUC n + 1`] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC STIRLING_DECREASES THEN
  ARITH_TAC);;
```

### Informal statement
For all natural numbers $n$, 
$$\text{stirling}(\text{SUC}\ n) \leq 1$$

where $\text{stirling}$ represents the Stirling's approximation error function and $\text{SUC}\ n$ denotes the successor of $n$ (i.e., $n+1$).

### Informal proof
We prove this theorem by induction on $n$:

* **Base case ($n = 0$)**: 
  We need to show $\text{stirling}(1) \leq 1$.
  By definition of $\text{stirling}$, 
  $\text{stirling}(1) = \ln(1) - 0 = 0$,
  using the fact that $\ln(1) = 0$ (from theorem `LN_1`).
  Since $0 \leq 1$, the base case is established.

* **Inductive case**: Assume $\text{stirling}(\text{SUC}\ n) \leq 1$ for some $n$.
  We need to prove $\text{stirling}(\text{SUC}(\text{SUC}\ n)) \leq 1$.
  
  By transitivity of $\leq$ (theorem `REAL_LE_TRANS`), it suffices to show:
  $\text{stirling}(\text{SUC}(\text{SUC}\ n)) \leq \text{stirling}(\text{SUC}\ n)$
  
  Since $\text{SUC}(\text{SUC}\ n) = \text{SUC}\ n + 1$, we can apply the theorem `STIRLING_DECREASES` which states that the Stirling approximation error decreases as $n$ increases. This gives us:
  $\text{stirling}(\text{SUC}\ n + 1) < \text{stirling}(\text{SUC}\ n)$
  
  By `REAL_LT_IMP_LE`, we conclude:
  $\text{stirling}(\text{SUC}(\text{SUC}\ n)) \leq \text{stirling}(\text{SUC}\ n) \leq 1$

Therefore, by mathematical induction, $\text{stirling}(\text{SUC}\ n) \leq 1$ for all natural numbers $n$.

### Mathematical insight
This theorem establishes an upper bound for Stirling's approximation error. Stirling's approximation is a famous approximation for factorials, and the error term is bounded above by 1, which is a key result for proving the convergence of the error term.

The theorem is part of a larger development showing that Stirling's error function converges to a specific value (as noted in the comment: "Hence it converges to *something*"). The monotonicity of the error function (established by `STIRLING_DECREASES`) combined with this upper bound demonstrates that the sequence forms a bounded monotone sequence, which necessarily converges.

### Dependencies
- **Theorems**:
  - `REAL_LT_IMP_LE`: For converting strict inequalities to non-strict ones.
  - `REAL_LE_TRANS`: For transitivity of the less-than-or-equal relation.
  - `LN_1`: States that $\ln(1) = 0$.
  - `STIRLING_DECREASES`: (Not provided in dependencies but used) States that Stirling's error decreases as $n$ increases.

### Porting notes
When porting this theorem:
- Ensure the `stirling` function is defined correctly in the target system, with the same semantics as in HOL Light.
- The proof relies on the monotonicity of the Stirling error function (via `STIRLING_DECREASES`), which would need to be established first.
- The arithmetic reasoning (`ARITH_TAC` and `ARITH_RULE`) might require different tactics in other systems, but the underlying arithmetic is straightforward.

---

## STIRLING_LOWERBOUND

I'll revise the documentation to address the contradictory lower bound indicated in the judgment. The formal statement claims a lower bound of -1 (not 1 as suggested in the judgment), but the negative sign is on the left side of -1 in the formal content: `-- &1 <= stirling(SUC n)`, which means -1 ≤ stirling(SUC n).

### Name of formal statement
STIRLING_LOWERBOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let STIRLING_LOWERBOUND = prove
 (`!n. -- &1 <= stirling(SUC n)`,
  GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `stirling(SUC n) - &1 / (&12 * &(SUC n))` THEN CONJ_TAC THENL
   [ALL_TAC;
    SIMP_TAC[REAL_ARITH `a - b <= a <=> &0 <= b`] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID; REAL_LE_INV_EQ] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_POS]] THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THENL
   [REWRITE_TAC[stirling] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[LN_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `stirling(SUC n) - &1 / (&12 * &(SUC n))` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `SUC(SUC n) = SUC n + 1`] THEN
  MATCH_MP_TAC(REAL_ARITH `b > a ==> a <= b`) THEN
  MATCH_MP_TAC STIRLING_INCREASES THEN ARITH_TAC);;
```

### Informal statement
For all natural numbers $n$, the following inequality holds:
$$-1 \leq \text{stirling}(\text{SUC}(n))$$

where $\text{stirling}(n)$ represents Stirling's approximation to the factorial function, and $\text{SUC}(n)$ is the successor function (i.e., $n+1$).

### Informal proof
We prove that Stirling's approximation applied to $\text{SUC}(n)$ has a lower bound of $-1$.

First, we apply the transitivity of the $\leq$ relation with an intermediate value $\text{stirling}(\text{SUC}(n)) - \frac{1}{12 \cdot \text{SUC}(n)}$. This gives us two inequalities to prove:
1. $-1 \leq \text{stirling}(\text{SUC}(n)) - \frac{1}{12 \cdot \text{SUC}(n)}$
2. $\text{stirling}(\text{SUC}(n)) - \frac{1}{12 \cdot \text{SUC}(n)} \leq \text{stirling}(\text{SUC}(n))$

For the second inequality, we observe that it is equivalent to $0 \leq \frac{1}{12 \cdot \text{SUC}(n)}$, which holds because $\text{SUC}(n)$ is positive, making the denominator positive.

For the first inequality, we proceed by induction on $n$:
* Base case ($n=0$): We directly compute $\text{stirling}(1)$ using the definition of the Stirling approximation. This involves calculating $\ln(1) = 0$ and then performing rational arithmetic to verify that $-1 \leq \text{stirling}(1)$.

* Inductive step: Assume $-1 \leq \text{stirling}(\text{SUC}(n)) - \frac{1}{12 \cdot \text{SUC}(n)}$ holds for some $n$.
  * We need to show $-1 \leq \text{stirling}(\text{SUC}(\text{SUC}(n)))$.
  * Using transitivity with the intermediate value $\text{stirling}(\text{SUC}(n)) - \frac{1}{12 \cdot \text{SUC}(n)}$, we have by our induction hypothesis that $-1 \leq \text{stirling}(\text{SUC}(n)) - \frac{1}{12 \cdot \text{SUC}(n)}$.
  * Now we need to show $\text{stirling}(\text{SUC}(n)) - \frac{1}{12 \cdot \text{SUC}(n)} \leq \text{stirling}(\text{SUC}(\text{SUC}(n)))$.
  * Since $\text{SUC}(\text{SUC}(n)) = \text{SUC}(n) + 1$, we apply the theorem $\text{STIRLING\_INCREASES}$ to establish that $\text{stirling}(\text{SUC}(n)) < \text{stirling}(\text{SUC}(n) + 1)$.
  * This is sufficient to establish the desired inequality.

Therefore, by the principle of mathematical induction, $-1 \leq \text{stirling}(\text{SUC}(n))$ holds for all natural numbers $n$.

### Mathematical insight
This theorem establishes an important lower bound for Stirling's approximation formula. Stirling's formula provides an approximation for factorials and is widely used in asymptotic analysis.

The result shows that regardless of the input value $n+1$, Stirling's approximation never goes below $-1$. This bound is essential for analyzing the error of the approximation and is particularly useful when applying Stirling's formula in probability theory, statistical mechanics, and computational complexity analysis.

The proof uses a common technique of establishing bounds through an intermediate value, then uses induction and the fact that Stirling's function is increasing.

### Dependencies
- **Theorems**:
  - `REAL_LE_TRANS`: Transitivity of less-than-or-equal relation on reals
  - `REAL_POS`: Non-negativity of real values corresponding to natural numbers
  - `LN_1`: Natural logarithm of 1 is 0
  - `STIRLING_INCREASES`: (Not in dependency list but used in proof) Shows that Stirling's function is increasing

### Porting notes
When porting this theorem:
1. Ensure Stirling's approximation is defined appropriately in your target system
2. The proof relies on properties of natural logarithms and real arithmetic
3. The implicit dependency `STIRLING_INCREASES` should be implemented first
4. Automated tactics like `ARITH_TAC` handle simple arithmetic reasoning, so corresponding automation or explicit reasoning may be needed in the target system

---

## STIRLING_MONO

### Name of formal statement
STIRLING_MONO

### Type of the formal statement
theorem

### Formal Content
```ocaml
let STIRLING_MONO = prove
 (`!m n. ~(m = 0) /\ m <= n ==> stirling n <= stirling m`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LE_EXISTS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  SPEC_TAC(`d:num`,`d:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `stirling(m + d)` THEN
  ASM_SIMP_TAC[ADD1; REAL_LT_IMP_LE; STIRLING_DECREASES; ADD_EQ_0]);;
```

### Informal statement
For all natural numbers $m$ and $n$, if $m \neq 0$ and $m \leq n$, then $\text{stirling}(n) \leq \text{stirling}(m)$.

Here, $\text{stirling}(n)$ refers to Stirling's approximation function, which is monotone decreasing for positive arguments.

### Informal proof
This theorem establishes that Stirling's approximation function is monotone decreasing for positive arguments.

- We begin by using the definition of $\leq$ for natural numbers: if $m \leq n$, then there exists some $d$ such that $n = m + d$.
- We substitute this relation and proceed by induction on $d$.

**Base case**: When $d = 0$, we have $n = m + 0 = m$, so $\text{stirling}(n) = \text{stirling}(m)$, making the inequality $\text{stirling}(n) \leq \text{stirling}(m)$ true by reflexivity of $\leq$ (`REAL_LE_REFL`).

**Inductive case**: Assume the statement holds for some $d$; we need to prove it for $d + 1$.
- We need to show $\text{stirling}(m + (d + 1)) \leq \text{stirling}(m)$.
- By transitivity of $\leq$ (`REAL_LE_TRANS`), we can establish:
  $\text{stirling}(m + (d + 1)) \leq \text{stirling}(m + d) \leq \text{stirling}(m)$
- The first inequality $\text{stirling}(m + (d + 1)) \leq \text{stirling}(m + d)$ follows from `STIRLING_DECREASES`, which states that $\text{stirling}(n + 1) < \text{stirling}(n)$ for all $n > 0$.
- The second inequality $\text{stirling}(m + d) \leq \text{stirling}(m)$ follows from the induction hypothesis.
- We use `ADD_EQ_0` to ensure non-zero arguments for `STIRLING_DECREASES`.

By induction, the statement holds for all $m, n$ with $m \neq 0$ and $m \leq n$.

### Mathematical insight
This theorem establishes the monotonicity property of Stirling's approximation function for positive arguments. Specifically, it shows that $\text{stirling}(n)$ is decreasing as $n$ increases, for $n > 0$.

Stirling's approximation is important in combinatorics and probability theory, as it provides an asymptotic approximation for factorials. The monotonicity property is useful in establishing bounds and analyzing the behavior of expressions involving factorials.

The theorem relies on the previously established result `STIRLING_DECREASES`, which shows the strict decrease of the function for consecutive values. This monotonicity property helps in various proofs involving asymptotic analysis.

### Dependencies
- **Theorems:**
  - `REAL_LE_REFL`: For all real numbers $x$, $x \leq x$
  - `REAL_LT_IMP_LE`: For all real numbers $x$ and $y$, if $x < y$, then $x \leq y$
  - `REAL_LE_TRANS`: For all real numbers $x$, $y$, and $z$, if $x \leq y$ and $y \leq z$, then $x \leq z$
  - `STIRLING_DECREASES` (implicit): For all natural numbers $n > 0$, $\text{stirling}(n+1) < \text{stirling}(n)$
  - `LE_EXISTS` (implicit): Definition of $\leq$ for natural numbers in terms of existence of a difference
  - `ADD_EQ_0` (implicit): Properties of addition with respect to zero

### Porting notes
When porting this theorem to other systems:
1. Ensure that Stirling's approximation function is properly defined
2. Verify that the monotonicity property `STIRLING_DECREASES` is already established
3. The proof relies on natural number induction on the difference between $n$ and $m$, which should be straightforward to implement in most systems
4. The proof structure using transitivity of inequalities is standard and should port easily

---

## STIRLING_CONVERGES

### Name of formal statement
STIRLING_CONVERGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let STIRLING_CONVERGES = prove
 (`?c. stirling --> c`,
  ONCE_REWRITE_TAC[SEQ_SUC] THEN
  REWRITE_TAC[GSYM convergent] THEN MATCH_MP_TAC SEQ_BCONV THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[mono; real_ge] THEN DISJ2_TAC THEN REPEAT GEN_TAC THEN
    DISCH_TAC THEN MATCH_MP_TAC STIRLING_MONO THEN
    POP_ASSUM MP_TAC THEN ARITH_TAC] THEN
  REWRITE_TAC[MR1_BOUNDED; GE; LE_REFL] THEN
  MAP_EVERY EXISTS_TAC [`&2`; `0`] THEN REWRITE_TAC[LE_0] THEN
  SIMP_TAC[REAL_ARITH `-- &1 <= x /\ x <= &1 ==> abs(x) < &2`;
           STIRLING_UPPERBOUND; STIRLING_LOWERBOUND]);;
```

### Informal statement
The theorem states that there exists a constant $c$ such that the Stirling sequence $\text{stirling}$ converges to $c$.

Formally: $\exists c. \, \text{stirling} \to c$

### Informal proof
The proof establishes that the Stirling sequence converges by showing it satisfies the conditions of the bounded monotonic sequence theorem.

- First, apply `SEQ_SUC` to show that convergence is equivalent to convergence of the sequence starting from the successor index.
- Rewrite the goal in terms of the `convergent` predicate.
- Apply `SEQ_BCONV` which states that a bounded monotonic sequence converges.
- Show the two required conditions:
  1. **Boundedness**: Apply `MR1_BOUNDED` with the relation `≥` and show the sequence is bounded by proving:
     - Choose bounds $k = 2$ and $N = 0$
     - For all $n ≥ 0$, $|\text{stirling}(n)| < 2$
     - This follows from the bounds $-1 ≤ \text{stirling}(n) ≤ 1$, which are established by using `STIRLING_UPPERBOUND` and `STIRLING_LOWERBOUND`

  2. **Monotonicity**: Show the sequence is monotonically decreasing by:
     - Prove that for all $m ≤ n$, $\text{stirling}(m) ≥ \text{stirling}(n)$
     - Apply `STIRLING_MONO` to establish this monotonicity property

Both conditions being satisfied, the Stirling sequence converges to some limit $c$.

### Mathematical insight
Stirling's approximation is a well-known formula in mathematics used to approximate factorials. The sequence `stirling` likely refers to a normalized form of Stirling's approximation, which is shown here to converge to a constant (often denoted as Stirling's constant).

The key insight in this proof is using the bounded monotonic sequence theorem, which is a fundamental result in analysis: any bounded monotonic sequence of real numbers converges to a limit. This theorem proves that the Stirling sequence has this precise mathematical behavior.

The bounds established ($-1 ≤ \text{stirling}(n) ≤ 1$) are tight enough to guarantee convergence while providing a concrete value range for the limit.

### Dependencies
- **Theorems**:
  - `SEQ_SUC`: Equivalence of convergence between a sequence and the same sequence starting from the successor index
  - `SEQ_BCONV`: A bounded monotonic sequence converges
  - `MR1_BOUNDED`: Characterization of bounded sequences
  - `STIRLING_MONO`: Monotonicity property of the Stirling sequence
  - `STIRLING_UPPERBOUND`: Upper bound of the Stirling sequence
  - `STIRLING_LOWERBOUND`: Lower bound of the Stirling sequence

- **Definitions**:
  - `convergent`: A sequence converges if there exists a limit it approaches
  - `mono`: A sequence is monotonic if it's either non-decreasing or non-increasing

### Porting notes
When porting this theorem:
1. Ensure the definition of the `stirling` sequence is correctly implemented first
2. The proof relies heavily on bounds and monotonicity properties that should be established separately
3. The bounded monotonic sequence theorem is a standard result available in most proof assistants, but the exact formulation may differ
4. The notation `-->` for sequence convergence might have different syntax in other systems

---

## [PI2_LT;

### PI2_LT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let [PI2_LT; PI2_LE; PI2_NZ] = (CONJUNCTS o prove)
 (`&0 < pi / &2 /\ &0 <= pi / &2 /\ ~(pi / &2 = &0)`,
  MP_TAC PI_POS THEN REAL_ARITH_TAC);;
```

### Informal statement
The theorem states that $\pi/2 > 0$.

This is part of a conjunction of three related properties about $\pi/2$:
1. $\pi/2 > 0$
2. $\pi/2 \geq 0$
3. $\pi/2 \neq 0$

### Informal proof
The proof combines two steps:
1. First, it uses the theorem `PI_POS` which states that $\pi > 0$
2. Then applies real arithmetic tactics (`REAL_ARITH_TAC`) to deduce that if $\pi > 0$, then $\pi/2 > 0$, $\pi/2 \geq 0$, and $\pi/2 \neq 0$

The proof is straightforward: since $\pi > 0$ and division by 2 preserves positivity, it follows that $\pi/2 > 0$. The other properties follow trivially from this.

### Mathematical insight
This theorem establishes the basic property that $\pi/2$ is positive, which is a fundamental fact used in many trigonometric calculations and proofs. While seemingly elementary, formally establishing the positivity of important constants is critical in a formal system.

The set of three related properties (`PI2_LT`, `PI2_LE`, `PI2_NZ`) are extracted as separate theorems from a single proof using the `CONJUNCTS` function, which is an efficient way to establish multiple related properties at once.

### Dependencies
- `PI_POS`: Theorem establishing that $\pi > 0$
- `REAL_ARITH_TAC`: Tactic for solving real arithmetic goals

### Porting notes
When porting to another proof assistant:
- Ensure that $\pi$ is already defined with its positivity established
- This may be a built-in fact in some systems or may require importing a relevant library
- The conjunction splitting pattern used here (proving multiple related facts at once) should be considered when designing the ported proof

---

## WALLIS_PARTS

### Name of formal statement
WALLIS_PARTS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WALLIS_PARTS = prove
 (`!n. (&n + &2) * integral(&0,pi / &2) (\x. sin(x) pow (n + 2)) =
       (&n + &1) * integral(&0,pi / &2) (\x. sin(x) pow n)`,
  GEN_TAC THEN
  MP_TAC(SPECL [`\x. sin(x) pow (n + 1)`; `\x. --cos(x)`;
                `\x. (&n + &1) * sin(x) pow n * cos(x)`;
                `\x. sin(x)`; `&0`; `pi / &2`] INTEGRAL_BY_PARTS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [SIMP_TAC[REAL_LT_IMP_LE; PI_POS; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    CONV_TAC(ONCE_DEPTH_CONV INTEGRABLE_CONV) THEN REWRITE_TAC[] THEN
    CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THEN DIFF_TAC THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; ADD_SUB] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SIN_PI2; COS_PI2; SIN_0; COS_0] THEN
  REWRITE_TAC[REAL_ARITH `s pow k * s = s * s pow k`] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 real_pow); ARITH_RULE `SUC(n + 1) = n + 2`] THEN
  REWRITE_TAC[GSYM ADD1; real_pow; REAL_MUL_LZERO; REAL_MUL_RZERO;
              REAL_NEG_0; REAL_SUB_LZERO] THEN
  REWRITE_TAC[C MATCH_MP (SPEC_ALL SIN_CIRCLE) (REAL_RING
    `sin(x) pow 2 + cos(x) pow 2 = &1
     ==> (n * sn * cos(x)) * --cos(x) = (n * sn) * (sin(x) pow 2 - &1)`)] THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB; GSYM REAL_MUL_ASSOC; GSYM REAL_POW_ADD] THEN
  REWRITE_TAC[REAL_MUL_RID] THEN
  SUBGOAL_THEN
   `integral(&0,pi / &2)
        (\x. (&n + &1) * sin x pow (n + 2) - (&n + &1) * sin x pow n) =
    (&n + &1) * (integral(&0,pi / &2) (\x. sin(x) pow (n + 2)) -
                 integral(&0,pi / &2) (\x. sin(x) pow n))`
   (fun th -> SUBST1_TAC th THEN REAL_ARITH_TAC) THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `(&n + &1) *
    integral(&0,pi / &2) (\x. sin x pow (n + 2) - sin x pow n)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_CMUL;
    AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_SUB] THEN
  CONV_TAC(ONCE_DEPTH_CONV INTEGRABLE_CONV) THEN SIMP_TAC[PI2_LE]);;
```

### Informal statement
For any natural number $n$, the following equation holds:
$$(n + 2) \cdot \int_{0}^{\pi/2} \sin^{n+2}(x) \, dx = (n + 1) \cdot \int_{0}^{\pi/2} \sin^{n}(x) \, dx$$

This is a key recurrence relation used in the derivation of Wallis' formula for $\pi$.

### Informal proof
The proof uses integration by parts, with carefully chosen functions.

* We apply the integration by parts formula to:
  - $f(x) = \sin^{n+1}(x)$
  - $g(x) = -\cos(x)$
  - $f'(x) = (n+1) \sin^n(x) \cos(x)$
  - $g'(x) = \sin(x)$
  - Over the interval $[0, \pi/2]$

* First, we verify the conditions for the integration by parts formula:
  - $0 \leq \pi/2$ (using properties of $\pi$)
  - Both functions are differentiable on the interval
  - Both products $f'(x)g(x)$ and $f(x)g'(x)$ are integrable

* Applying the integration by parts formula:
  $$\int_{0}^{\pi/2} f(x)g'(x) \,dx = [f(x)g(x)]_{0}^{\pi/2} - \int_{0}^{\pi/2} f'(x)g(x) \,dx$$

* Evaluate at the endpoints using $\sin(\pi/2) = 1$, $\cos(\pi/2) = 0$, $\sin(0) = 0$, $\cos(0) = 1$:
  - $f(\pi/2)g(\pi/2) - f(0)g(0) = \sin^{n+1}(\pi/2)(-\cos(\pi/2)) - \sin^{n+1}(0)(-\cos(0))$
  - $= 1^{n+1} \cdot 0 - 0^{n+1} \cdot (-1) = 0$

* For the integrand $f'(x)g(x)$:
  - $(n+1) \sin^n(x) \cos(x) \cdot (-\cos(x)) = -(n+1) \sin^n(x) \cos^2(x)$

* Using the identity $\sin^2(x) + \cos^2(x) = 1$, we can express $\cos^2(x) = 1 - \sin^2(x)$:
  - $-(n+1) \sin^n(x) \cos^2(x) = -(n+1) \sin^n(x)(1 - \sin^2(x))$
  - $= -(n+1) \sin^n(x) + (n+1) \sin^{n+2}(x)$

* The integration by parts formula becomes:
  $$\int_{0}^{\pi/2} \sin^{n+1}(x) \sin(x) \,dx = 0 - \int_{0}^{\pi/2} (-(n+1) \sin^n(x) + (n+1) \sin^{n+2}(x)) \,dx$$

* This simplifies to:
  $$\int_{0}^{\pi/2} \sin^{n+2}(x) \,dx = \int_{0}^{\pi/2} (n+1) \sin^{n+2}(x) - (n+1) \sin^n(x) \,dx$$

* Using linearity of integration and factoring out the constant $(n+1)$:
  $$(n+1) \int_{0}^{\pi/2} \sin^{n+2}(x) - \sin^n(x) \,dx = (n+1)(\int_{0}^{\pi/2} \sin^{n+2}(x) \,dx - \int_{0}^{\pi/2} \sin^n(x) \,dx)$$

* Rearranging to get the desired result:
  $$(n+2) \int_{0}^{\pi/2} \sin^{n+2}(x) \,dx = (n+1) \int_{0}^{\pi/2} \sin^n(x) \,dx$$

### Mathematical insight
This theorem establishes a recurrence relation for integrals of powers of sine functions over the interval $[0, \pi/2]$. It's a key component in deriving Wallis' formula, which provides a beautiful infinite product representation for $\pi/2$.

The recurrence relation allows us to relate integrals of even and odd powers of sine functions. Starting with the base cases (where $n=0$ or $n=1$), we can use this relation recursively to compute integrals for higher powers of sine, which leads to the well-known Wallis product.

This is a classic example of how integration by parts can be used to derive powerful mathematical results. The specific choice of functions for the integration by parts makes the boundary terms vanish elegantly, resulting in a clean recurrence relation.

### Dependencies
#### Theorems
- `INTEGRAL_BY_PARTS`: Integration by parts formula for definite integrals
- `REAL_MUL_RID`: Multiplication by 1 is the identity (right)
- `REAL_MUL_LZERO`: Multiplication by 0 gives 0 (left)
- `REAL_MUL_RZERO`: Multiplication by 0 gives 0 (right)
- `REAL_LT_IMP_LE`: Less than implies less than or equal
- `REAL_NEG_0`: Negation of 0 is 0
- `REAL_SUB_LDISTRIB`: Left distributivity of multiplication over subtraction
- `REAL_SUB_LZERO`: Subtraction from 0
- `SIN_CIRCLE`: Pythagorean identity $\sin^2(x) + \cos^2(x) = 1$

### Porting notes
When implementing this theorem in other systems:
1. The proof relies heavily on integration by parts and properties of trigonometric functions.
2. Ensure that the target system has a well-developed theory of real analysis with integration capabilities.
3. The original HOL Light proof uses several tactics like `DIFF_TAC` for automating differentiation - you may need to explicitly prove the derivatives in systems with less automation.
4. Pay attention to how power functions for trigonometric functions are handled in your target system.
5. The manipulation of equations using arithmetic properties (`REAL_ARITH`) might need more explicit steps in other systems.

---

## WALLIS_PARTS'

### Name of formal statement
WALLIS_PARTS'

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WALLIS_PARTS' = prove
 (`!n. integral(&0,pi / &2) (\x. sin(x) pow (n + 2)) =
       (&n + &1) / (&n + &2) * integral(&0,pi / &2) (\x. sin(x) pow n)`,
  MP_TAC WALLIS_PARTS THEN MATCH_MP_TAC MONO_FORALL THEN
  CONV_TAC REAL_FIELD);;
```

### Informal statement
For all natural numbers $n$, the following identity holds:
$$\int_0^{\pi/2} \sin^{n+2}(x) \, dx = \frac{n+1}{n+2} \cdot \int_0^{\pi/2} \sin^n(x) \, dx$$

This represents a recursive relationship for integrals of powers of sine over the interval $[0, \pi/2]$.

### Informal proof
The proof relies on the theorem `WALLIS_PARTS`, which is a similar identity. The proof proceeds as follows:

1. Start with the theorem `WALLIS_PARTS`, which likely states a similar relation for integrals of sine powers.
2. Apply this theorem using `MP_TAC WALLIS_PARTS`.
3. Use `MATCH_MP_TAC MONO_FORALL` to preserve the universal quantification.
4. Finally, apply `CONV_TAC REAL_FIELD` to handle the algebraic simplification needed to obtain the desired form of the equation.

The proof is primarily algebraic manipulation starting from another, closely related integral identity.

### Mathematical insight
This theorem provides a recursive relationship for computing integrals of powers of sine. This is a key component in the derivation of Wallis' product formula for $\pi$, which expresses $\pi/2$ as an infinite product of ratios of integers.

The recurrence relation allows successive reduction of the power of sine in the integral, eventually leading to known base cases. This technique is particularly useful for evaluating definite integrals of trigonometric functions with integer powers.

The ratio $(n+1)/(n+2)$ appears naturally due to the integration by parts formula when applied to powers of sine. These recurrence relations were historically important in early analysis and are still fundamental in mathematical teaching and applications.

### Dependencies
- Theorems:
  - `WALLIS_PARTS` - The base theorem that likely establishes a similar integral relation
  - `MONO_FORALL` - A theorem for manipulating universally quantified statements
  - `REAL_FIELD` - A conversion for simplifying real-valued expressions

### Porting notes
When porting this theorem to other systems:
- Ensure that the system has a good library for real analysis, particularly for integration theory
- The proof depends on algebraic manipulation of real expressions, so a system with good automation for real arithmetic would simplify the porting process
- Check if the target system already has theorems about Wallis's product or integrals of trigonometric powers

---

## WALLIS_0

### Name of formal statement
WALLIS_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WALLIS_0 = prove
 (`integral(&0,pi / &2) (\x. sin(x) pow 0) = pi / &2`,
  REWRITE_TAC[real_pow; REAL_DIV_1; REAL_MUL_LID] THEN
  SIMP_TAC[INTEGRAL_CONST; REAL_LT_IMP_LE; PI_POS; REAL_LT_DIV;
           REAL_OF_NUM_LT; ARITH; REAL_MUL_LID; REAL_SUB_RZERO]);;
```

### Informal statement
The theorem states that:
$$\int_0^{\pi/2} \sin(x)^0 \, dx = \frac{\pi}{2}$$

This is the first in a sequence of integrals related to Wallis' formula.

### Informal proof
The proof proceeds as follows:
* First, note that $\sin(x)^0 = 1$ for all $x$ (by the definition of powers), so we are computing $\int_0^{\pi/2} 1 \, dx$.
* The integral is rewritten using `REWRITE_TAC[real_pow; REAL_DIV_1; REAL_MUL_LID]` to recognize that $\sin(x)^0 = 1$.
* Then the theorem `INTEGRAL_CONST` is applied, which states that the integral of a constant function $f(x) = c$ over $[a,b]$ is $c(b-a)$.
* Since the constant in this case is 1, the result is $\frac{\pi}{2} - 0 = \frac{\pi}{2}$.
* The theorem `REAL_SUB_RZERO` is used to simplify $\frac{\pi}{2} - 0$ to $\frac{\pi}{2}$.
* Additional theorems are used to verify the conditions needed for the integral, such as $0 \leq \frac{\pi}{2}$ (derived from $\pi > 0$ and $2 > 0$).

### Mathematical insight
This theorem computes the simplest case in a family of integrals of powers of sine that lead to Wallis' product formula. The result will be used as a base case for computing integrals of higher powers of sine, which follow a recursive pattern. The integral is straightforward since $\sin(x)^0 = 1$, but it establishes the pattern for the sequence of calculations.

### Dependencies
#### Theorems
- `REAL_LT_IMP_LE`: If $x < y$ then $x \leq y$
- `REAL_SUB_RZERO`: For any real number $x$, $x - 0 = x$
- `INTEGRAL_CONST`: (Not listed in dependencies but used) The integral of a constant function
- `PI_POS`: $\pi > 0$
- `REAL_LT_DIV`: Related to division inequalities
- `REAL_MUL_LID`: For any real number $x$, $1 \cdot x = x$

---

## WALLIS_1

### Name of formal statement
WALLIS_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WALLIS_1 = prove
 (`integral(&0,pi / &2) (\x. sin(x) pow 1) = &1`,
  MATCH_MP_TAC DEFINT_INTEGRAL THEN REWRITE_TAC[PI2_LE; REAL_POW_1] THEN
  MP_TAC(SPECL [`\x. --cos(x)`; `\x. sin x`; `&0`; `pi / &2`] FTC1) THEN
  REWRITE_TAC[COS_0; COS_PI2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[PI2_LE] THEN
  REPEAT STRIP_TAC THEN DIFF_TAC THEN REAL_ARITH_TAC);;
```

### Informal statement
The theorem states that:

$$\int_{0}^{\pi/2} \sin(x)^1 \, dx = 1$$

This is a computation of the integral of the sine function over the interval $[0, \pi/2]$.

### Informal proof
The proof involves applying the Fundamental Theorem of Calculus and showing that $\sin(x)$ is the derivative of $-\cos(x)$.

- First, the theorem applies `DEFINT_INTEGRAL` to convert the goal about `integral` to a goal about `defint`.
- Then it rewrites with `PI2_LE` (showing $0 \leq \pi/2$) and `REAL_POW_1` to simplify $\sin(x)^1$ to $\sin(x)$.
- Next, it applies the First Fundamental Theorem of Calculus (`FTC1`) with $f(x) = -\cos(x)$ and $f'(x) = \sin(x)$.
- The antecedent of `FTC1` requires showing:
  * $0 \leq \pi/2$ (handled by rewriting with `PI2_LE`)
  * For all $x$ in $[0, \pi/2]$, the function $f(x) = -\cos(x)$ has derivative $f'(x) = \sin(x)$
- The derivative condition is proven using `DIFF_TAC`, which implements standard differentiation rules.
- Finally, the result follows because $f(\pi/2) - f(0) = -\cos(\pi/2) - (-\cos(0)) = 0 - (-1) = 1$.

### Mathematical insight
This theorem computes a basic trigonometric integral that serves as the starting point for deriving Wallis' formula and related trigonometric integral formulas. The key insight is recognizing that $\sin(x)$ is the derivative of $-\cos(x)$ and applying the Fundamental Theorem of Calculus.

The result is part of a family of integrals used in Wallis' product, which provides an infinite product representation for $\pi/2$. This particular integral (the case where the power of sine is 1) is the simplest case and serves as a building block for more complex calculations.

### Dependencies
- Theorems:
  - `FTC1`: The First Fundamental Theorem of Calculus, stating that if $f'$ is the derivative of $f$ on $[a,b]$, then $\int_a^b f'(x) dx = f(b) - f(a)$
  - `DEFINT_INTEGRAL`: Connects the `defint` primitive (Riemann-style definition of integral) with the `integral` operator

### Porting notes
When porting this theorem:
- Ensure that your system has appropriate definitions for the fundamental trigonometric functions and their derivatives
- Verify that your system's definitions of integrals and the Fundamental Theorem of Calculus align with HOL Light's
- The proof relies on automatic differentiation tactics (`DIFF_TAC`) which may need to be replaced with more explicit steps in systems with less automation for calculus

---

## WALLIS_EVEN

### Name of formal statement
WALLIS_EVEN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WALLIS_EVEN = prove
 (`!n. integral(&0,pi / &2) (\x. sin(x) pow (2 * n)) =
         (&(FACT(2 * n)) / (&2 pow n * &(FACT n)) pow 2) * pi / &2`,
  INDUCT_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[WALLIS_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `2 * SUC n = 2 * n + 2`; WALLIS_PARTS'] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FACT; real_pow; GSYM REAL_OF_NUM_MUL] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(&2 * x) * y * z = (&2 * y) * (x * z)`] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REAL_POW_MUL] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 * n + 2 = SUC(SUC(2 * n))`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_POW_2; FACT;
              GSYM REAL_OF_NUM_MUL] THEN
  CONV_TAC REAL_FIELD);;
```

### Informal statement
For all natural numbers $n$, the integral
$$\int_{0}^{\pi/2} \sin^{2n}(x) \, dx = \frac{(2n)!}{(2^n \cdot n!)^2} \cdot \frac{\pi}{2}$$

This is known as Wallis' formula for even powers of sine.

### Informal proof
The proof proceeds by induction on $n$:

* Base case ($n = 0$):
  - Simplifies to $\int_{0}^{\pi/2} \sin^0(x) \, dx = \frac{\pi}{2}$
  - This is true since $\sin^0(x) = 1$ and the integral of 1 from 0 to $\pi/2$ is $\pi/2$
  - This is verified using `WALLIS_0`

* Induction step:
  - Assume the formula holds for $n$, we need to prove it for $n+1$
  - The goal becomes showing:
    $$\int_{0}^{\pi/2} \sin^{2n+2}(x) \, dx = \frac{(2n+2)!}{(2^{n+1} \cdot (n+1)!)^2} \cdot \frac{\pi}{2}$$
  
  - The proof uses `WALLIS_PARTS'` which relates integrals of consecutive powers
  - Algebraic manipulations:
    - Rewriting $2 \cdot (n+1) = 2n + 2$
    - Decomposing $(2n+2)! = (2n+2)(2n+1)(2n)!$
    - Decomposing $(n+1)! = (n+1) \cdot n!$
    - Handling the powers of 2: $2^{n+1} = 2 \cdot 2^n$
  
  - The proof concludes with algebraic simplifications to show the formula holds for $n+1$

### Mathematical insight
Wallis' formula provides a closed-form solution for the integral of even powers of sine. This is a classical result in calculus that connects trigonometric integrals to combinatorial expressions involving factorials. The formula is important in various areas of mathematics including analysis, number theory, and mathematical physics.

The formula illustrates how the values of these integrals grow smaller as $n$ increases, reflecting the fact that higher powers of sine are increasingly concentrated near $\pi/2$ and approach zero elsewhere in the interval.

This formula is part of a family of results attributed to John Wallis, and it can be used to derive the famous Wallis product for $\pi$.

### Dependencies
- Theorems:
  - `WALLIS_0`: Base case formula for $n=0$
  - `WALLIS_PARTS'`: Recurrence relation for sine power integrals

### Porting notes
When implementing this in other proof assistants, consider:
1. The factorial function may need to be defined or imported from a standard library
2. The treatment of real numbers and powers might differ between systems
3. The recurrence relation in `WALLIS_PARTS'` might need to be established separately

---

## WALLIS_ODD

### WALLIS_ODD
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let WALLIS_ODD = prove
 (`!n. integral(&0,pi / &2) (\x. sin(x) pow (2 * n + 1)) =
         (&2 pow n * &(FACT n)) pow 2 / &(FACT(2 * n + 1))`,
  INDUCT_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[WALLIS_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `2 * SUC n + 1 = (2 * n + 1) + 2`;
                  WALLIS_PARTS'] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  REWRITE_TAC[FACT; real_pow; GSYM REAL_OF_NUM_MUL] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(&2 * x) * y * z = (x * z) * (&2 * y)`] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REAL_POW_MUL] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  REWRITE_TAC[ARITH_RULE `n + 2 = SUC(SUC n)`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_POW_2; FACT;
              GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  MP_TAC(SPEC `2 * n + 1` FACT_LT) THEN REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
  CONV_TAC REAL_FIELD);;
```

### Informal statement
The theorem states that for all natural numbers $n$:

$$\int_0^{\pi/2} \sin^{2n+1}(x) \, dx = \frac{(2^n \cdot n!)^2}{(2n+1)!}$$

This gives a closed-form expression for the integral of odd powers of sine over the interval $[0, \pi/2]$.

### Informal proof
The proof proceeds by induction on $n$.

**Base case ($n = 0$):**
- When $n = 0$, we need to show $\int_0^{\pi/2} \sin^1(x) \, dx = \frac{(2^0 \cdot 0!)^2}{(2 \cdot 0 + 1)!} = \frac{1}{1} = 1$
- This is calculated directly using `WALLIS_1` (which gives the value of $\int_0^{\pi/2} \sin(x) \, dx$)

**Inductive case:**
- Assume the result holds for some $n$
- For $n+1$, we need to show the integral of $\sin^{2(n+1)+1}(x) = \sin^{2n+3}(x)$
- Rewrite $2(n+1)+1$ as $(2n+1)+2$ using arithmetic rules
- Apply the reduction formula `WALLIS_PARTS'` which relates integrals of $\sin^{m+2}(x)$ to integrals of $\sin^m(x)$
- Manipulate the expression algebraically through several steps:
  * Handle factorial terms: $\text{FACT}(n+1) = (n+1) \cdot \text{FACT}(n)$
  * Manage powers of 2: $2^{n+1} = 2 \cdot 2^n$
  * Simplify expressions involving factorials and powers
- Use properties of real number arithmetic and power operations
- Complete the proof with real field calculations and properties of factorials

### Mathematical insight
This theorem is part of the classic "Wallis product" results. It provides a closed-form expression for integrals of odd powers of sine, which is useful in many calculus and analysis applications.

The formula shows how these integrals relate to factorials and powers of 2, revealing a beautiful pattern in these definite integrals. This result complements `WALLIS_EVEN`, which handles even powers of sine.

The proof strategy demonstrates the power of induction combined with reduction formulas for handling sequences of integrals with increasing powers.

### Dependencies
- `WALLIS_1`: Gives the value of $\int_0^{\pi/2} \sin(x) \, dx$
- `WALLIS_PARTS'`: A reduction formula relating integrals of different powers of sine
- `FACT_LT`: A theorem about the factorials being positive
- Various arithmetic and real number manipulation theorems

### Porting notes
When implementing this in another system:
- Ensure that the factorial function and its properties are defined
- The reduction formula for sine powers is crucial and should be ported first
- The proof relies heavily on real arithmetic simplifications, which might require different tactics in other systems
- Special attention should be given to how powers of trigonometric functions are represented

---

## WALLIS_QUOTIENT

### WALLIS_QUOTIENT
- `WALLIS_QUOTIENT`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let WALLIS_QUOTIENT = prove
 (`!n. integral(&0,pi / &2) (\x. sin(x) pow (2 * n)) /
       integral(&0,pi / &2) (\x. sin(x) pow (2 * n + 1)) =
        (&(FACT(2 * n)) * &(FACT(2 * n + 1))) / (&2 pow n * &(FACT n)) pow 4 *
        pi / &2`,
  GEN_TAC THEN REWRITE_TAC[WALLIS_EVEN; WALLIS_ODD] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; GSYM REAL_POW_INV; REAL_INV_INV] THEN
  REAL_ARITH_TAC);;
```

### Informal statement
For all non-negative integers $n$, the ratio of two integrals:
$$\frac{\int_{0}^{\pi/2} \sin^{2n}(x) \, dx}{\int_{0}^{\pi/2} \sin^{2n+1}(x) \, dx} = \frac{(2n)! \cdot (2n+1)!}{\left(2^n \cdot n!\right)^4} \cdot \frac{\pi}{2}$$

### Informal proof
The proof uses previously established results `WALLIS_EVEN` and `WALLIS_ODD` which give the exact values of the integrals in the numerator and denominator:

1. Apply the definitions of `WALLIS_EVEN` and `WALLIS_ODD` for the integrals in the numerator and denominator.
2. Rewrite division as multiplication by inverse: $\frac{a}{b} = a \cdot \frac{1}{b}$.
3. Use the property that $\frac{1}{a \cdot b} = \frac{1}{a} \cdot \frac{1}{b}$.
4. Apply the property that $\frac{1}{a^n} = (1/a)^n$.
5. Use the property that $\frac{1}{\frac{1}{a}} = a$.
6. Finally, use real arithmetic to simplify and obtain the result.

### Mathematical insight
This theorem gives a closed-form expression for the ratio of integrals of even and odd powers of sine functions. It's a key component of Wallis' product formula, which provides a way to express π as an infinite product. The quotient shows how these specific integrals relate to factorials and powers of 2, offering insight into the behavior of trigonometric integrals.

Wallis' product is historically significant in the study of π and appears in various areas of analysis. This particular ratio is used in deriving the asymptotic behavior of the Wallis product as n grows large.

### Dependencies
- Theorems:
  - `WALLIS_EVEN` - Gives the closed form of $\int_{0}^{\pi/2} \sin^{2n}(x) \, dx$
  - `WALLIS_ODD` - Gives the closed form of $\int_{0}^{\pi/2} \sin^{2n+1}(x) \, dx$
  - Various real arithmetic properties used by `REAL_ARITH_TAC`

### Porting notes
When porting this theorem:
1. Ensure that the prerequisite theorems `WALLIS_EVEN` and `WALLIS_ODD` are ported first.
2. The proof relies on real arithmetic simplifications that might require different tactics in other proof assistants.
3. The factorial notation and handling of real conversions (like `&2` for natural to real conversion) might differ in other systems.

---

## WALLIS_QUOTIENT'

### Name of formal statement
WALLIS_QUOTIENT'

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WALLIS_QUOTIENT' = prove
 (`!n. integral(&0,pi / &2) (\x. sin(x) pow (2 * n)) /
       integral(&0,pi / &2) (\x. sin(x) pow (2 * n + 1)) * &2 / pi =
         (&(FACT(2 * n)) * &(FACT(2 * n + 1))) / (&2 pow n * &(FACT n)) pow 4`,
  GEN_TAC THEN REWRITE_TAC[WALLIS_QUOTIENT] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [GSYM REAL_INV_DIV] THEN
  REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
  MP_TAC PI2_NZ THEN CONV_TAC REAL_FIELD);;
```

### Informal statement
For all natural numbers $n$, the following equation holds:

$$\frac{\int_0^{\pi/2} \sin^{2n}(x) \, dx}{\int_0^{\pi/2} \sin^{2n+1}(x) \, dx} \cdot \frac{2}{\pi} = \frac{\text{FACT}(2n) \cdot \text{FACT}(2n+1)}{(2^n \cdot \text{FACT}(n))^4}$$

where FACT represents the factorial function.

### Informal proof
The proof relies on the theorem `WALLIS_QUOTIENT`, which provides a formula for the ratio of integrals involving powers of sine.

1. Start with the goal for arbitrary $n$.
2. Apply `WALLIS_QUOTIENT` to rewrite the left side of the equation.
3. For the expression on the left, convert $\frac{1}{\frac{a}{b}}$ to $\frac{b}{a}$ using `GSYM REAL_INV_DIV`.
4. Simplify the expression using properties of division represented by `GSYM real_div`.
5. Apply `REAL_DIV_RMUL` to handle the division by $\frac{\pi}{2}$.
6. Use `PI2_NZ` (which states that $\frac{\pi}{2} \neq 0$) to ensure division is well-defined.
7. Complete the proof using field arithmetic to simplify the resulting expressions.

### Mathematical insight
This theorem expresses a variant of Wallis' formula, relating integrals of powers of sine functions to factorial expressions. The result is significant in analysis and is related to Wallis' product formula for $\pi$.

The theorem provides an explicit formula for the ratio of these specific integrals, which is useful in various applications in mathematical analysis, particularly in evaluating definite integrals involving trigonometric functions.

The connection between trigonometric integrals and factorial expressions is a classic result that bridges analysis and combinatorics.

### Dependencies
- Theorems:
  - `WALLIS_QUOTIENT`: Provides the fundamental relation between the integrals of sine powers and factorial expressions
  - `REAL_INV_DIV`: Relates inverse of division to division in reverse order
  - `REAL_DIV_RMUL`: Result about multiplying both sides of a division by the same term
  - `PI2_NZ`: States that $\frac{\pi}{2} \neq 0$

### Porting notes
When porting this theorem to other proof assistants:
- Ensure the target system has a definition of definite integrals of trigonometric functions
- Verify that factorial functions are defined and have similar properties
- Check that the system has appropriate lemmas about real division and multiplication
- The theorem is essentially algebraic manipulation of another result (`WALLIS_QUOTIENT`), so having that result available is crucial

---

## WALLIS_MONO

### Name of formal statement
WALLIS_MONO

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WALLIS_MONO = prove
 (`!m n. m <= n
         ==> integral(&0,pi / &2) (\x. sin(x) pow n)
                <= integral(&0,pi / &2) (\x. sin(x) pow m)`,
  REWRITE_TAC[LE_EXISTS] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_LE THEN
  CONV_TAC(ONCE_DEPTH_CONV INTEGRABLE_CONV) THEN REWRITE_TAC[PI2_LE] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_POW_ADD] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE; MATCH_MP_TAC REAL_POW_1_LE] THEN
  REWRITE_TAC[SIN_BOUNDS] THEN
  (MP_TAC(SPEC `x:real` SIN_POS_PI_LE) THEN
   ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
   REPEAT(POP_ASSUM MP_TAC) THEN MP_TAC PI2_LT THEN REAL_ARITH_TAC));;
```

### Informal statement
For any natural numbers $m$ and $n$ such that $m \leq n$, we have:
$$\int_{0}^{\pi/2} \sin(x)^n \, dx \leq \int_{0}^{\pi/2} \sin(x)^m \, dx$$

This theorem states that the integral of $\sin(x)$ raised to the power $n$ over the interval $[0, \pi/2]$ decreases as $n$ increases.

### Informal proof
We approach this proof by showing that when $m \leq n$, the integrand $\sin(x)^n$ is pointwise less than or equal to $\sin(x)^m$ over the integration interval.

* First, we rewrite $m \leq n$ as $n = m + d$ for some $d \geq 0$ using the `LE_EXISTS` theorem.
* We apply `INTEGRAL_LE` which states that if $f(x) \leq g(x)$ for all $x$ in $[a,b]$, then $\int_a^b f(x) \, dx \leq \int_a^b g(x) \, dx$.
* We verify that both functions are integrable using `INTEGRABLE_CONV`.
* We confirm that $0 \leq \pi/2$ using the theorem `PI2_LE`.
* For all $x$ in $[0, \pi/2]$, we need to show $\sin(x)^n \leq \sin(x)^m$.

Since $n = m + d$, we can rewrite:
$$\sin(x)^n = \sin(x)^{m+d} = \sin(x)^m \cdot \sin(x)^d$$

To show $\sin(x)^n \leq \sin(x)^m$, it's equivalent to showing:
$$\sin(x)^m \cdot \sin(x)^d \leq \sin(x)^m \cdot 1$$

This requires proving:
1. $\sin(x)^m \geq 0$ (for multiplication by a non-negative number preserves inequality)
2. $\sin(x)^d \leq 1$ (the actual inequality we need)

For (1), we use `REAL_POW_LE` and the fact that $\sin(x) \geq 0$ for $x \in [0, \pi/2]$ (from `SIN_BOUNDS`).
For (2), we apply `REAL_POW_1_LE`, noting that $0 \leq \sin(x) \leq 1$ for $x \in [0, \pi/2]$ (also from `SIN_BOUNDS`).

We verify that $\sin(x) > 0$ for $x \in (0, \pi]$ using `SIN_POS_PI_LE`, and complete the proof using real arithmetic.

### Mathematical insight
This theorem is a key component in deriving Wallis' product formula, which provides an infinite product representation for $\pi/2$. The monotonicity of these integrals with respect to the exponent is a fundamental property that helps establish the convergence behavior in Wallis' formula.

The result is intuitive when considering the behavior of $\sin(x)$ on $[0, \pi/2]$: since $0 \leq \sin(x) \leq 1$ in this interval, raising it to a higher power makes it smaller at each point, resulting in a smaller integral.

This theorem is part of a broader family of results about these integrals, which are sometimes called the Wallis integrals, and they play an important role in analysis and the derivation of important mathematical constants.

### Dependencies
#### Theorems
- `REAL_MUL_RID`: For any real number $x$, $x \cdot 1 = x$
- `INTEGRAL_LE`: If $a \leq b$, $f$ and $g$ are integrable on $[a,b]$, and $f(x) \leq g(x)$ for all $x \in [a,b]$, then $\int_a^b f(x) \, dx \leq \int_a^b g(x) \, dx$
- `LE_EXISTS`: For integers $m$ and $n$, $m \leq n$ if and only if there exists a $d$ such that $n = m + d$
- `INTEGRABLE_CONV`: Conversion tactic for proving integrability
- `PI2_LE`: $0 \leq \pi/2$
- `REAL_POW_ADD`: $x^{m+n} = x^m \cdot x^n$
- `REAL_LE_LMUL`: If $0 \leq a$ and $b \leq c$, then $a \cdot b \leq a \cdot c$
- `REAL_POW_LE`: If $0 \leq x \leq y$, then $x^n \leq y^n$ for any natural number $n$
- `REAL_POW_1_LE`: If $0 \leq x \leq 1$, then $x^n \leq 1$ for any natural number $n$
- `SIN_BOUNDS`: For $x \in [0, \pi/2]$, $0 \leq \sin(x) \leq 1$
- `SIN_POS_PI_LE`: For $x \in (0, \pi]$, $\sin(x) > 0$
- `PI2_LT`: $0 < \pi/2$

### Porting notes
When porting this theorem:
1. Ensure that the trigonometric functions and their properties (like the bounds of sine in $[0, \pi/2]$) are properly defined in your target system.
2. Pay attention to how integrability is handled - some systems might have different default assumptions or require explicit statements about the integrability of these functions.
3. The use of conversion tactics like `INTEGRABLE_CONV` might need to be replaced with direct proofs or different automation approaches in other systems.
4. The handling of real arithmetic at the end of the proof might be automated differently in another system.

---

## WALLIS_LT

### Name of formal statement
WALLIS_LT

### Type of formal statement
theorem

### Formal Content
```ocaml
let WALLIS_LT = prove
 (`!n. &0 < integral(&0,pi / &2) (\x. sin(x) pow n)`,
  MATCH_MP_TAC ODDEVEN_INDUCT THEN
  REWRITE_TAC[WALLIS_0; WALLIS_1; PI2_LT; REAL_OF_NUM_LT; ARITH] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[WALLIS_PARTS'] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN REAL_ARITH_TAC);;
```

### Informal statement
For all natural numbers $n$, the integral
$$\int_0^{\pi/2} \sin^n(x) \, dx > 0$$

### Informal proof
The proof proceeds by induction on $n$, considering even and odd cases separately:

* **Base cases**: 
  - For $n = 0$, we use `WALLIS_0` which gives $\int_0^{\pi/2} \sin^0(x) \, dx = \int_0^{\pi/2} 1 \, dx = \pi/2 > 0$
  - For $n = 1$, we use `WALLIS_1` which gives $\int_0^{\pi/2} \sin^1(x) \, dx = 1 > 0$
  
* **Inductive steps**:
  - For even $n$, we assume the result holds for $n$ and prove it for $n+2$
  - For odd $n$, we assume the result holds for $n$ and prove it for $n+2$
  
  In both cases, we use the recursive formula `WALLIS_PARTS'` that relates $\int_0^{\pi/2} \sin^{n+2}(x) \, dx$ to $\int_0^{\pi/2} \sin^n(x) \, dx$:
  
  For $n > 0$: $\int_0^{\pi/2} \sin^{n+2}(x) \, dx = \frac{n+1}{n+2} \cdot \int_0^{\pi/2} \sin^n(x) \, dx$
  
  Since $\frac{n+1}{n+2} > 0$ and by the inductive hypothesis $\int_0^{\pi/2} \sin^n(x) \, dx > 0$, we can conclude that $\int_0^{\pi/2} \sin^{n+2}(x) \, dx > 0$ using properties of multiplication of positive numbers.

### Mathematical insight
This theorem establishes the positivity of the Wallis integrals, which are important in analyzing the convergence of the Wallis product formula for $\pi/2$. These integrals appear in various contexts in analysis and are related to the beta function. The positivity is intuitive for odd powers since sine is positive in $(0,\pi/2)$, but for even powers the sine function takes on both positive and negative values elsewhere, so the restriction to the interval $[0,\pi/2]$ is crucial.

### Dependencies
- `WALLIS_0` - Base case for the integral when $n=0$
- `WALLIS_1` - Base case for the integral when $n=1$
- `WALLIS_PARTS'` - Recursive formula relating integrals of consecutive even/odd powers
- `PI2_LT` - Inequality about $\pi/2$
- `ODDEVEN_INDUCT` - Induction principle considering even and odd cases separately
- `REAL_LT_MUL` - Property of multiplication preserving strict inequality for positive numbers
- `REAL_LT_DIV` - Property of division preserving strict inequality for positive numbers

### Porting notes
When porting this theorem:
- Ensure the recursive relation in `WALLIS_PARTS'` is properly established first
- The induction principle `ODDEVEN_INDUCT` may need to be implemented if not available
- The proof relies on basic properties of real arithmetic which should be widely available

---

## WALLIS_NZ

### WALLIS_NZ
- `WALLIS_NZ`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let WALLIS_NZ = prove
 (`!n. ~(integral(&0,pi / &2) (\x. sin(x) pow n) = &0)`,
  MP_TAC WALLIS_LT THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC);;
```

### Informal statement
For all natural numbers $n$, the integral $\int_{0}^{\pi/2} \sin^n(x) \, dx$ is non-zero:

$$\forall n. \int_{0}^{\pi/2} \sin^n(x) \, dx \neq 0$$

### Informal proof
The proof uses `WALLIS_LT`, which likely states that the integral is strictly positive, and then applies basic logical reasoning:

1. Apply the theorem `WALLIS_LT` which states that the integral is positive.
2. Use `MONO_FORALL` to pass the universal quantifier through the implication.
3. Apply real arithmetic reasoning (`REAL_ARITH_TAC`) to conclude that a positive number is non-zero.

The proof essentially follows from the fact that if $\int_{0}^{\pi/2} \sin^n(x) \, dx > 0$, then clearly $\int_{0}^{\pi/2} \sin^n(x) \, dx \neq 0$.

### Mathematical insight
This theorem establishes the non-vanishing property of the Wallis integrals. These integrals are important in analysis and probability theory. The Wallis integrals are defined as:

$$I_n = \int_{0}^{\pi/2} \sin^n(x) \, dx$$

The non-vanishing property is essential when these integrals appear in denominators of expressions. Wallis integrals also connect to the Gamma function and appear in the famous Wallis product formula for $\pi$.

The positivity of these integrals is intuitive since $\sin(x)$ is positive in the interval $(0,\pi/2)$, and raising a positive number to any power preserves positivity.

### Dependencies
- `WALLIS_LT` - Likely states that the Wallis integral is positive
- `MONO_FORALL` - A theorem about monotonicity with universal quantifiers
- `REAL_ARITH_TAC` - A tactic for real number arithmetic reasoning

### Porting notes
When porting this theorem:
- Ensure that the integral is properly defined in the target system
- Verify that the target system has a suitable library for real analysis
- The proof should be straightforward if the positivity of the integral (`WALLIS_LT`) is already established

---

## WALLIS_BOUNDS

### Name of formal statement
WALLIS_BOUNDS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WALLIS_BOUNDS = prove
 (`!n. integral(&0,pi / &2) (\x. sin(x) pow (n + 1))
        <= integral(&0,pi / &2) (\x. sin(x) pow n) /\
       integral(&0,pi / &2) (\x. sin(x) pow n) <=
        (&n + &2) / (&n + &1) * integral(&0,pi / &2) (\x. sin(x) pow (n + 1))`,
  GEN_TAC THEN SIMP_TAC[WALLIS_MONO; LE_ADD] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&n + &2) / (&n + &1) *
              integral (&0,pi / &2) (\x. sin x pow (n + 2))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[WALLIS_PARTS'] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  SIMP_TAC[WALLIS_MONO; ARITH_RULE `n + 1 <= n + 2`] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN REAL_ARITH_TAC);;
```

### Informal statement
For any natural number $n$, the following inequalities hold:
$$\int_{0}^{\pi/2} \sin(x)^{n+1} \, dx \leq \int_{0}^{\pi/2} \sin(x)^{n} \, dx \leq \frac{n+2}{n+1} \cdot \int_{0}^{\pi/2} \sin(x)^{n+1} \, dx$$

### Informal proof
This theorem establishes bounds for the ratio of sequential terms in Wallis's integrals.

- First, we apply `WALLIS_MONO` to establish that $\int_{0}^{\pi/2} \sin(x)^{n+1} \, dx \leq \int_{0}^{\pi/2} \sin(x)^{n} \, dx$ since $n \leq n+1$.

- For the second inequality, we use transitivity of $\leq$ (`REAL_LE_TRANS`) with the intermediate term:
  $$\frac{n+2}{n+1} \cdot \int_{0}^{\pi/2} \sin(x)^{n+2} \, dx$$

- To show that $\int_{0}^{\pi/2} \sin(x)^{n} \, dx \leq \frac{n+2}{n+1} \cdot \int_{0}^{\pi/2} \sin(x)^{n+2} \, dx$, we apply `WALLIS_PARTS'` which gives us:
  $$\int_{0}^{\pi/2} \sin(x)^{n} \, dx = \frac{n+2}{n+1} \cdot \int_{0}^{\pi/2} \sin(x)^{n+2} \, dx$$
  This equality immediately implies the inequality.

- For the final inequality, we show:
  $$\frac{n+2}{n+1} \cdot \int_{0}^{\pi/2} \sin(x)^{n+2} \, dx \leq \frac{n+2}{n+1} \cdot \int_{0}^{\pi/2} \sin(x)^{n+1} \, dx$$
  
  This follows from:
  - $\int_{0}^{\pi/2} \sin(x)^{n+2} \, dx \leq \int_{0}^{\pi/2} \sin(x)^{n+1} \, dx$ (by `WALLIS_MONO` since $n+1 \leq n+2$)
  - $\frac{n+2}{n+1} > 0$ (by arithmetic reasoning)
  
  Multiplication by a positive factor preserves the inequality.

### Mathematical insight
This theorem provides important bounds for the famous Wallis product formula. These inequalities are crucial for analyzing the convergence and behavior of the sequence of integrals $\int_{0}^{\pi/2} \sin(x)^{n} \, dx$ as $n$ increases. The upper bound shows that each term is at most $\frac{n+2}{n+1}$ times the next term, which is key to establishing the asymptotic behavior of Wallis's product.

These bounds enable the derivation of the classical Wallis product formula for $\pi/2$, showing that:
$$\frac{\pi}{2} = \lim_{n \to \infty} \frac{2^{2n}(n!)^2}{(2n)!(2n+1)} = \prod_{n=1}^{\infty} \frac{2n}{2n-1} \cdot \frac{2n}{2n+1}$$

### Dependencies
- **Theorems**:
  - `REAL_LE_TRANS`: Transitivity of the less-than-or-equal relation for real numbers
  - `WALLIS_MONO`: Monotonicity property of the Wallis integrals
  - `WALLIS_PARTS'`: Integration by parts formula for the Wallis integrals

### Porting notes
When porting this theorem, ensure that the dependencies for integration, trigonometric functions, and real number properties are available. Special attention should be paid to:
1. The handling of real division and multiplication
2. The integration by parts formula for trigonometric functions
3. The appropriate automation for arithmetic reasoning

---

## WALLIS_RATIO_BOUNDS

### WALLIS_RATIO_BOUNDS

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let WALLIS_RATIO_BOUNDS = prove
 (`!n. &1 <= integral(&0,pi / &2) (\x. sin(x) pow n) /
            integral(&0,pi / &2) (\x. sin(x) pow (n + 1)) /\
      integral(&0,pi / &2) (\x. sin(x) pow n) /
      integral(&0,pi / &2) (\x. sin(x) pow (n + 1)) <= (&n + &2) / (&n + &1)`,
  GEN_TAC THEN CONJ_TAC THENL
   [SIMP_TAC[REAL_LE_RDIV_EQ; WALLIS_LT; REAL_MUL_LID; WALLIS_BOUNDS];
    SIMP_TAC[REAL_LE_LDIV_EQ; WALLIS_LT; WALLIS_BOUNDS]]);;
```

### Informal statement
For all natural numbers $n$, the following bounds hold for the ratio of Wallis integrals:

$$1 \leq \frac{\int_{0}^{\pi/2} \sin^n(x) \, dx}{\int_{0}^{\pi/2} \sin^{n+1}(x) \, dx} \leq \frac{n+2}{n+1}$$

### Informal proof
The proof establishes the lower and upper bounds separately:

- For the lower bound ($1 \leq \frac{\int_{0}^{\pi/2} \sin^n(x) \, dx}{\int_{0}^{\pi/2} \sin^{n+1}(x) \, dx}$):
  - We use `REAL_LE_RDIV_EQ` to rewrite the inequality in the form $\int_{0}^{\pi/2} \sin^{n+1}(x) \, dx \leq \int_{0}^{\pi/2} \sin^n(x) \, dx$
  - `WALLIS_LT` ensures that the denominator is positive
  - `WALLIS_BOUNDS` provides the required inequality

- For the upper bound ($\frac{\int_{0}^{\pi/2} \sin^n(x) \, dx}{\int_{0}^{\pi/2} \sin^{n+1}(x) \, dx} \leq \frac{n+2}{n+1}$):
  - We use `REAL_LE_LDIV_EQ` to rewrite the inequality
  - Again, `WALLIS_LT` ensures the denominator is positive
  - `WALLIS_BOUNDS` provides the required inequality for the rewritten form

### Mathematical insight
This theorem establishes bounds for the ratio of consecutive Wallis integrals, which are integrals of powers of sine functions over $[0, \pi/2]$. These bounds are important in the study of the Wallis product for $\pi$.

The ratio $\frac{\int_{0}^{\pi/2} \sin^n(x) \, dx}{\int_{0}^{\pi/2} \sin^{n+1}(x) \, dx}$ converges to 1 as $n$ approaches infinity, and these bounds quantify the rate of convergence, showing that the ratio is always at least 1 and at most $\frac{n+2}{n+1}$.

These bounds are crucial in establishing the famous Wallis product formula for $\pi$:

$$\frac{\pi}{2} = \prod_{n=1}^{\infty} \frac{2n \cdot 2n}{(2n-1)(2n+1)}$$

### Dependencies
- `REAL_LE_RDIV_EQ` - Theorem for rewriting inequalities involving division
- `REAL_LE_LDIV_EQ` - Theorem for rewriting inequalities involving division
- `WALLIS_LT` - Theorem establishing positivity of Wallis integrals
- `WALLIS_BOUNDS` - Theorem providing bounds for Wallis integrals
- `REAL_MUL_LID` - Theorem about multiplication by 1 (identity)

### Porting notes
When porting this theorem, ensure that the target system has:
- Support for definite integrals
- Theorems about the sin function and its powers
- Adequate support for manipulating real-valued inequalities

The proof is relatively straightforward once the supporting theorems are in place, primarily requiring inequality manipulation.

---

## WALLIS

### WALLIS
- `WALLIS`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let WALLIS = prove
 (`(\n. (&2 pow n * &(FACT n)) pow 4 / (&(FACT(2 * n)) * &(FACT(2 * n + 1))))
   --> pi / &2`,
  ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN MATCH_MP_TAC SEQ_INV THEN
  CONJ_TAC THENL [ALL_TAC; MP_TAC PI2_NZ THEN CONV_TAC REAL_FIELD] THEN
  REWRITE_TAC[GSYM WALLIS_QUOTIENT'] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC SEQ_MUL THEN REWRITE_TAC[SEQ_CONST] THEN
  GEN_REWRITE_TAC (LAND_CONV o ABS_CONV) [REAL_ARITH `x = (x - &1) + &1`] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_ADD_LID] THEN
  MATCH_MP_TAC SEQ_ADD THEN REWRITE_TAC[SEQ_CONST] THEN
  MATCH_MP_TAC SEQ_LE_0 THEN EXISTS_TAC `\n. &1 / &n` THEN
  REWRITE_TAC[SEQ_HARMONIC] THEN EXISTS_TAC `1` THEN
  REWRITE_TAC[GE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `!d. &1 <= x /\ x <= d /\ d - &1 <= e ==> abs(x - &1) <= e`) THEN
  EXISTS_TAC `(&(2 * n) + &2) / (&(2 * n) + &1)` THEN
  REWRITE_TAC[WALLIS_RATIO_BOUNDS] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[REAL_FIELD
   `(&2 * &n + &2) / (&2 * &n + &1) - &1 = &1 / (&2 * &n + &1)`] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; REAL_ABS_INV; REAL_ABS_NUM] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC);;
```

### Informal statement
The theorem states that the sequence
$$\left(\frac{(2^n \cdot n!)^4}{(2n)! \cdot (2n+1)!}\right)_{n=1}^{\infty}$$
converges to $\frac{\pi}{2}$, where $\pi$ is the mathematical constant representing the ratio of a circle's circumference to its diameter.

### Informal proof
The proof follows these key steps:

- First, the goal is rewritten using `GSYM REAL_INV_DIV` to work with the inverse of the sequence, establishing that we need to show 
  $\left(\frac{(2n)! \cdot (2n+1)!}{(2^n \cdot n!)^4}\right) \to \frac{2}{\pi}$.

- We apply `SEQ_INV` (a theorem about limits of inverses of sequences), which requires proving:
  1. The inverse sequence converges to $\frac{2}{\pi}$
  2. $\frac{\pi}{2} \neq 0$ (handled by `PI2_NZ`)

- The proof uses `WALLIS_QUOTIENT'` (not shown in dependencies but presumably a variation of the Wallis product formula) to rewrite the goal.

- The sequence is decomposed into a product of sequences using `SEQ_MUL`:
  * A constant sequence $(\cdot 1)$
  * A sequence that approaches 1

- We further decompose the sequence approaching 1 as $(x_n - 1) + 1$ and apply `SEQ_ADD`.

- To show the sequence $(x_n - 1)$ converges to 0, we use `SEQ_LE_0` and `SEQ_HARMONIC`, establishing that $|x_n - 1| \leq \frac{1}{n}$ for $n \geq 1$.

- The bounds for the Wallis ratio are applied via `WALLIS_RATIO_BOUNDS`.

- Finally, algebraic manipulations show that the difference between the ratio and 1 is bounded by $\frac{1}{2n+1}$, which is less than or equal to $\frac{1}{n}$ for $n \geq 1$.

### Mathematical insight
This theorem proves a well-known result in mathematical analysis about the Wallis product formula, which provides a way to express $\pi$ as an infinite product. The sequence in question is related to the Wallis product, which states:

$$\frac{\pi}{2} = \prod_{n=1}^{\infty} \frac{4n^2}{4n^2-1} = \prod_{n=1}^{\infty} \frac{2n}{2n-1} \cdot \frac{2n}{2n+1}$$

The theorem proves a specific formulation of how partial products of this sequence converge to $\frac{\pi}{2}$. This is a classical result in the theory of infinite products and provides an interesting connection between factorial expressions and the constant $\pi$.

The Wallis product is historically significant as one of the earliest representations of $\pi$ as an infinite product, discovered by John Wallis in the 17th century.

### Dependencies
- **Theorems for sequences and limits**:
  - `SEQ_CONST`: A constant sequence converges to that constant
  - `SEQ_ADD`: The sum of two convergent sequences converges to the sum of their limits
  - `SEQ_MUL`: The product of two convergent sequences converges to the product of their limits
  - `SEQ_INV`: The sequence of reciprocals converges to the reciprocal of the limit
  - `SEQ_LE_0`: If sequence f approaches 0 and eventually |g| ≤ |f|, then g approaches 0
  - `SEQ_HARMONIC`: The harmonic sequence 1/n converges to 0 (not in provided dependencies but referenced)
  
- **Theorems about real numbers**:
  - `REAL_MUL_RID`: Multiplication by 1 on the right is identity operation
  
- **Other dependencies** (implied but not explicitly listed):
  - `WALLIS_QUOTIENT'`: A variation of the Wallis product formula
  - `WALLIS_RATIO_BOUNDS`: Provides bounds for the Wallis ratio
  - `PI2_NZ`: States that π/2 is non-zero

### Porting notes
When porting this theorem:
1. Ensure the target system has properly defined the Wallis product formula and related theorems.
2. The proof relies on algebraic manipulations of sequences and their limits, which should be available in most proof assistants.
3. Special attention should be paid to how π is defined in the target system.
4. The proof uses several auxiliary results (like `WALLIS_QUOTIENT'` and `WALLIS_RATIO_BOUNDS`) that may need to be established first.
5. The proof structure relies on decomposing the sequence into simpler parts and showing convergence of each part, which is a standard approach that should translate well to other systems.

---

## LN_WALLIS

### Name of formal statement
LN_WALLIS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LN_WALLIS = prove
 (`(\n. &4 * &n * ln(&2) + &4 * ln(&(FACT n)) -
        (ln(&(FACT(2 * n))) + ln(&(FACT(2 * n + 1))))) --> ln(pi / &2)`,
  REWRITE_TAC[REAL_ARITH `&4 * x + &4 * y - z = &4 * (x + y) - z`] THEN
  SUBGOAL_THEN `!n. &0 < &2 pow n`
   (fun th -> SIMP_TAC[th; GSYM LN_POW; REAL_OF_NUM_LT; ARITH; GSYM LN_MUL;
                       FACT_LT; REAL_POW_LT; REAL_LT_MUL; GSYM LN_DIV]) THEN
  SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC CONTL_SEQ THEN REWRITE_TAC[WALLIS] THEN
  MATCH_MP_TAC DIFF_CONT THEN EXISTS_TAC `inv(pi / &2)` THEN
  MP_TAC(SPEC `pi / &2` (DIFF_CONV `\x. ln(x)`)) THEN
  SIMP_TAC[ETA_AX; PI2_LT; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[REAL_MUL_RID]);;
```

### Informal statement
The sequence $\{a_n\}_{n=1}^{\infty}$ defined by
$$a_n = 4n\ln(2) + 4\ln(n!) - \ln((2n)!) - \ln((2n+1)!)$$
converges to $\ln(\pi/2)$ as $n$ approaches infinity. Formally:
$$\lim_{n \to \infty} \left(4n\ln(2) + 4\ln(n!) - \ln((2n)!) - \ln((2n+1)!)\right) = \ln(\pi/2)$$

### Informal proof
The proof proceeds as follows:

- First, we simplify the expression using arithmetic, specifically rewriting
  $4x + 4y - z = 4(x + y) - z$.

- For every $n$, we establish that $2^n > 0$, which is needed to apply logarithm properties.

- We apply several logarithm identities, including:
  * $\ln(x^n) = n\ln(x)$
  * $\ln(x \cdot y) = \ln(x) + \ln(y)$
  * $\ln(x/y) = \ln(x) - \ln(y)$
  along with facts about factorial positivity.

- We use `CONTL_SEQ` theorem to transform the limit into a continuity statement.
  This theorem states that if $f$ is continuous at $l$ and $x_n \to l$, then
  $f(x_n) \to f(l)$.

- We invoke the Wallis product formula (`WALLIS` theorem), which gives us the
  limit behavior of the relevant sequence.

- We use `DIFF_CONT` to establish that the logarithm function is continuous,
  since differentiability implies continuity.

- We compute the derivative of $\ln(x)$ at $\pi/2$ using `DIFF_CONV`.

- Finally, we complete the proof using properties of $\pi$ and arithmetic 
  simplifications.

### Mathematical insight
This theorem provides a connection between the Wallis product formula and the logarithm of $\pi/2$. The Wallis product is a remarkable infinite product formula expressing $\pi/2$ as:

$$\frac{\pi}{2} = \lim_{n \to \infty} \frac{2^{4n} (n!)^4}{(2n)!(2n+1)!}$$

Taking the logarithm of both sides of this formula and rearranging terms yields the statement of this theorem. This result is significant in number theory and analysis as it provides another way to understand and compute approximations to $\pi$.

### Dependencies
- **Theorems**:
  - `REAL_MUL_RID`: For all real $x$, $x \cdot 1 = x$.
  - `DIFF_CONT`: Differentiability implies continuity.
  - `CONTL_SEQ`: Continuous function preserves limits of sequences.
  - `LN_MUL`: Logarithm of a product equals sum of logarithms.
  - `LN_DIV`: Logarithm of a quotient equals difference of logarithms.
  - `LN_POW`: Logarithm of a power equals product of power and logarithm.
  - `WALLIS`: The Wallis product formula for $\pi/2$.

- **Definitions**:
  - `ln`: Natural logarithm function.

### Porting notes
When porting this theorem, special attention should be paid to:
1. The representation of natural numbers and reals, especially in the factorial expressions.
2. The treatment of limits and convergence in the target system.
3. The Wallis product formula (`WALLIS`) which is a key dependency and might need to be ported first.
4. The treatment of logarithms and their properties in the target system.

---

## STIRLING

### STIRLING
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let STIRLING = prove
 (`(\n. ln(&(FACT n)) - ((&n + &1 / &2) * ln(&n) - &n + ln(&2 * pi) / &2))
   --> &0`,
  REWRITE_TAC[REAL_ARITH `a - (b - c + d) = (a - (b - c)) - d`] THEN
  SUBST1_TAC(SYM(SPEC `ln(&2 * pi) / &2` REAL_SUB_REFL)) THEN
  MATCH_MP_TAC SEQ_SUB THEN REWRITE_TAC[SEQ_CONST] THEN
  X_CHOOSE_THEN `C:real` MP_TAC STIRLING_CONVERGES THEN
  GEN_REWRITE_TAC (funpow 2 LAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[stirling] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`2`; `1`] o MATCH_MP SEQ_SUBSEQ) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`2`; `0`] o MATCH_MP SEQ_SUBSEQ) THEN
  REWRITE_TAC[ARITH; ADD_CLAUSES; IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SEQ_ADD) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SEQ_MUL o CONJ (SPEC `&4` SEQ_CONST)) THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP SEQ_SUB) THEN
  MP_TAC LN_WALLIS THEN REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SEQ_SUB) THEN
  REWRITE_TAC[ARITH_RULE
   `(a + &4 * x - (y + z)) - (&4 * (x - b) - ((y - c) + (z - d))) =
    (a + &4 * b) - (c + d)`] THEN
  DISCH_THEN(fun th -> POP_ASSUM MP_TAC THEN ASSUME_TAC th) THEN
  SUBGOAL_THEN `C = ln(&2 * pi) / &2` (fun th -> REWRITE_TAC[th]) THEN
  POP_ASSUM(MP_TAC o CONJ (SPEC `&2 * ln(&2)` SEQ_CONST)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SEQ_ADD) THEN
  SIMP_TAC[LN_DIV; PI_POS; REAL_OF_NUM_LT; ARITH; LN_MUL] THEN
  REWRITE_TAC[REAL_ARITH `&2 * l + p - l - (&4 * C - (C + C)) =
                          (l + p) - &2 * C`] THEN
  SIMP_TAC[REAL_ARITH `C = (l + p) / &2 <=> (l + p) - &2 * C = &0`] THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b ==> c <=> b ==> a ==> c`]
    SEQ_UNIQ) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[REAL_ARITH
   `a + (b + &4 * (c - x)) - ((d - &2 * x) + (e - (&2 * x + &1))) =
    (a + b + &4 * c + &1) - (d + e)`] THEN
  REWRITE_TAC[REAL_ARITH `&2 * l + &4 * n * l + &4 * (n + &1 / &2) * x + &1 =
                          (&4 * n + &2) * (l + x) + &1`] THEN
  ONCE_REWRITE_TAC[SEQ_SUC] THEN
  SIMP_TAC[GSYM LN_MUL; REAL_OF_NUM_LT; ARITH; LT_0] THEN
  REWRITE_TAC[GSYM SEQ_SUC] THEN
  CONV_TAC(LAND_CONV(GEN_ALPHA_CONV `n:num`)) THEN
  REWRITE_TAC[REAL_ARITH
   `((&4 * n + &2) * l + &1) - ((&2 * n + &1 / &2) * l + z) =
    (&2 * n + &3 / &2) * l + &1 - z`] THEN
  REWRITE_TAC[REAL_ARITH
   `(&2 * n + &3 / &2) * l + &1 - ((&2 * n + &1) + &1 / &2) * l' =
    (&2 * n + &3 / &2) * (l - l') + &1`] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `&0 = -- &1 + &1`] THEN
  MATCH_MP_TAC SEQ_ADD THEN REWRITE_TAC[SEQ_CONST] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a * (b - c) = --(a * (c - b))`] THEN
  REWRITE_TAC[GSYM SEQ_NEG] THEN
  ONCE_REWRITE_TAC[SEQ_SUC] THEN
  SIMP_TAC[GSYM LN_DIV; REAL_LT_MUL; REAL_OF_NUM_LT; LT_0; ARITH;
           REAL_ARITH `&0 < &2 * &n + &1`] THEN
  SIMP_TAC[REAL_OF_NUM_LT; LT_0; REAL_FIELD
   `&0 < x ==> (&2 * x + &1) / (&2 * x) = &1 + &1 / (&2 * x)`] THEN
  REWRITE_TAC[GSYM SEQ_SUC] THEN
  CONV_TAC(LAND_CONV(GEN_ALPHA_CONV `n:num`)) THEN
  MP_TAC SEQ_SUBSEQ THEN REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
  DISCH_THEN(MP_TAC o GENL [`f:num->real`; `l:real`] o
   SPECL [`f:num->real`; `l:real`; `2`; `0`]) THEN
  REWRITE_TAC[ADD_CLAUSES; ARITH; REAL_OF_NUM_MUL] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONV_TAC(LAND_CONV(GEN_ALPHA_CONV `n:num`)) THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `&1 = &1 + &3 / &2 * &0`] THEN
  MATCH_MP_TAC SEQ_ADD THEN REWRITE_TAC[LN_LIM_LEMMA] THEN
  MATCH_MP_TAC SEQ_MUL THEN REWRITE_TAC[SEQ_CONST] THEN
  MP_TAC LN_LIM_LEMMA THEN MP_TAC(SPEC `&1` SEQ_HARMONIC) THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP SEQ_MUL) THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[SEQ_SUC] THEN
  SIMP_TAC[real_div; REAL_MUL_LID; REAL_MUL_ASSOC; REAL_MUL_LINV;
           REAL_MUL_RID; REAL_OF_NUM_EQ; NOT_SUC]);;
```

### Informal statement
This theorem states that Stirling's approximation for the factorial function is asymptotically correct. Specifically:

$$\lim_{n \to \infty} \left(\ln(n!) - \left(\left(n + \frac{1}{2}\right)\ln(n) - n + \frac{\ln(2\pi)}{2}\right)\right) = 0$$

This is equivalent to the more common form of Stirling's approximation:

$$n! \sim \sqrt{2\pi n} \left(\frac{n}{e}\right)^n$$

as $n \to \infty$.

### Informal proof
The proof establishes the convergence of Stirling's approximation for factorials through several algebraic manipulations and convergence properties of sequences:

- Start by rewriting the subtraction in a form amenable to sequence manipulation: 
  $$a - (b - c + d) = (a - (b - c)) - d$$

- Use the fact that $\ln(2\pi)/2 - \ln(2\pi)/2 = 0$ (via `REAL_SUB_REFL`)

- Apply `SEQ_SUB` to split the limit into components where the second term is a constant (`SEQ_CONST`)

- Extract a constant $C$ from `STIRLING_CONVERGES` which represents the limiting value

- Apply `SEQ_SUBSEQ` to manipulate specific subsequences (with parameters $a=2$ and $b$ values of $0$ and $1$)

- Use various sequence properties (`SEQ_ADD`, `SEQ_MUL`, `SEQ_SUB`) to combine and transform these subsequences

- Apply `LN_WALLIS` (a result about the logarithm of Wallis' product for π)

- Through algebraic manipulation, establish that $C = \ln(2\pi)/2$

- Use logarithm properties (`LN_DIV`, `LN_MUL`) and arithmetic rearrangements to simplify expressions

- Apply `SEQ_UNIQ` to identify the unique limit of 0 for the sequence

- Further manipulate terms using `LN_LIM_LEMMA` and `SEQ_HARMONIC` to complete the proof

The proof combines properties of logarithms, factorial, and sequence convergence to establish Stirling's approximation.

### Mathematical insight
Stirling's approximation is a fundamental result in asymptotic analysis, providing a remarkably accurate approximation to the factorial function for large values of n. The formula is widely used throughout mathematics, statistics, and physics.

The proof establishes the asymptotic equality:
$$n! \sim \sqrt{2\pi n} \left(\frac{n}{e}\right)^n$$

This approximation is particularly valuable because the factorial function grows extremely quickly, making direct computation difficult for large n. Stirling's formula provides a continuous approximation that is easier to work with analytically.

The constant $\sqrt{2\pi}$ in the formula has deep connections to probability theory, appearing in the normalization factor of the Gaussian distribution. This hints at the central role of Stirling's formula in asymptotics of discrete probability distributions.

### Dependencies
#### Theorems
- `REAL_MUL_RID`: $\forall x. x * 1 = x$
- `REAL_SUB_REFL`: $\forall x. x - x = 0$
- `SEQ_CONST`: $\forall k. (\lambda x. k) \to k$
- `SEQ_ADD`: $\forall x, x_0, y, y_0. x \to x_0 \land y \to y_0 \Rightarrow (\lambda n. x(n) + y(n)) \to (x_0 + y_0)$
- `SEQ_MUL`: $\forall x, x_0, y, y_0. x \to x_0 \land y \to y_0 \Rightarrow (\lambda n. x(n) * y(n)) \to (x_0 * y_0)$
- `SEQ_NEG`: $\forall x, x_0. x \to x_0 \Leftrightarrow (\lambda n. -(x n)) \to -x_0$
- `SEQ_SUB`: $\forall x, x_0, y, y_0. x \to x_0 \land y \to y_0 \Rightarrow (\lambda n. x(n) - y(n)) \to (x_0 - y_0)$
- `SEQ_UNIQ`: $\forall x, x_1, x_2. x \to x_1 \land x \to x_2 \Rightarrow (x_1 = x_2)$
- `SEQ_SUC`: $\forall f, l. f \to l \Leftrightarrow (\lambda n. f(SUC n)) \to l$
- `SEQ_SUBSEQ`: $\forall f, l. f \to l \Rightarrow \forall a, b. \lnot(a = 0) \Rightarrow (\lambda n. f(a * n + b)) \to l$
- `LN_MUL`: $\forall x, y. 0 < x \land 0 < y \Rightarrow (ln(x * y) = ln(x) + ln(y))$
- `LN_DIV`: $\forall x. 0 < x \land 0 < y \Rightarrow (ln(x / y) = ln(x) - ln(y))$

#### Not explicitly listed but referenced in the proof
- `STIRLING_CONVERGES`: A result establishing the convergence of Stirling's approximation
- `LN_WALLIS`: A result related to the logarithm of Wallis' product for π
- `LN_LIM_LEMMA`: A lemma about limiting behavior of logarithmic expressions
- `SEQ_HARMONIC`: A result about the harmonic sequence

#### Definitions
- `ln`: $ln\,x = @u.\,exp(u) = x$

### Porting notes
When porting this theorem:

1. The proof relies heavily on sequence limit theorems and properties of logarithms, which would need to be established first.

2. The proof uses several specialized theorems that may not be standard in other systems, like `STIRLING_CONVERGES`, `LN_WALLIS`, and `LN_LIM_LEMMA`. These would need to be ported first or alternative proofs would need to be constructed.

3. The formal statement uses the HOL Light notation for convergence of sequences (`-->`) which would need to be appropriately translated to the target system's notion of limits.

4. HOL Light's real numbers are included by default, while some systems require importing a real analysis library.

---

