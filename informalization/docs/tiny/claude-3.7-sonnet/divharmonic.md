# divharmonic.ml

## Overview

Number of statements: 2

This file formalizes the proof that the harmonic series (sum of 1/n) diverges. It builds on the analysis and transcendental function libraries to establish that the sequence of partial sums grows beyond any bound. The file likely includes the standard proof that compares the harmonic series with an integral or uses grouping techniques to demonstrate divergence. The formalization provides a rigorous treatment of this fundamental result in analysis.

## HARMONIC_LEMMA

### HARMONIC_LEMMA
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let HARMONIC_LEMMA = prove
 (`!m. sum(1..2 EXP m) (\n. &1 / &n) >= &m / &2`,
  REWRITE_TAC[real_ge] THEN INDUCT_TAC THEN
  REWRITE_TAC[EXP; MULT_2; SUM_SING_NUMSEG] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `1 <= 2 EXP m + 1`] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
   `a <= x ==> b - a <= y ==> b <= x + y`)) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; GSYM (CONJUNCT2 EXP); GSYM MULT_2] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(2 EXP m + 1..2 EXP (SUC m))(\n. &1 / &(2 EXP (SUC m)))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[SUM_CONST_NUMSEG; EXP; ARITH_RULE `(2 * x + 1) - (x + 1) = x`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    MP_TAC(SPECL [`2`; `m:num`] EXP_EQ_0) THEN
    REWRITE_TAC[ARITH] THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
    CONV_TAC REAL_FIELD;
    MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ARITH_TAC]);;
```

### Informal statement
For all natural numbers $m$, the following inequality holds:
$$\sum_{n=1}^{2^m} \frac{1}{n} \geq \frac{m}{2}$$

This is stating that the partial sum of the first $2^m$ terms of the harmonic series is greater than or equal to $\frac{m}{2}$.

### Informal proof
The proof proceeds by induction on $m$:

**Base case** ($m = 0$): 
- We need to show $\sum_{n=1}^{2^0} \frac{1}{n} \geq \frac{0}{2}$
- Since $2^0 = 1$, this reduces to showing $\frac{1}{1} \geq 0$, which is true

**Inductive step**: Assume $\sum_{n=1}^{2^m} \frac{1}{n} \geq \frac{m}{2}$ for some $m$

We need to show $\sum_{n=1}^{2^{m+1}} \frac{1}{n} \geq \frac{m+1}{2}$

- Split the sum: $\sum_{n=1}^{2^{m+1}} \frac{1}{n} = \sum_{n=1}^{2^m} \frac{1}{n} + \sum_{n=2^m+1}^{2^{m+1}} \frac{1}{n}$
- By induction hypothesis, $\sum_{n=1}^{2^m} \frac{1}{n} \geq \frac{m}{2}$
- We need to show $\sum_{n=2^m+1}^{2^{m+1}} \frac{1}{n} \geq \frac{1}{2}$

For the second part, we use the fact that for all $n$ in the range $[2^m+1, 2^{m+1}]$, we have $\frac{1}{n} \geq \frac{1}{2^{m+1}}$. Therefore:

$\sum_{n=2^m+1}^{2^{m+1}} \frac{1}{n} \geq \sum_{n=2^m+1}^{2^{m+1}} \frac{1}{2^{m+1}} = (2^{m+1} - (2^m+1) + 1) \cdot \frac{1}{2^{m+1}} = \frac{2^m}{2^{m+1}} = \frac{1}{2}$

Therefore, $\sum_{n=1}^{2^{m+1}} \frac{1}{n} \geq \frac{m}{2} + \frac{1}{2} = \frac{m+1}{2}$, which completes the proof.

### Mathematical insight
This lemma provides a key lower bound for the partial sums of the harmonic series, showing that they grow at least logarithmically. Since $2^m$ can be written as $e^{m \ln 2}$, this result effectively shows that $\sum_{n=1}^{N} \frac{1}{n} \geq \frac{\ln N}{2\ln 2}$, which grows without bound as $N$ increases.

This lemma is a critical step in proving that the harmonic series diverges, as it establishes that the partial sums can be made arbitrarily large by taking sufficiently many terms.

### Dependencies
- `REAL_LE_TRANS` - Transitivity of the less-than-or-equal relation on real numbers
- `sum` - Definition of finite sums

### Porting notes
When porting this theorem:
- The induction on $m$ is standard and should translate directly
- Be careful with the numerical conversions (`REAL_OF_NUM`) which may be handled differently in other systems
- The key algebraic manipulations involve splitting the sum at $2^m$ and using the fact that $\frac{1}{n} \geq \frac{1}{2^{m+1}}$ for all $n$ in the range $[2^m+1, 2^{m+1}]$
- The proof uses multiple arithmetic simplifications that might need to be handled explicitly in other systems

---

## LOG_BOUND

### LOG_BOUND
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LOG_BOUND = prove
 (`&0 < x /\ x < &1 ==> ln(&1 + x) >= x / &2`,
  REWRITE_TAC[real_ge] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM LN_EXP] THEN
  ASM_SIMP_TAC[LN_MONO_LE; REAL_EXP_POS_LT; REAL_LT_ADD; REAL_LT_01] THEN
  MP_TAC(SPEC `x / &2` REAL_EXP_BOUND_LEMMA) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC);;
```

### Informal statement
For all real $x$ where $0 < x < 1$, we have:
$$\ln(1 + x) \geq \frac{x}{2}$$

### Informal proof
This theorem provides a lower bound for $\ln(1+x)$ when $x$ is between 0 and 1.

The proof proceeds as follows:
- We first rewrite the inequality $\ln(1+x) \geq \frac{x}{2}$ using the definition of $\geq$ in terms of $\leq$.
- Next, we rewrite the left-hand side using the property that $\ln(\exp(y)) = y$ for any real $y$ (using `LN_EXP`).
- Since $x > 0$ and $0 < 1$, we know that $0 < 1+x$ by `REAL_LT_ADD`. This allows us to apply the monotonicity of $\ln$ (using `LN_MONO_LE`).
- We use the lemma `REAL_EXP_BOUND_LEMMA` which provides bounds for $\exp(y)$, specifically for $y = \frac{x}{2}$.
- Finally, we combine all the assumptions and complete the proof using arithmetic reasoning.

### Mathematical insight
This theorem provides a simple but useful lower bound for the natural logarithm function in the interval $(0,1)$. The bound $\ln(1+x) \geq \frac{x}{2}$ shows that $\ln(1+x)$ grows at least half as quickly as $x$ in this interval.

This result is part of a family of bounds and approximations for logarithmic functions that are commonly used in analysis. It's particularly useful in contexts where we need to estimate or bound logarithmic expressions, such as in convergence proofs or error analysis.

The inequality can be understood intuitively by considering the concavity of the $\ln$ function - while $\ln(1+x)$ is always less than $x$ for $x > 0$ (another well-known bound), this theorem ensures it doesn't fall below $\frac{x}{2}$ when $x < 1$.

### Dependencies
- Theorems:
  - `REAL_LT_01`: States that $0 < 1$ in the reals.
  - `REAL_LT_ADD`: For real numbers $x,y$, if $0 < x$ and $0 < y$, then $0 < x + y$.
  - `LN_EXP`: For all real $x$, $\ln(\exp(x)) = x$.
  - `LN_MONO_LE`: For positive reals $x,y$, $\ln(x) \leq \ln(y) \iff x \leq y$ (monotonicity of $\ln$).
- Definitions:
  - `ln`: The natural logarithm function defined as $\ln(x) = u$ where $\exp(u)=x$.
- Other (not explicitly listed):
  - `REAL_EXP_BOUND_LEMMA`: A lemma providing bounds for the exponential function.
  - `REAL_EXP_POS_LT`: States that $\exp(x) > 0$ for all real $x$.

### Porting notes
When porting this theorem to other proof assistants:
- Make sure equivalent variants of the logarithm and exponential functions are available.
- Check if the target system has a similar lemma to `REAL_EXP_BOUND_LEMMA` for bounding exponential functions.
- The use of `ARITH_TAC` at the end suggests that straightforward arithmetic reasoning completes the proof, which might need to be expanded in systems with different automation capabilities.

---

