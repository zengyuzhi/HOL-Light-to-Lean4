# arithmetic_geometric_mean.ml

## Overview

Number of statements: 5

This file formalizes the arithmetic-geometric mean (AM-GM) inequality in HOL Light. It establishes the relationship that the arithmetic mean of non-negative real numbers is greater than or equal to their geometric mean, with equality holding if and only if all numbers are equal. The implementation builds upon products and transcendental functions by utilizing the imports from products.ml and transc.ml. The file provides rigorous proofs of both the binary and n-ary versions of this fundamental mathematical inequality.

## LEMMA_1

### LEMMA_1
- LEMMA_1

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LEMMA_1 = prove
 (`!x n. x pow (n + 1) - (&n + &1) * x + &n =
         (x - &1) pow 2 * sum(1..n) (\k. &k * x pow (n - k))`,
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ; ADD_CLAUSES] THENL
   [REAL_ARITH_TAC; REWRITE_TAC[ARITH_RULE `1 <= SUC n`]] THEN
  SIMP_TAC[ARITH_RULE `k <= n ==> SUC n - k = SUC(n - k)`; SUB_REFL] THEN
  REWRITE_TAC[real_pow; REAL_MUL_RID] THEN
  REWRITE_TAC[REAL_ARITH `k * x * x pow n = (k * x pow n) * x`] THEN
  ASM_REWRITE_TAC[SUM_RMUL; REAL_MUL_ASSOC; REAL_ADD_LDISTRIB] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_POW_ADD] THEN REAL_ARITH_TAC);;
```

### Informal statement
For any real number $x$ and natural number $n$, the following identity holds:
$$x^{n+1} - (n+1)x + n = (x-1)^2 \sum_{k=1}^{n} k \cdot x^{n-k}$$

### Informal proof
The proof proceeds by induction on the natural number $n$.

- **Base case**: When $n = 0$, we need to show:
  $$x^1 - (0+1)x + 0 = (x-1)^2 \sum_{k=1}^{0} k \cdot x^{0-k}$$
  
  The right side is an empty sum (as $k$ ranges from 1 to 0, which is empty), so it equals 0.
  The left side simplifies to $x - x = 0$.
  This is handled by the `REAL_ARITH_TAC` tactic.

- **Inductive step**: Assume the formula holds for some $n$. We need to prove it for $n+1$.
  
  First, we handle the summation boundaries using `SUM_CLAUSES_NUMSEG` and establish that $1 \leq n+1$.
  
  For each term in the sum, we transform ${(n+1) - k = (n-k) + 1}$ to work with the expression.
  
  We rewrite $x^{(n+1)-k}$ as $x^{(n-k)+1} = x^{n-k} \cdot x$ and distribute as needed.
  
  Finally, we use the inductive hypothesis and perform algebraic manipulations to complete the proof.
  
  The final steps involve distributing and combining terms, ultimately showing that the identity holds for $n+1$.

### Mathematical insight
This lemma establishes a non-trivial identity relating powers of $x$ to a weighted sum involving powers of $x$, multiplied by $(x-1)^2$. The identity is useful in various algebraic manipulations and can be seen as a special case of a more general pattern relating differences of powers.

The lemma appears in the context of proving the arithmetic-geometric mean inequality, as noted in the comment. The comment mentions that this proof is based on work by Michael Hirschhorn published in Mathematical Intelligencer.

### Dependencies
No explicit dependencies were listed in the provided information.

### Porting notes
When porting this proof:
- Induction is straightforward and should be available in most proof assistants
- The proof uses several arithmetic simplification tactics that would need equivalent operations in the target system
- The handling of summations and manipulations of powers follows standard patterns
- Real arithmetic simplifications (via `REAL_ARITH_TAC`) would need corresponding automation in the target system

---

## LEMMA_2

### Name of formal statement
LEMMA_2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LEMMA_2 = prove
 (`!n x. &0 <= x ==> &0 <= x pow (n + 1) - (&n + &1) * x + &n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LEMMA_1] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE] THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_POW_LE]);;
```

### Informal statement
For all natural numbers $n$ and real numbers $x$ such that $x \geq 0$, we have
$$x^{n+1} - (n+1)x + n \geq 0$$

### Informal proof
This theorem is proved using LEMMA_1 (which is not provided in the dependencies), but appears to be a lemma that gives an equivalent form of the expression $x^{n+1} - (n+1)x + n$.

The proof proceeds as follows:

- First, we rewrite the goal using LEMMA_1, which likely expresses the left-hand side in a form that makes the inequality more evident.
- Then, we use `MATCH_MP_TAC REAL_LE_MUL` which is a rule for showing that a product is non-negative when its factors are non-negative.
- We rewrite using `REAL_POW_2` and `REAL_LE_SQUARE` to handle squared terms.
- Next, we use `MATCH_MP_TAC SUM_POS_LE_NUMSEG`, which allows us to deduce that a sum over a numeric range is non-negative if all its terms are non-negative.
- Finally, we use simplification with `REAL_LE_MUL`, `REAL_POS`, and `REAL_POW_LE` to establish that all terms in the sum are non-negative, using the assumption that $x \geq 0$.

### Mathematical insight
This lemma establishes a non-obvious inequality between powers of non-negative real numbers. The inequality $x^{n+1} - (n+1)x + n \geq 0$ for $x \geq 0$ has applications in various mathematical contexts, particularly in analysis and polynomial inequalities.

Based on the proof structure, LEMMA_1 likely provides a reformulation of the expression as a sum of products, which makes it easier to prove the non-negativity by showing that each term in the sum is non-negative.

### Dependencies
#### Theorems
- `LEMMA_1` - Not provided in the dependency list, but appears to be crucial for reformulating the expression
- `REAL_LE_MUL` - Used to show that a product is non-negative when its factors are non-negative
- `REAL_POW_2` - Definition or property of squared terms
- `REAL_LE_SQUARE` - Property that squares of real numbers are non-negative
- `SUM_POS_LE_NUMSEG` - If all terms in a sum over a numeric range are non-negative, the sum is non-negative
- `REAL_LE_MUL` - Property of multiplication preserving non-negativity
- `REAL_POS` - Property stating that certain values are positive
- `REAL_POW_LE` - Property about non-negativity of powers of non-negative numbers

### Porting notes
When porting this theorem:
1. Ensure that LEMMA_1 is correctly ported first, as the proof relies heavily on it
2. Check how the target system handles numeric types - the theorem uses both natural numbers `n` and real numbers like `&n` (the real injection of natural number n)
3. The proof uses automation and matching tactics that may need to be adapted to the target system's proof style

---

## LEMMA_3

### Name of formal statement
LEMMA_3

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LEMMA_3 = prove
 (`!n x. 1 <= n /\ (!i. 1 <= i /\ i <= n + 1 ==> &0 <= x i)
         ==> x(n + 1) * (sum(1..n) x / &n) pow n
                <= (sum(1..n+1) x / (&n + &1)) pow (n + 1)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `a = sum(1..n+1) x / (&n + &1)` THEN
  ABBREV_TAC `b = sum(1..n) x / &n` THEN
  SUBGOAL_THEN `x(n + 1) = (&n + &1) * a - &n * b` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; LE_1;
                 REAL_ARITH `~(&n + &1 = &0)`] THEN
    SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `1 <= n + 1`; SUM_SING_NUMSEG] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= a /\ &0 <= b` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_DIV THEN
    (CONJ_TAC THENL [MATCH_MP_TAC SUM_POS_LE_NUMSEG; REAL_ARITH_TAC]) THEN
    ASM_SIMP_TAC[ARITH_RULE `p <= n ==> p <= n + 1`];
    ALL_TAC] THEN
  ASM_CASES_TAC `b = &0` THEN
  ASM_SIMP_TAC[REAL_POW_ZERO; LE_1; REAL_MUL_RZERO; REAL_POW_LE] THEN
  MP_TAC(ISPECL [`n:num`; `a / b`] LEMMA_2) THEN ASM_SIMP_TAC[REAL_LE_DIV] THEN
  REWRITE_TAC[REAL_ARITH `&0 <= x - a + b <=> a - b <= x`; REAL_POW_DIV] THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_POW_ADD] THEN UNDISCH_TAC `~(b = &0)` THEN
  CONV_TAC REAL_FIELD);;
```

### Informal statement
For any natural number $n$ and function $x$, if $1 \leq n$ and $x(i) \geq 0$ for all $i$ such that $1 \leq i \leq n+1$, then:

$$x(n+1) \cdot \left(\frac{\sum_{i=1}^n x(i)}{n}\right)^n \leq \left(\frac{\sum_{i=1}^{n+1} x(i)}{n+1}\right)^{n+1}$$

### Informal proof
This is a proof by algebraic manipulation.

* First, we introduce abbreviations:
  - Let $a = \frac{\sum_{i=1}^{n+1} x(i)}{n+1}$
  - Let $b = \frac{\sum_{i=1}^n x(i)}{n}$

* We establish that $x(n+1) = (n+1)a - nb$ by algebraic manipulation:
  - $\sum_{i=1}^{n+1} x(i) = \sum_{i=1}^n x(i) + x(n+1)$
  - $(n+1)a = \sum_{i=1}^{n+1} x(i) = \sum_{i=1}^n x(i) + x(n+1) = nb + x(n+1)$
  - Therefore $x(n+1) = (n+1)a - nb$

* We show that $a \geq 0$ and $b \geq 0$ as both are weighted sums of non-negative values $x(i)$.

* We consider two cases:
  - Case $b = 0$: In this case, the left side of our inequality is $0$, making the inequality trivially true since the right side is non-negative.
  
  - Case $b \neq 0$: We apply LEMMA_2 (with parameters $n$ and $\frac{a}{b}$), which gives us:
    $$\left(\frac{a}{b}\right)^n \cdot \left(n \cdot \left(\frac{a}{b} - 1\right) + 1\right) \leq \left(\frac{a}{b}\right)^{n+1}$$
    
    After algebraic manipulation, this is equivalent to our goal:
    $$x(n+1) \cdot b^n \leq a^{n+1}$$
    
    The proof is completed by algebraic simplification.

### Mathematical insight
This lemma essentially proves an inequality between weighted means. It shows that as we include an additional non-negative term $x(n+1)$ in a weighted average, a specific inequality holds between the powers of these averages.

This result appears to be a building block toward proving inequalities related to arithmetic means and potentially the inequality of arithmetic and geometric means. The structure suggests it may be part of a larger inductive argument about weighted averages.

### Dependencies
- `LEMMA_2`: A previous result that this proof builds upon
- Basic HOL Light theorems about real arithmetic and summation

### Porting notes
When implementing this theorem in other systems:
- Ensure the summation notation is properly defined
- The proof relies heavily on algebraic manipulation and case analysis
- Pay attention to division by zero handling, as the proof separates the case when $b = 0$

---

## AGM

### Name of formal statement
AGM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let AGM = prove
 (`!n a. 1 <= n /\ (!i. 1 <= i /\ i <= n ==> &0 <= a(i))
         ==> product(1..n) a <= (sum(1..n) a / &n) pow n`,
  INDUCT_TAC THEN REWRITE_TAC[ARITH; PRODUCT_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[ARITH_RULE `1 <= SUC n`] THEN X_GEN_TAC `x:num->real` THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[PRODUCT_CLAUSES_NUMSEG; ARITH; SUM_SING_NUMSEG] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[ADD1] THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `x(n + 1) * (sum(1..n) x / &n) pow n` THEN
    ASM_SIMP_TAC[LEMMA_3; GSYM REAL_OF_NUM_ADD; LE_1;
                 ARITH_RULE `i <= n ==> i <= n + 1`] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[LE_REFL; LE_1; ARITH_RULE `i <= n ==> i <= n + 1`]]);;
```

### Informal statement
For any positive integer $n$ and function $a: \mathbb{N} \to \mathbb{R}$ such that $a(i) \geq 0$ for all $i$ with $1 \leq i \leq n$, the arithmetic-geometric mean inequality holds:

$$\prod_{i=1}^{n} a(i) \leq \left(\frac{\sum_{i=1}^{n} a(i)}{n}\right)^n$$

### Informal proof
The proof proceeds by induction on $n$.

**Base case ($n = 1$):**
- When $n = 1$, the product $\prod_{i=1}^{1} a(i) = a(1)$ and the sum $\sum_{i=1}^{1} a(i) = a(1)$.
- Therefore, $\prod_{i=1}^{1} a(i) = a(1) = \left(\frac{a(1)}{1}\right)^1 = \left(\frac{\sum_{i=1}^{1} a(i)}{1}\right)^1$, which trivially satisfies the inequality with equality.

**Inductive step:**
- Assume the inequality holds for some $n \geq 1$.
- We need to prove it for $n+1$.
- The proof applies a transitive inequality:
  - First, we show $\prod_{i=1}^{n+1} a(i) \leq a(n+1) \cdot \left(\frac{\sum_{i=1}^{n} a(i)}{n}\right)^n$
  - Then, we use the fact that $a(n+1) \cdot \left(\frac{\sum_{i=1}^{n} a(i)}{n}\right)^n \leq \left(\frac{\sum_{i=1}^{n+1} a(i)}{n+1}\right)^{n+1}$
- The first part follows from the induction hypothesis.
- The second part requires a separate lemma (LEMMA_3, not shown in the dependencies) which likely relates to the weighted AM-GM inequality.
- The inequality is preserved by multiplication since $a(i) \geq 0$ for all $i$.

### Mathematical insight
The theorem formalizes the well-known Arithmetic-Geometric Mean (AGM) inequality, which states that the arithmetic mean of non-negative real numbers is greater than or equal to their geometric mean, with equality if and only if all the numbers are equal.

This inequality is fundamental in analysis and has numerous applications in optimization, information theory, and other areas of mathematics. The inequality captures the intuition that the arithmetic mean is "pulled" toward the larger values compared to the geometric mean.

The proof technique using induction is standard for this inequality, though there are other proof methods (using Jensen's inequality, Cauchy-Schwarz inequality, or Lagrange multipliers).

### Dependencies
- **Theorems**:
  - `PRODUCT_CLAUSES_NUMSEG`: Defines recursive clauses for calculating the product of a function over a finite range of natural numbers.
  - `LEMMA_3`: This appears in the proof but is not provided in the dependencies. It likely demonstrates why $a(n+1) \cdot \left(\frac{\sum_{i=1}^{n} a(i)}{n}\right)^n \leq \left(\frac{\sum_{i=1}^{n+1} a(i)}{n+1}\right)^{n+1}$.

### Porting notes
- When porting, ensure that the library has appropriate definitions for finite products and sums over ranges.
- The theorem uses forward reasoning with transitive inequality, which might require explicit chain of inequalities in systems with less automation for inequalities.
- The specialized lemma (LEMMA_3) would need to be identified and ported first, as it's crucial to completing the inductive step.
- Consider whether the target system has existing libraries for AM-GM inequality that could be leveraged instead of porting this specific implementation.

---

## AGM_ROOT

### Name of formal statement
AGM_ROOT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let AGM_ROOT = prove
 (`!n a. 1 <= n /\ (!i. 1 <= i /\ i <= n ==> &0 <= a(i))
         ==> root n (product(1..n) a) <= sum(1..n) a / &n`,
  INDUCT_TAC THEN REWRITE_TAC[ARITH; ARITH_RULE `1 <= SUC n`] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `root(SUC n) ((sum(1..SUC n) a / &(SUC n)) pow (SUC n))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ROOT_MONO_LE THEN
    ASM_SIMP_TAC[AGM; ARITH_RULE `1 <= SUC n`] THEN
    MATCH_MP_TAC PRODUCT_POS_LE THEN
    ASM_REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC POW_ROOT_POS THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; SUM_POS_LE_NUMSEG]]);;
```

### Informal statement
For any natural number $n \geq 1$ and any function $a : \mathbb{N} \to \mathbb{R}$ where $a(i) \geq 0$ for all $i \in \{1, 2, \ldots, n\}$, the following inequality holds:

$$\sqrt[n]{\prod_{i=1}^{n} a(i)} \leq \frac{\sum_{i=1}^{n} a(i)}{n}$$

This is a statement of the arithmetic-geometric mean inequality in a root form.

### Informal proof
The proof proceeds by induction on $n$.

**Base case** ($n = 1$): 
For $n = 1$, the inequality becomes $\sqrt[1]{a(1)} \leq \frac{a(1)}{1}$, which simplifies to $a(1) \leq a(1)$, which is trivially true. This case is handled by arithmetic simplifications.

**Inductive step**:
Assume the theorem holds for $n$, and we need to prove it for $n+1$.

* We apply transitivity of $\leq$ using `REAL_LE_TRANS` to establish:
  $$\sqrt[n+1]{\prod_{i=1}^{n+1} a(i)} \leq \sqrt[n+1]{\left(\frac{\sum_{i=1}^{n+1} a(i)}{n+1}\right)^{n+1}} \leq \frac{\sum_{i=1}^{n+1} a(i)}{n+1}$$

* For the first inequality, we use `ROOT_MONO_LE` to show that the $n+1$-th root is monotonically increasing, along with the arithmetic-geometric mean inequality (`AGM` theorem) to establish:
  $$\prod_{i=1}^{n+1} a(i) \leq \left(\frac{\sum_{i=1}^{n+1} a(i)}{n+1}\right)^{n+1}$$

* We also use `PRODUCT_POS_LE` to verify that the product is non-negative, which is necessary for applying the root function.

* For the second inequality, we apply `POW_ROOT_POS` which states that for $x \geq 0$ and any $n$, $\sqrt[n+1]{x^{n+1}} = x$. This simplifies the right side of our first inequality to exactly $\frac{\sum_{i=1}^{n+1} a(i)}{n+1}$.

* We verify that $\frac{\sum_{i=1}^{n+1} a(i)}{n+1} \geq 0$ using `REAL_LE_DIV`, `REAL_POS`, and `SUM_POS_LE_NUMSEG` since all $a(i) \geq 0$.

### Mathematical insight
This theorem states the arithmetic-geometric mean inequality in terms of the $n$-th root of a product rather than the more common formulation using geometric mean directly. The inequality establishes that the geometric mean of non-negative numbers is always less than or equal to their arithmetic mean, which is a fundamental inequality in analysis and optimization.

The proof elegantly uses induction and properties of roots to establish this relationship, showing how the more general AM-GM inequality can be derived from simpler cases. This form is particularly useful in contexts where working with roots is more convenient than with direct geometric means.

### Dependencies
#### Theorems
- `PRODUCT_POS_LE`: If a set $s$ is finite and all elements $x \in s$ satisfy $f(x) \geq 0$, then the product $\prod_{x \in s} f(x) \geq 0$.
- `POW_ROOT_POS`: For any natural number $n$ and real $x \geq 0$, $\sqrt[n+1]{x^{n+1}} = x$.
- `AGM`: The arithmetic-geometric mean inequality (not directly shown in dependencies but used).
- `ROOT_MONO_LE`: If $0 \leq a \leq b$, then $\sqrt[n]{a} \leq \sqrt[n]{b}$ (not directly shown in dependencies but used).

### Porting notes
When porting this theorem:
1. Ensure your target system has appropriate definitions for $n$-th roots, particularly for handling the edge cases when inputs are zero.
2. The theorem uses HOL Light's `product` and `sum` functions over intervals of natural numbers (1..n), so make sure equivalent constructs exist in your target system.
3. Check that your system has basic theorems about the monotonicity of roots and the relationship between powers and roots, which are essential for this proof.

---

