# arithmetic_geometric_mean.ml

## Overview

Number of statements: 5

`arithmetic_geometric_mean.ml` formalizes the arithmetic-geometric mean inequality. The file relies on real number theory from `transc.ml` and product notation defined in `products.ml`. It provides definitions and proves theorems related to this fundamental inequality.


## LEMMA_1

### Name of formal statement
LEMMA_1

### Type of the formal statement
theorem

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
For all real numbers `x` and natural numbers `n`, the following equation holds:
`x^(n+1) - (n+1) * x + n = (x - 1)^2 * sum(k=1 to n, k * x^(n-k))`.

### Informal sketch
The proof proceeds by induction on `n`.

- Base case (`n = 0`): The equation simplifies and is proven by real arithmetic.
- Inductive step: Assume the equation holds for `n`. We need to prove it for `n+1`.
  - Expand the summation `sum(1..n+1) (\k. &k * x pow (n+1 - k))` using `SUM_CLAUSES_NUMSEG` to `sum(1..n) (\k. &k * x pow (n+1 - k)) + &((n+1)) * x pow (n+1 - (n+1))`.
  - Simplify using arithmetic equalities.
  - Use the inductive hypothesis to rewrite the term `x pow (n + 1) - (&n + &1) * x + &n`
  - Simplify using rules like `real_pow`, `REAL_MUL_RID`, and arithmetic properties (`REAL_MUL_ASSOC`, `REAL_ADD_LDISTRIB`).
  - The goal is further simplified by rewriting `REAL_OF_NUM_SUC` and `REAL_POW_ADD`.
  - The proof finishes using real arithmetic.

### Mathematical insight
This lemma relates a polynomial expression `x^(n+1) - (n+1) * x + n` to a summation involving powers of `x` and a quadratic factor `(x - 1)^2`. It can be viewed as a specific instance related to inequalities concerning arithmetic and geometric means.

### Dependencies
- `Library/products.ml`
- `SUM_CLAUSES_NUMSEG`
- `ARITH_EQ`
- `ADD_CLAUSES`
- `real_pow`
- `REAL_MUL_RID`
- `SUM_RMUL`
- `REAL_MUL_ASSOC`
- `REAL_ADD_LDISTRIB`
- `REAL_OF_NUM_SUC`
- `REAL_POW_ADD`
- `ARITH_RULE \`1 <= SUC n\``
- `ARITH_RULE \`k <= n ==> SUC n - k = SUC(n - k)\``
- `SUB_REFL`

### Porting notes (optional)
- The frequent use of real arithmetic tactics suggests that a proof assistant with good automation for real number reasoning would be beneficial.
- The need to rewrite using arithmetic rules may require using tactics that allow conditional rewriting or applying rules only when the condition is met.


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
For all natural numbers `n` and real numbers `x`, if `0 <= x`, then `0 <= x^(n+1) - (n+1) * x + n`.

### Informal sketch
The proof proceeds as follows:
- Strip the quantifiers and implication.
- Rewrite using `LEMMA_1`. This likely expands or simplifies an expression based on a previous lemma.
- Apply `REAL_LE_MUL`. This probably uses the fact that if `0 <= a` and `0 <= b` then `0 <= a*b`.
- Rewrite using `REAL_POW_2` and `REAL_LE_SQUARE`. This likely simplifies powers or introduces squares where appropriate, and uses the fact that `0 <= x^2` for any real number `x`.
- Apply `SUM_POS_LE_NUMSEG`. This likely proves the result by summing up the differences of consecutive powers of `x`.
- Apply simplification tactics using the assumptions in the context, with rewriting using `REAL_LE_MUL`, `REAL_POS`, and `REAL_POW_LE` to complete the proof.

### Mathematical insight
This lemma establishes a lower bound for the polynomial `x^(n+1) - (n+1)*x + n` when `x` is non-negative. It is likely used as an intermediate step in proving some other result related to inequalities or real analysis. The form of the polynomial suggests that the minimum value might be related to `x = 1`, where the polynomial evaluates to `0`.

### Dependencies
- `LEMMA_1`
- `REAL_LE_MUL`
- `REAL_POW_2`
- `REAL_LE_SQUARE`
- `SUM_POS_LE_NUMSEG`
- `REAL_POS`
- `REAL_POW_LE`


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
For all natural numbers `n` and functions `x` from natural numbers to real numbers, if `1 <= n` and for all `i`, if `1 <= i` and `i <= n + 1` implies `0 <= x i`, then `x(n + 1) * (sum(1..n) x / &n) pow n <= (sum(1..n+1) x / (&n + &1)) pow (n + 1)`.

### Informal sketch
The proof proceeds by induction-like reasoning.
- First, abbreviations `a = sum(1..n+1) x / (&n + &1)` and `b = sum(1..n) x / &n` are introduced.
- Then, the goal is rewritten using the equation `x(n + 1) = (&n + &1) * a - &n * b`. The proof then involves simplifying the expression using the definitions of `a` and `b`, and arithmetic simplification.
- It is then shown that `0 <= a` and `0 <= b`. This involves proving that the sums `sum(1..n+1) x` and `sum(1..n) x` are non-negative, which follows from the assumption that `x i >= 0` for all `i` in the range `1..n+1`.
- The proof proceeds by considering the case when `b = 0`. In this case, the inequality simplifies and can be proven directly since the terms are nonnegative.
- Finally, the case where `b` is not zero is handled by applying `LEMMA_2` with `n` and `a/b`. This step uses the fact that `0 < b`. It also uses real arithmetic and rewriting rules to simplify the inequality. The proof concludes by discharging the assumption `~(b = &0)`.

### Mathematical insight
This lemma represents a step towards proving that the geometric mean is less than or equal to the arithmetic mean in certain conditions. It manipulates sums and inequalities involving real numbers and powers. The proof uses simplification, variable substitution, and a case split based on whether a certain sum is zero. The lemma builds upon `LEMMA_2`, suggesting that it is part of a larger chain of lemmas culminating in the AM-GM inequality or a related result.

### Dependencies
- Theorems: `LEMMA_2`
- Definitions: `REAL_ARITH`, `REAL_FIELD`

### Porting notes (optional)
- The reification of sums and their manipulation rules are key dependency.
- `LEMMA_2` needs to be ported before porting `LEMMA_3`.
- The proof relies heavily on real arithmetic simplification, which may require tailored tactics in other proof assistants.


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
For all natural numbers `n`, and for all functions `a` from natural numbers to real numbers, if `n` is greater than or equal to 1, and for all `i`, if `i` is greater than or equal to 1 and `i` is less than or equal to `n`, then `a(i)` is greater than or equal to 0, then the product of `a(i)` for `i` from 1 to `n` is less than or equal to the `(sum of a(i) for i from 1 to n divided by n) raised to the power of n`.

### Informal sketch
The proof proceeds by induction on `n`.

*   **Base Case (n = 0):** After assuming `n = 0`, the goal simplifies using properties of `product` and `sum` over the range `1..0`, which are both empty. This results in `1 <= 0 /\ ... ==> 1 <= ...`, which is trivially true, since `1 <= 0` is false.

*   **Inductive Step:** Assume the theorem holds for `n`, and prove it for `n+1`. This involves showing that if `1 <= n+1` and all `a(i)` are non-negative for `i` between 1 and `n+1`, then `product(1..(n+1)) a <= (sum(1..(n+1)) a / &(n+1)) pow (n+1)`. The inductive hypothesis is applied, and the goal is transformed to compare `x(n + 1) * (sum(1..n) x / &n) pow n` with `(sum(1..(n+1)) x / &(n+1)) pow (n+1)`. Properties of real number arithmetic, including `REAL_LE_TRANS`, `REAL_MUL_SYM` and properties of powers are used to complete the proof. `LEMMA_3` which states that `&(1 + n) = &1 + &n` also plays a key role.

### Mathematical insight
This theorem states the Arithmetic Mean - Geometric Mean (AM-GM) inequality for real numbers. It is a fundamental inequality in mathematics with numerous applications in optimization, analysis, and number theory.

### Dependencies

*   Theorems: `ARITH`, `PRODUCT_CLAUSES_NUMSEG`, `ADD1`, `REAL_LE_TRANS`, `REAL_LE_RMUL`, `LE_REFL`, `LE_1`
*   Definitions: `product`, `sum`, `pow`.
*   Lemmas: `LEMMA_3` (likely stating `&(1 + n) = &1 + &n`), `GSYM REAL_OF_NUM_ADD`.
*   Tactics employ rules regarding sums and product over number segments: `ARITH_RULE i <= n ==> i <= n + 1`

### Porting notes (optional)
The `prove` function indicates extensive automation. The inductive step relies on real number arithmetic and properties of summation and product, which may require specific tactics or libraries depending on the target proof assistant. The reliance on automation and pre-proven arithmetic rules may make porting to proof assistants with different automation levels challenging.


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
For all natural numbers `n` and all functions `a` from natural numbers to real numbers, if `n` is greater than or equal to 1, and for all `i`, if `i` is between 1 and `n` (inclusive), then `a(i)` is non-negative, then the `n`-th root of the product of `a(i)` from `i = 1` to `n` is less than or equal to the sum of `a(i)` from `i = 1` to `n`, divided by `n`.

### Informal sketch
The proof proceeds by induction on `n`.
- Base case: `n = 1`. The goal simplifies to `root 1 a(1) <= sum(1..1) a / &1`, which simplifies to `a(1) <= a(1)`, which is true.
- Inductive step: Assume the theorem holds for `n`. We need to prove it for `SUC n`.
    - We start with the inequality we want to prove, use the transitivity of the real less-than-or-equal relation, and existentially quantify over `root(SUC n) ((sum(1..SUC n) a / &(SUC n)) pow (SUC n))`.
    - We then have to prove two inequalities. The first uses the inequality between the arithmetic and geometric means (`AGM`), the monotonicity of the `root` function (`ROOT_MONO_LE`), and the fact that a product of non-negative numbers is non-negative (`PRODUCT_POS_LE`). The second uses the fact that for positive x, `(x pow n) root n = x` (`POW_ROOT_POS`) and some inequalities and identities to show that `root(SUC n) ((sum(1..SUC n) a / &(SUC n)) pow (SUC n)) <= sum(1..SUC n) a / &(SUC n)`.

### Mathematical insight
The theorem states the inequality between the geometric and arithmetic means. Specifically, it states that for any list of `n` non-negative real numbers, the `n`-th root of their product is less than or equal to their average. This is a fundamental result in real analysis and is useful in various contexts such as optimization and probability theory.

### Dependencies
- `ARITH`
- `REAL_LE_TRANS`
- `ROOT_MONO_LE`
- `AGM`
- `PRODUCT_POS_LE`
- `IN_NUMSEG`
- `FINITE_NUMSEG`
- `REAL_EQ_IMP_LE`
- `POW_ROOT_POS`
- `REAL_LE_DIV`
- `REAL_POS`
- `SUM_POS_LE_NUMSEG`


---

