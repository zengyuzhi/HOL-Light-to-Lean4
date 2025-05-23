# bernoulli.ml

## Overview

Number of statements: 16

The `bernoulli.ml` file defines and explores properties of Bernoulli numbers and polynomials, as well as the sum of kth powers. It builds upon concepts from binomial theory, analysis, and transcendental functions, as indicated by its imports from `binomial.ml`, `analysis.ml`, and `transc.ml`. The file's content is focused on formalizing these mathematical concepts within the HOL Light system. Its definitions and theorems provide a foundation for further reasoning about Bernoulli numbers and related mathematical objects.

## SUM_DIFFS

### Name of formal statement
SUM_DIFFS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SUM_DIFFS = prove
 (`!a m n. m <= n + 1 ==> sum(m..n) (\i. a(i + 1) - a(i)) = a(n + 1) - a(m)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG] THENL
   [REWRITE_TAC[ARITH_RULE `m <= 0 + 1 <=> m = 0 \/ m = 1`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[ARITH; ADD_CLAUSES; REAL_SUB_REFL];
    SIMP_TAC[ARITH_RULE `m <= SUC n + 1 <=> m <= n + 1 \/ m = SUC n + 1`] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[ADD1] THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_REFL; ARITH_RULE `~((n + 1) + 1 <= n + 1)`] THEN
    MATCH_MP_TAC SUM_TRIV_NUMSEG THEN ARITH_TAC])
```

### Informal statement
For all functions `a` and integers `m` and `n`, if `m` is less than or equal to `n + 1`, then the sum from `m` to `n` of `a(i + 1) - a(i)` is equal to `a(n + 1) - a(m)`.

### Informal sketch
* The proof starts by applying `GEN_TAC` twice to introduce the variables `a`, `m`, and `n`.
* Then, it applies `INDUCT_TAC` to perform induction.
* The `REWRITE_TAC[SUM_CLAUSES_NUMSEG]` tactic is used to rewrite the sum using the `SUM_CLAUSES_NUMSEG` rule.
* The proof then proceeds by cases, using `REWRITE_TAC` and `SIMP_TAC` to simplify the expressions and `ASM_REWRITE_TAC` and `ASM_SIMP_TAC` to apply specific rules such as `ARITH`, `ADD_CLAUSES`, `REAL_SUB_REFL`, and `ADD1`.
* The `MATCH_MP_TAC SUM_TRIV_NUMSEG` tactic is used to apply the `SUM_TRIV_NUMSEG` rule, and finally, `ARITH_TAC` is used to perform arithmetic reasoning.

### Mathematical insight
This theorem provides a way to simplify sums of differences of a function `a` over a range `[m, n]`. It states that the sum of the differences `a(i + 1) - a(i)` is equal to the difference of the function values at the endpoints, `a(n + 1) - a(m)`. This is a fundamental property of sums and differences, and it has numerous applications in mathematics, particularly in calculus and analysis.

### Dependencies
* Theorems:
	+ `SUM_CLAUSES_NUMSEG`
	+ `SUM_TRIV_NUMSEG`
* Definitions:
	+ `sum`
	+ `a` (a function)
* Inductive rules:
	+ `INDUCT_TAC`
* Tactics:
	+ `GEN_TAC`
	+ `REWRITE_TAC`
	+ `SIMP_TAC`
	+ `ASM_REWRITE_TAC`
	+ `ASM_SIMP_TAC`
	+ `MATCH_MP_TAC`
	+ `ARITH_TAC` 

### Porting notes
When porting this theorem to other proof assistants, special attention should be paid to the handling of sums, differences, and arithmetic reasoning. The `SUM_CLAUSES_NUMSEG` and `SUM_TRIV_NUMSEG` rules may need to be reformulated or replaced with equivalent rules in the target system. Additionally, the `INDUCT_TAC` and `ARITH_TAC` tactics may need to be replaced with equivalent tactics or strategies in the target system.

---

## DIFF_SUM

### Name of formal statement
DIFF_SUM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DIFF_SUM = prove
 (`!f f' a b.
        (!k. a <= k /\ k <= b ==> ((\x. f x k) diffl f'(k)) x)
        ==> ((\x. sum(a..b) (f x)) diffl (sum(a..b) f')) x`,
  REPLICATE_TAC 3 GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[ARITH; DIFF_CONST; SUM_TRIV_NUMSEG;
               ARITH_RULE `~(a <= SUC b) ==> b < a`] THEN
  DISCH_TAC THEN MATCH_MP_TAC DIFF_ADD THEN
  ASM_SIMP_TAC[LE_REFL; ARITH_RULE `k <= b ==> k <= SUC b`])
```

### Informal statement
For all functions `f` and `f'` and for all numbers `a` and `b`, if for every `k` such that `a` is less than or equal to `k` and `k` is less than or equal to `b`, the function `f(x, k)` is differentiable at `x` and equals `f'(k)` at `x`, then the function that sums `f(x, k)` from `a` to `b` is differentiable at `x` and equals the sum of `f'(k)` from `a` to `b` at `x`.

### Informal sketch
* The proof starts by generalizing the statement for `f`, `f'`, `a`, and `b` using `GEN_TAC`.
* It then proceeds by induction, as indicated by `INDUCT_TAC`, likely on the interval `[a, b]`.
* The `REWRITE_TAC[SUM_CLAUSES_NUMSEG]` step suggests rewriting the sum using properties of summation over a numeric segment, breaking down the sum into simpler cases.
* The use of `COND_CASES_TAC` implies considering different cases based on conditions, possibly related to the bounds `a` and `b` or properties of `f` and `f'`.
* Simplifications are then applied using `ASM_SIMP_TAC` with various theorems (`ARITH`, `DIFF_CONST`, `SUM_TRIV_NUMSEG`, and specific arithmetic rules) to reduce the expression and potentially discharge assumptions.
* The application of `MATCH_MP_TAC DIFF_ADD` indicates using a rule or theorem about differentiability of sums (`DIFF_ADD`) to conclude the differentiability of the sum of `f(x)` over the interval.
* Final simplifications with `ASM_SIMP_TAC` and specific arithmetic rules aim to establish the desired equality.

### Mathematical insight
This theorem is important because it establishes a condition under which the sum of a function over an interval is differentiable, relating the differentiability of the sum to the differentiability of the original function. This is crucial in calculus for understanding how differentiation applies to sums and integrals of functions, particularly in the context of optimization, physics, and other applications where rates of change are significant.

### Dependencies
* Theorems:
  - `DIFF_ADD`
  - `ARITH`
  - `DIFF_CONST`
  - `SUM_TRIV_NUMSEG`
  - `LE_REFL`
* Definitions:
  - `diffl` (differentiable at a point)
  - `sum` (summation over an interval)
* Inductive rules or properties:
  - Possibly `SUM_CLAUSES_NUMSEG` (properties of summation over numeric segments)

### Porting notes
When translating this into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles:
- Differentiability and its relation to summation
- Induction and case analysis over numeric intervals
- Arithmetic properties and their application in simplification tactics
- The representation of functions `f` and `f'` and their properties
- The specific rules or theorems like `DIFF_ADD` and their equivalents in the target system.

---

## bernoulli

### Name of formal statement
bernoulli

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let bernoulli = define
 `(bernoulli 0 = &1) /\
  (!n. bernoulli(SUC n) =
       --sum(0..n) (\j. &(binom(n + 2,j)) * bernoulli j) / (&n + &2))`
```

### Informal statement
The `bernoulli` function is defined such that `bernoulli 0` equals 1, and for all natural numbers `n`, `bernoulli (SUC n)` is defined as the sum from 0 to `n` of the product of the binomial coefficient `(n + 2, j)` and `bernoulli j`, divided by `n + 2`.

### Informal sketch
* The definition of `bernoulli` is recursive, starting with a base case for `bernoulli 0`.
* For any `n`, the definition of `bernoulli (SUC n)` involves a summation over all `j` from 0 to `n`.
* Within this summation, each term is the product of the binomial coefficient `binom(n + 2, j)` and the value of `bernoulli j`.
* The result of the summation is then divided by `n + 2`.
* The `SUC` function is used to represent the successor of a number, which is a common way to denote the next natural number in a sequence.

### Mathematical insight
The `bernoulli` numbers are a sequence of rational numbers that arise in number theory, and they are defined recursively as shown. This definition captures the essence of how each Bernoulli number depends on the previous ones, through a combination of binomial coefficients and a recursive formula. The Bernoulli numbers have numerous applications in mathematics, including the study of power sums, the Euler-Maclaurin formula, and more.

### Dependencies
* `binom` 
* `SUC`

### Porting notes
When translating this definition into another proof assistant, special care should be taken to preserve the recursive nature of the definition and to correctly implement the summation and division operations. The handling of binders and the representation of natural numbers may also require attention, depending on the target system. Additionally, the `binom` function and the `SUC` function should be defined or imported appropriately in the target system.

---

## BERNOULLI

### Name of formal statement
BERNOULLI

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let BERNOULLI = prove
 (`!n. sum(0..n) (\j. &(binom(n + 1,j)) * bernoulli j) =
       if n = 0 then &1 else &0`,
  INDUCT_TAC THEN
  REWRITE_TAC[bernoulli; SUM_CLAUSES_NUMSEG; GSYM ADD1; ADD_CLAUSES; binom;
              REAL_MUL_LID; LE_0; NOT_SUC] THEN
  SIMP_TAC[BINOM_LT; ARITH_RULE `n < SUC n`; BINOM_REFL; REAL_ADD_LID] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[ARITH_RULE `SUC(SUC n) = n + 2`] THEN
  MATCH_MP_TAC(REAL_FIELD `x = &n + &2 ==> s + x * --s / (&n + &2) = &0`) THEN
  REWRITE_TAC[ADD1; BINOM_TOP_STEP_REAL; ARITH_RULE `~(n = n + 1)`] THEN
  REWRITE_TAC[BINOM_REFL] THEN REAL_ARITH_TAC)
```

### Informal statement
For all natural numbers `n`, the sum from `0` to `n` of the product of `binom(n + 1, j)` and `bernoulli j` is equal to `1` if `n` is `0`, and `0` otherwise.

### Informal sketch
* The proof proceeds by induction on `n`.
* The base case is straightforward, and for the inductive step, several simplifications and rewrites are applied to transform the sum into a more manageable form.
* Key steps involve applying properties of binomial coefficients (`binom`), Bernoulli numbers (`bernoulli`), and arithmetic properties, including `REAL_MUL_LID`, `LE_0`, and `NOT_SUC`.
* The `MATCH_MP_TAC` tactic is used with a specific rule from `REAL_FIELD` to further simplify the expression.
* The proof concludes with additional rewrites and simplifications, including `BINOM_REFL` and `REAL_ARITH_TAC`, to reach the desired equality.

### Mathematical insight
This theorem provides a recurrence relation involving Bernoulli numbers and binomial coefficients, which is fundamental in number theory. The relation shows how the sum of products of these coefficients and numbers over a range relates to a simple condition on `n`. This kind of relation is crucial for understanding properties and behaviors of Bernoulli numbers and their applications in mathematics.

### Dependencies
* Theorems:
  + `binom`
  + `bernoulli`
  + `REAL_FIELD`
  + `BINOM_LT`
  + `BINOM_REFL`
* Definitions:
  + `SUM_CLAUSES_NUMSEG`
  + `GSYM`
  + `ADD1`
  + `ADD_CLAUSES`
  + `REAL_MUL_LID`
  + `LE_0`
  + `NOT_SUC`
  + `REAL_OF_NUM_ADD`
  + `ARITH_RULE`
* Inductive rules: None explicitly mentioned, but the proof uses induction (`INDUCT_TAC`).

### Porting notes
When translating this theorem into another proof assistant, pay close attention to the handling of arithmetic properties, especially those involving `REAL_FIELD`, as different systems may have different mechanisms for dealing with real arithmetic. Additionally, the `MATCH_MP_TAC` step might require careful handling, as the specific rule application might need to be adapted to the target system's tactic language.

---

## bernpoly

### Name of formal statement
bernpoly

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let bernpoly = new_definition
 `bernpoly n x = sum(0..n) (\k. &(binom(n,k)) * bernoulli k * x pow (n - k))`;;
```

### Informal statement
The `bernpoly` function is defined as the sum from 0 to `n` of the terms `&(binom(n,k)) * bernoulli k * x pow (n - k)`, where `k` ranges from 0 to `n`. This definition involves the binomial coefficient `binom(n,k)`, the `bernoulli` numbers, and the power function `pow`.

### Informal sketch
* The definition of `bernpoly` involves a summation over a range of values, indicating a construction that aggregates terms based on a specific pattern.
* The `binom(n,k)` term suggests the use of combinatorial principles, specifically binomial coefficients, which are fundamental in counting and probability theory.
* The presence of `bernoulli k` indicates that the definition is related to Bernoulli numbers, which are a sequence of rational numbers that arise in number theory and combinatorics.
* The term `x pow (n - k)` implies a dependence on the variable `x` and an exponentiation operation, which is common in polynomial constructions.
* The use of `&( )` around `binom(n,k)` suggests a specific type or context for the binomial coefficient that may be relevant to the proof assistant's type system.

### Mathematical insight
The `bernpoly` definition is related to the Bernoulli polynomials, which are a sequence of polynomials that appear in various areas of mathematics, including number theory, combinatorics, and analysis. These polynomials are closely related to the Bernoulli numbers and have applications in approximation theory, numerical analysis, and other fields. The definition provided here constructs these polynomials using a summation formula that involves binomial coefficients and powers of `x`, reflecting their combinatorial and algebraic structure.

### Dependencies
* `binom`
* `bernoulli`
* `sum`
* `pow`

### Porting notes
When translating this definition into another proof assistant, care should be taken to ensure that the binomial coefficient `binom(n,k)`, Bernoulli numbers `bernoulli k`, and power function `pow` are correctly defined and used. Additionally, the summation `sum(0..n)` and the lambda abstraction `(\k. ...)` should be properly handled, as they may have different representations in other systems. The use of `&( )` around `binom(n,k)` may also require special attention due to potential differences in type systems between proof assistants.

---

## DIFF_BERNPOLY

### Name of formal statement
DIFF_BERNPOLY

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DIFF_BERNPOLY = prove
 (`!n x. ((bernpoly (SUC n)) diffl (&(SUC n) * bernpoly n x)) x`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[bernpoly; SUM_CLAUSES_NUMSEG; LE_0] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ADD_RID] THEN
  MATCH_MP_TAC DIFF_ADD THEN REWRITE_TAC[SUB_REFL; real_pow; DIFF_CONST] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC DIFF_SUM THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[ADD1; BINOM_TOP_STEP_REAL] THEN
  DIFF_TAC THEN ASM_SIMP_TAC[ARITH_RULE `k <= n ==> ~(k = n + 1)`] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
  ASM_SIMP_TAC[ARITH_RULE `k <= n ==> (n + 1) - k - 1 = n - k`] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `k <= n ==> k <= n + 1`] THEN
  UNDISCH_TAC `k <= n:num` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_LE] THEN
  ABBREV_TAC `z = x pow (n - k)` THEN CONV_TAC REAL_FIELD)
```

### Informal statement
For all natural numbers `n` and all real numbers `x`, the derivative of the `(n+1)`-th Bernoulli polynomial at `x` is equal to `(n+1)` times the `n`-th Bernoulli polynomial at `x`.

### Informal sketch
* The proof starts by applying `GEN_TAC` to introduce the variables `n` and `x`.
* It then uses `GEN_REWRITE_TAC` with `GSYM ETA_AX` to transform the goal, followed by rewriting with `bernpoly`, `SUM_CLAUSES_NUMSEG`, and `LE_0`.
* The `MATCH_MP_TAC DIFF_ADD` tactic is used to apply the sum rule for differentiation, and `REWRITE_TAC` is used with `SUB_REFL`, `real_pow`, and `DIFF_CONST` to simplify.
* Further rewriting and simplification are done using `GSYM SUM_LMUL`, `MATCH_MP_TAC DIFF_SUM`, and `REPEAT STRIP_TAC`.
* The proof involves case analysis and simplification using `ASM_SIMP_TAC` with various arithmetic rules, and finally, `ABBREV_TAC` is used to introduce an abbreviation for `x pow (n - k)`.

### Mathematical insight
This theorem provides a key derivative recurrence for Bernoulli polynomials, which are important in number theory and analysis. The recurrence relation allows for the computation of higher-order Bernoulli polynomials and their derivatives, facilitating various applications in mathematics and computer science.

### Dependencies
* `bernpoly`
* `SUM_CLAUSES_NUMSEG`
* `LE_0`
* `REAL_ADD_RID`
* `DIFF_ADD`
* `SUB_REFL`
* `real_pow`
* `DIFF_CONST`
* `SUM_LMUL`
* `DIFF_SUM`
* `ADD1`
* `BINOM_TOP_STEP_REAL`
* `REAL_MUL_LZERO`
* `REAL_ADD_LID`
* `REAL_OF_NUM_SUB`
* `REAL_OF_NUM_ADD`
* `REAL_OF_NUM_LE`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of binders, arithmetic rules, and the `REAL_FIELD` convolution. In particular, ensure that the target system correctly handles the derivative of polynomials and the properties of Bernoulli polynomials. Additionally, be mindful of the differences in tactic languages and the specific rewriting and simplification mechanisms available in the target system.

---

## INTEGRALS_EQ

### Name of formal statement
INTEGRALS_EQ

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let INTEGRALS_EQ = prove
 (`!f g. (!x. ((\x. f(x) - g(x)) diffl &0) x) /\ f(&0) = g(&0)
         ==> !x. f(x) = g(x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`\x:real. f(x) - g(x)`; `x:real`; `&0`] DIFF_ISCONST_ALL) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC)
```

### Informal statement
For all functions f and g, if for all x, the function that maps x to f(x) - g(x) is differentiable at 0 and f(0) equals g(0), then for all x, f(x) equals g(x).

### Informal sketch
* The proof starts by assuming the antecedent of the implication: for all x, the function `\x. f(x) - g(x)` is differentiable at 0, and f(0) = g(0).
* It then applies the `DIFF_ISCONST_ALL` theorem to the function `\x. f(x) - g(x)`, `x:real`, and `&0`, which implies that `\x. f(x) - g(x)` is constant.
* The proof then uses `ASM_REWRITE_TAC` to simplify the expression and `REAL_ARITH_TAC` to perform real arithmetic, ultimately showing that for all x, f(x) = g(x).

### Mathematical insight
This theorem is important because it shows that if two functions have the same value at 0 and their difference is differentiable at 0, then the two functions are equal everywhere. This is a key result in real analysis, highlighting the rigidity of functions under certain conditions.

### Dependencies
* `DIFF_ISCONST_ALL`
* `REAL_ARITH_TAC`

### Porting notes
When porting this theorem to another proof assistant, pay attention to how differentiability and real arithmetic are handled. In particular, the `DIFF_ISCONST_ALL` theorem and `REAL_ARITH_TAC` tactic may need to be replaced with equivalent constructs in the target system. Additionally, the use of `REPEAT STRIP_TAC` and `MP_TAC` may need to be adjusted depending on the proof assistant's tactic language.

---

## RECURRENCE_BERNPOLY

### Name of formal statement
RECURRENCE_BERNPOLY

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let RECURRENCE_BERNPOLY = prove
 (`!n x. bernpoly n (x + &1) - bernpoly n x = &n * x pow (n - 1)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[bernpoly; SUM_SING_NUMSEG; REAL_SUB_REFL; SUB_REFL;
                real_pow; REAL_MUL_LZERO];
    ALL_TAC] THEN
  MATCH_MP_TAC INTEGRALS_EQ THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real` THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN
    ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
    DISCH_THEN(MP_TAC o AP_TERM `(*) (&(SUC n))`) THEN
    REWRITE_TAC[REAL_MUL_RZERO] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_SUB_LDISTRIB] THEN
    REPEAT(MATCH_MP_TAC DIFF_SUB THEN CONJ_TAC) THEN
    SIMP_TAC[SUC_SUB1; DIFF_CMUL; DIFF_POW; DIFF_BERNPOLY; ETA_AX] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC DIFF_CHAIN THEN REWRITE_TAC[DIFF_BERNPOLY] THEN
    DIFF_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[bernpoly; GSYM SUM_SUB_NUMSEG] THEN
  REWRITE_TAC[REAL_ADD_LID; REAL_POW_ONE; GSYM REAL_SUB_LDISTRIB] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0; SUB_REFL; real_pow] THEN
  REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_ADD_RID] THEN
  SIMP_TAC[ARITH_RULE `i <= n ==> SUC n - i = SUC(n - i)`] THEN
  REWRITE_TAC[real_pow; REAL_MUL_LZERO; REAL_SUB_RZERO; REAL_MUL_RID] THEN
  REWRITE_TAC[BERNOULLI; ADD1] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH; real_pow; REAL_MUL_LID] THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0] THEN
  ASM_REWRITE_TAC[ADD_SUB])
```

### Informal statement
For all natural numbers `n` and real numbers `x`, the difference between the `n`-th Bernoulli polynomial evaluated at `x + 1` and `x` is equal to `n` times `x` raised to the power of `n - 1`.

### Informal sketch
* The proof proceeds by induction on `n`.
* The base case involves simplifying the expression for the difference of the Bernoulli polynomials using various properties of real numbers and polynomials.
* The inductive step involves assuming the result for `n` and proving it for `n + 1` using properties of derivatives and the `BERNOULLI` definition.
* Key steps include using `MATCH_MP_TAC INTEGRALS_EQ` to establish an equality between integrals, and `DIFF_TAC` to compute derivatives.
* The proof also relies on various simplification and rewriting steps using `REWRITE_TAC` and `SIMP_TAC` to manipulate the expressions.

### Mathematical insight
This theorem provides a recurrence relation for the Bernoulli polynomials, which are important in number theory and algebra. The relation shows how the difference between the polynomial evaluated at successive points relates to the polynomial's degree and the point itself. This insight is crucial for understanding properties and behaviors of Bernoulli polynomials.

### Dependencies
* `bernpoly`
* `SUM_SING_NUMSEG`
* `REAL_SUB_REFL`
* `SUB_REFL`
* `real_pow`
* `REAL_MUL_LZERO`
* `INTEGRALS_EQ`
* `BERNOULLI`
* `ADD1`
* `DIFF_BERNPOLY`
* `ETA_AX`
* `DIFF_CMUL`
* `DIFF_POW`
* `DIFF_SUB`
* `REAL_ENTIRE`
* `REAL_POW_EQ_0`

### Porting notes
When translating this theorem into other proof assistants, pay special attention to the handling of binders, especially in the inductive step where the assumption for `n` is used to prove the result for `n + 1`. Additionally, the use of `MATCH_MP_TAC` and `REWRITE_TAC` may need to be adapted to the target system's tactic language and rewriting mechanisms.

---

## SUM_OF_POWERS

### Name of formal statement
SUM_OF_POWERS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SUM_OF_POWERS = prove
 (`!n. sum(0..n) (\k. &k pow m) =
        (bernpoly(SUC m) (&n + &1) - bernpoly(SUC m) (&0)) / (&m + &1)`,
  GEN_TAC THEN ASM_SIMP_TAC[REAL_EQ_RDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
  ONCE_REWRITE_TAC[GSYM REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `sum(0..n) (\i. bernpoly (SUC m) (&(i + 1)) - bernpoly (SUC m) (&i))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[RECURRENCE_BERNPOLY; GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC; SUC_SUB1];
    SIMP_TAC[SUM_DIFFS; LE_0] THEN REWRITE_TAC[REAL_OF_NUM_ADD]])
```

### Informal statement
For all natural numbers `n`, the sum from `0` to `n` of `k` raised to the power of `m` equals `(bernpoly(SUC m) (n + 1) - bernpoly(SUC m) (0)) / (m + 1)`, where `bernpoly` denotes the Bernoulli polynomial and `SUC` denotes the successor function.

### Informal sketch
* The proof starts by applying generalization (`GEN_TAC`) to the statement, followed by simplification using `ASM_SIMP_TAC` with `REAL_EQ_RDIV_EQ` and `REAL_ARITH` to handle the division and arithmetic properties.
* It then applies `ONCE_REWRITE_TAC` with `GSYM REAL_MUL_SYM` to rearrange the multiplication, and `REWRITE_TAC` with `GSYM SUM_LMUL` to transform the summation.
* The proof proceeds by applying `MATCH_MP_TAC` with `EQ_TRANS` to establish an equality through a transient expression, and `EXISTS_TAC` to introduce a summation involving Bernoulli polynomials.
* The proof splits into two branches using `CONJ_TAC`, each handling different aspects of the equality:
  + The first branch involves rewriting using `RECURRENCE_BERNPOLY`, `GSYM REAL_OF_NUM_ADD`, `GSYM REAL_OF_NUM_SUC`, and `SUC_SUB1` to manipulate the Bernoulli polynomials and arithmetic expressions.
  + The second branch simplifies using `SIMP_TAC` with `SUM_DIFFS` and `LE_0`, followed by a rewrite using `REAL_OF_NUM_ADD` to finalize the arithmetic manipulation.

### Mathematical insight
This theorem relates the sum of powers of natural numbers to an expression involving Bernoulli polynomials. The key idea is to leverage properties of Bernoulli polynomials, such as their recurrence relation (`RECURRENCE_BERNPOLY`), to transform the summation into a more manageable form. The use of `EQ_TRANS` and introducing a transient summation expression allows for a step-by-step manipulation of the original statement into the final form, showcasing a strategic application of mathematical properties to simplify complex expressions.

### Dependencies
- Theorems:
  + `REAL_EQ_RDIV_EQ`
  + `REAL_ARITH`
  + `EQ_TRANS`
  + `SUM_LMUL`
  + `RECURRENCE_BERNPOLY`
  + `SUM_DIFFS`
- Definitions:
  + `bernpoly`
  + `SUC`
- Tactics and functions:
  + `GEN_TAC`
  + `ASM_SIMP_TAC`
  + `ONCE_REWRITE_TAC`
  + `REWRITE_TAC`
  + `MATCH_MP_TAC`
  + `EXISTS_TAC`
  + `CONJ_TAC`
  + `SIMP_TAC`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to:
- The handling of `bernpoly` and its properties, as different systems may have varying levels of support for Bernoulli polynomials.
- The use of `EQ_TRANS` and transient expressions, which might require adjustments based on the target system's support for equality reasoning and existential quantification.
- The arithmetic and summation properties, which could be represented differently across systems, affecting the applicability of tactics like `REAL_ARITH` and `SUM_LMUL`.

---

## SUM_CONV

### Name of formal statement
SUM_CONV

### Type of the formal statement
Theorem/Conversion

### Formal Content
```ocaml
let SUM_CONV =
  let pth = prove
   (`sum(0..0) f = f 0 /\ sum(0..SUC n) f = sum(0..n) f + f(SUC n)`,
    SIMP_TAC[SUM_CLAUSES_NUMSEG; LE_0]) in
  let econv_0 = GEN_REWRITE_CONV I [CONJUNCT1 pth]
  and econv_1 = GEN_REWRITE_CONV I [CONJUNCT2 pth] in
  let rec sconv tm =
    (econv_0 ORELSEC
     (LAND_CONV(RAND_CONV num_CONV) THENC econv_1 THENC
      COMB2_CONV (RAND_CONV sconv) (RAND_CONV NUM_SUC_CONV))) tm in
  sconv;;
```

### Informal statement
The `SUM_CONV` conversion defines a theorem that proves two properties of summation. Firstly, it states that the sum of a function `f` from `0` to `0` is equal to `f(0)`. Secondly, it states that the sum of `f` from `0` to `SUC(n)` (the successor of `n`) is equal to the sum of `f` from `0` to `n` plus `f(SUC(n))`. This conversion is defined recursively, applying these properties to simplify expressions involving summations.

### Informal sketch
* The proof starts by proving a base case and an inductive step for the summation properties using `SIMP_TAC` with `SUM_CLAUSES_NUMSEG` and `LE_0`.
* It then defines two conversion rules, `econv_0` and `econv_1`, based on the first and second conjuncts of the proven theorem, respectively.
* The recursive function `sconv` applies these conversions to terms, first trying `econv_0`, and if that fails, applying a combination of conversions involving `num_CONV`, `econv_1`, `sconv` itself (for recursive application), and `NUM_SUC_CONV` to handle the successor case.
* This process allows for the simplification of summation expressions by iteratively applying the base and inductive cases.

### Mathematical insight
The `SUM_CONV` conversion is crucial for simplifying and reasoning about summations in formal proofs. It encapsulates fundamental properties of summation, enabling the automation of proofs involving sums by recursively breaking them down into simpler cases. This conversion is essential in various mathematical developments, particularly in combinatorics, analysis, and algebra, where summations are ubiquitous.

### Dependencies
* Theorems:
  + `SUM_CLAUSES_NUMSEG`
  + `LE_0`
* Definitions:
  + `sum`
  + `SUC`
  + `num_CONV`
  + `NUM_SUC_CONV`

### Porting notes
When translating `SUM_CONV` into another proof assistant, special attention should be given to how each system handles recursive functions, conversions, and the application of theorems as rewrite rules. The porting process may require adjustments to match the target system's syntax and built-in support for automation and recursion. Additionally, the handling of binders and the specifics of how `SUC` and `num_CONV` are defined and used will need careful consideration to ensure the conversion works as intended in the new system.

---

## BINOM_CONV

### Name of formal statement
BINOM_CONV

### Type of the formal statement
Theorem/Conversion Rule

### Formal Content
```ocaml
let BINOM_CONV =
  let pth = prove
   (`a * b * x = FACT c ==> x = (FACT c) DIV (a * b)`,
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN CONJ_TAC THENL
     [POP_ASSUM MP_TAC THEN ARITH_TAC;
      POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
      SIMP_TAC[LT_NZ; MULT_ASSOC; MULT_CLAUSES] THEN
      MESON_TAC[LT_NZ; FACT_LT]]) in
  let match_pth = MATCH_MP pth
  and binom_tm = `binom` in
  fun tm ->
    let bop,lr = dest_comb tm in
    if bop <> binom_tm then failwith "BINOM_CONV" else
    let l,r = dest_pair lr in
    let n = dest_numeral l and k = dest_numeral r in
    if n </ k then
      let th = SPECL [l;r] BINOM_LT in
      MP th (EQT_ELIM(NUM_LT_CONV(lhand(concl th))))
    else
      let d = n -/ k in
      let th1 = match_pth(SPECL [mk_numeral d; r] BINOM_FACT) in
      CONV_RULE NUM_REDUCE_CONV th1
```

### Informal statement
The `BINOM_CONV` conversion rule is defined for terms of the form `binom(n, k)`, where `n` and `k` are numerals. It applies to equations where the left-hand side is a product of `a`, `b`, and `x`, and the right-hand side is `FACT(c)`, concluding that `x` equals `(FACT(c)) DIV (a * b)`. The rule handles cases where `n` is less than `k` by applying `BINOM_LT` and where `n` is not less than `k` by applying `BINOM_FACT` and performing necessary arithmetic manipulations.

### Informal sketch
* The proof starts by proving a lemma `pth` that if `a * b * x = FACT(c)`, then `x = (FACT(c)) DIV (a * b)`. This involves using `REPEAT STRIP_TAC`, `CONV_TAC SYM_CONV`, `MATCH_MP_TAC DIV_UNIQ`, and other tactics to establish this relationship.
* It then defines `match_pth` as `MATCH_MP pth` and checks if the input term `tm` is of the form `binom(n, k)`.
* If `n < k`, it applies `BINOM_LT` with `n` and `k` as arguments and uses `EQT_ELIM` with `NUM_LT_CONV` to derive the conclusion.
* If `n` is not less than `k`, it calculates `d = n - k`, applies `BINOM_FACT` with `d` and `k` as arguments, and then applies `CONV_RULE NUM_REDUCE_CONV` to simplify the result.

### Mathematical insight
The `BINOM_CONV` rule is crucial for simplifying expressions involving binomial coefficients by leveraging properties of factorials and arithmetic. It plays a significant role in proofs involving combinatorial identities and algebraic manipulations, especially when dealing with expressions that can be simplified using properties of factorials and divisibility.

### Dependencies
#### Theorems
- `DIV_UNIQ`
- `BINOM_LT`
- `BINOM_FACT`
- `CONTRAPOS_THM`
- `LT_NZ`
- `FACT_LT`
#### Definitions
- `binom`
- `FACT`
#### Tactics and Functions
- `REPEAT STRIP_TAC`
- `CONV_TAC SYM_CONV`
- `MATCH_MP_TAC`
- `EXISTS_TAC`
- `CONJ_TAC`
- `POP_ASSUM MP_TAC`
- `ARITH_TAC`
- `ONCE_REWRITE_TAC`
- `GSYM`
- `SIMP_TAC`
- `MESON_TAC`
- `EQT_ELIM`
- `NUM_LT_CONV`
- `CONV_RULE`
- `NUM_REDUCE_CONV`

---

## BERNOULLIS

### Name of formal statement
BERNOULLIS

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let BERNOULLIS =
  let th_0,th_1 = CONJ_PAIR bernoulli
  and b_tm = `bernoulli` in
  let conv_1 = GEN_REWRITE_CONV I [th_1] in
  let rec bconv n =
    if n <= 0 then [th_0] else
    let bths = bconv (n - 1)
    and tm = mk_comb(b_tm,mk_small_numeral n) in
    (RAND_CONV num_CONV THENC conv_1 THENC
     LAND_CONV(RAND_CONV SUM_CONV) THENC
     ONCE_DEPTH_CONV BETA_CONV THENC
     DEPTH_CONV(NUM_RED_CONV ORELSEC BINOM_CONV) THENC
     GEN_REWRITE_CONV ONCE_DEPTH_CONV bths THENC
     REAL_RAT_REDUCE_CONV) tm :: bths in
  bconv;;
```

### Informal statement
The definition `BERNOULLIS` is a recursive function `bconv` that takes an integer `n` and generates a list of theorems related to the `bernoulli` function. It starts with a base case when `n` is less than or equal to 0, returning a list containing `th_0`. For positive `n`, it recursively generates theorems for `n-1`, constructs a term `tm` by applying `bernoulli` to `n`, and then applies a series of conversions to `tm` using various HOL Light tactics (`RAND_CONV`, `LAND_CONV`, `ONCE_DEPTH_CONV`, `DEPTH_CONV`, `GEN_REWRITE_CONV`, and `REAL_RAT_REDUCE_CONV`), before prepending the result to the list of theorems for `n-1`.

### Informal sketch
* The definition begins by splitting the `bernoulli` theorem into two parts, `th_0` and `th_1`, using `CONJ_PAIR`.
* It then defines a conversion `conv_1` based on `th_1` using `GEN_REWRITE_CONV`.
* The recursive function `bconv` takes an integer `n` and:
  + For `n <= 0`, returns a list containing `th_0`.
  + For `n > 0`, recursively calls itself with `n-1` to get a list of theorems `bths`.
  + Constructs a term `tm` by applying `bernoulli` to `n`.
  + Applies a series of conversions to `tm`:
    - `RAND_CONV num_CONV` for numerical conversion
    - `LAND_CONV(RAND_CONV SUM_CONV)` for handling summations
    - `ONCE_DEPTH_CONV BETA_CONV` for beta reduction
    - `DEPTH_CONV(NUM_RED_CONV ORELSEC BINOM_CONV)` for numerical reduction and binomial expansion
    - `GEN_REWRITE_CONV ONCE_DEPTH_CONV bths` for rewriting using previously derived theorems
    - `REAL_RAT_REDUCE_CONV` for final simplification
  + Prepends the result of these conversions to the list of theorems `bths` for `n-1`.

### Mathematical insight
The `BERNOULLIS` definition is a constructive approach to generating a sequence of theorems related to the Bernoulli numbers, which are crucial in number theory. The recursive nature of `bconv` allows for the systematic derivation of properties and relationships involving these numbers, leveraging various mathematical transformations and simplifications provided by the HOL Light tactics. This definition showcases a structured method for exploring and proving statements about the Bernoulli numbers, which are important in many areas of mathematics, including combinatorics and analysis.

### Dependencies
* `bernoulli`
* `CONJ_PAIR`
* `GEN_REWRITE_CONV`
* `RAND_CONV`
* `LAND_CONV`
* `ONCE_DEPTH_CONV`
* `BETA_CONV`
* `DEPTH_CONV`
* `NUM_RED_CONV`
* `BINOM_CONV`
* `REAL_RAT_REDUCE_CONV`

---

## BERNOULLI_CONV

### Name of formal statement
BERNOULLI_CONV

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let BERNOULLI_CONV =
  let b_tm = `bernoulli` in
  fun tm -> let op,n = dest_comb tm in
            if op <> b_tm || not(is_numeral n) then failwith "BERNOULLI_CONV"
            else hd(BERNOULLIS(dest_small_numeral n))
```

### Informal statement
BERNOULLI_CONV is a conversion function that takes a term `tm` as input. It first checks if `tm` is an application of the `bernoulli` operator to a numeral `n`. If this condition is met and `n` is indeed a numeral, it returns the first element of the list `BERNOULLIS` applied to the small numeral `n`. If `tm` does not match this pattern or if `n` is not a numeral, it raises an exception with the message "BERNOULLI_CONV".

### Informal sketch
* The function `BERNOULLI_CONV` is defined to take a term `tm` and attempt to deconstruct it into an operator `op` and an operand `n` using `dest_comb`.
* It checks if `op` is the `bernoulli` operator and if `n` is a numeral using `is_numeral`.
* If both conditions are met, it applies `dest_small_numeral` to `n` and uses the result as an argument to `BERNOULLIS`, returning the head of the resulting list.
* If the input term does not match the expected pattern of `bernoulli` applied to a numeral, it fails with an exception.

### Mathematical insight
The `BERNOULLI_CONV` function appears to be part of a mechanism for handling Bernoulli numbers, which are a sequence of rational numbers that arise in number theory. The function's purpose is to convert a term representing a Bernoulli number into a specific form, likely for further manipulation or proof. The use of `BERNOULLIS` suggests a predefined list or sequence of Bernoulli numbers, and `dest_small_numeral` implies a way to extract or manipulate small numerals, which are likely used as indices into this sequence.

### Dependencies
* `bernoulli`
* `BERNOULLIS`
* `dest_comb`
* `is_numeral`
* `dest_small_numeral`

### Porting notes
When translating `BERNOULLI_CONV` into another proof assistant, special attention should be paid to how that system handles pattern matching on terms, extraction of numerals, and exception handling. The `BERNOULLIS` sequence and the `bernoulli` operator will also need to be defined or imported appropriately. Additionally, the equivalent of `dest_comb`, `is_numeral`, and `dest_small_numeral` functions will need to be identified or implemented in the target system.

---

## BERNPOLY_CONV

### Name of formal statement
BERNPOLY_CONV

### Type of the formal statement
Theorem/Conversion

### Formal Content
```ocaml
let BERNPOLY_CONV =
  let conv_1 =
    REWR_CONV bernpoly THENC SUM_CONV THENC
    TOP_DEPTH_CONV BETA_CONV THENC NUM_REDUCE_CONV
  and conv_3 =
    ONCE_DEPTH_CONV BINOM_CONV THENC REAL_POLY_CONV in
  fun tm ->
    let n = dest_small_numeral(lhand tm) in
    let conv_2 = GEN_REWRITE_CONV ONCE_DEPTH_CONV (BERNOULLIS n) in
    (conv_1 THENC conv_2 THENC conv_3) tm;;
```

### Informal statement
The `BERNPOLY_CONV` conversion takes a term `tm` and applies a series of conversions to it. First, it extracts a small numeral `n` from the left-hand side of `tm`. Then, it defines three conversions: `conv_1`, which applies `REWR_CONV` with `bernpoly`, followed by `SUM_CONV`, `TOP_DEPTH_CONV` with `BETA_CONV`, and finally `NUM_REDUCE_CONV`; `conv_2`, which applies `GEN_REWRITE_CONV` with `ONCE_DEPTH_CONV` and `BERNOULLIS n`; and `conv_3`, which applies `ONCE_DEPTH_CONV` with `BINOM_CONV` followed by `REAL_POLY_CONV`. The conversion `BERNPOLY_CONV` then applies `conv_1`, `conv_2`, and `conv_3` in sequence to the input term `tm`.

### Informal sketch
* The conversion starts by extracting a small numeral `n` from the input term `tm`.
* It then applies a series of conversions to `tm`:
  + `conv_1` applies rewriting using `bernpoly`, followed by sum conversion, beta conversion at the top level, and numerical reduction.
  + `conv_2` applies a generalized rewrite using `BERNOULLIS n` at a depth of one.
  + `conv_3` applies a binomial conversion followed by a real polynomial conversion.
* The final result is obtained by applying `conv_1`, `conv_2`, and `conv_3` in sequence to the input term `tm`.
* Key HOL Light terms involved include `REWR_CONV`, `SUM_CONV`, `TOP_DEPTH_CONV`, `BETA_CONV`, `NUM_REDUCE_CONV`, `GEN_REWRITE_CONV`, `ONCE_DEPTH_CONV`, `BINOM_CONV`, and `REAL_POLY_CONV`.

### Mathematical insight
The `BERNPOLY_CONV` conversion appears to be related to Bernoulli polynomials and their properties. The use of `BERNOULLIS n` suggests a connection to Bernoulli numbers, which are closely related to Bernoulli polynomials. The conversion may be used to simplify or manipulate expressions involving Bernoulli polynomials.

### Dependencies
* Theorems/Definitions:
  + `bernpoly`
  + `BERNOULLIS`
* Tactics:
  + `REWR_CONV`
  + `SUM_CONV`
  + `TOP_DEPTH_CONV`
  + `BETA_CONV`
  + `NUM_REDUCE_CONV`
  + `GEN_REWRITE_CONV`
  + `ONCE_DEPTH_CONV`
  + `BINOM_CONV`
  + `REAL_POLY_CONV`

### Porting notes
When porting this conversion to another proof assistant, special attention should be paid to the handling of binders and the implementation of the various conversions. The `GEN_REWRITE_CONV` tactic, in particular, may require careful handling, as its behavior can depend on the specifics of the proof assistant's rewriting mechanism. Additionally, the `ONCE_DEPTH_CONV` tactic may need to be reimplemented or replaced with a similar tactic in the target proof assistant.

---

## SOP_CONV

### Name of formal statement
SOP_CONV

### Type of the formal statement
Theorem/Conversion Rule

### Formal Content
```ocaml
let SOP_CONV =
  let pth = prove
   (`sum(0..n) (\k. &k pow m) =
        (\p. (p(&n + &1) - p(&0)) / (&m + &1))
        (\x. bernpoly (SUC m) x)`,
    REWRITE_TAC[SUM_OF_POWERS]) in
  let conv_0 = REWR_CONV pth in
  REWR_CONV pth THENC
  RAND_CONV(ABS_CONV(LAND_CONV NUM_SUC_CONV THENC BERNPOLY_CONV)) THENC
  TOP_DEPTH_CONV BETA_CONV THENC
  REAL_POLY_CONV
```

### Informal statement
The theorem `SOP_CONV` proves that the sum of the `m`-th powers of the first `n` natural numbers is equal to the difference of the `n+1`-th and 0-th values of the `m+1`-th Bernoulli polynomial, divided by `m+1`. This is achieved through a series of rewriting and conversion steps.

### Informal sketch
* The proof starts by proving a key equation using `REWRITE_TAC` with the `SUM_OF_POWERS` theorem.
* This equation is then used to define a conversion `conv_0` via `REWR_CONV`.
* The main conversion `SOP_CONV` is then composed from several steps:
 + Applying the `REWR_CONV` with the proven equation.
 + Applying `RAND_CONV` with a combination of `ABS_CONV`, `LAND_CONV`, `NUM_SUC_CONV`, and `BERNPOLY_CONV`.
 + Applying `TOP_DEPTH_CONV` with `BETA_CONV`.
 + Finally, applying `REAL_POLY_CONV`.
* These steps involve rewriting, conversion, and simplification to transform the initial sum into the desired form involving Bernoulli polynomials.

### Mathematical insight
The `SOP_CONV` theorem provides a way to express the sum of powers of natural numbers in terms of Bernoulli polynomials, which are important in number theory and have applications in various mathematical areas. This conversion can simplify expressions and provide insights into properties of sums of powers.

### Dependencies
* Theorems:
 + `SUM_OF_POWERS`
* Definitions:
 + `bernpoly`
 + `SUC`
* Tactics and Conversions:
 + `REWRITE_TAC`
 + `REWR_CONV`
 + `RAND_CONV`
 + `ABS_CONV`
 + `LAND_CONV`
 + `NUM_SUC_CONV`
 + `BERNPOLY_CONV`
 + `TOP_DEPTH_CONV`
 + `BETA_CONV`
 + `REAL_POLY_CONV`

### Porting notes
When translating `SOP_CONV` into other proof assistants, pay close attention to the handling of Bernoulli polynomials and the specific sequence of rewriting and conversion steps. Differences in how binders are handled and the availability of similar tactics or conversions may require adjustments to the ported version. Additionally, the representation of natural numbers and polynomials might vary, affecting how the sum of powers and the Bernoulli polynomial are defined and manipulated.

---

## SOP_NUM_CONV

### Name of formal statement
SOP_NUM_CONV

### Type of the formal statement
Theorem/Conversion Rule

### Formal Content
```ocaml
let SOP_NUM_CONV =
  let pth = prove
   (`sum(0..n) (\k. &k pow p) = &m ==> nsum(0..n) (\k. k EXP p) = m`,
    REWRITE_TAC[REAL_OF_NUM_POW; GSYM REAL_OF_NUM_SUM_NUMSEG;
                REAL_OF_NUM_EQ]) in
  let rule_1 = PART_MATCH (lhs o rand) pth in
  fun tm ->
    let th1 = rule_1 tm in
    let th2 = SOP_CONV(lhs(lhand(concl th1))) in
    MATCH_MP th1 th2;;
```

### Informal statement
For all natural numbers `n`, `m`, and `p`, if the sum from 0 to `n` of `k` to the power of `p` equals `m`, then the sum from 0 to `n` of `k` exponential `p` equals `m`. This is proven using a combination of rewriting and matching rules.

### Informal sketch
* The proof starts with a `prove` statement that establishes a relationship between a sum of powers and a sum of exponentials.
* It uses `REWRITE_TAC` with specific rewriting rules (`REAL_OF_NUM_POW`, `GSYM REAL_OF_NUM_SUM_NUMSEG`, `REAL_OF_NUM_EQ`) to transform the initial statement.
* A `PART_MATCH` is applied to create a rule (`rule_1`) that can be used for partial pattern matching.
* The main conversion function `SOP_NUM_CONV` takes a term `tm` and applies `rule_1` to it, obtaining a theorem `th1`.
* It then applies another conversion `SOP_CONV` to the left-hand side of the conclusion of `th1`, obtaining `th2`.
* Finally, it combines `th1` and `th2` using `MATCH_MP` to derive the final theorem.

### Mathematical insight
This conversion rule appears to facilitate the transformation between different representations of sums involving powers and exponentials, potentially simplifying expressions or making them more amenable to further reasoning. It leverages properties of real numbers and their representation in HOL Light to establish an equivalence that can be crucial in various mathematical proofs, especially those involving summations and exponential functions.

### Dependencies
* `REAL_OF_NUM_POW`
* `GSYM REAL_OF_NUM_SUM_NUMSEG`
* `REAL_OF_NUM_EQ`
* `PART_MATCH`
* `MATCH_MP`
* `SOP_CONV`

### Porting notes
When translating this into another proof assistant, pay close attention to how each system handles pattern matching (`PART_MATCH`), rewriting (`REWRITE_TAC`), and the combination of theorems (`MATCH_MP`). Additionally, ensure that the target system has analogous representations for real numbers, summations, and exponential functions, and that these are correctly aligned with the original HOL Light constructs. Special care should be taken with the `GSYM` tactic, as its behavior might differ between systems, affecting the correctness of the ported proof.

---

