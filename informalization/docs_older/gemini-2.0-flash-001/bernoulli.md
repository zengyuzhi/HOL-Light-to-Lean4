# bernoulli.ml

## Overview

Number of statements: 16

The file `bernoulli.ml` formalizes Bernoulli numbers and polynomials. It also contains definitions and theorems related to the sum of kth powers. Its content relies on binomial coefficients, analysis, and transcendental functions.


## SUM_DIFFS

### Name of formal statement
SUM_DIFFS

### Type of the formal statement
theorem

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
    MATCH_MP_TAC SUM_TRIV_NUMSEG THEN ARITH_TAC]);;
```

### Informal statement
For any function `a` from natural numbers to real numbers, and any natural numbers `m` and `n`, if `m` is less than or equal to `n + 1`, then the sum of the differences `a(i + 1) - a(i)` as `i` ranges from `m` to `n` is equal to `a(n + 1) - a(m)`.

### Informal sketch
The proof proceeds by induction on `n`.

- **Base Case:** When `n` is such that `m <= n + 1` is equivalent to `m = 0 \/ m = 1`. This case is handled by simplifying the sum and evaluating the differences, using basic arithmetic and the reflexivity of subtraction.
- **Inductive Step:** Assuming the theorem holds for `n`, we want to prove it holds for `n + 1`. We show that `m <= (n + 1) + 1` implies `m <= n + 1 \/ m = n + 1`.  Under the assumption `m <= (n + 1) + 1`, we split the interval `m` to `n + 1` into `m` to `n` and `n+1`. Thus the sum from `m` to `n + 1` is equal to the sum from `m` to `n` plus the term `a((n + 1) + 1) - a(n + 1)`. By the inductive hypothesis, the sum from `m` to `n` is `a(n + 1) - a(m)`. So after simplification based on the inductive hypothesis, we are left to show that `a(n + 1) - a(m) + a(S(n + 1)) - a(n + 1) = a(S(n + 1)) - a(m)`, which is proven by basic real arithmetic.
- The induction step also leverages the theorem `SUM_TRIV_NUMSEG`, and the trivial case where `n + 1 + 1 <= n + 1` (which is always false).

### Mathematical insight
This theorem states a discrete analogue of the fundamental theorem of calculus. It shows that the sum of consecutive differences of a function over an interval equals the difference of the function's values at the interval's endpoints. This result is a basic and important tool for manipulating sums and simplifying expressions.

### Dependencies
- `SUM_CLAUSES_NUMSEG`
- `ARITH`
- `ADD_CLAUSES`
- `REAL_SUB_REFL`
- `ADD1`
- `SUM_TRIV_NUMSEG`


---

## DIFF_SUM

### Name of formal statement
DIFF_SUM

### Type of the formal statement
theorem

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
  ASM_SIMP_TAC[LE_REFL; ARITH_RULE `k <= b ==> k <= SUC b`]);;
```

### Informal statement
For all functions `f` and `f'` and for all natural numbers `a` and `b`, if for all `k` such that `a <= k` and `k <= b`, the function `\x. f x k` is differentiable with limit `f'(k)` at `x`, then the function `\x. sum(a..b) (f x)` is differentiable with limit `sum(a..b) f'` at `x`.

### Informal sketch
The proof proceeds by induction on `b`.

- **Base Case:** When `b = 0`, the summation `sum(a..0)` is considered. Cases need to be split depending on whether `a <= 0` to apply `SUM_TRIV_NUMSEG`.
- **Inductive Step:** Assume that the statement holds for `b`. We need to show that it also holds for `SUC b`. By using `SUM_CLAUSES_NUMSEG`, the sum from `a` to `SUC b` can be split into `sum(a..b) (f x) + f x (SUC b)`. The derivative of the sum can then be expressed as the sum of the derivatives, using the theorem `DIFF_ADD`. The assumption about differentiability is then used.

### Mathematical insight
This theorem states that the derivative of a finite sum is the sum of the derivatives, provided each term in the sum is differentiable. It's a fundamental result in calculus and real analysis, allowing term-by-term differentiation of finite series. The condition `!k. a <= k /\ k <= b ==> ((\x. f x k) diffl f'(k)) x` states that for all `k` between `a` and `b`, the partial function `f x k` has derivative `f' k` at `x`. This is a crucial condition for the theorem to hold.

### Dependencies
- `ARITH`
- `DIFF_CONST`
- `SUM_TRIV_NUMSEG`
- `DIFF_ADD`
- `LE_REFL`
- `SUM_CLAUSES_NUMSEG`

### Porting notes (optional)
- The theorem relies on the definition of `sum` over a natural number range (from `a` to `b`). The definition of `sum` and its properties (`SUM_CLAUSES_NUMSEG`, `SUM_TRIV_NUMSEG`) must be available in the target proof assistant.
- The handling of differentiability (`diffl`) and its properties (`DIFF_ADD`, `DIFF_CONST`) needs to be considered.
- The arithmetic reasoning (`ARITH_RULE`, `LE_REFL`) may require adaptation or specific arithmetic tactics in other proof assistants.


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
       --sum(0..n) (\j. &(binom(n + 2,j)) * bernoulli j) / (&n + &2))`;;
```

### Informal statement
The Bernoulli numbers are defined recursively such that the 0-th Bernoulli number is 1, and for every natural number `n`, the (n+1)-th Bernoulli number is equal to the negation of the sum from 0 to `n` of terms of the form `(binom(n+2,j) * bernoulli j)` divided by `(n+2)`.

### Informal sketch
The definition introduces the Bernoulli numbers as a recursive function. The base case is `bernoulli 0 = 1`. The recursive step defines `bernoulli (SUC n)` in terms of a summation involving previous Bernoulli numbers `bernoulli j` for `j` from 0 to `n`, binomial coefficients `binom(n+2, j)`, and the natural number `n`. This captures the standard recursive definition of Bernoulli numbers.

### Mathematical insight
The Bernoulli numbers appear in many areas of mathematics, including number theory, analysis, and topology. They are especially prominent in formulas for sums of powers of integers, the Euler-Maclaurin formula, and the Riemann zeta function. This definition provides a way to compute the Bernoulli numbers recursively.

### Dependencies
- `binom` (Binomial coefficients)
- `sum` (Summation over a range)


---

## BERNOULLI

### Name of formal statement
BERNOULLI

### Type of the formal statement
theorem

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
  REWRITE_TAC[BINOM_REFL] THEN REAL_ARITH_TAC);;
```

### Informal statement
For all natural numbers *n*, the sum from 0 to *n* of the terms (binomial coefficient of (*n* + 1, *j*) times the *j*-th Bernoulli number) is equal to 1 if *n* is 0, and 0 otherwise.

### Informal sketch
The proof proceeds by induction on `n`.

*   Base case (`n = 0`): The sum reduces to the binomial coefficient of (1,0) times the 0-th Bernoulli number, which simplifies to 1 * 1 = 1, as required.
*   Inductive step: Assume the theorem holds for `n`. We need to show it holds for `SUC n` (i.e., `n + 1`).
    *   Rewrite the inductive step's summation using the definition of `bernoulli`, the summation clauses `SUM_CLAUSES_NUMSEG`, and properties of addition (`ADD_CLAUSES`).
    *   Simplify the expression using binomial coefficient identities such as `BINOM_LT`, `BINOM_REFL`, and cancellation laws for real numbers (`REAL_ADD_LID`).
    *   Apply additional rewriting rules using `ADD_CLAUSES` and convert real numbers to natural numbers using `REAL_OF_NUM_ADD`.
    * Employ arithmetic reasoning, like `SUC(SUC n) = n + 2`.
    * Reason using field simplification of the form `x = &n + &2 ==> s + x * --s / (&n + &2) = &0)`.
    *   Using properties of the binomial coefficient, `BINOM_TOP_STEP_REAL`, and arithmetic facts like `~(n = n + 1)`, simplify the expression.
    * Utilize `BINOM_REFL` to simplify further.
    * Finally, the goal is discharged using real arithmetic tactics (`REAL_ARITH_TAC`).

### Mathematical insight
This theorem represents a recurrence relation formula that connects Bernoulli numbers to binomial coefficients and the sum of their products. It serves as a way to compute or define Bernoulli numbers recursively. The theorem highlights a fundamental property of Bernoulli numbers.

### Dependencies
*   `bernoulli`
*   `SUM_CLAUSES_NUMSEG`
*   `ADD1`
*   `ADD_CLAUSES`
*   `binom`
*   `REAL_MUL_LID`
*   `LE_0`
*   `NOT_SUC`
*   `BINOM_LT`
*   `BINOM_REFL`
*   `REAL_ADD_LID`
*   `REAL_OF_NUM_ADD`
*   `BINOM_TOP_STEP_REAL`

### Porting notes
*   The presence of tactics like `REAL_ARITH_TAC` suggests the need for a decision procedure for universally quantified real arithmetic formulas.
*   Careful attention should be paid to the handling of the binomial coefficients and the definition of the summation operator.
*   The induction tactic `INDUCT_TAC` corresponds to standard mathematical induction; ensure that your system correctly handles inductive proofs over natural numbers.


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
The Bernoulli polynomial of degree `n` at `x`, denoted `bernpoly n x`, is defined as the sum from `k = 0` to `n` of the expression `(binom(n,k)) * bernoulli k * x pow (n - k)`, where `binom(n, k)` is the binomial coefficient "n choose k", `bernoulli k` is the k-th Bernoulli number, and `x pow (n - k)` is `x` raised to the power of `n - k`.

### Informal sketch
The definition of `bernpoly n x` is a direct application of the summation operator `sum` over a range of integers.  The core of the definition involves pointwise evaluation via a lambda abstraction `\k. ...` that computes a real number for each `k` from `0` to `n`.  The expression being summed combines the binomial coefficient `binom(n, k)`, the Bernoulli number `bernoulli k`, and a power `x pow (n - k)`. Each of these components has its own independent definition. Thus, the overall construction simply defines a weighted sum.

### Mathematical insight
Bernoulli polynomials are a classical family of polynomials with many applications in number theory, analysis, and combinatorics. This definition expresses the Bernoulli polynomial as a sum involving binomial coefficients, Bernoulli numbers, and powers of the variable `x`. This particular form is useful for relating Bernoulli polynomials to Bernoulli numbers and for deriving various identities.

### Dependencies
- `sum`
- `binom`
- `bernoulli`
- `pow`


---

## DIFF_BERNPOLY

### Name of formal statement
DIFF_BERNPOLY

### Type of the formal statement
theorem

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
  ABBREV_TAC `z = x pow (n - k)` THEN CONV_TAC REAL_FIELD);;
```

### Informal statement
For all natural numbers `n` and real numbers `x`, the derivative with respect to `x` of the `(n+1)`-th Bernoulli polynomial evaluated at `x` is equal to `(n+1)` times the `n`-th Bernoulli polynomial evaluated at `x`.

### Informal sketch
The proof proceeds by induction on `n`.
- The goal is `!n x. ((bernpoly (SUC n)) diffl (&(SUC n) * bernpoly n x)) x`, which states the derivative of the (n+1)-th Bernoulli polynomial is (n+1) times the n-th Bernoulli polynomial.
- First, rewrite using the definition of `bernpoly`, `SUM_CLAUSES_NUMSEG` (which provides rewrite rules for sums), and `LE_0` (which states that `x <= 0` is false if `x` is a natural number).
- Next, rewrite with `GSYM REAL_ADD_RID` to move the real addition to the right.
- Then, apply the derivative of a sum rule (`DIFF_ADD`). Simplify using reflexivity of subtraction (`SUB_REFL`) and the derivative of a constant (`DIFF_CONST`).
- Rewrite to prepare for differentiating the summation. Use the fact that a sum multiplied by a constant is the sum of the constant multiplied by each term (`GSYM SUM_LMUL`), and then use the rule for differentiating a sum (`DIFF_SUM`).
- Eliminate outer quantifiers via stripping, and rewrite using `ADD1` and `BINOM_TOP_STEP_REAL` (the binomial coefficient identity such that `(n+1)! / (k! * (n+1-k)!) = (n+1) / (n+1-k)` if the arguments are real).
- Differentiate using `DIFF_TAC`. Simplify using the assumption that `k <= n` implies `~(k = n + 1)`.
- Rewrite to clean up the arithmetic, using `REAL_MUL_LZERO` and `REAL_ADD_LID`.
- Simplify the expression using `k <= n ==> (n + 1) - k - 1 = n - k` and other algebraic rules.
- Eliminate the discharge goal using the assumption `k <= n:num`.
- Convert to real numbers using `GSYM REAL_OF_NUM_ADD` and `GSYM REAL_OF_NUM_LE`.
- Finally, apply real field tactics (`CONV_TAC REAL_FIELD`).

### Mathematical insight
This theorem provides a fundamental relationship between Bernoulli polynomials of consecutive degrees via differentiation. It is a standard result in the theory of Bernoulli polynomials and is crucial for various applications, including numerical analysis and asymptotic expansions.

### Dependencies
- `bernpoly`
- `SUM_CLAUSES_NUMSEG`
- `LE_0`
- `REAL_ADD_RID`
- `DIFF_ADD`
- `SUB_REFL`
- `real_pow`
- `DIFF_CONST`
- `SUM_LMUL`
- `DIFF_SUM`
- `ADD1`
- `BINOM_TOP_STEP_REAL`
- `REAL_MUL_LZERO`
- `REAL_ADD_LID`
- `REAL_OF_NUM_SUB`
- `REAL_OF_NUM_ADD`
- `REAL_OF_NUM_LE`


---

## INTEGRALS_EQ

### Name of formal statement
INTEGRALS_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INTEGRALS_EQ = prove
 (`!f g. (!x. ((\x. f(x) - g(x)) diffl &0) x) /\ f(&0) = g(&0)
         ==> !x. f(x) = g(x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`\x:real. f(x) - g(x)`; `x:real`; `&0`] DIFF_ISCONST_ALL) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;
```

### Informal statement
For any real-valued functions `f` and `g`, if the difference `f(x) - g(x)` has a derivative of zero at every point `x`, and `f(0)` equals `g(0)`, then `f(x)` equals `g(x)` for all `x`.

### Informal sketch
The proof proceeds as follows:
- Assume that the derivative of `f(x) - g(x)` is zero for all `x`, and that `f(0) = g(0)`.
- Apply the theorem `DIFF_ISCONST_ALL`, instantiated for the function `\x:real. f(x) - g(x)`, the point `x`, and `&0`.  This theorem states that if a function has a derivative of zero everywhere, then the difference between its value at any point `x` and its value at `0` is zero. In this case, `(f(x) - g(x)) - (f(0) - g(0)) = 0`.
- Simplify using the assumption `f(0) = g(0)` so that `f(x) - g(x) = 0`.
- Apply real arithmetic to deduce `f(x) = g(x)`.

### Mathematical insight
This theorem states that a function is uniquely determined by its derivative and its value at a single point. This is a fundamental result in calculus, guaranteeing the uniqueness of antiderivatives up to a constant.

### Dependencies
- Theorem: `DIFF_ISCONST_ALL`


---

## RECURRENCE_BERNPOLY

### Name of formal statement
RECURRENCE_BERNPOLY

### Type of the formal statement
theorem

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
  ASM_REWRITE_TAC[ADD_SUB]);;
```

### Informal statement
For all natural numbers `n` and all real numbers `x`, the difference between the Bernoulli polynomial of degree `n` evaluated at `x + 1` and the Bernoulli polynomial of degree `n` evaluated at `x` is equal to `n` times `x` raised to the power of `n - 1`.

### Informal sketch
The proof proceeds by induction on `n`.

- Base case (`n = 0`): The theorem simplifies using the definition of `bernpoly`, `SUM_SING_NUMSEG`, `REAL_SUB_REFL`, `SUB_REFL`, `real_pow`, and `REAL_MUL_LZERO`.
- Inductive step:
  - Assume the theorem holds for `n`.
  - Prove it for `SUC n`.
  - Use `MATCH_MP_TAC` on `INTEGRALS_EQ` and then perform case splitting using `CONJ_TAC`.
  - Introduce `x:real` and apply the inductive hypothesis using `FIRST_X_ASSUM(MP_TAC o SPEC x:real)`.
  - Rewrite using `GSYM REAL_SUB_0`.
  - Apply `AP_TERM `(*) (&(SUC n))` and rewrite using `REAL_MUL_RZERO`. Use substitution and rewrite using `REAL_SUB_LDISTRIB`.
  - Repeatedly apply `MATCH_MP_TAC` with `DIFF_SUB` and perform case splitting using `CONJ_TAC`.
  - Simplify using rules like `SUC_SUB1`, `DIFF_CMUL`, `DIFF_POW`, `DIFF_BERNPOLY`, and `ETA_AX`.
  - Rewrite using `GSYM REAL_MUL_RID`.
  - Apply `MATCH_MP_TAC` with `DIFF_CHAIN` and rewrite using `DIFF_BERNPOLY`.
  - Differentiate using `DIFF_TAC` and apply real arithmetic tactics (`REAL_ARITH_TAC`).
- Simplify the initial goal using the definition of `bernpoly`, `GSYM SUM_SUB_NUMSEG`.
- Rewrite using identities like `REAL_ADD_LID`, `REAL_POW_ONE`, and `GSYM REAL_SUB_LDISTRIB`.
- Rewrite using `SUM_CLAUSES_NUMSEG`, `LE_0`, `SUB_REFL`, and `real_pow`.
- Rewrite using `REAL_SUB_REFL`, `REAL_MUL_RZERO`, `REAL_ADD_RID`. Simplify using arithmetic (`ARITH_RULE i <= n ==> SUC n - i = SUC(n - i)`).
- Rewrite using `real_pow`, `REAL_MUL_LZERO`, `REAL_SUB_RZERO`, and `REAL_MUL_RID`.
- Rewrite using the definitions of `BERNOULLI` and `ADD1`.
- Perform case analysis using `COND_CASES_TAC`.
- Perform assumption rewriting with arithmetic (`ARITH`) and simplification using `real_pow` and `REAL_MUL_LID`.
- Convert and rewrite using `REAL_ENTIRE` and `REAL_POW_EQ_0`. Finally, use assumption rewriting with `ADD_SUB`.

### Mathematical insight
This theorem expresses a fundamental recurrence relation satisfied by Bernoulli polynomials. It relates the difference of the Bernoulli polynomial at `x+1` and `x` to a power of `x`. This recurrence can be used to compute Bernoulli polynomials and derive other identities.

### Dependencies
- Definitions:
  - `bernpoly`
  - `BERNOULLI`
- Theorems/Lemmas:
  - `SUM_SING_NUMSEG`
  - `REAL_SUB_REFL`
  - `SUB_REFL`
  - `real_pow`
  - `REAL_MUL_LZERO`
  - `INTEGRALS_EQ`
  - `GSYM REAL_SUB_0`
  - `REAL_MUL_RZERO`
  - `REAL_SUB_LDISTRIB`
  - `DIFF_SUB`
  - `SUC_SUB1`
  - `DIFF_CMUL`
  - `DIFF_POW`
  - `DIFF_BERNPOLY`
  - `ETA_AX`
  - `GSYM REAL_MUL_RID`
  - `DIFF_CHAIN`
  - `SUM_SUB_NUMSEG`
  - `REAL_ADD_LID`
  - `REAL_POW_ONE`
  - `SUM_CLAUSES_NUMSEG`
  - `LE_0`
  - `REAL_ADD_RID`
  - `ARITH_RULE i <= n ==> SUC n - i = SUC(n - i)`
  - `ADD1`
  - `REAL_ENTIRE`
  - `REAL_POW_EQ_0`
  - `ADD_SUB`


---

## SUM_OF_POWERS

### Name of formal statement
SUM_OF_POWERS

### Type of the formal statement
theorem

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
    SIMP_TAC[SUM_DIFFS; LE_0] THEN REWRITE_TAC[REAL_OF_NUM_ADD]]);;
```

### Informal statement
For all natural numbers `n`, the sum from `0` to `n` of `k` raised to the power of `m` is equal to the difference between the Bernoulli polynomial of degree `m+1` evaluated at `n+1` and the Bernoulli polynomial of degree `m+1` evaluated at `0`, divided by `m+1`.

### Informal sketch
The proof proceeds as follows:
- The goal is to prove the formula for the sum of powers.
- Simplify using `REAL_EQ_RDIV_EQ` and `REAL_ARITH &0 < &n + &1`. This rewrites the division by `&m + &1` as multiplication by its reciprocal.
- Rewrite using the commutative property of multiplication `REAL_MUL_SYM`.
- Rewrite the sum of a scalar multiple `SUM_LMUL` to pull the scalar outside the sum, so that we need to show that `bernpoly (SUC m) (&n + &1) - bernpoly (SUC m) (&0)` equals the sum of  `(&m + &1) * (&k pow m)`.
- Apply `EQ_TRANS` after showing that there exists a sum of the form `sum(0..n) (\i. bernpoly (SUC m) (&(i + 1)) - bernpoly (SUC m) (&i))` that is equal to `bernpoly(SUC m) (&n + &1) - bernpoly(SUC m) (&0)`. This introduces the telescoping sum. 
- Split into two subgoals.
- The first subgoal involves rewriting using the recurrence relation for Bernoulli polynomials `RECURRENCE_BERNPOLY` and simplifying `REAL_OF_NUM_ADD`, as well as `REAL_OF_NUM_SUC` and `SUC_SUB1`.
- The second subgoal proves the collapsing sum `SUM_DIFFS` simplifies and rewrites with `LE_0` and `REAL_OF_NUM_ADD`.

### Mathematical insight
This theorem provides a closed-form expression for the sum of the `m`-th powers of the first `n` natural numbers, expressed in terms of Bernoulli polynomials. The proof uses the recurrence relation for Bernoulli polynomials and the telescoping property of a summation of differences.

### Dependencies
- `REAL_EQ_RDIV_EQ`
- `REAL_ARITH &0 < &n + &1`
- `REAL_MUL_SYM`
- `SUM_LMUL`
- `RECURRENCE_BERNPOLY`
- `REAL_OF_NUM_ADD`
- `REAL_OF_NUM_SUC`
- `SUC_SUB1`
- `SUM_DIFFS`
- `LE_0`


---

## SUM_CONV

### Name of formal statement
SUM_CONV

### Type of the formal statement
Theorem

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
The theorem `SUM_CONV` defines a conversion rule `sconv` for simplifying expressions of the form `sum(0..n) f`, where `sum` represents the summation of the function `f` from `0` to `n`.
The conversion `sconv` uses the following two rewrite rules derived from a proven theorem:
1. `sum(0..0) f` is rewritten to `f 0`.
2. `sum(0..SUC n) f` is rewritten to `sum(0..n) f + f(SUC n)`.
The conversion `sconv` applies the first rewrite rule if possible. Otherwise, it checks if the upper bound of the summation is a number using `num_CONV`. If successful, the number is decomposed into its successor using `NUM_SUC_CONV`, and the second rewrite rule is applied. Finally, `sconv` is recursively applied to the summation term and the successor term using `COMB2_CONV`.

### Informal sketch
The conversion `SUM_CONV` is constructed as follows:
- First, a theorem is proven establishing the base case and recursive case for the summation over a number segment, i.e., `sum(0..0) f = f 0 /\ sum(0..SUC n) f = sum(0..n) f + f(SUC n)`.
- Then, two conversions `econv_0` and `econv_1` are created by extracting the two conjuncts of the theorem and converting them to equational rewrite rules. `econv_0` converts `sum(0..0) f` to `f 0`. `econv_1` converts `sum(0..SUC n) f` to `sum(0..n) f + f(SUC n)`.
- A recursive conversion `sconv` is defined:
  - It first attempts to apply `econv_0`.
  - If `econv_0` fails, it attempts to match the upper bound of the summation with a number using `num_CONV`. If it is a number, then `NUM_SUC_CONV` decomposes the number into successor form if applicable and it applies `econv_1` to rewrite `sum(0..SUC n) f` to `sum(0..n) f + f(SUC n)`. Finally, `sconv` is recursively applied to the subterms `sum(0..n) f` and `SUC n`.

### Mathematical insight
`SUM_CONV` provides a computational mechanism to evaluate finite sums of the form `sum(0..n) f` by repeatedly applying the recursive definition of the summation. It uses the base case `sum(0..0) f = f 0` and the recursive step `sum(0..SUC n) f = sum(0..n) f + f(SUC n)`. This conversion allows the proof assistant to automatically compute the value of many concrete summations.

### Dependencies
- Theorems: `SUM_CLAUSES_NUMSEG`, `LE_0`.
- Conversions: `num_CONV`, `NUM_SUC_CONV`.

### Porting notes (optional)
- In other proof assistants, the tactic `SIMP_TAC` might be replaced by corresponding simplification tactics or auto-rewriting mechanisms. The equivalents of `CONJUNCT1` and `CONJUNCT2` would be used to extract the two rewrite rules from the main theorem.
- The `ORELSEC` combinator for conversions can be emulated using `TRY` or similar constructs that attempt the first conversion and, if it fails, proceed to the second.
- The recursion in `sconv` needs to be handled carefully, ensuring termination and proper unfolding of the rewrite rules.


---

## BINOM_CONV

### Name of formal statement
BINOM_CONV

### Type of the formal statement
theorem

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
      CONV_RULE NUM_REDUCE_CONV th1;;
```

### Informal statement
The theorem `BINOM_CONV` defines a conversion that simplifies the term `binom n k` where `n` and `k` are numerals. If `n` is less than `k`, then `binom n k` reduces to 0. If `n` is greater than or equal to `k`, then `binom n k` is rewritten by reducing factorials.

### Informal sketch
- The code defines a conversion `BINOM_CONV` that takes a term `tm` as input.
- The conversion first checks if the term `tm` has the form `binom n k`. If not, it fails.
- If `tm` has the form `binom n k`, where `n` and `k` are numerals, it checks if `n < k`.
- If `n < k`, it uses the theorem `BINOM_LT` (which states that if `n < k` then `binom n k = 0`) and the fact that `n < k` implies the HOL Light term `l < r` represents a true proposition to reduce `binom n k` to 0.
- Otherwise (i.e., if `n >= k`), it calculates `d = n - k` and uses the theorem `BINOM_FACT` with appropriate specialization by `d` and `k` to transform `binom n k`. The theorem `BINOM_FACT` relates the binomial coefficient to factorials, and after specialization the conv_rule uses a NUM_REDUCE_CONV rule (likely arithmetic simplification) to reduce the expression using the factorial definition.
- The initial theorem `a * b * x = FACT c ==> x = (FACT c) DIV (a * b)` is proven by stripping the assumptions, applying symmetry to the conversion, matching division uniqueness, asserting the existence of 0, using conjunction tactic, applying modus ponens with an arithmetic tactic, applying modus ponens and rewriting with `CONTRAPOS_THM` and simplifying with `LT_NZ`, `MULT_ASSOC`, `MULT_CLAUSES` and `MESON`.

### Mathematical insight
The binomial coefficient `binom n k` represents the number of ways to choose `k` elements from a set of `n` elements. It is mathematically defined as `n! / (k! * (n-k)!)` when `n >= k` and `0` when `n < k`. This conversion is an implementation of this mathematical understanding on HOL Light terms.

### Dependencies
- `BINOM_LT`: States that if `n < k`, then `binom n k = 0`.
- `BINOM_FACT`: Relates the binomial coefficient to factorials.
- `FACT`: Factorial function.
- `DIV`: Division function.
- `GSYM CONTRAPOS_THM`
- `LT_NZ`
- `MULT_ASSOC`
- `MULT_CLAUSES`

### Porting notes (optional)
- In other proof assistants, ensure that the binomial coefficient is defined appropriately, alongside appropriate definitions and theorems regarding factorials and arithmetic.
- The approach used here emphasizes rewriting and arithmetic simplification, so a system with good support for these techniques will be beneficial.
- The HOL Light-specific tactics may have different analogues in other proof assistants, but the underlying mathematical steps should remain similar.


---

## BERNOULLIS

### Name of formal statement
BERNOULLIS

### Type of the formal statement
Definition

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
The definition `BERNOULLIS` computes a list of theorems about Bernoulli numbers.  It uses a recursive function `bconv` which, given a natural number `n`, returns a list of theorems. If `n` is less than or equal to 0, it returns a list containing the theorem `th_0`. Otherwise, it recursively calls `bconv` with `n - 1` to obtain a list of theorems `bths`. It then constructs a term `tm` representing the Bernoulli number with index `n` (i.e., `bernoulli n`). It applies a conversion to `tm` that simplifies it using arithmetic conversions, the theorem `th_1`, arithmetic conversions on sums, beta reduction, simplification using numeric reduction or binomial theorem expansion, rewriting using previously calculated Bernoulli number theorems `bths`, and real rational reduction. The result of this conversion is then prepended to the list `bths`.

### Informal sketch
The definition calculates a list of theorems proving closed forms for Bernoulli numbers using a recursive function `bconv`:
- The base case: If `n` is zero or negative, a list containing the theorem `th_0` is returned.
- The inductive step:
  - Recursively compute the theorems for `bernoulli 0`, `bernoulli 1`, ..., `bernoulli (n-1)`.
  - Construct the term `bernoulli n`.
  - Simplify `bernoulli n` using a combination of:
    - Arithmetic conversions (`num_CONV`, `SUM_CONV`)
    - Rewriting with the theorem `th_1` (likely a recurrence relation defining Bernoulli numbers).
    - Beta reduction (`BETA_CONV`).
    - Numeric reduction or binomial expansion (`NUM_RED_CONV`, `BINOM_CONV`).
    - Rewriting with previously computed Bernoulli theorems `bths`.
    - Rational reduction (`REAL_RAT_REDUCE_CONV`)
  - Prepend the resulting theorem to the list of theorems `bths`.
  - Return the updated list.

The overall process involves a recursive computation combined with simplification strategies to derive theorems about Bernoulli numbers.

### Mathematical insight
The code computes theorems for Bernoulli numbers by iteratively computing and simplifying expressions for successive Bernoulli numbers. The simplification involves using a recurrence relation and previously computed values to express each Bernoulli number in a closed form. The recursive accumulation of theorems represents a dynamic programming approach where previously computed theorems are used to derive later ones.

### Dependencies
- `bernoulli` (A definition or axiom introducing Bernoulli numbers)
- `CONJ_PAIR`
- `GEN_REWRITE_CONV`
- `num_CONV`, `SUM_CONV`, `BETA_CONV`, `NUM_RED_CONV`, `BINOM_CONV`, `REAL_RAT_REDUCE_CONV`

### Porting notes (optional)
- The key part to translate is the tactic application sequence to derive the theorems. Other systems are unlikely to have have exact equivalents for the tactics like `ONCE_DEPTH_CONV` etc., so the translation should focus on achieving the effect of those tactics, rather than a line-for-line tactic translation. Specifically, it is important to apply the arithmetic conversion, the theorem `th_1` (which defines the bernoulli number), beta-reduction, simplification using numeric and binomial conversions, the use of previously computed bernoulli theorems and rational reduction at each step.


---

## BERNOULLI_CONV

### Name of formal statement
BERNOULLI_CONV

### Type of the formal statement
Conversion

### Formal Content
```ocaml
let BERNOULLI_CONV =
  let b_tm = `bernoulli` in
  fun tm -> let op,n = dest_comb tm in
            if op <> b_tm || not(is_numeral n) then failwith "BERNOULLI_CONV"
            else hd(BERNOULLIS(dest_small_numeral n));;
```

### Informal statement
`BERNOULLI_CONV` is a conversion that, when applied to a term `tm`, checks if `tm` is of the form `bernoulli n`, where `n` is a numeral. If it is, it returns the head of the list of Bernoulli numbers up to the `n`-th one (computed by the function `BERNOULLIS applied to `n`). Otherwise, the conversion fails.

### Informal sketch
- Check if the input term `tm` is an application.
- If not, the conversion fails.
- If it is, decompose it into operator `op` and operand `n`.
- Check if the operator `op` is the term `bernoulli`.
- If not, the conversion fails.
- Check if the operand `n` is a numeral.
- If not, the conversion fails.
- If all checks pass, convert the numeral `n` to a small numeral.
- Compute the list of Bernoulli numbers up to the `n`-th one by applying the function `BERNOULLIS` to `n`.
- Return the head of the resulting list, which represents the `n`-th Bernoulli number.

### Mathematical insight
This conversion provides a way to compute Bernoulli numbers by evaluating the term `bernoulli n`. The function `BERNOULLIS` presumably precomputes these values for efficiency.

### Dependencies
- `bernoulli` (term)
- `dest_comb` (function decomposing a combination term)
- `is_numeral` (predicate checking if a term is a numeral)
- `dest_small_numeral` (function converting a numeral to a small numeral)
- `BERNOULLIS` (function computing a list of Bernoulli numbers)
- `hd` (function returning the head of a list)


---

## BERNPOLY_CONV

### Name of formal statement
BERNPOLY_CONV

### Type of the formal statement
theorem

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
The function `BERNPOLY_CONV` takes a term `tm` as input. It decomposes `tm` into its left-hand side `lhand tm`, which is expected to be a small numeral `n`. It then applies a conversion consisting of three sub-conversions: `conv_1`, `conv_2`, and `conv_3`, in sequence. `conv_1` rewrites using the definition of `bernpoly`, expands the summation, performs beta reduction at the top level, and reduces the resulting numerals. `conv_2` rewrites using the `n`-th Bernoulli number, `BERNOULLIS n`. `conv_3` converts binomial coefficients and processes into a real polynomial.

### Informal sketch
The theorem defines a conversion `BERNPOLY_CONV` to simplify an expression involving the Bernoulli polynomial of a small numeral `n`.
- Given an input term `tm`, extract the numeral `n` from the left-hand side of `tm`.
- Define `conv_1` to perform the following steps:
  - Rewrite using the definition of `bernpoly`.
  - Expand the resulting summation using `SUM_CONV`.
  - Perform beta reduction at the top level, reducing lambda abstractions using `BETA_CONV`.
  - Reduce numerals using `NUM_REDUCE_CONV`.
- Define `conv_2` to rewrite using the value of the `n`-th Bernoulli number `BERNOULLIS n`.
- Define `conv_3` to perform the following steps:
  - Expand binomial coefficients using `BINOM_CONV`.
  - Convert into a real polynomial representation using `REAL_POLY_CONV`.
- Apply the three conversions in sequence: `conv_1` followed by `conv_2` followed by `conv_3`.

### Mathematical insight
The theorem provides a conversion for simplifying expressions involving Bernoulli polynomials. It expands the Bernoulli polynomial, substitutes the appropriate Bernoulli number, and then simplify the result into a real polynomial. This simplification is useful in computations and proofs involving Bernoulli polynomials.

### Dependencies
- `bernpoly`
- `BERNOULLIS`
- `BINOM_CONV`
- `REAL_POLY_CONV`

### Porting notes (optional)
- The definition relies on the presence of predefined concrete values for Bernoulli numbers (`BERNOULLIS`). The porter will need to ensure correct representation of the constants. Implementations of rewriting, summation expansion, beta reduction, numeral reduction and polynomial conversion may vary across provers.


---

## SOP_CONV

### Name of formal statement
SOP_CONV

### Type of the formal statement
theorem

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
  REAL_POLY_CONV;;
```

### Informal statement
The theorem `SOP_CONV` states that the sum of the $m$-th powers of the first $n$ natural numbers is equal to the polynomial expression in $n$ given by evaluating the Bernoulli polynomial `bernpoly (SUC m)` at $n+1$, subtracting its evaluation at $0$, and dividing the result by $m+1$.
Formally:
$$
\sum_{k=0}^{n} k^m = \frac{\text{bernpoly}(m+1, n+1) - \text{bernpoly}(m+1, 0)}{m+1}
$$

### Informal sketch
The proof of the theorem `SOP_CONV` proceeds as follows:
- Starts by proving an initial theorem `pth` which establishes the equality using `REWRITE_TAC` and the theorem `SUM_OF_POWERS`.
- Applies the initial result to rewrite the goal.
- Applies a conversion to the right-hand side, which involves:
  - Applying absolute conversion and then a conversion that applies from left to right. It applies `NUM_SUC_CONV` which simplifies successor numbers such as `SUC m`. It transforms the `bernpoly` term using the `BERNPOLY_CONV`.
- Applies Beta reduction at the top depth of the term to simplify the lambda abstraction.
- Applies `REAL_POLY_CONV` to convert the expression to a real polynomial form.

### Mathematical insight
The theorem `SOP_CONV` provides a closed-form expression for the sum of the $m$-th powers of the first $n$ natural numbers, expressing it in terms of the Bernoulli polynomials. This is a fundamental result in number theory with applications in various fields such as combinatorics and analysis. The theorem connects discrete sums (sum of powers) with continuous functions (Bernoulli polynomials).

### Dependencies
- `SUM_OF_POWERS`
- `NUM_SUC_CONV`
- `BERNPOLY_CONV`


---

## SOP_NUM_CONV

### Name of formal statement
SOP_NUM_CONV

### Type of the formal statement
theorem

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
For any natural number `n`, `p`, and `m`, If the sum of `k^p` from `k = 0` to `n` (where `k` is first coerced to a real) is equal to the real number `m`, then the sum of `k^p` from `k = 0` to `n` (where `k` is used as a natural number), equals `m`.

### Informal sketch
The theorem states the equivalence between the summation of `k^p` from 0 to n, where `k` is a real, and where `k` is a natural number, given the summation result `m` is a real.
- First, a theorem `pth` is proved using rewriting with `REAL_OF_NUM_POW`, the symmetric form of `REAL_OF_NUM_SUM_NUMSEG`, and `REAL_OF_NUM_EQ`. This theorem states that if `sum(0..n) (\k. &k pow p) = &m` , then `nsum(0..n) (\k. k EXP p) = m`.
- Then, `rule_1` is derived from `pth` using `PART_MATCH` applied to the left-hand side of the right-hand side of `pth`.
- The proof proceeds by matching a provided term `tm` via `rule_1` which simplifies the real summation via conversion from a real sum to a natural number sum to create theorem `th1`.
- Then, `th2` is created by applying `SOP_CONV` to the left-hand side of the left-hand side of the conclusion of `th1`, effectively simplifying the summation expression.
- Finally, `th1` and `th2` are combined using `MATCH_MP` to complete the proof.

### Mathematical insight
This theorem highlights the relationship between summation over reals and natural numbers. It essentially states that if you have a sum of powers of natural numbers that equals some real number when each term is converted to a real number, then you can directly compute the natural number sum and equate it to the given real, which can be helpful for converting between the two types of summation for simplification purposes.

### Dependencies
- `REAL_OF_NUM_POW`
- `REAL_OF_NUM_SUM_NUMSEG`
- `REAL_OF_NUM_EQ`
- `SOP_CONV`

### Porting notes (optional)
- The `SOP_CONV` conversion might require special attention when porting, as conversion tactics can vary greatly between proof assistants.
- The handling of real and natural number coercions (`&` operator) might need adaptation based on the target system's type system.


---

