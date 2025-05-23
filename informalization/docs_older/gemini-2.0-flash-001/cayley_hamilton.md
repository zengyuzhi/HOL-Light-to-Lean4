# cayley_hamilton.ml

## Overview

Number of statements: 14

This file, `cayley_hamilton.ml`, formalizes the Cayley-Hamilton theorem for real matrices. It relies on complex number theory and summation from `complexes.ml` and `msum.ml`. The file likely defines concepts related to matrices and their characteristic polynomials, culminating in a proof of the Cayley-Hamilton theorem.


## MATRIC_POLYFUN_EQ_0

### Name of formal statement
MATRIC_POLYFUN_EQ_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MATRIC_POLYFUN_EQ_0 = prove
 (`!n A:num->real^N^M.
        (!x. msum(0..n) (\i. x pow i %% A i) = mat 0) <=>
        (!i. i IN 0..n ==> A i = mat 0)`,
  SIMP_TAC[CART_EQ; MSUM_COMPONENT; MAT_COMPONENT; LAMBDA_BETA;
           FINITE_NUMSEG; COND_ID;
           ONCE_REWRITE_RULE[REAL_MUL_SYM] MATRIX_CMUL_COMPONENT] THEN
  REWRITE_TAC[MESON[]
   `(!x i. P i ==> !j. Q j ==> R x i j) <=>
    (!i. P i ==> !j. Q j ==> !x. R x i j)`] THEN
  REWRITE_TAC[REAL_POLYFUN_EQ_0] THEN MESON_TAC[]);;
```

### Informal statement
For any natural number `n` and any function `A` from numbers to real-valued `N` by `M` matrices, the following holds: the polynomial function in `x` formed by taking the sum from `i = 0` to `n` of `x` raised to the power of `i` multiplied by the matrix `A i` is equal to the zero matrix for all `x` if and only if for all `i` in the range from `0` to `n`, the matrix `A i` is equal to the zero matrix.

### Informal sketch
*   The proof proceeds by simplifying the expression `msum(0..n) (\i. x pow i %% A i) = mat 0`.
*   First, simplification tactics are applied that use rules about equality of Cartesian products (`CART_EQ`), the component of a matrix sum (`MSUM_COMPONENT`), the component of a matrix (`MAT_COMPONENT`), beta reduction (`LAMBDA_BETA`), finiteness of numerical segments (`FINITE_NUMSEG`), conditional identities (`COND_ID`), and rewriting the real multiplication with a symmetric version (`ONCE_REWRITE_RULE[REAL_MUL_SYM] MATRIX_CMUL_COMPONENT`).
*   Then, the theorem `(!x i. P i ==> !j. Q j ==> R x i j) <=> (!i. P i ==> !j. Q j ==> !x. R x i j)` is applied to move the quantifier over `x`.
*   The theorem `REAL_POLYFUN_EQ_0` is used which states that a real polynomial is equal to zero if and only if all its coefficients are equal to zero.
*   Finally, the goal is discharged using a MESON call.

### Mathematical insight
The theorem `MATRIC_POLYFUN_EQ_0` states that if a matrix-valued polynomial is zero for all values of the scalar variable `x`, then all the matrix coefficients of the polynomial must be zero matrices. This is a generalization of the corresponding result for ordinary polynomials (with real or complex coefficients).

### Dependencies
*   `CART_EQ`
*   `MSUM_COMPONENT`
*   `MAT_COMPONENT`
*   `LAMBDA_BETA`
*   `FINITE_NUMSEG`
*   `COND_ID`
*   `MATRIX_CMUL_COMPONENT`
*   `REAL_MUL_SYM`
*   `REAL_POLYFUN_EQ_0`
*   `MESON[] (!x i. P i ==> !j. Q j ==> R x i j) <=> (!i. P i ==> !j. Q j ==> !x. R x i j)`

### Porting notes (optional)
The theorem relies heavily on simplification through rewriting. Recreating this proof in another proof assistant may require similar simplification steps using lemmas about matrix components and arithmetic. The `MESON_TAC` calls may need to be replaced with explicit proof steps depending on the capabilities of the other proof assistant. Handling the matrix-indexed sum (`msum`) appropriately will also be key.


---

## MATRIC_POLY_LEMMA

### Name of formal statement
MATRIC_POLY_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MATRIC_POLY_LEMMA = prove
 (`!(A:real^N^N) B (C:real^N^N) n.
        (!x. msum (0..n) (\i. (x pow i) %% B i) ** (A - x %% mat 1) = C)
        ==> C = mat 0`,
  SIMP_TAC[GSYM MSUM_MATRIX_RMUL; FINITE_NUMSEG; MATRIX_SUB_LDISTRIB] THEN
  REWRITE_TAC[MATRIX_MUL_RMUL] THEN ONCE_REWRITE_TAC[MATRIX_MUL_LMUL] THEN
  ONCE_REWRITE_TAC[MATRIX_CMUL_ASSOC] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
  SIMP_TAC[MSUM_SUB; FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. msum(0..SUC n)
         (\i. x pow i %% (((if i = 0 then (--C:real^N^N) else mat 0) +
                           (if i <= n then B i ** (A:real^N^N) else mat 0)) -
                          (if i = 0 then mat 0 else B(i - 1) ** mat 1))) =
        mat 0`
  MP_TAC THENL
   [SIMP_TAC[MATRIX_CMUL_SUB_LDISTRIB; MSUM_SUB; FINITE_NUMSEG;
             MATRIX_CMUL_ADD_LDISTRIB; MSUM_ADD] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[MATRIX_CMUL_RZERO] THEN
    ONCE_REWRITE_TAC[MESON[]
     `(if p then mat 0 else x) = (if ~p then x else mat 0)`] THEN
    REWRITE_TAC[GSYM MSUM_RESTRICT_SET; IN_NUMSEG] THEN
    REWRITE_TAC[ARITH_RULE `(0 <= i /\ i <= SUC n) /\ i = 0 <=> i = 0`;
      ARITH_RULE `(0 <= i /\ i <= SUC n) /\ i <= n <=> 0 <= i /\ i <= n`;
      ARITH_RULE `(0 <= i /\ i <= SUC n) /\ ~(i = 0) <=>
                  1 <= i /\ i <= SUC n`] THEN
    REWRITE_TAC[SING_GSPEC; GSYM numseg; MSUM_SING; real_pow] THEN
    REWRITE_TAC[MATRIX_CMUL_LID] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM th]) THEN
    REWRITE_TAC[MATRIX_NEG_SUB] THEN REWRITE_TAC[MATRIX_SUB; AC MATRIX_ADD_AC
     `(((A:real^N^N) + --B) + B) + C = (--B + B) + A + C`] THEN
    REWRITE_TAC[MATRIX_ADD_LNEG; MATRIX_ADD_LID] THEN
    REWRITE_TAC[num_CONV `1`] THEN REWRITE_TAC[ADD1; MSUM_OFFSET] THEN
    REWRITE_TAC[ADD_CLAUSES; ADD_SUB; MATRIX_ADD_RNEG];
    REWRITE_TAC[MATRIC_POLYFUN_EQ_0; IN_NUMSEG; LE_0] THEN DISCH_TAC THEN
    SUBGOAL_THEN `!i:num. B(n - i) = (mat 0:real^N^N)` MP_TAC THENL
     [MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN
        REWRITE_TAC[LE_REFL; SUB_0; NOT_SUC; ARITH_RULE `~(SUC n <= n)`] THEN
        REWRITE_TAC[MATRIX_ADD_LID; SUC_SUB1; MATRIX_MUL_RID] THEN
        REWRITE_TAC[MATRIX_SUB_LZERO; MATRIX_NEG_EQ_0];
        X_GEN_TAC `m:num` THEN DISCH_TAC THEN
        DISJ_CASES_TAC(ARITH_RULE `n - SUC m = n - m \/ m < n`) THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `n - m:num`) THEN
        ASM_SIMP_TAC[ARITH_RULE `m < n ==> ~(n - m = 0)`;
                     ARITH_RULE `n - m <= SUC n /\ n - m <= n`] THEN
        REWRITE_TAC[MATRIX_MUL_LZERO; MATRIX_ADD_LID; MATRIX_SUB_LZERO] THEN
        REWRITE_TAC[MATRIX_MUL_RID; MATRIX_NEG_EQ_0] THEN
        ASM_SIMP_TAC[ARITH_RULE `n - m - 1 = n - SUC m`]];
      DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[SUB_REFL] THEN
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
      ASM_REWRITE_TAC[LE_0; MATRIX_MUL_LZERO; MATRIX_ADD_RID] THEN
      REWRITE_TAC[MATRIX_SUB_RZERO; MATRIX_NEG_EQ_0]]]);;
```
### Informal statement
For any natural number `N`, for any `N`x`N` matrices `A`, `B`, and `C` of real numbers, and for any natural number `n`, if for all `x`, the matrix polynomial `msum (0..n) (\i. (x pow i) %% B i) ** (A - x %% mat 1)` equals `C`, then `C` is the zero matrix.

### Informal sketch
The proof proceeds by:
- Simplifying the equation `msum (0..n) (\i. (x pow i) %% B i) ** (A - x %% mat 1) = C` using properties of matrix arithmetic and sums.
- Establishing the goal `msum(0..SUC n) (\i. x pow i %% (((if i = 0 then --C else mat 0) + (if i <= n then B i ** A else mat 0)) - (if i = 0 then mat 0 else B(i - 1) ** mat 1))) = mat 0`.
- Simplifying the goal using properties of matrix arithmetic, distributivity, and conditional expressions.
- Using the theorem `MATRIC_POLYFUN_EQ_0` which states that a polynomial function is zero if and only if all coefficients are zero.
- Proving `!i:num. B(n - i) = (mat 0:real^N^N)` by induction on `n`.
  - **Base case (n = 0):** Show that `B 0 = mat 0` using simplification and matrix properties.
  - **Inductive step:** Assuming `!i:num. B(n - i) = (mat 0:real^N^N)`, show that `!i:num. B(SUC n - i) = (mat 0:real^N^N)`.
    - Consider two cases, one where `i > 0` and the other where `i = 0`.
    - Apply inductive hypothesis for `n - m`, where `m` is a dummy variable
    - Rewrite using matrix arithmetic and simplification.
- Applying the zero matrix property to conclude that C is the zero matrix.

### Mathematical insight
This theorem states that if a matrix polynomial equals a constant matrix `C` for all values of `x`, and that matrix polynomial is of the form `msum (0..n) (\i. (x pow i) %% B i) ** (A - x %% mat 1)`, then the constant matrix `C` must be the zero matrix. This is related to the uniqueness of polynomial representations and the properties of matrix multiplication and addition. The condition `A - x %% mat 1` multiplying `B` constrains the coefficients. Essentially it is the fact that if a polynomial is to evaluate as a constant, the constant must be zero unless the linear term is zero.

### Dependencies
- Definitions: `msum`, `mat`
- Theorems/Lemmas: `MSUM_MATRIX_RMUL`, `FINITE_NUMSEG`, `MATRIX_SUB_LDISTRIB`, `MATRIX_MUL_RMUL`, `MATRIX_MUL_LMUL`, `MATRIX_CMUL_ASSOC`, `CONJUNCT2 real_pow`, `MSUM_SUB`, `MATRIX_CMUL_SUB_LDISTRIB`, `MATRIX_CMUL_ADD_LDISTRIB`, `MSUM_ADD`,`GSYM MSUM_RESTRICT_SET`, `IN_NUMSEG`, `SING_GSPEC`, `GSYM numseg`, `MSUM_SING`, `real_pow`, `MATRIX_CMUL_LID`,`MATRIX_NEG_SUB`, `MATRIX_SUB`, `AC MATRIX_ADD_AC`,`MATRIX_ADD_LNEG`, `MATRIX_ADD_LID`,`MATRIC_POLYFUN_EQ_0`,`LE_0`
- Rules: `ARITH_RULE`, `num_CONV`, `num_INDUCTION`

### Porting notes (optional)
- The proof relies heavily on rewriting and simplification using properties of matrix arithmetic. Ensure that the target proof assistant has similar capabilities for handling matrix operations and arithmetic identities.
- The tactic `MESON[] `(if p then mat 0 else x) = (if ~p then x else mat 0)`` might need to be replaced as `MESON`is specific to HOL Light.
- The theorem `MATRIC_POLYFUN_EQ_0` (a polynomial function is zero if and only if all coefficients are zero) must be available where the polynomial is on matrices.
- The induction tactic (`MATCH_MP_TAC num_INDUCTION`) and arithmetic reasoning (`ARITH_RULE`) needs to be replaced by equivalents.


---

## POLYFUN_N_CONST

### Name of formal statement
POLYFUN_N_CONST

### Type of the formal statement
theorem

### Formal Content
```ocaml
let POLYFUN_N_CONST = prove
 (`!c n. ?b. !x. c = sum(0..n) (\i. b i * x pow i)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\i. if i = 0 then c else &0` THEN
  REWRITE_TAC[COND_RAND; COND_RATOR; REAL_MUL_LZERO] THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET; IN_NUMSEG] THEN
  REWRITE_TAC[ARITH_RULE `(0 <= i /\ i <= n) /\ i = 0 <=> i = 0`] THEN
  REWRITE_TAC[SING_GSPEC; SUM_SING; real_pow; REAL_MUL_RID]);;
```
### Informal statement
For any real number `c` and natural number `n`, there exists a function `b` from natural numbers to real numbers such that for all real numbers `x`, `c` is equal to the sum from 0 to `n` of `b i * x pow i`.

### Informal sketch
The proof demonstrates that any constant `c` can be represented as a degree `n` polynomial.
- Introduce the function `b` such that `b i = c` if `i = 0` and `b i = 0` otherwise.
- Simplify the summation `sum(0..n) (\i. b i * x pow i)` using properties of conditional expressions and arithmetic. Specifically, substitute definition of `b` to get `sum(0..n) (\i. (if i = 0 then c else &0) * x pow i)`.
- Simplify terms where the lambda function evaluates to zero.
- The summation then reduces to a single term where `i = 0`, i.e. `c * x pow 0`.
- Since `x pow 0 = 1`, the term simplifies to `c * 1 = c`.

### Mathematical insight
This theorem shows that for any constant `c` and natural number `n`, one can always find coefficients such that the polynomial evaluates to that constant, thereby expressing a constant as a finite sum polynomial by mapping the constant to the zero-indexed coefficient and all other coefficients to zero. This shows a simple representation of constants as polynomials.

### Dependencies
- `COND_RAND`
- `COND_RATOR`
- `REAL_MUL_LZERO`
- `GSYM SUM_RESTRICT_SET`
- `IN_NUMSEG`
- `ARITH_RULE`
- `SING_GSPEC`
- `SUM_SING`
- `real_pow`
- `REAL_MUL_RID`


---

## POLYFUN_N_ADD

### Name of formal statement
POLYFUN_N_ADD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let POLYFUN_N_ADD = prove
 (`!f g. (?b. !x. f(x) = sum(0..n) (\i. b i * x pow i)) /\
         (?c. !x. g(x) = sum(0..n) (\i. c i * x pow i))
         ==> ?d. !x. f(x) + g(x) = sum(0..n) (\i. d i * x pow i)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\i. (b:num->real) i + c i` THEN
  ASM_REWRITE_TAC[SUM_ADD_NUMSEG; REAL_ADD_RDISTRIB]);;
```

### Informal statement
For all functions `f` and `g`, if there exists a function `b` from natural numbers to real numbers such that for all `x`, `f(x)` is equal to the sum from `0` to `n` of the terms `b(i) * x^i`, and there exists a function `c` from natural numbers to real numbers such that for all `x`, `g(x)` is equal to the sum from `0` to `n` of the terms `c(i) * x^i`, then there exists a function `d` from natural numbers to real numbers such that for all `x`, `f(x) + g(x)` is equal to the sum from `0` to `n` of the terms `d(i) * x^i`.

### Informal sketch
The proof demonstrates that the sum of two polynomials of degree at most `n` is also a polynomial of degree at most `n`.

- Assume that `f` and `g` are polynomials of degree at most `n` with coefficients `b` and `c` respectively.
- Exhibit coefficients `d` defined as `d(i) = b(i) + c(i)`.
- Show that with this definition of `d`, `f(x) + g(x)` equals the sum from `0` to `n` of `d(i) * x^i`.
- The proof rewrites the expression `f(x) + g(x)` using the assumption, and then combines the two sums using `SUM_ADD_NUMSEG` and `REAL_ADD_RDISTRIB`.

### Mathematical insight
This theorem states that the set of polynomials of degree at most `n` forms a vector space (specifically, it's closed under addition). The coefficients of the sum of two polynomials are simply the sums of the corresponding coefficients of the original polynomials.

### Dependencies
- `SUM_ADD_NUMSEG`: Theorem about adding two sums with the same bounds.
- `REAL_ADD_RDISTRIB`:  Theorem stating the right distributivity law for addition over multiplication in real numbers.

### Porting notes (optional)
The main work in porting this theorem lies in ensuring the correct versions, or constructions, of `SUM_ADD_NUMSEG` and `REAL_ADD_RDISTRIB` are present in the target proof assistant. The handling of existential quantifiers and rewriting should be straightforward in most systems (e.g., Lean, Coq, Isabelle).


---

## POLYFUN_N_CMUL

### Name of formal statement
POLYFUN_N_CMUL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let POLYFUN_N_CMUL = prove
 (`!f c. (?b. !x. f(x) = sum(0..n) (\i. b i * x pow i))
         ==> ?b. !x. c * f(x) = sum(0..n) (\i. b i * x pow i)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\i. c * (b:num->real) i` THEN
  ASM_REWRITE_TAC[SUM_LMUL; GSYM REAL_MUL_ASSOC]);;
```

### Informal statement
For all functions `f` from real numbers to real numbers and for all real numbers `c`, if there exists a function `b` from natural numbers to real numbers such that for all real numbers `x`, `f(x)` is equal to the sum from 0 to `n` of `b(i) * x^i`, then there exists a function `b` from natural numbers to real numbers such that for all real numbers `x`, `c * f(x)` is equal to the sum from 0 to `n` of `b(i) * x^i`.

### Informal sketch
The proof proceeds as follows:

- Assume that there exists a function `b` such that for all `x`, `f(x) = sum(0..n) (\i. b i * x pow i)`.
- We want to show that there exists a function `b'` such that for all `x`, `c * f(x) = sum(0..n) (\i. b' i * x pow i)`.
- Choose `b'` to be the function defined by `b'(i) = c * b(i)`.
- Now, we need to show that `c * f(x) = sum(0..n) (\i. (c * b i) * x pow i)`.
- Rewrite `c * f(x)` using the assumption to get `c * sum(0..n) (\i. b i * x pow i)`.
- Apply `SUM_LMUL` to rewrite the sum to `sum(0..n) (\i. c * (b i * x pow i))`.
- Use associativity of real multiplication, `GSYM REAL_MUL_ASSOC`, to rewrite this to `sum(0..n) (\i. (c * b i) * x pow i)`.
- This completes the proof.

### Mathematical insight
This theorem states that if a function `f` can be represented as a polynomial of degree `n`, then `c * f` can also be represented as a polynomial of degree `n`. This is achieved by simply multiplying each coefficient of the original polynomial by `c`. This is a fundamental property of polynomials and scalar multiplication.

### Dependencies
- `SUM_LMUL`
- `REAL_MUL_ASSOC`


---

## POLYFUN_N_SUM

### Name of formal statement
POLYFUN_N_SUM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let POLYFUN_N_SUM = prove
 (`!f s. FINITE s /\
         (!a. a IN s ==> ?b. !x. f x a = sum(0..n) (\i. b i * x pow i))
         ==> ?b. !x. sum s (f x) = sum(0..n) (\i. b i * x pow i)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; FORALL_IN_INSERT; NOT_IN_EMPTY; POLYFUN_N_CONST] THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC POLYFUN_N_ADD THEN ASM_SIMP_TAC[]);;
```
### Informal statement
For all functions `f` and sets `s`, if `s` is finite and for all `a` in `s` there exists `b` such that for all `x`, `f x a` is equal to the sum from `0` to `n` of (`b i * x pow i`), then there exists `b'` such that for all `x`, the sum over `s` of `f x` is equal to the sum from `0` to `n` of (`b' i * x pow i`).

### Informal sketch
The theorem states that if a finite set of functions `f x a` are all polynomials in `x` of degree at most `n` (where `a` ranges over the finite set `s`), then the sum of these functions over `s` is also a polynomial in `x` of degree at most `n`.

The proof proceeds by induction on the finite set `s`.

*   Base case: If `s` is empty, the sum over `s` is `0`, which is a polynomial of degree at most `n` (all coefficients are zero).
*   Inductive step: Assume the theorem holds for `s`. We must show it holds for `INSERT a s`.  We are given that `f x a` is a polynomial of degree at most `n` and, by the inductive hypothesis, `sum s (f x)` is a polynomial of degree at most `n`.  We need to show that `sum (INSERT a s) (f x)` is a polynomial of degree at most `n`.
    Since `sum (INSERT a s) (f x) = f x a + sum s (f x)`, this follows directly from the fact that the sum of two polynomials of degree at most `n` is also a polynomial of degree at most `n`. This is formalized by `POLYFUN_N_ADD`.

### Mathematical insight
The theorem demonstrates a key property of polynomials which is closure under finite summation. The insight is that if each element of a finite set is a polynomial of degree at most `n`, then the sum over that set is also a polynomial of degree at most `n`. This is useful because it allows reasoning about the degree and coefficients of polynomials resulting from summation.

### Dependencies
*   `FINITE_INDUCT_STRONG`
*   `SUM_CLAUSES`
*   `FORALL_IN_INSERT`
*   `NOT_IN_EMPTY`
*   `POLYFUN_N_CONST`
*   `POLYFUN_N_ADD`
*   `IMP_CONJ`


---

## POLYFUN_N_PRODUCT

### Name of formal statement
POLYFUN_N_PRODUCT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let POLYFUN_N_PRODUCT = prove
 (`!f s n. FINITE s /\
           (!a:A. a IN s ==> ?c d. !x. f x a = c + d * x) /\ CARD(s) <= n
           ==> ?b. !x. product s (f x) = sum(0..n) (\i. b i * x pow i)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; POLYFUN_N_CONST; FORALL_IN_INSERT] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES] THEN
  INDUCT_TAC THENL [ARITH_TAC; REWRITE_TAC[LE_SUC]] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `b:num->real`) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `c:real` (X_CHOOSE_TAC `d:real`)) THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `\i. (if i <= n then c * b i else &0) +
                  (if ~(i = 0) then d * b(i - 1) else &0)` THEN
  X_GEN_TAC `x:real` THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB; SUM_ADD_NUMSEG] THEN
  REWRITE_TAC[COND_RAND; COND_RATOR; GSYM SUM_LMUL; REAL_MUL_LZERO] THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET; IN_NUMSEG] THEN
  REWRITE_TAC[ARITH_RULE
   `((0 <= i /\ i <= SUC n) /\ i <= n <=> 0 <= i /\ i <= n) /\
    ((0 <= i /\ i <= SUC n) /\ ~(i = 0) <=> 1 <= i /\ i <= SUC n)`] THEN
  REWRITE_TAC[GSYM numseg] THEN
  REWRITE_TAC[MESON[num_CONV `1`; ADD1] `1..SUC n = 0+1..n+1`] THEN
  REWRITE_TAC[SUM_OFFSET; ADD_SUB; REAL_POW_ADD] THEN
  BINOP_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN REAL_ARITH_TAC);;
```

### Informal statement
For any function `f`, set `s`, and natural number `n`, if `s` is finite, and for every `a` in `s`, there exist real numbers `c` and `d` such that for all `x`, `f x a = c + d * x`, and the cardinality of `s` is less than or equal to `n`, then there exists a function `b` from natural numbers to real numbers such that for all `x`, the product of `f x` over `s` is equal to the sum from 0 to `n` of `b i * x pow i`.

### Informal sketch
The theorem states that if a function `f` applied to elements of a finite set `s` yields linear functions (of the form `c + d * x`), and the size of the set is bounded by `n`, then the product of these linear functions over the set `s` can be expressed as a polynomial in `x` of degree at most `n`.

The proof proceeds by strong induction on the finiteness of the set `s`.

- Base case: `s` is empty. The `product` over an empty set is 1, which can be represented as a constant polynomial.
- Inductive step: Assume the theorem holds for all sets `s'` such that `s'` is finite and `CARD(s') <= n`. We want to prove it for `insert a s'`, where `a` is not in `s`, and `CARD(insert a s') <= n`. Also assume that for all `x`, `f x a = c + d * x` for some real numbers `c` and `d`.
    - The product over `insert a s'` is `f x a * product s' (f x)`.
    - By the inductive hypothesis, `product s' (f x) = sum(0..n) (\i. b i * x pow i)` for some function `b`.
    - We need to show that `(c + d * x) * sum(0..n) (\i. b i * x pow i)` can be expressed as `sum(0..n) (\i. b' i * x pow i)` for some function `b'`.
    - The proof constructs the required function `b'` explicitly as `\i. (if i <= n then c * b i else &0) + (if ~(i = 0) then d * b(i - 1) else &0)`.
    - After expanding the product and rearranging the summation, this can be shown using arithmetic reasoning and `SUM_EQ_NUMSEG`.

### Mathematical insight
The theorem shows how a product of linear functions, indexed by a finite set, can be represented as a polynomial. The degree of the resulting polynomial is bounded by the cardinality of the set. This is a fundamental concept in polynomial algebra, particularly related to the representation of functions and algebraic structures.

### Dependencies

**Theorems:**
- `FINITE_INDUCT_STRONG`
- `IMP_CONJ`
- `RIGHT_FORALL_IMP_THM`

**Definitions:**
- `FINITE`
- `CARD`
- `product`
- `sum`
- `pow`

**Other Rules:**
- `PRODUCT_CLAUSES`
- `POLYFUN_N_CONST`
- `FORALL_IN_INSERT`
- `CARD_CLAUSES`
- `LE_SUC`
- `REAL_ADD_RDISTRIB`
- `SUM_ADD_NUMSEG`
- `COND_RAND`
- `COND_RATOR`
- `SUM_LMUL`
- `REAL_MUL_LZERO`
- `SUM_RESTRICT_SET`
- `IN_NUMSEG`
- `numseg`
- `ADD1`
- `REAL_POW_ADD`

**Conversion:**
-  `num_CONV \`1\``

### Porting notes (optional)
- The proof relies on strong induction on finiteness and arithmetic reasoning. A port to another theorem prover will require equivalent induction principles and simplification lemmas about sums and products.
- The explicit construction of the polynomial coefficients (function `b'`) may require careful handling of dependent types or explicit quantifiers, depending on the target system.
- The tactics `X_CHOOSE_TAC` and `X_CHOOSE_THEN` perform Skolemization, which may need to be translated into appropriate existential introduction rules in other systems.



---

## COFACTOR_ENTRY_AS_POLYFUN

### Name of formal statement
COFACTOR_ENTRY_AS_POLYFUN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COFACTOR_ENTRY_AS_POLYFUN = prove
 (`!A:real^N^N x i j.
        1 <= i /\ i <= dimindex(:N) /\
        1 <= j /\ j <= dimindex(:N)
        ==> ?c. !x. cofactor(A - x %% mat 1)$i$j =
                    sum(0..dimindex(:N)-1) (\i. c(i) * x pow i)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[cofactor; LAMBDA_BETA; det] THEN
  MATCH_MP_TAC POLYFUN_N_SUM THEN
  SIMP_TAC[FINITE_PERMUTATIONS; FINITE_NUMSEG; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN
  MATCH_MP_TAC POLYFUN_N_CMUL THEN
  SUBGOAL_THEN `1..dimindex(:N) = i INSERT ((1..dimindex(:N)) DELETE i)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_DELETE; IN_NUMSEG] THEN ASM_ARITH_TAC;
    SIMP_TAC[PRODUCT_CLAUSES; FINITE_DELETE; FINITE_NUMSEG]] THEN
  ASM_REWRITE_TAC[IN_DELETE; IN_NUMSEG] THEN
  MATCH_MP_TAC POLYFUN_N_CMUL THEN
  MATCH_MP_TAC POLYFUN_N_PRODUCT THEN
  SIMP_TAC[CARD_DELETE; FINITE_DELETE; FINITE_NUMSEG] THEN
  ASM_REWRITE_TAC[IN_NUMSEG; IN_DELETE; CARD_NUMSEG_1; LE_REFL] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:num->num) k IN 1..dimindex(:N)` MP_TAC THENL
   [ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG]; ALL_TAC] THEN
  ASM_SIMP_TAC[IN_NUMSEG; LAMBDA_BETA] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(p:num->num) k = j` THEN ASM_REWRITE_TAC[] THENL
   [REPEAT(EXISTS_TAC `&0`) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_SUB_COMPONENT; MATRIX_CMUL_COMPONENT; MAT_COMPONENT] THEN
  REWRITE_TAC[REAL_ARITH `a - x * d:real = a + (--d) * x`] THEN MESON_TAC[]);;
```

### Informal statement
For any natural number `N`, any `N` by `N` matrix `A` of real numbers, any real number `x`, and any natural numbers `i` and `j`, if `i` is between 1 and `N` (inclusive) and `j` is between 1 and `N` (inclusive), then there exists a function `c` from natural numbers to real numbers such that, for all `x`, the `(i,j)` entry of the cofactor matrix of `A - x * I` (where `I` is the `N` by `N` identity matrix) is equal to the sum from 0 to `N-1` of `c(i) * x^i`.

### Informal sketch
The theorem states that each entry of the cofactor matrix of `A - x*I` is a polynomial in `x`. The proof proceeds as follows:
- Strip the quantifiers and assumptions.
- Simplify using the definitions of `cofactor`, `LAMBDA_BETA`, and `det`.
- Apply `POLYFUN_N_SUM` to express the determinant as a polynomial.
- Use lemmas about `FINITE_PERMUTATIONS`, `FINITE_NUMSEG`, and `FORALL_IN_GSPEC`.
- Introduce an explicit function `p:num->num` using `X_GEN_TAC` and discharge the assumption.
- Apply `POLYFUN_N_CMUL`.
- Show the equivalence of `1..dimindex(:N) = i INSERT ((1..dimindex(:N)) DELETE i)` via rewriting with `EXTENSION`, `IN_INSERT`, `IN_DELETE`, and `IN_NUMSEG` and some arithmetic reasoning and simplification.
- Eliminate `i` from the above equality.
- Apply `POLYFUN_N_CMUL`, and `POLYFUN_N_PRODUCT`.
- Simplify with theorems about `CARD_DELETE`, `FINITE_DELETE`, and `FINITE_NUMSEG`.
- Simplify with theorems about `IN_NUMSEG`, `IN_DELETE`, `CARD_NUMSEG_1` and `LE_REFL`.
- Introduce `k:num` and strip. Prove that `(p:num->num) k IN 1..dimindex(:N)` and use it via `MP_TAC`.
- Simplify with `IN_NUMSEG` and `LAMBDA_BETA`.
- Case split on `(p:num->num) k = j`. Then simplify with `MATRIX_SUB_COMPONENT`, `MATRIX_CMUL_COMPONENT`, and `MAT_COMPONENT`. Rewrite using `REAL_ARITH` to rewrite `a - x * d:real = a + (--d) * x`. Finally finish the proof with `MESON_TAC`.

### Mathematical insight
The theorem expresses the fact that the entries of the adjugate matrix of `A - xI` are polynomials in `x`. Specifically, the adjugate of `A - xI` consists of the cofactors, and the cofactor expansion of the determinant shows that the determinant, hence each cofactor, is a polynomial in `x`. This result is important in linear algebra and matrix analysis. For example it relates to computing eigenvalues via finding the roots of characteristic polynomial.

### Dependencies
- Definitions: `cofactor`, `det`
- Theorems: `POLYFUN_N_SUM`, `FINITE_PERMUTATIONS`, `FINITE_NUMSEG`, `FORALL_IN_GSPEC`, `POLYFUN_N_CMUL`, `EXTENSION`, `IN_INSERT`, `IN_DELETE`, `PRODUCT_CLAUSES`, `FINITE_DELETE`, `CARD_DELETE`, `CARD_NUMSEG_1`, `LE_REFL`, `PERMUTES_IN_IMAGE`, `MATRIX_SUB_COMPONENT`, `MATRIX_CMUL_COMPONENT`, `MAT_COMPONENT`

### Porting notes (optional)
- The proof relies heavily on the `POLYFUN` library, which provides theorems about polynomials. Ensure that similar results are available in the target proof assistant.
- Tactics such as `ASM_CASES_TAC` and `MESON_TAC` are powerful automation tools in HOL Light. Replicating their effect might require more explicit reasoning in other systems.


---

## DETERMINANT_AS_POLYFUN

### Name of formal statement
DETERMINANT_AS_POLYFUN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DETERMINANT_AS_POLYFUN = prove
 (`!A:real^N^N.
        ?c. !x. det(A - x %% mat 1) =
                sum(0..dimindex(:N)) (\i. c(i) * x pow i)`,
  GEN_TAC THEN REWRITE_TAC[det] THEN
  MATCH_MP_TAC POLYFUN_N_SUM THEN
  SIMP_TAC[FINITE_PERMUTATIONS; FINITE_NUMSEG; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN
  MATCH_MP_TAC POLYFUN_N_CMUL THEN MATCH_MP_TAC POLYFUN_N_PRODUCT THEN
  SIMP_TAC[FINITE_NUMSEG; CARD_NUMSEG_1; LE_REFL; IN_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:num->num) k IN 1..dimindex(:N)` MP_TAC THENL
   [ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG]; ALL_TAC] THEN
  ASM_SIMP_TAC[IN_NUMSEG; LAMBDA_BETA] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MATRIX_SUB_COMPONENT; MATRIX_CMUL_COMPONENT; MAT_COMPONENT] THEN
  REWRITE_TAC[REAL_ARITH `a - x * d:real = a + (--d) * x`] THEN MESON_TAC[]);;
```

### Informal statement
For every real matrix `A` of size `N` by `N`, there exists a function `c` from natural numbers to real numbers such that for all real numbers `x`, the determinant of the matrix `A` minus `x` times the identity matrix is equal to the sum, from `0` to `dimindex(:N)`, of `c(i)` times `x` to the power of `i`.

### Informal sketch
The proof demonstrates that the determinant of a matrix `A - x * I` is a polynomial in `x`. This is proven by:
- Rewriting `det(A - x %% mat 1)` to its explicit definition using `det`.
- Applying `POLYFUN_N_SUM` to express the determinant as a sum of polynomials.
- Simplifying using theorems about finite permutations (`FINITE_PERMUTATIONS`), finite number segments (`FINITE_NUMSEG`), and universal quantification (`FORALL_IN_GSPEC`).
- Introducing a function `p` representing a permutation.
- Applying `POLYFUN_N_CMUL` and `POLYFUN_N_PRODUCT` to handle scalar multiplication and products within the summation.
- Simplifying with theorems about finite number segments and inequalities.
- Introducing a variable `k` representing a natural number.
- Proving the subgoal `(p:num->num) k IN 1..dimindex(:N)` using `PERMUTES_IN_IMAGE` and `IN_NUMSEG`.
- Simplifying using theorems related to number segments and lambda expressions.
- Simplifying using properties of matrix subtraction, scalar multiplication, and the identity matrix.
- Rewriting `a - x * d:real = a + (--d) * x` to prepare for the final step.
- Completing the proof using `MESON_TAC`.

### Mathematical insight
This theorem establishes that the characteristic polynomial of a matrix is indeed a polynomial. The coefficients of this polynomial are expressible in terms of the entries of the matrix A. This result is a fundamental component in linear algebra and eigenvalue theory.

### Dependencies
- `det`
- `POLYFUN_N_SUM`
- `FINITE_PERMUTATIONS`
- `FINITE_NUMSEG`
- `FORALL_IN_GSPEC`
- `POLYFUN_N_CMUL`
- `POLYFUN_N_PRODUCT`
- `CARD_NUMSEG_1`
- `LE_REFL`
- `IN_NUMSEG`
- `PERMUTES_IN_IMAGE`
- `LAMBDA_BETA`
- `MATRIX_SUB_COMPONENT`
- `MATRIX_CMUL_COMPONENT`
- `MAT_COMPONENT`
- `REAL_ARITH`

### Porting notes (optional)
- The proof relies heavily on properties of finite sets and permutations. Ensure that the target proof assistant has adequate support for these concepts.
- The `MESON_TAC` call suggests a significant amount of automated reasoning is involved in the final step. Replicating this step may require careful attention.
- The theorem `REAL_ARITH` indicates that specific real arithmetic rewriting rules are used which is good to be checked when porting.


---

## char_poly

### Name of formal statement
char_poly

### Type of the formal statement
new_specification

### Formal Content
```ocaml
let char_poly = new_specification ["char_poly"]
  (REWRITE_RULE[SKOLEM_THM] DETERMINANT_AS_POLYFUN);;
```

### Informal statement
The function `char_poly` is specified by rewriting the term using the `REWRITE_RULE[SKOLEM_THM]` applied to `DETERMINANT_AS_POLYFUN`. This effectively defines `char_poly` to be the characteristic polynomial obtained from the determinant function, represented as a polynomial function.

### Informal sketch
- The `new_specification` mechanism in HOL Light introduces a new function (`char_poly`) satisfying a given equation.
- The equation is derived by rewriting the term via `REWRITE_RULE[SKOLEM_THM]` with `DETERMINANT_AS_POLYFUN`.
- `DETERMINANT_AS_POLYFUN` expresses that the determinant of a matrix can be viewed as a polynomial function of its entries.
- `REWRITE_RULE[SKOLEM_THM]` likely applies Skolemization and rewriting to transform the determinant expression into a suitable form for defining the coefficients of the polynomial. The rewriting process is critical to ensure that `char_poly` is well-defined.

### Mathematical insight
The core idea is to define the characteristic polynomial of a matrix directly through its determinant. The determinant is expressed as a polynomial function of the matrix entries. This ensures the existence of `char_poly` and provides a computational route for deriving its coefficients.

### Dependencies
- `DETERMINANT_AS_POLYFUN`
- `SKOLEM_THM`


---

## COFACTOR_AS_MATRIC_POLYNOMIAL

### Name of formal statement
COFACTOR_AS_MATRIC_POLYNOMIAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COFACTOR_AS_MATRIC_POLYNOMIAL = prove
 (`!A:real^N^N. ?C.
      !x. cofactor(A - x %% mat 1) =
          msum(0..dimindex(:N)-1) (\i. x pow i %% C i)`,
  GEN_TAC THEN SIMP_TAC[CART_EQ; MSUM_COMPONENT; FINITE_NUMSEG] THEN
  MP_TAC(ISPEC `A:real^N^N` COFACTOR_ENTRY_AS_POLYFUN) THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[IMP_IMP] THEN REWRITE_TAC[LAMBDA_SKOLEM] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(num->real)^N^N` ASSUME_TAC) THEN
  EXISTS_TAC `(\i. lambda j k. ((c:(num->real)^N^N)$j$k) i):num->real^N^N` THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `i:num`] THEN STRIP_TAC THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MATRIX_CMUL_COMPONENT; LAMBDA_BETA] THEN REAL_ARITH_TAC);;
```
### Informal statement
For any square matrix `A` of real numbers with dimension `N` by `N`, there exists a function `C` from natural numbers to real-valued `N` by `N` matrices, such that for all real numbers `x`, the cofactor of the matrix `A - x` times the identity matrix is equal to the sum, from `0` to `dimindex(:N) - 1`, of `x` raised to the power of `i`, multiplied by the matrix `C i`.

### Informal sketch
- The goal is to prove the existence of a matrix polynomial representation for the cofactor of `A - xI`. The proof starts by using `COFACTOR_ENTRY_AS_POLYFUN`, which expresses each entry of the cofactor matrix as a polynomial in `x`.
- Then, the proof introduces a Skolem function `c` to represent the coefficients of the polynomial for each entry.
- An existential quantifier is introduced to assert the existence of a function that maps `i` to a matrix whose `j`, `k` entry is the `i`-th coefficient of the polynomial representing the `j`, `k` entry of the cofactor matrix.
- The proof proceeds by stripping quantifiers and simplifying the expression involving the matrix sum (`msum`).
- The proof then relies on `SUM_EQ_NUMSEG` to equate the indexed summation, and then makes use of `MATRIX_CMUL_COMPONENT` and `LAMBDA_BETA` to reduce the matrix expressions to equality.
- Finally, `REAL_ARITH_TAC` completes the proof by using real arithmetic reasoning.

### Mathematical insight
This theorem shows that the cofactor matrix of `A - xI` can be expressed as a matrix polynomial in `x`. This is a crucial step in proving the Cayley-Hamilton theorem, which states that every square matrix satisfies its own characteristic equation. The theorem provides a concrete form for the coefficient matrices in the polynomial.

### Dependencies
- `CART_EQ`
- `MSUM_COMPONENT`
- `FINITE_NUMSEG`
- `COFACTOR_ENTRY_AS_POLYFUN`
- `IMP_CONJ`
- `RIGHT_FORALL_IMP_THM`
- `IMP_IMP`
- `LAMBDA_SKOLEM`
- `SUM_EQ_NUMSEG`
- `MATRIX_CMUL_COMPONENT`
- `LAMBDA_BETA`


---

## MATRIC_POWER_DIFFERENCE

### Name of formal statement
MATRIC_POWER_DIFFERENCE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MATRIC_POWER_DIFFERENCE = prove
 (`!A:real^N^N x n.
        A mpow (SUC n) - x pow (SUC n) %% mat 1 =
        msum (0..n) (\i. x pow i %% A mpow (n - i)) ** (A - x %% mat 1)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MSUM_CLAUSES_NUMSEG; real_pow; SUB_0; mpow] THEN
    REWRITE_TAC[MATRIX_MUL_RID; MATRIX_CMUL_LID; MATRIX_MUL_LID] THEN
    REWRITE_TAC[REAL_MUL_RID];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `(A mpow SUC n - x pow SUC n %% mat 1) ** A +
      (x pow (SUC n) %% mat 1 :real^N^N) ** (A - x %% mat 1:real^N^N)` THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MPOW_SUC] THEN
      REWRITE_TAC[MATRIX_SUB_RDISTRIB; MATRIX_SUB_LDISTRIB] THEN
      REWRITE_TAC[MATRIX_SUB; MATRIX_MUL_LMUL; MATRIX_MUL_LID] THEN
      REWRITE_TAC[GSYM MATRIX_ADD_ASSOC] THEN AP_TERM_TAC THEN
      REWRITE_TAC[MATRIX_ADD_ASSOC; MATRIX_ADD_LNEG; MATRIX_ADD_LID] THEN
      REWRITE_TAC[real_pow; MATRIX_CMUL_ASSOC] THEN REWRITE_TAC[REAL_MUL_AC];

      ASM_REWRITE_TAC[MSUM_CLAUSES_NUMSEG; LE_0] THEN
      REWRITE_TAC[SUB_REFL; mpow; MATRIX_ADD_RDISTRIB] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      SIMP_TAC[GSYM MSUM_MATRIX_RMUL; FINITE_NUMSEG] THEN
      MATCH_MP_TAC MSUM_EQ THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[MATRIX_MUL_LMUL] THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[ARITH_RULE `i <= n ==> SUC n - i = SUC(n - i)`] THEN
      REWRITE_TAC[MPOW_SUC; GSYM MATRIX_MUL_ASSOC] THEN AP_TERM_TAC THEN
      REWRITE_TAC[MATRIX_SUB_LDISTRIB; MATRIX_SUB_RDISTRIB] THEN
      REWRITE_TAC[MATRIX_MUL_RMUL; MATRIX_MUL_LMUL] THEN
      REWRITE_TAC[MATRIX_MUL_LID; MATRIX_MUL_RID]]]);;
```

### Informal statement
For all square matrices `A` of real numbers of size `N`x`N` and for all natural numbers `n`, the difference between `A` raised to the power of `SUC n` (i.e. n+1) and the scalar matrix `x` raised to the power of `SUC n` times the identity matrix of the same size, equals the matrix product of the sum from `0` to `n` of the matrices where each is the matrix product of `x` raised to the power of `i` times `A` raised to the power of `n-i`, with the matrix result of subtracting the scalar matrix `x` multiplied by the identity matrix from `A`.

### Informal sketch
The proof proceeds by induction on `n`.
- Base case: For `n = 0`, the statement reduces to showing that `A - x %% mat 1 = (A - x %% mat 1)`, which is trivial.
- Inductive step: Assume the statement holds for `n`. We need to prove it for `SUC n`.
  - The goal is to show that `A mpow (SUC (SUC n)) - x pow (SUC (SUC n)) %% mat 1 = msum (0..SUC n) (\i. x pow i %% A mpow (SUC n - i)) ** (A - x %% mat 1)`.
  - This is proved by rewriting and rearranging terms.
  - Express the left-hand side as `(A mpow (SUC n)) ** A - (x pow (SUC n)) * x %% mat 1`.
  - Rewrite both sides of the equation to introduce the induction hypothesis. This involves manipulating the summation term and using properties of matrix multiplication and scalar multiplication.
  - Showing that the rearranged terms on both sides are equal requires distributivity of scalar and matrix multiplication, associativity of matrix multiplication, and rewriting the summation term.

### Mathematical insight
The theorem expresses a factorization of the difference of matrix powers, similar to the algebraic identity `a^(n+1) - b^(n+1) = (sum_{i=0}^n a^i b^(n-i)) * (a-b)`. This theorem generalizes that concept to matrices, replacing scalar multiplication with matrix multiplication, and scalar powers with matrix powers.  The result is a formula expressing `A^(n+1) - x^(n+1) * I` as a product involving `A - x*I` and a sum of mixed powers of `A` and `x`, where `I` is the identity matrix.

### Dependencies
- `MSUM_CLAUSES_NUMSEG`
- `real_pow`
- `SUB_0`
- `mpow`
- `MATRIX_MUL_RID`
- `MATRIX_CMUL_LID`
- `MATRIX_MUL_LID`
- `REAL_MUL_RID`
- `MPOW_SUC`
- `MATRIX_SUB_RDISTRIB`
- `MATRIX_SUB_LDISTRIB`
- `MATRIX_SUB`
- `MATRIX_MUL_LMUL`
- `MATRIX_MUL_LID`
- `MATRIX_ADD_ASSOC`
- `MATRIX_ADD_LNEG`
- `MATRIX_ADD_LID`
- `MATRIX_CMUL_ASSOC`
- `REAL_MUL_AC`
- `LE_0`
- `SUB_REFL`
- `MATRIX_ADD_RDISTRIB`
- `MSUM_MATRIX_RMUL`
- `FINITE_NUMSEG`
- `MSUM_EQ`
- `IN_NUMSEG`
- `MATRIX_MUL_RMUL`
- `GSYM MATRIX_MUL_ASSOC`

### Porting notes (optional)
- The extensive use of rewriting may require careful consideration in other proof assistants to ensure efficient proof automation.
- The `GSYM` (reverse equality) tactic is used frequently, which the porter must account for in the destination proof assistant.
- The properties of `msum` and `mpow` will need to be established within the target environment and linked properly.


---

## MATRIC_CHARPOLY_DIFFERENCE

### Name of formal statement
MATRIC_CHARPOLY_DIFFERENCE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MATRIC_CHARPOLY_DIFFERENCE = prove
 (`!A:real^N^N. ?B.
      !x. msum(0..dimindex(:N)) (\i. char_poly A i %% A mpow i) -
          sum(0..dimindex(:N)) (\i. char_poly A i * x pow i) %% mat 1 =
          msum(0..(dimindex(:N)-1)) (\i. x pow i %% B i) ** (A - x %% mat 1)`,
  GEN_TAC THEN SPEC_TAC(`dimindex(:N)`,`n:num`) THEN
  SPEC_TAC(`char_poly(A:real^N^N)`,`c:num->real`) THEN
  GEN_TAC THEN INDUCT_TAC THEN
  SIMP_TAC[MSUM_CLAUSES_NUMSEG; SUM_CLAUSES_NUMSEG; LE_0] THENL
   [EXISTS_TAC `(\i. mat 0):num->real^N^N` THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MSUM_CLAUSES_NUMSEG] THEN
    REWRITE_TAC[real_pow; MATRIX_MUL_LMUL; MATRIX_MUL_LZERO; mpow;
                REAL_MUL_RID; MATRIX_CMUL_RZERO; MATRIX_SUB_REFL];
    FIRST_X_ASSUM(X_CHOOSE_TAC `B:num->real^N^N`) THEN
    REWRITE_TAC[MATRIX_SUB; MATRIX_NEG_ADD; MATRIX_CMUL_ADD_RDISTRIB] THEN
    ONCE_REWRITE_TAC[AC MATRIX_ADD_AC
     `(A + B) + (C + D):real^N^N = (A + C) + (B + D)`] THEN
    ASM_REWRITE_TAC[GSYM MATRIX_SUB] THEN
    REWRITE_TAC[GSYM MATRIX_CMUL_ASSOC; GSYM MATRIX_CMUL_SUB_LDISTRIB] THEN
    REWRITE_TAC[MATRIC_POWER_DIFFERENCE; SUC_SUB1] THEN
    EXISTS_TAC `(\i. (if i <= n - 1 then B i else mat 0) +
                     c(SUC n) %% A mpow (n - i)):num->real^N^N` THEN
    X_GEN_TAC `x:real` THEN REWRITE_TAC[MATRIX_CMUL_ADD_LDISTRIB] THEN
    SIMP_TAC[MSUM_ADD; FINITE_NUMSEG; MATRIX_ADD_RDISTRIB] THEN
    REWRITE_TAC[GSYM MATRIX_MUL_LMUL] THEN
    BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THENL
     [REWRITE_TAC[COND_RAND; COND_RATOR; MATRIX_CMUL_RZERO] THEN
      REWRITE_TAC[GSYM MSUM_RESTRICT_SET; IN_NUMSEG] THEN
      REWRITE_TAC[numseg; ARITH_RULE
       `(0 <= i /\ i <= n) /\ i <= n - 1 <=> 0 <= i /\ i <= n - 1`];
      SIMP_TAC[GSYM MSUM_LMUL; FINITE_NUMSEG; MATRIX_CMUL_ASSOC] THEN
      REWRITE_TAC[REAL_MUL_SYM]]]);;
```
### Informal statement
For any square matrix `A` of real numbers with dimensions `N` by `N`, there exists a function `B` from natural numbers to matrices of real numbers with dimensions `N` by `N`, such that for all real numbers `x`, the difference between `msum` from `0` to `dimindex(:N)` of the expression `char_poly A i` multiplied by `A` raised to the power of `i` and the `sum` from `0` to `dimindex(:N)` of the expression `char_poly A i` multiplied by `x` raised to the power of `i`, all multiplied elementwise by the matrix `1`, is equal to `msum` from `0` to `dimindex(:N)` minus `1` of the expression `x` raised to the power of `i` multiplied elementwise by `B i` multiplied on the right by the difference between `A` and `x` multiplied elementwise by the matrix `1`.

### Informal sketch
The theorem asserts the existence of a matrix-valued function `B` that satisfies a certain polynomial equation related to the characteristic polynomial of a matrix `A`. The proof proceeds by induction on `n = dimindex(:N)`.

- **Base case:**  When `n = 0`, we choose `B` to be the function that always returns the zero matrix (`mat 0`).  The goal is simplified using arithmetic and properties of matrix operations such as `MATRIX_MUL_LMUL`, `MATRIX_MUL_LZERO`, `MATRIX_CMUL_RZERO` and `MATRIX_SUB_REFL`.
- **Inductive step:**  Assume the theorem holds for `n`. We need to prove it for `SUC n`. We are given a suitable `B` for `n` (using `X_CHOOSE_TAC`).  We then construct a new function `B'` for `SUC n` as follows: `B' i = (if i <= n - 1 then B i else mat 0) + c(SUC n) %% A mpow (n - i)`, where `c` denotes the characteristic polynomial, `A` is the matrix and `mpow` is matrix power. The subsequent steps involve algebraic manipulations, including distributing scalar multiplication over matrix addition (`MATRIX_CMUL_ADD_LDISTRIB`, `MATRIX_CMUL_ADD_RDISTRIB`), and using `MATRIC_POWER_DIFFERENCE` and properties of summation (`MSUM_ADD`, `MATRIX_ADD_RDISTRIB`).  The proof also handles edge cases (using `COND_RAND`, `COND_RATOR`, etc.) to reconcile the sums.

### Mathematical insight
The theorem appears to express a relation between the characteristic polynomial of a matrix `A` and its powers. Specifically, it relates the sum and `msum` of matrix powers weighted by the coefficients of `A`'s characteristic polynomial and their relationship to the difference `A - xI` (where `I` is the unit matrix). The function `B` can be viewed as a kind of remainder when dividing the polynomial msum representation by (A - xI).

### Dependencies
- `MSUM_CLAUSES_NUMSEG`
- `SUM_CLAUSES_NUMSEG`
- `LE_0`
- `real_pow`
- `MATRIX_MUL_LMUL`
- `MATRIX_MUL_LZERO`
- `mpow`
- `REAL_MUL_RID`
- `MATRIX_CMUL_RZERO`
- `MATRIX_SUB_REFL`
- `MATRIX_SUB`
- `MATRIX_NEG_ADD`
- `MATRIX_CMUL_ADD_RDISTRIB`
- `MATRIX_ADD_AC`
- `MATRIX_CMUL_ASSOC`
- `MATRIX_CMUL_SUB_LDISTRIB`
- `MATRIC_POWER_DIFFERENCE`
- `SUC_SUB1`
- `MATRIX_CMUL_ADD_LDISTRIB`
- `MSUM_ADD`
- `FINITE_NUMSEG`
- `MATRIX_ADD_RDISTRIB`
- `COND_RAND`
- `COND_RATOR`
- `MATRIX_CMUL_RZERO`
- `MSUM_RESTRICT_SET`
- `IN_NUMSEG`
- `numseg`
- `ARITH_RULE`
- `MSUM_LMUL`
- `REAL_MUL_SYM`


---

## CAYLEY_HAMILTON

### Name of formal statement
CAYLEY_HAMILTON

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CAYLEY_HAMILTON = prove
 (`!A:real^N^N. msum(0..dimindex(:N)) (\i. char_poly A i %% A mpow i) = mat 0`,
  GEN_TAC THEN MATCH_MP_TAC MATRIC_POLY_LEMMA THEN MATCH_MP_TAC(MESON[]
   `!g. (!x. g x = k) /\ (?a b c. !x. f a b c x = g x)
        ==> ?a b c. !x. f a b c x = k`) THEN
  EXISTS_TAC
   `\x. (msum(0..dimindex(:N)) (\i. char_poly A i %% (A:real^N^N) mpow i) -
         sum(0..dimindex(:N)) (\i. char_poly A i * x pow i) %% mat 1) +
        sum(0..dimindex(:N)) (\i. char_poly A i * x pow i) %% mat 1` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[MATRIX_SUB; GSYM MATRIX_ADD_ASSOC; MATRIX_ADD_LNEG] THEN
    REWRITE_TAC[MATRIX_ADD_RID];
    X_CHOOSE_THEN `B:num->real^N^N` (fun th -> ONCE_REWRITE_TAC[th])
     (ISPEC `A:real^N^N` MATRIC_CHARPOLY_DIFFERENCE) THEN
    REWRITE_TAC[GSYM char_poly; GSYM MATRIX_MUL_LEFT_COFACTOR] THEN
    REWRITE_TAC[GSYM MATRIX_ADD_RDISTRIB] THEN
    REWRITE_TAC[GSYM COFACTOR_TRANSP; TRANSP_MATRIX_SUB] THEN
    REWRITE_TAC[TRANSP_MATRIX_CMUL; TRANSP_MAT] THEN
    X_CHOOSE_THEN `C:num->real^N^N` (fun th -> ONCE_REWRITE_TAC[th])
     (ISPEC `transp A:real^N^N` COFACTOR_AS_MATRIC_POLYNOMIAL) THEN
    MAP_EVERY EXISTS_TAC
     [`A:real^N^N`; `(\i. B i + C i):num->real^N^N`; `dimindex(:N)-1`] THEN
    SIMP_TAC[GSYM MSUM_ADD; FINITE_NUMSEG; MATRIX_CMUL_ADD_LDISTRIB]]);;
```

### Informal statement
For any square matrix `A` of real numbers with dimensions `N` by `N`, the matrix resulting from the sum (indexed from 0 to `dimindex(:N)`) of terms calculated by multiplying the `i`-th coefficient of the characteristic polynomial of `A` by the matrix power `A` to the power of `i` is equal to the zero matrix.

### Informal sketch
The proof of the Cayley-Hamilton theorem proceeds as follows:
- It starts by applying `MATRIC_POLY_LEMMA` to relate a matrix polynomial evaluated at matrix A to the coefficients of polynomial evaluated as a scalar.
- An equality prover (`MESON`) is used to rewrite a generalized equality.
- The proof introduces an intermediate term: `(msum(0..dimindex(:N)) (\i. char_poly A i %% (A:real^N^N) mpow i) - sum(0..dimindex(:N)) (\i. char_poly A i * x pow i) %% mat 1) + sum(0..dimindex(:N)) (\i. char_poly A i * x pow i) %% mat 1`. This expression is equivalent to the original term but rewritten to separate matrix and scalar calculations.
- The goal `msum(0..dimindex(:N)) (\i. char_poly A i %% A mpow i) = mat 0` is split into two parts, one showing the cancellation in matrix space and the other applying scalar polynomial properties.
- The left conjunct simplifies using properties of matrix subtraction, associativity of matrix addition, the existence of additive inverses, and the right identity property of matrix addition.
- Apply `MATRIC_CHARPOLY_DIFFERENCE` to instantiate `B:num->real^N^N`.
- Rearrange the expressions by using `char_poly`, `MATRIX_MUL_LEFT_COFACTOR` and the distributive property.
- Apply `COFACTOR_AS_MATRIC_POLYNOMIAL` to instantiate '`C:num->real^N^N`.
- Existentially quantify `A`, `(\i. B i + C i)` and `dimindex(:N)-1`.
- The right conjunct is further simplified using `MSUM_ADD`, `FINITE_NUMSEG` and `MATRIX_CMUL_ADD_LDISTRIB` to finish the proof.

### Mathematical insight
The Cayley-Hamilton theorem is a fundamental result in linear algebra. It states that every square matrix satisfies its own characteristic equation. This theorem has numerous applications in matrix analysis, control theory, and other areas of mathematics and engineering. By substituting the matrix into its own characteristic polynomial, one obtains the zero matrix.

### Dependencies
- `MATRIC_POLY_LEMMA`
- `MATRIX_SUB`
- `MATRIX_ADD_ASSOC`
- `MATRIX_ADD_LNEG`
- `MATRIX_ADD_RID`
- `MATRIC_CHARPOLY_DIFFERENCE`
- `char_poly`
- `MATRIX_MUL_LEFT_COFACTOR`
- `MATRIX_ADD_RDISTRIB`
- `COFACTOR_TRANSP`
- `TRANSP_MATRIX_SUB`
- `TRANSP_MATRIX_CMUL`
- `TRANSP_MAT`
- `COFACTOR_AS_MATRIC_POLYNOMIAL`
- `MSUM_ADD`
- `FINITE_NUMSEG`
- `MATRIX_CMUL_ADD_LDISTRIB`


---

