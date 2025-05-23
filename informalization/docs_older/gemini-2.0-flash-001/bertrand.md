# bertrand.ml

## Overview

Number of statements: 88

`bertrand.ml` proves Bertrand's conjecture, stating there is always a prime between $n$ and $2n$ for $n > 0$. The file also includes a weak form of the prime number theorem. The proof relies on results from prime number theory, real analysis, and transcendental number theory, as well as the floor function.


## num_of_float

### Name of formal statement
num_of_float

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let num_of_float =
  let p22 = ( ** ) 2.0 22.0
  and p44 = ( ** ) 2.0 44.0
  and p66 = ( ** ) 2.0 66.0
  and q22 = pow2 22 and q44 = pow2 44 and q66 = pow2 66 in
  fun x ->
    let y0,n = frexp x in
    let u0 = int_of_float(y0 *. p22) in
    let y1 = p22 *. y0 -. float_of_int u0 in
    let u1 = int_of_float(y1 *. p22) in
    let y2 = p22 *. y1 -. float_of_int u1 in
    let u2 = int_of_float(y2 *. p22) in
    let y3 = p22 *. y2 -. float_of_int u2 in
    if y3 <> 0.0 then failwith "num_of_float: inexactness!" else
    (num u0 // q22 +/ num u1 // q44 +/ num u2 // q66) */ pow2 n;;
```

### Informal statement
The function `num_of_float` maps a floating-point number `x` to a rational number. It decomposes `x` into its mantissa `y0` and exponent `n` using `frexp`. Then, it computes three integer values `u0`, `u1`, and `u2` based on successive multiplications of `y0` by $2^{22}$ and taking the integer part. Finally, if a remainder `y3` is non-zero, then the function fails; otherwise, the result is the rational number $(u0/2^{22} + u1/2^{44} + u2/2^{66}) \cdot 2^n$.

### Informal sketch
- Decompose the input float `x` into mantissa `y0` and exponent `n` such that `x = y0 * 2^n` and `0.5 <= abs(y0) < 1`.
- Compute `u0`, `u1`, and `u2` by repeatedly multiplying the mantissa by $2^{22}$ and taking the integer part. This process is effectively extracting 22-bit chunks from the mantissa.
- Check for inexactness: Ensure that the remainder `y3` is zero. If it is not, then the conversion is inexact, and the function fails. This check is crucial because you do not want to lose precision.
- If `y3` is zero, then construct a rational number representation of `x`. Each $u_i$ is an integer, $q_i = 2^{22i}$, and $n$ is the exponent from the original `frexp` decomposition. The result is `(num u0 // q22 +/ num u1 // q44 +/ num u2 // q66) */ pow2 n`.

### Mathematical insight
This definition provides a way to convert a floating-point number to a rational number with a certain degree of accuracy determined by how many integer parts `u0`, `u1`, `u2` are taken. The conversion is only considered valid if the remainder `y3` is zero, meaning the floating point number can be exactly represented by a sum of fractions with powers of 2 in the denominator. This is important for exact real arithmetic or when a rational representation of a floating-point number is required. The choice of $2^{22}$ seems arbitrary, but it might have to do with the size of integers that can be represented without overflow, as the code uses `int_of_float` and `float_of_int`.

### Dependencies
- `Library/prime.ml`
- `Library/pocklington.ml`
- `Library/analysis.ml`
- `Library/transc.ml`
- `Library/calc_real.ml`
- `Library/floor.ml`
- `pow2`
- `frexp`
- `int_of_float`
- `float_of_int`
- `num`
- `(//)`: rational number division
- `(+/)`: rational number addition
- `(*)`: rational number multiplication
- `( ** )`: real exponentiation

### Porting notes
- The `frexp` function might have a different name or implementation in other proof assistants. Ensure the correct decomposition of floating-point numbers into mantissa and exponent is used.
- The `num` type and rational number operations `(//)`, `(+/)`, `(*)` need to be provided, possibly from a rational number library.
- The handling of `failwith` might differ in other systems. Consider replacing it with an appropriate error handling mechanism or a return of an optional value.
- Be mindful of potential overflow issues when converting between floats and integers, particularly when using `int_of_float` and `float_of_int`. Explicit bounds may be needed to prevent overflows.


---

## ISQRT

### Name of formal statement
ISQRT

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let ISQRT = new_definition
  `ISQRT n = @m. m EXP 2 <= n /\ n < (m + 1) EXP 2`;;
```

### Informal statement
The integer square root of `n`, denoted `ISQRT n`, is defined to be some `m` such that `m` squared is less than or equal to `n`, and `n` is strictly less than `(m + 1)` squared.

### Informal sketch
- The definition introduces a function `ISQRT` that maps a natural number `n` to some natural number `m` satisfying the specified conditions.
- The definition uses Hilbert choice (`@`) to pick a suitable `m`. The conditions ensure that `m` is the greatest integer whose square is less than or equal to `n`.

### Mathematical insight
The `ISQRT` function computes the integer square root, i.e., the floor of the square root of a natural number. The definition captures the standard mathematical notion of an integer square root. The use of Hilbert choice guarantees the existence of a value, provided that a value satisfying the condition exists (which can be shown constructively).

### Dependencies
None


---

## ISQRT_WORKS

### Name of formal statement
ISQRT_WORKS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ISQRT_WORKS = prove
 (`!n. ISQRT(n) EXP 2 <= n /\ n < (ISQRT(n) + 1) EXP 2`,
  GEN_TAC THEN REWRITE_TAC[ISQRT] THEN CONV_TAC SELECT_CONV THEN
  SUBGOAL_THEN `(?m. m EXP 2 <= n) /\ (?a. !m. m EXP 2 <= n ==> m <= a)`
  MP_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[num_MAX] THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    MESON_TAC[ARITH_RULE `~(m + 1 <= m)`; NOT_LE]] THEN
  CONJ_TAC THENL [EXISTS_TAC `0` THEN REWRITE_TAC[ARITH; LE_0]; ALL_TAC] THEN
  EXISTS_TAC `n:num` THEN X_GEN_TAC `m:num` THEN
  MESON_TAC[LE_SQUARE_REFL; EXP_2; LE_TRANS]);;
```
### Informal statement
For all natural numbers `n`, the square of `ISQRT(n)` is less than or equal to `n`, and `n` is less than the square of `ISQRT(n) + 1`.

### Informal sketch
The proof proceeds as follows:
- Start with the goal `!n. ISQRT(n) EXP 2 <= n /\ n < (ISQRT(n) + 1) EXP 2`.
- Rewrite using the definition of `ISQRT`.
- Apply a conversion tactic to select the appropriate subterm.
- Reduce the goal to proving the existence of a maximum `m` such that `m EXP 2 <= n`, and that this `m` is the maximum.
- Prove the existence part by noting that 0 satisfies the condition, so such an `m` exists.
- Prove the maximum part using `num_MAX`, `MONO_EXISTS`, and the arithmetic rule `~(m + 1 <= m)`; `NOT_LE`.
- Show that 0 satisfies the condition `0 EXP 2 <= n`.
- Show that `n` itself is an upper bound for suitable `m`, such that `m EXP 2 <= n`.
- Specialize the universally quantified `m:num` with `n:num` (existential instantiation with `n`).
- Complete the proof using `LE_SQUARE_REFL`, `EXP_2`, and `LE_TRANS`.

### Mathematical insight
This theorem establishes the correctness of the integer square root function `ISQRT`. It states that `ISQRT(n)` is the largest integer whose square is less than or equal to `n`. In other words, it formalizes the expected behavior of an integer square root function.

### Dependencies
- Definitions: `ISQRT`
- Theorems/Rules: `ARITH`, `LE_0`, `LE_SQUARE_REFL`, `EXP_2`, `LE_TRANS`, `num_MAX`, `MONO_EXISTS`, `ARITH_RULE` `~(m + 1 <= m)`, `NOT_LE`

### Porting notes (optional)
The main challenge in porting this theorem lies in the automation. HOL Light's `MESON_TAC` plays a key role in discharging several goals. If the target proof assistant lacks similar automation, some manual proof steps may be needed. The proof relies on basic arithmetic facts, which should be readily available in most proof assistants. Ensure that the definition of integer square root (`ISQRT`) is ported correctly.


---

## ISQRT_0

### Name of formal statement
ISQRT_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ISQRT_0 = prove
 (`ISQRT 0 = 0`,
  MP_TAC(SPEC `0` ISQRT_WORKS) THEN
  SIMP_TAC[ARITH_RULE `x <= 0 <=> (x = 0)`; EXP_EQ_0; ARITH_EQ]);;
```
### Informal statement
The integer square root of 0 is 0.

### Informal sketch
The proof proceeds as follows:
- Apply the specific instance of `ISQRT_WORKS` with `0` as argument.
- Simplify using arithmetic rules to establish `x <= 0 <=> (x = 0)`; `EXP_EQ_0`; `ARITH_EQ`.

### Mathematical insight
This theorem establishes the base case for the integer square root function, showing its value at 0 is indeed 0. This is a fundamental property required for reasoning about integer square roots.

### Dependencies
- Theorems: `ISQRT_WORKS`
- Definitions: `ISQRT`
- Other: `ARITH_RULE`, `EXP_EQ_0`, `ARITH_EQ`


---

## ISQRT_UNIQUE

### Name of formal statement
ISQRT_UNIQUE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ISQRT_UNIQUE = prove
 (`!m n. (ISQRT n = m) <=> m EXP 2 <= n /\ n < (m + 1) EXP 2`,
  REPEAT GEN_TAC THEN EQ_TAC THEN MP_TAC (SPEC `n:num` ISQRT_WORKS) THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(ISQRT n) EXP 2 < (m + 1) EXP 2 /\
                m EXP 2 < (ISQRT n + 1) EXP 2`
  MP_TAC THENL
   [ASM_MESON_TAC[LT_SUC_LE; LE_SUC_LT; LET_TRANS; LTE_TRANS];
    SIMP_TAC[num_CONV `2`; EXP_MONO_LT; NOT_SUC; GSYM LE_ANTISYM] THEN ARITH_TAC]);;
```

### Informal statement
For all natural numbers `m` and `n`, `ISQRT n = m` if and only if `m^2 <= n` and `n < (m + 1)^2`.

### Informal sketch
The proof demonstrates the uniqueness property of the integer square root (`ISQRT`).

- First, universally quantify over `m` and `n`; then decompose the equivalence into two implications with `EQ_TAC`.
- The forward implication is proven using `ISQRT_WORKS` and `MESON_TAC`. Specifically, instantiate `ISQRT_WORKS` with `n:num` and use Modus Ponens.
- The second goal, the reverse implication, initiates by stripping the goal with `REPEAT STRIP_TAC`.
- Then, introduce a subgoal: `(ISQRT n)^2 < (m + 1)^2 /\ m^2 < (ISQRT n + 1)^2`.
- Use Modus Ponens to replace goal with subgoal, which simplifies proving implication direction.
- The first branch uses assumption, `LT_SUC_LE`, `LE_SUC_LT`, `LET_TRANS`, `LTE_TRANS` and `MESON_TAC` to get the desired result.
- The second branch simplifies using rewriting rules, including `num_CONV 2`, `EXP_MONO_LT`, `NOT_SUC`, and the symmetric version of `LE_ANTISYM`; `ARITH_TAC` completes the proof.

### Mathematical insight
This theorem establishes a fundamental property of the integer square root, namely that `ISQRT n = m` is uniquely determined by the condition that m is the largest natural number whose square is at most `n`. The integer square root of `n` is `m` if and only if `n` lies between the square of `m` and the square of `m+1`. This uniquely characterises `ISQRT`.

### Dependencies
- `ISQRT`
- `ISQRT_WORKS`
- `LT_SUC_LE`
- `LE_SUC_LT`
- `LET_TRANS`
- `LTE_TRANS`
- `EXP_MONO_LT`
- `NOT_SUC`
- `LE_ANTISYM`

### Porting notes (optional)
This theorem relies on the definition and properties of integer square root (`ISQRT`) and inequalities. Translation to other provers would require ensuring that the integer square root is defined equivalently and that the core arithmetic lemmas about inequalities on natural numbers are available.


---

## ISQRT_SUC

### Name of formal statement
ISQRT_SUC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ISQRT_SUC = prove
 (`!n. ISQRT(SUC n) =
       if ?m. SUC n = m EXP 2 then SUC(ISQRT n) else ISQRT n`,
  GEN_TAC THEN REWRITE_TAC[ISQRT_UNIQUE] THEN COND_CASES_TAC THENL
   [ALL_TAC;
    ASM_MESON_TAC[ISQRT_WORKS; ARITH_RULE
     `a <= n /\ n < b /\ ~(SUC n = a) /\ ~(SUC n = b)
      ==> a <= SUC n /\ SUC n < b`]] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MP_TAC(CONJUNCT2(SPEC `n:num` ISQRT_WORKS)) THEN
    REWRITE_TAC[EXP_2; GSYM ADD1; MULT_CLAUSES; ADD_CLAUSES; LT_SUC] THEN
    ARITH_TAC] THEN
  POP_ASSUM(X_CHOOSE_TAC `m:num`) THEN
  SUBGOAL_THEN `m = SUC(ISQRT n)` SUBST_ALL_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[LE_REFL]] THEN
  SUBGOAL_THEN `ISQRT(n) EXP 2 < m EXP 2 /\ m EXP 2 <= SUC(ISQRT n) EXP 2`
  MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[num_CONV `2`; EXP_MONO_LE; EXP_MONO_LT; NOT_SUC] THEN
    ARITH_TAC] THEN
  MP_TAC(SPEC `n:num` ISQRT_WORKS) THEN REWRITE_TAC[ADD1] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[LT_SUC_LE; LE_SUC_LT]);;
```

### Informal statement
For all natural numbers `n`, `ISQRT(SUC n)` is equal to `SUC(ISQRT n)` if there exists a natural number `m` such that `SUC n = m EXP 2`; otherwise, `ISQRT(SUC n)` is equal to `ISQRT n`.

### Informal sketch
The proof proceeds by induction on `n`.
- Base case: Proved automatically
- Inductive step: We must prove that the theorem holds for `SUC n` given that it holds for `n`
  - Case 1: Assume there exists an `m` such that `SUC n = m EXP 2`. Then we want to show `ISQRT(SUC n) = SUC(ISQRT n)`. This proceeds by using `ISQRT_UNIQUE` and `ISQRT_WORKS`.  Then we show `a <= n /\ n < b /\ ~(SUC n = a) /\ ~(SUC n = b) ==> a <= SUC n /\ SUC n < b` using `ARITH_RULE` and `ASM_MESON_TAC`.
  - Case 2: Assume there does not exist an `m` such that `SUC n = m EXP 2`. Then we want to show `ISQRT(SUC n) = ISQRT n`. This proceeds by assuming there exists an `m` such that `SUC(ISQRT n) = m` and proving `m = SUC(ISQRT n)`. Then by proving `ISQRT(n) EXP 2 < m EXP 2 /\ m EXP 2 <= SUC(ISQRT n) EXP 2`

### Mathematical insight
The theorem `ISQRT_SUC` specifies how the integer square root function `ISQRT` behaves when its argument is incremented. It essentially states that the integer square root of `SUC n` is the same as the integer square root of `n` unless `SUC n` is a perfect square, in which case it is incremented by one.

### Dependencies
- `ISQRT_UNIQUE`
- `ISQRT_WORKS`
- `ARITH_RULE`
- `EXP_2`
- `ADD1`
- `MULT_CLAUSES`
- `ADD_CLAUSES`
- `LT_SUC`
- `LE_REFL`
- `EXP_MONO_LE`
- `EXP_MONO_LT`
- `NOT_SUC`
- `LT_SUC_LE`
- `LE_SUC_LT`
- `num_CONV`


---

## LN_2_COMPOSITION

### Name of formal statement
LN_2_COMPOSITION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LN_2_COMPOSITION = prove
 (`ln(&2) =
   &7 * ln(&1 + inv(&8)) - &2 * ln(&1 + inv(&24)) - &4 * ln(&1 + inv(&80))`,
  CONV_TAC(GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4
        [GSYM LN_POW; GSYM LN_MUL; GSYM LN_DIV; REAL_POW_LT; real_div;
         REAL_LT_ADD; REAL_LT_MUL; REAL_LT_INV_EQ; REAL_OF_NUM_LT; ARITH]) THEN
  AP_TERM_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV);;
```
### Informal statement
Prove that the natural logarithm of 2 is equal to `7` times the natural logarithm of `1 + 1/8` minus `2` times the natural logarithm of `1 + 1/24` minus `4` times the natural logarithm of `1 + 1/80`.

### Informal sketch
The proof is conducted as follows:
- The initial goal is `ln(&2) = &7 * ln(&1 + inv(&8)) - &2 * ln(&1 + inv(&24)) - &4 * ln(&1 + inv(&80))`.
- The proof primarily uses simplification with real number arithmetic and logarithm identities, via `CONV_TAC(GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4[GSYM LN_POW; GSYM LN_MUL; GSYM LN_DIV; REAL_POW_LT; real_div; REAL_LT_ADD; REAL_LT_MUL; REAL_LT_INV_EQ; REAL_OF_NUM_LT; ARITH])`. This step applies simplification conversions including `LN_POW`, `LN_MUL`, `LN_DIV`, `REAL_POW_LT` as well as arithmetic simplification rules. The `ARITH` rewriting rule likely performs basic arithmetic reductions.
- Next, `AP_TERM_TAC` applies the simplification to the top-level term.
- Finally, the constants are reduced using `REAL_RAT_REDUCE_CONV`.

### Mathematical insight
This theorem provides a specific formula for computing `ln(2)` as a combination of logarithms of numbers close to 1. Such formulas are useful for numerical computation of logarithms, especially when combined with Taylor series or other approximation techniques, as `ln(1+x)` can be efficiently approximated for small `x`. By carefully choosing the coefficients and fractions, an accurate approximation of `ln(2)` can be obtained with relatively few terms.

### Dependencies
- `LN_POW`
- `LN_MUL`
- `LN_DIV`
- `REAL_POW_LT`
- `real_div`
- `REAL_LT_ADD`
- `REAL_LT_MUL`
- `REAL_LT_INV_EQ`
- `REAL_OF_NUM_LT`
- `ARITH`


---

## LN_N_CONV

### Name of formal statement
LN_N_CONV

### Type of the formal statement
Conversion

### Formal Content
```ocaml
let LN_N_CONV =
  let pth = prove
   (`x = (&1 + inv(&8)) pow n * (x / (&1 + inv(&8)) pow n)`,
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
    MATCH_MP_TAC REAL_POW_NZ THEN CONV_TAC REAL_RAT_REDUCE_CONV)
  and qth = prove
   (`&0 < x
     ==> (ln((&1 + inv(&8)) pow n * x / (&1 + inv(&8)) pow n) =
          &n * ln(&1 + inv(&8)) + ln(&1 + (x / (&1 + inv(&8)) pow n - &1)))`,
    REWRITE_TAC[REAL_ARITH `&1 + (x - &1) = x`] THEN
    SIMP_TAC[LN_MUL; LN_POW; REAL_LT_DIV; REAL_POW_LT;
             REAL_RAT_REDUCE_CONV `&0 < &1 + inv(&8)`])
  and ln_tm = `ln` and x_tm = `x:real` and n_tm = `n:num` in
  fun tm0 ->
    let ltm,tm = dest_comb tm0 in
    if ltm <> ln_tm then failwith "expected ln(ratconst)" else
    let x = rat_of_term tm in
    let rec dlog n y =
      let y' = y +/ y // num 8 in
      if y' </ x then dlog (n + 1) y' else n in
    let n = dlog 0 (num 1) in
    let th1 = INST [mk_small_numeral n,n_tm; tm,x_tm] pth in
    let th2 = AP_TERM ltm th1 in
    let th3 = PART_MATCH (lhs o rand) qth (rand(concl th2)) in
    let th4 = MP th3 (EQT_ELIM(REAL_RAT_REDUCE_CONV(lhand(concl th3)))) in
    let th5 = TRANS th2 th4 in
    CONV_RULE(funpow 4 RAND_CONV REAL_RAT_REDUCE_CONV) th5;;
```

### Informal statement
The conversion `LN_N_CONV` takes a term of the form `ln(x)` where `x` is a rational constant, and transforms it into the expression `&n * ln(&1 + inv(&8)) + ln(&1 + (x / (&1 + inv(&8)) pow n - &1))` where `n` is a natural number such that `(1 + 1/8)^n` is the largest power of `(1 + 1/8)` less than or equal to `x`. This conversion first proves two intermediate theorems, `pth` and `qth`. Theorem `pth` states that `x = (&1 + inv(&8)) pow n * (x / (&1 + inv(&8)) pow n)`. Theorem `qth` states that if `0 < x`, then `ln((&1 + inv(&8)) pow n * x / (&1 + inv(&8)) pow n) = &n * ln(&1 + inv(&8)) + ln(&1 + (x / (&1 + inv(&8)) pow n - &1))`.

### Informal sketch
The `LN_N_CONV` conversion works as follows:
- It takes a term `tm0` and checks if it is of the form `ln(x)` where `x` is a rational constant.
- If it is, it computes the largest natural number `n` such that `(1 + 1/8)^n <= x`. This is done by the auxiliary function `dlog`.
- It instantiates the theorems `pth` and `qth` with the computed `n` and the original term `x`.
  - `pth` shows the equality `x = (&1 + inv(&8)) pow n * (x / (&1 + inv(&8)) pow n)`.
  - `qth` shows the equality `ln((&1 + inv(&8)) pow n * x / (&1 + inv(&8)) pow n) = &n * ln(&1 + inv(&8)) + ln(&1 + (x / (&1 + inv(&8)) pow n - &1))`. given the condition `0 < x`.
- It then manipulates and combines these theorems to derive and return a theorem that `ln(x)` is equal to `&n * ln(&1 + inv(&8)) + ln(&1 + (x / (&1 + inv(&8)) pow n - &1))`.

The proofs of `pth` and `qth` are relatively straightforward using standard real arithmetic tactics and simplification rules involving logarithms.

Specifically,
- `pth` is proved by rewriting `x` using arithmetic simplification, symmetry, and the property that `x = (x / y) * y`.
- `qth` is proved by rewriting using `REAL_ARITH`, then simplifying with logarithmic identities such as `LN_MUL` (logarithm of a product), `LN_POW` (logarithm of a power), and other real arithmetic rules.

### Mathematical insight
The purpose of this conversion is to transform the logarithm of a rational constant into a form that is more amenable to further simplification or evaluation. By extracting a power of `(1 + 1/8)`, the conversion can reduce the size of the argument to the logarithm, potentially leading to a simpler expression. The choice of `(1 + 1/8)` as the base is likely related to the specific context in which this conversion is used (perhaps related to machine word size).

### Dependencies
- `REAL_RAT_REDUCE_CONV`: Conversion for reducing real rational expressions.
- `LN_MUL`: Theorem stating that `ln(x * y) = ln(x) + ln(y)`.
- `LN_POW`: Theorem stating that `ln(x pow y) = y * ln(x)`.
- `REAL_LT_DIV`: Theorem related to inequalities and division in real numbers.
- `REAL_POW_LT`: Theorem related to inequalities and exponentiation in real numbers.
- `REAL_ARITH`: Tactic for real arithmetic reasoning.
- `REAL_DIV_LMUL`: Theorem stating that x = (x / y) * y.
- `REAL_POW_NZ`: Theorem about powers of nonzero real numbers.


---

## LN_N2_CONV

### Name of formal statement
LN_N2_CONV

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LN_N2_CONV =
  let pth = prove
   (`x = &2 pow n * (x / &2 pow n)`,
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
    MATCH_MP_TAC REAL_POW_NZ THEN CONV_TAC REAL_RAT_REDUCE_CONV)
  and qth = prove
   (`&0 < x
     ==> (ln(&2 pow n * x / &2 pow n) =
          &n * ln(&2) + ln(&1 + (x / &2 pow n - &1)))`,
    REWRITE_TAC[REAL_ARITH `&1 + (x - &1) = x`] THEN
    SIMP_TAC[LN_MUL; LN_POW; REAL_LT_DIV; REAL_POW_LT;
             REAL_RAT_REDUCE_CONV `&0 < &2`])
  and ln_tm = `ln` and x_tm = `x:real` and n_tm = `n:num` in
  fun tm0 ->
    let ltm,tm = dest_comb tm0 in
    if ltm <> ln_tm then failwith "expected ln(ratconst)" else
    let x = rat_of_term tm in
    let rec dlog n y =
      let y' = y */ num 2 in
      if y' </ x then dlog (n + 1) y' else n in
    let n = dlog 0 (num 1) in
    let th1 = INST [mk_small_numeral n,n_tm; tm,x_tm] pth in
    let th2 = AP_TERM ltm th1 in
    let th3 = PART_MATCH (lhs o rand) qth (rand(concl th2)) in
    let th4 = MP th3 (EQT_ELIM(REAL_RAT_REDUCE_CONV(lhand(concl th3)))) in
    let th5 = TRANS th2 th4 in
    let th6 = CONV_RULE(funpow 4 RAND_CONV REAL_RAT_REDUCE_CONV) th5 in
    let th7 = CONV_RULE (funpow 3 RAND_CONV REAL_RAT_REDUCE_CONV) th6 in
    CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV LN_N_CONV)) th7;;
```

### Informal statement
A conversion tactic that reduces `ln(x)` where `x` is a rational constant by factoring out powers of 2. The tactic first finds an integer `n` such that `x` can be written as `2^n * y`, where `1 <= y < 2`. Then, it rewrites `ln(x)` as `ln(2^n * y / 2^n) = n * ln(2) + ln(1 + (y / 2^n - 1))`.

### Informal sketch
The theorem defines a conversion tactic for simplifying the natural logarithm of rational constants.
- First, it proves a theorem `x = &2 pow n * (x / &2 pow n)` using `REAL_RAT_REDUCE_CONV`, `SYM_CONV`, `REAL_DIV_LMUL`, and `REAL_POW_NZ`. This establishes that `x` can be represented this way.
- Second, it proves a related theorem `&0 < x ==> (ln(&2 pow n * x / &2 pow n) = &n * ln(&2) + ln(&1 + (x / &2 pow n - &1)))`. This step uses `REAL_ARITH` to rewrite `&1 + (x - &1) = x` and then applies simplifications based on properties of logarithms (`LN_MUL`, `LN_POW`) and inequalities (`REAL_LT_DIV`, `REAL_POW_LT`), along with rational reduction.
- The conversion tactic `LN_N2_CONV` takes a term `tm0` of the form `ln(x)` where `x` is a rational constant.
- It determines `n`, the integer power of 2, such that `x = (2^n) * y` with `1 ≤ y < 2` using the helper function `dlog`. This step involves repeated multiplication by 2 and comparison with the given rational number.
- It instantiates the theorems `x = &2 pow n * (x / &2 pow n)` and `&0 < x ==> (ln(&2 pow n * x / &2 pow n) = &n * ln(&2) + ln(&1 + (x / &2 pow n - &1)))` with the calculated `n` and `x`.
- It uses matching and term manipulation to rewrite the input term using `ln(2^n * x / 2^n) = n * ln(2) + ln(1 + (x / 2^n - 1))`.
- It then simplifies the resulting expression using further conversions, specifically focusing on rational reduction.
- Finally, it applies the `LN_N_CONV` conversion to the `ln(2)` term.

### Mathematical insight
The function `LN_N2_CONV` reduces the logarithm of a rational constant by extracting factors of 2. This technique is important for simplifying logarithmic expressions and for numerical evaluation where factors of 2 can be handled efficiently. By isolating the `ln(2)` component, it simplifies the remaining argument of the `ln` function and may allow for further simplifications or approximations, and is a special case of reducing by multiples of ln(2).

### Dependencies
- `LN_MUL`
- `LN_POW`
- `REAL_LT_DIV`
- `REAL_POW_LT`
- `REAL_RAT_REDUCE_CONV`
- `REAL_ARITH`
- `REAL_DIV_LMUL`
- `REAL_POW_NZ`
- `LN_N_CONV`

### Porting notes (optional)
- The tactic relies heavily on simplification with theorems related to real arithmetic and rational numbers. Ensure that the target proof assistant has equivalent theorems and simplification procedures.
- The use of conversionals (`CONV_RULE`) might need to be adapted to the corresponding mechanisms for applying conversions in the target proof assistant.
- The `funpow` function is specific to HOL Light's conversionals. Ensure the target proof assistant has methods for applying conversion to a function raised to a power.


---

## FLOOR_DOUBLE_NUM

### Name of formal statement
FLOOR_DOUBLE_NUM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FLOOR_DOUBLE_NUM = prove
 (`!n r d.
        d < 2 /\ 0 < r
        ==> &2 * floor(&n / &r) <= floor(&(2 * n + d) / &r) /\
            floor(&(2 * n + d) / &r) <= &2 * floor(&n / &r) + &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `floor(&n / &r) = floor((&n + &d / &2) / &r)` SUBST1_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    SUBGOAL_THEN `&2 * &n + &d = &2 * (&n + &d / &2)` SUBST1_TAC THENL
     [SIMP_TAC[REAL_ADD_LDISTRIB; REAL_DIV_LMUL; REAL_OF_NUM_EQ; ARITH_EQ];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_ADD_LDISTRIB; GSYM REAL_MUL_ASSOC; real_div] THEN
    REWRITE_TAC[GSYM real_div; FLOOR_DOUBLE]] THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[GSYM FLOOR_UNIQUE] THEN
  MP_TAC(SPEC `&n / &r` FLOOR) THEN SIMP_TAC[] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&n / &r` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div; REAL_ADD_RDISTRIB; REAL_LE_ADDR] THEN
    SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LE_INV_EQ];
    ALL_TAC] THEN
  UNDISCH_TAC `&n / &r < floor (&n / &r) + &1` THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT] THEN
  SIMP_TAC[REAL_LT_INTEGERS; FLOOR; INTEGER_CLOSED] THEN
  MATCH_MP_TAC(REAL_ARITH `b < a ==> n + a <= c ==> n + b < c`) THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID; REAL_OF_NUM_LT; ARITH]);;
```
### Informal statement
For all natural numbers `n`, `r`, and `d`, if `d` is less than 2 and `r` is greater than 0, then `2` times the floor of `n` divided by `r` is less than or equal to the floor of `(2 * n + d)` divided by `r`, and the floor of `(2 * n + d)` divided by `r` is less than or equal to `2` times the floor of `n` divided by `r` plus `1`.

### Informal sketch
The proof establishes an inequality about the floor function applied to real numbers.

- First, the goal is reduced to proving `floor(&n / &r) = floor((&n + &d / &2) / &r)`. This step simplifies the expression inside the floor function, bridging the gap between `&2 * n + d` and `&n`.
- The proof then verifies that `&2 * n + d = &2 * (&n + &d / &2)` using previously established rules of real number arithmetic. This equality makes it possible to rewrite the expression inside the floor function.
- Using the lemma `FLOOR_DOUBLE`, the theorem rewrites an expression involving the floor function.
- Rewriting `FLOOR_UNIQUE` in reverse, we show that `x = floor(y)` if what `x` equals satisfies the property of being unique.
- Then, using `FLOOR` and some algebraic manipulation, we rewrite the expression such that an expression involving the floor function appears.
- We then show the inequality `&n / &r < floor (&n / &r) + &1`.
- Finally, using previously established real arithmetic we show that the goal is satisfied.

### Mathematical insight
This theorem gives bounds on how the floor function interacts with multiplication by 2. This is useful when reasoning about binary representations or bit shifts in a formal setting.

### Dependencies
- `REAL_OF_NUM_ADD`
- `REAL_OF_NUM_MUL`
- `REAL_ADD_LDISTRIB`
- `REAL_DIV_LMUL`
- `REAL_OF_NUM_EQ`
- `ARITH_EQ`
- `REAL_MUL_ASSOC`
- `real_div`
- `FLOOR_DOUBLE`
- `FLOOR_UNIQUE`
- `FLOOR`
- `REAL_LE_TRANS`
- `REAL_LE_ADDR`
- `REAL_LE_MUL`
- `REAL_POS`
- `REAL_LE_INV_EQ`
- `REAL_LT_LDIV_EQ`
- `REAL_OF_NUM_LT`
- `REAL_LT_INTEGERS`
- `INTEGER_CLOSED`
- `REAL_ARITH`
- `REAL_MUL_LID`


---

## LN_FACT

### Name of formal statement
LN_FACT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LN_FACT = prove
 (`!n. ln(&(FACT n)) = sum(1,n) (\d. ln(&d))`,
  INDUCT_TAC THEN REWRITE_TAC[FACT; sum; LN_1] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_MUL; LN_MUL; REAL_OF_NUM_LT; FACT_LT; LT_0] THEN
  ASM_REWRITE_TAC[ADD1] THEN REWRITE_TAC[ADD_AC; REAL_ADD_AC]);;
```

### Informal statement
For all natural numbers `n`, the natural logarithm of the factorial of `n` is equal to the sum, from 1 to `n`, of the natural logarithms of `d`, where `d` ranges from 1 to `n`.

### Informal sketch
The proof proceeds by induction on `n`.

- **Base Case:** `n = 0`. The left-hand side is `ln(FACT 0) = ln(1) = 0`, and the right-hand side is the sum from 1 to 0 of `ln(d)`, which is also 0.
- **Inductive Step:** Assume `ln(FACT n) = sum(1, n) (\d. ln(&d))`. We want to show `ln(FACT (n+1)) = sum(1, n+1) (\d. ln(&d))`.
    - The proof starts by rewriting using the definitions of `FACT`, `sum`, and `LN_1`, and then simplifies using properties of real numbers, logarithms, and inequalities involving `FACT`. Specifically, the rules used are `REAL_OF_NUM_MUL`, `LN_MUL`, `REAL_OF_NUM_LT`, `FACT_LT`, and `LT_0`.
    - It uses the assumption to rewrite and then employs properties of addition to move the new term in `sum (1, n+1)` to its correct position. The properties used are `ADD1` and the associativity and commutativity of addition `ADD_AC` and `REAL_ADD_AC`.

### Mathematical insight
This theorem relates the logarithm of the factorial function to a sum of logarithms, which is a discrete analog of integration. It is a fundamental result useful for estimating the growth of the factorial function and is related to Stirling's approximation.

### Dependencies
- `FACT` (factorial function)
- `sum` (summation)
- `LN_1` (ln(1) = 0)
- `REAL_OF_NUM_MUL` (inject real numbers from multiplication of natural numbers definition)
- `LN_MUL` (logarithm of a product)
- `REAL_OF_NUM_LT` (inject real numbers from `<` definition)
- `FACT_LT` (strict positivity of factorial)
- `LT_0` (0 < 1)
- `ADD1` (n + 1)
- `ADD_AC` (Associativity and Commutativity of addition)
- `REAL_ADD_AC` (Reals Associativity and Commutativity of addition)


---

## LN_FACT_BOUNDS

### Name of formal statement
LN_FACT_BOUNDS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LN_FACT_BOUNDS = prove
 (`!n. ~(n = 0) ==> abs(ln(&(FACT n)) - (&n * ln(&n) - &n)) <= &1 + ln(&n)`,
  SUBGOAL_THEN
   `!n. ~(n = 0)
        ==> ?z. &n < z /\ z < &(n + 1) /\
                (&(n + 1) * ln(&(n + 1)) - &n * ln(&n) = ln(z) + &1)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`\x. x * ln(x)`; `\x. ln(x) + &1`; `&n`; `&(n + 1)`]
                 MVT_ALT) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[REAL_ARITH `(n + &1) - n = &1`] THEN
    REWRITE_TAC[REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[REAL_ARITH `a < a + &1`] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    MP_TAC(SPEC `x:real` (DIFF_CONV `\x. x * ln(x)`)) THEN
    SIMP_TAC[REAL_MUL_LID; REAL_MUL_RID; REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `&n` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
    UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num->real`) THEN
  SUBGOAL_THEN
   `!n. &(n + 1) * ln(&(n + 1)) = sum(1,n) (\i. ln(k i) + &1)`
  MP_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[NOT_SUC] THEN
    REWRITE_TAC[sum; ADD_CLAUSES; LN_1; REAL_MUL_RZERO] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n + 1`) THEN
    REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[ARITH_RULE `(n + 1) + 1 = n + 2`;
                ARITH_RULE `SUC(n + 1) = n + 2`] THEN
    DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
    REWRITE_TAC[REAL_ARITH `(a - b = c) <=> (a = b + c)`] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_AC];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD] THEN
  CONV_TAC(LAND_CONV(BINDER_CONV(RAND_CONV(RAND_CONV(LAND_CONV
    (LAND_CONV num_CONV)))))) THEN
  REWRITE_TAC[ADD1; SUM_REINDEX; SUM_CONST] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(a = b + c * &1) <=> (b = a - c)`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. abs(sum(1,n+1) (\i. ln (&i)) - (&(n + 1) * ln (&(n + 1)) - &(n + 1)))
        <= &1 + ln(&(n + 1))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o funpow 3 RAND_CONV)
     [GSYM REAL_OF_NUM_ADD] THEN
    MATCH_MP_TAC(REAL_ARITH
     `abs(x - (y - z)) <= a ==> abs(x - (y - (z + &1))) <= &1 + a`) THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC
      (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM th]) THEN
    SUBGOAL_THEN
     `sum(1,n + 1) (\i. ln (&i)) = sum(1,n) (\i. ln(&(i + 1)))`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [SUM_DIFF] THEN
      REWRITE_TAC[SUM_1; ADD_CLAUSES; LN_1; REAL_SUB_RZERO] THEN
      GEN_REWRITE_TAC (funpow 3 LAND_CONV) [SYM(NUM_REDUCE_CONV `0 + 1`)] THEN
      REWRITE_TAC[SUM_REINDEX] THEN REWRITE_TAC[ADD_AC];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM SUM_SUB] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1,n) (\n. abs(ln(&(n + 1)) - ln(k n)))` THEN
    REWRITE_TAC[ABS_SUM] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1,n) (\i. ln(&(i + 1)) - ln(&i))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `a < b /\ b < c ==> abs(c - b) <= c - a`) THEN
      SUBGOAL_THEN `&0 < &r /\ &r < k r /\ k r < &(r + 1)` MP_TAC THENL
       [ALL_TAC; MESON_TAC[LN_MONO_LT; REAL_LT_TRANS]] THEN
      ASM_SIMP_TAC[REAL_OF_NUM_LT; ARITH_RULE `0 < r <=> 1 <= r`;
                   ARITH_RULE `~(r = 0) <=> 1 <= r`];
      ALL_TAC] THEN
    REWRITE_TAC[SUM_SUB] THEN
    REWRITE_TAC[GSYM(SPECL [`f:num->real`; `m:num`; `1`] SUM_REINDEX)] THEN
    ONCE_REWRITE_TAC[SUM_DIFF] THEN
    REWRITE_TAC[ARITH; SUM_2; SUM_1; LN_1; REAL_ADD_RID] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `2 + n = SUC(1 + n)`] THEN
    REWRITE_TAC[sum; ADD_CLAUSES] THEN
    REWRITE_TAC[ADD_AC] THEN
    REWRITE_TAC[REAL_ARITH `(a + b) - c - (a - c) = b`; REAL_LE_REFL];
    ALL_TAC] THEN
  INDUCT_TAC THEN REWRITE_TAC[NOT_SUC] THEN
  ASM_REWRITE_TAC[ADD1; LN_FACT]);;
```

### Informal statement
For all natural numbers `n` such that `n` is not equal to 0, the absolute value of the difference between the natural logarithm of the factorial of `n` and the expression `n * ln(n) - n` is less than or equal to `1 + ln(n)`.

### Informal sketch
The proof proceeds as follows:
- The main goal is to prove `!n. ~(n = 0) ==> abs(ln(&(FACT n)) - (&n * ln(&n) - &n)) <= &1 + ln(&n)`.
- First, an intermediate existential goal is introduced using the Mean Value Theorem (`MVT_ALT`):
  - `!n. ~(n = 0) ==> ?z. &n < z /\ z < &(n + 1) /\ (&(n + 1) * ln(&(n + 1)) - &n * ln(&n) = ln(z) + &1)`.
  - This subgoal states that there exists a real number `z` between `n` and `n+1` such that `(n+1)*ln(n+1) - n*ln(n) = ln(z) + 1`. This relies on applying the Mean Value Theorem to the function `f(x) = x*ln(x)`.
  - This subgoal is proved using the Mean Value Theorem (`MVT_ALT`), real arithmetic, and differentiation (`DIFF_CONV`).
- The main goal is then rewritten using the proven existential statement, introducing a choice function `k:num->real` such that for each `n`, `&n < k(n) /\ k(n) < &(n + 1) /\ (&(n + 1) * ln(&(n + 1)) - &n * ln(&n) = ln(k n) + &1)`.
- Next, we want to show that `&(n + 1) * ln(&(n + 1)) = sum(1,n) (\i. ln(k i) + &1)`. This is proven by induction on `n`.
  - The base case `n = 0` is handled.
  - The inductive step involves showing that if the equality holds for `n`, then it also holds for `n+1`.
- After the inductive step, the proof proceeds by rewriting the sum and re-indexing.
- A new subgoal is introduced: `!n. abs(sum(1,n+1) (\i. ln (&i)) - (&(n + 1) * ln (&(n + 1)) - &(n + 1))) <= &1 + ln(&(n + 1))`. The main statement can be derived by induction from this.
- After assuming this statement (by `ASSUME_TAC`), the proof proceeds by manipulating sums and applying `REAL_LE_TRANS` to relate the original expression to the sum of the absolute values of differences `abs(ln(&(n + 1)) - ln(k n))`.
- The rest of the proof involves manipulating summations, applying the properties of logarithms and absolute values, and leveraging the fact that `&n < k(n) < &(n + 1)` to bound the differences. The monotonicity of logarithm is then leveraged.
- Finally, induction is used again on `n`.

### Mathematical insight
This theorem provides bounds for the approximation of `ln(n!)` by `n*ln(n) - n`. This is an important result related to Stirling's approximation, which provides an even more precise asymptotic formula for the factorial function. The theorem states that the error in the approximation is bounded by `1 + ln(n)`.

### Dependencies
#### Theorems
- `RIGHT_IMP_EXISTS_THM`
- `REAL_LTE_TRANS`
- `REAL_LE_TRANS`
- `LN_MONO_LT`

#### Definitions
- `FACT`
- `ln`
- `abs`
- `sum`

#### Conversions
- `DIFF_CONV`
- `num_CONV`
- `NUM_REDUCE_CONV`

#### Rules
- `REAL_ARITH`
- `ARITH_RULE`

#### Others
- `MVT_ALT` (Mean Value Theorem)
- `SKOLEM_THM`
- `ADD1`
- `LN_FACT`
- `SUM_LE`
- `REAL_MUL_LID` (identity for real multiplication)
- `REAL_MUL_RID`
- `REAL_MUL_LINV`
- `REAL_LT_IMP_NZ`
- `REAL_OF_NUM_LT`
- `LN_1`
- `REAL_SUB_RZERO`
- `SUM_DIFF`
- `SUM_REINDEX`
- `ABS_SUM`
- `SUM_SUB`
- `ADD_CLAUSES`
- `ADD_AC`
- `REAL_LE_REFL`
- `ADD_EQ_0`
- `REAL_MUL_RZERO`

### Porting notes (optional)
- The proof relies heavily on real arithmetic and properties of logarithms and summations. Therefore, make sure that these are available and well-supported in the target proof assistant.
- The use of `MVT_ALT` suggests that a good formalization of the Mean Value Theorem is required.
- The proof uses some automation, so ensure that the target proof assistant has comparable tactics (e.g., for arithmetic, rewriting, and discharging assumptions).
- Pay attention to the different number types (natural numbers `num`, real numbers `real`). Implicit conversions between these types may need to made explicit.


---

## primepow

### Name of formal statement
primepow

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let primepow = new_definition
  `primepow q <=> ?p k. 1 <= k /\ prime p /\ (q = p EXP k)`;;
```
### Informal statement
A number `q` is a `primepow` if and only if there exist a prime number `p` and a natural number `k` such that `k` is greater than or equal to 1 and `q` is equal to `p` raised to the power of `k`.

### Informal sketch
The definition introduces the concept of a prime power. It states that a number `q` is a prime power if it can be expressed as a prime number `p` raised to some positive integer power `k`.
The purpose is simply to define when a number has this property.
There is nothing to prove, as its a definition.

### Mathematical insight
The `primepow` definition captures the notion of numbers that are powers of prime numbers (e.g., 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, ...). This concept is useful in number theory, for example, in the context of unique factorization.

### Dependencies
- Definitions: `prime`

### Porting notes (optional)
When porting this definition, ensure that the target system has a definitions of primality and exponentiation. In many proof assistants, the exponentiation operator `EXP` will need to be defined separately, perhaps as a recursive function or via repeated multiplication. Pay attention to the handling of natural numbers and ensure that '1' is correctly interpreted as the smallest allowed power.


---

## aprimedivisor

### Name of formal statement
aprimedivisor

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let aprimedivisor = new_definition
  `aprimedivisor q = @p. prime p /\ p divides q`;;
```

### Informal statement
The function `aprimedivisor` is defined such that `aprimedivisor q` returns some `p` such that `p` is a prime number and `p` divides `q`.

### Informal sketch
The definition introduces a function `aprimedivisor` using the definitional axiom `new_definition`. The right-hand side `@p. prime p /\ p divides q` uses Hilbert's choice operator `@` to select *some* `p` satisfying the predicate `prime p /\ p divides q`. The existence of such a `p` needs to be shown to ensure the definition is consistent.

*   The definition introduces a function selecting some prime divisor of a number `q`, provided that such a divisor exists.

### Mathematical insight
This definition introduces a function that selects a prime divisor of a given number. This is a standard construction in number theory.

### Dependencies
*   `prime` (definition of primality)
*   `divides` (definition of divisibility)

### Porting notes (optional)
This definition relies on Hilbert's choice operator.  Many proof assistants have equivalents of Hilbert's choice, but their behavior must be well understood for this definition to work correctly. The definitional principle essentially ensures that the function is well-defined, assuming there exists at least one prime divisor `p` for a given `q` if `q` is greater than 1. The target proof assistant must either have a definitional mechanism similar to HOL Light's `new_definition` or allow the introduction of axioms that assert the properties of Hilbert's choice.


---

## PRIMEPOW_GE_2

### Name of formal statement
PRIMEPOW_GE_2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PRIMEPOW_GE_2 = prove
 (`!q. primepow q ==> 2 <= q`,
  REWRITE_TAC[primepow; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`q:num`; `p:num`; `k:num`] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `p:num` THEN
  ASM_SIMP_TAC[PRIME_GE_2] THEN GEN_REWRITE_TAC LAND_CONV [GSYM EXP_1] THEN
  REWRITE_TAC[LE_EXP] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH]);;
```
### Informal statement
For all `q`, if `q` is a prime power, then 2 is less than or equal to `q`.

### Informal sketch
The proof proceeds as follows:
- Start with the definition of `primepow q` which is `exists p k. prime p /\ 0 < k /\ q = p pow k`.
- Introduce the existential variables `q`, `p`, and `k`.
- Separate the conjunctions from the definition of `primepow`.
- Perform substitution using `q = p pow k`.
- Use transitivity of less than or equal, specifically `LE_TRANS`.
- Instantiate an existential quantifier with `p`.
- Simplify, using `PRIME_GE_2`, which states that for all `p`, if `prime p`, then `2 <= p`.
- Rewrite using `EXP_1` which states `1 < n pow (SUC m)`.
- Rewrite using `LE_EXP`.
- Perform case analysis and arithmetic.

### Mathematical insight
This theorem establishes a fundamental property of prime powers: that they are always greater than or equal to 2. This is a basic result used in number theory.

### Dependencies
- Definitions: `primepow`
- Theorems: `LEFT_IMP_EXISTS_THM`, `PRIME_GE_2`, `LE_TRANS`, `EXP_1`, `LE_EXP`


---

## PRIMEPOW_0

### Name of formal statement
PRIMEPOW_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PRIMEPOW_0 = prove
 (`~(primepow 0)`,
  MESON_TAC[NUM_REDUCE_CONV `2 <= 0`; PRIMEPOW_GE_2]);;
```

### Informal statement
It is not the case that 0 is a prime power.

### Informal sketch
The proof demonstrates that 0 is not a prime power by contradiction. `NUM_REDUCE_CONV \`2 <= 0\`` reduces the inequality `2 <= 0` to false. In conjunction with the theorem `PRIMEPOW_GE_2`, which states that all prime powers are greater than or equal to 2, we obtain a contradiction using automated theorem proving (`MESON_TAC`).

### Mathematical insight
This theorem establishes a basic property of prime powers, namely that 0 is not a prime power. This is important because prime powers are typically defined to be powers of prime numbers, and by definition, prime powers are greater than or equal to 2, or in some definitions 1. 0 does not satisfy these conditions.

### Dependencies
- Theorem: `PRIMEPOW_GE_2`
- Conversion: `NUM_REDUCE_CONV`


---

## APRIMEDIVISOR_PRIMEPOW

### Name of formal statement
APRIMEDIVISOR_PRIMEPOW

### Type of the formal statement
theorem

### Formal Content
```ocaml
let APRIMEDIVISOR_PRIMEPOW = prove
 (`!p k. prime p /\ 1 <= k ==> (aprimedivisor(p EXP k) = p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[aprimedivisor] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC[] THEN
  X_GEN_TAC `q:num` THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
   `1 <= k ==> (k = SUC(k - 1))`)) THEN
  REWRITE_TAC[EXP] THEN
  ASM_MESON_TAC[DIVIDES_REFL; DIVIDES_RMUL; PRIME_DIVEXP; PRIME_DIVPROD;
                prime; PRIME_1]);;
```
### Informal statement
For all prime numbers `p` and natural numbers `k` such that `1 <= k`, the almost prime divisor of `p` raised to the power of `k` (denoted `p EXP k`) is `p`.

### Informal sketch
The proof proceeds by:
- Stripping the quantifiers and the implication.
- Rewriting using the definition of `aprimedivisor`.
- Applying a matching rule to eliminate the existential quantifier in the definition of `aprimedivisor`.
- Introducing an arbitrary number `q` as a potential divisor.
- Applying the arithmetic fact `1 <= k ==> (k = SUC(k - 1))` to rewrite `k`.
- Rewriting using the definition of `EXP`.
- Using the Meson theorem prover with `DIVIDES_REFL`, `DIVIDES_RMUL`, `PRIME_DIVEXP`, `PRIME_DIVPROD`, `prime`, and `PRIME_1` to complete the proof. The Meson prover combines the given facts with assumptions to automatically derive a contradiction when assuming the negation of the goal.

### Mathematical insight
This theorem states a fundamental property of the `aprimedivisor` function when applied to powers of prime numbers. It essentially asserts that the smallest prime divisor of `p^k` is `p` itself when `p` is a prime number. This is an important result for reasoning about prime factorization and divisibility in number theory.

### Dependencies
- Definitions: `aprimedivisor`, `EXP`
- Theorems: `DIVIDES_REFL`, `DIVIDES_RMUL`, `PRIME_DIVEXP`, `PRIME_DIVPROD`, `prime`, `PRIME_1`
- Arithmetic rule: `1 <= k ==> (k = SUC(k - 1))`

### Porting notes (optional)
The proof relies heavily on the Meson prover, which automates the reasoning based on provided lemmas. When porting, ensure similar automation capabilities or be prepared to explicitly construct the divisibility argument. The arithmetic reasoning `1 <= k ==> (k = SUC(k - 1))` might need adaptation depending on how natural numbers and inequalities are represented in the target proof assistant.


---

## APRIMEDIVISOR

### Name of formal statement
APRIMEDIVISOR

### Type of the formal statement
theorem

### Formal Content
```ocaml
let APRIMEDIVISOR = prove
 (`!n. ~(n = 1) ==> prime(aprimedivisor n) /\ (aprimedivisor n) divides n`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[aprimedivisor] THEN
  CONV_TAC SELECT_CONV THEN ASM_SIMP_TAC[PRIME_FACTOR]);;
```

### Informal statement
For all natural numbers `n`, if `n` is not equal to 1, then `aprimedivisor n` is a prime number and `aprimedivisor n` divides `n`.

### Informal sketch
The proof proceeds by induction or by simplification using the definition of `aprimedivisor` and the theorem `PRIME_FACTOR`.
- The goal is to prove that for any natural number `n` not equal to 1, `aprimedivisor n` is a prime divisor of `n`.
- The proof first discharges the assumption `~(n = 1)`.
- It then simplifies the goal using the definition of `aprimedivisor`.
- Simplification is further done using the theorem `PRIME_FACTOR`.
- The theorem `PRIME_FACTOR` states the existence of a prime factor for numbers not equal to 1.

### Mathematical insight
The theorem establishes that for any natural number greater than 1, the function `aprimedivisor` returns a prime number that divides the input number. This is a fundamental result in number theory, as it guarantees the existence of a prime factor for any composite number. The function `aprimedivisor` effectively computes a prime factor.

### Dependencies
- Definitions: `aprimedivisor`, `prime`
- Theorems: `PRIME_FACTOR`


---

## BIG_POWER_LEMMA

### Name of formal statement
BIG_POWER_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BIG_POWER_LEMMA = prove
 (`!m n. 2 <= m ==> ?k. n <= m EXP k`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `SUC n` THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP (SUC n)` THEN
  ASM_REWRITE_TAC[EXP_MONO_LE; NOT_SUC] THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[EXP; ARITH] THEN
  UNDISCH_TAC `n <= 2 EXP SUC n` THEN REWRITE_TAC[EXP] THEN
  MP_TAC(SPECL [`2:num`; `n:num`] EXP_EQ_0) THEN
  REWRITE_TAC[ARITH] THEN SPEC_TAC(`2 EXP n`,`m:num`) THEN ARITH_TAC);;
```

### Informal statement
For all natural numbers `m` and `n`, if `m` is greater than or equal to 2, then there exists a natural number `k` such that `n` is less than or equal to `m` raised to the power of `k`.

### Informal sketch
The proof proceeds by induction on `n`.
- Base case: Show that there exists a `k` such that 0 <= m^k. Since `m` >= 2, we can pick `k` to be `SUC 0` which is 1.
- Inductive step: Assume that `n <= m^k` for some `k`. We want to show that `SUC n <= m^k'` for some `k'`.
    - We instantiate `k'` with `SUC n`, so we aim to prove `SUC n <= m^(SUC n)`.
    - Since `m >= 2`, we have `SUC n <= 2^(SUC n) <= m^(SUC n)`.
    - For the proof of `SUC n <= 2 EXP (SUC n)`, we perform induction on `n`.
        - Base Case: `0 <= 2 EXP (SUC 0)` is equivalent to `0 <= 2 EXP 1` which is `0 <= 2`, which is true.
        - Inductive Step: Assume `n <= 2 EXP (SUC n)`. We need to show `SUC n <= 2 EXP (SUC SUC n)`.
            - `2 EXP (SUC SUC n)` is `2 EXP (SUC n) * 2`.
            - By the inductive hypothesis, `n <= 2 EXP (SUC n)`, therefore `SUC n <= 2 EXP (SUC n) + 1`.
            - We have `2 EXP (SUC n) + 1 <= 2 EXP (SUC n) * 2`, and therefore `SUC n <= 2 EXP (SUC SUC n)`.

### Mathematical insight
This lemma establishes that for any base `m` greater than or equal to 2, any number `n` can be bounded above by some power of `m`. This is a fundamental property used in bounding the growth of functions and proving results in complexity theory and number theory. It highlights how exponential growth (with a base of at least 2) eventually surpasses linear growth.

### Dependencies
- `EXP_MONO_LE`: Monotonicity of exponentiation with respect to <=.
- `NOT_SUC`: The successor function always produces a non-zero result.
- `EXP`: Definition of exponentiation.
- `ARITH`: Arithmetic reasoning, especially linear arithmetic and inequalities.
- `EXP_EQ_0`: Exponentiation with base 0 and power of a natural number.
- `LE_TRANS`: Transitivity of the less than or equal to relation, i.e., if `a <= b` and `b <= c` then `a <= c`.


---

## PRIME_PRIMEPOW

### Name of formal statement
PRIME_PRIMEPOW

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PRIME_PRIMEPOW = prove
 (`!p. prime p ==> primepow p`,
  MESON_TAC[prime; primepow; LE_REFL; EXP_1]);;
```
### Informal statement
For all `p`, if `p` is a prime number, then `p` is a prime power.

### Informal sketch
The proof proceeds by using the definitions of `prime` and `primepow`.
- The definition of `primepow` states that `n` is a prime power if there exists a prime number `p` and a natural number `k` greater than 0 such that `n = p^k`.
- The definition of `prime` states that `p` is prime if `p > 1` and its only divisors are 1 and itself. We want to prove that prime numbers are prime powers.
- If `p` is prime, then `p = p^1`. We know that 1 is greater than 0.
- Therefore, by the definition of `primepow`, `p` is a prime power.

The tactic `MESON_TAC` is used which attempts to automatically discharge the goal using the supplied theorems.

### Mathematical insight
This theorem states a rather trivial but fundamental connection between prime numbers and prime powers. Every prime number is, trivially, also a prime power (with exponent 1). The HOL Light definition of `primepow` likely requires the exponent to be greater than 0, excluding 1 as a prime power.

### Dependencies
- Definitions: `prime`, `primepow`
- Theorems: `LE_REFL`, `EXP_1`


---

## rec

### Name of formal statement
rec

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let rec bezout (m,n) =
  if m =/ num 0 then (num 0,num 1) else if n =/ num 0 then (num 1,num 0)
  else if m <=/ n then
    let q = quo_num n m and r = mod_num n m in
    let (x,y) = bezout(m,r) in
    (x -/ q */ y,y)
  else let (x,y) = bezout(n,m) in (y,x);;
```
### Informal statement
The function `bezout` is defined recursively on a pair of natural numbers (m, n) as follows:
- If m is not equal to 0, then `bezout (m, n)` returns the pair (0, 1).
- Else, if n is not equal to 0, then `bezout (m, n)` returns the pair (1, 0).
- Else, if m is less than or equal to n, then:
  - Let q be the quotient of n divided by m, and r be the remainder of n divided by m.
  - Let (x, y) be the result of `bezout (m, r)`.
  - Then `bezout (m, n)` returns the pair (x - q * y, y).
- Otherwise (i.e., if m > n and both are nonzero), let (x, y) be the result of `bezout (n, m)`. Then `bezout (m, n)` returns the pair (y, x).

### Informal sketch
The definition of `bezout` computes the coefficients x and y in Bezout's identity am + bn = gcd(m, n) for natural numbers m and n.

- Base cases: If either `m` or `n` is zero, return (0, 1) or (1, 0) accordingly. These satisfy the Bezout identity as gcd(m, 0) = m = 1*m + 0*0 and gcd(0, n) = n = 0*0 + 1*n
- Recursive step: If `m <= n`, compute the quotient `q` and remainder `r` of dividing `n` by `m`. Recursively call `bezout (m, r)` to obtain coefficients `x` and `y` such that `xm + yr = gcd(m, r)`. Since `r = n - qm`, we have `xm + y(n - qm) = (x - qy)m + yn = gcd(m, r) = gcd(m, n)`. Thus, return `(x - qy, y)`.
- Otherwise, `m > n`, so recursively call `bezout (n, m)` to obtain coefficients `x` and `y` such that `xn + ym = gcd(n, m)`. Then `ym + xn = gcd(n, m) = gcd(m, n)`, so return `(y, x)`.

### Mathematical insight
This definition provides a recursive algorithm to compute Bezout's identity, which states that for any two integers (or natural numbers), there exist integers (or natural numbers) x and y such that ax + by = gcd(a, b), where gcd(a, b) is the greatest common divisor of a and b.  The algorithm mirrors the Euclidean algorithm for computing the GCD.

### Dependencies
- Definitions: `quo_num`, `mod_num`


---

## PRIMEPOW_CONV

### Name of formal statement
PRIMEPOW_CONV

### Type of the formal statement
Conversion

### Formal Content
```ocaml
let PRIMEPOW_CONV =
  let pth0 = prove
   (`primepow 0 <=> F`,
    REWRITE_TAC[primepow] THEN MESON_TAC[EXP_EQ_0; PRIME_0])
  and pth1 = prove
   (`primepow 1 <=> F`,
    REWRITE_TAC[primepow] THEN
    MESON_TAC[EXP_EQ_1; PRIME_1; NUM_REDUCE_CONV `1 <= 0`])
  and pth2 = prove
   (`prime p ==> 1 <= k /\ (q = p EXP k) ==> (primepow q <=> T)`,
    MESON_TAC[primepow])
  and pth3 = prove
   (`(p * x = r * y + 1) /\ ~(p = 1) /\ ~(r = 1) /\ (q = p * r * d)
     ==> (primepow q <=> F)`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[primepow] THEN
    DISCH_THEN(X_CHOOSE_THEN `P:num` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(SPEC `r:num` PRIME_FACTOR) THEN
    MP_TAC(SPEC `p:num` PRIME_FACTOR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `P_p:num` MP_TAC) THEN
    REWRITE_TAC[divides] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `d_p:num` SUBST_ALL_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `P_r:num` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `d_r:num` SUBST_ALL_TAC) THEN
    SUBGOAL_THEN `P_p divides P /\ P_r divides P` ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC PRIME_DIVEXP THEN EXISTS_TAC `k:num` THEN
      ASM_MESON_TAC[divides; MULT_AC]; ALL_TAC] THEN
    SUBGOAL_THEN `(P_p = P) /\ (P_r = P:num)` (CONJUNCTS_THEN SUBST_ALL_TAC)
    THENL [ASM_MESON_TAC[prime]; ALL_TAC] THEN
    ASM_MESON_TAC[DIVIDES_ADD_REVR; divides; MULT_AC; DIVIDES_ONE; prime])
  and p_tm = `p:num` and k_tm = `k:num` and q_tm = `q:num`
  and r_tm = `r:num` and d_tm = `d:num`
  and x_tm = `x:num` and y_tm = `y:num` and primepow_tm = `primepow` in
  fun tm0 ->
    let ptm,tm = dest_comb tm0 in
    if ptm <> primepow_tm then failwith "expected primepow(numeral)" else
    let q = dest_numeral tm in
    if q =/ num 0 then pth0
    else if q =/ num 1 then pth1 else
    match factor q with
      [] -> failwith "internal failure in PRIMEPOW_CONV"
    | [p,k] -> let th1 = INST [mk_numeral q,q_tm;
                               mk_numeral p,p_tm;
                               mk_numeral k,k_tm] pth2 in
               let th2 = MP th1 (EQT_ELIM(PRIME_CONV(lhand(concl th1)))) in
               MP th2 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th2))))
    | (p,_)::(r,_)::_ ->
               let d = q // (p */ r) in
               let (x,y) = bezout(p,r) in
               let p,r,x,y =
                 if x </ num 0 then r,p,y,minus_num x
                 else p,r,x,minus_num y in
               let th1 = INST [mk_numeral q,q_tm;
                               mk_numeral p,p_tm;
                               mk_numeral r,r_tm;
                               mk_numeral x,x_tm;
                               mk_numeral y,y_tm;
                               mk_numeral d,d_tm] pth3 in
               MP th1 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th1))));;
```
### Informal statement
The function `PRIMEPOW_CONV` is a conversion that, when applied to a term of the form `primepow(q)` where `q` is a numeral, attempts to prove whether `q` is a prime power. It operates as follows:

- If `q` is 0, it returns a proof of `primepow 0 <=> F`.
- If `q` is 1, it returns a proof of `primepow 1 <=> F`.
- If `q` is neither 0 nor 1, it factors `q` into prime factors.
  - If `q` has a unique prime factor `p` with multiplicity `k` (i.e., `q = p^k`), it returns a proof of `prime p ==> 1 <= k /\ (q = p EXP k) ==> (primepow q <=> T)`. Showing that `primepow q` is equivalent to `T` under these conditions.
  - If `q` has at least two distinct prime factors `p` and `r`, it finds integers `x` and `y` such that `p*x + r*y = 1`, and lets `d = q / (p*r)`.  It then returns a proof of `(p * x = r * y + 1) /\ ~(p = 1) /\ ~(r = 1) /\ (q = p * r * d) ==> (primepow q <=> F)`.

### Informal sketch
The conversion `PRIMEPOW_CONV` checks whether a given numeral `q` is a prime power.

- Cases for 0 and 1 are handled directly using rewriting and basic arithmetic facts.
- If `q` has a unique prime factor `p` with multiplicity `k`, the conversion proves `primepow q` is equivalent to true by instantiating a theorem stating that if `p` is prime and `q = p^k` with `k >= 1`, then `q` is a prime power.
- If `q` has distinct prime factors `p` and `r`, the conversion uses Bezout's identity to derive integers `x` and `y` satisfying `p*x + r*y = 1`.  Using this information, along with the fact that `q = p * r * d`, where `d` is the remaining factor, ultimately a contradiction is derived to prove that `primepow q` is equivalent to false. It uses the theorem `PRIME_FACTOR` to decompose `p` and `r` into prime factors `P_p` and `P_r` respectively, and proves that both `P_p` and `P_r` divides `P`, and that `P_p = P` and `P_r = P`, leading to a contradiction using divisibility properties. It leverages several theorems related to divisibility, primality, and arithmetic properties of multiplication and addition. Key tactics used here include `REPEAT STRIP_TAC`, `REWRITE_TAC`, `DISCH_THEN`, existential introduction using `X_CHOOSE_THEN`, and `ASM_MESON_TAC` for discharging assumptions with MESON.

### Mathematical insight
The core idea is to determine if a number `q` is a prime power using its prime factorization. If the prime factorization of `q` contains only one distinct prime number, then `q` is a prime power; otherwise, it's not. The utilization of Bezout's identity when there are two or more distinct prime factors allows construction of a proof that no such `q` can be a prime power by reducing it to contradictions about its prime factors.

### Dependencies
- `primepow` (definition): Defines the `primepow` predicate.
- `EXP_EQ_0`: Theorem that `p EXP 0 = 1`.
- `PRIME_0`: Theorem that 0 is not a prime number.
- `EXP_EQ_1`: Theorem that `p EXP 1 = p`.
- `PRIME_1`: Theorem that 1 is not a prime number.
- `PRIME_CONV`: Conversion for deciding primality.
- `PRIME_FACTOR`: Theorem about the existence of prime factors (probably stating every number has a prime factor).
- `divides` (implicit): Divisibility relation.
- `DIVIDES_ADD_REVR`: Theorem about divisibility and addition.
- `DIVIDES_ONE`: Theorem about divisibility and 1.
- `MULT_AC`: Theorem about the associativity and commutativity of multiplication.

### Porting notes (optional)

- The use of conversions is a distinctive feature of HOL Light. In other provers like Coq or Lean, this could be expressed as a tactic or decision procedure. Factoring the number `q` and analyzing the resulting factors will need to be done carefully.
- The calls to MESON may need to be replaced by more explicit proof steps, depending on the capabilities of the automated reasoners in the target proof assistant.
- The core mathematical reasoning should translate directly, but the automation level may differ.


---

## APRIMEDIVISOR_CONV

### Name of formal statement
APRIMEDIVISOR_CONV

### Type of the formal statement
Theorem and Conversion

### Formal Content
```ocaml
let APRIMEDIVISOR_CONV =
  let pth = prove
   (`prime p ==> 1 <= k /\ (q = p EXP k) ==> (aprimedivisor q = p)`,
    MESON_TAC[APRIMEDIVISOR_PRIMEPOW])
  and p_tm = `p:num` and k_tm = `k:num` and q_tm = `q:num`
  and aprimedivisor_tm = `aprimedivisor` in
  fun tm0 ->
    let ptm,tm = dest_comb tm0 in
    if ptm <> aprimedivisor_tm then failwith "expected primepow(numeral)" else
    let q = dest_numeral tm in
    if q =/ num 0 then failwith "APRIMEDIVISOR_CONV: not a prime power" else
    match factor q with
      [p,k] -> let th1 = INST [mk_numeral q,q_tm;
                               mk_numeral p,p_tm;
                               mk_numeral k,k_tm] pth in
               let th2 = MP th1 (EQT_ELIM(PRIME_CONV(lhand(concl th1)))) in
               MP th2 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th2))))
    | _ -> failwith "APRIMEDIVISOR_CONV: not a prime power";;
```
### Informal statement
Given a term of the form `aprimedivisor q`, where `q` is a prime power, the conversion determines the prime divisor `p` of `q`. 
If `q` is a prime power `p^k` (where `p` is prime and `k` is a natural number greater than or equal to 1), then `aprimedivisor q = p`.

### Informal sketch
- The conversion `APRIMEDIVISOR_CONV` takes a term `tm0` as input.
- It checks if `tm0` is of the form `aprimedivisor q`, where `q` is a numeral. If not, it fails.
- It checks if `q` is a prime power. If not, it fails.
- It factors `q` into a list of prime-exponent pairs `[p, k]`, such that `q = p^k`.
- It instantiates the theorem `APRIMEDIVISOR_PRIMEPOW` with `q`, `p`, and `k`: `prime p ==> 1 <= k /\ (q = p EXP k) ==> (aprimedivisor q = p)`.
- It eliminates the implication using `MP` (modus ponens) along with `PRIME_CONV`, which derives `prime p` by computation.
- It applies numeral reduction (`NUM_REDUCE_CONV`) to the hypothesis `1 <= k /\ (q = p EXP k)` to prove it.
- Finally, it performs another `MP` (modus ponens) with the reduced premise to get `aprimedivisor q = p`.

### Mathematical insight
The theorem formalizes the notion that the `aprimedivisor` function, when applied to a prime power, returns the prime base of that power. This is a fundamental property used in number theory. The conversion is an automated procedure to reduce a term `aprimedivisor q` to its simplest form, `p`, when `q` is a prime power.

### Dependencies
- Definitions: `aprimedivisor`
- Theorems: `APRIMEDIVISOR_PRIMEPOW`
- Tactics: `MESON_TAC`, `EQT_ELIM`, `MP`
- Conversions: `PRIME_CONV`, `NUM_REDUCE_CONV`


---

## mangoldt

### Name of formal statement
mangoldt

### Type of formal statement
new_definition

### Formal Content
```ocaml
let mangoldt = new_definition
  `mangoldt d = if primepow d then ln(&(aprimedivisor d)) else &0`;;
```

### Informal statement
The `mangoldt` function, applied to `d`, is defined as follows: if `d` is a prime power, then the result is the natural logarithm of the unique prime divisor of `d`; otherwise, the result is 0.

### Informal sketch
- The definition introduces a function `mangoldt` that maps a natural number `d` to a real number.
- The definition uses a conditional:
    - If `d` is a prime power (i.e., `primepow d` is true), then `mangoldt d` is the natural logarithm of the unique prime divisor of `d`. The function `aprimedivisor` returns the unique prime divisor of a prime power, and `ln` calculates the natural logarithm, coerced to a real number using the `&` operator.
    - Otherwise (i.e., `d` is not a prime power), `mangoldt d` is 0, coerced to a real number.

### Mathematical insight
The Mangoldt function is a crucial number-theoretic function. It is non-zero precisely at prime powers and is zero otherwise. The value at a prime power is the natural log of the prime which is raised to some power.

### Dependencies
- `primepow`
- `aprimedivisor`
- `ln`


---

## MANGOLDT_POS

### Name of formal statement
MANGOLDT_POS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MANGOLDT_POS = prove
 (`!d. &0 <= mangoldt d`,
  GEN_TAC THEN REWRITE_TAC[mangoldt] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  ASM_MESON_TAC[APRIMEDIVISOR_PRIMEPOW; ARITH_RULE `2 <= a ==> 1 <= a`;
                PRIME_GE_2; LN_POS; REAL_OF_NUM_LE; primepow]);;
```

### Informal statement
For all natural numbers `d`, the real number `mangoldt d` is greater than or equal to 0.

### Informal sketch
The proof proceeds as follows:
- Start by expanding the definition of `mangoldt d`.
- Perform case analysis based on the definition of `mangoldt`, which states:
  - If `d` is a prime power, `mangoldt d` is the natural logarithm of the prime.
  - Otherwise, `mangoldt d` is 0.
- In the case where `mangoldt d` is 0, rewrite using `REAL_LE_REFL` to show `0 <= 0`.
- In the case where `d` is a prime power, use the following facts:
  - `APRIMEDIVISOR_PRIMEPOW`: If `d` is a prime power, then there exists a prime `p` and a natural number `n` such that `d = p^n`.
  - `primepow`: Definition of prime power predicate.
  - `PRIME_GE_2`: Every prime number is greater than or equal to 2.
  - `ARITH_RULE 2 <= a ==> 1 <= a`: Basic arithmetic fact.
  - `LN_POS`: The natural logarithm of a number greater than or equal to 1 is greater than or equal to 0.
  - `REAL_OF_NUM_LE`: Converts a natural number inequality to a real number inequality.
  Since prime numbers are greater than or equal to 2, and 2 is greater than or equal to 1, then the natural logarithm of any prime number must be greater than or equal to zero.
- Use an automated theorem prover (`ASM_MESON_TAC`) along with the enumerated facts to complete the proof.

### Mathematical insight
The `mangoldt` function is always non-negative. This follows from the definition of the `mangoldt` function, which is either 0 or the natural logarithm of a prime number. Since prime numbers are always greater than or equal to 2, and the natural logarithm function is non-negative for numbers greater than or equal to 1, the `mangoldt` function must always be non-negative.

### Dependencies
- Definitions: `mangoldt`, `primepow`
- Theorems: `APRIMEDIVISOR_PRIMEPOW`, `PRIME_GE_2`, `LN_POS`, `REAL_OF_NUM_LE`, `REAL_LE_REFL`
- Tactic: `ARITH_RULE 2 <= a ==> 1 <= a`


---

## LN_PRIMEFACT

### Name of formal statement
LN_PRIMEFACT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LN_PRIMEFACT = prove
 (`!n. ~(n = 0)
       ==> (ln(&n) =
            sum(1,n) (\d. if primepow d /\ d divides n
                          then ln(&(aprimedivisor d)) else &0))`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `n = 1` THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum(1,n) (\d. &0)` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[SUM_0; LN_1]; ALL_TAC] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[PRIMEPOW_GE_2; DIVIDES_LE; NUM_REDUCE_CONV `2 <= 1`;
                  LE_TRANS];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_FACTOR) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_EQ_0; DE_MORGAN_THM]) THEN
  ANTS_TAC THENL
   [ONCE_REWRITE_TAC[ARITH_RULE `m < p * m <=> 1 * m < p * m`] THEN
    SIMP_TAC[LT_MULT_RCANCEL; ARITH_RULE `1 < p <=> 2 <= p`] THEN
    ASM_SIMP_TAC[PRIME_GE_2];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  ASM_SIMP_TAC[LN_MUL; REAL_OF_NUM_LT; ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
  DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `?k. 1 <= k /\ (p EXP k) divides (p * m)` MP_TAC THENL
   [EXISTS_TAC `1` THEN SIMP_TAC[EXP_1; DIVIDES_RMUL; DIVIDES_REFL; LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `?k. !j. 1 <= j /\ (p EXP j) divides (p * m) ==> j <= k`
  MP_TAC THENL
   [MP_TAC(SPECL [`p:num`; `p * m:num`] BIG_POWER_LEMMA) THEN
    ASM_SIMP_TAC[PRIME_GE_2] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    ASM_REWRITE_TAC[MULT_EQ_0] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[NOT_LE] THEN
    DISCH_TAC THEN MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `p EXP k` THEN
    ASM_REWRITE_TAC[LT_EXP] THEN ASM_SIMP_TAC[PRIME_GE_2];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [TAUT `a ==> b ==> c <=> b /\ a ==> c`] THEN
  GEN_REWRITE_TAC LAND_CONV [num_MAX] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `sum (1,m)
     (\d. if primepow d /\ d divides m then ln (&(aprimedivisor d)) else &0) =
    sum (1,p * m)
     (\d. if primepow d /\ d divides m then ln (&(aprimedivisor d)) else &0)`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[SUM_DIFF] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `1 + p * m = (1 + m) + (p * m - m)` SUBST1_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE
        `1 * y <= x ==> (1 + x = (1 + y) + (x - y))`) THEN
      SIMP_TAC[LE_MULT_RCANCEL] THEN
      ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`];
      ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM SUM_TWO] THEN
    MATCH_MP_TAC(REAL_ARITH `(b = &0) ==> (a = a + b)`) THEN
    SUBGOAL_THEN
     `!d. d >= 1 + m
          ==> ((if primepow d /\ d divides m then ln (&(aprimedivisor d))
                else &0) = &0)`
    MP_TAC THENL
     [X_GEN_TAC `d:num` THEN REWRITE_TAC[GE] THEN DISCH_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[DIVIDES_LE; ARITH_RULE `~(1 + m <= d /\ d <= m)`];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUM_ZERO) THEN DISCH_THEN MATCH_MP_TAC THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SUM_DIFF] THEN REWRITE_TAC[SUM_1] THEN
  REWRITE_TAC[PRIMEPOW_0; REAL_SUB_RZERO] THEN
  SUBGOAL_THEN `1 + p * m = p EXP k + 1 + (p * m - p EXP k)` SUBST1_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `k <= p ==> (1 + p = k + 1 + (p - k))`) THEN
    ASM_MESON_TAC[DIVIDES_LE; MULT_EQ_0];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_TWO] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(a = a') /\ (l + b = c) ==> (l + a + b = a' + c)`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `d:num` THEN REWRITE_TAC[ADD_CLAUSES; LE_0] THEN STRIP_TAC THEN
    ASM_CASES_TAC `primepow d` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `d divides (p * m) <=> d divides m`
     (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `primepow d` THEN REWRITE_TAC[primepow] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:num` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` MP_TAC) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_CASES_TAC `q = p:num` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MATCH_MP_TAC(TAUT `(b ==> a) /\ b ==> (a <=> b)`) THEN
      REWRITE_TAC[DIVIDES_LMUL] THEN
      MATCH_MP_TAC DIVIDES_TRANS THEN
      EXISTS_TAC `p EXP (k - 1)` THEN CONJ_TAC THENL
       [REWRITE_TAC[divides] THEN EXISTS_TAC `p EXP ((k - 1) - j)` THEN
        REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN
        UNDISCH_TAC `p EXP j < p EXP k` THEN ASM_REWRITE_TAC[LT_EXP] THEN
        ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `p EXP k divides (p * m)` THEN
      FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (funpow 2 LAND_CONV o RAND_CONV)
                  [th]) o MATCH_MP
          (ARITH_RULE `1 <= k ==> (k = SUC(k - 1))`)) THEN
      REWRITE_TAC[divides; EXP] THEN MATCH_MP_TAC MONO_EXISTS THEN
      SIMP_TAC[GSYM MULT_ASSOC; EQ_MULT_LCANCEL] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EQ_TAC THEN REWRITE_TAC[DIVIDES_LMUL] THEN
    REWRITE_TAC[divides] THEN DISCH_THEN(X_CHOOSE_THEN `r:num` MP_TAC) THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN
      MP_TAC(AP_TERM `(divides) p` th)) THEN
    SIMP_TAC[DIVIDES_RMUL; DIVIDES_REFL] THEN DISCH_TAC THEN
    SUBGOAL_THEN `p divides (q EXP j) \/ p divides r` MP_TAC THENL
     [ASM_MESON_TAC[PRIME_DIVPROD]; ALL_TAC] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [SUBGOAL_THEN `p divides q` MP_TAC THENL
       [ASM_MESON_TAC[PRIME_DIVEXP]; ALL_TAC] THEN
      ASM_MESON_TAC[prime; PRIME_1];
      ALL_TAC] THEN
    UNDISCH_TAC `p * m = q EXP j * r` THEN
    UNDISCH_TAC `p divides r` THEN
    REWRITE_TAC[divides] THEN DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
    ONCE_REWRITE_TAC[ARITH_RULE `a * b * c = b * a * c:num`] THEN
    SIMP_TAC[EQ_MULT_LCANCEL] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM SUM_SPLIT] THEN REWRITE_TAC[SUM_1] THEN
  REWRITE_TAC[REAL_ADD_ASSOC] THEN BINOP_TAC THENL
   [SUBGOAL_THEN `primepow (p EXP k)` ASSUME_TAC THENL
     [ASM_MESON_TAC[primepow]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((p EXP k) divides m)` ASSUME_TAC THENL
     [REWRITE_TAC[divides] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:num` SUBST_ALL_TAC) THEN
      MP_TAC(ARITH_RULE `~(k + 1 <= k)`) THEN REWRITE_TAC[] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[ARITH_RULE `1 <= k + 1`] THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[EXP_ADD; EXP_1] THEN
      MESON_TAC[MULT_ASSOC; DIVIDES_REFL; DIVIDES_RMUL];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_ADD_RID] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_MESON_TAC[APRIMEDIVISOR_PRIMEPOW];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `d:num` THEN REWRITE_TAC[ADD_CLAUSES; LE_0] THEN STRIP_TAC THEN
  ASM_CASES_TAC `primepow d` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `d divides (p * m) <=> d divides m`
   (fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `primepow d` THEN REWRITE_TAC[primepow] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_CASES_TAC `q = p:num` THENL
   [UNDISCH_THEN `q = p:num` SUBST_ALL_TAC THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    MATCH_MP_TAC(TAUT `(b ==> a) /\ ~a ==> (a <=> b)`) THEN
    REWRITE_TAC[DIVIDES_LMUL] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `a + 1 <= b ==> a < b`)) THEN
    REWRITE_TAC[LT_EXP] THEN ASM_SIMP_TAC[PRIME_GE_2; NOT_LT];
    ALL_TAC] THEN
  DISCH_THEN SUBST_ALL_TAC THEN EQ_TAC THEN REWRITE_TAC[DIVIDES_LMUL] THEN
  REWRITE_TAC[divides] THEN DISCH_THEN(X_CHOOSE_THEN `r:num` MP_TAC) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    MP_TAC(AP_TERM `(divides) p` th)) THEN
  SIMP_TAC[DIVIDES_RMUL; DIVIDES_REFL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `p divides (q EXP j) \/ p divides r` MP_TAC THENL
   [ASM_MESON_TAC[PRIME_DIVPROD]; ALL_TAC] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [SUBGOAL_THEN `p divides q` MP_TAC THENL
     [ASM_MESON_TAC[PRIME_DIVEXP]; ALL_TAC] THEN
    ASM_MESON_TAC[prime; PRIME_1];
    ALL_TAC] THEN
  UNDISCH_TAC `p * m = q EXP j * r` THEN
  UNDISCH_TAC `p divides r` THEN
  REWRITE_TAC[divides] THEN DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
  ONCE_REWRITE_TAC[ARITH_RULE `a * b * c = b * a * c:num`] THEN
  SIMP_TAC[EQ_MULT_LCANCEL] THEN ASM_MESON_TAC[]);;
```
### Informal statement
For all natural numbers `n` such that `n` is not equal to 0, it is the case that the natural logarithm of the real representation of `n` is equal to the sum from 1 to `n` of the function that maps `d` to the natural logarithm of the real representation of the `aprimedivisor` of `d` if `d` is a prime power and `d` divides `n`, and to 0 otherwise.

### Informal sketch
The proof proceeds by induction on `n`.

- Base case: `n = 1`. The sum from 1 to 1 of the function is &0 because no `d` such that `1 <= d <= 1` is a prime power and divides 1, appealing to `SUM_0`, `LN_1`, `SUM_EQ`, `PRIMEPOW_GE_2`, `DIVIDES_LE`, `NUM_REDUCE_CONV`, `LE_TRANS`.
- Inductive step: Assume `n > 1`. The proof then introduces the prime factor `p` of `n` using `PRIME_FACTOR`, and writes `n = p * m` for some `m`, where `p` is a prime number. The goal becomes `ln(& (p * m)) = sum(1, p * m) (\d. if primepow d /\ d divides (p * m) then ln(&(aprimedivisor d)) else &0)`.
 It uses the logarithmic identity `ln(x*y) = ln(x) + ln(y)` via `LN_MUL` and induction hypothesis on `m`.
 Subgoals are then established:
- Existence of `k` such that `1 <= k /\ (p EXP k) divides (p * m)` (trivial, choose `k = 1`).
- Existence of `k` such that `!j. 1 <= j /\ (p EXP j) divides (p * m) ==> j <= k`, using `BIG_POWER_LEMMA`.
- Shows that the sum from 1 to `m` is equal to the sum from 1 to `p * m` when the function argument `d` is greater than or equal to `1 + m`.
- Shows `1 + p * m = (1 + m) + (p * m - m)` using `ARITH_RULE` and `SUM_DIFF` to separate the sum.
- Then splits off the sum on 1 using `SUM_SPLIT`, and considers the term for `p EXP k` in the summation.  The proof uses algebraic manipulations of sums, and logical manipulations of `divides` and `primepow`. Case splits are done where needed (e.g. `q = p` where `q` appears in `primepow d = exists q j. prime q /\ d = q EXP j`).

### Mathematical insight
The theorem gives a formula for computing the natural logarithm of a number `n` based on the prime powers that divide `n`. It decomposes `ln(n)` into a sum of logarithms of the prime divisors of the prime powers dividing `n`, which gives important normal form. The `aprimedivisor` function computes the prime base that generates a given prime power.

### Dependencies
- `PRIME_FACTOR`
- `LN_MUL`
- `BIG_POWER_LEMMA`
- `PRIMEPOW_GE_2`
- `DIVIDES_LE`
- `NUM_REDUCE_CONV`
- `LE_TRANS`
- `DIVIDES_LMUL`
- `PRIME_DIVPROD`
- `PRIME_DIVEXP`
- `prime`
- `PRIME_1`

### Porting notes (optional)
- The reliance on `ARITH_TAC` may require more explicit rewriting in other proof assistants.
- The use of tactics like `ASM_CASES_TAC`, `COND_CASES_TAC` indicates significant case splitting which must be handled carefully.
- The theorem `BIG_POWER_LEMMA` will need to be explicitly ported or proven if unavailable.


---

## MANGOLDT

### Name of formal statement
MANGOLDT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MANGOLDT = prove
 (`!n. ln(&(FACT n)) = sum(1,n) (\d. mangoldt(d) * floor(&n / &d))`,
  GEN_TAC THEN REWRITE_TAC[LN_FACT] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1,n) (\m. sum(1,n) (\d. if primepow d /\ d divides m
                                then ln (&(aprimedivisor d))
                                else &0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[LN_PRIMEFACT; ARITH_RULE `~(n = 0) <=> 1 <= n`] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `d < n + 1 ==> (n = d + (n - d))`)) THEN
    DISCH_THEN(fun th ->
     GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[GSYM SUM_SPLIT] THEN
    REWRITE_TAC[REAL_ARITH `(a = a + b) <=> (b = &0)`] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum(1 + d,n - d) (\k. &0)` THEN CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC[SUM_0]] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[DIVIDES_LE; ARITH_RULE
     `1 <= d /\ 1 + d <= r /\ (r <= d \/ (d = 0)) ==> F`];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SUM_SWAP] THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `d:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[mangoldt] THEN
  ASM_CASES_TAC `primepow d` THEN ASM_REWRITE_TAC[SUM_0; REAL_MUL_LZERO] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `1 <= d ==> ~(d = 0)`)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVISION) THEN
  DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
  MAP_EVERY ABBREV_TAC [`q = n DIV d`; `r = n MOD d`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN `floor (&(q * d + r) / &d) = &q` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM FLOOR_UNIQUE] THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ;
                 REAL_OF_NUM_LT; ARITH_RULE `0 < d <=> 1 <= d`] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL] THEN
    REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    UNDISCH_TAC `r < d:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM SUM_SPLIT] THEN
  MATCH_MP_TAC(REAL_ARITH `(b = &0) /\ (a = c) ==> (a + b = c)`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `sum(1 + q * d,r) (\x. &0)` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[SUM_0]] THEN
    MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[] THEN
    X_GEN_TAC `s:num` THEN STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `d divides s` THEN REWRITE_TAC[divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:num` SUBST_ALL_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `1 + x <= y * z ==> x < z * y`)) THEN
    ASM_SIMP_TAC[LT_MULT_RCANCEL; ARITH_RULE `1 <= d ==> ~(d = 0)`] THEN
    REWRITE_TAC[LT_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:num` SUBST_ALL_TAC) THEN
    UNDISCH_TAC `d * (q + SUC e) < r + 1 + q * d` THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES; GSYM ADD_ASSOC] THEN
    REWRITE_TAC[ARITH_RULE `d * q + x < y + 1 + q * d <=> x <= y`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE `a + b <= c ==> a <= c:num`)) THEN
    ASM_REWRITE_TAC[NOT_LE];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SUM_DIFF] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[GSYM SUM_TWO] THEN
  SIMP_TAC[SUM_1; DIVIDES_0; DIVIDES_LMUL; DIVIDES_REFL] THEN
  REWRITE_TAC[REAL_ARITH `(a + b) - b = a`] THEN
  REWRITE_TAC[GSYM SUM_GROUP] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(0,q) (\x. ln (&(aprimedivisor d)))` THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[SUM_CONST; REAL_MUL_AC]] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
    `1 <= d ==> (d = 1 + (d - 1))`)) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC
    (funpow 2 LAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[GSYM SUM_SPLIT; SUM_1] THEN
  SIMP_TAC[DIVIDES_LMUL; DIVIDES_REFL] THEN
  MATCH_MP_TAC(REAL_ARITH `(b = &0) ==> (a + b = a)`) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(m * d + 1,d - 1) (\x. &0)` THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[SUM_0]] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `s:num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [LE_EXISTS] THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num` SUBST_ALL_TAC) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(d divides (t + 1))` MP_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    UNDISCH_TAC `t + m * d + 1 < d - 1 + m * d + 1` THEN
    REWRITE_TAC[LT_ADD_RCANCEL] THEN
    UNDISCH_TAC `d divides (t + m * d + 1)` THEN
    ASM_CASES_TAC `t = 0` THEN ASM_REWRITE_TAC[ADD_CLAUSES] THENL
     [ASM_MESON_TAC[DIVIDES_REFL; DIVIDES_LMUL; DIVIDES_ADD_REVR;
                    DIVIDES_ONE; PRIMEPOW_GE_2; NUM_REDUCE_CONV `2 <= 1`];
      DISCH_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `d divides (t + m * d + 1)` THEN
  ONCE_REWRITE_TAC[ARITH_RULE `t + m * d + 1 = (t + 1) + m * d`] THEN
  MESON_TAC[DIVIDES_REFL; DIVIDES_LMUL; DIVIDES_ADD_REVL]);;
```

### Informal statement
For all natural numbers `n`, the natural logarithm of the factorial of `n` equals the sum from `1` to `n` of `mangoldt(d)` times the floor of the real number `n/d`.

### Informal sketch
The proof establishes the identity by expanding the logarithm of the factorial and relating it to the Mangoldt function.
- The proof starts by rewriting `ln(FACT n)` using `LN_FACT`.
- An existential quantifier is introduced, postulating a double sum.The goal is to show that the left-hand side is equal to that double sum. The double sum iterates over `m` and `d` from 1 to `n`. The summand is `ln(aprimedivisor(d))` if `d` is a prime power and `d` divides `m`, and 0 otherwise.
- It is shown the double sum equals the expression on the right side of the main equality to be proved.
- The order of summation in the double is swapped.
- Then, the definition of the Mangoldt function is applied.
- Cases are split on whether `d` is a prime power.
- Some algebraic manipulations and splitting of sums are performed. `n` is divided by `d` using the division algorithm, obtaining quotient `q` and remainder `r`. The property of the floor function `floor((q*d + r)/d) = q` is used.
- More sum splitting and simplifications finally give the desired identity.

### Mathematical insight
This result connects the factorial function to the Mangoldt function, a central function in number theory that identifies prime powers. It provides a way to express the logarithm of the factorial as a sum involving the Mangoldt function and the floor function.

### Dependencies
- `FACT`
- `ln`
- `sum`
- `mangoldt`
- `floor`
- `LN_FACT`
- `LN_PRIMEFACT`
- `DIVIDES_LE`
- `DIVISION`
- `FLOOR_UNIQUE`
- `INTEGER_CLOSED`
- `REAL_LE_RDIV_EQ`
- `REAL_LT_LDIV_EQ`
- `REAL_OF_NUM_LT`
- `REAL_OF_NUM_ADD`
- `REAL_OF_NUM_MUL`
- `REAL_OF_NUM_LE`
- `REAL_OF_NUM_LT`
- `DIVIDES_0`
- `DIVIDES_LMUL`
- `DIVIDES_REFL`
- `DIVIDES_ONE`
- `DIVIDES_ADD_REVR`
- `PRIMEPOW_GE_2`


---

## psi

### Name of formal statement
- psi

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let psi = new_definition
  `psi(n) = sum(1,n) (\d. mangoldt(d))`;;
```
### Informal statement
- Define a function `psi` such that for any natural number `n`, `psi(n)` is equal to the sum from `1` to `n` of the values of the `mangoldt` function evaluated at `d`.

### Informal sketch
- The definition introduces the Chebyshev psi function, which is a summation of the `mangoldt` function over the divisors of `n`.
- Key steps in creating such definition involve:
  - Defining an appropriate summing operator like `sum` from `1` to `n`.
  - Applying the `mangoldt` function to the divisors `d`.

### Mathematical insight
- The Chebyshev psi function is fundamental in number theory and is closely related to the prime-counting function. It plays a crucial role in the explicit formulas for the distribution of prime numbers.

### Dependencies
- Definitions: `sum`, `mangoldt`


---

## PSI_BOUNDS_LN_FACT

### Name of formal statement
PSI_BOUNDS_LN_FACT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_BOUNDS_LN_FACT = prove
 (`!n. ln(&(FACT(n))) - &2 * ln(&(FACT(n DIV 2))) <= psi(n) /\
       psi(n) - psi(n DIV 2) <= ln(&(FACT(n))) - &2 * ln(&(FACT(n DIV 2)))`,
  X_GEN_TAC `k:num` THEN MP_TAC(SPECL [`k:num`; `2`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  MAP_EVERY ABBREV_TAC [`n = k DIV 2`; `d = k MOD 2`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  REWRITE_TAC[psi; MANGOLDT] THEN
  SUBGOAL_THEN
   `sum (1,n) (\d. mangoldt d * floor (&n / &d)) =
    sum (1,2 * n + d) (\d. mangoldt d * floor (&n / &d))`
  SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 * n + d = n + (n + d)`] THEN
    ONCE_REWRITE_TAC[GSYM SUM_SPLIT] THEN
    REWRITE_TAC[REAL_ARITH `(a = a + b) <=> (b = &0)`] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `sum(1 + n,n + d) (\k. &0)` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[SUM_0]] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ENTIRE] THEN DISJ2_TAC THEN REWRITE_TAC[FLOOR_EQ_0] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE
     `1 + n <= r ==> 0 < r`)) THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_OF_NUM_LT] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_POS; REAL_MUL_LID; REAL_OF_NUM_LT] THEN
    UNDISCH_TAC `1 + n <= r` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_CMUL; GSYM SUM_SUB] THEN
    MATCH_MP_TAC SUM_LE THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH `m * f - &2 * m * f' = m * (f - &2 * f')`] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[MANGOLDT_POS] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&2 * a <= b /\ b <= &2 * a + &1
      ==> b - &2 * a <= &1`) THEN
    ASM_SIMP_TAC[FLOOR_DOUBLE_NUM; ARITH_RULE `0 < r <=> 1 <= r`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1,2 * n + d) (\d. mangoldt d) - sum(1,n) (\d. mangoldt d) =
    sum(1,2 * n + d) (\d. if d <= n then &0 else mangoldt d)`
  SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 * n + d = n + (n + d)`] THEN
    ONCE_REWRITE_TAC[GSYM SUM_SPLIT] THEN
    MATCH_MP_TAC(REAL_ARITH
     `(c = &0) /\ (b = d) ==> ((a + b) - a = c + d)`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `sum(1,n) (\k. &0)` THEN CONJ_TAC THENL
       [ALL_TAC; REWRITE_TAC[SUM_0]] THEN
      MATCH_MP_TAC SUM_EQ THEN
      SIMP_TAC[ARITH_RULE `r < n + 1 <=> r <= n`];
      ALL_TAC] THEN
    MATCH_MP_TAC SUM_EQ THEN
    SIMP_TAC[ARITH_RULE `1 + n <= r ==> ~(r <= n)`];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_CMUL; GSYM SUM_SUB] THEN MATCH_MP_TAC SUM_LE THEN
  X_GEN_TAC `r:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `m * a - &2 * m * b = m * (a - &2 * b)`] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[MANGOLDT_POS] THEN
    ASM_SIMP_TAC[REAL_SUB_LE; FLOOR_DOUBLE_NUM; ARITH_RULE `0 < r <=> 1 <= r`];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `a = a * &1`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[MANGOLDT_POS] THEN
  MATCH_MP_TAC(REAL_ARITH `(b = &0) /\ &1 <= a ==> &1 <= a - &2 * b`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FLOOR_EQ_0] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_OF_NUM_LT;
                 ARITH_RULE `0 < r <=> 1 <= r`] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_POS] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_REWRITE_TAC[GSYM NOT_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(a = &1) ==> &1 <= a`) THEN
  REWRITE_TAC[GSYM FLOOR_UNIQUE; INTEGER_CLOSED] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_OF_NUM_LT;
               ARITH_RULE `0 < r <=> 1 <= r`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT; REAL_OF_NUM_MUL;
              REAL_OF_NUM_ADD] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC);;
```

### Informal statement
For all natural numbers `n`, the natural logarithm of the factorial of `n` minus two times the natural logarithm of the factorial of `n` divided by 2 is less than or equal to `psi(n)`, and `psi(n)` minus `psi(n` divided by 2) is less than or equal to the natural logarithm of the factorial of `n` minus two times the natural logarithm of the factorial of `n` divided by 2.

### Informal sketch
The proof establishes an upper and lower bound for the Chebyshev function `psi(n)` in terms of logarithms of factorials. The main steps involve:
- Generalizing the goal by introducing `k:num`.
- Splitting the goal into two subgoals using `CONJUNCTS_THEN2`.
- Rewriting `psi` with `MANGOLDT`.
- Splitting a summation and proving its parts are equal to `&0`
- Splitting a summation and proving a less than relation

Specifically, the proof proceeds by induction on `n` and leverages properties of the Mangoldt function, floor function, and summation.

*   The proof starts by generalizing the goal and performing some initial arithmetic simplifications (`X_GEN_TAC`, `MP_TAC`, `REWRITE_TAC`).
*   The variable `k` is divided into `n` and `d` using `MAP_EVERY ABBREV_TAC`, likely representing quotient and remainder.
*   The theorem is split into two parts, each concerning one of the inequalities (`DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)`).
*   The definition of `psi` is unfolded using `REWRITE_TAC`.
*   Several manipulations involving sums are applied. Specifically sums are split using `SUM_SPLIT` and differences of sums are expressed as sums of differences.
*   The inequalities are established using a combination of algebraic manipulation, properties of the floor function, and lemmas about the Mangoldt function. The tactics `MATCH_MP_TAC` and `ASM_SIMP_TAC` are used extensively along with `REAL_ARITH`.

### Mathematical insight
The theorem relates the Chebyshev function `psi(n)`, which sums the von Mangoldt function over all integers up to `n`, to logarithmic expressions involving factorials. This provides a bound on `psi(n)` via more elementary functions (factorials and logarithms), which is useful in analytic number theory.

### Dependencies
- `FACT`
- `psi`
- `MANGOLDT`
- `DIVISION`
- `ARITH_EQ`
- `MULT_SYM`
- `SUM_SPLIT`
- `SUM_0`
- `SUM_EQ`
- `SUM_CMUL`
- `SUM_SUB`
- `SUM_LE`
- `REAL_ENTIRE`
- `FLOOR_EQ_0`
- `REAL_LE_RDIV_EQ`
- `REAL_LT_LDIV_EQ`
- `REAL_OF_NUM_LT`
- `REAL_MUL_LZERO`
- `REAL_POS`
- `REAL_MUL_LID`
- `REAL_LE_LMUL`
- `MANGOLDT_POS`
- `FLOOR_DOUBLE_NUM`
- `FLOOR_UNIQUE`
- `INTEGER_CLOSED`
- `REAL_OF_NUM_MUL`
- `REAL_OF_NUM_LE`
- `REAL_OF_NUM_ADD`

### Porting notes (optional)
- The theorem relies heavily on real and arithmetic reasoning. A target proof assistant should ideally have good automation for these domains.
- Summation manipulation is a key part of the proof. Ensure the target system has equivalent summation tactics.
- The use of `FLOOR` and related lemmas requires a well-developed theory of integers and reals.


---

## LN_FACT_DIFF_BOUNDS

### Name of formal statement
LN_FACT_DIFF_BOUNDS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LN_FACT_DIFF_BOUNDS = prove
 (`!n. abs((ln(&(FACT(n))) - &2 * ln(&(FACT(n DIV 2)))) - &n * ln(&2))
       <= &4 * ln(if n = 0 then &1 else &n) + &3`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_SIMP_TAC[FACT; MULT_CLAUSES; LN_1; DIV_0; ARITH_EQ] THEN
    REWRITE_TAC[REAL_MUL_LZERO] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  MAP_EVERY ABBREV_TAC [`q = n DIV 2`; `r = n MOD 2`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  ASM_CASES_TAC `q = 0` THENL
   [UNDISCH_TAC `~(q * 2 + r = 0)` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    ASM_SIMP_TAC[ARITH_RULE `r < 2 ==> ((r = 0) <=> ~(r = 1))`] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    REWRITE_TAC[num_CONV `1`; FACT; MULT_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[LN_1] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_LZERO; REAL_SUB_RZERO] THEN
    REWRITE_TAC[REAL_NEG_0; REAL_SUB_LZERO; REAL_ADD_LID; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_ABS_NEG] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= &2 ==> x <= &3`) THEN
    SUBST1_TAC(REAL_ARITH `&2 = &1 + &1`) THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= x /\ x <= &1 ==> abs(x) <= &1 + &1`) THEN
    ASM_SIMP_TAC[LN_POS; LN_LE; REAL_OF_NUM_LE; ARITH; REAL_LE_ADDL];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!a'. abs((a' - b) - c) <= d - abs(a' - a) ==> abs((a - b) - c) <= d`) THEN
  EXISTS_TAC `ln(&(FACT(q * 2)))` THEN
  MP_TAC(SPEC `q:num` LN_FACT_BOUNDS) THEN
  MP_TAC(SPEC `q * 2` LN_FACT_BOUNDS) THEN
  ASM_REWRITE_TAC[MULT_EQ_0; ARITH_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs(a - (a2 - &2 * a1)) <= b - &2 * b1 - b2
    ==> abs(l2 - a2) <= b2
        ==> abs(l1 - a1) <= b1
            ==> abs((l2 - &2 * l1) - a) <= b`) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  ASM_SIMP_TAC[LN_MUL; REAL_OF_NUM_LT; ARITH;
               ARITH_RULE `0 < q <=> ~(q = 0)`] THEN
  REWRITE_TAC[REAL_ARITH
   `(q * &2 + r) * l2 - ((q * &2) * (lq + l2) - q * &2 - &2 * (q * lq - q)) =
    r * l2`] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `x <= a - b - c - d <=> x + b <= a - c - d`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `ln(&2) + ln(&q * &2 + &r)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &1 * y ==> abs(x) <= y`) THEN
      SIMP_TAC[LN_POS_LT; REAL_LT_IMP_LE; REAL_LE_RMUL_EQ;
               REAL_LE_MUL; REAL_POS; REAL_OF_NUM_LT; ARITH] THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN UNDISCH_TAC `r < 2` THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC o MATCH_MP (ARITH_RULE
     `r < 2 ==> (r = 0) \/ (r = 1)`))
    THENL
     [REWRITE_TAC[ADD_CLAUSES; REAL_SUB_REFL; REAL_ADD_RID; REAL_ABS_NUM] THEN
      MATCH_MP_TAC LN_POS THEN
      REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_MUL] THEN
      UNDISCH_TAC `~(q = 0)` THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM ADD1; FACT] THEN
    SIMP_TAC[GSYM REAL_OF_NUM_MUL; LN_MUL; REAL_OF_NUM_LT;
             FACT_LT; LT_0] THEN
    REWRITE_TAC[REAL_ARITH `abs(b - (a + b)) = abs a`] THEN
    REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_SUC; GSYM REAL_OF_NUM_ADD;
                GSYM REAL_OF_NUM_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs(x) <= x`) THEN
    MATCH_MP_TAC LN_POS THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH
   `l2 + lnn <= (&4 * lnn + &3) - a - b
    <=> a + b + l2 <= &3 * lnn + &3`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&3 * ln(&q * &2) + &3` THEN CONJ_TAC THENL
   [ALL_TAC;
    SIMP_TAC[REAL_LE_RADD; REAL_LE_LMUL_EQ; REAL_OF_NUM_LT; ARITH] THEN
    ASM_SIMP_TAC[LN_MONO_LE; REAL_POS; REAL_OF_NUM_LT;
                 ARITH_RULE `0 < q <=> ~(q = 0)`;
                 REAL_ARITH `&0 < q /\ &0 <= r ==> &0 < q * &2 + r`;
                 REAL_ARITH `&0 < q ==> &0 < q * &2`] THEN
    REWRITE_TAC[REAL_LE_ADDR; REAL_POS]] THEN
  ASM_SIMP_TAC[LN_MUL; REAL_OF_NUM_LT; ARITH;
               ARITH_RULE `0 < q <=> ~(q = 0)`] THEN
  SUBGOAL_THEN `&0 <= ln(&2)` (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
  MATCH_MP_TAC LN_POS THEN REWRITE_TAC[REAL_OF_NUM_LE; ARITH]);;
```

### Informal statement
For all natural numbers `n`, the absolute value of the difference between `ln(FACT(n)) - 2 * ln(FACT(n DIV 2))` and `n * ln(2)` is less than or equal to `4 * ln(if n = 0 then 1 else n) + 3`.

### Informal sketch
The proof proceeds by induction on `n`.

- Base case: `n = 0`. Simplify using `FACT`, `MULT_CLAUSES`, `LN_1`, `DIV_0`, `ARITH_EQ` and `REAL_MUL_LZERO`. Reduce the resulting rational constant and prove the equality.
- Inductive step: Assume the theorem holds for some `n`. Prove that it holds for `n+1`. First, use the division algorithm to express `n` as `2q + r`, where `q = n DIV 2` and `r = n MOD 2`.
- Case split based on `q = 0`.
  - If `q = 0`, and thus `n = r < 2`, use arithmetic simplification and rewriting with `FACT`, `MULT_CLAUSES`, `LN_1`, `REAL_MUL_RZERO`, `REAL_SUB_LZERO`, `REAL_SUB_RZERO`, `REAL_NEG_0`, `REAL_ADD_LID`, `REAL_MUL_LID`, and `REAL_ABS_NEG`. Simplify using `LN_POS`, `LN_LE`, `REAL_OF_NUM_LE`, and `ARITH`.
  - If `q > 0`, use the inductive hypothesis on `q` and `2q`. Apply the arithmetic result `abs(a - (a2 - 2 * a1)) <= b - 2 * b1 - b2 ==> abs(l2 - a2) <= b2 ==> abs(l1 - a1) <= b1 ==> abs((l2 - 2 * l1) - a) <= b`. Rewrite using properties of `REAL_OF_NUM` and `LN_MUL`, simplifying using `ARITH`. Rewrite to isolate the term to be bounded.
- Apply `REAL_LE_TRANS`.
- To bound the remaining terms, prove that `abs(x) <= y` holds, using simplification with monotonicity of `LN`, positivity properties, and arithmetic.
- Rewrite using arithmetic and properties of `REAL_OF_NUM`. Use the fact that `0 <= ln(2)` and simplify with `ARITH_TAC`.

### Mathematical insight
This theorem provides bounds on the difference between `ln(FACT(n))` and its approximation using `ln(FACT(n DIV 2))`. It relates to Stirling's approximation for the factorial function and provides error bounds. This type of bounds is useful in complexity analysis and numerical algorithms.

### Dependencies
- Definitions: `FACT`
- Theorems: `DIVISION`, `LN_FACT_BOUNDS`, `LN_MUL`, `LN_POS_LT`, `REAL_LT_IMP_LE`, `REAL_LE_RMUL_EQ`, `REAL_LE_MUL`, `REAL_POS`, `REAL_OF_NUM_LT`, `ADD1`, `FACT_LT`, `LT_0`, `LN_POS`, `LN_LE`, `REAL_OF_NUM_LE`, `REAL_LE_ADDL`, `REAL_LE_TRANS`, `REAL_LE_ADD2`, `REAL_LE_RADD`, `REAL_LE_LMUL_EQ`, `LN_MONO_LE`
- Rules: `MULT_CLAUSES`, `LN_1`, `DIV_0`, `ARITH_EQ`, `ADD_CLAUSES`, `REAL_MUL_LZERO`, `REAL_MUL_RZERO`, `REAL_SUB_LZERO`, `REAL_SUB_RZERO`, `REAL_NEG_0`, `REAL_ADD_LID`, `REAL_MUL_LID`, `REAL_ABS_NEG`, `REAL_ARITH`, `REAL_OF_NUM_ADD`, `REAL_OF_NUM_MUL`

### Porting notes
- The frequent use of `REAL_ARITH` suggests that a powerful arithmetic decision procedure is required in the target proof assistant.
- Special attention needs to be given to the handling of real numbers and their interaction with natural numbers, as the conversion between these types is pervasive via `REAL_OF_NUM`.
- Tactics like `ASM_CASES_TAC`, `ASM_REWRITE_TAC`, and `ASM_SIMP_TAC` rely heavily on the automation capabilities of HOL Light. You might need to replace these with more explicit proof steps in other proof assistants.


---

## PSI_BOUNDS_INDUCT

### Name of formal statement
PSI_BOUNDS_INDUCT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_BOUNDS_INDUCT = prove
 (`!n. &n * ln(&2) - (&4 * ln (if n = 0 then &1 else &n) + &3) <= psi(n) /\
       psi(n) - psi(n DIV 2)
       <= &n * ln(&2) + (&4 * ln (if n = 0 then &1 else &n) + &3)`,
  MESON_TAC[PSI_BOUNDS_LN_FACT; LN_FACT_DIFF_BOUNDS; REAL_ARITH
             `m <= a /\ b <= m /\ abs(m - n) <= k
              ==> n - k <= a /\ b <= n + k`]);;
```
### Informal statement
For all natural numbers `n`, the digamma function `psi(n)` is bounded as follows:
`n * ln(2) - (4 * ln(if n = 0 then 1 else n) + 3) <= psi(n)`
and
`psi(n) - psi(n DIV 2) <= n * ln(2) + (4 * ln(if n = 0 then 1 else n) + 3)`.

### Informal sketch
The theorem establishes upper and lower bounds for the digamma function `psi(n)` and the difference `psi(n) - psi(psi(n DIV 2))`. The proof uses:
- `PSI_BOUNDS_LN_FACT`: This likely provides some initial bounds or facts about the digamma function and its relation to logarithms.
- `LN_FACT_DIFF_BOUNDS`: This likely gives the bounds for difference of logarithm functions.
- `REAL_ARITH 'm <= a /\ b <= m /\ abs(m - n) <= k ==> n - k <= a /\ b <= n + k'`: This is a real arithmetic fact stating that if `m` is between `a` and `b`, and the absolute difference between `m` and `n` is at most `k`, then `n - k <= a` and `b <= n + k`.
The MESON tactic combines these facts to prove the overall bounds.

### Mathematical insight
This theorem provides explicit bounds for the digamma function `psi(n)` in terms of elementary functions like `n * ln(2)` and `ln(n)`. These bounds are likely useful for estimating the growth rate of `psi(n)` and for comparing it to other related functions. Specifically these bounds describe the inductive step to bounds.

### Dependencies
- `PSI_BOUNDS_LN_FACT`
- `LN_FACT_DIFF_BOUNDS`
- `REAL_ARITH`


---

## MANGOLDT_CONV

### Name of formal statement
MANGOLDT_CONV

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MANGOLDT_CONV =
  GEN_REWRITE_CONV I [mangoldt] THENC
  RATOR_CONV(LAND_CONV PRIMEPOW_CONV) THENC
  GEN_REWRITE_CONV I [COND_CLAUSES] THENC
  TRY_CONV(funpow 2 RAND_CONV APRIMEDIVISOR_CONV);;
```

### Informal statement
The conversion `MANGOLDT_CONV` simplifies expressions of the form `mangoldt n`, where `n` is a numeral. It does this by first rewriting using the definition of `mangoldt`, then simplifying the resulting conjunction involving `primepow` using its definition, then rewriting using conditional clauses (`COND_CLAUSES`), and finally repeatedly applying `APRIMEDIVISOR_CONV` up to two times if applicable.

### Informal sketch
The conversion `MANGOLDT_CONV` evaluates the `mangoldt` function applied to a numeral. The process involves the following steps:

- Unfold the definition of the `mangoldt` function using `GEN_REWRITE_CONV I [mangoldt]`. The `mangoldt` function returns `log p` if the input is a prime power `p^k` for some prime `p` and integer `k >= 1`, and `0` otherwise.
- Simplify the conjunction resulting from the definition of `mangoldt` by unfolding the definition of `primepow` using `RATOR_CONV(LAND_CONV PRIMEPOW_CONV)`. This step essentially expands the predicate `primepow n` to its definition, which states that `n` is a power of a prime number.
- Rewrite the expression using conditional clauses (`COND_CLAUSES`) using `GEN_REWRITE_CONV I [COND_CLAUSES]` to reduce the conditions based on the properties of numerals such as transitivity and reflexivity.
- Optionally, apply the conversion `APRIMEDIVISOR_CONV` up to two times to simplify the expression, using `TRY_CONV(funpow 2 RAND_CONV APRIMEDIVISOR_CONV)`. The `APRIMEDIVISOR_CONV` is likely responsible for handling cases involving prime divisors. `funpow 2` causes the conversion to be applied at most twice.

### Mathematical insight
The `mangoldt` function is a crucial concept in number theory, related to the distribution of prime numbers. Evaluating `mangoldt` for a given numeral is a basic step in computing arithmetic functions and verifying properties related to prime numbers. This conversion provides a way to efficiently compute `mangoldt(n)` within the theorem prover itself.

### Dependencies
- `mangoldt` (definition of the Mangoldt function)
- `primepow` (definition of the prime power predicate)
- `COND_CLAUSES` (conditional clauses, likely tautologies helpful for simplifying conditions)
- `APRIMEDIVISOR_CONV` (conversion related to prime divisors)


---

## MANGOLDT_CONV

### Name of formal statement
MANGOLDT_CONV

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let MANGOLDT_CONV =
  let pth0 = prove
   (`mangoldt 0 = ln(&1)`,
    REWRITE_TAC[mangoldt; primepow; LN_1] THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[EXP_EQ_0; PRIME_0])
  and pth1 = prove
   (`mangoldt 1 = ln(&1)`,
    REWRITE_TAC[mangoldt; primepow; LN_1] THEN COND_CASES_TAC THEN
    ASM_MESON_TAC[EXP_EQ_1; PRIME_1; NUM_REDUCE_CONV `1 <= 0`])
  and pth2 = prove
   (`prime p ==> 1 <= k /\ (q = p EXP k) ==> (mangoldt q = ln(&p))`,
    SIMP_TAC[mangoldt; APRIMEDIVISOR_PRIMEPOW] THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[primepow])
  and pth3 = prove
   (`(p * x = r * y + 1) /\ ~(p = 1) /\ ~(r = 1) /\ (q = p * r * d)
     ==> (mangoldt q = ln(&1))`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `~(primepow q)`
     (fun th -> REWRITE_TAC[LN_1; th; mangoldt]) THEN
    REWRITE_TAC[primepow] THEN
    DISCH_THEN(X_CHOOSE_THEN `P:num` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(SPEC `r:num` PRIME_FACTOR) THEN
    MP_TAC(SPEC `p:num` PRIME_FACTOR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `P_p:num` MP_TAC) THEN
    REWRITE_TAC[divides] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `d_p:num` SUBST_ALL_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `P_r:num` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `d_r:num` SUBST_ALL_TAC) THEN
    SUBGOAL_THEN `P_p divides P /\ P_r divides P` ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC PRIME_DIVEXP THEN EXISTS_TAC `k:num` THEN
      ASM_MESON_TAC[divides; MULT_AC]; ALL_TAC] THEN
    SUBGOAL_THEN `(P_p = P) /\ (P_r = P:num)` (CONJUNCTS_THEN SUBST_ALL_TAC)
    THENL [ASM_MESON_TAC[prime]; ALL_TAC] THEN
    ASM_MESON_TAC[DIVIDES_ADD_REVR; divides; MULT_AC; DIVIDES_ONE; prime])
  and p_tm = `p:num` and k_tm = `k:num` and q_tm = `q:num`
  and r_tm = `r:num` and d_tm = `d:num`
  and x_tm = `x:num` and y_tm = `y:num` and mangoldt_tm = `mangoldt` in
  fun tm0 ->
    let ptm,tm = dest_comb tm0 in
    if ptm <> mangoldt_tm then failwith "expected mangoldt(numeral)" else
    let q = dest_numeral tm in
    if q =/ num 0 then pth0
    else if q =/ num 1 then pth1 else
    match factor q with
      [] -> failwith "internal failure in MANGOLDT_CONV"
    | [p,k] -> let th1 = INST [mk_numeral q,q_tm;
                               mk_numeral p,p_tm;
                               mk_numeral k,k_tm] pth2 in
               let th2 = MP th1 (EQT_ELIM(PRIME_CONV(lhand(concl th1)))) in
               MP th2 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th2))))
    | (p,_)::(r,_)::_ ->
               let d = q // (p */ r) in
               let (x,y) = bezout(p,r) in
               let p,r,x,y =
                 if x </ num 0 then r,p,y,minus_num x
                 else p,r,x,minus_num y in
               let th1 = INST [mk_numeral q,q_tm;
                               mk_numeral p,p_tm;
                               mk_numeral r,r_tm;
                               mk_numeral x,x_tm;
                               mk_numeral y,y_tm;
                               mk_numeral d,d_tm] pth3 in
               MP th1 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th1))));;
```

### Informal statement
The theorem defines a conversion `MANGOLDT_CONV` that evaluates the `mangoldt` function at a given natural number. The `mangoldt` function is defined as follows:
- `mangoldt 0 = ln(1)`
- `mangoldt 1 = ln(1)`
- If `p` is a prime number and `q = p^k` for some natural number `k` such that `1 <= k`, then `mangoldt q = ln(p)`.
- If `p`, `r`, `x`, `y`, and `d` are natural numbers such that `p * x = r * y + 1`, `~(p = 1)`, `~(r = 1)`, and `q = p * r * d`, then `mangoldt q = ln(1)`.
If none of these forms apply, the tactic fails.

### Informal sketch
The conversion `MANGOLDT_CONV` works by cases on the input number `q` to the `mangoldt` function.:

- If `q = 0`, the theorem `mangoldt 0 = ln(&1)` is proved by rewriting with the definitions of `mangoldt`, `primepow`, and `LN_1`, then simplifying with `COND_CASES_TAC`, and using `ASM_MESON_TAC` with theorems about exponentials.
- If `q = 1`, the theorem `mangoldt 1 = ln(&1)` is proved similarly, using the definitions of `mangoldt`, `primepow`, and `LN_1`, simplifying with `COND_CASES_TAC`, and using `ASM_MESON_TAC` with theorems about exponentials and the fact that `1 <= 0` is false.
- If `q` is a prime power, i.e., `q = p^k` for some prime `p` and natural number `k >= 1`, then the theorem `prime p ==> 1 <= k /\ (q = p EXP k) ==> (mangoldt q = ln(&p))` is used. This is proved by simplifying with the definitions of `mangoldt` and `APRIMEDIVISOR_PRIMEPOW`, simplifying with `COND_CASES_TAC`, and using `ASM_MESON_TAC` with the definition of `primepow`.
- If `q` can be written as `q = p * r * d` such that `p * x = r * y + 1`, `~(p = 1)`, and `~(r = 1)` for some natural numbers `p`, `r`, `x`, `y`, and `d`, then the theorem `(p * x = r * y + 1) /\ ~(p = 1) /\ ~(r = 1) /\ (q = p * r * d) ==> (mangoldt q = ln(&1))` is used. This is proved by showing that `q` is not a prime power, and rewriting with the definition of `mangoldt` and `LN_1`. This involves using `PRIME_FACTOR` to factor `p` and `r`, and using the fact that if `P_p divides P` and `P_r divides P`, then `(P_p = P) /\ (P_r = P)`.
- The function `factor` computes the prime factorization if `q`
- The function `bezout` computes `x`, `y` such that `p*x+r*y=gcd(p,r)`

### Mathematical insight
The `mangoldt` function is a crucial function in number theory, especially in the study of prime numbers. It's defined based on the prime factorization of the input number. Specifically, it's non-zero (equal to the logarithm of the prime) only when the input is a prime power; otherwise, it is zero. This function is essential for various results related to the distribution of primes and estimating sums over prime numbers. The theorem provides an effective way to compute the value of the `mangoldt` function for any given natural number.

### Dependencies
- Definitions: `mangoldt`, `primepow`, `prime`
- Theorems: `LN_1`, `EXP_EQ_0`, `PRIME_0`, `EXP_EQ_1`, `PRIME_1`, `NUM_REDUCE_CONV`, `APRIMEDIVISOR_PRIMEPOW`, `DIVIDES_ADD_REVR`, `divides`, `MULT_AC`, `DIVIDES_ONE`, `PRIME_FACTOR`


---

## PSI_LIST

### Name of formal statement
PSI_LIST

### Type of the formal statement
Definition

### Formal Content
```ocaml
let PSI_LIST =
  let PSI_0 = prove
   (`psi(0) = ln(&1)`,
    REWRITE_TAC[psi; sum; LN_1])
  and PSI_SUC = prove
   (`psi(SUC n) = psi(n) + mangoldt(SUC n)`,
    REWRITE_TAC[psi; sum; ADD1] THEN REWRITE_TAC[ADD_AC])
  and n_tm = `n:num`
  and SIMPER_CONV =
    SIMP_CONV [REAL_ADD_RID; GSYM LN_MUL; REAL_OF_NUM_MUL;
               REAL_OF_NUM_LT; ARITH] in
  let rec PSI_LIST n =
    if n = 0 then [PSI_0] else
    let ths = PSI_LIST (n - 1) in
    let th1 = INST [mk_small_numeral(n-1),n_tm] PSI_SUC in
    let th2 = GEN_REWRITE_RULE (RAND_CONV o LAND_CONV) [hd ths] th1 in
    let th3 = CONV_RULE(COMB_CONV (funpow 2 RAND_CONV NUM_SUC_CONV)) th2 in
    let th4 = CONV_RULE (funpow 2 RAND_CONV MANGOLDT_CONV) th3 in
    (CONV_RULE(RAND_CONV SIMPER_CONV) th4)::ths in
  PSI_LIST;;
```

### Informal statement
The function `PSI_LIST`, when applied to a natural number `n`, returns a list of theorems.
The first theorem in the list asserts that `psi(0) = ln(1)`. The subsequent theorems express `psi(SUC n) = psi(n) + mangoldt(SUC n)`, where `SUC n` is the successor of `n`, `psi` is the Chebyshev function, `mangoldt` is the Mangoldt function, and `ln` is the natural logarithm.
Specifically, the list consists of proofs of `psi(0) = ln(1)` and `psi(i) = psi(i-1) + mangoldt(i)` for each `i` from 1 to `n`.

### Informal sketch
The definition constructs a list of theorems proving the evaluation of the Chebyshev function `psi(n)` for all natural numbers up to a given `n`.

- Base Case (`n = 0`): The list contains a single theorem proving `psi(0) = ln(1)`. This uses rewriting with `psi`, `sum`, and `LN_1`.
- Inductive Step (`n > 0`):
  - Recursively compute the list of theorems for `n - 1`.
  - Instantiate the theorem `PSI_SUC` (which states `psi(SUC n) = psi(n) + mangoldt(SUC n)`) with `n - 1`, obtaining a theorem about `psi(n)`.
  - Use the first theorem in the list for `n-1` (i.e., the theorem stating `psi(0) = ln(1)` if `n = 1` or `psi(n-1) = ...` if `n > 1`) to rewrite the instantiated `PSI_SUC` theorem. The rewrite involves `LAND_CONV` and `RAND_CONV`.
  - Apply conversions to simplify the rewritten theorem. These conversions include `NUM_SUC_CONV` repeated twice on the right-hand side (`RAND_CONV`), followed by `MANGOLDT_CONV` repeated twice on the right-hand side.
  - Further simplify the theorem using `SIMPER_CONV`, which applies rules like `REAL_ADD_RID`, the inverse of `LN_MUL`, `REAL_OF_NUM_MUL`, `REAL_OF_NUM_LT`, and `ARITH`.
  - Prepend the simplified theorem about `psi(n)` to the list of theorems for `n - 1`.

### Mathematical insight
The `PSI_LIST` definition provides a way to compute and prove the value of the Chebyshev function `psi(n)` for a range of natural numbers. It leverages the recurrence relation `psi(n+1) = psi(n) + mangoldt(n+1)`. The resulting list of theorems provides a verified computation of the Chebyshev function.

### Dependencies
- Definitions:
  - `psi` (Chebyshev function)
  - `mangoldt` (Mangoldt function)
  - `sum`
- Theorems/Lemmas:
  - `LN_1`
  - `ADD1`
  - `ADD_AC`
- Conversion tactics/rules:
  - `REAL_ADD_RID`
  - `LN_MUL`
  - `REAL_OF_NUM_MUL`
  - `REAL_OF_NUM_LT`
  - `ARITH`
  - `NUM_SUC_CONV`
  - `MANGOLDT_CONV`


---

## PSI_LIST_300

### Name of formal statement
PSI_LIST_300

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let PSI_LIST_300 = PSI_LIST 300;;
```

### Informal statement
Define `PSI_LIST_300` to be equal to `PSI_LIST` applied to 300.

### Informal sketch
The definition introduces a specific instance of a parameterized function. It directly applies `PSI_LIST` to the natural number 300. No proof is involved, as it is a direct definition.

### Mathematical insight
This definition likely computes a specific list or data structure derived from the function `PSI_LIST` when instantiated with the value 300. It's probably an element within a larger computation or experiment done for up to 300 iterations/elements.

### Dependencies
- Definition: `PSI_LIST`


---

## PSI_UBOUND_128

### Name of formal statement
PSI_UBOUND_128

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_UBOUND_128 = prove
 (`!n. n <= 128 ==> psi(n) <= &133 / &128 * &n`,
  let lemma = prove
   (`a <= b /\ l <= a /\ rest ==> l <= a /\ l <= b /\ rest`,
    MESON_TAC[REAL_LE_TRANS])
  and tac = time (CONV_TAC(LAND_CONV LN_N2_CONV THENC REALCALC_REL_CONV)) in
  REWRITE_TAC[ARITH_RULE `n <= 128 <=> n < 129`] THEN
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC(PSI_LIST_300) THEN
  REWRITE_TAC[LN_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REPEAT
   ((MATCH_MP_TAC lemma THEN
     CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN
     GEN_REWRITE_TAC I [TAUT `T /\ a <=> a`])
    ORELSE
     (CONJ_TAC THENL [tac THEN NO_TAC; ALL_TAC])
    ORELSE tac));;
```

### Informal statement
For all natural numbers `n`, if `n` is less than or equal to 128, then `psi(n)` is less than or equal to `(133/128) * n` (where `psi(n)` is the Chebyshev's second function).

### Informal sketch
The proof proceeds by:
- Rewrite the inequality `n <= 128` as `n < 129`.
- Expand the definition of `psi(n)` using `EXPAND_CASES_CONV`. Since the statement is restricted to `n <= 128`, `psi(n)` will be evaluated to a specific list of values (defined by `PSI_LIST_300`).
- Rewrite using `LN_1`.
- Reduce the real rational expression by `REAL_RAT_REDUCE_CONV`.
- Repeatedly apply one of three tactics to discharge the goals:
  - Use `REAL_LE_TRANS` to show transitivity of real number inequality.
  - Perform Real arithmetic calculation by `REALCALC_REL_CONV`.
   - Simplify the expression.

### Mathematical insight
The theorem provides an upper bound for the Chebyshev's second function `psi(n)` for `n` less than or equal to 128. It is a sharp linear bound with a constant factor of 133/128. The Chebyshev function is significant in number theory, especially in connection with prime number theorem.

### Dependencies
- `REAL_LE_TRANS`
- `PSI_LIST_300`
- `LN_1`


---

## PSI_UBOUND_128_LOG

### Name of formal statement
PSI_UBOUND_128_LOG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_UBOUND_128_LOG = prove
 (`!n. n <= 128 ==> psi(n) <= (&3 / &2 * ln(&2)) * &n`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP PSI_UBOUND_128) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
  CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV THENC REALCALC_REL_CONV));;
```
### Informal statement
For all natural numbers `n`, if `n` is less than or equal to 128, then `psi(n)` is less than or equal to `(3/2 * ln(2)) * n`.

### Informal sketch
The proof proceeds as follows:
- Start with the goal `!n. n <= 128 ==> psi(n) <= (&3 / &2 * ln(&2)) * &n`.
- Discharge the assumption `n <= 128`.
- Apply `PSI_UBOUND_128` (presumably a theorem stating `!n. psi(n) <= &7 / &10 * &n`). This introduces a new goal to show that `&7 / &10 * &n <= (&3 / &2 * ln(&2)) * &n` under the assumption that `n <= 128`.
- Use a theorem of the form `a <= b ==> x <= a ==> x <= b` to reduce the goal to proving `&7 / &10 * &n <= (&3 / &2 * ln(&2)) * &n`.
- Use `REAL_LE_RMUL`, likely a theorem stating that `a <= b ==> a * x <= b * x` for non-negative `x`, to transform the goal into showing `&7 / &10 <= &3 / &2 * ln(&2)`. This relies on `REAL_POS` to establish `&n >= 0`.
- Rewrite using `REAL_POS` to prove that `&n >= 0` holds.
- Apply `LN_N2_CONV` to replace `ln(&2)` with its numerical approximation.
- Apply `REALCALC_REL_CONV`, which applies real arithmetic reasoning to verify the inequality `&7 / &10 <= &3 / &2 * ln(&2)`.

### Mathematical insight
This theorem provides an upper bound for the prime power counting function `psi(n)` in terms of `n * log(2)`. It's a refinement of a previous bound `PSI_UBOUND_128` utilizing the fact that `psi(n)` grows slower than a linear function in `n`. Expressing the upper bound as a multiple of `ln(2)` is convenient for certain analytic number theory arguments, as `ln(2)` often appears in related estimates.

### Dependencies
- `PSI_UBOUND_128`
- `REAL_ARITH`
- `REAL_LE_RMUL`
- `REAL_POS`
- `LN_N2_CONV`
- `REALCALC_REL_CONV`

### Porting notes (optional)
- The dependency `REALCALC_REL_CONV` suggests the proof relies on a pre-built decision procedure for real arithmetic. In other proof assistants, one might need to invoke similar decision procedures (e.g., `lia` in Coq, `smt` in Isabelle/HOL).
- The conversion `LN_N2_CONV` likely involves replacing `ln(2)` with a numerical constant. Ensure that the target proof assistant has a similar mechanism for handling such constants and performing real arithmetic.


---

## OVERPOWER_LEMMA

### Name of formal statement
OVERPOWER_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let OVERPOWER_LEMMA = prove
 (`!f g d a.
        f(a) <= g(a) /\
        (!x. a <= x ==> ((\x. g(x) - f(x)) diffl (d(x)))(x)) /\
        (!x. a <= x ==> &0 <= d(x))
        ==> !x. a <= x ==> f(x) <= g(x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`\x:real. g(x) - f(x)`; `d:real->real`; `a:real`; `x:real`]
               MVT_ALT) THEN
  UNDISCH_TAC `a <= x` THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
  ASM_CASES_TAC `x:real = a` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MATCH_MP_TAC(REAL_ARITH
   `fa <= ga /\ &0 <= d ==> (gx - fx - (ga - fa) = d) ==> fx <= gx`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
  ASM_SIMP_TAC[REAL_SUB_LE; REAL_LT_IMP_LE]);;
```

### Informal statement
For all real-valued functions `f`, `g`, and `d`, and for all real numbers `a`, if the following conditions hold:
1. `f(a)` is less than or equal to `g(a)`, and
2. For all `x` such that `a` is less than or equal to `x`, the derivative of `g(x) - f(x)` at `x` is `d(x)`, and
3. For all `x` such that `a` is less than or equal to `x`, `0` is less than or equal to `d(x)`,
then, for all `x` such that `a` is less than or equal to `x`, `f(x)` is less than or equal to `g(x)`.

### Informal sketch
The proof proceeds as follows:
- Start by assuming `f(a) <= g(a)`, `g(x) - f(x)` is differentiable with derivative `d(x)` for `a <= x`, and `0 <= d(x)` for `a <= x`. The goal is to show `f(x) <= g(x)` for `a <= x`.
- Apply the Mean Value Theorem (`MVT_ALT`) to the function `g(x) - f(x)` on the interval `[a, x]`.
- Consider the case `x = a`. In this case the result is trivial.
- Consider the case `a < x`. The Mean Value Theorem guarantees the existence of a `z` in the interval `(a, x)` such that `g(x) - f(x) - (g(a) - f(a)) = d(z) * (x - a)`.
- Use the facts that `f(a) <= g(a)` and `0 <= d(z)` to deduce that `f(x) <= g(x)`. This involves using real arithmetic to show that if `f(a) <= g(a)` and `0 <= d(z)`, then `g(x) - f(x) - (g(a) - f(a)) = d(z) * (x - a)` implies `f(x) <= g(x)`.
- Use the fact that `0 <= d(z)` and `0 < x - a` to show that `0 <= d(z) * (x - a)`.

### Mathematical insight
This theorem provides a sufficient condition for showing that one function `f` is always less than or equal to another function `g` on an interval `[a, infinity)`. It states that if `f` starts below `g` at `a`, and the derivative of the difference `g - f` is non-negative on this interval, then `f` will remain below `g` on the entire interval. This is a powerful "overpowering" lemma that is widely applicable.

### Dependencies

**Theorems:**
- `MVT_ALT`
- `REAL_LE_LT`
- `REAL_ARITH`
- `REAL_LE_MUL`
- `REAL_SUB_LE`
- `REAL_LT_IMP_LE`

### Porting notes (optional)
- The Mean Value Theorem (`MVT_ALT`) needs to be available.
- Properties of real numbers/arithmetic, especially those dealing with inequalities, need to be available.
- The `diffl` operator representing differentiation for real-valued functions needs to be available. Depending on the target prover, ensure that diffentiability needs to be proven separately, and the derivative function itself passed to `MVT_ALT`.


---

## DOUBLE_CASES_RULE

### Name of formal statement
DOUBLE_CASES_RULE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DOUBLE_CASES_RULE th =
  let bod = snd(dest_forall(concl th)) in
  let ant,cons = dest_imp bod in
  let m = dest_numeral (rand ant)
  and c = rat_of_term (lhand(lhand(rand cons))) in
  let x = float_of_num(m +/ num 1) in
  let d = (4.0 *. log x +. 3.0) /. (x *. log 2.0) in
  let c' = c // num 2 +/ num 1 +/
           (floor_num(num_of_float(1024.0 *. d)) +/ num 2) // num 1024 in
  let c'' = max_num c c' in
  let tm = mk_forall
   (`n:num`,
    subst [mk_numeral(num 2 */ m),rand ant;
          term_of_rat c'',lhand(lhand(rand cons))] bod) in
  prove(tm,
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (mk_comb(`(<=) (n:num)`,mk_numeral m)) THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP th) THEN
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC LN_POS THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    MP_TAC(SPEC `n:num` PSI_BOUNDS_INDUCT) THEN
    SUBGOAL_THEN `~(n = 0)` (fun th -> REWRITE_TAC[th]) THENL
     [FIRST_ASSUM(UNDISCH_TAC o check is_neg o concl) THEN ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `pn2 <= ((a - &1) * l2) * n - logtm
      ==> u <= v /\ pn - pn2 <= n * l2 + logtm ==> pn <= (a * l2) * n`) THEN
    MP_TAC(SPEC `n DIV 2` th) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[LE_LDIV_EQ; ARITH] THEN
      FIRST_ASSUM(UNDISCH_TAC o check ((not) o is_neg) o concl) THEN
      ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    W(fun (asl,w) ->
       MATCH_MP_TAC REAL_LE_TRANS THEN
       EXISTS_TAC(mk_comb(rator(lhand w),`&n / &2`))) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        MATCH_MP_TAC LN_POS THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        ALL_TAC] THEN
      SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
      MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN ARITH_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [real_div] THEN
    MATCH_MP_TAC(REAL_ARITH
     `logtm <= ((c - a * b) * l2) * n
      ==> (a * l2) * n * b <= (c * l2) * n - logtm`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SUBST1_TAC(REAL_ARITH `&n = &1 + (&n - &1)`) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `~(n <= b) ==> b + 1 <= n`)) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_OF_NUM_LE] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
     `a <= n ==> a - &1 <= n - &1`)) THEN
    ABBREV_TAC `x = &n - &1` THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV) THEN
    SPEC_TAC(`x:real`,`x:real`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    MATCH_MP_TAC OVERPOWER_LEMMA THEN
    W(fun (asl,w) ->
        let th = DIFF_CONV
         (lhand(rator(rand(body(rand(lhand(rand(body(rand w))))))))) in
        MP_TAC th) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [REAL_MUL_LZERO; REAL_ADD_LID; REAL_ADD_RID;
      REAL_MUL_RID; REAL_MUL_LID] THEN
    W(fun (asl,w) ->
        let tm = mk_abs(`x:real`,rand(rator(rand(body(rand(lhand w)))))) in
        DISCH_TAC THEN EXISTS_TAC tm) THEN
    CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[real_sub] THEN
      CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN
      CONV_TAC REALCALC_REL_CONV;
      ALL_TAC] THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_TAC THEN
      DISCH_THEN(fun th -> FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN REWRITE_TAC[REAL_SUB_LE] THEN
    SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `a <= x ==> inv(&1 + x) <= inv(&1 + a) /\
                 inv(&1 + a) <= b ==> inv(&1 + x) <= b`)) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN CONV_TAC REALCALC_REL_CONV);;
```
### Informal statement
For any theorem `th` of the form `!n:num. n <= m ==> rat_of_term (lhand(lhand(rand cons))) <= a`, where `bod` is the body of the forall, `ant,cons = dest_imp bod`, `m = dest_numeral (rand ant)`, `c = rat_of_term (lhand(lhand(rand cons)))`, `x = float_of_num(m +/ num 1)`, `d = (4.0 *. log x +. 3.0) /. (x *. log 2.0)`,
`c' = c // num 2 +/ num 1 +/
           (floor_num(num_of_float(1024.0 *. d)) +/ num 2) // num 1024`,
`c'' = max_num c c'`,
then there exists a proof of the theorem 
`!n:num. subst [mk_numeral(num 2 */ m),rand ant;
          term_of_rat c'',lhand(lhand(rand cons))] bod`, which is a substitution in the body `bod` of `n <= m` with `2 * m` and `rat_of_term (lhand(lhand(rand cons)))` with `c''`.

### Informal sketch
The proof proceeds by mathematical induction and real arithmetic reasoning to extend the range of explicit cases using recurrence.
- The goal is to prove a statement of the form `!n:num. P(n)`, where `P(n)` is `subst [mk_numeral(num 2 */ m),rand ant; term_of_rat c'',lhand(lhand(rand cons))] bod`.
- First, cases are split based on `n <= m`. (`ASM_CASES_TAC (mk_comb(<=,mk_numeral m))`)
  - If `n <= m` holds, the original theorem `th` and real arithmetic reasoning are used to show the result. This part involves real number lemmas for multiplication and logarithmic positivity.
  - Otherwise, we show that the negation of `n = 0` holds by arithmetic.
- Then, induction is applied on `n`, using `PSI_BOUNDS_INDUCT`.
- In the inductive step, one assumes `~(n = 0)`. We show that this assumption is true by arithmetic.
- Several real arithmetic lemmas, including one relating `pn2`, `logtm`, `l2`, `a`, `c` etc.
- Perform substitution of `n DIV 2` (integer division) into `th`.
- The proof involves extensive manipulation of inequalities using theorems like `REAL_LE_TRANS`, `REAL_LE_LMUL`, `REAL_LE_RDIV_EQ`, `REAL_OF_NUM_LT`, `REAL_OF_NUM_MUL`, and `DIVISION`.
- We also use `OVERPOWER_LEMMA`.
- Simplification is done by real field arithmetic and rewriting.
- Some lambda abstraction and discharging of assumptions.
- Application of lemmas like `REAL_SUB_LE`, `REAL_LT_DIV`, `REAL_LE_INV2`.
- Finally, the statement is proved by arithmetic (`REAL_ARITH_TAC`).

### Mathematical insight
This theorem appears to be a step in a more extensive algorithm dealing with inequalities. It extends the range on which a previously derived inequality (embodied in hypothesis `th`) is valid. The construction of `c''` which takes the `max_num` of `c` and a more complex expression `c'` suggests that the theorem allows one to increase a bound on the quantity related to constant `c` given the induction hypothesis in `th` holds. The structure of the proof, using both direct cases and induction, strongly indicates that the initial ranges or base cases available must be extended step by step utilizing real arithmetic to refine the precision.

### Dependencies
- `dest_forall`
- `dest_imp`
- `dest_numeral`
- `rat_of_term`
- `floor_num`
- `num_of_float`
- `mk_forall`
- `mk_numeral`
- `term_of_rat`
- `prove`
- `REPEAT`
- `STRIP_TAC`
- `ASM_CASES_TAC`
- `MP_TAC`
- `MATCH_MP_TAC`
- `REAL_ARITH`
- `REAL_LE_RMUL`
- `REWRITE_TAC`
- `REAL_POS`
- `CONV_TAC`
- `REAL_RAT_REDUCE_CONV`
- `LN_POS`
- `ALL_TAC`
- `SPEC`
- `PSI_BOUNDS_INDUCT`
- `UNDISCH_TAC`
- `check is_neg`
- `ARITH_TAC`
- `LE_LDIV_EQ`
- `ARITH`
- `ASM_SIMP_TAC`
- `check ((not) o is_neg)`
- `W`
- `EXISTS_TAC`
- `CONJ_TAC`
- `REAL_LE_LMUL`
- `REAL_LE_MUL`
- `SIMP_TAC`
- `REAL_LE_RDIV_EQ`
- `REAL_OF_NUM_LT`
- `REAL_OF_NUM_MUL`
- `REAL_OF_NUM_LE`
- `DIVISION`
- `GEN_REWRITE_TAC`
- `LAND_CONV`
- `RAND_CONV`
- `real_div`
- `SUBST1_TAC`
- `ARITH_RULE`
- `GSYM REAL_OF_NUM_LE`
- `ABBREV_TAC`
- `NUM_REDUCE_CONV`
- `POP_ASSUM_LIST`
- `OVERPOWER_LEMMA`
- `DIFF_CONV`
- `TOP_DEPTH_CONV`
- `REAL_MUL_LZERO`
- `REAL_ADD_LID`
- `REAL_ADD_RID`
- `REAL_MUL_RID`
- `REAL_MUL_LID`
- `mk_abs`
- `ONCE_DEPTH_CONV`
- `LN_N2_CONV`
- `REALCALC_REL_CONV`
- `real_sub`
- `GEN_TAC`
- `X_GEN_TAC`
- `REAL_SUB_LE`
- `REAL_LT_DIV`
- `REAL_LE_INV2`
- `REAL_MUL_SYM`
- `GSYM REAL_LE_LDIV_EQ`

### Porting notes (optional)
- The extensive use of real arithmetic (`REAL_ARITH`) might require using SMT solvers or similar automation in other proof assistants.
- HOL Light's rewriting tactics (`REWRITE_TAC`, `GEN_REWRITE_TAC`) can often be translated into similar simplification tactics in other systems, but the specific conversions (e.g., `REAL_RAT_REDUCE_CONV`, `LN_N2_CONV`) might need to be defined separately.
- The tactic `ASM_CASES_TAC` which automatically adds assumption can be translated by generating the assumptions manually.
- The `DIFF_CONV` and `REALCALC_REL_CONV` may need custom implementations, or a call to dedicated real analysis libraries


---

## PSI_UBOUND_1024_LOG

### Name of formal statement
PSI_UBOUND_1024_LOG

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PSI_UBOUND_1024_LOG = funpow 3 DOUBLE_CASES_RULE PSI_UBOUND_128_LOG;;
```

### Informal statement
The theorem `PSI_UBOUND_1024_LOG` is obtained by applying the function `funpow` to the arguments `3`, `DOUBLE_CASES_RULE`, and `PSI_UBOUND_128_LOG`. The function `funpow` applies the rule `DOUBLE_CASES_RULE` three times to the theorem `PSI_UBOUND_128_LOG`.

### Informal sketch
The theorem `PSI_UBOUND_1024_LOG` is derived by iteratively applying `DOUBLE_CASES_RULE` to `PSI_UBOUND_128_LOG` three times. This suggests a proof by repeated application of a transformation rule to an initial theorem.
- Starting with `PSI_UBOUND_128_LOG`, we want to sequentially apply `DOUBLE_CASES_RULE` three times.
 - After each application, we obtain a new theorem with a progressively larger bound. Namely, after the first, second and third application to `PSI_UBOUND_128_LOG` we will derive `PSI_UBOUND_256_LOG`, `PSI_UBOUND_512_LOG` and `PSI_UBOUND_1024_LOG` respectively.
- This hints at a proof by induction which is automated here by `funpow`.

### Mathematical insight
This theorem establishes a bound related to a function named `PSI` for the specific value 1024. The repeated application of `DOUBLE_CASES_RULE` likely refines or expands the initial bound given by `PSI_UBOUND_128_LOG` to larger values in a stepwise manner. This is a common strategy in bounding problems where inequalities are iteratively improved.

### Dependencies
- Theorem: `PSI_UBOUND_128_LOG`
- Rule: `DOUBLE_CASES_RULE`
- Function: `funpow`


---

## PSI_BOUNDS_SUSTAINED_INDUCT

### Name of formal statement
PSI_BOUNDS_SUSTAINED_INDUCT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_BOUNDS_SUSTAINED_INDUCT = prove
 (`&4 * ln(&1 + &2 pow j) + &3 <= (d * ln(&2)) * (&1 + &2 pow j) /\
   &4 / (&1 + &2 pow j) <= d * ln(&2) /\ &0 <= c /\ c / &2 + d + &1 <= c
   ==> !k. j <= k /\
           (!n. n <= 2 EXP k ==> psi(n) <= (c * ln(&2)) * &n)
           ==> !n. n <= 2 EXP (SUC k) ==> psi(n) <= (c * ln(&2)) * &n`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n <= 2 EXP k` THEN ASM_SIMP_TAC[] THEN
  MP_TAC(SPEC `n:num` PSI_BOUNDS_INDUCT) THEN
  SUBGOAL_THEN `~(n = 0)` (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC(ARITH_RULE `!a. ~(a = 0) /\ ~(n <= a) ==> ~(n = 0)`) THEN
    EXISTS_TAC `2 EXP k` THEN ASM_REWRITE_TAC[EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `pn2 <= ((a - &1) * l2) * n - logtm
    ==> u <= v /\ pn - pn2 <= n * l2 + logtm ==> pn <= (a * l2) * n`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n DIV 2`) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[LE_LDIV_EQ; ARITH] THEN
    MATCH_MP_TAC(ARITH_RULE `n <= 2 * k ==> n < 2 * (k + 1)`) THEN
    ASM_REWRITE_TAC[GSYM(CONJUNCT2 EXP)];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  W(fun (asl,w) ->
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC(mk_comb(rator(lhand w),`&n / &2`))) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LN_POS THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [real_div] THEN
  MATCH_MP_TAC(REAL_ARITH
   `logtm <= ((c - a * b) * l2) * n
    ==> (a * l2) * n * b <= (c * l2) * n - logtm`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(d * ln (&2)) * &n` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN SIMP_TAC[LN_POS; REAL_OF_NUM_LE; ARITH] THEN
    REWRITE_TAC[GSYM real_div] THEN
    ASM_REWRITE_TAC[REAL_ARITH `d <= c - &1 - c2 <=> c2 + d + &1 <= c`]] THEN
  SUBST1_TAC(REAL_ARITH `&n = &1 + (&n - &1)`) THEN
  SUBGOAL_THEN `&2 pow j <= &n - &1` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 pow k` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_MONO; REAL_OF_NUM_LE; ARITH]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
      `~(n <= b) ==> b + 1 <= n`)) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_OF_NUM_LE] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_POW] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `x = &n - &1` THEN SPEC_TAC(`x:real`,`x:real`) THEN
  MATCH_MP_TAC OVERPOWER_LEMMA THEN
  W(fun (asl,w) ->
      let th = DIFF_CONV
       (lhand(rator(rand(body(rand(lhand(rand(body(rand w))))))))) in
      MP_TAC th) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [REAL_MUL_LZERO; REAL_ADD_LID; REAL_ADD_RID;
    REAL_MUL_RID; REAL_MUL_LID] THEN
  W(fun (asl,w) ->
      let tm = mk_abs(`x:real`,rand(rator(rand(body(rand(lhand w)))))) in
      DISCH_TAC THEN EXISTS_TAC tm) THEN
  CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN
    DISCH_THEN(fun th -> FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < a ==> a <= x ==> &0 < &1 + x`) THEN
    SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  X_GEN_TAC `z:real` THEN DISCH_TAC THEN REWRITE_TAC[REAL_SUB_LE] THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `a <= x ==> inv(&1 + x) <= inv(&1 + a) /\
               inv(&1 + a) <= b ==> inv(&1 + x) <= b`)) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[REAL_LE_LADD] THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; ARITH; REAL_ARITH
     `&0 < x ==> &0 < &1 + x`];
    ALL_TAC] THEN
  SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  ASM_REWRITE_TAC[GSYM real_div]);;
```

### Informal statement
Assume that for some real numbers `&0`, `&1`, `&2`, `&3`, `&4`, and `d` the following conditions hold: `&4 * ln(&1 + &2 pow j) + &3 <= (d * ln(&2)) * (&1 + &2 pow j)`, `&4 / (&1 + &2 pow j) <= d * ln(&2)`, `&0 <= c`, and `c / &2 + d + &1 <= c`.
Then, for all natural numbers `k`, if `j <= k` and for all natural numbers `n`, if `n <= 2 EXP k` implies `psi(n) <= (c * ln(&2)) * &n`, then for all natural numbers `n`, `n <= 2 EXP (SUC k)` implies `psi(n) <= (c * ln(&2)) * &n`.

### Informal sketch
The proof proceeds by induction on `k`. The goal is to prove that for all `k`, if for all `n <= 2 EXP k`, `psi(n) <= (c * ln(&2)) * &n`, then for all `n <= 2 EXP (SUC k)`, `psi(n) <= (c * ln(&2)) * &n`.

- The base case (`k = 0`) is covered by using `PSI_BOUNDS_INDUCT` and splitting cases on `n <= 2 EXP k`, specifically by considering if `n = 0`.

- In the inductive step, assume the hypothesis holds for `k`.

- We consider `n <= 2 EXP (SUC k)`. We split cases based on whether `n <= 2 EXP k`.

- If `n <= 2 EXP k`, we use the inductive hypothesis to get `psi(n) <= (c * ln(&2)) * &n`.

- If `~(n <= 2 EXP k)`, we want to prove the inductive step by leveraging the arithmetic properties to show that `psi(n)` is bounded. This involves showing that `psi(n) <= (c * ln(&2)) * &n`. The proof proceeds as follows:

  - First consider `pn2 <= ((a - &1) * l2) * n - logtm ==> u <= v /\ pn - pn2 <= n * l2 + logtm ==> pn <= (a * l2) * n`.
    We instantiate the assumption with `n DIV 2`.

  - After several rewriting steps, we utilize inequalities such as `n <= 2 * k ==> n < 2 * (k + 1)` as well as the transitivity of inequalities.

  - Then, the proof substitutes `&n = &1 + (&n - &1)` and proves `&2 pow j <= &n - &1`.

  - The proof uses `OVERPOWER_LEMMA` which can be difficult to port to other proof assistants due to the `DIFF_CONV` tactic which computes derivatives. This lemma establishes an upper bound on a certain function related to the `psi` function.

  - The proof then uses several arithmetic facts about real numbers (`REAL_MUL_LZERO`, `REAL_ADD_LID`, `REAL_ADD_RID`, `REAL_MUL_RID`, `REAL_MUL_LID`).

  - It proceeds by rewriting to make use of the assumptions about `c` and `d`. Several inequalities are used to bound `psi(n)` by `(c * ln(&2)) * &n`, thus implying `psi(n) <= (c * ln(&2)) * &n` as required.

### Mathematical insight
This theorem is an inductive step towards proving an upper bound for the `psi` function (related to prime counting). It states that if the upper bound holds for a certain range of natural numbers quantified by `k`, then it holds for the extended range. This type of result is usually used to provide an ultimate bound on prime numbers and related quantities.

### Dependencies
- `PSI_BOUNDS_INDUCT`
- `EXP_EQ_0`
- `LE_LDIV_EQ`
- `REAL_LE_TRANS`
- `REAL_LE_LMUL`
- `REAL_LE_MUL`
- `LN_POS`
- `REAL_RAT_REDUCE_CONV`
- `REAL_LE_RDIV_EQ`
- `REAL_OF_NUM_LT`
- `REAL_OF_NUM_MUL`
- `REAL_OF_NUM_LE`
- `DIVISION`
- `real_div`
- `REAL_LE_RMUL`
- `REAL_POS`
- `GSYM real_div`
- `REAL_POW_MONO`
- `GSYM REAL_OF_NUM_LE`
- `GSYM REAL_OF_NUM_ADD`
- `GSYM REAL_OF_NUM_POW`
- `OVERPOWER_LEMMA`
- `REAL_MUL_LZERO`
- `REAL_ADD_LID`
- `REAL_ADD_RID`
- `REAL_MUL_RID`
- `REAL_MUL_LID`
- `REAL_SUB_LE`
- `REAL_LT_DIV`
- `REAL_LE_INV2`
- `REAL_LE_LADD`
- `REAL_MUL_SYM`

### Porting notes (optional)
- The `OVERPOWER_LEMMA` and use of the `DIFF_CONV` tactic to calculate derivatives needed to apply it may be difficult to replicate in other proof assistants directly. The lemma itself would need to be ported manually, and the proof might require a different approach to bypass the need for derivative calculation via `DIFF_CONV`.
- The extensive use of `REAL_ARITH` may suggest the need to manually provide some arithmetic lemmas in other proof assistants if the automation is not as strong.


---

## PSI_BOUNDS_SUSTAINED

### Name of formal statement
PSI_BOUNDS_SUSTAINED

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_BOUNDS_SUSTAINED = prove
 (`(!n. n <= 2 EXP k ==> psi(n) <= (c * ln(&2)) * &n)
   ==> &4 * ln(&1 + &2 pow k) + &3
         <= ((c / &2 - &1) * ln(&2)) * (&1 + &2 pow k) /\
       &4 / (&1 + &2 pow k) <= (c / &2 - &1) * ln(&2) /\ &0 <= c
           ==> !n. psi(n) <= (c * ln(&2)) * &n`,
  let lemma = prove
   (`c / &2 + (c / &2 - &1) + &1 <= c`,
    REWRITE_TAC[REAL_ARITH `c2 + (c2 - &1) + &1 = &2 * c2`] THEN
    SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; ARITH_EQ; REAL_LE_REFL]) in
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o C CONJ lemma) THEN
  ABBREV_TAC `d = c / &2 - &1` THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP PSI_BOUNDS_SUSTAINED_INDUCT) THEN
  X_GEN_TAC `m:num` THEN
  SUBGOAL_THEN `?j. m <= 2 EXP j` MP_TAC THENL
   [EXISTS_TAC `m:num` THEN SPEC_TAC(`m:num`,`m:num`) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN INDUCT_TAC THEN REWRITE_TAC[ARITH] THEN
    REWRITE_TAC[EXP] THEN MATCH_MP_TAC(ARITH_RULE
     `~(a = 0) /\ m <= a ==> SUC m <= 2 * a`) THEN
    ASM_REWRITE_TAC[EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN SPEC_TAC(`m:num`,`m:num`) THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP 0` THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; LE_0];
    ALL_TAC] THEN
  ASM_CASES_TAC `k <= j:num` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP (SUC j) <= 2 EXP k`
   (fun th -> ASM_MESON_TAC[th; LE_TRANS]) THEN
  ASM_REWRITE_TAC[LE_EXP; ARITH] THEN
  UNDISCH_TAC `~(k <= j:num)` THEN ARITH_TAC);;
```

### Informal statement
If for all natural numbers `n`, `n` is less than or equal to 2 raised to the power of `k` implies `psi(n)` is less than or equal to `(c * ln(2)) * n`, then the following conditions hold:
1. `4 * ln(1 + 2^k) + 3 <= ((c / 2 - 1) * ln(2)) * (1 + 2^k)`, and
2. `4 / (1 + 2^k) <= (c / 2 - 1) * ln(2)`, and
3. `0 <= c`
imply that for all natural numbers `n`, `psi(n)` is less than or equal to `(c * ln(2)) * n`.

### Informal sketch
The proof proceeds by induction on `n` to show that `psi(n)` is bounded by `(c * ln(2)) * n`.
- First, a lemma is proved that `c / 2 + (c / 2 - 1) + 1 <= c`.
- The antecedent of the main theorem is assumed.
- It is shown that for any natural number `m`, there exists a `j` such that `m <= 2^j`. This is done by induction on `m`.
- Then induction on `n` is peformed.
   - Base case: We want to show that `psi(0) <= (c * ln(2)) * 0`, that is to say, `psi(0) <= 0`
   - Inductive step: Assume `psi(n) <= (c * ln(2)) * n`. We want to show `psi(SUC n) <= (c * ln(2)) * SUC n`
      - The inductive hypothesis is used.
      - We consider the cases where either `k <= j` or `~(k <= j)`.
      - In the first case proof goes by meson.
      - In the second case it is shown `2^(SUC j) <= 2^k` and the arith tactic finishes the proof.

### Mathematical insight
This theorem states that if the inequality `psi(n) <= (c * ln(2)) * n` holds for all `n <= 2^k`, then under some other conditions on `c` and `k`, it holds for all `n`. This can be used to establish an upper bound for the Chebyshev function `psi(n)`.

### Dependencies
- `PSI_BOUNDS_SUSTAINED_INDUCT`
- `REAL_ARITH c2 + (c2 - &1) + &1 = &2 * c2`
- `REAL_DIV_LMUL`
- `REAL_OF_NUM_EQ`
- `ARITH_EQ`
- `REAL_LE_REFL`
- `GSYM CONJ_ASSOC`
- `LEFT_IMP_EXISTS_THM`
- `SWAP_FORALL_THM`
- `LE_TRANS`
- `LE_EXP`
- `EXP_EQ_0`
- `ARITH_EQ`
- `LE_0`
- `EXP`

### Porting notes (optional)
- The proof relies heavily on real arithmetic simplification, so the target proof assistant should have good support for this.
- The use of `ASM_CASES_TAC` and `ASM_MESON_TAC` suggests that automatic case splitting and first-order reasoning are important.


---

## PSI_UBOUND_LOG

### Name of formal statement
PSI_UBOUND_LOG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_UBOUND_LOG = prove
 (`!n. psi(n) <= (&4407 / &2048 * ln (&2)) * &n`,
  MP_TAC PSI_UBOUND_1024_LOG THEN
  SUBST1_TAC(SYM(NUM_REDUCE_CONV `2 EXP 10`)) THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP PSI_BOUNDS_SUSTAINED) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN
  CONJ_TAC THEN CONV_TAC REALCALC_REL_CONV);;
```
### Informal statement
For all natural numbers `n`, the Chebyshev function `psi(n)` is less than or equal to `(4407/2048) * ln(2) * n`.

### Informal sketch
The proof proceeds as follows:
- It starts by applying the theorem `PSI_UBOUND_1024_LOG`, which presumably establishes the bound for n = 2^10 = 1024, i.e., `psi(1024) <= (4407/2048) * ln(2) * 1024`.
- It substitutes `2 EXP 10` (which is 1024) in the inequality.
- It discharges the assumption of the theorem and uses it to prove the whole theorem `PSI_BOUNDS_SUSTAINED`. The theorem `PSI_BOUNDS_SUSTAINED` must state that if the bound holds for some n, then it sustains to all numbers.
- It simplifies using real rational arithmetic reduction.
- It then uses `LN_N2_CONV` to evaluate ln(2).
- Finally, it simplifies using real calculus relation conversions.

### Mathematical insight
This theorem provides an upper bound for the Chebyshev psi function, which is a summation over primes and prime powers up to a given number. The bound is linear in `n`, with a constant factor involving `ln(2)`. This type of bound is useful in analytic number theory for estimating the growth of prime-related functions.

### Dependencies
- `PSI_UBOUND_1024_LOG`
- `PSI_BOUNDS_SUSTAINED`
- `LN_N2_CONV`


---

## PSI_UBOUND_3_2

### Name of formal statement
PSI_UBOUND_3_2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_UBOUND_3_2 = prove
 (`!n. psi(n) <= &3 / &2 * &n`,
  GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&4407 / &2048 * ln (&2)) * &n` THEN
  REWRITE_TAC[PSI_UBOUND_LOG] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
  CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN
  CONV_TAC REALCALC_REL_CONV);;
```

### Informal statement
For all `n`, the Chebyshev function `psi(n)` is less than or equal to `3/2 * n`.

### Informal sketch
The proof establishes the upper bound `psi(n) <= (3/2) * n`.

- First, the proof proceeds by induction and transitivity.
- It uses `PSI_UBOUND_LOG` which provides that `psi(n) <= (4407/2048) * ln(2) * n`.
- The goal is then to show that `(4407/2048) * ln(2) <= 3/2`.
- The proof uses `LN_N2_CONV` to approximate `ln(2)`.
- Finally, `REALCALC_REL_CONV` is used to prove the real inequality.

### Mathematical insight
This theorem provides an upper bound for the Chebyshev function `psi(n)`. The Chebyshev functions play a crucial role in number theory, particularly in the study of the distribution of prime numbers. Establishing bounds for these functions is important for proving various results related to prime numbers.

### Dependencies
- `PSI_UBOUND_LOG`
- `REAL_LE_TRANS`
- `REAL_LE_RMUL`
- `REAL_POS`
- `LN_N2_CONV`


---

## PSI_LBOUND_3_5

### Name of formal statement
PSI_LBOUND_3_5

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_LBOUND_3_5 = prove
 (`!n. 4 <= n ==> &3 / &5 * &n <= psi(n)`,
  let lemma = prove
   (`a <= b /\ b <= l /\ rest ==> a <= l /\ b <= l /\ rest`,
    MESON_TAC[REAL_LE_TRANS])
  and tac = time (CONV_TAC(RAND_CONV LN_N2_CONV THENC REALCALC_REL_CONV)) in
  GEN_TAC THEN ASM_CASES_TAC `n < 300` THENL
   [POP_ASSUM MP_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC(PSI_LIST_300) THEN
    REWRITE_TAC[LN_1; ARITH] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REPEAT
     ((MATCH_MP_TAC lemma THEN
       CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN
       GEN_REWRITE_TAC I [TAUT `T /\ a <=> a`])
      ORELSE
       (CONJ_TAC THENL [tac THEN NO_TAC; ALL_TAC])
      ORELSE tac);
    ALL_TAC] THEN
  DISCH_THEN(K ALL_TAC) THEN
  MP_TAC(CONJUNCT1 (SPEC `n:num` PSI_BOUNDS_INDUCT)) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= x ==> a <= x`) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(n < 300) ==> ~(n = 0)`] THEN
  MATCH_MP_TAC(REAL_ARITH `c <= n * (b - a) ==> a * n <= n * b - c`) THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 / &11 * &n` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
    REWRITE_TAC[real_sub] THEN CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN
    CONV_TAC REALCALC_REL_CONV] THEN
  ABBREV_TAC `x = &n - &1` THEN
  SUBGOAL_THEN `&n = &1 + x` SUBST1_TAC THENL
   [EXPAND_TAC "x" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&299 <= x` MP_TAC THENL
   [EXPAND_TAC "x" THEN REWRITE_TAC[REAL_LE_SUB_LADD] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; ARITH] THEN
    UNDISCH_TAC `~(n < 300)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SPEC_TAC(`x:real`,`x:real`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  MATCH_MP_TAC OVERPOWER_LEMMA THEN
  W(fun (asl,w) ->
      let th = DIFF_CONV
       (lhand(rator(rand(body(rand(lhand(rand(body(rand w))))))))) in
      MP_TAC th) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [REAL_MUL_LZERO; REAL_ADD_LID; REAL_ADD_RID;
    REAL_MUL_RID; REAL_MUL_LID] THEN
  W(fun (asl,w) ->
      let tm = mk_abs(`x:real`,rand(rator(rand(body(rand(lhand w)))))) in
      DISCH_TAC THEN EXISTS_TAC tm) THEN
  CONJ_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN
    CONV_TAC REALCALC_REL_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN
    DISCH_THEN(fun th -> FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_SUB_LE] THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(&1 + &299)` THEN CONJ_TAC THENL
   [ALL_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;
```

### Informal statement
For all natural numbers `n`, if `4 <= n`, then `3/5 * n <= psi(n)`.

### Informal sketch
The proof proceeds as follows:
- Establish the base cases for `4 <= n < 300` by explicit calculation, using the precomputed list `PSI_LIST_300`. The calculation involves repeatedly refining inequalities using `REAL_RAT_REDUCE_CONV` and related real arithmetic tactics.
- Apply mathematical induction using `PSI_BOUNDS_INDUCT` to extend the result to all `n` with `4 <= n`.
- Assume `n >= 300`. We introduce `x = n - 1`, so `n = 1 + x`.
- Show that `x >= 299` under the assumption `~(n < 300)`.
- Instantiate `OVERPOWER_LEMMA` with `x` (i.e., `n - 1`) and simplify using real arithmetic.
- Prove that the inequality holds for `n>=300` based on the properties shown above, using simplifications, arithmetic reasoning, rewriting, and discharging assumptions.
- Finally, combine the base cases and the inductive step to conclude the theorem.

### Mathematical insight
This theorem establishes a lower bound for the Dedekind psi function, `psi(n)`, stating that for `n >= 4`, `psi(n)` is greater than or equal to `(3/5)*n`. This is a step towards characterizing the behavior of Dedekind's psi function.

### Dependencies
- `PSI_LIST_300`: A precomputed list of values of the Dedekind psi function for `n` up to 300.
- `PSI_BOUNDS_INDUCT`: An induction theorem for the Dedekind psi function.
- `LN_N2_CONV`: A conversion related to logarithms.
- `REAL_LE_TRANS`: Transitivity of real inequality.
- `REAL_POS`: Positivity of real numbers.
- `REAL_LE_RMUL`: Multiplication property for inequalities with positive real numbers.
- `real_sub`: Subtraction of real numbers.
- `REAL_OF_NUM_ADD`, `REAL_OF_NUM_LE`: Conversions from natural to real numbers.
- `REAL_SUB_LE`, `REAL_LE_RDIV_EQ`, `REAL_OF_NUM_LT`, `ARITH`: Theorems about real arithmetic and arithmetic.
- `REAL_LE_INV2`: Inequality for inverses.
- `OVERPOWER_LEMMA`: A lemma related to overpowering expressions.


---

## theta

### Name of formal statement
- theta

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let theta = new_definition
  `theta(n) = sum(1,n) (\p. if prime p then ln(&p) else &0)`;;
```
### Informal statement
- The function `theta` is defined such that for any natural number `n`, `theta(n)` is the sum from 1 to `n` of a function that takes a natural number `p` as input. If `p` is a prime number, the function returns the natural logarithm of `p`; otherwise, it returns 0.

### Informal sketch
- Define the `theta` function using `new_definition`.
- The definition involves the summation of `ln(&p)` for all primes `p` from 1 to `n`.
- The summation is achieved via `sum(1,n) (\p. if prime p then ln(&p) else &0)`.

### Mathematical insight
- The `theta` function, often denoted as $\vartheta(x)$ or $\psi(x)$ in number theory (variants exist), is a summation over prime numbers less than or equal to `n`. Specifically, this definition corresponds to the first Chebyshev function, summing the logarithms of primes less than or equal to `n`. This function is important in the study of the distribution of prime numbers.

### Dependencies
- Definitions:
  - `prime`
  - `ln`
  - `sum`


---

## THETA_LIST

### Name of formal statement
THETA_LIST

### Type of the formal statement
Definition

### Formal Content
```ocaml
let THETA_LIST =
  let THETA_0 = prove
   (`theta(0) = ln(&1)`,
    REWRITE_TAC[theta; sum; LN_1])
  and THETA_SUC = prove
   (`theta(SUC n) = theta(n) + (if prime(SUC n) then ln(&(SUC n)) else &0)`,
    REWRITE_TAC[theta; sum; ADD1] THEN REWRITE_TAC[ADD_AC])
  and n_tm = `n:num`
  and SIMPER_CONV =
    NUM_REDUCE_CONV THENC
    ONCE_DEPTH_CONV PRIME_CONV THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV
     [COND_CLAUSES; REAL_ADD_LID; REAL_ADD_RID] THENC
    SIMP_CONV [GSYM LN_MUL; REAL_OF_NUM_MUL; REAL_OF_NUM_LT; ARITH] in
  let rec THETA_LIST n =
    if n = 0 then [THETA_0] else
    let ths = THETA_LIST (n - 1) in
    let th1 = INST [mk_small_numeral(n-1),n_tm] THETA_SUC in
    let th2 = GEN_REWRITE_RULE (RAND_CONV o LAND_CONV) [hd ths] th1 in
    CONV_RULE SIMPER_CONV th2::ths in
  THETA_LIST;;
```

### Informal statement
The definition `THETA_LIST` constructs a list of theorems of the form `theta(i) = ...` for all `i` from 0 up to `n`. The function `THETA_LIST` takes a natural number `n` as input and returns a list of theorems.

The theorem at index 0, `THETA_0`, states that `theta(0) = ln(1)`.

The theorem `THETA_SUC` states that `theta(SUC n) = theta(n) + (if prime(SUC n) then ln(SUC n) else 0)`.

The function `THETA_LIST` is defined recursively.
- If `n = 0`, it returns a list containing only the theorem `THETA_0`.
- Otherwise, it computes `THETA_LIST(n-1)` to get a list of theorems `ths` for values up to `n-1`.
- Then it instantiates `THETA_SUC` with `n-1` to get a theorem `th1` that expresses the relation between `theta(n)` and `theta(n-1)`.
- It rewrites `th1` using the first theorem in the list `ths` (specifically, rewrites the right-hand side of  `theta(n-1)` in `th1`), obtaining the theorem `th2` expressing `theta(n)` in terms of `n`.
- Finally, it adds `th2` to the front of the list `ths` and returns the extended list.

### Informal sketch
The definition constructs a list of theorems proving the value of `theta(n)` for all n from 0 to some N. The definition proceeds as follows:

- Prove `theta(0) = ln(1)` using rewriting with `theta`, `sum`, and `LN_1`. Store this theorem as `THETA_0`.
- Prove `theta(SUC n) = theta(n) + (if prime(SUC n) then ln(SUC n) else 0)` using rewriting with `theta`, `sum`, `ADD1`, and `ADD_AC`. Store this theorem as `THETA_SUC`.
- Define a conversion `SIMPER_CONV` to simplify expressions involving `theta`. It uses numerical reduction, prime number simplification, rewriting with conditional expressions (COND_CLAUSES), identities for addition (REAL_ADD_LID, REAL_ADD_RID), and simplification with rules about logarithms, real numbers, and arithmetic.
- Define the recursive function `THETA_LIST n` as follows:
    - If `n = 0`, the function returns a list containing only `THETA_0`.
    - If `n > 0`, then the function recursively calculates `THETA_LIST (n-1)` resulting in the list `ths`. Then, it instantiates `THETA_SUC` with `n-1` to get an instance `th1` of the recurrence relation at `n-1`. It then rewrites the right-hand side of the instantiated `THETA_SUC` theorem using the theorem `hd ths` to produce the theorem `th2`. The `SIMPER_CONV` conversion is then applied to simplify `th2`, and finally, `th2` is prepended to the list `ths` and returned.

### Mathematical insight
The `THETA_LIST` function provides an efficient way to generate proofs for the values of the `theta` function for a range of inputs. It uses a combination of theorem proving, rewriting, and recursion to compute and store the theorems, allowing for easy access to the value of `theta(n)` for any `n` up to the given limit. This is especially useful when needing to evaluate the `theta` function multiple times, as the proofs are precomputed and readily available in the list. The `theta` function in this context likely refers to a summation related to prime numbers, which is hinted at by the conditional `if prime(SUC n) then ln(SUC n) else 0`.

### Dependencies
Rewriting Rules:
- `theta`
- `sum`
- `LN_1`
- `ADD1`
- `ADD_AC`
- `COND_CLAUSES`
- `REAL_ADD_LID`
- `REAL_ADD_RID`
- `LN_MUL`
- `REAL_OF_NUM_MUL`
- `REAL_OF_NUM_LT`
- `ARITH`
Tactics:
- `REWRITE_TAC`
- `NUM_REDUCE_CONV`
- `ONCE_DEPTH_CONV`
- `PRIME_CONV`
- `GEN_REWRITE_CONV`
- `TOP_DEPTH_CONV`
- `SIMP_CONV`
- `GSYM`
- `INST`
- `RAND_CONV`
- `LAND_CONV`
- `CONV_RULE`

### Porting notes (optional)
- The `prove` calls create theorems using tactics. These will need to be translated into equivalent proof constructions in other systems.
- The use of conversions such as `SIMPER_CONV` represent simplification strategies. Porting this definition would likely require reimplementing similar simplification procedures/tactics in the target proof assistant, paying special attention to automation of arithmetic and simplification of real number expressions.
- The reification between `num` and `real` types (`REAL_OF_NUM_MUL` and `REAL_OF_NUM_LT`) might need special attention as the handling of these coercions often varies across systems.


---

## PRIMEPOW_ODD_EVEN

### Name of formal statement
PRIMEPOW_ODD_EVEN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PRIMEPOW_ODD_EVEN = prove
 (`!p q j k.
     ~(prime(p) /\ prime(q) /\ 1 <= j /\ (p EXP (2 * j) = q EXP (2 * k + 1)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `q divides p` ASSUME_TAC THENL
   [MATCH_MP_TAC PRIME_DIVEXP THEN EXISTS_TAC `2 * j` THEN
    UNDISCH_TAC `p EXP (2 * j) = q EXP (2 * k + 1)` THEN
    REWRITE_TAC[EXP_ADD; EXP_1] THEN
    ASM_MESON_TAC[divides; MULT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `q = p:num` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[prime]; ALL_TAC] THEN
  UNDISCH_TAC `p EXP (2 * j) = p EXP (2 * k + 1)` THEN
  REWRITE_TAC[GSYM LE_ANTISYM] THEN REWRITE_TAC[LE_EXP] THEN
  COND_CASES_TAC THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(p = 1)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
  REWRITE_TAC[LE_ANTISYM] THEN
  DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH_EVEN]);;
```

### Informal statement
For all prime numbers `p` and `q`, and for all natural numbers `j` and `k`, it is not the case that `p` is prime, `q` is prime, `j` is greater than or equal to 1, and `p` raised to the power of `2 * j` is equal to `q` raised to the power of `2 * k + 1`.

### Informal sketch
The proof proceeds by contradiction, assuming that there exist prime numbers `p` and `q` and natural numbers `j` and `k` such that `p` is prime, `q` is prime, `j >= 1`, and `p^(2*j) = q^(2*k+1)`.

- First, it is shown that `q` divides `p`. This is done by applying `PRIME_DIVEXP` which states that if a prime raised to some power divides a number then the prime divides the number.
- Next, it is shown that `q = p`. This follows from the fact that `p` and `q` are prime and `q` divides `p`.
- We then have `p^(2*j) = p^(2*k+1)`.
- Because `p` is prime, `p` cannot be 0 or 1. Taking cases, if `p=0` or `p=1`, we get contradiction by `PRIME_0` and `PRIME_1`.
- Since `p` is not 0 or 1, we can compare the exponents: `2 * j = 2 * k + 1`.
- Finally, it is shown that `2 * j` is even and `2 * k + 1` is odd, which implies that they cannot be equal leading to a contradiction.

### Mathematical insight
This theorem states that an even power of a prime number cannot be equal to an odd power of another prime number. This stems from the uniqueness of prime factorization.

### Dependencies
* `prime`
* `divides`
* `EXP_ADD`
* `EXP_1`
* `MULT_SYM`
* `PRIME_DIVEXP`
* `PRIME_0`
* `PRIME_1`
* `LE_ANTISYM`
* `LE_EXP`
* `EVEN_ADD`
* `EVEN_MULT`
* `ARITH_EVEN`


---

## PSI_SPLIT

### Name of formal statement
PSI_SPLIT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_SPLIT = prove
 (`psi(n) = theta(n) +
            sum(1,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k))
                          then ln(&(aprimedivisor d)) else &0) +
            sum(1,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k + 1))
                          then ln(&(aprimedivisor d)) else &0)`,
  REWRITE_TAC[psi; theta; GSYM SUM_ADD] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
  REWRITE_TAC[mangoldt; primepow] THEN
  ASM_CASES_TAC `?p k. 1 <= k /\ prime p /\ (r = p EXP k)` THEN
  ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    SUBGOAL_THEN `~(?p k. 1 <= k /\ prime p /\ (r = p EXP (2 * k))) /\
                  ~(?p k. 1 <= k /\ prime p /\ (r = p EXP (2 * k + 1))) /\
                  ~(prime r)`
     (fun th -> REWRITE_TAC[th; REAL_ADD_LID]) THEN
    ASM_MESON_TAC[ARITH_RULE `1 <= k ==> 1 <= 2 * k /\ 1 <= 2 * k + 1`;
                  EXP_1; LE_REFL]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `m:num` MP_TAC)) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(SPECL [`m:num`; `2`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
  MAP_EVERY ABBREV_TAC [`k = m DIV 2`; `d = m MOD 2`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  ASM_SIMP_TAC[APRIMEDIVISOR_PRIMEPOW] THEN
  FIRST_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
   `d < 2 ==> (d = 0) \/ (d = 1)`)) THEN
  ASM_REWRITE_TAC[PRIME_EXP; ADD_EQ_0; MULT_EQ_0; ARITH_EQ] THENL
   [UNDISCH_TAC `1 <= k * 2 + 0` THEN REWRITE_TAC[ADD_CLAUSES] THEN
    ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(k * 2 = 1)` (fun th -> REWRITE_TAC[th]) THENL
     [DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
      REWRITE_TAC[EVEN_MULT; ARITH_EVEN]; ALL_TAC] THEN
    REPEAT(COND_CASES_TAC THEN
           ASM_REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID]) THEN
    ASM_MESON_TAC[PRIMEPOW_ODD_EVEN; MULT_SYM;
                  ARITH_RULE `~(k = 0) ==> 1 <= k`];
    ALL_TAC] THEN
  ASM_CASES_TAC `k = 0` THENL
   [MATCH_MP_TAC(REAL_ARITH
     `(a = a') /\ (b = &0) /\ (c = &0) ==> (a = a' + b + c)`) THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[ARITH; EXP_1]; ALL_TAC] THEN
    CONJ_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[PRIMEPOW_ODD_EVEN; MULT_SYM]; ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `q:num` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` MP_TAC) THEN STRIP_TAC THEN
    SUBGOAL_THEN `q divides p` ASSUME_TAC THENL
     [MATCH_MP_TAC PRIME_DIVEXP THEN EXISTS_TAC `k * 2 + 1` THEN
      UNDISCH_TAC `p EXP (k * 2 + 1) = q EXP (2 * j + 1)` THEN
      REWRITE_TAC[EXP_ADD; EXP_1] THEN
      ASM_MESON_TAC[divides; MULT_SYM];
      ALL_TAC] THEN
    SUBGOAL_THEN `q = p:num` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[prime]; ALL_TAC] THEN
    UNDISCH_TAC `p EXP (k * 2 + 1) = p EXP (2 * j + 1)` THEN
    REWRITE_TAC[GSYM LE_ANTISYM] THEN REWRITE_TAC[LE_EXP] THEN
    ASM_CASES_TAC `p = 0` THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `p = 1` THENL [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
    REWRITE_TAC[LE_ANTISYM] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= j ==> ~(1 = 2 * j + 1)`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `(k * 2 + 1 = 1) <=> (k = 0)`; ARITH_EQ] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID]) THEN
  ASM_MESON_TAC[PRIMEPOW_ODD_EVEN; MULT_SYM; ARITH_RULE
   `~(k = 0) ==> 1 <= k`]);;
```

### Informal statement
For any natural number `n`, `psi(n)` is equal to `theta(n)` plus the sum from 1 to `n` over all `d` of the expression: if there exist `p` and `k` such that `1 <= k`, `p` is prime, and `d` is equal to `p` raised to the power of `2 * k`, then the natural logarithm of the real number representation of `aprimedivisor d`; otherwise, the real number `0`; plus the sum from 1 to `n` over all `d` of the expression: if there exist `p` and `k` such that `1 <= k`, `p` is prime, and `d` is equal to `p` raised to the power of `2 * k + 1`, then the natural logarithm of the real number representation of `aprimedivisor d`; otherwise, the real number `0`.

### Informal sketch
The proof proceeds as follows:
- Start with the definition of `psi(n)` and `theta(n)`. Apply `SUM_ADD` to split the sum.
- Use `SUM_EQ` to transform a sum over prime powers, making use of the definition of `mangoldt` and `primepow`.
- Perform a case split on the existence of `p` and `k` such that `1 <= k` and `prime p` and `r` equals to `p EXP k`.
- In the negative case (when no such `p` and `k` exist), show that `~(prime r)` and use that to simplify to `REAL_ADD_LID` i.e. `x + 0 = x`.
- In the positive case (when such `p` and `k` exist), apply the choose operator to introduce witnesses `p` and `m`.
- Instantiate the equation `r = p EXP k` with `k = m DIV 2` and `d = m MOD 2`.
- Simplify using `APRIMEDIVISOR_PRIMEPOW`.
- Perform case split on `d < 2` and utilize `PRIME_EXP` and  `ADD_EQ_0`, `MULT_EQ_0`, `ARITH_EQ` to simplify the sum.
- Deal with the resulting cases by exploiting arithmetic reasoning about even and odd numbers, and prime powers.
- For dealing with the cases `k = 0`, infer `q divides p`, `q = p`, perform substitution and utilize `PRIME_0`, `PRIME_1` to simplify the expression.
- Use arithmetic reasoning and simplification (`EVEN_MULT`,`ARITH_EVEN`, `REAL_ADD_LID`,`REAL_ADD_RID`) to complete proof.

### Mathematical insight
This theorem decomposes the Chebyshev function `psi(n)` into the sum of the von Mangoldt function `theta(n)` and two sums. These sums account for prime powers of the form `p^(2k)` and `p^(2k+1)` respectively where `p` is prime.

### Dependencies
- Definitions: `psi`, `theta`, `mangoldt`, `primepow`, `aprimedivisor`
- Theorems: `GSYM SUM_ADD`, `SUM_EQ`, `DIVISION`, `ARITH_EQ`, `APRIMEDIVISOR_PRIMEPOW`, `PRIME_EXP`, `ADD_EQ_0`, `MULT_EQ_0`, `ARITH_EQ`, `EVEN_MULT`, `ARITH_EVEN`, `REAL_ADD_LID`, `REAL_ADD_RID`, `PRIMEPOW_ODD_EVEN`, `MULT_SYM`, `EXP_1`, `LE_REFL`, `PRIME_DIVEXP`, `LE_ANTISYM`, `LE_EXP`, `PRIME_0`, `PRIME_1`, `EXP_ADD`, `divides`, `prime`
- Rules: `ARITH_RULE`


---

## SUM_SURJECT

### Name of formal statement
SUM_SURJECT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_SURJECT = prove
 (`!f i m n p q.
        (!r. m <= r /\ r < m + n ==> &0 <= f(i r)) /\
        (!s. p <= s /\ s < p + q /\ ~(f(s) = &0)
             ==> ?r. m <= r /\ r < m + n /\ (i r = s))
        ==> sum(p,q) f <= sum(m,n) (\r. f(i r))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(m,n) (\r. if p:num <= i(r) /\ i(r) < p + q
                            then f(i(r)) else &0)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUM_LE THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN
    ASM_MESON_TAC[REAL_LE_REFL; ADD_AC]] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  SPEC_TAC(`q:num`,`q:num`) THEN INDUCT_TAC THENL
   [STRIP_TAC THEN REWRITE_TAC[sum] THEN
    REWRITE_TAC[ARITH_RULE `~(p <= q /\ q < p + 0)`] THEN
    REWRITE_TAC[SUM_0; REAL_LE_REFL];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> POP_ASSUM MP_TAC THEN STRIP_ASSUME_TAC th) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[ARITH_RULE `s < p + q ==> s < p + SUC q`];
    ALL_TAC] THEN
  REWRITE_TAC[sum] THEN
  SUBGOAL_THEN
   `sum(m,n) (\r. if p <= i r /\ i r < p + SUC q then f (i r) else &0) =
    sum(m,n) (\r. if p <= i r /\ i r < p + q then f (i r) else &0) +
    sum(m,n) (\r. if i r = p + q then f(i r) else &0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_ADD] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `(i:num->num) r = p + q` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[LE_ADD; LT_REFL; ARITH_RULE `p + q < p + SUC q`] THEN
      REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[ARITH_RULE
       `r < p + SUC q <=> (r = p + q) \/ r < p + q`] THEN
    REWRITE_TAC[REAL_ADD_RID];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `f <= s'' ==> s <= s' ==> s + f <= s' + s''`) THEN
  UNDISCH_TAC
   `!s. p <= s /\ s < p + SUC q /\ ~(f s = &0)
           ==> (?r:num. m <= r /\ r < m + n /\ (i r = s))` THEN
  DISCH_THEN(MP_TAC o SPEC `p + q:num`) THEN
  ASM_CASES_TAC `f(p + q:num) = &0` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(m,n) (\r. &0)` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUM_0; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC SUM_LE THEN X_GEN_TAC `r:num` THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_LE_REFL] THEN ASM_MESON_TAC[ADD_SYM];
    ALL_TAC] THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `n = (s - m) + 1 + ((m + n) - (s + 1))` SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`m <= s:num`; `s < m + n:num`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_SPLIT] THEN
  ASM_SIMP_TAC[SUM_1; ARITH_RULE `m <= s ==> (m + (s - m) = s:num)`] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= y ==> a <= x + a + y`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(m,s - m) (\r. &0)` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUM_0; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC SUM_LE THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC
      [`m <= r:num`; `r < s - m + m:num`; `s < m + n:num`; `m <= s:num`] THEN
    ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(s + 1,(m + n) - (s + 1)) (\r. &0)` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUM_0; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC SUM_LE THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC
      [`r < (m + n) - (s + 1) + s + 1:num`;
       `s + 1 <= r`; `s < m + n:num`; `m <= s:num`] THEN
    ARITH_TAC]);;
```

### Informal statement
For all functions `f` from numbers to reals, functions `i` from numbers to numbers, and numbers `m`, `n`, `p`, and `q`, if the following conditions hold:
1. For all numbers `r`, if `m <= r` and `r < m + n`, then `0 <= f(i r)`.
2. For all numbers `s`, if `p <= s` and `s < p + q` and `f(s)` is not equal to `0`, then there exists a number `r` such that `m <= r` and `r < m + n` and `i r = s`.

Then, the sum of `f(s)` from `p` to `q` is less than or equal to the sum of `f(i r)` from `m` to `n`.

### Informal sketch
The proof proceeds by induction on `q`.

- Base case: `q = 0`.  The goal simplifies to showing `sum(p, 0) f <= sum(m, n) (\r. f(i r))`. Since `sum(p, 0) f = 0`, we need to show `0 <= sum(m, n) (\r. f(i r))`. This follows from the assumption `!r. m <= r /\ r < m + n ==> &0 <= f(i r)`.

- Inductive step: Assume the theorem holds for `q`. We want to prove it for `SUC q`.  That is, we assume `sum(p, q) f <= sum(m, n) (\r. f(i r))` and want to show `sum(p, SUC q) f <= sum(m, n) (\r. f(i r))`.
  - Rewrite `sum(p, SUC q)` as `sum(p, q) + f(p + q)`.  The goal becomes `sum(p, q) f + f(p + q) <= sum(m, n) (\r. f(i r))`.
  - The proof proceeds by considering two cases: `f(p + q) = &0` and `f(p + q) != &0`.
  - Case 1: `f(p + q) = &0`.  Then the goal becomes `sum(p, q) f <= sum(m, n) (\r. f(i r))`, which is the induction hypothesis.
  - Case 2: `f(p + q) != &0`. Then there is an `s` such that `m <= s /\ s < m + n /\ (i s = p + q)`. Split the sum `sum(m, n)` into three parts:
    `sum(m, s - m) + f(i s) + sum(s + 1, (m + n) - (s + 1))`. Now we need to show `sum(p, q) f + f(p + q) <= sum(m, s - m) + f(i s) + sum(s + 1,(m + n) - (s + 1))`. Because `i s = p + q`, this reduces to `sum(p, q) f <= sum(m, s - m) + sum(s + 1, (m + n) - (s + 1))`.
   - To complete this, we introduce sums of zeros to dominate the right hand side.

### Mathematical insight
The theorem states that if the range of the function `i` covers the range of the summation in the left-hand side, and `f` has nonnegative values at the images `i r`, the inequality `sum(p,q) f <= sum(m,n) (\r. f(i r))` holds. This is a generalization of the usual relation `sum(p,q) f <= sum(m,n) f` if `p=m`, and `q=n`. The interesting part of this result allows for a surjection between the two ranges with the condition that `0 <= f(i(r))`.
This theorem is significant because it relates two sums under the condition that one summation index can be mapped onto the other with the function `i`. The condition that values are non-negative is crucial for the inequality to hold.

### Dependencies
- `REAL_LE_TRANS`
- `SUM_LE`
- `SUM_0`
- `REAL_LE_REFL`
- `ADD_AC`
- `SUM_ADD`
- `SUM_EQ`
- `LE_ADD`
- `LT_REFL`
- `REAL_ADD_LID`
- `REAL_ADD_RID`
- `REAL_ARITH`
- `ADD_SYM`
- `SUM_SPLIT`
- `SUM_1`

### Porting notes (optional)
The most challenging part to port will be the heavy usage of `ARITH_TAC` and `REAL_ARITH`, both of which rely on automation to discharge arithmetic goals. The user will need to have some similar tactic written or adapt the code to suit the proof goals for the new proof assistant.
The `SUBST1_TAC` tactic and others need to be carefully considered as the order that goals are broken down will depend on the proof assistant.
The use of `GSYM` will need to be emulated by swapping statements and will require extra work.

---

## PSI_RESIDUES_COMPARE_2

### Name of formal statement
PSI_RESIDUES_COMPARE_2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_RESIDUES_COMPARE_2 = prove
 (`sum(2,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k + 1))
                 then ln(&(aprimedivisor d)) else &0)
   <= sum(2,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k))
                    then ln(&(aprimedivisor d)) else &0)`,
  MP_TAC(SPECL
   [`\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k + 1))
                    then ln(&(aprimedivisor d)) else &0`;
    `\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP k)
                  then d * (aprimedivisor d) else d`;
    `2`; `n:num`; `2`; `n:num`] SUM_SURJECT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `r:num` THEN STRIP_TAC THEN
      ASM_CASES_TAC `?p k. 1 <= k /\ prime p /\ (r = p EXP k)` THEN
      ASM_REWRITE_TAC[] THENL
       [ALL_TAC;
        COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
        ASM_MESON_TAC[ARITH_RULE `1 <= k ==> 1 <= 2 * k + 1`]] THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` MP_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      ASM_SIMP_TAC[APRIMEDIVISOR_PRIMEPOW] THEN
      COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
      SUBGOAL_THEN `p EXP k * p = p EXP (k + 1)` SUBST1_TAC THENL
       [REWRITE_TAC[EXP_ADD; EXP_1; MULT_AC]; ALL_TAC] THEN
      ASM_SIMP_TAC[APRIMEDIVISOR_PRIMEPOW; ARITH_RULE `1 <= k + 1`] THEN
      ASM_MESON_TAC[LN_POS; REAL_OF_NUM_LE; PRIME_GE_2; REAL_LE_REFL;
                    ARITH_RULE `2 <= n ==> 1 <= n`];
      ALL_TAC] THEN
    X_GEN_TAC `s:num` THEN
    ASM_CASES_TAC `?p k. 1 <= k /\ prime p /\ (s = p EXP (2 * k + 1))` THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    EXISTS_TAC `p EXP (2 * k)` THEN
    COND_CASES_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[ARITH_RULE `1 <= k ==> 1 <= 2 * k`]] THEN
    ASM_SIMP_TAC[APRIMEDIVISOR_PRIMEPOW; EXP_ADD; EXP_1;
                 ARITH_RULE `1 <= k ==> 1 <= 2 * k`] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 <= n <=> ~(n = 0) /\ ~(n = 1)`;
                  EXP_EQ_0; EXP_EQ_1] THEN
      ASM_MESON_TAC[PRIME_1; PRIME_0;
                    ARITH_RULE `1 <= k ==> ~(2 * k = 0)`];
      ALL_TAC] THEN
    MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `p EXP (2 * k + 1)` THEN
    ASM_REWRITE_TAC[LE_EXP] THEN
    COND_CASES_TAC THEN UNDISCH_TAC `1 <= k` THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC SUM_LE THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  ASM_CASES_TAC `?p k. 1 <= k /\ prime p /\ (r = p EXP k)` THEN
  ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_MESON_TAC[ARITH_RULE `1 <= k ==> 1 <= 2 * k /\ 1 <= 2 * k + 1`]] THEN
  FIRST_X_ASSUM(CHOOSE_THEN (K ALL_TAC)) THEN
  ASM_CASES_TAC `?p k. 1 <= k /\ prime p /\ (r = p EXP (2 * k))` THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    ASM_SIMP_TAC[APRIMEDIVISOR_PRIMEPOW;
                 ARITH_RULE `1 <= k ==> 1 <= 2 * k`] THEN
    SUBGOAL_THEN `p EXP (2 * k) * p = p EXP (2 * k + 1)` SUBST1_TAC THENL
     [REWRITE_TAC[EXP_ADD; EXP_1; MULT_AC]; ALL_TAC] THEN
    COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    ASM_SIMP_TAC[APRIMEDIVISOR_PRIMEPOW; REAL_LE_REFL;
                 ARITH_RULE `1 <= k ==> 1 <= 2 * k + 1`];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
  FIRST_ASSUM(UNDISCH_TAC o check is_neg o concl) THEN
  MATCH_MP_TAC(TAUT `(b ==> a) ==> ~a ==> b ==> c`) THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`p:num`; `k:num`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `r:num` APRIMEDIVISOR) THEN
  ASM_SIMP_TAC[ARITH_RULE `2 <= n ==> ~(n = 1)`] THEN
  ABBREV_TAC `q = aprimedivisor r` THEN STRIP_TAC THEN
  SUBGOAL_THEN `q divides p` ASSUME_TAC THENL
   [MATCH_MP_TAC PRIME_DIVEXP THEN EXISTS_TAC `2 * k + 1` THEN
    ASM_MESON_TAC[divides; MULT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `q = p:num` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[prime]; ALL_TAC] THEN
  UNDISCH_TAC `r * p = p EXP (2 * k + 1)` THEN
  REWRITE_TAC[EXP_ADD; EXP_1; EQ_MULT_RCANCEL] THEN
  ASM_MESON_TAC[PRIME_0]);;
```

### Informal statement
For all natural numbers `n` greater than or equal to 2, the sum from 2 to `n` of the function that maps `d` to `ln(aprimedivisor d)` if there exist `p` and `k` such that `1 <= k`, `p` is prime, and `d = p^(2*k+1)`, and to 0 otherwise, is less than or equal to the sum from 2 to `n` of the function that maps `d` to `ln(aprimedivisor d)` if there exist `p` and `k` such that `1 <= k`, `p` is prime, and `d = p^(2*k)`, and to 0 otherwise.

### Informal sketch
The proof proceeds by induction or a related technique to compare sums.
- The proof starts by using `SUM_SURJECT` to relate the sums based on how the function maps input `d` to expressions involving `aprimedivisor d` under certain conditions related to primes.
- By rewriting and simplifying the goal using `REWRITE_TAC` and `ANTS_TAC` the proof continues by splitting the goal into two subgoals using `CONJ_TAC`.
- The proof aims to show that for any `r` the term in the first sum is smaller than or equal to the term in the second sum using ASM tactics and `REAL_LE_REFL`. The proof relies on some arithmetical reasoning, and `APRIMEDIVISOR_PRIMEPOW` to rewrite expressions involving prime powers and their `aprimedivisor`.

More specifically:
- Subgoal 1: Show that for any `r`, if `r = p^k` where `p` is prime and `1 <= k`, then `0 <= ln(&(aprimedivisor (p^(2 * k))))`. Note that `aprimedivisor (p^(2 * k))` is equal to `p`. After substitution and arithmetic reasoning, we want to show `0 <= ln(&p)`, which follows from `LN_POS` given `2 <= p`.
- Subgoal 2: Show that for any `s`, if `s = p^(2*k+1)` where `p` is prime and `1 <= k`, then there exists some `d` such that `d = p^(2k)` and `ln(&(aprimedivisor s)) <= ln(&(aprimedivisor d))`.
    - It proceeds by choosing `d = p^(2k)`, using congruence and applying appropriate rewrites.
- After finishing off the two subgoals the main goal is finished by MATCHING and using `SUM_LE` theorem to finaly conclude.

### Mathematical insight
The theorem establishes a relationship between two sums involving the logarithmic function applied to the `aprimedivisor` of integers `d` that are specifically of the form `p^(2*k+1)` and `p^(2*k)` for some prime `p` and integer `k >= 1`. The theorem provides a bound between these sums by relating how prime powers are distributed.

### Dependencies
- `SUM_SURJECT`
- `APRIMEDIVISOR_PRIMEPOW`
- `LN_POS`
- `REAL_OF_NUM_LE`
- `PRIME_GE_2`
- `REAL_LE_REFL`
- `PRIME_1`
- `PRIME_0`
- `LE_EXP`
- `SUM_LE`
- `APRIMEDIVISOR`
- `divides`
- `PRIME_DIVEXP`
- `prime`

### Porting notes (optional)
- The tactic `ASM_CASES_TAC` might need special attention as it involves case splitting based on whether a certain predicate holds, which may require different approaches depending on the target proof assistant.


---

## PSI_RESIDUES_COMPARE

### Name of formal statement
PSI_RESIDUES_COMPARE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_RESIDUES_COMPARE = prove
 (`!n. sum(1,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k + 1))
                     then ln(&(aprimedivisor d)) else &0)
       <= sum(1,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k))
                        then ln(&(aprimedivisor d)) else &0)`,
  GEN_TAC THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[sum; REAL_LE_REFL] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
   `~(n = 0) ==> (n = 1 + (n - 1))`)) THEN
  REWRITE_TAC[GSYM SUM_SPLIT; SUM_1] THEN
  MATCH_MP_TAC(REAL_ARITH
   `b <= d /\ (a = &0) /\ (c = &0) ==> a + b <= c + d`) THEN
  REWRITE_TAC[PSI_RESIDUES_COMPARE_2; ARITH] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_MESON_TAC[EXP_EQ_1; PRIME_1; ARITH_RULE
    `1 <= k ==> ~(2 * k = 0) /\ ~(2 * k + 1 = 0)`]);;
```

### Informal statement
For all natural numbers `n`, the sum from 1 to `n` of the function that maps `d` to `ln(aprimedivisor d)` if there exist natural number `k` and prime `p` such that `1 <= k` and `d = p^(2*k+1)`, and to `0` otherwise, is less than or equal to the sum from 1 to `n` of the function that maps `d` to `ln(aprimedivisor d)` if there exist natural number `k` and prime `p` such that `1 <= k` and `d = p^(2*k)`, and to `0` otherwise.

### Informal sketch
The proof proceeds by induction on `n`.
- Base case: `n = 0`. In this case both sums are equal to 0, and the inequality holds trivially.
- Inductive step: Assume that the inequality holds for `n`. We want to prove that it holds for `n+1`.
    - Split the sums at `n+1` using `SUM_SPLIT` and `SUM_1`.
    - Apply the inductive hypothesis and the fact that `a <= d /\ (a = &0) /\ (c = &0) ==> a + b <= c + d` to reduce the goal to proving `if ?p k. 1 <= k /\ prime p /\ (n+1 = p EXP (2 * k + 1)) then ln(&(aprimedivisor (n+1))) else &0 <= if ?p k. 1 <= k /\ prime p /\ (n+1 = p EXP (2 * k)) then ln(&(aprimedivisor (n+1))) else &0`. This involves reasoning about under which conditions the terms in the summed expressions become non-zero.
    - Perform case splits on existentially quantified terms of `(?p k. 1 <= k /\ prime p /\ (n+1 = p EXP (2 * k + 1)))` and `(?p k. 1 <= k /\ prime p /\ (n+1 = p EXP (2 * k)))`.
    - Simplify using assumptions and properties like `EXP_EQ_1` and `PRIME_1` and arithmetic facts to complete the proof.

### Mathematical insight
This theorem compares two sums involving logarithmic functions of divisors of `n`. The divisors are specific powers of primes. The left side sums `ln(aprimedivisor d)` for `d = p^(2k+1)` while the right side sums `ln(aprimedivisor d)` for `d = p^(2k)`, where p is prime and k >= 1. The theorem states that the sum of the latter expression is at least as big as the former which relates to the distribution of prime powers and prime divisors.

### Dependencies
- `sum`
- `REAL_LE_REFL`
- `GSYM SUM_SPLIT`
- `SUM_1`
- `EXP_EQ_1`
- `PRIME_1`
- `PSI_RESIDUES_COMPARE_2`
- `prime`
- `aprimedivisor`


---

## PSI_SQRT

### Name of formal statement
PSI_SQRT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_SQRT = prove
 (`!n. psi(ISQRT(n)) =
        sum(1,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k))
                      then ln(&(aprimedivisor d)) else &0)`,
  REWRITE_TAC[psi] THEN INDUCT_TAC THEN
  REWRITE_TAC[ISQRT_0; sum; ISQRT_SUC] THEN
  ASM_CASES_TAC `?m. SUC n = m EXP 2` THENL
   [ALL_TAC;
    SUBGOAL_THEN `~(?p k. 1 <= k /\ prime p /\ (1 + n = p EXP (2 * k)))`
    ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[EXP_MULT] THEN
      ASM_MESON_TAC[ARITH_RULE `1 + n = SUC n`];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_ADD_RID]] THEN
  ASM_REWRITE_TAC[REAL_EQ_ADD_LCANCEL; sum] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `m:num`) THEN
  SUBGOAL_THEN `1 + ISQRT n = m` SUBST1_TAC THENL
   [SUBGOAL_THEN `(1 + ISQRT n) EXP 2 = SUC n` MP_TAC THENL
     [ALL_TAC;
      ASM_REWRITE_TAC[num_CONV `2`; GSYM LE_ANTISYM] THEN
      REWRITE_TAC[EXP_MONO_LE; EXP_MONO_LT; NOT_SUC]] THEN
    MP_TAC(SPEC `n:num` ISQRT_SUC) THEN
    COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    REWRITE_TAC[ARITH_RULE `1 + n = SUC n`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(SPEC `SUC n` ISQRT_WORKS) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[num_CONV `2`; GSYM LE_ANTISYM] THEN
    REWRITE_TAC[EXP_MONO_LE; EXP_MONO_LT; NOT_SUC] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 + n = SUC n`] THEN
  REWRITE_TAC[mangoldt; primepow] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[EXP_MULT] THEN
  REWRITE_TAC[EXP_MONO_EQ; ARITH_EQ] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[aprimedivisor] THEN
  REPEAT AP_TERM_TAC THEN ABS_TAC THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)`) THEN
  DISCH_TAC THEN REWRITE_TAC[EXP; EXP_1] THEN
  ASM_SIMP_TAC[PRIME_DIVEXP_EQ; ARITH_EQ]);;
```

### Informal statement
For all natural numbers `n`, the value of the `psi` function applied to the integer square root of `n` is equal to the sum, from `1` to `n`, of a function that maps each `d` to the natural logarithm of the absolute value of the `aprimedivisor` of `d` if there exist natural numbers `p` and `k` such that `k` is greater than or equal to `1`, `p` is prime, and `d` is equal to `p` raised to the power `2 * k`; otherwise, it is equal to `0`.

### Informal sketch
The proof proceeds by induction on `n`.

- Base case: `n = 0`. The theorem is proven by rewriting with `ISQRT_0` and `sum`.
- Inductive step: Assume the theorem holds for `n`. We want to prove it for `SUC n`.
  - We consider two cases: either there exists `m` such that `SUC n = m EXP 2` or not.
    - If `~(?m. SUC n = m EXP 2)`: Use assumption to prove `~(?p k. 1 <= k /\ prime p /\ (1 + n = p EXP (2 * k)))`. Then, rewrite using `REAL_ADD_RID` to simplify the sum.
    - If `SUC n = m EXP 2` for some m: Choose such an `m`.
      - Prove `1 + ISQRT n = m` by proving `(1 + ISQRT n) EXP 2 = SUC n`. Use `ISQRT_SUC` to derive this equality. Also use `ISQRT_WORKS` to establish equality for proved square roots.
      - Apply the induction hypothesis and rewrite the sum using properties of prime powers and `aprimedivisor`. Simplify using `PRIME_DIVEXP_EQ` and arithmetic.

### Mathematical insight
This theorem relates the `psi` function evaluated at the integer square root to a sum involving prime powers. The `psi` function is a summation over primes related to the Mangoldt function, and the theorem provides a way to compute it based on a sum over the integers up to `n`.
The connection leverages number-theoretic properties related to prime divisors and perfect squares.

### Dependencies
- `psi`
- `ISQRT`
- `ISQRT_0`
- `ISQRT_SUC`
- `ISQRT_WORKS`
- `prime`
- `EXP`
- `aprimedivisor`
- `ln`
- `sum`
- `mangoldt`
- `primepow`
- `PRIME_DIVEXP_EQ`

### Porting notes (optional)
The theorem depends on the definitions of `psi`, `ISQRT`, `aprimedivisor`, the definition of primality `prime`, the exponentiation operator `EXP` and their established formal properties. Porting this theorem requires ensuring that the counterpart definitions capture the same mathematical intent with the same formal properties in the target proof assistant. The arithmetic reasoning performed by `ARITH_TAC` might need to be replaced with alternative tactics depending on the arithmetic automation available in the target system. The use of `ASM_MESON_TAC` suggests reliance on classical reasoning which might require appropriate setup in other proof assistants such as Coq or Lean depending on the context. The tactic `COND_CASES_TAC` which destructs an if-then-else statements could be replaced by `destruct if_statement.` in Coq.


---

## PSI_THETA

### Name of formal statement
PSI_THETA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_THETA = prove
 (`!n. theta(n) + psi(ISQRT n) <= psi(n) /\
       psi(n) <= theta(n) + &2 * psi(ISQRT n)`,
  GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [PSI_SPLIT] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [PSI_SPLIT] THEN
  MP_TAC(SPEC `n:num` PSI_RESIDUES_COMPARE) THEN
  REWRITE_TAC[GSYM PSI_SQRT] THEN
  SIMP_TAC[REAL_MUL_2; GSYM REAL_ADD_ASSOC; REAL_LE_LADD; REAL_LE_ADDR] THEN
  DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC SUM_POS_GEN THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[APRIMEDIVISOR_PRIMEPOW;
    ARITH_RULE `1 <= k ==> 1 <= 2 * k + 1`] THEN
  MATCH_MP_TAC LN_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
  ASM_MESON_TAC[PRIME_0; ARITH_RULE `~(p = 0) ==> 1 <= p`]);;
```

### Informal statement
For all natural numbers `n`, `theta(n) + psi(ISQRT n)` is less than or equal to `psi(n)`, and `psi(n)` is less than or equal to `theta(n) + 2 * psi(ISQRT n)`.

### Informal sketch
The theorem compares `psi(n)` with `theta(n)` and `psi(ISQRT n)`. The proof proceeds as follows:

- Split both instances of `psi` using `PSI_SPLIT` to express `psi(n)` and `psi(ISQRT n)` as sums over primes and prime powers.
- Apply `PSI_RESIDUES_COMPARE`. This likely introduces a specific comparison between the sums related to `psi`.
- Use `PSI_SQRT` to rewrite the expression.
- Use simplification with real arithmetic rules (`REAL_MUL_2`, `REAL_ADD_ASSOC`, `REAL_LE_LADD`, `REAL_LE_ADDR`) to rearrange and simplify the inequality.
- Introduce an assumption.
- Use `SUM_POS_GEN` and instantiate a variable `r:num`. This step likely deals with sums of positive terms.
- Perform conditional case splitting with `COND_CASES_TAC` and use reflexivity of the real less than or equal relation (`REAL_LE_REFL`).
- Perform substitutions based on assumptions and theorems related to prime divisors (`APRIMEDIVISOR_PRIMEPOW`).
- Use `LN_POS` and `REAL_OF_NUM_LE` along with `ASM_MESON_TAC` encompassing `PRIME_0` and an arithmetic rule to discharge the goal automatically.

### Mathematical insight
The theorem provides bounds for the prime power counting function `psi(n)` in terms of `theta(n)` (which sums the logarithms of primes up to `n`) and `psi(ISQRT n)`. This is related to estimates in prime number theory. The theorem and the proof method suggest a strategy of relating the sum over all prime powers to a sum over primes and a smaller error term involving the square root.

### Dependencies
- `PSI_SPLIT`
- `PSI_RESIDUES_COMPARE`
- `PSI_SQRT`
- `REAL_MUL_2`
- `REAL_ADD_ASSOC`
- `REAL_LE_LADD`
- `REAL_LE_ADDR`
- `SUM_POS_GEN`
- `REAL_LE_REFL`
- `APRIMEDIVISOR_PRIMEPOW`
- `LN_POS`
- `REAL_OF_NUM_LE`
- `PRIME_0`

### Porting notes (optional)
- The main challenge in porting this theorem is likely to be reproducing the tactic-based proof strategy, especially the simplification steps involving real arithmetic rules and the use of automatic tactics like `ASM_MESON_TAC`.
- If the target proof assistant has strong automation for real arithmetic and number theory, the proof may be simplified. Otherwise, more explicit rewriting steps may be required to achieve the same result.
- The definitions of `psi` and `theta`, and related theorems like `PSI_SPLIT`, `PSI_RESIDUES_COMPARE`, and `PSI_SQRT` must be available or ported first.


---

## THETA_LE_PSI

### Name of formal statement
THETA_LE_PSI

### Type of the formal statement
theorem

### Formal Content
```ocaml
let THETA_LE_PSI = prove
 (`!n. theta(n) <= psi(n)`,
  GEN_TAC THEN REWRITE_TAC[theta; psi] THEN MATCH_MP_TAC SUM_LE THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[MANGOLDT_POS] THEN
  ASM_SIMP_TAC[mangoldt; PRIME_PRIMEPOW] THEN
  SUBGOAL_THEN `aprimedivisor p = p`
   (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
  ASM_MESON_TAC[APRIMEDIVISOR_PRIMEPOW; EXP_1; LE_REFL]);;
```
### Informal statement
For all natural numbers `n`, `theta(n)` is less than or equal to `psi(n)`.

### Informal sketch
The proof proceeds by:
- Initial steps involve rewriting the `theta` and `psi` functions using their definitions and applying `SUM_LE`.
- Then generalizing over a prime number `p` and stripping the goal.
- Performing case analysis on whether `p` is a prime number.
- If `p` is prime, rewriting using `MANGOLDT_POS`, and simplifying using definitions of `mangoldt` and `PRIME_PRIMEPOW`.
- Showing that `aprimedivisor p = p` implies `REAL_LE_REFL`. This implication is handled by rewriting with the equation `aprimedivisor p = p` which simplifies the goal to reflexivity of `<=` and then applying the theorem `REAL_LE_REFL`.
- Finally, discharging the assumption `aprimedivisor p = p` by proving it using `APRIMEDIVISOR_PRIMEPOW`, `EXP_1` and `LE_REFL` with `ASM_MESON_TAC`.

### Mathematical insight
The theorem shows a basic inequality relation between two key arithmetic functions, `theta(x)` and `psi(x)`. These are Chebyshev functions, and this theorem demonstrates that for any `n`, `theta(n)` is always less than or equal to `psi(n)`. This relationship is important in analytic number theory.

### Dependencies
- Definitions: `theta`, `psi`, `mangoldt`
- Theorems: `SUM_LE`, `MANGOLDT_POS`, `PRIME_PRIMEPOW`, `APRIMEDIVISOR_PRIMEPOW`, `EXP_1`, `LE_REFL`, `REAL_LE_REFL`


---

## PSI_UBOUND_30

### Name of formal statement
PSI_UBOUND_30

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_UBOUND_30 = prove
 (`!n. n <= 30 ==> psi(n) <= &65 / &64 * &n`,
  let lemma = prove
   (`a <= b /\ l <= a /\ rest ==> l <= a /\ l <= b /\ rest`,
    MESON_TAC[REAL_LE_TRANS])
  and tac = time (CONV_TAC(LAND_CONV LN_N2_CONV THENC REALCALC_REL_CONV)) in
  REWRITE_TAC[ARITH_RULE `n <= 30 <=> n < 31`] THEN
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC(PSI_LIST_300) THEN
  REWRITE_TAC[LN_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REPEAT
   ((MATCH_MP_TAC lemma THEN
     CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN
     GEN_REWRITE_TAC I [TAUT `T /\ a <=> a`])
    ORELSE
     (CONJ_TAC THENL [tac THEN NO_TAC; ALL_TAC])
    ORELSE tac));;
```

### Informal statement
For all natural numbers `n`, if `n` is less than or equal to 30, then `psi(n)` is less than or equal to `65/64 * n`.

### Informal sketch
The theorem is proved by:
- First, rewriting `n <= 30` into `n < 31`.
- Then, expanding the cases.
- Rewriting with `PSI_LIST_300`.
- Rewriting with `LN_1`.
- Reducing the real rational expression.
- Repeatedly applying the following tactics:
    - Using a lemma based on `REAL_LE_TRANS` to transform inequalities. This involves reducing real rational expressions and tautologies.
    - Or, conjuncting and then applying `tac`. The tactic `tac` involves converting using `LAND_CONV LN_N2_CONV` followed by `REALCALC_REL_CONV`.
    - Or, applying the tactic `tac`.

### Mathematical insight
The theorem provides a tighter upper bound for the Dedekind psi function, denoted as `psi(n)`, for natural numbers up to 30. This is useful to minimize the case analysis when dealing with estimates about `psi`.

### Dependencies
- `REAL_LE_TRANS`
- `PSI_LIST_300`
- `LN_1`

### Porting notes (optional)
- The tactic `MESON_TAC` is used for automated reasoning, which may need replacement depending on the target prover's automation capabilities.
- The tactic `REALCALC_REL_CONV` may require a corresponding real arithmetic decision procedure or simplifier in the target prover. The same applies for `ARITH_RULE`.
- Tactics like `CONV_TAC`, `REWRITE_TAC`, and `MATCH_MP_TAC` are standard tactics present in most proof assistants, so their direct translation should not pose a challenge. However, the specific conversions like `LAND_CONV LN_N2_CONV` might require adaptation based on the available library of conversions in the target prover.


---

## THETA_UBOUND_3_2

### Name of formal statement
THETA_UBOUND_3_2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let THETA_UBOUND_3_2 = prove
 (`!n. theta(n) <= &3 / &2 * &n`,
  MESON_TAC[REAL_LE_TRANS; PSI_UBOUND_3_2; THETA_LE_PSI]);;
```

### Informal statement
For all natural numbers `n`, the function `theta(n)` is less than or equal to `3/2 * n`.

### Informal sketch
The proof uses `MESON_TAC` with the following theorems:
- `REAL_LE_TRANS`: A general transitivity rule for real number inequality (<=).
- `PSI_UBOUND_3_2`: A previously established upper bound for `psi(n)`, specifically `psi(n) <= 3/2 * n`.
- `THETA_LE_PSI`: A theorem stating that `theta(n) <= psi(n)` for all `n`.

The main reasoning steps are:
- From `THETA_LE_PSI`, we know `theta(n) <= psi(n)`.
- From `PSI_UBOUND_3_2`, we know `psi(n) <= 3/2 * n`.
- Using `REAL_LE_TRANS`, we combine these two inequalities to conclude `theta(n) <= 3/2 * n`.

### Mathematical insight
This theorem provides an explicit upper bound for the Chebyshev theta function, `theta(n)`. The theta function is important in number theory, particularly in the study of the distribution of prime numbers. Bounding it by a linear function is a crucial step in proving results like the Prime Number Theorem.

### Dependencies
- Theorems: `REAL_LE_TRANS`, `PSI_UBOUND_3_2`, `THETA_LE_PSI`


---

## THETA_LBOUND_1_2

### Name of formal statement
THETA_LBOUND_1_2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let THETA_LBOUND_1_2 = prove
 (`!n. 5 <= n ==> &1 / &2 * &n <= theta(n)`,
  let lemma = prove
   (`a <= b /\ b <= l /\ rest ==> a <= l /\ b <= l /\ rest`,
    MESON_TAC[REAL_LE_TRANS])
  and tac = time (CONV_TAC(RAND_CONV LN_N2_CONV THENC REALCALC_REL_CONV)) in
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n >= 900` THENL
   [MP_TAC(CONJUNCT2(SPEC `n:num` PSI_THETA)) THEN
    MP_TAC(SPEC `n:num` PSI_LBOUND_3_5) THEN
    ASM_SIMP_TAC[ARITH_RULE `n >= 900 ==> 4 <= n`] THEN
    MATCH_MP_TAC(REAL_ARITH
     `d <= (a - b) * n ==> a * n <= ps ==> ps <= th + d ==> b * n <= th`) THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&3 / &2 * &(ISQRT n)` THEN
    REWRITE_TAC[PSI_UBOUND_3_2] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SUBGOAL_THEN `&(ISQRT n) pow 2 <= (&n * &1 / &30) pow 2` MP_TAC THENL
     [ALL_TAC;
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[REAL_NOT_LE] THEN
      DISCH_TAC THEN MATCH_MP_TAC REAL_POW_LT2 THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&n` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; ISQRT_WORKS];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2; REAL_ARITH
     `(a * b) * (a * b) = a * a * b * b`] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    SIMP_TAC[REAL_MUL_ASSOC; GSYM REAL_LE_LDIV_EQ;
             REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `n >= 900` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `n < 413` THENL
   [UNDISCH_TAC `5 <= n` THEN UNDISCH_TAC `n < 413` THEN
    SPEC_TAC(`n:num`,`n:num`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC(THETA_LIST 412) THEN
    REWRITE_TAC[LN_1; ARITH] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REPEAT
     ((MATCH_MP_TAC lemma THEN
       CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN
       GEN_REWRITE_TAC I [TAUT `T /\ a <=> a`])
      ORELSE
       (CONJ_TAC THENL [tac THEN NO_TAC; ALL_TAC])
      ORELSE tac);
    ALL_TAC] THEN
  MP_TAC(CONJUNCT2(SPEC `n:num` PSI_THETA)) THEN
  MP_TAC(SPEC `n:num` PSI_LBOUND_3_5) THEN
  ASM_SIMP_TAC[ARITH_RULE `5 <= n ==> 4 <= n`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `d <= (a - b) * n ==> a * n <= ps ==> ps <= th + d ==> b * n <= th`) THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&65 / &64 * &(ISQRT n)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PSI_UBOUND_30 THEN
    SUBGOAL_THEN `(ISQRT n) EXP (SUC 1) <= 30 EXP (SUC 1)` MP_TAC THENL
     [ALL_TAC; REWRITE_TAC[EXP_MONO_LE; NOT_SUC]] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
    REWRITE_TAC[ARITH; ISQRT_WORKS] THEN
    UNDISCH_TAC `~(n >= 900)` THEN ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SUBGOAL_THEN `&(ISQRT n) pow 2 <= (&n * &16 / &325) pow 2` MP_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[REAL_NOT_LE] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_POW_LT2 THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&n` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; ISQRT_WORKS];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2; REAL_ARITH
   `(a * b) * (a * b) = a * a * b * b`] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SIMP_TAC[GSYM REAL_LE_LDIV_EQ;
           REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&413` THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
  UNDISCH_TAC `~(n < 413)` THEN ARITH_TAC);;
```

### Informal statement
For all natural numbers `n`, if `5 <= n`, then `1/2 * n <= theta(n)`.

### Informal sketch
The proof proceeds by induction-like case splitting, considering three main cases for the natural number `n`: `n >= 900`, `n < 413`, and the remaining case which is handled using simplification and arithmetic reasoning.

- Case 1: `n >= 900`. Uses `PSI_THETA` and `PSI_LBOUND_3_5` to establish the inequality. It involves real arithmetic and simplification to show that `1/2 * n <= theta(n)`. It utilizes inequalities relating `psi(n)` to `theta(n)` and lower bounds on `psi(n)`. The proof constructs an intermediate value `&3 / &2 * &(ISQRT n)` and shows bounds to relate this constant to `psi(n)` and `theta(n)`. Then it shows `&(ISQRT n) pow 2 <= (&n * &1 / &30) pow 2`.
- Case 2: `n < 413`. This case uses `THETA_LIST 412` providing a list of pre-computed theta values, to directly check the inequality `1/2 * n <= theta(n)` for all `n` in the range `5 <= n < 413`. `lemma` and `tac` are utilized to further assist in proving the inequality.
- Case 3: The default case resulting from the failure of the `ASM_CASES_TAC` tactic, which handles the remaining values, `n < 900` and `n >= 413`, using similar reasoning as in the first case, utilizing `PSI_THETA` and `PSI_LBOUND_3_5` to establish the inequality. Additionally, this case constructs the intermediate value `&65 / &64 * &(ISQRT n)` and aims to show bounds to relate it to `psi(n)` and `theta(n)`. Then it proves `&(ISQRT n) pow 2 <= (&n * &16 / &325) pow 2`.

### Mathematical insight
The theorem establishes a lower bound on the `theta(n)` function, stating that it is at least half of `n` for all `n >= 5`. The proof leverages pre-computed bounds for a finite interval and analytical bounds based on related functions such as `psi(n)` for sufficiently large `n`. The intermediate value constructions are motivated by finding simple functions that can bound `psi` and `theta` with some slack.

### Dependencies
- `PSI_THETA`
- `PSI_LBOUND_3_5`
- `PSI_UBOUND_3_2`
- `THETA_LIST`
- `ISQRT_WORKS`
- `PSI_UBOUND_30`
- `EXP_MONO_LE`
- `LE_TRANS`
### Porting notes (optional)
- The proof relies heavily on real arithmetic reasoning which may require specific automation or tactics in other systems.
- The case splitting based on specific numerical values may suggest a need for computational reflection or similar techniques to automate the verification of inequalities over finite ranges.
- The functions `theta(n)` and `psi(n)` must be defined beforehand along with their basic properties.


---

## FLOOR_POS

### Name of formal statement
FLOOR_POS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FLOOR_POS = prove
 (`!x. &0 <= x ==> &0 <= floor x`,
  GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `x < &1` THENL
   [ASM_MESON_TAC[FLOOR_EQ_0; REAL_LE_REFL]; ALL_TAC] THEN
  MP_TAC(last(CONJUNCTS(SPEC `x:real` FLOOR))) THEN
  UNDISCH_TAC `~(x < &1)` THEN REAL_ARITH_TAC);;
```

### Informal statement
For all real numbers `x`, if `x` is greater than or equal to 0, then the floor of `x` is greater than or equal to 0.

### Informal sketch
The proof proceeds by the following steps:
- Assume `&0 <= x`.
- Perform case split on whether `x < &1`.
  - Case 1: `x < &1`. Use `FLOOR_EQ_0` (which states `!x. x < &1 ==> floor x = &0`) and `REAL_LE_REFL` (which states `!x. x <= x`) to show `&0 <= floor x`. Specifically, since `floor x = &0` and `&0 <= &0`, we have `&0 <= floor x`.
  - Case 2: `~(x < &1)`.
    - Instantiate the definition of `FLOOR` (which likely has the form `!x. floor x <= x /\ (!n. n <= x ==> n <= floor x)`) with `x:real`.
    - Use the second conjunct of this instantiation: Forall n. `n <= x ==> n <= floor x`.
    - Discharge the assumption `~(x < &1)` to obtain `&1 <= x`.
    - Use real arithmetic to deduce `&0 <= floor x`.

### Mathematical insight
This theorem states that the floor function preserves non-negativity. If a real number is non-negative, its floor will also be non-negative. This is a fundamental property of the floor function and is essential for many arguments about integers and real numbers in formal mathematics.

### Dependencies
- `FLOOR`
- `FLOOR_EQ_0`
- `REAL_LE_REFL`

### Porting notes (optional)
- The proof relies on a case split, properties of the floor function (`FLOOR_EQ_0` and the definition `FLOOR`), and real arithmetic. Ensure that the target proof assistant has equivalent theorems and decision procedures.
- The specific tactic `ASM_MESON_TAC` suggests that the proof in HOL Light relies on automatic theorem proving with equality and first-order logic with assumptions. This part of the proof might require more manual guidance in other proof assistants that do not have equally powerful automation.
- The tactic `REAL_ARITH_TAC` uses a real number decision procedure, ensure an equivalent is present in the target system.


---

## FLOOR_NUM_EXISTS

### Name of formal statement
FLOOR_NUM_EXISTS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FLOOR_NUM_EXISTS = prove
 (`!x. &0 <= x ==> ?k. floor x = &k`,
  REPEAT STRIP_TAC THEN MP_TAC(CONJUNCT1(SPEC `x:real` FLOOR)) THEN
  REWRITE_TAC[integer] THEN
  ASM_MESON_TAC[FLOOR_POS; REAL_ARITH `&0 <= x ==> (abs x = x)`]);;
```
### Informal statement
For all real numbers `x`, if `0 <= x`, then there exists an integer `k` such that `floor x = k`.

### Informal sketch
The proof proceeds as follows:
- Strip the quantifiers and assumption to obtain `x` and the assumption `0 <= x`.
- Apply the theorem `FLOOR` (definition of floor as greatest integer less than or equal to `x`) after specializing it with `x`. This results in `floor x <= x /\ x < floor x + 1 /\ integer(floor x)`.
- Rewrite the theorem using the lemma `integer` to show that `floor x` is indeed an integer.
- Use `ASM_MESON_TAC` along with `FLOOR_POS` (which states that `&0 <= x ==> &0 <= floor x`) and a real arithmetic fact `&0 <= x ==> (abs x = x)` to complete the proof.

### Mathematical insight
This theorem establishes the existence of an integer value for the floor of any non-negative real number. This is a fundamental property of the floor function, ensuring that it maps non-negative reals to integers, which is crucial for various applications in number theory and real analysis.

### Dependencies
- `FLOOR`
- `integer`
- `FLOOR_POS`
- `REAL_ARITH`


---

## FLOOR_DIV_INTERVAL

### Name of formal statement
`FLOOR_DIV_INTERVAL`

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FLOOR_DIV_INTERVAL = prove
 (`!n d k. ~(d = 0)
           ==> ((floor(&n / &d) = &k) =
                  if k = 0 then &n < &d
                  else &n / &(k + 1) < &d /\ &d <= &n / &k)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[FLOOR_EQ_0] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_OF_NUM_LT;
                 ARITH_RULE `0 < d <=> ~(d = 0)`] THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_POS; REAL_MUL_LID; REAL_OF_NUM_LT];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM FLOOR_UNIQUE; INTEGER_CLOSED] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_OF_NUM_LT;
                 ARITH_RULE `0 < d <=> ~(d = 0)`; ARITH_RULE `0 < k + 1`] THEN
  REWRITE_TAC[REAL_MUL_AC; CONJ_ACI; REAL_OF_NUM_ADD]);;
```

### Informal statement
For all real numbers `n` and `d`, and for all integers `k`, if `d` is not equal to zero, then `floor(n / d) = k` if and only if:
if `k = 0` then `n < d`, else `n / (k + 1) < d` and `d <= n / k`.

### Informal sketch
The proof proceeds by cases on whether `k = 0`.
- Case `k = 0`:
  - Use the theorem `FLOOR_EQ_0` to rewrite `floor(n / d) = 0` to `n / d < 1`.
  - Simplify using properties of real numbers and arithmetic, notably `REAL_LE_RDIV_EQ`, `REAL_LT_LDIV_EQ`, `REAL_OF_NUM_LT`, `0 < d <=> ~(d = 0)`, as well as `REAL_MUL_LZERO`, `REAL_POS`, `REAL_MUL_LID`, `REAL_OF_NUM_LT` to arrive at `n < d`.
- Case `k != 0`:
  - Rewrite using `GSYM FLOOR_UNIQUE; INTEGER_CLOSED` from `floor(n / d) = k` to `k <= n / d /\ n / d < k + 1`.
  - Simplify the inequalities using `REAL_LE_RDIV_EQ`, `REAL_LT_LDIV_EQ`, `REAL_OF_NUM_LT`, `0 < d <=> ~(d = 0)`, and `0 < k + 1`.
  - Rearrange terms using commutativity and associativity of multiplication (`REAL_MUL_AC`; `CONJ_ACI`; `REAL_OF_NUM_ADD`) to obtain the desired conclusion.

### Mathematical insight
This theorem provides an alternative characterization of the floor of a real number divided by another real number, expressing the condition `floor(n / d) = k` as an interval condition on `n / k` and `n / (k+1)` relative to `d`. This is useful for reasoning about the floor function in situations where comparing `n / d` directly to an integer is not convenient. The special case `k = 0` is handled separately since the general condition involves division by `k` and `k+1`.

### Dependencies
- `FLOOR_EQ_0`
- `FLOOR_UNIQUE`
- `INTEGER_CLOSED`
- `REAL_LE_RDIV_EQ`
- `REAL_LT_LDIV_EQ`
- `REAL_OF_NUM_LT`
- `REAL_MUL_LZERO`
- `REAL_POS`
- `REAL_MUL_LID`
- `REAL_MUL_AC`
- `CONJ_ACI`
- `REAL_OF_NUM_ADD`
- `ARITH_RULE`


---

## FLOOR_DIV_EXISTS

### Name of formal statement
FLOOR_DIV_EXISTS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FLOOR_DIV_EXISTS = prove
 (`!n d. ~(d = 0)
         ==> ?k. (floor(&n / &d) = &k) /\
                 d * k <= n /\ n < d * (k + 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?k. floor (&n / &d) = &k` MP_TAC THENL
   [ASM_SIMP_TAC[FLOOR_NUM_EXISTS; REAL_LE_DIV; REAL_POS]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `k:num` THEN SIMP_TAC[] THEN ASM_SIMP_TAC[FLOOR_DIV_INTERVAL] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; LE_0; ADD_CLAUSES; REAL_OF_NUM_LT] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_OF_NUM_LT;
               ARITH_RULE `0 < k + 1 /\ (~(k = 0) ==> 0 < k)`] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
  REWRITE_TAC[CONJ_ACI]);;
```
### Informal statement
For all natural numbers `n` and `d`, if `d` is not equal to 0, then there exists a natural number `k` such that `floor(&n / &d) = &k` and `d * k <= n` and `n < d * (k + 1)`.

### Informal sketch
The proof proceeds by:
- First, stripping the quantifiers and the implication.
- Then, showing the existence of a natural number `k` such that `floor(&n / &d) = &k`. This step uses `FLOOR_NUM_EXISTS`, `REAL_LE_DIV` and `REAL_POS`.
- After this, apply `MONO_EXISTS` to introduce the variable `k:num`, and perform simplification.
- We then rewrite with `FLOOR_DIV_INTERVAL` to obtain the interval in which `&n / &d` lies.
- We proceed with case splitting on `k` and use arithmetic reasoning and simplification to establish `d * k <= n /\ n < d * (k + 1)`.
- The proof involves rewriting with `MULT_CLAUSES`, `LE_0`, `ADD_CLAUSES`, and `REAL_OF_NUM_LT`, followed by simplification utilizing rules like `REAL_LT_LDIV_EQ`, `REAL_LE_RDIV_EQ`, `REAL_OF_NUM_LT`, and an arithmetic rule.
- Finally, the proof rewrites using conversions from natural numbers to reals and applies associativity, commutativity and idempotence rules for conjunction.

### Mathematical insight
This theorem establishes the existence of a quotient `k` which is a natural number (`num`) when dividing two natural numbers `n` and `d`, such that `k` equals the floor of the real division of `n` and `d`. The conditions `d * k <= n` and `n < d * (k + 1)` guarantee integral division with remainder. This theorem provides essential properties for division in the natural numbers.

### Dependencies
- Theorems:
  - `FLOOR_NUM_EXISTS`
  - `REAL_LE_DIV`
  - `REAL_POS`
  - `FLOOR_DIV_INTERVAL`
- Other:
  - `MULT_CLAUSES`
  - `LE_0`
  - `ADD_CLAUSES`
  - `REAL_OF_NUM_LT`
  - `REAL_LT_LDIV_EQ`
  - `REAL_LE_RDIV_EQ`
  - `REAL_OF_NUM_MUL`
  - `CONJ_ACI`

### Porting notes (optional)
When porting to other proof assistants, ensure that there is a clear distinction between number types (natural numbers `num` vs reals). Also, the `floor` function and corresponding theorems about inequalities and existence of floor for real numbers need to be available. The arithmetic reasoning might require tactics or decision procedures specific to the target proof assistant. Handling of real number conversions from the natural numbers (`REAL_OF_NUM_*`) should also be verified.


---

## FLOOR_HALF_INTERVAL

### Name of formal statement
FLOOR_HALF_INTERVAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FLOOR_HALF_INTERVAL = prove
 (`!n d. ~(d = 0)
         ==> (floor (&n / &d) - &2 * floor (&(n DIV 2) / &d) =
                if ?k. ODD k /\ n DIV (k + 1) < d /\ d <= n DIV k
                then &1 else &0)`,
  let lemma = prove(`ODD(k) ==> ~(k = 0)`,MESON_TAC[EVEN; NOT_EVEN]) in
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP FLOOR_DIV_EXISTS) THEN
  FIRST_ASSUM(MP_TAC o SPEC `n DIV 2` o MATCH_MP FLOOR_DIV_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:num`
   (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:num`
   (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
  MAP_EVERY UNDISCH_TAC [`n DIV 2 < d * (k1 + 1)`; `d * k1 <= n DIV 2`] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> ~(a ==> ~(b /\ c))`] THEN
  SIMP_TAC[GSYM NOT_LE; LE_LDIV_EQ; LE_RDIV_EQ; ARITH_EQ; lemma; ADD_EQ_0] THEN
  REWRITE_TAC[NOT_LE; NOT_IMP] THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `d * 2 * k1 < d * (k2 + 1) /\ d * k2 < d * 2 * (k1 + 1)`
  MP_TAC THENL [ASM_MESON_TAC[LET_TRANS; MULT_AC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[LT_MULT_LCANCEL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP
   (ARITH_RULE
     `2 * k1 < k2 + 1 /\ k2 < 2 * (k1 + 1)
      ==> (k2 = 2 * k1) \/ (k2 = 2 * k1 + 1)`)) THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
              REAL_ADD_SUB; REAL_SUB_REFL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ] THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    DISCH_THEN(MP_TAC o SPEC `2 * k1 + 1`) THEN
    ASM_REWRITE_TAC[ARITH_ODD; ODD_ADD; ODD_MULT] THEN
    ASM_MESON_TAC[MULT_AC]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[ODD_EXISTS; ADD1] THEN
  DISCH_THEN(X_CHOOSE_THEN `k3:num` SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `d * 2 * k1 < d * ((2 * k3 + 1) + 1) /\
                d * (2 * k3 + 1) < d * 2 * (k1 + 1)`
  MP_TAC THENL [ASM_MESON_TAC[LET_TRANS; MULT_AC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[LT_MULT_LCANCEL] THEN
  DISCH_THEN(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
   `2 * k1 < (2 * k3 + 1) + 1 /\ 2 * k3 + 1 < 2 * (k1 + 1)
    ==> (k3 = k1)`)) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC);;
```
### Informal statement
For all natural numbers `n` and `d`, if `d` is not equal to 0, then `floor(n / d) - 2 * floor((n DIV 2) / d)` is equal to 1 if there exists a natural number `k` such that `k` is odd and `n DIV (k + 1) < d` and `d <= n DIV k`; otherwise, it is equal to 0.

### Informal sketch
The proof proceeds by showing that the expression `floor(n / d) - 2 * floor((n DIV 2) / d)` evaluates to 1 under the condition that `exists k. ODD k /\ n DIV (k + 1) < d /\ d <= n DIV k`, and 0 otherwise.
- First, rewrite `floor(n/d)` using `FLOOR_DIV_EXISTS` to introduce `k1` such that `d * k1 <= n < d * (k1 + 1)`.
- Then, rewrite `floor((n DIV 2)/d)` using `FLOOR_DIV_EXISTS` to introduce `k2` such that `d * k2 <= n DIV 2 < d * (k2 + 1)`.
- Manipulate the inequalities to get `d * 2 * k1 < d * (k2 + 1) /\ d * k2 < d * 2 * (k1 + 1)`.
- Simplify the inequalities by canceling d: `2 * k1 < k2 + 1 /\ k2 < 2 * (k1 + 1)`.
- By arithmetic reasoning, `k2` must be either `2 * k1` or `2 * k1 + 1`.
- Consider the two cases for `k2`.
  - If `k2 = 2 * k1`, then we aim to disprove `exists k. ODD k /\ n DIV (k + 1) < d /\ d <= n DIV k`.
    - We assume `exists k. ODD k /\ n DIV (k + 1) < d /\ d <= n DIV k` and arrive at contradiction, which solves the first case where the expression will be 0.
  - If `k2 = 2 * k1 + 1`, then we need to prove the existence of `k` such that `ODD k /\ n DIV (k + 1) < d /\ d <= n DIV k`.
    - Instantiate it with `2 * k1 + 1` and manipulate the inequalities to show that it is true, which solves the second case where expression will be 1.

### Mathematical insight
This theorem relates the floor function of `n/d` to the floor function of `(n DIV 2)/d`. The essential idea is to characterize the difference `floor(n / d) - 2 * floor((n DIV 2) / d)` in terms of whether `d` falls within a certain range determined by `n` and an odd number `k`. This result can be used to analyze the behavior of floor functions and integer division.

### Dependencies
- `EVEN`
- `NOT_EVEN`
- `FLOOR_DIV_EXISTS`
- `NOT_LE`
- `LE_LDIV_EQ`
- `LE_RDIV_EQ`
- `ARITH_EQ`
- `ADD_EQ_0`
- `LET_TRANS`
- `MULT_AC`
- `LT_MULT_LCANCEL`
- `REAL_OF_NUM_ADD`
- `REAL_OF_NUM_MUL`
- `REAL_ADD_SUB`
- `REAL_SUB_REFL`
- `REAL_OF_NUM_EQ`
- `ARITH_ODD`
- `ODD_ADD`
- `ODD_MULT`
- `NOT_EXISTS_THM`
- `ODD_EXISTS`
- `ADD1`

### Porting notes (optional)
- The proof relies heavily on arithmetic reasoning and inequality manipulation. A proof assistant with strong automation for linear arithmetic should be helpful.
- The automatic choice of witnesses (`X_CHOOSE_THEN`) may need to be translated to explicit existence proofs in some other proof assistants.


---

## SUM_EXPAND_LEMMA

### Name of formal statement
SUM_EXPAND_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_EXPAND_LEMMA = prove
 (`!n m k. (m + 2 * k = n)
         ==> (sum (1,n DIV (2 * k + 1))
                  (\d. if ?k. ODD k /\ n DIV (k + 1) < d /\ d <= n DIV k
                       then mangoldt d else &0) =
              sum (1,n) (\d. --(&1) pow (d + 1) * psi (n DIV d)) -
              sum (1,2 * k)
                  (\d. --(&1) pow (d + 1) * psi (n DIV d)))`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_SIMP_TAC[DIV_0; ADD_EQ_0; ARITH_EQ; REAL_SUB_REFL; sum]; ALL_TAC] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `m:num` THEN ASM_CASES_TAC `m = 0` THENL
   [DISCH_THEN(K ALL_TAC) THEN ASM_SIMP_TAC[ADD_CLAUSES] THEN
    ASM_SIMP_TAC[DIV_REFL; SUM_1; DIV_1; REAL_SUB_REFL] THEN
    SUBGOAL_THEN `n DIV (n + 1) = 0` (fun th -> REWRITE_TAC[th; sum]) THEN
    ASM_MESON_TAC[DIV_EQ_0; ARITH_RULE `n < n + 1 /\ ~(n + 1 = 0)`];
    ALL_TAC] THEN
  ASM_CASES_TAC `m = 1` THENL
   [DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:num` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM ADD1; ARITH_RULE `1 + n = SUC n`] THEN
    SIMP_TAC[DIV_REFL; NOT_SUC; sum; SUM_1] THEN
    REWRITE_TAC[REAL_ADD_SUB; mangoldt] THEN
    CONV_TAC(ONCE_DEPTH_CONV PRIMEPOW_CONV) THEN
    REWRITE_TAC[COND_ID] THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC[REAL_ENTIRE] THEN DISJ2_TAC THEN
    REWRITE_TAC[ARITH_RULE `1 + n = SUC n`] THEN
    SIMP_TAC[DIV_REFL; NOT_SUC] THEN REWRITE_TAC(LN_1::PSI_LIST 1);
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `m - 2`) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(m = 0) ==> m - 2 < m`] THEN
  DISCH_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC k`) THEN ANTS_TAC THENL
   [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o funpow 2 RAND_CONV o TOP_DEPTH_CONV)
   [ARITH_RULE `2 * SUC k = SUC(SUC(2 * k))`; sum] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(s - ss = x + y) ==> (ss = a - ((b + x) + y)) ==> (s = a - b)`) THEN
  REWRITE_TAC[REAL_POW_NEG; EVEN_ADD; ARITH_EVEN; EVEN; EVEN_MULT] THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID; REAL_MUL_LNEG] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ADD_SYM] THEN
  REWRITE_TAC[psi; GSYM real_sub] THEN
  MATCH_MP_TAC(REAL_ARITH `!b. (a - b = d) /\ (b = c) ==> (a - c = d)`) THEN
  EXISTS_TAC `sum (1,n DIV (SUC (2 * k) + 1))
                  (\d. if ?k. ODD k /\ n DIV (k + 1) < d /\ d <= n DIV k
                       then mangoldt d else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_DIFFERENCES_EQ THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIV_MONO2 THEN ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `r:num` THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    DISCH_THEN(MP_TAC o SPEC `2 * k + 1`) THEN
    REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH_ODD] THEN
    ASM_REWRITE_TAC[ARITH_RULE `n <= r <=> n < 1 + r`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `n < r <=> 1 + n <= r`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `(2 * k + 1) + 1 = SUC(2 * k) + 1`];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_MORETERMS_EQ THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIV_MONO2 THEN ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `r:num` THEN
  REWRITE_TAC[ARITH_RULE `2 * SUC k + 1 = 2 * k + 3`] THEN
  REWRITE_TAC[ARITH_RULE `SUC(2 * k) + 1 = 2 * k + 2`] THEN STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `oj:num` MP_TAC) THEN
  REWRITE_TAC[ODD_EXISTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` SUBST1_TAC) THEN
  REWRITE_TAC[ARITH_RULE `SUC(2 * k) + 1 = 2 * k + 2`] THEN
  REWRITE_TAC[ARITH_RULE `SUC(2 * k) = 2 * k + 1`] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `1 + a <= b ==> a < b`)) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `a < 1 + b ==> a <= b`)) THEN
  SIMP_TAC[GSYM NOT_LE; LE_RDIV_EQ; LE_LDIV_EQ; ADD_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[NOT_LE] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(2 * j + 1) * r < (2 * k + 3) * r /\
                (2 * k + 2) * r < (2 * j + 2) * r`
  MP_TAC THENL [ASM_MESON_TAC[LET_TRANS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[LT_MULT_RCANCEL] THEN
  ASM_CASES_TAC `r = 0` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
   `2 * j + 1 < 2 * k + 3 /\ 2 * k + 2 < 2 * j + 2 ==> (j = k)`)) THEN
  ASM_MESON_TAC[LET_TRANS; LT_REFL; MULT_AC]);;
```

### Informal statement
For all natural numbers `n`, `m`, and `k`, if `m + 2 * k = n`, then
the sum from `d = 1` to `n DIV (2 * k + 1)` of the function that returns `mangoldt d` if there exists some `k` such that `k` is odd and `n DIV (k + 1) < d` and `d <= n DIV k`, and returns 0 otherwise, is equal to the sum from `d = 1` to `n` of `(-1)^(d+1) * psi(n DIV d)` minus the sum from `d = 1` to `2 * k` of `(-1)^(d+1) * psi(n DIV d)`.

### Informal sketch
The proof proceeds by induction-like reasoning, but with explicit case splits.
- Case split on `n = 0`. The goal is simplified using arithmetic and summation lemmas.
- Assuming `n > 0`, introduce `m` such that `n = m + 2 * k`.
- Case split on `m = 0`. Simplify using arithmetic and summation rules.
- Case split on `m = 1`.
  - Deduce `n = 2 * k + 1`.
  - Simplify sums and invoke `mangoldt` definition in the case of prime power.
  - Reduce to known formulas for `ln 1` and the values of function `psi` at 1.
- Assuming `m > 1`, obtain hypothesis for `m - 2`. Introduce `k` such that `n = m + 2 * k`.
  - Apply inductive hypothesis after arithmetic reasoning.
  - Expand sums using `2 * SUC k = SUC(SUC(2 * k))`.
  - Use real arithmetic to rewrite the target into `s = a - b` from `s - ss = x + y` and `ss = a - ((b + x) + y)`.
  - Use properties of `REAL_POW_NEG`, `EVEN_ADD`, `ARITH_EVEN`, `EVEN`, and `EVEN_MULT`.
  - Apply `REAL_POW_ONE`, `REAL_MUL_LID`, and `REAL_MUL_LNEG`.
  - Apply properties of `psi` and arithmetic simplifications.
  - Exploit identities involving sums of differences.
  - Reduce to showing inequalities.
  - Show that `(2 * j + 1) * r < (2 * k + 3) * r /\ (2 * k + 2) * r < (2 * j + 2) * r`.
  - Case split on `r = 0`, then use arithmetic and assumption to finish the proof.

### Mathematical insight
This theorem relates a sum involving the `mangoldt` function to another sum involving the `psi` function. The `mangoldt` function is non-zero only at prime powers. The `psi` function is Chebyshev's function.  The equation appears to be a combinatorial identity arising from number theory, possibly related to prime number distribution. The condition `m + 2 * k = n` seems to be a specific way to iterate through the space by induction with a step of 2.

### Dependencies
- `DIV_0`, `ADD_EQ_0`, `ARITH_EQ`, `REAL_SUB_REFL`, `sum`, `num_WF`, `ADD_CLAUSES`, `DIV_REFL`, `SUM_1`, `DIV_1`, `GSYM ADD1`, `ARITH_RULE 1 + n = SUC n`, `NOT_SUC`, `REAL_ADD_SUB`, `mangoldt`, `PRIMEPOW_CONV`, `COND_ID`, `REAL_ENTIRE`, `LN_1`, items of `PSI_LIST`, `REAL_ARITH`, `REAL_POW_NEG`, `EVEN_ADD`, `ARITH_EVEN`, `EVEN`, `EVEN_MULT`, `REAL_POW_ONE`, `REAL_MUL_LID`, `REAL_MUL_LNEG`, `ADD_SYM`, `psi`, `real_sub`, `SUM_DIFFERENCES_EQ`, `DIV_MONO2`, `NOT_EXISTS_THM`, `ODD_ADD`, `ODD_MULT`, `ARITH_ODD`, `ARITH_RULE n <= r <=> n < 1 + r`, `ARITH_RULE n < r <=> 1 + n <= r`, `ARITH_RULE (2 * k + 1) + 1 = SUC(2 * k) + 1`, `SUM_MORETERMS_EQ`, `ARITH_RULE 2 * SUC k + 1 = 2 * k + 3`, `ARITH_RULE SUC(2 * k) + 1 = 2 * k + 2`, `ODD_EXISTS`, `ARITH_RULE 1 + a <= b ==> a < b`, `ARITH_RULE a < 1 + b ==> a <= b`, `NOT_LE`, `LE_RDIV_EQ`, `LE_LDIV_EQ`, `ARITH_EQ`, `LT_MULT_RCANCEL`, `ARITH_RULE 2 * j + 1 < 2 * k + 3 /\ 2 * k + 2 < 2 * j + 2 ==> (j = k)`, `LET_TRANS`, `LT_REFL`, `MULT_AC`

### Porting notes (optional)
The proof relies heavily on built-in arithmetic simplification and rewriting. Ensure the target system has equivalent automation. The use of `EXISTS_TAC` followed by `CONJ_TAC` suggests the need for existential reasoning and proof by cases. Special attention should be put on how `mangoldt` and `psi` functions are defined as it may be required to prove equality between definitions.


---

## FACT_EXPAND_PSI

### Name of formal statement
FACT_EXPAND_PSI

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FACT_EXPAND_PSI = prove
 (`!n. ln(&(FACT(n))) - &2 * ln(&(FACT(n DIV 2))) =
          sum(1,n) (\d. --(&1) pow (d + 1) * psi(n DIV d))`,
  GEN_TAC THEN REWRITE_TAC[MANGOLDT] THEN
  SUBGOAL_THEN
   `sum (1,n DIV 2) (\d. mangoldt d * floor (&(n DIV 2) / &d)) =
    sum (1,n) (\d. mangoldt d * floor (&(n DIV 2) / &d))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `n = n DIV 2 + (n - n DIV 2)`
     (fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [th])
    THENL [MESON_TAC[SUB_ADD; DIV_LE; ADD_SYM; NUM_REDUCE_CONV `2 = 0`];
           ALL_TAC] THEN
    REWRITE_TAC[GSYM SUM_SPLIT] THEN
    MATCH_MP_TAC(REAL_ARITH `(b = &0) ==> (a = a + b)`) THEN
    MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ENTIRE; FLOOR_EQ_0] THEN DISJ2_TAC THEN
    SIMP_TAC[REAL_LE_DIV; REAL_POS] THEN
    SUBGOAL_THEN `0 < r /\ n DIV 2 < r` MP_TAC THENL
     [UNDISCH_TAC `1 + n DIV 2 <= r` THEN ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; REAL_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_CMUL; GSYM SUM_SUB] THEN
  REWRITE_TAC[REAL_ARITH `m * x - &2 * m * y = m * (x - &2 * y)`] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1,n) (\d. if ?k. ODD k /\ n DIV (k + 1) < d /\ d <= n DIV k
                  then mangoldt d else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[FLOOR_HALF_INTERVAL; ARITH_RULE `1 <= d ==> ~(d = 0)`] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO];
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `n:num`; `0`] SUM_EXPAND_LEMMA) THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; sum; REAL_SUB_RZERO; DIV_1]);;
```

### Informal statement
For all natural numbers `n`, the natural logarithm of the factorial of `n` minus 2 times the natural logarithm of the factorial of `n` divided by 2 is equal to the sum from 1 to `n` of the function that maps `d` to negative 1 raised to the power of `d + 1`, multiplied by the `psi` function evaluated at `n` divided by `d`.

### Informal sketch
The proof proceeds by:
- Rewriting with the definition of the `Mangoldt` function (`MANGOLDT`).
- Proving the subgoal `sum (1,n DIV 2) (\d. mangoldt d * floor (&(n DIV 2) / &d)) = sum (1,n) (\d. mangoldt d * floor (&(n DIV 2) / &d))`.
- Substituting `n = n DIV 2 + (n - n DIV 2)`.
- Splitting the summation range using `SUM_SPLIT`.
- Showing that the additional term arising from the split is zero, using `SUM_EQ_0` and properties of `floor`. This involves proving that the floor of `n DIV 2` divided by `r` equals 0, where `r` is a number greater than `n DIV 2`.
- Rewriting with properties of sums (`SUM_CMUL`, `SUM_SUB`) and performing arithmetic simplification.
- Showing this is equivalent to a sum involving a conditional term `if ?k. ODD k /\ n DIV (k + 1) < d /\ d <= n DIV k then mangoldt d else &0`. This introduces a conditional which includes an existential quantifier on `k`.
- Simplifying the conditional sum using `FLOOR_HALF_INTERVAL`.
- Expanding a specialized sum using `SUM_EXPAND_LEMMA` to finalize the proof.

### Mathematical insight
This theorem relates the logarithm of the factorial function to a sum involving the `psi` function, which is related to the von Mangoldt function. This is a result connecting number-theoretic functions with logarithmic expressions.

### Dependencies
- `MANGOLDT`
- `SUB_ADD`
- `DIV_LE`
- `ADD_SYM`
- `NUM_REDUCE_CONV`
- `GSYM`
- `SUM_SPLIT`
- `REAL_ARITH`
- `SUM_EQ_0`
- `REAL_ENTIRE`
- `FLOOR_EQ_0`
- `REAL_LE_DIV`
- `REAL_POS`
- `REAL_LT_LDIV_EQ`
- `REAL_OF_NUM_LT`
- `REAL_MUL_LID`
- `SUM_CMUL`
- `SUM_SUB`
- `EQ_TRANS`
- `SUM_EQ`
- `FLOOR_HALF_INTERVAL`
- `ARITH_RULE`
- `SUM_EXPAND_LEMMA`
- `ADD_CLAUSES`
- `MULT_CLAUSES`
- `REAL_SUB_RZERO`
- `DIV_1`


---

## PSI_MONO

### Name of formal statement
PSI_MONO

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_MONO = prove
 (`!m n. m <= n ==> psi(m) <= psi(n)`,
  SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM; psi] THEN
  REWRITE_TAC[GSYM SUM_SPLIT] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_ADDR] THEN
  MATCH_MP_TAC SUM_POS_GEN THEN REWRITE_TAC[MANGOLDT_POS]);;
```

### Informal statement
For all natural numbers `m` and `n`, if `m` is less than or equal to `n`, then `psi(m)` is less than or equal to `psi(n)`.

### Informal sketch
The proof proceeds as follows:
- First, expand the less-than-or-equal relation using `LE_EXISTS` and the definition of `psi`.
- Rewrite using `SUM_SPLIT` (generalized) to separate sums, and then repeatedly strip quantifiers and implications.
- Rewrite the less-than-or-equal relation for real numbers using `REAL_LE_ADDR` and apply `SUM_POS_GEN`, which states that a sum of positive numbers is positive.
- Rewrite using `MANGOLDT_POS`, which asserts that the Mangoldt function is non-negative.

### Mathematical insight
This theorem establishes that the `psi` function (Chebyshev function) is monotonically increasing. This is a crucial property for bounding and approximating `psi(x)`. The proof leverages the fact that `psi(x)` is defined as a sum of non-negative terms (the Mangoldt function), and therefore increasing the upper bound of the sum will never decrease the overall value.

### Dependencies
- Definitions: `psi`
- Theorems: `LE_EXISTS`, `LEFT_IMP_EXISTS_THM`, `SUM_SPLIT`, `REAL_LE_ADDR`, `SUM_POS_GEN`, `MANGOLDT_POS`


---

## PSI_POS

### Name of formal statement
PSI_POS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_POS = prove
 (`!n. &0 <= psi(n)`,
  SUBGOAL_THEN `psi(0) = &0` (fun th -> MESON_TAC[th; PSI_MONO; LE_0]) THEN
  REWRITE_TAC(LN_1::PSI_LIST 0));;
```
### Informal statement
For all natural numbers `n`, `0` is less than or equal to `psi(n)`.

### Informal sketch
The proof proceeds as follows:
- First, show that `psi(0) = &0`. This is achieved using `MESON_TAC` with the assumption `PSI_MONO` (monotonicity of `psi`) and `LE_0` (a theorem about less than or equal to zero) to prove the base case.
- Then, rewrite the goal using the result of `LN_1::PSI_LIST 0`, which lists the properties of `psi` for the case when `n` is 0.

### Mathematical insight
The theorem `PSI_POS` establishes that the function `psi`, when applied to any natural number, always yields a non-negative real number. This lower bound is a basic property of the `psi` function, which is probably related to logarithms.

### Dependencies
- Theorems: `PSI_MONO`, `LE_0`, `LN_1`
- Definitions: `psi`
- Lists: `PSI_LIST`


---

## PSI_EXPANSION_CUTOFF

### Name of formal statement
PSI_EXPANSION_CUTOFF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_EXPANSION_CUTOFF = prove
 (`!n m p. m <= p
         ==> sum(1,2 * m) (\d. --(&1) pow (d + 1) * psi(n DIV d))
               <= sum(1,2 * p) (\d. --(&1) pow (d + 1) * psi(n DIV d)) /\
             sum(1,2 * p + 1) (\d. --(&1) pow (d + 1) * psi(n DIV d))
               <= sum(1,2 * m + 1) (\d. --(&1) pow (d + 1) * psi(n DIV d))`,
  GEN_TAC THEN SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM] THEN
  GEN_REWRITE_TAC BINDER_CONV [SWAP_FORALL_THM] THEN
  SIMP_TAC[LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  X_GEN_TAC `m:num` THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; REAL_LE_REFL] THEN
  REWRITE_TAC[ARITH_RULE `2 * SUC n = SUC(SUC(2 * n))`;
              ARITH_RULE `SUC(SUC n) + 1 = SUC(SUC(n + 1))`; sum] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `s1 <= s1' /\ s2' <= s2
    ==> &0 <= a + b /\ &0 <= --c + --d
        ==> s1 <= (s1' + a) + b /\ (s2' + c) + d <= s2`)) THEN
  REWRITE_TAC[REAL_POW_NEG; EVEN_ADD; EVEN_MULT; ARITH_EVEN; EVEN] THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID; REAL_MUL_LNEG; REAL_NEG_NEG] THEN
  REWRITE_TAC[REAL_ARITH `&0 <= a + --b <=> b <= a`] THEN
  CONJ_TAC THEN MATCH_MP_TAC PSI_MONO THEN
  MATCH_MP_TAC DIV_MONO2 THEN ARITH_TAC);;
```

### Informal statement
For all natural numbers `n`, `m`, and `p`, if `m` is less than or equal to `p`, then the following two conditions hold:
1. The sum from `d = 1` to `2 * m` of `(-1)^(d+1) * psi(n / d)` is less than or equal to the sum from `d = 1` to `2 * p` of `(-1)^(d+1) * psi(n / d)`.
2. The sum from `d = 1` to `2 * p + 1` of `(-1)^(d+1) * psi(n / d)` is less than or equal to the sum from `d = 1` to `2 * m + 1` of `(-1)^(d+1) * psi(n / d)`.

### Informal sketch
The proof proceeds by induction on `m`.
- The base case is handled by rewriting with basic arithmetic facts.
- In the inductive step, we assume the theorem holds for `m` and prove it for `m + 1`.
- Using the induction hypothesis, we show the inequality holds by comparing sums with `2 * m` and `2 * p`.
- The tactic `REAL_ARITH` handles reasoning about real number inequalities.
- The monotonicity of `psi` (`PSI_MONO`) and integer division (`DIV_MONO2`) are used.
- Rewriting with facts about even and odd numbers is also applied.

### Mathematical insight
This theorem establishes a bound on the partial sums of an alternating series involving the `psi` function and the integer division operation. It essentially captures the idea that as we increase the cutoff point in the summation, the value oscillates, but remains bounded. The bound is crucial in contexts where we want to approximate an infinite sum by truncating it at a finite point, ensuring accuracy up to a certain level.

### Dependencies

**Theorems, Definitions, and Rules:**
- `LE_EXISTS`
- `LEFT_IMP_EXISTS_THM`
- `SWAP_FORALL_THM`
- `LEFT_FORALL_IMP_THM`
- `EXISTS_REFL`
- `ADD_CLAUSES`
- `REAL_LE_REFL`
- `REAL_POW_NEG`
- `EVEN_ADD`
- `EVEN_MULT`
- `ARITH_EVEN`
- `EVEN`
- `REAL_POW_ONE`
- `REAL_MUL_LID`
- `REAL_MUL_LNEG`
- `REAL_NEG_NEG`
- `PSI_MONO`
- `DIV_MONO2`

**Tactics:**
- `ARITH_RULE`
- `REAL_ARITH`
- `INDUCT_TAC`
- `GEN_TAC`
- `SIMP_TAC`
- `GEN_REWRITE_TAC`
- `X_GEN_TAC`
- `REWRITE_TAC`
- `FIRST_ASSUM`
- `MATCH_MP_TAC`
- `MATCH_MP`
- `CONJ_TAC`
- `ARITH_TAC`
- `BINDER_CONV`

### Porting notes (optional)
- The `psi` function might need a custom definition in other systems.
- The `ARITH_TAC` tactic in HOL Light is quite powerful, so the required arithmetic reasoning steps might need to be spelled out more explicitly in less automated systems.
- The handling of real number arithmetic, especially inequalities, needs to be carefully checked.


---

## FACT_PSI_BOUND_ODD

### Name of formal statement
FACT_PSI_BOUND_ODD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FACT_PSI_BOUND_ODD = prove
 (`!n k. ODD(k)
         ==> ln(&(FACT n)) - &2 * ln(&(FACT (n DIV 2)))
             <= sum(1,k) (\d. --(&1) pow (d + 1) * psi(n DIV d))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FACT_EXPAND_PSI] THEN
  ASM_CASES_TAC `k <= n:num` THENL
   [ALL_TAC;
    MATCH_MP_TAC(REAL_ARITH `(b = a) ==> a <= b`) THEN
    MATCH_MP_TAC SUM_MORETERMS_EQ THEN
    ASM_SIMP_TAC[ARITH_RULE `~(k <= n) ==> n <= k:num`] THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN REWRITE_TAC[REAL_ENTIRE] THEN
    DISJ2_TAC THEN SUBGOAL_THEN `n DIV r = 0` SUBST1_TAC THENL
     [ASM_MESON_TAC[DIV_EQ_0; ARITH_RULE `1 + n <= r ==> n < r /\ ~(r = 0)`];
      REWRITE_TAC(LN_1::PSI_LIST 0)]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1,SUC(2 * n DIV 2))
                 (\d. -- &1 pow (d + 1) * psi (n DIV d))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `m <= n DIV 2`
     (fun th -> SIMP_TAC[th; ADD1; PSI_EXPANSION_CUTOFF]) THEN
    SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN
    POP_ASSUM MP_TAC THEN ARITH_TAC] THEN
  MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
  MAP_EVERY ABBREV_TAC [`q = n DIV 2`; `r = n MOD 2`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [th])
   MP_TAC) THEN
  REWRITE_TAC[ARITH_RULE `r < 2 <=> (r = 0) \/ (r = 1)`] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[ADD1; MULT_AC; REAL_LE_REFL] THEN
  REWRITE_TAC[GSYM ADD1; ADD_CLAUSES; sum; REAL_LE_ADDR] THEN
  REWRITE_TAC[REAL_POW_NEG; EVEN; EVEN_ADD; EVEN_MULT; ARITH_EVEN] THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID; PSI_POS]);;
```
### Informal statement
For all natural numbers `n` and `k`, if `k` is odd, then
`ln(fact(n)) - 2 * ln(fact(n div 2))` is less than or equal to the sum from `d = 1` to `k` of `(-1)^(d+1) * psi(n div d)`.

### Informal sketch
The proof proceeds as follows:
- First, expand the `psi` function using `FACT_EXPAND_PSI`.
- Perform a case split on whether `k <= n`.
- **Case 1:** `k <= n`. In this case, the goal becomes an inequality about sums.
- **Case 2:** `~(k <= n)`. Here, one applies transitivity with the theorem `SUM_MORETERMS_EQ` that states how to calculate sums when upper bounds are extended. Subsequently introduce variable `r`, rewrite using `REAL_ENTIRE`, reduce subgoal `n div r = 0` by showing premise `1 + n <= r ==> n < r /\ ~(r = 0)`, and apply theorems about `LN_1` and `PSI_LIST`.
- Decompose the odd condition on `k` into `k = 2 * m + 1` form with existential quantifier.
- Apply transitivity rule `REAL_LE_TRANS`, substituting with the sum from `d = 1` to `2 * (n DIV 2) + 1` of `(-1)^(d+1) * psi(n DIV d)`.
- Refine the proof using properties of division and inequalities, specifically `m <= n DIV 2`, simplifying with `LE_RDIV_EQ` and `ARITH_EQ`. Some `psi` values are expanded with premise `m <= n DIV 2` using `PSI_EXPANSION_CUTOFF`. Then arithmetic tactic `ARITH_TAC`.
- Exploit the division theorem `DIVISION` to write `n = 2 * q + r`, where `q = n DIV 2` and `r = n MOD 2`.
- Perform proof engineering that splits the case based on modular arithmetic on `r < 2 <=> (r = 0) \/ (r = 1)` .
- Conclude, using properties of real numbers, addition, multiplication, exponentiation, parity, and the fact that `psi` is positive, to show the reflexivity `REAL_LE_REFL` of real number inequality.

### Mathematical insight
This theorem provides an upper bound for `ln(fact(n)) - 2 * ln(fact(n div 2))` when `k` is odd, expressed using the `psi` function and a sum. This relates factorial bounds to the psi function via an inequality.

### Dependencies
- `FACT_EXPAND_PSI`
- `DIV_EQ_0`
- `ODD_EXISTS`
- `REAL_LE_TRANS`
- `DIVISION`
- `LN_1`
- `PSI_LIST`
- `ADD1`
- `PSI_EXPANSION_CUTOFF`
- `LE_RDIV_EQ`
- `ARITH_EQ`
- `ARITH_RULE`
- `REAL_ENTIRE`
- `SUM_MORETERMS_EQ`
- `MULT_AC`
- `ADD_CLAUSES`
- `REAL_LE_ADDR`
- `REAL_POW_NEG`
- `EVEN`
- `EVEN_ADD`
- `EVEN_MULT`
- `ARITH_EVEN`
- `REAL_POW_ONE`
- `REAL_MUL_LID`
- `PSI_POS`
- `LAND_CONV`
- `REAL_LE_REFL`

### Porting notes (optional)
- The proof relies heavily on real arithmetic reasoning. A proof assistant with strong support for real number inequalities would be beneficial.
- The extensive use of rewriting suggests that a system with good equational reasoning capabilities is desirable.
- Be careful with the handling of integer division (`DIV`) and modulo (`MOD`) operations, as different systems may have different semantics.


---

## FACT_PSI_BOUND_EVEN

### Name of formal statement
FACT_PSI_BOUND_EVEN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FACT_PSI_BOUND_EVEN = prove
 (`!n k. EVEN(k)
         ==> sum(1,k) (\d. --(&1) pow (d + 1) * psi(n DIV d))
             <= ln(&(FACT n)) - &2 * ln(&(FACT (n DIV 2)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FACT_EXPAND_PSI] THEN
  ASM_CASES_TAC `k <= n:num` THENL
   [ALL_TAC;
    MATCH_MP_TAC(REAL_ARITH `(a = b) ==> a <= b`) THEN
    MATCH_MP_TAC SUM_MORETERMS_EQ THEN
    ASM_SIMP_TAC[ARITH_RULE `~(k <= n) ==> n <= k:num`] THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN REWRITE_TAC[REAL_ENTIRE] THEN
    DISJ2_TAC THEN SUBGOAL_THEN `n DIV r = 0` SUBST1_TAC THENL
     [ASM_MESON_TAC[DIV_EQ_0; ARITH_RULE `1 + n <= r ==> n < r /\ ~(r = 0)`];
      REWRITE_TAC(LN_1::PSI_LIST 0)]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1,2 * n DIV 2)
                 (\d. -- &1 pow (d + 1) * psi (n DIV d))` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `m <= n DIV 2`
     (fun th -> SIMP_TAC[th; ADD1; PSI_EXPANSION_CUTOFF]) THEN
    SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN
    POP_ASSUM MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
  MAP_EVERY ABBREV_TAC [`q = n DIV 2`; `r = n MOD 2`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [th])
   MP_TAC) THEN
  REWRITE_TAC[ARITH_RULE `r < 2 <=> (r = 0) \/ (r = 1)`] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[ADD1; MULT_AC; ADD_CLAUSES; REAL_LE_REFL] THEN
  REWRITE_TAC[GSYM ADD1; ADD_CLAUSES; sum; REAL_LE_ADDR] THEN
  REWRITE_TAC[REAL_POW_NEG; EVEN; EVEN_ADD; EVEN_MULT; ARITH_EVEN] THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID; PSI_POS]);;
```

### Informal statement
For all natural numbers `n` and `k`, if `k` is even, then the sum from `d = 1` to `k` of `(-1)^(d+1) * psi(n DIV d)` is less than or equal to `ln(FACT n) - 2 * ln(FACT (n DIV 2))`.

### Informal sketch
The proof proceeds as follows:
- Expand `psi` using `FACT_EXPAND_PSI`.
- Perform case analysis on `k <= n`.
- In the case where `k > n`, simplify the target using `SUM_MORETERMS_EQ` and show the second term `sum(n+1,k) (\d. --(&1) pow (d + 1) * psi(n DIV d))` is zero. This requires showing `n DIV r = 0` where `r` is universally quantified between `n+1` and `k` and using the fact that `n < r` to get `n DIV r=0`.
- In the case where `k <= n`, apply a rewriting using `EVEN n <!> $EX m. n = 2 * m`.
- Choose such an `m` and instantiate the goal with `sum(1,2 * n DIV 2) (\d. -- &1 pow (d + 1) * psi (n DIV d))`.
- Show that `m <= n DIV 2` using `LE_RDIV_EQ` and `ARITH_EQ`.
- Simplify using `ADD1` and `PSI_EXPANSION_CUTOFF`.
- Apply the theorem `DIVISION` on `n` and `2`.
- Rename `n DIV 2` to `q` and `n MOD 2` to `r`.
- Use the fact that `r < 2 <=> (r = 0) \/ (r = 1)`.
- Perform cases analysis on whether `r = 0` or `r = 1`.
- Rewrite using algebraic properties: `ADD1`, `MULT_AC`, `ADD_CLAUSES`, `REAL_LE_REFL`, `REAL_LE_ADDR`, `REAL_POW_NEG`, `EVEN`, `EVEN_ADD`, `EVEN_MULT`, `ARITH_EVEN`, `REAL_POW_ONE`, `REAL_MUL_LID`, and `PSI_POS`.

### Mathematical insight
The theorem provides an upper bound for a sum involving the `psi` function, which relates to the prime factorization of numbers. This theorem is a step in bounding the prime counting function `pi(x)`.

### Dependencies
- Definitions: `EVEN`, `DIV`, `FACT`, `ln`, `pow`, `psi`
- Theorems: `FACT_EXPAND_PSI`, `REAL_ARITH`, `SUM_MORETERMS_EQ`, `DIV_EQ_0`, `LN_1`, `PSI_LIST`, `EVEN_EXISTS`, `REAL_LE_TRANS`, `LE_RDIV_EQ`, `ARITH_EQ`, `DIVISION`, `ARITH_RULE`, `ADD1`, `PSI_EXPANSION_CUTOFF`
- Rules: `REAL_LE_REFL`, `REAL_LE_ADDR`, `REAL_POW_NEG`, `EVEN_ADD`, `EVEN_MULT`, `ARITH_EVEN`, `REAL_POW_ONE`, `REAL_MUL_LID`, `PSI_POS`, `MULT_AC`, `ADD_CLAUSES`

### Porting notes (optional)
- The proof relies heavily on rewriting with arithmetic facts and real number inequalities. A proof assistant with strong support for real number arithmetic and rewriting will be beneficial.
- The `PSI_EXPANSION_CUTOFF` theorem and other theorems related to the `psi` function should be ported first as they form important steps in the simplification.


---

## FACT_PSI_BOUND_2_3

### Name of formal statement
FACT_PSI_BOUND_2_3

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FACT_PSI_BOUND_2_3 = prove
 (`!n. psi(n) - psi(n DIV 2)
       <= ln(&(FACT n)) - &2 * ln(&(FACT (n DIV 2))) /\
       ln(&(FACT n)) - &2 * ln(&(FACT (n DIV 2)))
       <= psi(n) - psi(n DIV 2) + psi(n DIV 3)`,
  GEN_TAC THEN
  MP_TAC(SPECL [`n:num`; `2`] FACT_PSI_BOUND_EVEN) THEN
  MP_TAC(SPECL [`n:num`; `3`] FACT_PSI_BOUND_ODD) THEN
  REWRITE_TAC[ARITH] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_SUM_CONV) THEN
  REWRITE_TAC[ARITH; REAL_ADD_LID; DIV_1] THEN
  REWRITE_TAC[REAL_POW_NEG; ARITH; REAL_POW_ONE; REAL_MUL_LID] THEN
  REAL_ARITH_TAC);;
```

### Informal statement
For all natural numbers `n`, the following inequalities hold:
1.  `psi(n) - psi(n DIV 2) <= ln(&(FACT n)) - &2 * ln(&(FACT (n DIV 2)))`
2.  `ln(&(FACT n)) - &2 * ln(&(FACT (n DIV 2))) <= psi(n) - psi(n DIV 2) + psi(n DIV 3)`

where `psi(n)` is the Chebyshev function, `FACT n` is the factorial of `n`, and `ln` is the natural logarithm. `n DIV k` is integer division of `n` by `k`.

### Informal sketch
The proof proceeds as follows:
- Introduce the universal quantifier for `n`.
- Apply `FACT_PSI_BOUND_EVEN` with specialization `n:num` and `2`.
- Apply `FACT_PSI_BOUND_ODD` with specialization `n:num` and `3`.
- Rewrite using arithmetic rules.
- Perform a conversion using `REAL_SUM_CONV` at depth.
- Rewrite using arithmetic rules, `REAL_ADD_LID`, and `DIV_1`.
- Rewrite using `REAL_POW_NEG`, arithmetic rules, `REAL_POW_ONE`, and `REAL_MUL_LID`.
- Use real arithmetic to complete the proof and discharge the goal.

### Mathematical insight
This theorem provides bounds on the difference of the Chebyshev function `psi(n)` at `n` and `n/2` in terms of the logarithm of factorials. Furthermore, logarithmic factorial expressions are also bounded by `psi(n) - psi(n DIV 2) + psi(n DIV 3)`. This is useful in estimating the growth of `psi(n)`. Intuitively, it relates a sum over primes to a product over all positive integers up to `n`.

### Dependencies
- `FACT_PSI_BOUND_EVEN`
- `FACT_PSI_BOUND_ODD`
- `ARITH`
- `REAL_SUM_CONV`
- `REAL_ADD_LID`
- `DIV_1`
- `REAL_POW_NEG`
- `REAL_POW_ONE`
- `REAL_MUL_LID`
- `REAL_ARITH_TAC`


---

## PSI_DOUBLE_LEMMA

### Name of formal statement
PSI_DOUBLE_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PSI_DOUBLE_LEMMA = prove
 (`!n. n >= 1200 ==> &n / &6 <= psi(n) - psi(n DIV 2)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `n:num` FACT_PSI_BOUND_2_3) THEN
  MATCH_MP_TAC(REAL_ARITH
   `b + p3 <= a ==> u <= v /\ a <= p - p2 + p3 ==> b <= p - p2`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&n / &6 + &n / &2` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LE_LADD] THEN MP_TAC(SPEC `n DIV 3` PSI_UBOUND_3_2) THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 / &2 * &n / &3` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
      MP_TAC(SPECL [`n:num`; `3`] DIVISION) THEN ARITH_TAC;
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(SPEC `n:num` LN_FACT_DIFF_BOUNDS) THEN
  MATCH_MP_TAC(REAL_ARITH
   `ltm <= nl2 - a ==> abs(lf - nl2) <= ltm ==> a <= lf`) THEN
  ASM_SIMP_TAC[ARITH_RULE `n >= 1200 ==> ~(n = 0)`] THEN
  REWRITE_TAC[real_div; GSYM REAL_SUB_LDISTRIB; GSYM REAL_ADD_LDISTRIB] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&n * &1 / &38` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    SIMP_TAC[REAL_LE_SUB_LADD] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    CONV_TAC(RAND_CONV LN_N2_CONV) THEN CONV_TAC REALCALC_REL_CONV] THEN
  SUBST1_TAC(REAL_ARITH `&n = &1 + (&n - &1)`) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
   `n >= b ==> b <= n:num`)) THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_OF_NUM_LE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `a <= n ==> a - &1 <= n - &1`)) THEN
  ABBREV_TAC `x = &n - &1` THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV) THEN
  SPEC_TAC(`x:real`,`x:real`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  MATCH_MP_TAC OVERPOWER_LEMMA THEN
  W(fun (asl,w) ->
      let th = DIFF_CONV
       (lhand(rator(rand(body(rand(lhand(rand(body(rand w))))))))) in
      MP_TAC th) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [REAL_MUL_LZERO; REAL_ADD_LID; REAL_ADD_RID;
    REAL_MUL_RID; REAL_MUL_LID] THEN
  W(fun (asl,w) ->
      let tm = mk_abs(`x:real`,rand(rator(rand(body(rand(lhand w)))))) in
      DISCH_TAC THEN EXISTS_TAC tm) THEN
  CONJ_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[real_sub] THEN
    CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN
    CONV_TAC REALCALC_REL_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN
    DISCH_THEN(fun th -> FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN REWRITE_TAC[REAL_SUB_LE] THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `a <= x ==> inv(&1 + x) <= inv(&1 + a) /\
               inv(&1 + a) <= b ==> inv(&1 + x) <= b`)) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;
```

### Informal statement
For all natural numbers `n`, if `n` is greater than or equal to 1200, then the real number `n/6` is less than or equal to `psi(n) - psi(n/2)`.

### Informal sketch
The proof proceeds as follows:
- Start with the assumption `n >= 1200`.
- Use `FACT_PSI_BOUND_2_3` to establish an initial bound on `psi(n)`.
- Manipulate inequalities to show that `psi(n) - psi(n/2)` is bounded below by `n/6`.
- Use `PSI_UBOUND_3_2` to obtain an upper bound for `psi(n/3)`.
- Apply difference bounds `LN_FACT_DIFF_BOUNDS` on logarithmic factorial functions.
- Perform arithmetic and algebraic manipulations to relate `ln(n!)` and `ln((n/2)!)`.
- Reduce and simplify the inequality to derive the desired result.
- Finally show the result using real arithmetic tactics.

### Mathematical insight
This theorem provides a lower bound for the difference between the prime-counting function `psi(n)` evaluated at `n` and `n/2`, specifically, `psi(n) - psi(n/2) >= n/6` for `n >= 1200`. This is likely used in the context of analytic number theory to estimate the growth rate or distribution of prime numbers.

### Dependencies
- Theorems: `REAL_ARITH`, `REAL_LE_TRANS`, `REAL_LE_LADD`, `REAL_LE_LMUL`, `REAL_LE_RDIV_EQ`, `REAL_OF_NUM_LT`, `ARITH`, `REAL_OF_NUM_MUL`, `REAL_OF_NUM_LE`, `REAL_MUL_SYM`, `REAL_MUL_ASSOC`, `REAL_LE_REFL`, `REAL_POS`, `REAL_LE_SUB_LADD`, `REAL_SUB_LDISTRIB`, `REAL_ADD_LDISTRIB`, `REAL_SUB_LE`, `REAL_LT_DIV`, `REAL_LE_INV2`
- Definitions: `psi`, `DIVISION`, `LN_N2_CONV`, `REALCALC_REL_CONV`, `REAL_RAT_REDUCE_CONV`, `real_div`, `real_sub`
- Facts: `FACT_PSI_BOUND_2_3`, `PSI_UBOUND_3_2`, `LN_FACT_DIFF_BOUNDS`, `OVERPOWER_LEMMA`
- Rules: `ARITH_RULE`


---

## THETA_DOUBLE_LEMMA

### Name of formal statement
THETA_DOUBLE_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let THETA_DOUBLE_LEMMA = prove
 (`!n. n >= 1200 ==> theta(n DIV 2) < theta(n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(CONJUNCT2 (SPEC `n:num` PSI_THETA)) THEN
  MP_TAC(CONJUNCT1 (SPEC `n DIV 2` PSI_THETA)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PSI_DOUBLE_LEMMA) THEN
  MP_TAC(SPEC `ISQRT(n DIV 2)` PSI_POS) THEN
  SUBGOAL_THEN
   `&2 * psi (ISQRT n) < &n / &6`
   (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&3 / &2 * &(ISQRT n)` THEN
  REWRITE_TAC[PSI_UBOUND_3_2] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN
  SIMP_TAC[GSYM real_div; REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT] THEN
  SUBGOAL_THEN `(ISQRT n * 18) EXP (SUC 1) < n EXP (SUC 1)` MP_TAC THENL
   [ALL_TAC; REWRITE_TAC[EXP_MONO_LT; NOT_SUC]] THEN
  REWRITE_TAC[EXP; EXP_1] THEN
  MATCH_MP_TAC(ARITH_RULE `324 * i * i < a ==> (i * 18) * (i * 18) < a`) THEN
  MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `324 * n` THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM EXP_2; ISQRT_WORKS; LE_MULT_LCANCEL];
    REWRITE_TAC[LT_MULT_RCANCEL] THEN POP_ASSUM MP_TAC THEN ARITH_TAC]);;
```

### Informal statement
For all natural numbers `n`, if `n` is greater than or equal to 1200 then `theta(n DIV 2)` is less than `theta(n)`.

### Informal sketch
The proof demonstrates that for sufficiently large `n`, the `theta` function decreases when its argument is halved.

- Start by stripping the goal and using `PSI_THETA` which gives bounds on `theta(n)` in terms of `psi(sqrt(n))`.
- Instantiate `PSI_THETA` for `n` and `n DIV 2` and use `PSI_DOUBLE_LEMMA` which relates `psi(sqrt(n))` and `psi(sqrt(n DIV 2))`.
- This reduces the goal to showing that `2 * psi(sqrt(n)) < n/6`.
- Use `PSI_POS` to show that `ISQRT(n DIV 2)` is positive, and introduce the subgoal `&2 * psi (ISQRT n) < &n / &6`.
- The proof proceeds by bounding `psi(sqrt(n))` using `PSI_UBOUND_3_2` stating that `psi(n) <= 3/2 * n`.
- The goal is then reduced to proving `(ISQRT n * 18) EXP (SUC 1) < n EXP (SUC 1)`
- The goal is simplified by `EXP_MONO_LT`, `EXP`, and `EXP_1`.
- Finally, this inequality is shown using arithmetic reasoning.

### Mathematical insight
This lemma shows that the `theta` function, which sums the logarithms of primes less than or equal to a given number, increases less than linearly. Specifically, it increases by a smaller factor when the input is doubled, showing a degree of sub-linearity in its growth. Proving this lemma contributes to establishing that the Chebyshev `theta` function changes (increases) sufficiently fast.

### Dependencies
- `PSI_THETA`
- `PSI_DOUBLE_LEMMA`
- `PSI_POS`
- `PSI_UBOUND_3_2`
- `EXP_MONO_LT`
- `EXP`
- `EXP_1`
- `EXP_2`
- `ISQRT_WORKS`
- `LE_MULT_LCANCEL`
- `LT_MULT_RCANCEL`
- `REAL_MUL_SYM`
- `GSYM REAL_LT_RDIV_EQ`
- `REAL_OF_NUM_LT`
- `real_div`
- `GSYM REAL_MUL_ASSOC`
- `REAL_LET_TRANS`
- `REAL_LT_DIV`
- `REAL_RAT_REDUCE_CONV`
- `REAL_MUL_LID`
- `GSYM real_div`
- `REAL_OF_NUM_MUL`

### Porting notes (optional)
- The `REAL_ARITH_TAC` tactic might need to be replaced with a more granular set of tactics, or a more powerful arithmetic decision procedure, depending on the target proof assistant.
- The handling of real number arithmetic and the instantiation of generic theorems about reals might require adjustments depending on how the target system handles reals.
- The tactics `REPEAT STRIP_TAC`, `MP_TAC`, `FIRST_ASSUM`, `ONCE_REWRITE_TAC`, `SIMP_TAC`, `REWRITE_TAC`, `MATCH_MP_TAC`, `EXISTS_TAC, `GEN_REWRITE_TAC`, `CONV_TAC`, `SUBGOAL_THEN`, `ALL_TAC`, `CONJ_TAC, `POP_ASSUM` and `ARITH_TAC` need equivalent tactics or tactic combinations in the target proof assistant. Some of these, like `ARITH_TAC`, are quite powerful and may require significant effort to replace.


---

## BIG_BERTRAND

### Name of formal statement
BIG_BERTRAND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BIG_BERTRAND = prove
 (`!n. n >= 2400 ==> ?p. prime(p) /\ n <= p /\ p <= 2 * n`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `2 * n` THETA_DOUBLE_LEMMA) THEN
  ANTS_TAC THENL [POP_ASSUM MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(a /\ b /\ c) <=> b /\ c ==> ~a`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `sum(n + 1,n) (\p. if prime p then ln (&p) else &0) = &0`
  MP_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `sum(n + 1,n) (\r. &0)` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[SUM_0]] THEN
    MATCH_MP_TAC SUM_EQ THEN
    ASM_SIMP_TAC[ARITH_RULE
     `n + 1 <= r /\ r < n + n + 1 ==> n <= r /\ r <= 2 * n`];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(b + a = c) ==> (a = &0) ==> ~(b < c)`) THEN
  REWRITE_TAC[theta] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[SUM_SPLIT] THEN
  REWRITE_TAC[MULT_2]);;
```
### Informal statement
For all natural numbers `n`, if `n` is greater than or equal to 2400, then there exists a prime number `p` such that `n` is less than or equal to `p` and `p` is less than or equal to `2 * n`.

### Informal sketch
The proof proceeds as follows:
- Start by stripping the goal.
- Apply a theorem about doubling a value (`THETA_DOUBLE_LEMMA`).
- Perform arithmetic simplification

The main steps are:
- Assume the antecedent `n >= 2400`.
- Reduce the goal to showing that for some prime `p` we have `n <= p <= 2n`.
- Introduce a contradiction argument showing no such primes can occur
- Negate the goal using `CONTRAPOS_THM` and `NOT_EXISTS_THM` to convert it into an inequality about a sum over primes.
- Show that the sum can be rewritten `sum(n + 1, n) (\p. if prime p then ln (&p) else &0) = &0`.
- Use `EQ_TRANS` and `SUM_0` to show that the sum equals `&0`.
- Employ `REAL_ARITH` to show that `~(b < c)`.
- Simplify using `theta`, `ADD_SYM`, `SUM_SPLIT`, and `MULT_2`.

### Mathematical insight
This theorem proves Bertrand's postulate for sufficiently large `n` (specifically, `n >= 2400`). Bertrand's Postulate states that for any integer `n > 1`, there exists a prime number `p` such that `n < p < 2n`. This theorem establishes a lower bound on `n` for which the postulate holds.

### Dependencies
- `DIV_MULT`
- `ARITH_EQ`
- `CONTRAPOS_THM`
- `NOT_EXISTS_THM`
- `SUM_0`
- `SUM_EQ`
- `REAL_ARITH`
- `theta`
- `ADD_SYM`
- `SUM_SPLIT`
- `MULT_2`
- `THETA_DOUBLE_LEMMA`


---

## LANDAU_TRICK

### Name of formal statement
LANDAU_TRICK

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LANDAU_TRICK = prove
 (`!n. 0 < n /\ n < 2400
       ==> n <= 2 /\ 2 <= 2 * n \/
           n <= 3 /\ 3 <= 2 * n \/
           n <= 5 /\ 5 <= 2 * n \/
           n <= 7 /\ 7 <= 2 * n \/
           n <= 13 /\ 13 <= 2 * n \/
           n <= 23 /\ 23 <= 2 * n \/
           n <= 43 /\ 43 <= 2 * n \/
           n <= 83 /\ 83 <= 2 * n \/
           n <= 163 /\ 163 <= 2 * n \/
           n <= 317 /\ 317 <= 2 * n \/
           n <= 631 /\ 631 <= 2 * n \/
           n <= 1259 /\ 1259 <= 2 * n \/
           n <= 2503 /\ 2503 <= 2 * n`,
  let lemma = TAUT
   `(p /\ b1 ==> a1) /\ (~b1 ==> a2) ==> p ==> b1 /\ a1 \/ a2` in
  GEN_TAC THEN ONCE_REWRITE_TAC[TAUT `a /\ b ==> c <=> a ==> c \/ ~b`] THEN
  REWRITE_TAC[GSYM DISJ_ASSOC] THEN
  REPEAT(MATCH_MP_TAC lemma THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC]) THEN
  ARITH_TAC);;
```

### Informal statement
For all `n`, if `n` is greater than 0 and less than 2400, then at least one of the following conditions holds:
- `n` is less than or equal to 2 and 2 is less than or equal to 2 times `n`, or
- `n` is less than or equal to 3 and 3 is less than or equal to 2 times `n`, or
- `n` is less than or equal to 5 and 5 is less than or equal to 2 times `n`, or
- `n` is less than or equal to 7 and 7 is less than or equal to 2 times `n`, or
- `n` is less than or equal to 13 and 13 is less than or equal to 2 times `n`, or
- `n` is less than or equal to 23 and 23 is less than or equal to 2 times `n`, or
- `n` is less than or equal to 43 and 43 is less than or equal to 2 times `n`, or
- `n` is less than or equal to 83 and 83 is less than or equal to 2 times `n`, or
- `n` is less than or equal to 163 and 163 is less than or equal to 2 times `n`, or
- `n` is less than or equal to 317 and 317 is less than or equal to 2 times `n`, or
- `n` is less than or equal to 631 and 631 is less than or equal to 2 times `n`, or
- `n` is less than or equal to 1259 and 1259 is less than or equal to 2 times `n`, or
- `n` is less than or equal to 2503 and 2503 is less than or equal to 2 times `n`.

### Informal sketch
The proof proceeds by the following steps:

- Introduce the universally quantified variable `n` using `GEN_TAC`.
- Rewrite the implication `a /\ b ==> c` to `a ==> c \/ ~b`.
- Use associativity of disjunction (`DISJ_ASSOC`).
- Apply a lemma equivalent to `(p /\ b1 ==> a1) /\ (~b1 ==> a2) ==> p ==> b1 /\ a1 \/ a2` repeatedly. This splits the proof into cases depending on whether `n` satisfies `n <= k` where `k` ranges over the list `[2, 3, 5, 7, 13, 23, 43, 83, 163, 317, 631, 1259]`.
- Each case is then split further to prove `n <= k` and `k <= 2 * n`, using `CONJ_TAC`.
- The first goal obtained after `CONJ_TAC` is solved using `ARITH_TAC` and the second goal is solved by `ALL_TAC` within `CONJ_TAC`. `ALL_TAC` handles the second goal successfully as it arises from the lemma in which the implication `~b1 ==> a2` has been performed, making the second subgoal of the form `p ==> True`
- Finally, `ARITH_TAC` is used to discharge the top-level arithmetic goal.

### Mathematical insight
The theorem essentially provides a hand-crafted disjunctive normal form specifically tailored to the range [1, 2400). The selection of integers `k` is such that for any n within the defined range, at least one of the conditions is satisfied. This is a specific instance of a general technique to decompose a proof by cases over a set of intervals. The `LANDAU_TRICK` name hints that it might be an instance of specific technique, potentially related to inequalities.

### Dependencies
- `TAUT`
- `DISJ_ASSOC`
- `ARITH_TAC`

### Porting notes (optional)
The main challenge in porting this theorem is replicating the arithmetic reasoning and the case splitting strategy. Modern proof assistants like Lean or Coq have powerful automation tactics for linear arithmetic that may make this proof more concise.
The `TAUT` tactic might need to be replicated by specific tautology checker or a rewriting using basic logical equivalences.
The `lemma` application can be done within the automation, or by manually applying the lemma and rewriting.


---

## BERTRAND

### Name of formal statement
BERTRAND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BERTRAND = prove
 (`!n. ~(n = 0) ==> ?p. prime p /\ n <= p /\ p <= 2 * n`,
  REPEAT STRIP_TAC THEN
  DISJ_CASES_TAC(ARITH_RULE `n >= 2400 \/ n < 2400`) THEN
  ASM_SIMP_TAC[BIG_BERTRAND] THEN MP_TAC(SPEC `n:num` LANDAU_TRICK) THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
  STRIP_TAC THEN
  ASM_MESON_TAC(map (PRIME_CONV o curry mk_comb `prime` o mk_small_numeral)
                    [2;3;5;7;13;23;43;83;163;317;631;1259;2503]));;
```
### Informal statement
For all natural numbers `n`, if `n` is not equal to 0, then there exists a prime number `p` such that `n` is less than or equal to `p` and `p` is less than or equal to `2 * n`.

### Informal sketch
The proof proceeds as follows:
- Case split on whether `n >= 2400` or `n < 2400`.
- If `n >= 2400`, apply the theorem `BIG_BERTRAND`.
- Apply a "Landau trick", which appears to involve specialization of some theorem involved in bounding `n`.
- Simplify the condition `0 < n` to `~(n = 0)`.
- Prove the case `n < 2400` by explicitly exhibiting a suitable prime `p` for each `n` in that range. This appears to be done by checking the primes 2, 3, 5, 7, 13, 23, 43, 83, 163, 317, 631, 1259, 2503.

### Mathematical insight
This theorem is Bertrand's Postulate, which states that for every integer `n > 0`, there is always a prime number `p` such that `n <= p < 2n`. The theorem is proven by combining a result for larger `n` (greater or equal to 2400) with an explicit check for small values of `n`. The "Landau trick" likely refers to some number-theoretical inequality that allows bounding `n` in relation to these prime numbers.

### Dependencies
- Theorems: `BIG_BERTRAND`
- Definitions: `prime`

### Porting notes (optional)
The main challenge in porting this theorem lies in finding or proving an equivalent of `BIG_BERTRAND` and the "Landau trick" within the target proof assistant's library. The explicit check for small `n` values with a finite enumeration of primes should be straightforward to implement in most systems. Be mindful of how primality is defined (`prime`).


---

## pii

### Name of formal statement
pii

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let pii = new_definition
  `pii(n) = sum(1,n) (\p. if prime(p) then &1 else &0)`;;
```

### Informal statement
The function `pii(n)` is defined as the sum from 1 to `n` of the function that maps `p` to 1 if `p` is a prime number, and to 0 otherwise.

### Informal sketch
The definition of `pii(n)` explicitly constructs a function that counts the number of primes less than or equal to `n`.
- The function `sum(1,n) f` denotes the summation of `f(i)` where `i` ranges from `1` to `n`.
- The lambda abstraction `\p. if prime(p) then &1 else &0` defines a function that takes a number `p` as input. If `p` is a prime number (as determined by the predicate `prime(p)`), the function returns 1; otherwise, it returns 0.
- Consequently, `pii(n)` sums up the values of this function for all numbers from 1 to `n`, effectively counting the number of prime numbers in the range `[1, n]`.

### Mathematical insight
The function `pii(n)` is a standard notation in number theory, representing the prime-counting function, which gives the number of primes less than or equal to `n`. This definition provides a formal way to express and reason about this function within HOL Light. The comment associated with this definition indicates that it will be used in a weak form of the Prime Number Theorem.

### Dependencies
- `prime`
- `sum`


---

## PII_LIST

### Name of formal statement
PII_LIST

### Type of the formal statement
Definition

### Formal Content
```ocaml
let PII_LIST =
  let PII_0 = prove
   (`pii(0) = &0`,
    REWRITE_TAC[pii; sum])
  and PII_SUC = prove
   (`pii(SUC n) = pii(n) + (if prime(SUC n) then &1 else &0)`,
    REWRITE_TAC[pii; sum; ADD1] THEN REWRITE_TAC[ADD_AC])
  and n_tm = `n:num`
  and SIMPER_CONV =
    NUM_REDUCE_CONV THENC
    ONCE_DEPTH_CONV PRIME_CONV THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV [COND_CLAUSES] THENC
    REAL_RAT_REDUCE_CONV in
  let rec PII_LIST n =
    if n = 0 then [PII_0] else
    let ths = PII_LIST (n - 1) in
    let th1 = INST [mk_small_numeral(n-1),n_tm] PII_SUC in
    let th2 = GEN_REWRITE_RULE (RAND_CONV o LAND_CONV) [hd ths] th1 in
    CONV_RULE SIMPER_CONV th2::ths in
  PII_LIST;;
```

### Informal statement
The function `PII_LIST` takes a natural number `n` as input and returns a list of theorems. The `i`-th theorem in the list (where `i` ranges from 0 to `n`) asserts that `pii(i)` is equal to the numerical value of the number of primes less than or equal to `i`.
`pii(0)` is equal to 0. For any natural number `n`, `pii(SUC n)` is equal to `pii(n)` plus 1 if `SUC n` is a prime number, and `pii(n)` otherwise.

### Informal sketch
The definition of `PII_LIST` proceeds as follows:

- First, the base case `PII_0` proves that `pii(0) = 0` using rewriting with the definitions of `pii` and `sum`.
- Then, the inductive step `PII_SUC` proves that `pii(SUC n) = pii(n) + (if prime(SUC n) then 1 else 0)`. This is done by rewriting with the definitions of `pii`, `sum`, `ADD1`, and `ADD_AC` (commutativity and associativity of addition).
- `SIMPER_CONV` defines a simplification conversion based on numerical reduction, primality checking, conditional rewriting, and real/rational reduction.
- The recursive function `PII_LIST` is defined as follows:
    - Base case: If `n = 0`, return the list containing only theorem `PII_0`.
    - Inductive case:
        - Recursively compute `PII_LIST (n - 1)` to get a list of theorems `ths`.
        - Instantiate the theorem `PII_SUC` with `n-1` to obtain a theorem `th1` about `pii(n)`.
        - Combine the head of the list `ths` (which claims `pii(n-1) = ...`) with the instantiated `PII_SUC` theorem `th1` (stating `pii(n) = pii(n-1) + ...`) using `GEN_REWRITE_RULE` to deduce a concrete value for `pii(n)`. This step uses a conversion that applies rewrites to both sides of the equality, using `RAND_CONV o LAND_CONV` to target the right-hand side of the head of `ths` composed with the left-hand side of `PII_SUC`.
        - Apply `SIMPER_CONV` to the resulting theorem `th2` to simplify it.
        - Prepend `th2` to the list `ths` and return the result.

### Mathematical insight
This definition provides a way to compute a list of theorems that explicitly state the value of the prime-counting function `pii(n)` for all `n` up to a given limit. This is an optimized version where intermediate results are simplified and stored, such all values pii(0), pii(1), ... , pii(n) are available in theorem form. The `SIMPER_CONV` performs simplifications to directly reduce expressions, avoiding unnecessary complexity in the theorems.

### Dependencies
**Theorems/Definitions:**
- `pii`
- `sum`
- `ADD1`
- `ADD_AC`
- `prime`
- `COND_CLAUSES`

### Porting notes (optional)
- The tactics used in HOL Light are not directly portable, but the logical steps they perform should be easy to replicate in other proof assistants. The main difficulty will be to implement the simplification conversion `SIMPER_CONV`.
- The use of `GEN_REWRITE_RULE` to combine previous theorems may need adaptation depending on how rewriting is implemented in the target proof assistant. The important aspect is to rewrite using both sides of the equalities involved.


---

## PRIMES_FINITE

### Name of formal statement
PRIMES_FINITE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PRIMES_FINITE = prove
 (`!n. FINITE {p | p <= n /\ prime(p)}`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{p | p < SUC n}` THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ARITH_TAC);;
```

### Informal statement
For all natural numbers *n*, the set of prime numbers less than or equal to *n* is finite.

### Informal sketch
The proof proceeds as follows:
- Introduce a goal stating that the set of primes less than or equal to `n` is finite.
- Apply `FINITE_SUBSET`, reducing the goal to show that a superset is finite
- Show that the set `{p | p <= n /\ prime(p)}` is a subset of `{p | p < SUC n}`. Further, it suffices to show that `{p | p < SUC n}` is finite.
- Rewrite using `FINITE_NUMSEG_LT` expressing that the set of numbers less than successor `n` is finite.
- Rewrite using `SUBSET` and `IN_ELIM_THM` to eliminate the set comprehension notation.
- Apply `ARITH_TAC` to complete the proof.

### Mathematical insight
The theorem `PRIMES_FINITE` establishes a fundamental property of prime numbers: that the number of primes less than or equal to any given number is finite. This result is a stepping stone toward proving the infinitude of primes, which is a cornerstone of number theory.

### Dependencies
- `FINITE_SUBSET`: States that a subset of a finite set is finite.
- `FINITE_NUMSEG_LT`: States that the set of natural numbers less than n is finite.
- `SUBSET`: Defines the subset relation.
- `IN_ELIM_THM`: Theorem for eliminating the element-of relation.


---

## PII

### Name of formal statement
PII

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PII = prove
 (`!n. pii(n) = &(CARD {p | p <= n /\ prime(p)})`,
  INDUCT_TAC THENL
   [SUBGOAL_THEN `{p | p <= 0 /\ prime p} = {}`
     (fun th -> REWRITE_TAC(th::CARD_CLAUSES::PII_LIST 0)) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    MESON_TAC[LE; PRIME_0; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `{p | p <= SUC n /\ prime p} =
                if prime(SUC n) then (SUC n) INSERT {p | p <= n /\ prime p}
                else {p | p <= n /\ prime p}`
  SUBST1_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN
    ASM_MESON_TAC[LE];
    ALL_TAC] THEN
  REWRITE_TAC[pii; sum] THEN REWRITE_TAC[GSYM pii] THEN
  REWRITE_TAC[ARITH_RULE `1 + n = SUC n`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_ADD_RID] THEN
  SIMP_TAC[CARD_CLAUSES; PRIMES_FINITE] THEN COND_CASES_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN
    ASM_MESON_TAC[ARITH_RULE `~(SUC n <= n)`];
    REWRITE_TAC[REAL_OF_NUM_SUC]]);;
```

### Informal statement
For all natural numbers `n`, `pii(n)` is equal to the real number representation of the cardinality of the set of all primes `p` such that `p` is less than or equal to `n`.

### Informal sketch
The proof proceeds by induction on `n`.
- Base case: `n = 0`. Show that the set of primes less than or equal to 0 is empty. Compute the cardinality of the empty set and then convert it to real number representation.
- Inductive step: Assume that `pii(n)` equals the real number representation of the cardinality of the set of all primes `p` such that `p` is less than or equal to `n`. Show that `pii(SUC n)` equals the real number representation of the cardinality of the set of all primes `p` such that `p` is less than or equal to `SUC n`. The set `{p | p <= SUC n /\ prime p}` is equal to the conditional expression: if `SUC n` is prime, then it is `(SUC n) INSERT {p | p <= n /\ prime p}`, otherwise it is `{p | p <= n /\ prime p}`. The `pii` function is then unfolded and simplified based on whether `SUC n` is prime.

### Mathematical insight
This theorem formally defines the prime-counting function `pii(n)` within HOL Light. It establishes that `pii(n)` correctly counts the number of primes less than or equal to `n` and represents this count as a real number. This theorem is a fundamental result in number theory and serves as a basis for further analysis and manipulation of prime numbers within the formal system.

### Dependencies
- Definitions: `pii`, `prime`
- Theorems: `EXTENSION`, `IN_ELIM_THM`, `LE`, `PRIME_0`, `NOT_IN_EMPTY`, `IN_INSERT`, `CARD_CLAUSES`, `PRIMES_FINITE`, `REAL_ADD_RID`, `REAL_OF_NUM_SUC`
- Rules: `ARITH_RULE`


---

## PII_LBOUND

### Name of formal statement
PII_LBOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PII_LBOUND = prove
 (`!n. 3 <= n ==> &1 / &2 * (&n / ln(&n)) <= pii(n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; LN_POS_LT; REAL_OF_NUM_LT;
               ARITH_RULE `3 <= n ==> 1 < n`] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o MATCH_MP
   (ARITH_RULE `3 <= n ==> (n = 3) \/ (n = 4) \/ 5 <= n`)) THEN
  ASM_REWRITE_TAC(PII_LIST 4) THENL
   [CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN CONV_TAC REALCALC_REL_CONV;
    CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN CONV_TAC REALCALC_REL_CONV;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP THETA_LBOUND_1_2) THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> a <= x ==> a <= y`) THEN
  REWRITE_TAC[theta; pii; GSYM SUM_CMUL] THEN
  MATCH_MP_TAC SUM_LE THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; REAL_LE_REFL] THEN
  SUBGOAL_THEN `&0 < &r /\ &r <= &n`
   (fun th -> MESON_TAC[th; LN_MONO_LE; REAL_LTE_TRANS]) THEN
  REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
  UNDISCH_TAC `1 <= r` THEN UNDISCH_TAC `r < n + 1` THEN ARITH_TAC);;
```

### Informal statement
For every natural number `n`, if `3 <= n`, then `1 / 2 * (n / ln(n)) <= pii(n)`, where `pii(n)` is the prime-counting function.

### Informal sketch
The proof establishes a lower bound for the prime-counting function `pii(n)`. The proof proceeds by:

- Stripping the goal and rewriting with `real_div` and `REAL_MUL_ASSOC`.
- Simplifying using arithmetic rules related to real division, inequalities, and the logarithm function.
- Handling the base cases `n = 3` and `n = 4` by complete instantiation, using the precomputed values in the list `PII_LIST 4`.
- Applying a separate lower bound theorem for `theta`, named `THETA_LBOUND_1_2`, where `theta(x)` is the Chebyshev function.
- Rewriting using definitions of `theta` and `pii` along with `SUM_CMUL`.
- Applying a lemma related to the sum that is less than or equal given by `SUM_LE`.
- Performing induction on `r` with the assumption `&0 < &r /\ &r <= &n`.
- Applying `LN_MONO_LE` monotone inequality on the natural logarithm and `REAL_LTE_TRANS` transitivity for real less than or equal.

### Mathematical insight
This theorem provides a concrete lower bound for the prime-counting function, `pii(n)`, using the elementary function `n / ln(n)`. This result is a step towards the Prime Number Theorem, which gives an asymptotic estimate for `pii(n)`.

### Dependencies
- `real_div`
- `REAL_MUL_ASSOC`
- `GSYM real_div`
- `REAL_LE_LDIV_EQ`
- `LN_POS_LT`
- `REAL_OF_NUM_LT`
- `ARITH_RULE (3 <= n ==> 1 < n)`
- `REAL_MUL_SYM`
- `ARITH_RULE (3 <= n ==> (n = 3) \/ (n = 4) \/ 5 <= n)`
- `PII_LIST`
- `LN_N2_CONV`
- `REALCALC_REL_CONV`
- `THETA_LBOUND_1_2`
- `REAL_ARITH (x <= y ==> a <= x ==> a <= y)`
- `theta`
- `pii`
- `GSYM SUM_CMUL`
- `SUM_LE`
- `REAL_MUL_RZERO`
- `REAL_MUL_RID`
- `REAL_LE_REFL`
- `LN_MONO_LE`
- `REAL_LTE_TRANS`
- `REAL_OF_NUM_LT`
- `REAL_OF_NUM_LE`


---

## PII_UBOUND_CASES_50

### Name of formal statement
PII_UBOUND_CASES_50

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PII_UBOUND_CASES_50 = prove
 (`!n. n < 50 ==> 3 <= n ==> ln(&n) * pii(n) <= &5 * &n`,
  let tac = CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV THENC REALCALC_REL_CONV) in
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC(PII_LIST 49) THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REPEAT(CONJ_TAC THENL [tac THEN NO_TAC; ALL_TAC]) THEN tac);;
```

### Informal statement
For all natural numbers `n`, if `n` is less than 50 and `n` is greater than or equal to 3, then `ln(n) * pii(n)` is less than or equal to `5 * n` (where `ln` is the natural logarithm, `pii(n)` counts the number of primes less than or equal to `n`, and all numbers are represented as real numbers).

### Informal sketch
The proof proceeds by:
- Expanding cases using `EXPAND_CASES_CONV`.
- Applying simplifications using `NUM_REDUCE_CONV` and `REAL_RAT_REDUCE_CONV`.
- Rewriting the goal by expanding `pii(n)` for `n` up to 49 using the theorem `PII_LIST 49`.
- Simplifying using real number arithmetic simplification, rewriting with `REAL_LE_RDIV_EQ` and `REAL_OF_NUM_LT`, and using `ARITH` to discharge some subgoals.
- Further simplifying using `REAL_RAT_REDUCE_CONV`.
- Repeatedly splitting the goal into subgoals using `CONJ_TAC` and solving them by either applying a conversion tactic (`tac`) or the `ALL_TAC`.
- The conversion tactic `tac` uses `LN_N2_CONV`, `REALCALC_REL_CONV`, and `ONCE_DEPTH_CONV` to deal with inequalities involving natural logarithms.

### Mathematical insight
This theorem establishes an upper bound for the product of the natural logarithm of `n` and the prime-counting function `pii(n)` for small values of `n` (3 up to 49). This is a step toward proving a more general upper bound, likely to be used later in a more comprehensive result about prime numbers.

### Dependencies
- `PII_LIST`
- `REAL_LE_RDIV_EQ`
- `REAL_OF_NUM_LT`
- `ARITH`
- `LN_N2_CONV`
- `REALCALC_REL_CONV`


---

## THETA_POS

### Name of formal statement
THETA_POS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let THETA_POS = prove
 (`!n. &0 <= theta n`,
  GEN_TAC THEN REWRITE_TAC[theta] THEN
  MATCH_MP_TAC SUM_POS_GEN THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[LE_REFL; LN_POS; REAL_OF_NUM_LE]);;
```

### Informal statement
For all natural numbers `n`, 0 is less than or equal to `theta n`.

### Informal sketch
The proof proceeds as follows:
- Start with the goal `!n. &0 <= theta n`.
- Expand the definition of `theta` using `REWRITE_TAC[theta]`. The definition of `theta` probably involves a summation.
- Apply `SUM_POS_GEN` which probably states that a sum of positive terms is positive.
- Introduce a variable `p:num` using `X_GEN_TAC` and discharge the assumption using `DISCH_TAC`.
- Perform simplification using `REWRITE_TAC[]`.
- Perform case splitting using `COND_CASES_TAC`.
- Simplify the goal using assumptions and the theorems `LE_REFL`, `LN_POS`, and `REAL_OF_NUM_LE`. In particular, `LE_REFL` likely states that `x <= x` for any `x`, `LN_POS` likely states that the natural logarithm of a positive number is positive, and `REAL_OF_NUM_LE` likely connects the numeral ordering with real number ordering.

### Mathematical insight
This theorem establishes a lower bound for the function `theta`, demonstrating that its value is always non-negative for any natural number input. It's likely used in further analysis or calculations related to `theta`. The proof leverages general properties of sums and logarithms to show that `theta` can never be negative.

### Dependencies
- `theta`
- `SUM_POS_GEN`
- `LE_REFL`
- `LN_POS`
- `REAL_OF_NUM_LE`


---

## PII_MONO

### Name of formal statement
PII_MONO

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PII_MONO = prove
 (`!m n. m <= n ==> pii(m) <= pii(n)`,
  SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM; pii] THEN
  REWRITE_TAC[GSYM SUM_SPLIT] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_ADDR] THEN
  MATCH_MP_TAC SUM_POS_GEN THEN
  GEN_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;
```
### Informal statement
For all real numbers `m` and `n`, if `m` is less than or equal to `n`, then `pii(m)` is less than or equal to `pii(n)`.

### Informal sketch
The proof demonstrates that the function `pii` is monotonically increasing.
- We start with the assumption `m <= n`.
- The goal is to prove `pii(m) <= pii(n)`.
- The proof expands `pii` using its definition, revealing summations.
- We split the summation using `SUM_SPLIT` and rewrite using `REAL_LE_ADDR`.
- We use the fact that a sum of positive numbers is positive `SUM_POS_GEN`.
- We perform conditional case analysis using `COND_CASES_TAC`.
- Finally, we use `REAL_RAT_REDUCE_CONV` to discharge the remaining case.

### Mathematical insight
This theorem establishes the monotonicity of the `pii` function, which seems to be a function that calculates a sum based on its input. Monotonicity is a fundamental property in analysis and is essential for various kinds of reasoning, such as bounding errors in approximations, proving convergence, and comparing the behavior of different functions.

### Dependencies
- Definitions: `pii`
- Theorems: `LE_EXISTS`, `LEFT_IMP_EXISTS_THM`, `GSYM SUM_SPLIT`, `REAL_LE_ADDR`, `SUM_POS_GEN`

### Porting notes (optional)
The proof relies on rewriting and tactic-based manipulation of inequalities and summations. Porting to other systems may involve using similar rewriting techniques or employing SMT solvers if the target system has them. Systems with strong automation for real number inequalities might simplify the porting process. The `COND_CASES_TAC` tactic may need to be replaced with an equivalent case-splitting tactic or by using a more manual approach by explicitly proving each case. The definition of `pii` should be ported first.


---

## PII_POS

### Name of formal statement
PII_POS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PII_POS = prove
 (`!n. &0 <= pii(n)`,
  SUBGOAL_THEN `pii(0) = &0` (fun th -> MESON_TAC[th; PII_MONO; LE_0]) THEN
  REWRITE_TAC(LN_1::PII_LIST 0));;
```
### Informal statement
For all natural numbers `n`, `pii(n)` is greater than or equal to 0.

### Informal sketch
The proof proceeds by first establishing the base case (`pii(0) = &0`). Then use `MESON_TAC` to derive the goal `&0 <= pii(n)` from the base case together with monotonicity (`PII_MONO`) and `LE_0`, which states that 0 is less than or equal to 0. Finally we rewrite using `LN_1` and `PII_LIST 0`.

*   The base case `pii(0) = &0` is handled by rewriting using rewrite rules `LN_1` and `PII_LIST 0`.
*   The general case for all natural numbers is finished by using `MESON_TAC` with the lemma stating `pii` is monotone (`PII_MONO`) and the fact that 0 is less than or equal to 0 (`LE_0`).

### Mathematical insight
This theorem establishes a basic property of the `pii` function, namely that it always returns a non-negative real number for natural number inputs. This is a fundamental requirement for `pii` to be meaningfully interpreted as a length or size.

### Dependencies
*   Theorems: `PII_MONO`, `LE_0`, `LN_1`
*   Definitions: `PII_LIST`


---

## PII_CHANGE

### Name of formal statement
PII_CHANGE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PII_CHANGE = prove
 (`!m n. ~(m = 0) ==> ln(&m) * (pii n - pii m) <= &3 / &2 * &n`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `m <= n:num` THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a * (c - b) ==> a * (b - c) <= &0`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[LN_POS; REAL_OF_NUM_LE; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC PII_MONO THEN
    UNDISCH_TAC `~(m <= n:num)` THEN ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `theta n` THEN REWRITE_TAC[THETA_UBOUND_3_2] THEN
  MP_TAC(SPEC `m:num` THETA_POS) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= n - m ==> &0 <= m ==> a <= n`) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LE_EXISTS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  REWRITE_TAC[pii; theta; GSYM SUM_SPLIT; REAL_ADD_SUB] THEN
  REWRITE_TAC[GSYM SUM_CMUL] THEN
  MATCH_MP_TAC SUM_LE THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_REFL; REAL_MUL_RID] THEN
  SUBGOAL_THEN `&0 < &m /\ &m <= &r`
   (fun th -> MESON_TAC[th; LN_MONO_LE; REAL_LTE_TRANS]) THEN
  REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
  UNDISCH_TAC `1 + m <= r` THEN UNDISCH_TAC `~(m = 0)` THEN ARITH_TAC);;
```

### Informal statement
For all natural numbers `m` and `n`, if `m` is not equal to 0, then `ln(m) * (pii(n) - pii(m))` is less than or equal to `3/2 * n`.

### Informal sketch
The proof proceeds by induction on whether `m` is less than or equal to `n`.
- Case 1: `m <= n`.
  - Show that `ln(m) * (pii(n) - pii(m)) <= 3/2 * n` by using `REAL_LE_TRANS`. Introduce `0` and prove that `ln(m) * (pii(n) - pii(m))` is greater than or equal to `0`, and `0` is less than or equal to `3/2 * n`.
  - To prove `ln(m) * (pii(n) - pii(m)) >= 0`, it is shown that `ln(m) > 0` and `pii(n) - pii(m) >= 0`.
  - To prove `0 <= 3/2 * n`, use `REAL_POS` and `REAL_RAT_REDUCE_CONV`.
- Case 2: `~(m <= n)`.
  - Use `REAL_ARITH` to rewrite `a <= n - m ==> 0 <= m ==> a <= n`. Introduce `d` such that `n - m <= d <= n`. 
  - Then, use `SUM_LE` to prove `ln(m) * (pii(n) - pii(m)) <= 3/2 * n`. `COND_CASES_TAC` splits cases when `r >= m` and `~(r >= m)`.

### Mathematical insight
This theorem provides an upper bound on the difference of the prime-counting function `pii(n)` and `pii(m)` in terms of `n` and the natural logarithm of `m`. The bound is `3/2 * n / ln(m)`, and is useful in estimating the distribution of prime numbers.

### Dependencies
- `LN_POS`
- `REAL_OF_NUM_LE`
- `ARITH_RULE`
- `REAL_SUB_LE`
- `PII_MONO`
- `THETA_UBOUND_3_2`
- `THETA_POS`
- `LE_EXISTS`
- `pii`
- `theta`
- `SUM_SPLIT`
- `SUM_CMUL`
- `SUM_LE`
- `LN_MONO_LE`
- `REAL_LTE_TRANS`
- `REAL_OF_NUM_LT`
- `REAL_OF_NUM_LE`


---

## PII_ISQRT_INDUCT

### Name of formal statement
PII_ISQRT_INDUCT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PII_ISQRT_INDUCT = prove
 (`!n. 50 <= n
       ==> ln(&n) * pii(n)
           <= &9 / &4 * (&3 / &2 * &n + ln(&(ISQRT(n))) * pii(ISQRT(n)))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  GEN_REWRITE_TAC LAND_CONV [real_div] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MP_TAC(SPECL [`ISQRT n`; `n:num`] PII_CHANGE) THEN
  SUBGOAL_THEN `~(ISQRT n = 0)` ASSUME_TAC THENL
   [MP_TAC(SPEC `n:num` ISQRT_WORKS) THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN SIMP_TAC[ARITH] THEN
    DISCH_TAC THEN UNDISCH_TAC `50 <= n` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
   `a * p <= ls * p ==> ls * (p - ps) <= an ==> a * p <= an + ls * ps`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[PII_POS] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `ln((&(ISQRT n) + &1) pow 2)` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `&0 < &n /\ &n <= (&(ISQRT n) + &1) pow 2`
     (fun th -> MESON_TAC[th; REAL_LTE_TRANS; LN_MONO_LE]) THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_POW; REAL_OF_NUM_LE;
                REAL_OF_NUM_LT] THEN
    SIMP_TAC[ISQRT_WORKS; LT_IMP_LE] THEN
    UNDISCH_TAC `50 <= n` THEN ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[LN_POW; REAL_POS; REAL_ARITH `&0 <= x ==> &0 < x + &1`] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC(REAL_ARITH `a - b <= b * (d - &1) ==> a <= b * d`) THEN
  ASM_SIMP_TAC[GSYM LN_DIV; REAL_ARITH `&0 < x ==> &0 < x + &1`;
               REAL_OF_NUM_LT; ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
  REWRITE_TAC[real_div; REAL_ADD_RDISTRIB] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_OF_NUM_EQ; ARITH; REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&(ISQRT n))` THEN
  ASM_SIMP_TAC[LN_LE; REAL_POS; REAL_LE_INV_EQ] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN REWRITE_TAC[GSYM real_div] THEN
  SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT;
               ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
  SUBGOAL_THEN `&7 <= &(ISQRT n)` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `7 EXP 2 < (ISQRT n + 1) EXP 2` MP_TAC THENL
     [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `n:num` THEN
      REWRITE_TAC[ISQRT_WORKS] THEN CONV_TAC NUM_REDUCE_CONV THEN
      UNDISCH_TAC `50 <= n` THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[num_CONV `2`; EXP_MONO_LT; NOT_SUC] THEN ARITH_TAC;
    ALL_TAC] THEN
  SPEC_TAC(`&(ISQRT n)`,`x:real`) THEN
  MATCH_MP_TAC OVERPOWER_LEMMA THEN
  W(fun (asl,w) ->
      let th = DIFF_CONV
       (lhand(rator(rand(body(rand(lhand(rand(body(rand w))))))))) in
      MP_TAC th) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [REAL_MUL_LZERO; REAL_ADD_LID; REAL_ADD_RID;
    REAL_MUL_RID; REAL_MUL_LID] THEN
  SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
  W(fun (asl,w) ->
      let tm = mk_abs(`x:real`,rand(rator(rand(body(rand(lhand w)))))) in
      DISCH_TAC THEN EXISTS_TAC tm) THEN
  CONJ_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[real_sub] THEN
    CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN
    CONV_TAC REALCALC_REL_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN
    DISCH_THEN(fun th -> FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  SIMP_TAC[LN_POS; REAL_LE_ADD; REAL_POS; REAL_ARITH `&7 <= x ==> &1 <= x`]);;
```

### Informal statement
For all natural numbers `n`, if `50 <= n` then `ln(real(n)) * pii(n) <= 9/4 * (3/2 * real(n) + ln(real(ISQRT(n))) * pii(ISQRT(n)))`.

### Informal sketch
The proof proceeds by induction.  The induction hypothesis is that `ln(real(n)) * pii(n) <= 9/4 * (3/2 * real(n) + ln(real(ISQRT(n))) * pii(ISQRT(n)))` holds for all `n >= 50`.
It uses a change of variable `PII_CHANGE` and the fact that  `~(ISQRT n = 0)` when `n >= 50`, which is established using `ISQRT_WORKS` to show that `1 <= ISQRT n` and basic arithmetic.

The proof then uses the following strategy:
- Match `a * p <= ls * p` against the current goal, where `a` corresponds to the left-hand side, `p` to `pii(n)`, and `ls` to some expression.
- Show `ls * (p - ps) <= an`, where `ps` refers to `pii(ISQRT(n))` and `an` to the upper bound we want.
- Conclude by arithmetic that `a * p <= an + ls * ps`.

The lemma `PII_POS` (that `pii(x)` is positive) is used. Several real arithmetic simplification steps are performed using the `REAL_RAT_REDUCE_CONV` conversion and lemmas about `REAL_LE_RDIV_EQ` and `REAL_LT_DIV`.

An intermediate stage requires showing that there exists `ln((&(ISQRT n) + &1) pow 2)` such that some inequalities hold, specifically `&0 < &n /\ &n <= (&(ISQRT n) + &1) pow 2`. This is proven by rewriting with `REAL_OF_NUM_ADD`, `REAL_OF_NUM_POW`, `REAL_OF_NUM_LE`, `REAL_OF_NUM_LT`, simplifying with `ISQRT_WORKS` and `LT_IMP_LE`, and using arithmetic with the assumption `50 <= n`.

Further simplification and rewriting with lemmas such as `LN_POW`, `REAL_POS`, and `REAL_ARITH` are performed. Various real arithmetic rules and conversions are applied, including simplification involving logarithms and division.

It's shown that `&(ISQRT n) >= &7`, which is used in further real number manipulations. This involves several steps that relate `n` and `ISQRT(n)` leading finally to `7 EXP 2 < (ISQRT n + 1) EXP 2` which is verified with prior lemmas and conversions.

Then, `OVERPOWER_LEMMA` is matched and differentiated. Several simplifications with real arithmetic rules are applied (`REAL_MUL_LZERO`, `REAL_ADD_LID`, `REAL_ADD_RID`, `REAL_MUL_RID`, `REAL_MUL_LID`, `REAL_MUL_LINV`, `REAL_LT_IMP_NZ`). An existence proof is performed, followed by more simplification and real calculus. Finally `LN_POS` and other real lemmas are used to reach the conclusion.

### Mathematical insight
This theorem provides an upper bound on the product of the natural logarithm of `n` and `pii(n)`, where `pii(n)` is likely related to the prime-counting function. The bound involves a more complex expression that includes `ISQRT(n)` which represents the integer square root of n. The theorem is useful for estimating the growth rate of `pii(n)`.

### Dependencies
- `REAL_MUL_SYM`
- `GSYM REAL_LE_LDIV_EQ`
- `REAL_LT_DIV`
- `REAL_OF_NUM_LT`
- `ARITH`
- `real_div`
- `REAL_MUL_ASSOC`
- `PII_CHANGE`
- `ISQRT_WORKS`
- `GSYM CONTRAPOS_THM`
- `PII_POS`
- `REAL_LE_RMUL`
- `REAL_RAT_REDUCE_CONV`
- `GSYM REAL_LE_RDIV_EQ`
- `REAL_LE_TRANS`
- `LN_MONO_LE`
- `REAL_OF_NUM_ADD`
- `REAL_OF_NUM_POW`
- `REAL_OF_NUM_LE`
- `LT_IMP_LE`
- `LN_POW`
- `REAL_POS`
- `real_div`
- `GSYM REAL_MUL_ASSOC`
- `GSYM LN_DIV`
- `REAL_ADD_RDISTRIB`
- `REAL_MUL_RINV`
- `REAL_OF_NUM_EQ`
- `REAL_MUL_LID`
- `LN_LE`
- `REAL_LE_INV_EQ`
- `REAL_MUL_LID`
- `GSYM real_div`
- `EXP_MONO_LT`
- `NOT_SUC`
- `OVERPOWER_LEMMA`
- `REAL_MUL_LZERO`
- `REAL_ADD_LID`
- `REAL_ADD_RID`
- `REAL_MUL_RID`
- `REAL_MUL_LID`
- `REAL_MUL_LINV`
- `REAL_LT_IMP_NZ`
- `LN_N2_CONV`
- `REAL_SUB_RZERO`
- `LN_POS`
- `REAL_LE_ADD`

### Porting notes (optional)
- The proof relies heavily on real arithmetic simplification using tactics like `REAL_ARITH_TAC` and conversions like `REAL_RAT_REDUCE_CONV`. Other proof assistants may have different levels of automation for these kinds of tasks.
- Porting will require a well-developed theory of real numbers.
- Special attention may be required to translate `ISQRT`, `pii`, and `ln` functions and their associated properties correctly.


---

## PII_UBOUND_5

### Name of formal statement
PII_UBOUND_5

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PII_UBOUND_5 = prove
 (`!n. 3 <= n ==> pii(n) <= &5 * (&n / ln(&n))`,
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ; LN_POS_LT; REAL_OF_NUM_LT;
           ARITH_RULE `3 <= n ==> 1 < n`] THEN
  GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `n < 50` THEN ASM_SIMP_TAC[PII_UBOUND_CASES_50] THEN
  DISCH_THEN(MP_TAC o SPEC `ISQRT n`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
  SUBGOAL_THEN `7 <= ISQRT n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `7 EXP 2 < (ISQRT n + 1) EXP 2` MP_TAC THENL
     [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `n:num` THEN
      REWRITE_TAC[ISQRT_WORKS] THEN CONV_TAC NUM_REDUCE_CONV THEN
      UNDISCH_TAC `50 <= n` THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[num_CONV `2`; EXP_MONO_LT; NOT_SUC] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `7 <= n ==> 3 <= n`;
               ARITH_RULE `50 <= n ==> 3 <= n`] THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `(ISQRT n) EXP 2 < n EXP 2` MP_TAC THENL
     [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `n:num` THEN
      REWRITE_TAC[ISQRT_WORKS] THEN REWRITE_TAC[EXP_2] THEN
      MATCH_MP_TAC(ARITH_RULE `1 * n < m ==> n < m`) THEN
      REWRITE_TAC[LT_MULT_RCANCEL] THEN
      UNDISCH_TAC `50 <= n` THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[num_CONV `2`; EXP_MONO_LT; NOT_SUC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PII_ISQRT_INDUCT) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&9 / &4 * (&3 / &2 * &n + &5 * &(ISQRT n))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[REAL_LE_LADD];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `i * (a * c) <= n * (d - a * b) ==> a * (b * n + c * i) <= d * n`) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(ISQRT n) * &7` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `ISQRT n * ISQRT n` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[LE_MULT_LCANCEL];
    REWRITE_TAC[GSYM EXP_2; ISQRT_WORKS]]);;
```

### Informal statement
For all natural numbers `n`, if `3 <= n`, then `pii(n) <= 5 * (n / ln(n))`, where `pii(n)` is the number of primes less than or equal to `n`, and `ln(n)` is the natural logarithm of `n`. Real interpretations are used on both sides of the inequality.

### Informal sketch
The proof proceeds by well-founded induction on the natural number `n`.
- Base Case: The theorem is proven directly for `n < 50` using `PII_UBOUND_CASES_50`.
- Inductive Step: Assume the theorem holds for all `m` such that `ISQRT n <= m < n` (where `ISQRT n` is the integer square root of `n`).  The goal is to show that it holds for `n`, assuming `n >= 50`.
    - We assume `7 <= ISQRT n`. This assumption is justified by proving `7 <= ISQRT n` by showing `49 < (ISQRT n + 1)^2`, which relies on the definition of `ISQRT` and `n >= 50`.
    - After some arithmetic manipulations and simplifications, the inductive hypothesis `PII_ISQRT_INDUCT` is applied.
    - Real arithmetic is used extensively, including `REAL_LE_TRANS` and rewriting with properties of real numbers and logarithms, to show that `pii(n) <= 5 * (n / ln(n))`.
    - The induction step involves showing the existence of appropriate intermediate values for bounding `pii(n)` by `5 * (n / ln(n))`. We select `&9 / &4 * (&3 / &2 * &n + &5 * &(ISQRT n))` and `&(ISQRT n) * &7` in existential steps.

### Mathematical insight
This theorem provides an upper bound for the prime-counting function `pii(n)`. The prime number theorem states that `pii(n)` is asymptotic to `n / ln(n)`. This theorem gives a concrete upper bound of `5 * (n / ln(n))`. This bound is weaker than what is known, but it provides a reasonably simple and provable bound using well-founded induction.

### Dependencies

**Theorems:**
- `num_WF`
- `PII_UBOUND_CASES_50`
- `PII_ISQRT_INDUCT`
- `REAL_LE_TRANS`
- `LE_TRANS`

**Definitions:**
- `pii`
- `ISQRT`
- `real_div`
- `real_mul`
- `ln`

**Axioms/Rules:**
- `REAL_MUL_ASSOC`
- `REAL_LE_RDIV_EQ`
- `LN_POS_LT`
- `REAL_OF_NUM_LT`
- `ARITH_RULE`
- `REAL_MUL_SYM`
- `REAL_OF_NUM_LE`
- `EXP_MONO_LT`
- `NOT_SUC`
- `EXP_2`
- `LT_MULT_RCANCEL`
- `REAL_LE_LMUL`
- `REAL_LE_LADD`
- `REAL_LE_LDIV_EQ`
- `REAL_LT_DIV`
- `REAL_POS`
- `REAL_OF_NUM_MUL`
- `LE_MULT_LCANCEL`
- `GSYM EXP_2`
- `ISQRT_WORKS`

### Porting notes (optional)
- The proof relies on `ISQRT`, which is a quotient-remainder based definition of the integer square root. Alternative definitions may require adjustments to the proof.
- The extensive use of real arithmetic and simplification tactics suggests that a proof assistant with strong support for real number reasoning will be helpful.
- The wellfounded induction follows a non-standard scheme from `PII_ISQRT_INDUCT`, which might require explicit encoding in other proof assistants.


---

