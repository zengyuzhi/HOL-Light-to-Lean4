# e_is_transcendental.ml

## Overview

Number of statements: 24

The file `e_is_transcendental.ml` formalizes a proof that the mathematical constant e is transcendental, following an approach described on the PlanetMath website and documented in a 2011 Journal of Formal Reasoning paper. It builds on HOL Light's analysis, transcendental functions, prime numbers, and Liouville's theorem libraries to construct the proof, which was originally organized across multiple modules now concatenated into a single file. The file contains custom proof machinery (including a modified PROVE function that handles additional assumptions) to support the transcendence proof, a fundamental result in number theory establishing that e cannot be expressed as a root of any non-zero polynomial with rational coefficients.

## PROVE(t,tac)

### Name of formal statement
PROVE

### Type of the formal statement
function

### Formal Content
```ocaml
let PROVE(t,tac) =
  let th = TAC_PROOF(([],t),tac) in
  let t' = concl th in
  if t' = t then th else
  try EQ_MP (ALPHA t' t) th
  with Failure _ -> failwith "PROVE: justification generated wrong theorem";;
```

### Informal statement
`PROVE(t,tac)` is a function that takes a term `t` and a tactic `tac`, and attempts to prove `t` using the given tactic. It returns a theorem. 

This function ensures that the conclusion of the resulting theorem exactly matches the input term `t`. If the tactic produces a theorem with a conclusion `t'` that is alpha-equivalent to `t` (i.e., differs only in variable names), it performs an alpha-conversion to ensure the returned theorem has exactly the conclusion `t`.

### Informal proof
The implementation works as follows:

1. Apply the given tactic `tac` to the goal `([], t)` (empty assumption list with goal `t`) using the `TAC_PROOF` function.
2. Extract the conclusion `t'` from the resulting theorem.
3. If `t'` is identical to `t`, return the theorem directly.
4. Otherwise, attempt to apply alpha-conversion:
   - Use `ALPHA t' t` to create a theorem that establishes the alpha-equivalence between `t'` and `t`.
   - Apply `EQ_MP` to convert the theorem with conclusion `t'` to an equivalent theorem with conclusion `t`.
5. If the alpha-conversion fails, raise an error indicating that the tactic produced an incorrect theorem.

### Mathematical insight
This is a utility function that ensures the conclusion of a theorem matches exactly the term we intended to prove. It's particularly useful in formal verification where exact term matching might be needed for further theorem applications.

The key insight is handling alpha-equivalence - recognizing that theorems with the same logical content but different variable names should be treated as equivalent. This function provides a wrapper that normalizes the output theorem to have the exact expected conclusion.

This function is a variant of the standard HOL Light `prove` function, but it does not check for additional assumptions in the result. According to the comment, this version was created to accommodate proofs that introduce extra assumptions in certain places.

### Dependencies
- `TAC_PROOF`: Function that applies a tactic to a goal and produces a theorem.
- `ALPHA`: Converts a theorem to an alpha-equivalent version with different variable names.
- `EQ_MP`: Modus ponens rule for equations.
- `concl`: Extracts the conclusion from a theorem.

### Porting notes
When porting this function to another proof assistant:
1. Ensure the target system has similar mechanisms for handling alpha-equivalence.
2. Consider whether the target system automatically handles alpha-equivalence or requires explicit conversion.
3. Note that this version is more permissive than the standard `prove` function as it doesn't check for additional assumptions in the proof result.
4. In systems with more sophisticated term equality checking, the explicit alpha-conversion may not be necessary.

---

## OLD_SUM

### Name of formal statement
OLD_SUM

### Type of the formal statement
Value assignment/renaming

### Formal Content
```ocaml
let OLD_SUM = sum;;
```

### Informal statement
`OLD_SUM` is defined to be equal to the `sum` function from HOL Light's analysis library. This is a value assignment that preserves the original `sum` function before it potentially gets overwritten by another library.

### Informal proof
There is no proof involved in this definition, as it is simply an assignment of the existing `sum` function to a new name `OLD_SUM`.

### Mathematical insight
This definition serves a practical purpose in the HOL Light implementation rather than a mathematical one. It preserves the original implementation of the `sum` function from HOL core (likely from iter.ml) before it gets overwritten when Library/analysis.ml is loaded. This allows code that depends on the original behavior of `sum` to continue functioning correctly by referencing `OLD_SUM` instead.

The original `sum` function represents finite summation over natural numbers with the following properties:
- `sum(n,0) f = 0` (summation over empty range equals zero)
- `sum(n,SUC m) f = sum(n,m) f + f(n + m)` (recursive definition of summation)

This kind of preservation of original definitions is common in large formal mathematics libraries to manage namespace conflicts while maintaining backward compatibility.

### Dependencies
- **Theorems**:
  - `sum`: Definition of finite summation from HOL Light's analysis library

### Porting notes
When porting to other proof assistants, you would not typically need to recreate this specific renaming, as it addresses an implementation-specific issue in HOL Light. Instead, you should focus on porting the actual `sum` function and ensuring it's available in appropriate contexts. Be aware of potential naming conflicts in the target system's mathematical libraries.

---

## ADD_ASSUMS

### ADD_ASSUMS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- new_function_definition

### Formal Content
```ocaml
let ADD_ASSUMS lst thm =
    let f x y = ADD_ASSUM y x in
    List.fold_left f thm lst
;;
```

### Informal statement
This function `ADD_ASSUMS` takes a list of assumptions `lst` and a theorem `thm`, and adds each assumption in the list to the theorem.

Specifically, for a list of assumptions `[a₁, a₂, ..., aₙ]` and a theorem `thm`, it applies the function `ADD_ASSUM` repeatedly to add each assumption to the theorem, resulting in a new theorem with all the additional assumptions.

The function is defined as:
```
ADD_ASSUMS lst thm = fold_left ADD_ASSUM thm lst
```
where `fold_left` applies `ADD_ASSUM` to the theorem and each assumption in the list from left to right.

### Informal proof
This is a definition, not a theorem, so it does not have a proof. The implementation simply uses `List.fold_left` to apply the function `f` (which is defined as `f x y = ADD_ASSUM y x`) to the theorem and each assumption in the list.

### Mathematical insight
This is a utility function that simplifies the process of adding multiple assumptions to a theorem. Instead of repeatedly calling `ADD_ASSUM` for each assumption, this function allows adding all assumptions from a list in one operation.

This kind of function is useful in interactive theorem proving when you need to temporarily introduce several assumptions for a proof step and then discharge them later.

### Dependencies
- `ADD_ASSUM` - A HOL Light function that adds a single assumption to a theorem.
- `List.fold_left` - A standard OCaml list function that applies a function to an accumulator and each element of a list from left to right.

### Porting notes
When porting to other proof assistants:
- This is a simple utility function that should be straightforward to implement in any system that has a way to add assumptions to theorems.
- The exact behavior may need to be adjusted based on how the target system handles assumptions and theorems.
- Note that the function reverses the argument order of `ADD_ASSUM` using the helper function `f`, so that the theorem comes first in `fold_left`.

---

## SPLIT_CONJOINED_ASSUMPT_TAC

### SPLIT_CONJOINED_ASSUMPT_TAC
- SPLIT_CONJOINED_ASSUMPT_TAC

### Type of the formal statement
- tactic definition

### Formal Content
```ocaml
let SPLIT_CONJOINED_ASSUMPT_TAC t =
    (UNDISCH_TAC t) THEN
    (ONCE_REWRITE_TAC [TAUT `(X /\ Y ==> Z) <=> (X ==> Y ==> Z)`]) THEN
    (DISCH_TAC THEN DISCH_TAC)
;;
```

### Informal statement
This tactic takes a goal with an assumption of the form $A \wedge B$ and splits it into two separate assumptions $A$ and $B$.

Specifically, given:
- A goal state with an assumption of the form $A \wedge B \Rightarrow C$

The tactic transforms it into a goal state with:
- Two separate assumptions $A$ and $B$ implying $C$

### Informal proof
The implementation works as follows:

1. First, we use `UNDISCH_TAC t` to move the conjunctive assumption $t$ (which has the form $A \wedge B$) back into the goal.

2. Then we use `ONCE_REWRITE_TAC` with the tautology $(X \wedge Y \Rightarrow Z) \Leftrightarrow (X \Rightarrow Y \Rightarrow Z)$ to transform the goal.

3. Finally, we apply `DISCH_TAC THEN DISCH_TAC` to move both parts of the conjunction ($X$ and $Y$) back into separate assumptions.

In this way, we effectively split a single conjunctive assumption into two separate assumptions.

### Mathematical insight
This tactic implements a standard logical transformation that's frequently useful in interactive theorem proving. When working with a conjunction in the assumptions, it's often more convenient to have each conjunct as a separate assumption so they can be referenced independently in later steps.

This tactic is a utility that saves the user from having to perform this common transformation manually. It's similar to the common practice in mathematical proofs of saying "Let's assume $A \wedge B$" and then later referring to $A$ and $B$ as separate facts.

The transformation is based on the logical equivalence:
$(A \wedge B \Rightarrow C) \Leftrightarrow (A \Rightarrow B \Rightarrow C)$

### Dependencies
None explicitly listed in the provided information.

### Porting notes
This tactic should be straightforward to port to other systems:
- It relies on basic tactics for manipulating assumptions and goals
- The core logical equivalence $(A \wedge B \Rightarrow C) \Leftrightarrow (A \Rightarrow B \Rightarrow C)$ is standard in most logical systems
- When implementing in other systems, look for equivalent tactics to `UNDISCH_TAC`, `ONCE_REWRITE_TAC`, and `DISCH_TAC`

---

## ADD_ASSUM_DISCH

### ADD_ASSUM_DISCH
- ADD_ASSUM_DISCH

### Type of the formal statement
- definition

### Formal Content
```ocaml
let ADD_ASSUM_DISCH ass thm = DISCH ass (ADD_ASSUM ass thm);;
```

### Informal statement
The function `ADD_ASSUM_DISCH` takes an assumption `ass` and a theorem `thm`, and returns a new theorem where `ass` is both added as an assumption and discharged. Specifically, it applies the following transformation:

Given:
- `ass`: A term that will become an assumption
- `thm`: A theorem

The function returns:
- A new theorem formed by adding `ass` as an assumption to `thm` and then discharging that assumption in one operation.

### Informal proof
This is a direct definition that combines two operations:
1. First, `ADD_ASSUM ass thm` adds `ass` as an assumption to the theorem `thm`.
2. Then, `DISCH ass` discharges the assumption `ass` from the resulting theorem.

The composition of these two operations effectively includes the assumption in the theorem and then immediately discharges it, creating an implication.

### Mathematical insight
This function is primarily a utility that combines two common theorem manipulation operations (adding an assumption and discharging it) in a single step. 

The operation is useful in proof automation and theorem manipulation when you need to introduce an assumption into a theorem and immediately create an implication from it. This pattern occurs frequently enough in proof development that having this combined operation as a single function improves code readability and reduces verbosity.

### Dependencies
- `ADD_ASSUM`: Adds a term as an assumption to a theorem
- `DISCH`: Discharges an assumption from a theorem by creating an implication

### Porting notes
When porting to other proof assistants:
- This is a basic utility function that relies on two fundamental theorem manipulation operations (adding and discharging assumptions).
- Most proof assistants have equivalents for both operations, making this straightforward to port.
- The implementation is simple enough that you could either define it directly or just use the two operations in sequence when needed.

---

## BRW

### Name of formal statement
BRW

### Type of the formal statement
Function definition

### Formal Content
```ocaml
let BRW t f = ONCE_REWRITE_RULE [TAUT t] f;;
```

### Informal statement
The function `BRW` (Boolean ReWrite) applies a boolean rewriting rule to a theorem exactly once. Given:
- A term `t` representing a tautology
- A theorem `f`

The function returns a new theorem that is the result of applying the rewrite rule created from the tautology `t` exactly once to theorem `f`.

### Informal proof
This is a function definition rather than a theorem, so it doesn't have a proof. The definition uses `ONCE_REWRITE_RULE` with a list containing the tautology `t` (converted to a theorem using the `TAUT` function) and applies it to theorem `f`.

### Mathematical insight
This function serves as a utility for applying boolean simplifications based on tautologies. The key insight is that it provides a convenient shorthand for applying boolean rewrites exactly once, which is a common operation when manipulating logical expressions in theorem proving.

Using the function `BRW` avoids repeatedly writing the longer expression `ONCE_REWRITE_RULE [TAUT t]` when performing boolean simplifications. The "exactly once" nature of the rewrite is important, as it gives more precise control over where and how the rewrite is applied compared to exhaustive rewriting strategies.

### Dependencies
- `ONCE_REWRITE_RULE`: Applies rewrite rules to a theorem exactly once
- `TAUT`: Converts a term representing a tautology into a theorem

### Porting notes
When porting this to other systems:
- Ensure the target system has an equivalent to `ONCE_REWRITE_RULE` that applies rewrite rules exactly once
- Check if the target system has a similar function to `TAUT` for proving tautologies automatically
- This function is a simple utility wrapper, so it might not need direct porting if the target system has more elegant ways to handle boolean rewrites

---

## BRW0

### BRW0

### Type of the formal statement
Rewrite rule (theorem)

### Formal Content
```ocaml
let BRW0 f = BRW `(X ==> Y ==> Z) <=> (X /\ Y ==> Z)` f;;
```

### Informal statement
The rewrite rule `BRW0` states the logical equivalence:
$$(X \Rightarrow Y \Rightarrow Z) \iff (X \land Y \Rightarrow Z)$$

This is a fundamental property in propositional logic establishing that a chain of implications is equivalent to a single implication with a conjunction in the antecedent.

### Informal proof
This appears to be a built-in rewrite rule in HOL Light that applies the logical equivalence between nested implications and implications with conjunctions. The proof is likely handled by the system's core logic.

The equivalence can be verified through basic propositional logic:
- In one direction: If $X \Rightarrow (Y \Rightarrow Z)$ and we assume $X \land Y$, then we have $X$ and also $Y$. From $X$ we get $Y \Rightarrow Z$, and since we have $Y$, we can conclude $Z$.
- In the other direction: If $X \land Y \Rightarrow Z$, and we assume $X$, and then assume $Y$, we effectively have $X \land Y$, which by our assumption implies $Z$.

### Mathematical insight
This rewrite rule captures a fundamental property in propositional logic about the relationship between nested implications and conjunctive antecedents. It is particularly useful in interactive theorem proving as it allows for convenient restructuring of logical statements during proofs.

Converting between these two forms is a common operation when reasoning about logical formulas, especially when working with rule application or when organizing assumptions in a proof. The rewrite directionality (from nested implications to a single implication with a conjunction) can simplify the structure of complex logical expressions.

### Dependencies
None explicitly listed.

### Porting notes
This is a basic logical equivalence that should be available in most theorem provers, either as a built-in rule or as an easily provable lemma. When porting, check if the target system has a similar rewrite rule or add it as a fundamental lemma early in development.

---

## BRW1

### BRW1

### Type of the formal statement
- Theorem (automation rule via BRW)

### Formal Content
```ocaml
let BRW1 f = BRW `(X /\ Y ==> Z) <=> (X ==> Y ==> Z)` f;;
```

### Informal statement
This theorem establishes the logical equivalence:
$$(X \land Y \Rightarrow Z) \Leftrightarrow (X \Rightarrow Y \Rightarrow Z)$$

This is a fundamental rule of propositional logic expressing the relationship between conjunction and nested implications.

### Informal proof
This is a basic rewrite rule that doesn't contain an explicit proof in the code. It states the currying/uncurrying equivalence between a conjunction in the antecedent and nested implications.

The proof would follow from the definitions of implication and conjunction:
- For the forward direction: Assume $X \land Y \Rightarrow Z$. Now assume $X$ and $Y$. These assumptions give us $X \land Y$, which by our first assumption implies $Z$. 
- For the backward direction: Assume $X \Rightarrow Y \Rightarrow Z$. Now assume $X \land Y$. From this, we have both $X$ and $Y$. From $X$ and our first assumption, we get $Y \Rightarrow Z$. Applying this with our $Y$, we obtain $Z$.

### Mathematical insight
This equivalence is a fundamental theorem in propositional logic, sometimes known as "currying" in reference to its connection to function currying in lambda calculus. It allows for interchanging between conjunction in the antecedent and nested implications, which is particularly useful in natural deduction systems.

The rule is frequently used when restructuring implications to isolate individual conditions. It allows us to convert between a combined hypothesis ($X \land Y$) and a sequence of individual hypotheses ($X$ then $Y$).

### Dependencies
This theorem doesn't have explicitly listed dependencies, as it's a basic propositional tautology that follows directly from the definitions of conjunction and implication.

### Porting notes
This rule is a standard logical equivalence that should be available in any proof assistant, though possibly with a different name. In Lean, this corresponds to two theorems: `imp_and_distrib` and `and_imp`, or it might be directly available as a simplification rule.

---

## rewrites0

### rewrites0
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem list

### Formal Content
```ocaml
let rewrites0 = map REAL_ARITH [`&0 + (y:real) = y`;`(x:real) * &0 = &0`;`(&1:real) + &0 = &1`;`(x:real) * &1 = x`];;
```

### Informal statement
`rewrites0` is a list of four real number arithmetic theorems:

1. $0 + y = y$ for any real $y$
2. $x \cdot 0 = 0$ for any real $x$
3. $1 + 0 = 1$
4. $x \cdot 1 = x$ for any real $x$

These represent basic properties of real number arithmetic with respect to the additive identity 0 and multiplicative identity 1.

### Informal proof
Each theorem in the list is proven using the HOL Light tactic `REAL_ARITH`, which automatically proves certain real arithmetic facts. These theorems are basic properties of real numbers:

1. $0 + y = y$ - this is the additive identity property
2. $x \cdot 0 = 0$ - this is the property that multiplication by zero yields zero
3. $1 + 0 = 1$ - this is a special case of the additive identity property
4. $x \cdot 1 = x$ - this is the multiplicative identity property

These are all axioms or basic derivable facts in real number systems, so the proofs are automatically handled by the `REAL_ARITH` decision procedure.

### Mathematical insight
These theorems represent fundamental properties of the real number field:
- The first and third theorems represent the additive identity property
- The second theorem represents the zero property of multiplication
- The fourth theorem represents the multiplicative identity property

These basic algebraic properties are essential building blocks for real number arithmetic and are frequently used in simplifying expressions. Bundling them together as `rewrites0` makes them conveniently available for automated rewriting strategies in proofs involving real numbers.

### Dependencies
- Tactics/procedures:
  - `REAL_ARITH`: A decision procedure for real arithmetic

### Porting notes
When porting to other proof assistants:
- These theorems should already exist in the standard library of most proof assistants with real number support
- In systems with good automation for arithmetic (like Isabelle/HOL or Lean), these theorems might be automatically proven or even built into the simplifier
- In systems with less automation, you might need to explicitly reference the corresponding theorems in the standard library rather than reproving them

---

## PDI_DEF

### PDI_DEF

### Type of the formal statement
new_recursive_definition

### Formal Content
```ocaml
let PDI_DEF = new_recursive_definition num_RECURSION
    `    (poly_diff_iter p 0 = p)
      /\ (poly_diff_iter p (SUC n) = poly_diff (poly_diff_iter p n))
    `
let PDI_POLY_DIFF_COMM = PROVE(
    `! p n.(poly_diff_iter (poly_diff p) n) = (poly_diff (poly_diff_iter p n))`,
    STRIP_TAC THEN INDUCT_TAC THEN (ASM_SIMP_TAC [PDI_DEF])
)

let SODN = new_definition
    `SODN p n = iterate poly_add (0..n) (\i.poly_diff_iter p i)`
;;
```

### Informal statement
The function `poly_diff_iter` is defined recursively on natural numbers as follows:

For a polynomial $p$ and a natural number $n$:
- $\text{poly\_diff\_iter}(p, 0) = p$
- $\text{poly\_diff\_iter}(p, n+1) = \text{poly\_diff}(\text{poly\_diff\_iter}(p, n))$

This defines the $n$-fold iterated differentiation of a polynomial $p$.

### Informal proof
This is a recursive definition, not a theorem, so it doesn't have a proof.

### Mathematical insight
This definition formalizes the concept of repeatedly applying the differentiation operator to a polynomial. The function `poly_diff_iter(p, n)` represents the $n$-th derivative of polynomial $p$. 

It's a fundamental building block for working with properties of polynomial derivatives in a formal setting. By defining iterated differentiation recursively, we can easily prove properties about the behavior of polynomials under repeated differentiation.

The `PDI_POLY_DIFF_COMM` theorem that follows demonstrates an important property: the operations of differentiating and iterating differentiation commute, which is expected from the mathematical meaning of these operations.

The `SODN` definition (Sum of Derivatives up to N) combines this concept to form the sum of all derivatives of a polynomial from the 0th (the polynomial itself) up to the nth derivative.

### Dependencies
- `num_RECURSION`: Used to define recursive functions over natural numbers
- `poly_diff`: Represents the derivative of a polynomial

### Porting notes
When porting this definition to another system:
1. Ensure the target system has a way to define polynomials and their differentiation
2. Confirm that the recursive definition mechanism in the target system can handle this simple pattern
3. Consider whether the target system's type inference will require more explicit typing annotations for polynomials

---

## SOD

### Name of formal statement
SOD

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let SOD = new_definition `!p. SOD p = SODN p (LENGTH p)`;;
```

### Informal statement
For any polynomial $p$, $\text{SOD}(p)$ is defined as $\text{SODN}(p, \text{LENGTH}(p))$.

Here:
- $p$ represents a polynomial
- $\text{LENGTH}(p)$ refers to the length of the polynomial (likely the number of coefficients)
- $\text{SODN}(p, n)$ is presumably a function that computes the sum of derivatives up to order $n$ of polynomial $p$ (based on the naming convention, though the definition of SODN isn't provided in the dependencies)

### Informal proof
This is a definition, so no proof is required.

### Mathematical insight
This definition appears to be creating a shorthand notation for the sum of all derivatives of a polynomial $p$ up to its length. The acronym SOD likely stands for "Sum Of Derivatives".

The function takes a polynomial and computes the sum of its derivatives up to the order equal to the length of the polynomial itself. This is useful in various polynomial analysis contexts, particularly when analyzing properties related to derivatives of polynomials.

The choice to sum derivatives up to exactly the length of the polynomial is canonical because for a polynomial of degree $n$, all derivatives of order higher than $n$ are zero. Thus, $\text{SOD}(p)$ effectively captures the sum of all non-zero derivatives of the polynomial.

### Dependencies
#### Definitions
- `SODN` (not provided in the dependency list but referenced in the definition)

### Porting notes
When porting this definition to another system, ensure that:
1. The `SODN` function is properly defined first
2. The system has an appropriate representation for polynomials
3. `LENGTH` is properly defined for the polynomial representation in the target system

Note that the specific representation of polynomials may vary between systems, so the implementation of `LENGTH` might need adjustment accordingly.

---

## PHI

### PHI

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let PHI = new_definition `Phi f x = (exp (-- x)) * (poly (SOD f) x)`

let PLANETMATH_EQN_1_1_1 = PROVE(
    `! x f.((Phi f) diffl ((exp (--x)) * ((poly (poly_diff (SOD f)) x) - (poly (SOD f) x))) )(x)`,
    let lem1 = SPECL [`\x.exp (--x)`;
                      `\x.poly (SOD f) x`;
                      `--(exp (--x))`;
                      `poly (poly_diff (SOD f)) x`;
                      `x:real`]  DIFF_MUL in
    let EXP_NEG_X_DIFF = PROVE(
          `!x. ((\x.exp (--x)) diffl (-- (exp (--x))))(x)`,
          STRIP_TAC THEN DIFF_TAC THEN REAL_ARITH_TAC) in
    let lem2 = SPEC `x:real` EXP_NEG_X_DIFF in
    let lem3 = SPECL [`SOD f`;`x:real`] POLY_DIFF in
    let lem4 = CONJ lem2 lem3 in
    let lem5 = BETA_RULE (MP lem1 lem4) in
    let lem6 = REAL_ARITH `(a*(b - c)) = (-- a*c) + (b*a)` in
    let PHI_abs = PROVE(
          `Phi f  = \x.((exp (-- x)) * (poly (SOD f) x))`,
          (PURE_REWRITE_TAC [SYM (ABS `x:real` (SPEC_ALL PHI))])
          THEN (ACCEPT_TAC (SYM (ETA_CONV `\x.(Phi f x)`))))
    in
    (REPEAT STRIP_TAC) THEN
    (REWRITE_TAC [PHI_abs]) THEN
    (REWRITE_TAC [lem6]) THEN
    (ACCEPT_TAC lem5)
)

let POLY_SUB = PROVE(
        `!p1 p2 x. poly (p1 ++ (neg p2)) x = poly p1 x - poly p2 x`,
        (REWRITE_TAC [POLY_ADD;poly_neg;POLY_CMUL]) THEN REAL_ARITH_TAC
)
let ZERO_INSERT_NUMSEG = PROVE(
    `!n. (0..n) = (0 INSERT (1..n))`,
    let lem01 = SIMP_RULE [ARITH_RULE `0 <= n`] (SPECL [`0`;`n:num`] NUMSEG_LREC) in
    let lem02 = SIMP_RULE [ARITH_RULE `0 + 1 = 1`] lem01 in
    (ACCEPT_TAC (GEN_ALL (GSYM lem02)))
)
let PDI_POLYDIFF_SUC_LEMMA = PROVE(
    `!f n .(poly_diff_iter (poly_diff f) n) = poly_diff_iter f (SUC n)`,
    STRIP_TAC THEN INDUCT_TAC THENL
    [ (SIMP_TAC [PDI_DEF]);
      (ONCE_REWRITE_TAC [PDI_DEF]) THEN
      (ONCE_REWRITE_TAC [PDI_DEF]) THEN
      (SIMP_TAC [PDI_POLY_DIFF_COMM])
    ]
)
let SOD_POLY_DIFF_ITERATE = PROVE(
    `!f .(SOD (poly_diff f)) = iterate (++) (1..(LENGTH f)) (\i.poly_diff_iter f i)`,
    let lemA1 = SPECL [`1`;`0`] NUMSEG_EMPTY in
    let lemA2 = SIMP_RULE [ARITH_RULE `0 < 1`] lemA1 in
    let lem1 =  MATCH_MP ITERATE_IMAGE_NONZERO MONOIDAL_POLY_ADD in
    let lem2 = ISPECL [`poly_diff_iter f`;`SUC`;`0..(LENGTH (poly_diff f))`] lem1 in
    let lem3 = SIMP_RULE [FINITE_NUMSEG] lem2 in
    let lem4 = ONCE_REWRITE_RULE [ARITH_RULE `~(~(x=y) /\ (SUC x) = (SUC y))`] lem3 in
    let lem5 = SIMP_RULE [] lem4 in
    let lem6 = ISPECL [`0`;`n:num`;`1`] NUMSEG_OFFSET_IMAGE in
    let lem7 = SIMP_RULE [ARITH_RULE `!m.m+1 = SUC m`] lem6 in
    let lem8 = SIMP_RULE [ARITH_RULE `SUC 0 = 1`] lem7 in
    let lem9 = ONCE_REWRITE_RULE [ETA_CONV `(\i. SUC i)`] lem8 in
    let lem10 = ONCE_REWRITE_RULE [GSYM lem9] lem5 in
    let lem11 = ONCE_REWRITE_RULE [GSYM (ETA_CONV `(\i. poly_diff_iter f i)`)] lem10 in
    let lem12 = SIMP_RULE [o_DEF] lem11 in
    let lemma0 = PROVE(
        `! h t.SUC (LENGTH (poly_diff (CONS h t))) = LENGTH (CONS h t)`,
        (SIMP_TAC [LENGTH_POLY_DIFF;LENGTH;PRE])
    ) in
    (ONCE_REWRITE_TAC [SOD]) THEN (ONCE_REWRITE_TAC [SODN]) THEN
    (ONCE_REWRITE_TAC [PDI_POLYDIFF_SUC_LEMMA ]) THEN LIST_INDUCT_TAC THENL
    [ (SIMP_TAC [poly_diff;LENGTH]) THEN
      (SIMP_TAC [GSYM lemma0;lem12]) THEN
      (SIMP_TAC [NUMSEG_SING;MONOIDAL_POLY_ADD;ITERATE_SING]) THEN
      (SIMP_TAC [lemA2;MATCH_MP ITERATE_CLAUSES_GEN MONOIDAL_POLY_ADD]) THEN
      (ONCE_REWRITE_TAC [POLY_ADD_IDENT]) THEN
      (SIMP_TAC [PDI_DEF;POLY_DIFF_CLAUSES]);
      (SIMP_TAC [lem12;GSYM lemma0])
    ]
)
let ZERO_ITERATE_POLYADD_LEMMA = PROVE(
    `!n f .iterate (++) (0 INSERT (1..n)) f
           = (f 0) ++ iterate (++) (1..n) f`,
    let lem0 = PROVE(`!n. ~(0 IN (1..n))`,
                      STRIP_TAC THEN (ONCE_REWRITE_TAC [IN_NUMSEG]) THEN
                      ARITH_TAC) in
    let lem1 = ISPEC `poly_add` ITERATE_CLAUSES_GEN in
    let lem2 = SIMP_RULE [MONOIDAL_POLY_ADD] lem1  in
    let lem3 = CONJUNCT2 lem2  in
    let lem4 = ISPECL [`f:(num -> (real)list)`;`0`;`1..n`] lem3  in
    let lem5 = ISPECL [`poly_add`;`f:(num -> (real)list)`;`1..n` ] FINITE_SUPPORT  in
    let lem6 = SIMP_RULE [FINITE_NUMSEG] lem5 in
    let lem7 = MP lem4 lem6  in
    let lem9 = SIMP_RULE [lem0] lem7  in
    (ACCEPT_TAC (GEN_ALL lem9))
)
let SOD_SOD_POLYDIFF = PROVE(
    `!f .(SOD f) = f ++ (SOD (poly_diff f))`,
    (ONCE_REWRITE_TAC [SOD_POLY_DIFF_ITERATE]) THEN (ONCE_REWRITE_TAC [SOD]) THEN
    (ONCE_REWRITE_TAC [SODN]) THEN
    (ONCE_REWRITE_TAC [ZERO_INSERT_NUMSEG]) THEN
    (ONCE_REWRITE_TAC [ZERO_ITERATE_POLYADD_LEMMA]) THEN
    (BETA_TAC) THEN (SIMP_TAC [PDI_DEF])
)
let SUC_INSERT_NUMSEG = PROVE(
    `!n. (0..(SUC n)) = (SUC n) INSERT (0..n)`,
    let lem01 = SIMP_RULE [ARITH_RULE `0 <= SUC n`]
                          (SPECL [`0`;`n:num`] NUMSEG_REC) in
    ACCEPT_TAC (GEN_ALL lem01)
)
let SUC_NOT_IN_NUMSEG = PROVE(
    `!m n. ~((SUC n) IN (m..n))`,
    STRIP_TAC THEN (ONCE_REWRITE_TAC [IN_NUMSEG]) THEN ARITH_TAC
)
let SUC_ITERATE_PDI_POLYDIFF_LEMMA = PROVE(
    `iterate (++) ((SUC n) INSERT (0..n)) (\i.poly_diff_iter (poly_diff p) i) =
     (poly_diff_iter (poly_diff p) (SUC n)) ++
     iterate (++) (0..n) (\i.poly_diff_iter (poly_diff p) i)`,
    let lem1 = ISPEC `poly_add` ITERATE_CLAUSES_GEN in
    let lem2 = SIMP_RULE [MONOIDAL_POLY_ADD] lem1 in
    let lem3 = CONJUNCT2 lem2 in
    let lem4 = ISPECL [`(\i.poly_diff_iter (poly_diff p) i)`;`SUC n`;`0..n`] lem3 in
    let lem5 = ISPECL [`poly_add`;`\i.poly_diff_iter (poly_diff p) i`;`0..n` ] FINITE_SUPPORT in
    let lem6 = SIMP_RULE [FINITE_NUMSEG] lem5 in
    let lem7 = MP lem4 lem6 in
    let lem9 = SIMP_RULE [SPEC `0` SUC_NOT_IN_NUMSEG] lem7 in
    ACCEPT_TAC lem9
)
let SODN_POLY_DIFF_COMM = PROVE(
    `!n p.(SODN (poly_diff p) n) = poly_diff (SODN p n)`,
    let lem = MP (ISPEC `poly_add` ITERATE_SING) MONOIDAL_POLY_ADD in
    let lem1 = ISPEC `poly_add` ITERATE_CLAUSES_GEN in
    let lem2 = SIMP_RULE [MONOIDAL_POLY_ADD] lem1 in
    let lem3 = CONJUNCT2 lem2 in
    let lem10 = SIMP_RULE [GSYM SUC_INSERT_NUMSEG] SUC_ITERATE_PDI_POLYDIFF_LEMMA in
    let lema00 = ISPECL [`(\i.poly_diff_iter (p) i)`;`SUC n`;`0..n`] lem3 in
    let lema0 = SIMP_RULE [GSYM SUC_INSERT_NUMSEG] lema00 in
    let lem15 = ISPECL [`poly_add`;`\i.poly_diff_iter (p) i`;`0..n` ] FINITE_SUPPORT in
    let lem16 = SIMP_RULE [FINITE_NUMSEG] lem15 in
    let lema1 = MP lema0 lem16 in
    let lema2 = SIMP_RULE [SPEC `0` SUC_NOT_IN_NUMSEG] lema1 in
    let lema3 = ONCE_REWRITE_RULE [GSYM SODN] lema2 in
    INDUCT_TAC THENL
    [ (ONCE_REWRITE_TAC [SODN]) THEN
      (SIMP_TAC [NUMSEG_SING;ITERATE_SING]) THEN
      (ONCE_REWRITE_TAC [lem]) THEN
      (BETA_TAC) THEN
      (SIMP_TAC [PDI_POLY_DIFF_COMM])
      ;
      (ONCE_REWRITE_TAC [SODN]) THEN (ONCE_REWRITE_TAC [lem10]) THEN
      (ONCE_REWRITE_TAC [GSYM SODN]) THEN (ASM_SIMP_TAC []) THEN
      (ONCE_REWRITE_TAC [PDI_DEF ]) THEN
      (ONCE_REWRITE_TAC [PDI_POLY_DIFF_COMM]) THEN
      (ONCE_REWRITE_TAC [GSYM POLYDIFF_ADD]) THEN
      STRIP_TAC THEN AP_TERM_TAC THEN
      (ONCE_REWRITE_TAC [lema3]) THEN (SIMP_TAC [PDI_DEF])
    ]
)
let SUC_ITERATE_POLYADD_LEMMA = PROVE(
    `!n f .iterate (++) ((SUC n) INSERT (0..n)) f
           = (f (SUC n)) ++ iterate (++) (0..n) f`,
    let lem1 = ISPEC `poly_add` ITERATE_CLAUSES_GEN in
    let lem2 = SIMP_RULE [MONOIDAL_POLY_ADD] lem1  in
    let lem3 = CONJUNCT2 lem2  in
    let lem4 = ISPECL [`f:(num -> (real)list)`;`SUC n`;`0..n`] lem3  in
    let lem5 = ISPECL [`poly_add`;`f:(num -> (real)list)`;`0..n` ] FINITE_SUPPORT  in
    let lem6 = SIMP_RULE [FINITE_NUMSEG] lem5 in
    let lem7 = MP lem4 lem6  in
    let lem9 = SIMP_RULE [SPEC `0` SUC_NOT_IN_NUMSEG] lem7  in
    ACCEPT_TAC (GEN_ALL lem9)
)
let NUMSEG_LENGTH_POLYDIFF_LEMMA = PROVE(
    `!f. (0..(LENGTH f)) = ((LENGTH f) INSERT (0..(LENGTH (poly_diff f))))`,
    (SIMP_TAC [LENGTH_POLY_DIFF]) THEN (LIST_INDUCT_TAC) THENL
    [ (SIMP_TAC [LENGTH;PRE]) THEN (SIMP_TAC [NUMSEG_CLAUSES]) THEN
      (SIMP_TAC [INSERT_DEF;NOT_IN_EMPTY;IN]);
      (SIMP_TAC [LENGTH;PRE]) THEN
      (SIMP_TAC [ARITH_RULE `0 <= SUC n`;NUMSEG_REC])
    ]
)
let POLY_DIFF_LENGTH_LT = PROVE(
    `!p. (~(p=[])) ==> (LENGTH (poly_diff p)) < (LENGTH p)`,
    SIMP_TAC [LENGTH_POLY_DIFF;LENGTH_EQ_NIL;
               ARITH_RULE `!n.(~(n=0)) ==> (PRE n) < n`]
);;
```

### Informal statement
The definition `Phi` represents a function that takes a polynomial `f` and a real value `x` and computes:

$$\Phi(f, x) = e^{-x} \cdot \text{poly}(\text{SOD}(f), x)$$

where:
- `e^{-x}` is the exponential function applied to the negative of `x`
- `poly(p, x)` evaluates a polynomial `p` at the point `x`
- `SOD(f)` represents the sum of derivatives of the polynomial `f` up to the length of `f`

### Informal proof
The HOL Light script contains multiple proofs related to the `Phi` function, particularly the theorem `PLANETMATH_EQN_1_1_1` which establishes that:

$$\frac{d}{dx}\Phi(f, x) = e^{-x} \cdot (\text{poly}(\text{poly\_diff}(\text{SOD}(f)), x) - \text{poly}(\text{SOD}(f), x))$$

The proof proceeds as follows:

- First, applies the product rule for differentiation (`DIFF_MUL`) to decompose the derivative of the product $e^{-x} \cdot \text{poly}(\text{SOD}(f), x)$
- Uses the known derivative of $e^{-x}$ which is $-e^{-x}$
- Uses the derivative of the polynomial evaluation which gives $\text{poly}(\text{poly\_diff}(\text{SOD}(f)), x)$
- Combines these results and simplifies using algebraic manipulations
- The key insight used is the relation: $(a \cdot (b - c)) = (-a \cdot c) + (b \cdot a)$

Additionally, the script proves several important supporting lemmas about polynomials and their derivatives, particularly:
- `SOD_SOD_POLYDIFF` which establishes $\text{SOD}(f) = f + \text{SOD}(\text{poly\_diff}(f))$
- Various lemmas about iterating over polynomial derivatives and ranges

### Mathematical insight
The function `Phi` is part of a framework for proving transcendence results, particularly in relation to the number e. The exponential decay factor $e^{-x}$ combined with polynomial evaluation creates a function with special differential properties.

The key mathematical insight is how the differentiation of `Phi` relates to the original function but with a specific difference term between the polynomial and its derivative. This structure is essential for creating the mathematical machinery needed in transcendence proofs.

The SOD (Sum of Derivatives) operation captures the behavior of repeated differentiation in a single polynomial, which simplifies the analysis of higher-order differential behavior.

### Dependencies
- **Definitions:**
  - `diffl` - Definition of differentiability in HOL Light
  - `PDI_DEF` - Polynomial derivative iteration definition
  - `SOD` - Sum of derivatives of a polynomial
  - `SODN` - Sum of derivatives up to n

- **Theorems:**
  - `DIFF_MUL` - Product rule for differentiation

### Porting notes
When porting this to other proof assistants:
1. Ensure proper handling of polynomial representation
2. Pay attention to the iteration over polynomial derivatives
3. The exponential function implementation may vary between systems
4. The recursive structure of SOD (Sum of Derivatives) might need special attention in systems with different recursion principles

---

## POLY_DIFF_LENGTH_LE_SUC

### Name of formal statement
POLY_DIFF_LENGTH_LE_SUC

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let POLY_DIFF_LENGTH_LE_SUC = PROVE(
    `! p n . (LENGTH p <= SUC n)  ==> (LENGTH (poly_diff p) <= n)`,
    (REPEAT STRIP_TAC) THEN (ASM_CASES_TAC `p:(real)list =[]`) THENL
    [ (ASM_SIMP_TAC [poly_diff;LENGTH]) THEN (ARITH_TAC);
      (ASM_MESON_TAC [POLY_DIFF_LENGTH_LT;LT_SUC_LE;LTE_TRANS])
    ]
)
let PDI_LENGTH_AUX = PROVE(
    `! n p. (LENGTH p <= n) ==> poly_diff_iter p n = []`,
    INDUCT_TAC THENL
    [ MESON_TAC [PDI_DEF;LENGTH_EQ_NIL;ARITH_RULE `n <= 0 <=> n = 0`];
      ASM_MESON_TAC [PDI_DEF;PDI_POLY_DIFF_COMM;POLY_DIFF_LENGTH_LE_SUC] ]
)
let PDI_LENGTH_NIL =  PROVE(
    `! p . poly_diff_iter p (LENGTH p) = []`,
    SIMP_TAC [PDI_LENGTH_AUX;LE_REFL]
)
let SOD_POLYDIFF_THEOREM = PROVE(
    `!f .(SOD (poly_diff f)) = (poly_diff (SOD f))`,
    let lemmmag = PROVE(
        `0 INSERT (0..0) = (0..0)`,
        (SIMP_TAC [NUMSEG_SING]) THEN
        (SIMP_TAC [INSERT_DEF;NOT_IN_EMPTY;IN])) in
    let SUC_LENGTH_CONS = PROVE(
        `SUC (LENGTH (t:(real)list)) = (LENGTH (CONS h t))`,
        (SIMP_TAC [LENGTH])) in
    (ONCE_REWRITE_TAC [SOD]) THEN
    (ONCE_REWRITE_TAC [SODN_POLY_DIFF_COMM]) THEN
    (ONCE_REWRITE_TAC [SODN]) THEN
    (STRIP_TAC) THEN
    (CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [NUMSEG_LENGTH_POLYDIFF_LEMMA]))) THEN
    (SPEC_TAC (`f:(real)list`,`f:(real)list`)) THEN
    (LIST_INDUCT_TAC) THENL
    [ (SIMP_TAC [poly_diff]) THEN
      (SIMP_TAC [LENGTH]) THEN
      (SIMP_TAC [SUM_SING_NUMSEG ]) THEN
      (SIMP_TAC [lemmmag])
      ;
       (SIMP_TAC [LENGTH_POLY_DIFF]) THEN
       (SIMP_TAC [LENGTH;PRE]) THEN
       (CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [SUC_ITERATE_POLYADD_LEMMA]))) THEN
       (SIMP_TAC [LENGTH;PRE]) THEN
       (SIMP_TAC [GSYM SODN]) THEN
       (ONCE_REWRITE_TAC [GSYM SODN]) THEN
       (ONCE_REWRITE_TAC [SUC_LENGTH_CONS]) THEN
       (ONCE_REWRITE_TAC [PDI_LENGTH_NIL]) THEN
       (SIMP_TAC [POLY_ADD_CLAUSES ]);
    ]
)
let SOD_SOD_DIFF_LEMMA = PROVE(
    `!f x.(poly (SOD f) x) - (poly (poly_diff (SOD f)) x) = poly f x`,
    MESON_TAC [SOD_SOD_POLYDIFF; POLY_ADD ; POLY_SUB;SOD_POLYDIFF_THEOREM;
               REAL_ARITH `((x:real) + y) -y = x`]
)

let PLANETMATH_EQN_1_1_2 = PROVE(
    `!f x.
        ((exp (--x)) * ((poly (poly_diff (SOD f)) x) - (poly (SOD f) x)))
        = (-- (exp (--x))) * (poly f x)`,
    let lem17 = PROVE(`!x y.(x - y) = (-- (y - x))`,REAL_ARITH_TAC) in
    (REPEAT STRIP_TAC) THEN
    (ONCE_REWRITE_TAC [lem17]) THEN (ONCE_REWRITE_TAC [SOD_SOD_DIFF_LEMMA])
    THEN REAL_ARITH_TAC
)

let PLANETMATH_EQN_1_1_3 = PROVE(
    `! x f.((Phi f) diffl (-- (exp (--x)) * (poly f x)))(x)`,
    (ONCE_REWRITE_TAC [GSYM PLANETMATH_EQN_1_1_2]) THEN (ACCEPT_TAC PLANETMATH_EQN_1_1_1)
)
let PHI_CONTL =
   let lem0 = SPECL [`Phi f`;`-- (exp (--x)) * (poly f x)`;`x:real`] DIFF_CONT in
   GEN_ALL (MP lem0 (SPEC_ALL PLANETMATH_EQN_1_1_3))

let PHI_DIFFERENTIABLE = PROVE(
    `!f x.(Phi f) differentiable x`,
    (SIMP_TAC [differentiable]) THEN (REPEAT STRIP_TAC) THEN
    (EXISTS_TAC `((exp (--x)) * ((poly (poly_diff (SOD f)) x) - (poly (SOD f) x)))`)
    THEN (SIMP_TAC [PLANETMATH_EQN_1_1_1])
)
let PLANETMATH_EQN_1_2 =
   (* this one's a bit nasty *)
   let FO_LEMMA2 = GEN_ALL (PROVE(
         `((! l z. (C (l:real) (z:real)) ==> l = (l' z))) ==> ((? (l:real) (z:real) .(A z) /\ (B  z) /\ (C l z) /\ (D l) ) ==> (? (z:real).((A z) /\ (B z) /\ (D (l' z)))))`,
       let lem0 = PROVE(`(! (l:real) z.(C l (z:real)) ==> l = (l' z)) ==> ((C l z) = ((C l z) /\ l = (l' z)))`, MESON_TAC[]) in
       let lem1 = UNDISCH lem0 in
        (STRIP_TAC THEN (ONCE_REWRITE_TAC [lem1]) THEN (MESON_TAC[]))
   )) in
    let PROP_LEMMA = TAUT `! a b c d.((a /\ b /\ c) ==> d) = (b ==> c ==> a ==> d)` in
    let MVT_SPEC = SPECL [`Phi f`;`&0`;`x:real`] MVT in
    let MVT_SPEC2 = ONCE_REWRITE_RULE [PROP_LEMMA] MVT_SPEC in
    let MVT_SPEC3 = UNDISCH MVT_SPEC2 in
    let MVT_SPEC4 = UNDISCH MVT_SPEC3 in
    let MVT_SPEC5 = UNDISCH MVT_SPEC4 in
    let lem0 = PROVE(`! x. x - &0 = x`,REAL_ARITH_TAC) in
    let MVT_SPEC6 = ONCE_REWRITE_RULE [lem0] MVT_SPEC5 in
    let DIFF_UNIQ_SPEC1 = SPEC `Phi f` DIFF_UNIQ in
    let DIFF_UNIQ_SPEC2 = SPEC `l:real` DIFF_UNIQ_SPEC1 in
    let DIFF_UNIQ_SPEC3 = SPEC ` (-- (exp (--x)) * (poly f x)) ` DIFF_UNIQ_SPEC2 in
    let DIFF_UNIQ_SPEC4 = SPEC `x:real` DIFF_UNIQ_SPEC3 in
    let lem8 = SIMP_RULE [PLANETMATH_EQN_1_1_3] DIFF_UNIQ_SPEC4 in
    let lem9 = GENL [`l:real`;`x:real`] lem8 in
    let lem10 = SPECL [`\l x.((Phi f diffl l) x)`;`\z.(&0)<z`;`\z.z < (x:real)`;`\l. (Phi f x) - (Phi f (&0)) = x * l`] FO_LEMMA2  in
    let lem12 = SPEC `\x.(--(exp (--x))) * (poly f x)` lem10 in
    let lem13 = BETA_RULE lem12 in
    let lem14 = MP lem13 lem9 in
    let lem15 = MP lem14 MVT_SPEC6  in
    let lem70 = SPECL [`f:(real)list`;`x':real`] PHI_DIFFERENTIABLE  in
    let lem71 = ADD_ASSUM `(&0) < x' /\ x' < x` lem70 in
    let lem72 = GEN `x':real` (DISCH_ALL lem71) in
    let lem73 = MP (DISCH (concl lem72) lem15) lem72 in
    let lem80 = SPECL [`f:(real)list`;`x':real`] PHI_CONTL  in
    let lem81 = ADD_ASSUM `(&0) <= x' /\ x' <= x` lem80 in
    let lem82 = GEN `x':real` (DISCH_ALL lem81) in
    let lem83 = MP (DISCH (concl lem82) lem73) lem82 in
    lem83

let xi_DEF  = new_specification ["xi"]
    (let FO_LEM = PROVE(
         `  (! x f.(P x) ==> ? z. (Q z x f))
          = (! (x:real) (f:(real)list). ? (z:real). (P x) ==> (Q z x f))`,
         MESON_TAC []) in
    ((CONV_RULE SKOLEM_CONV)
      (ONCE_REWRITE_RULE [FO_LEM]
        (GEN_ALL (DISCH_ALL PLANETMATH_EQN_1_2)))))

let PLANETMATH_LEMMA_1 = PROVE(
    `!x f.  &0 < x
            ==> poly (SOD f) (&0) * exp x =
                poly (SOD f) x + x * exp (x - xi x f) * poly f (xi x f)`,
    let lemA = CONJUNCT2 (CONJUNCT2 (UNDISCH (SPEC_ALL xi_DEF))) in
    let lemB = ONCE_REWRITE_RULE [PHI] lemA in
    let lemC = ONCE_REWRITE_RULE [REAL_ARITH `((A:real) - B = C) = (B = A - C)`] lemB in
    let lemD = SIMP_RULE [REAL_NEG_0;REAL_EXP_0;REAL_MUL_LID] lemC in
    let lem01 =  ASSUME `A = ((exp (-- x))*B - (C *( -- (exp (-- y))) * D))` in
    let lem02 = DISJ2 `exp x = &0` lem01 in
    let lem03 = REWRITE_RULE [GSYM (SPEC `exp x` REAL_EQ_MUL_LCANCEL)] lem02 in
    let lem04 = SIMP_RULE [REAL_EXP_NEG_MUL;REAL_EXP_ADD_MUL] lem03 in
    let lem05 = SIMP_RULE [REAL_SUB_LDISTRIB] lem04 in
    let lem07 = SIMP_RULE [REAL_MUL_ASSOC;REAL_EXP_NEG_MUL;REAL_MUL_LID] lem05 in
    let fact00 = REAL_ARITH `(B:real) - ((expx * C) * (--expy))  * D = B + C * (expx * expy) * D` in
    let lem08 = ONCE_REWRITE_RULE [fact00] lem07 in
    let lem09 = SIMP_RULE [GSYM REAL_EXP_ADD] lem08 in
    let lem10 = SIMP_RULE [PROVE(`(x:real) + -- y =  x - y`, REAL_ARITH_TAC)] lem09 in
    let lem11 = GEN_ALL (DISCH_ALL lem10) in
    let lem12 = SPECL [`poly (SOD f) (&0)`;
                       `poly (SOD f) x`;
                       `x:real`;
                       `x:real`;
                       `xi x f`;
                       `poly f (xi x f)`] lem11 in
    let lem13 = MP lem12 lemD  in
    let lem14 = SPECL [`exp x`;`poly (SOD f) (&0)`] REAL_MUL_SYM in
    ACCEPT_TAC (GEN_ALL (DISCH_ALL (ONCE_REWRITE_RULE [lem14] lem13)))
)

end;;
```

### Informal statement
For all polynomials $p$ and natural numbers $n$, if the length of $p$ is at most $n+1$ (i.e., $\text{LENGTH}(p) \leq n+1$), then the length of the derivative of $p$ is at most $n$ (i.e., $\text{LENGTH}(\text{poly\_diff}(p)) \leq n$).

In terms of polynomial degrees, this theorem states that if a polynomial has degree at most $n$, then its derivative has degree at most $n-1$.

### Informal proof
The proof proceeds by case analysis on whether $p$ is the empty list (representing the zero polynomial):

* If $p = []$, then $\text{poly\_diff}(p) = []$ by definition, so $\text{LENGTH}(\text{poly\_diff}(p)) = 0 \leq n$ for any $n$.

* If $p \neq []$, then by theorem `POLY_DIFF_LENGTH_LT`, we know that $\text{LENGTH}(\text{poly\_diff}(p)) < \text{LENGTH}(p)$.
  
  Given our assumption that $\text{LENGTH}(p) \leq n+1$, we can combine these facts:
  
  $\text{LENGTH}(\text{poly\_diff}(p)) < \text{LENGTH}(p) \leq n+1$
  
  Therefore, $\text{LENGTH}(\text{poly\_diff}(p)) \leq n$ by the transitivity of $\leq$ and the property that if $a < b+1$ then $a \leq b$.

### Mathematical insight
This theorem formalizes the well-known property that differentiation reduces the degree of a polynomial by exactly 1 (or results in zero if the polynomial is constant). This is a fundamental property of polynomial differentiation that is used throughout calculus and analysis.

In HOL Light, polynomials are represented as lists of coefficients, where the length of the list corresponds to the degree of the polynomial plus 1. The theorem uses this representation to formalize the relationship between a polynomial's degree and the degree of its derivative.

### Dependencies
- `POLY_DIFF_LENGTH_LT`: States that for non-empty polynomials, the length of the derivative is strictly less than the length of the original polynomial
- `LT_SUC_LE`: States that $a < b+1$ implies $a \leq b$
- `LTE_TRANS`: Transitivity of $\leq$ relation

### Porting notes
When porting to other theorem provers, be aware of how polynomials are represented. HOL Light represents polynomials as lists of coefficients, but other systems may use different representations. The core mathematical statement should remain the same regardless of representation: differentiation reduces the degree of a non-constant polynomial by exactly 1.

---

## POLY_MCLAURIN

### POLY_MCLAURIN
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let POLY_MCLAURIN =  PROVE(
    `! p x. poly p x =
            psum (0, LENGTH p) (\m.poly (poly_diff_iter p m) (&0) / &(FACT m) * x pow m)`,
    let lem002 = SPECL [`poly p`;`\n.poly (poly_diff_iter p n)`] MCLAURIN_ALL_LE in
    let lem003 = SIMP_RULE [Pm_lemma1.PDI_DEF;POLY_DIFF] lem002 in
    let lem004 = REWRITE_RULE [ETA_CONV `(\x.poly l x)`] POLY_DIFF in
    let lem005 = MATCH_MP lem003 (GEN `m:num` (SPECL [`poly_diff_iter p m`] lem004)) in
    let lem007 = SPECL [`x:real`;`LENGTH (p:(real)list)`] lem005 in
    let lem008 = ONCE_REWRITE_RULE [Pm_lemma1.PDI_LENGTH_NIL] lem007 in
    let lem009 = ONCE_REWRITE_RULE [poly] lem008 in
    let lem010 = SIMP_RULE [REAL_ARITH `!x. ((&0)/x) = &0`] lem009 in
    let lem011 = SIMP_RULE [REAL_MUL_LZERO;REAL_ADD_RID] lem010 in
    let lem012 = PROVE(`(? t . (A t) /\ B) ==> B`, MESON_TAC []) in
    ACCEPT_TAC (GEN_ALL (MATCH_MP lem012 lem011))
)
let DIFF_ADD_CONST_COMMUTE = PROVE(
    `!f a l x . (f diffl l) (x + a) ==> ((\x. f (x + a)) diffl l) x`,
    let lem01 = CONJ (SPEC_ALL DIFF_X) (SPECL [`a:real`;`x:real`] DIFF_CONST) in
    let lem02 = BETA_RULE (MATCH_MP DIFF_ADD lem01) in
    let lem03 = ONCE_REWRITE_RULE [REAL_ARITH `&1 + &0 = &1`] lem02 in
    let lem04 = SPECL [`f:real->real`;`\(x:real).((x + a)):real`;`l:real`;`&1`] DIFF_CHAIN  in
    let MUL_ONE = REAL_ARITH `! x.(&1) * x = x /\ x * (&1) = x` in
    let lem05 = ONCE_REWRITE_RULE [MUL_ONE] (BETA_RULE lem04) in
    let lem06 = GEN_ALL (SIMP_RULE [lem03] lem05) in
    ACCEPT_TAC lem06
)
let POLY_DIFF_ADD_CONST_COMMUTE = PROVE(
    `! p1 p2 a.(!x.(poly p2 x) = (poly p1 (x-a)))
            ==> (!x . ((poly (poly_diff p2) x) = (poly (poly_diff p1) (x-a))))`,
    let lem01 = SPECL
                  [`\x.poly p1 x`;`-- a:real`;`l:real`;`x:real`]
                  DIFF_ADD_CONST_COMMUTE in
    let lem02 = ONCE_REWRITE_RULE [REAL_ARITH `w + --v = w - v`] (BETA_RULE lem01) in
    let lem03 = SPECL [`p1:(real)list`;`(x:real) -a`] POLY_DIFF in
    let lem04 = MATCH_MP lem02 lem03 in
    let lem05 = ASSUME `!x.poly p2 x = poly p1 (x - a)` in
    let lem06 = ONCE_REWRITE_RULE [GSYM lem05] lem04 in
    let lem07 = SPECL [`p2:(real)list`;`x:real`] POLY_DIFF in
    let lem08 = MATCH_MP DIFF_UNIQ (CONJ lem07 lem06)  in
    (REPEAT STRIP_TAC) THEN (ACCEPT_TAC lem08)
)

let HARD_WON = PROVE(
    `! p1 p2 a n.(!x.(poly p2 x) = (poly p1 (x-a)))
            ==> ((\x.poly (poly_diff_iter p2 n) x) = (\x.(poly (poly_diff_iter p1 n) (x - a)))) `,
    let lem = SPECL [`poly_diff_iter p1 n`;`poly_diff_iter p2 n`;`a:real`] POLY_DIFF_ADD_CONST_COMMUTE in
    let tm = `(!x . poly p2 x = poly p1 (x -a )) ==>
                   (\x.poly (poly_diff_iter p2 n) x) = (\x. poly (poly_diff_iter p1 n) (x - a))` in
    (STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC ) THEN
    (INDUCT_TAC) THENL
    [ SIMP_TAC [Pm_lemma1.PDI_DEF] ;
      STRIP_TAC THEN (ONCE_REWRITE_TAC [Pm_lemma1.PDI_DEF]) THEN (UNDISCH_TAC tm) THEN
      (ASM_REWRITE_TAC[FUN_EQ_THM]) THEN (ACCEPT_TAC lem)
    ]
)
(* if f:real->real is a function, let us call the function g x = f (x+a),
 * where a is a constant, a "shifting" of f by a.  if f is defined by a poly,
 * i.e. a (real)list, then (poly_shift f a) is the (real)list defining
 * the shifting of f by a.
 *)
let POLY_SHIFT_DEF = new_recursive_definition list_RECURSION
               `   (poly_shift [] a = [])
                /\ (poly_shift (CONS c t) a =
                   (CONS c (poly_shift t a)) ++ (a ## (poly_shift t a)))`

(* POLY_SHIFT simply says that poly_shift does what is supposed to do
 *)
let POLY_SHIFT = PROVE(
    `! p a x .(poly p (x + a)) = (poly (poly_shift p a) x)`,
    let lem01 = ASSUME `! a x . poly  t (x + a) = poly (poly_shift t a ) x` in
    LIST_INDUCT_TAC THENL
    [
     (ONCE_REWRITE_TAC [POLY_SHIFT_DEF;poly]) THEN (SIMP_TAC [poly]);
     (REPEAT STRIP_TAC) THEN (ONCE_REWRITE_TAC [POLY_SHIFT_DEF]) THEN
     (ONCE_REWRITE_TAC [POLY_ADD]) THEN (ONCE_REWRITE_TAC [POLY_CMUL]) THEN
     (ONCE_REWRITE_TAC [poly;GSYM lem01]) THEN
     (ONCE_REWRITE_TAC [GSYM lem01]) THEN (REAL_ARITH_TAC)
    ]
)
let POLY_SHIFT_LENGTH = PROVE(
    `! p a . (LENGTH (poly_shift p a)) = (LENGTH p)`,

    (LIST_INDUCT_TAC) THENL
    [ (SIMP_TAC [POLY_SHIFT_DEF]);
      (SIMP_TAC [POLY_SHIFT_DEF]) THEN
      (ASM_SIMP_TAC
        [LENGTH;POLY_CMUL_LENGTH;POLY_ADD_LENGTH;
         ARITH_RULE `MAX (x:num) y = if (x > y) then x else y`;
         ARITH_RULE `! n. SUC n >n`])
    ]
)
let POLY_TAYLOR = PROVE(
    `! p x a. poly p x =
              psum (0,LENGTH p) (\m.poly (poly_diff_iter p m) a/ &(FACT m) * (x - a) pow m)`,
    let lem01 = SPEC `poly_shift p a` POLY_MCLAURIN in
    let lem02 = SPECL [`p:(real)list`;`poly_shift p a`;`-- a:real`;`n:num`] HARD_WON in
    let lem03 = GSYM ( SPECL [`p:(real)list`;`a:real`] POLY_SHIFT) in
    let lem04 = SIMP_RULE [REAL_ARITH `a - --b = a + b`] lem02 in
    let lem05 = ONCE_REWRITE_RULE [ETA_AX] (MP lem04 lem03) in
    let lem06 = BETA_RULE (ONCE_REWRITE_RULE [lem05] lem01) in
    let lem07 = ONCE_REWRITE_RULE [REAL_ARITH `&0 + a = a`] lem06 in
    let lem08 = ONCE_REWRITE_RULE [GSYM POLY_SHIFT] lem07 in
    let lem09 = ONCE_REWRITE_RULE [POLY_SHIFT_LENGTH] lem08 in
    let lem10 = RATOR_CONV (ONCE_REWRITE_CONV [REAL_ARITH `(x:real) = (x + a) - a`]) `x pow m` in
    let lem11 = ONCE_REWRITE_RULE [lem10] lem09 in
    let lem12 = SPEC `(x - a):real` lem11 in
    let lem13 = ONCE_REWRITE_RULE [REAL_ARITH `(x:real) - a + a = x`] lem12 in
    ACCEPT_TAC (GEN_ALL lem13 )
)
let PLANETMATH_LEMMA_2_A = PROVE(
    `! p a x . poly p x =
       ((\s .psum (0,LENGTH p) ((\m.poly (poly_diff_iter p m) a/ &(FACT m) * (s m))))
         (\m.(x - a) pow m))`,
    BETA_TAC THEN (MATCH_ACCEPT_TAC POLY_TAYLOR)
)
let ITERATE_SUC_REC = PROVE(
    `!(op:D -> D -> D) m n (f:num -> D) .
              monoidal op ==>
              (m <= SUC n) ==>
              iterate op (m..(SUC n)) f
               = op (f (SUC n)) (iterate op (m..n) f)`,
    let lem0 = UNDISCH_ALL (SPEC_ALL (GSYM NUMSEG_REC)) in
    let lem1 = ISPEC `op:D -> D -> D` ITERATE_CLAUSES_GEN in
    let lem2 = CONJUNCT2 (UNDISCH lem1) in
    let lem3 = ISPECL [`f:(num -> D)`;`SUC n`;`m..n`] lem2 in
    let lem4 = SIMP_RULE [] (DISCH_ALL lem3) in
    let lem50 = PROVE(
        `!m n. ~((SUC n) IN (m..n))`,
        STRIP_TAC THEN (ONCE_REWRITE_TAC [IN_NUMSEG]) THEN ARITH_TAC) in
    let lem5 = SIMP_RULE [lem50;FINITE_SUPPORT;FINITE_NUMSEG] lem4 in
    let lem6 = ADD_ASSUM `m <= SUC n` lem5 in
    let lem7 = ONCE_REWRITE_RULE [lem0] lem6 in
    SIMP_TAC [lem7]
);;
```

### Informal statement
This theorem establishes the McLaurin series representation of a polynomial function. For any polynomial $p$ and real value $x$:
$$\text{poly}\ p\ x = \sum_{m=0}^{n-1} \frac{\text{poly}(\text{poly\_diff\_iter}\ p\ m)(0)}{m!} \cdot x^m$$
where:
- $\text{poly}\ p\ x$ evaluates the polynomial $p$ at point $x$
- $\text{poly\_diff\_iter}\ p\ m$ represents the $m$-th iterated derivative of polynomial $p$
- $\text{LENGTH}\ p$ is the length of the polynomial coefficient list
- $\text{FACT}\ m$ is the factorial of $m$

### Informal proof
The proof relies on the general McLaurin series expansion for real-valued differentiable functions, specialized to polynomial functions.

Main steps of the proof:
- Apply `MCLAURIN_ALL_LE` theorem to the polynomial function, using `poly_diff_iter` to express its higher derivatives.
- Use the properties of polynomial derivatives to establish that each term in the McLaurin expansion corresponds to evaluating the appropriate iterated derivative of the polynomial at 0, scaled by the factorial and power term.
- Show that for a polynomial of length $n$, the McLaurin series terminates exactly at the $(n-1)$-th term, as all higher derivatives become zero.
- Apply simplifications to convert the general McLaurin remainder formula to the exact polynomial representation.

The proof essentially shows that a polynomial can be perfectly represented by its McLaurin series, with no remainder term, which is a fundamental property of polynomials.

### Mathematical insight
This theorem expresses the fundamental connection between polynomials and their derivatives. It shows that a polynomial $p$ can be completely reconstructed from the values of its successive derivatives at zero.

The formula is a special case of Taylor's theorem for polynomials expanded around zero (McLaurin series). While Taylor's theorem applies to general smooth functions and typically includes a remainder term, for polynomials of degree $n-1$, the series is exact with exactly $n$ terms.

This result is particularly useful when manipulating or analyzing polynomials through their derivatives, such as in polynomial interpolation, numerical integration, or when studying polynomial approximations to other functions.

### Dependencies
- **Theorems:**
  - `MCLAURIN_ALL_LE`: Provides the general McLaurin series expansion for functions with derivatives
  - `DIFF_X`, `DIFF_CONST`, `DIFF_ADD`, `DIFF_CHAIN`, `DIFF_UNIQ`: Basic differential calculus theorems
  - `REAL_MUL_LZERO`: Real arithmetic property

- **Definitions:**
  - `diffl`: Differentiability of a function at a point
  - `PDI_DEF`: Recursive definition of iterated polynomial differentiation

### Porting notes
When porting this theorem:
1. Ensure that polynomial representation is compatible - HOL Light represents polynomials as lists of coefficients
2. The iterated differentiation operation (`poly_diff_iter`) needs to be defined with equivalent semantics
3. The factorial and power functions should have compatible definitions
4. Pay attention to the indexing convention - the formula sums from 0 to LENGTH(p)-1, which assumes coefficients are stored from lowest to highest degree

The theorem establishes several auxiliary results about polynomial shifts and derivatives that might need separate proofs in the target system.

---

## ITERATE_POLY_ADD_PRE_REC

### Name of formal statement
ITERATE_POLY_ADD_PRE_REC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ITERATE_POLY_ADD_PRE_REC = PROVE(
    `!f n . n > 0
        ==> iterate (++) (0..n) f = (f n) ++ (iterate (++) (0..n-1) f)`,
    MESON_TAC [ITERATE_CLAUSES_NUMSEG; MONOIDAL_POLY_ADD; POLY_ADD_SYM;
               ARITH_RULE `0 <= x`; ARITH_RULE `n > 0 ==> n = SUC (n - 1)`]
);;
```

### Informal statement
For any function $f$ and natural number $n > 0$, the iteration of polynomial addition (denoted by $\oplus$) over the range $[0..n]$ applied to $f$ can be expressed as:

$$\text{iterate}(\oplus, [0..n], f) = f(n) \oplus \text{iterate}(\oplus, [0..n-1], f)$$

where $\text{iterate}(\oplus, [0..n], f)$ represents applying polynomial addition to the sequence $f(0), f(1), \ldots, f(n)$.

### Informal proof
The proof is constructed by applying the following key results:

- We use the theorem about iterate clauses over numerical segments `ITERATE_CLAUSES_NUMSEG`.
- We use the fact that polynomial addition forms a monoidal operation (`MONOIDAL_POLY_ADD`).
- We use the symmetry of polynomial addition (`POLY_ADD_SYM`).
- We apply arithmetic facts: that $0 \leq x$ for any natural number $x$, and that if $n > 0$, then $n = \text{SUC}(n-1)$.

These results together establish that when $n > 0$, the iteration of polynomial addition over $[0..n]$ can be broken down into adding $f(n)$ to the iteration over $[0..n-1]$.

### Mathematical insight
This theorem provides a recursive characterization of polynomial addition iteration. It shows that we can compute the sum of polynomials in a range by adding the last element to the sum of all previous elements.

This is particularly useful for inductive reasoning about polynomial sums and for developing algorithms that operate on polynomial sums incrementally. It breaks down the sum over a range into a more manageable form, allowing for recursive computation and analysis.

The theorem is analogous to how list operations can be decomposed into operations on the last element and operations on the rest of the list, but specifically in the context of polynomial addition over a numerical range.

### Dependencies
- `ITERATE_CLAUSES_NUMSEG`: Provides properties about iterate over numerical segments
- `MONOIDAL_POLY_ADD`: Establishes that polynomial addition is a monoidal operation
- `POLY_ADD_SYM`: States that polynomial addition is symmetric
- `ARITH_RULE`: Used for basic arithmetic facts

### Porting notes
When porting this theorem:
- Ensure the destination system has a well-defined notion of polynomial addition and iteration over ranges.
- Verify that the polynomial addition operation in the target system has the same monoidal and symmetric properties.
- The iterate operation might be represented differently in other systems (e.g., as fold, reduce, or a specific summation operator for polynomials).

---

## PSUM_ITERATE

### PSUM_ITERATE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PSUM_ITERATE = PROVE(
    `! n m f. psum (m,n) f
              = if (n > 0) then (iterate (+) (m..((n+m)-1)) f) else &0`,
    let lem01 = ARITH_RULE `~(n+m=0) ==> (SUC n + m) -1 = SUC ((n + m) -1)` in
    let lem02 = MP (ISPEC `(+)` ITERATE_SING) MONOIDAL_REAL_ADD in
    let lem03 = PROVE(
          `iterate (+) (m..SUC ((n + m) - 1)) f
           = f (SUC ((n+m)-1)) + iterate (+) (m..(n+m)-1) f`,
           MESON_TAC [ARITH_RULE `m <= SUC ((n+m)-1)`;ITERATE_CLAUSES_NUMSEG;
                      MONOIDAL_REAL_ADD;REAL_ADD_SYM]) in
    let lem04 = UNDISCH (UNDISCH (ARITH_RULE `~(n+m=0) ==> n=0 ==> m-1 < m`)) in
    let lem05 = SIMP_RULE [lem04] (SPECL [`m:num`;`m-1`] NUMSEG_EMPTY) in
    INDUCT_TAC THENL
    [ SIMP_TAC [ARITH_RULE `~(0 > 0)`;sum_DEF];
      (SIMP_TAC [ARITH_RULE `(SUC n) > 0`]) THEN (REPEAT STRIP_TAC) THEN
      (ASM_CASES_TAC `n + m =0`) THENL
      [ (REWRITE_TAC [UNDISCH (ARITH_RULE `n + m = 0 ==> n = 0`)]) THEN
        (REWRITE_TAC [lem02;NUMSEG_SING;ARITH_RULE `(SUC 0 +m) -1 = m`]) THEN
        (MESON_TAC [sum_DEF; ADD_CLAUSES;REAL_ARITH `&0 + x = x`]) ;
        (ONCE_REWRITE_TAC [sum_DEF;UNDISCH lem01]) THEN
        (REWRITE_TAC [lem03]) THEN (ASM_CASES_TAC `n = 0`) THEN
        (ASM_SIMP_TAC
          [ARITH_RULE `~(0 > 0)`;ADD_CLAUSES;REAL_ADD_LID;REAL_ADD_RID;
           lem05;ITERATE_CLAUSES_GEN; MONOIDAL_REAL_ADD;NEUTRAL_REAL_ADD;
           REAL_ADD_SYM;ADD_SYM;ARITH_RULE `~(n=0) ==> n>0 /\ SUC (n-1) = n`])
      ]
    ]
);;
```

### Informal statement
For all natural numbers $n$ and $m$, and function $f$, the partial sum $\operatorname{psum}(m,n)(f)$ equals:
- If $n > 0$, then $\operatorname{iterate}(+)(m..((n+m)-1))(f)$, which is the sum of $f(k)$ for $k$ ranging from $m$ to $(n+m)-1$
- Otherwise (if $n \leq 0$), then $0$

### Informal proof
This theorem is proved by induction on $n$.

**Base case** ($n = 0$):
- When $n = 0$, the condition $n > 0$ is false, so $\operatorname{psum}(m,0)(f) = 0$
- This follows directly from the definition of `sum_DEF`

**Inductive case** ($n = \operatorname{SUC}(n')$):
- For $n = \operatorname{SUC}(n')$, we have $\operatorname{SUC}(n') > 0$, so the condition is true
- We consider two subcases:
  - Subcase 1: $n' + m = 0$
    - This implies $n' = 0$ (by arithmetic)
    - The result then simplifies to $f(m) + 0 = f(m)$, using properties of a singular iteration, which matches $\operatorname{psum}(m,1)(f)$
  
  - Subcase 2: $n' + m \neq 0$
    - Using the definition of partial sum and the lemma that $(SUC(n') + m) - 1 = SUC((n' + m) - 1)$
    - We rewrite the iteration as $f(SUC((n'+m)-1)) + \operatorname{iterate}(+)(m..(n'+m)-1)(f)$
    - Further, we consider whether $n' = 0$:
      - If $n' = 0$, we use properties of empty number segments and monoidal properties of addition
      - If $n' \neq 0$, we apply the inductive hypothesis and arithmetic simplifications

The proof relies on careful manipulation of numerical expressions and properties of iteration over numeric ranges.

### Mathematical insight
This theorem establishes the relationship between the partial sum function `psum` and the iterate operation on numeric ranges. The key insight is expressing the sum of a function over a range in terms of the iterate operation with addition, showing how both concepts align.

The result is important for formalizing summation operations, providing a way to convert between different representations of sums that may be more convenient in different contexts. It bridges the gap between the abstract partial sum and concrete iteration over numeric ranges.

### Dependencies
- `sum_DEF`: Definition of the partial sum
- `ITERATE_CLAUSES_NUMSEG`: Properties of iteration over numeric ranges
- `ITERATE_CLAUSES_GEN`: General properties of iteration
- `ITERATE_SING`: Property of iteration over a singleton set
- `MONOIDAL_REAL_ADD`: Monoidal properties of real addition
- `NUMSEG_EMPTY`: Properties of empty numeric segments
- `NUMSEG_SING`: Properties of singleton numeric segments
- `NEUTRAL_REAL_ADD`: Neutral element property for real addition

### Porting notes
When porting this theorem:
- Ensure that the target system has a compatible definition of partial sums and iteration over numeric ranges
- Be aware that the HOL Light representation of intervals like `m..n` may differ in other systems
- The proof relies on case analysis on whether certain sums equal zero, which might require explicit handling in systems with different arithmetic automation

---

## FACT_DIV_RCANCELS

### Name of formal statement
FACT_DIV_RCANCELS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FACT_DIV_RCANCELS = PROVE(
    `!n x. x / &(FACT n) * &(FACT n) = x`,
    MESON_TAC [REAL_ARITH `!x. &0 < x ==> ~(x = &0)`;
               REAL_DIV_RMUL;FACT_LT;REAL_OF_NUM_LT]
)
let PLANETMATH_LEMMA_2_B = PROVE(
    `! p (x:real) a . poly (SOD p) a =
       ((\s .psum (0,LENGTH p) ((\m.poly (poly_diff_iter p m) a/ &(FACT m) * (s m))))
         (\m. &(FACT m)))`,
    let lem6 = ISPECL [`(\i.poly_diff_iter p i)`;`LENGTH (p:(real)list)`]
                ITERATE_POLY_ADD_PRE_REC in
    let lem7 = UNDISCH lem6 in
    let lem8 = UNDISCH (ARITH_RULE `~(LENGTH (p:(real)list) > 0) ==> (LENGTH p = 0)`) in
    let lem9 = ONCE_REWRITE_RULE [LENGTH_EQ_NIL] lem8 in
    BETA_TAC THEN (REPEAT STRIP_TAC) THEN (ONCE_REWRITE_TAC [FACT_DIV_RCANCELS]) THEN
    (ONCE_REWRITE_TAC [PSUM_ITERATE]) THEN (ASM_CASES_TAC `LENGTH (p:(real)list) > 0`) THENL
    [ (ASM_SIMP_TAC [Pm_lemma1.SOD;Pm_lemma1.SODN;ITERATE_RADD_POLYADD;ARITH_RULE `x + 0 = x`]) THEN
      (AP_THM_TAC) THEN (AP_TERM_TAC) THEN (SIMP_TAC [lem7;Pm_lemma1.PDI_LENGTH_NIL;POLY_ADD_CLAUSES]);
      (ASM_SIMP_TAC []) THEN
      (SIMP_TAC
      [lem9;poly;Pm_lemma1.SOD;Pm_lemma1.SODN;NUMSEG_SING;MONOIDAL_POLY_ADD;ITERATE_SING;LENGTH;Pm_lemma1.PDI_DEF])
    ]
)
end;;
```

### Informal statement
For all natural numbers $n$ and real numbers $x$, we have:

$$x / (n!) \cdot (n!) = x$$

where $n!$ denotes the factorial of $n$.

### Informal proof
This theorem states that dividing by a factorial and then multiplying by the same factorial gives back the original value.

The proof uses:
- The fact that factorials are always positive integers, so $n! > 0$
- From real arithmetic, a positive real is never equal to zero
- The rule for dividing and then multiplying by the same value: if $y \neq 0$, then $(x/y) \cdot y = x$

These properties are combined using the `MESON_TAC` tactic with the following lemmas:
- `REAL_ARITH` to establish that positive numbers are non-zero
- `REAL_DIV_RMUL` which states that $(x/y) \cdot y = x$ when $y \neq 0$
- `FACT_LT` which shows that factorials are positive
- `REAL_OF_NUM_LT` which relates inequalities between natural numbers and their real counterparts

### Mathematical insight
This theorem captures a basic property of real number arithmetic involving factorials. It's essentially applying the general property of division followed by multiplication: $(x/y) \cdot y = x$ when $y \neq 0$, specifically in the case where $y = n!$.

This particular form is likely used in contexts involving power series expansions, Taylor series, or other analytical applications where terms often contain factorial denominators. The theorem is particularly useful in contexts where expressions contain $x/n!$ and need to be manipulated.

### Dependencies
#### Theorems
- `REAL_ARITH`: Real arithmetic simplification
- `REAL_DIV_RMUL`: Division and multiplication cancellation
- `FACT_LT`: Factorials are positive
- `REAL_OF_NUM_LT`: Numeric embedding preserves order

#### Definitions
- `PDI_DEF`: Defines iterative polynomial differentiation
- `SOD`: Sum of derivatives definition

### Porting notes
When porting this theorem:
1. Ensure your target system has appropriate arithmetic simplification for real numbers
2. Check that factorial definitions are compatible
3. The proof is straightforward and should translate easily to other systems with basic arithmetic reasoning

Most proof assistants will have simpler ways to prove this result, possibly as a direct application of division properties without needing to explicitly reference factorial properties.

---

## N_IS_INT

### N_IS_INT
- N_IS_INT

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let N_IS_INT = PROVE(
    `!n . integer (&n)`,
    MESON_TAC [is_int]
)
let NEG_N_IS_INT = PROVE(
    `!n . integer (--(&n))`,
    MESON_TAC [is_int]
);;
```

### Informal statement
For all natural numbers $n$, the real number $n$ is an integer.

More formally, for any natural number $n$, $\text{integer}(n)$ holds, where $\&n$ represents the embedding of the natural number $n$ into the real numbers.

### Informal proof
The proof follows directly from the `is_int` theorem, which likely states that natural numbers are integers. The proof uses the `MESON_TAC` tactic with `is_int` as its only reference.

### Mathematical insight
This theorem establishes the basic fact that natural numbers are integers, which is foundational in number theory. The embedding of natural numbers into the reals (denoted by $\&n$ in HOL Light) preserves their integer property. This is a fundamental relationship in the hierarchy of number systems.

The theorem is accompanied by `NEG_N_IS_INT`, which states that the negation of a natural number is also an integer. Together, these theorems establish that both positive and negative whole numbers are integers.

### Dependencies
- `is_int`: Definition or theorem establishing when a real number is an integer

### Porting notes
When porting to other proof assistants:
- Ensure that the natural-to-real coercion (represented by `&` in HOL Light) has an equivalent in your target system
- Check how the `integer` predicate is defined in the target system
- This should be a straightforward port if the number hierarchy is set up similarly

---

## PLANETMATH_EQN_3

### Name of formal statement
PLANETMATH_EQN_3

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PLANETMATH_EQN_3 = PROVE(
    `!f. 0 < nu
          ==> poly (SOD f) (&0) * exp (&nu) =
              poly (SOD f) (&nu) +
              &nu * exp (&nu - xi (&nu) f) * poly f (xi (&nu) f)`,
    let RW = SPECL [`0`;`nu:num`] REAL_OF_NUM_LT in
    ACCEPT_TAC (ONCE_REWRITE_RULE [RW] (SPEC `(&nu):real` Pm_lemma1.PLANETMATH_LEMMA_1))
)
(* the RHS of PLANETMATH_EQN_4
 *  TBD: mentioned in paper
 *)
let LHS = new_definition
        `LHS c f = sum (0..(PRE (LENGTH c))) (\i.(EL i c)*(poly (SOD f) (&i)))`

(* the LHS of PLANETMATH_EQN_4
 *  TBD: mentioned in paper
 *)
let RHS = new_definition
        `RHS  c f = -- sum (1..(PRE (LENGTH c)) )
                          (\i.  (&i)
                              * (EL i c)
                              * (exp ((&i) - (xi (&i) f)))
                              * (poly f (xi (&i) f))
                          )`

let E_POW_N = PROVE(
    `!n.(exp (real_of_num 1)) pow n = exp(&n)`,
    SIMP_TAC [GSYM REAL_EXP_N;REAL_MUL_RID])


(*  The proof was originally done with a slightly different transcendental
 *  predicate than found in Harrison's 100/liouville.ml it turns out the difference
 *  is that &0 satisfies my transcendental!  Thankfully, it is easy to show that
 *  e != 0, and hence the two notions of transcendence are equivalent for e.
 *  So that I could eliminate even brining my muddled definition of
 *  transcendental into the proof, this file ultimately proves
 *  E_TRANSCENDENTAL_EQUIV, which allows the main proof to only mention
 *  Harrison's transcendental predicate.
 *)

let NO_CONST_TERM_POLY_ROOT = PROVE(
    `!p . (~(x = &0) /\ ((HD p) = &0) /\ (poly p x = &0) /\ ~(p = []))
           ==> ((poly (TL p) x) = &0)`,
    LIST_INDUCT_TAC THEN
    (ASM_SIMP_TAC [HD;TL;NOT_CONS_NIL;poly]) THEN
    (MESON_TAC [REAL_ARITH `((&0):real) + x = x`;REAL_ENTIRE])
)

let NEGATED_POLY_ROOT = PROVE(
    `!p . (poly p x = &0) ==> (poly ((-- &1) ## p) x = &0)`,
    MESON_TAC [POLY_CMUL;REAL_ARITH `(-- &1) * ((&0):real) = &0`]
)

(*  changes a polynomial p to p/x^k, where k is the lowest power
 *  of x where p has a non-zero coefficient.  This amounts to
 *  just stripping off all leading zeros from the head of the list p.
 *)
let POLY_NUKE = new_recursive_definition list_RECURSION
               `   (poly_nuk [] = [])
                /\ (poly_nuk (CONS (c:real) t) =
                   (if (c = &0) then (poly_nuk t) else (CONS c t)))`

let POLY_NUKE_ROOT = PROVE(
    `!p . ((~(x = &0)) /\ (poly p x = &0)) ==> (poly (poly_nuk p) x = &0)`,
    LIST_INDUCT_TAC THENL
    [ SIMP_TAC[POLY_NUKE];
      (ASM_CASES_TAC `(h:real) = &0`) THEN
      (ASM_MESON_TAC [HD;TL;POLY_NUKE;NOT_CONS_NIL;NO_CONST_TERM_POLY_ROOT])
    ]
)
let POLY_NUKE_ZERO = PROVE(
    `!p . (poly p = poly []) <=> (poly (poly_nuk p) = poly [])`,
    LIST_INDUCT_TAC THEN (ASM_MESON_TAC [POLY_ZERO;ALL;POLY_NUKE])
)
let POLY_CONST_NO_ROOTS = PROVE(
    `! c.  ~(poly [c] = poly []) ==> ~(poly [c] x = &0)`,
    (MESON_TAC [poly;REAL_ENTIRE;POLY_ZERO;ALL;
                REAL_ARITH `(x:real) + &0 = x`;
                REAL_ARITH `(x:real) * &0 = &0`])
)
let LENGTH_1 = PROVE(
    `! lst . (LENGTH lst = 1) <=> (? x. lst = [x])`,
    LIST_INDUCT_TAC THEN
    (MESON_TAC [LENGTH;ARITH_RULE `SUC x = 1 <=> x = 0`;NOT_CONS_NIL;LENGTH_EQ_NIL])
)
let SOUP_LEMMA = PROVE(
    `!p . ~(x = &0) /\ ~(poly p = poly []) /\ (poly p x = &0)
            ==> LENGTH (poly_nuk p) > 1`,
    let l0 = ARITH_RULE `(~(n = 0) /\ ~(n = 1)) <=> n > 1` in
    let l1 = UNDISCH (UNDISCH (BRW1 (SPEC_ALL POLY_NUKE_ROOT))) in
    (ONCE_REWRITE_TAC [GSYM l0]) THEN (REPEAT STRIP_TAC) THENL
    [ (ASM_MESON_TAC [LENGTH;LENGTH_EQ_NIL;POLY_NUKE_ZERO]);
      (ASM_MESON_TAC [l1;POLY_CONST_NO_ROOTS;LENGTH_1;LENGTH;POLY_NUKE_ZERO]) ]
)

let POLY_NUKE_HD_NONZERO = PROVE(
    `!p . ~(poly p = poly []) ==> ~((HD (poly_nuk p)) = &0)`,
    LIST_INDUCT_TAC THEN (ASM_CASES_TAC `(h:real) = &0`) THEN
    (ASM_SIMP_TAC [HD;POLY_ZERO;ALL;POLY_NUKE])
)

let IS_INT_POLY_NUKE = PROVE(
    `!p . (ALL integer p) ==> (ALL integer (poly_nuk p))`,
    LIST_INDUCT_TAC THEN (ASM_MESON_TAC [ALL;POLY_NUKE;N_IS_INT])
)

let POLY_X_NOT_POLY_NIL = PROVE(
    `~(poly [&0;&1] = poly [])`,
    (SIMP_TAC [FUN_EQ_THM;POLY_X;poly;PROVE(`(~ ! x .P x) <=> (? x. ~ P x)`,MESON_TAC[])] )
    THEN (EXISTS_TAC `real_of_num 1`) THEN (REAL_ARITH_TAC)
)

let NOT_TRANSCENDENTAL_ZERO = PROVE(
      `~ (transcendental (&0))`,
      (REWRITE_TAC [transcendental;algebraic]) THEN
      (EXISTS_TAC `[&0 ; &1]:(real)list`) THEN
      (MESON_TAC [POLY_X;POLY_X_NOT_POLY_NIL;ALL;N_IS_INT])
)

let ALL_IS_INT_POLY_CMUL = PROVE(
    `! p c. (integer c) /\ (ALL integer p) ==> (ALL integer (c ## p))`,
    (LIST_INDUCT_TAC) THEN (ASM_SIMP_TAC [poly_cmul;ALL;INTEGER_MUL])
)

(*
 * Harrison's transcendental predicate from 100/liouville.ml is equivalent
 * to my predicate conjoined with x != 0.
 *)
let TRANSCENDENTAL_MY_TRANSCENDENTAL = PROVE(
    `!x. transcendental x <=>
         (~(x = &0) /\
             ~ ? c.     (ALL integer c)
                     /\ ((LENGTH c) > 1)
                     /\ ((poly c x) = &0)
                     /\ (HD c) > &0 )`,
    let contra_pos = TAUT `(~X ==> ~Y /\ ~Z) <=> ((Y \/ Z) ==> X)` in
    let contra_pos2 = TAUT `((~X /\ ~Y) ==> ~Z) <=> (Z ==> ~X ==> Y)` in
    let l0 = PROVE(`!c . LENGTH c > 1 ==> HD c > &0 ==> ~(poly c = poly [])`,
                   LIST_INDUCT_TAC THEN
                   (ASM_MESON_TAC [LENGTH_EQ_NIL;ARITH_RULE `n > 1 ==> ~(n = 0)`;
                                   REAL_ARITH `(x:real) > &0 ==> ~(x = &0)`;
                                   HD;ALL;POLY_ZERO])) in
    let witness = `if ((&0) <= (HD (poly_nuk p)))
                   then (poly_nuk p)
                   else ((-- &1) ## (poly_nuk p))` in
    let l2 = REAL_ARITH `!(x:real). (&0 <= x) /\ ~(x = &0) ==> x > &0` in
    let l3 = PROVE( `! c p. LENGTH (c ## p) =  LENGTH p`,
                    STRIP_TAC THEN LIST_INDUCT_TAC THEN
                    (ASM_SIMP_TAC [poly_cmul;LENGTH])) in
    let POLY_CMUL_HD = PROVE(
        `! x p . (~(p = [])) ==> HD (x ## p) = x * (HD p)`,
        STRIP_TAC THEN LIST_INDUCT_TAC THEN (SIMP_TAC [NOT_CONS_NIL;poly_cmul;HD])
    ) in
    (REWRITE_TAC [transcendental;algebraic]) THEN
    (STRIP_TAC THEN EQ_TAC) THENL
    [ (ONCE_REWRITE_TAC [contra_pos]) THEN STRIP_TAC THENL
      [ASM_MESON_TAC [transcendental;algebraic; NOT_TRANSCENDENTAL_ZERO];
      (EXISTS_TAC `c:(real)list`) THEN
      (ASM_MESON_TAC [l0; NOT_TRANSCENDENTAL_ZERO  ])];
      (REWRITE_TAC [contra_pos2]) THEN
      (STRIP_TAC THEN STRIP_TAC) THEN (ASM_SIMP_TAC [IS_INT_POLY_NUKE]) THEN
      (EXISTS_TAC witness) THEN
      (ASM_CASES_TAC `((&0) <= (HD (poly_nuk p)))`) THEN
      (ASM_MESON_TAC [ IS_INT_POLY_NUKE;ALL_IS_INT_POLY_CMUL;NEG_N_IS_INT;
                       l2;POLY_NUKE_HD_NONZERO;NEGATED_POLY_ROOT;SOUP_LEMMA;
                       l3;POLY_NUKE_ROOT;POLY_NUKE_ZERO;POLY_CMUL_HD;
                       REAL_ARITH `~(&0 <= (x:real)) <=> ((-- &1) * x) > &0`])
    ]
)

let E_TRANSCENDENTAL_EQUIV = PROVE(
    `(transcendental (exp (&1))) <=>
     (~ ? c.  (ALL integer c)
           /\ ((LENGTH c) > 1)
           /\ ((poly c (exp (&1))) = &0)
           /\ (HD c) > &0 )`,
    MESON_TAC[TRANSCENDENTAL_MY_TRANSCENDENTAL;
              REAL_EXP_POS_LT; REAL_ARITH `&0 < (x:real) ==> ~(&0 = x)`]
)

(* TBD mentionedin paper *)
let PLANETMATH_EQN_4 =  PROVE(
    `(~ (transcendental (exp (&1)))) ==> ? c .
          ((ALL integer c) /\ ((LENGTH c) > 1) /\ ((EL 0 c) > &0) /\ (! f .((LHS c f) = (RHS c f))))`,
     let foo2 = PROVE( `(HD c) > (real_of_num 0) ==> EL 0 c > &0`,SIMP_TAC [EL]) in
     let lem01 = SPECL [`f:num->real`;`0`;`0`;`PRE (LENGTH (c:(real)list))`] SUM_COMBINE_R in
     let lem02 = ARITH_RULE `(0 <= 0 + 1 /\ 0 <= (PRE (LENGTH (c:(real)list))))` in
     let lem03 = GSYM (MP lem01 (lem02) ) in
     let lem06 = ISPECL [`f1:num->real`;
                         `f2:num->real`;
                         `1`;`(PRE (LENGTH (c:(real)list)))`] SUM_ADD in
     let new0 = SPECL [`f:num->real`;`1`;`PRE (LENGTH (c:(real)list))`] PSUM_SUM_NUMSEG in
     let new1 = SIMP_RULE [ARITH_RULE `~(1 = 0)`;ARITH_RULE `(1 + x) -1 = x`] new0 in
     let new2 = ONCE_REWRITE_RULE [new1] lem06 in
     let lem001 = REAL_ARITH `((A:real) * B * C * D + B * E) = (B * (A * C * D + E))` in
     let lem0 = REAL_ARITH `(x:real) =  x * (&1) - (&0) * y` in
     let lem1 = GEN_ALL (ONCE_REWRITE_RULE [GSYM REAL_EXP_0] lem0) in
     let lem2 = SPECL [`poly (SOD f) (&0)`;
                       ` exp (&0 - xi (&0) f) * poly f (xi (&0) f)`] lem1 in
     let PLANETMATH_EQN_3_TWEAKED =
         REWRITE_RULE
           [REAL_ARITH `((A:real) = B+C) <=> (B = A -C)`]
           PLANETMATH_EQN_3
     in
     let lem21 = GEN `nu:num` (SPEC_ALL PLANETMATH_EQN_3_TWEAKED) in
     let lem3 = CONJ lem21 lem2 in
     let NUM_CASES_LEMMA = PROVE(
         ` !P .((! n .(0 < n) ==> (P n)) /\ (P 0) ==> ! n . P n)`,
         (REPEAT STRIP_TAC) THEN (SPEC_TAC (`n:num`,`n:num`)) THEN
         INDUCT_TAC THEN (ASM_SIMP_TAC[]) THEN
         (ASM_SIMP_TAC [ARITH_RULE `0 < (SUC n)`])) in
     let lem4 = SPEC `(\nu.poly (SOD f) (&nu) = poly (SOD f) (&0) * exp (&nu) - &nu * (exp ((&nu) - xi (&nu) f)) * poly f (xi (&nu) f))` NUM_CASES_LEMMA in
     let lem5 = BETA_RULE lem4 in
     let lem6 = MP lem5 lem3 in
     let lem100 =
         SIMP_RULE
           [ARITH_RULE `!n.0 <= n`;ARITH_RULE `(0:num) + 1 = 1`]
           (ISPECL [`f:num->real`;`0`;`0`;`PRE (LENGTH (c:(real)list))`] SUM_COMBINE_R) in
     let lem0001 = ASSUME `LENGTH (c:(real)list) > 1` in
     let lem0002 = MATCH_MP (ARITH_RULE `(x:num) > 1 ==> ~(x=0)`) lem0001 in
     let lem0003 =  REWRITE_RULE [LENGTH_EQ_NIL] lem0002 in
     let lem0004 = MATCH_MP  POLY_SUM_EQUIV lem0003 in
     let SUM_LMUL_NUMSEG = GEN_ALL (ISPECL [`f:num->real`;`c:real`;`n..m`] SUM_LMUL) in
     (ONCE_REWRITE_TAC [E_TRANSCENDENTAL_EQUIV]) THEN
     (ONCE_REWRITE_TAC [LHS;RHS]) THEN
     (REPEAT STRIP_TAC) THEN
     (EXISTS_TAC `c:(real)list`) THEN
     (ONCE_REWRITE_TAC [GSYM REAL_RNEG_UNIQ]) THEN
     (ONCE_REWRITE_TAC [lem03]) THEN
     (ONCE_REWRITE_TAC [NUMSEG_CONV `0..0`]) THEN
     (ONCE_REWRITE_TAC [SUM_SING] ) THEN
     (ASM_SIMP_TAC[foo2]) THEN
     (BETA_TAC) THEN
     (ONCE_REWRITE_TAC [ARITH_RULE `0 + 1 = 1`] ) THEN
     (ONCE_REWRITE_TAC [REAL_ARITH `(A:real) + B + C = (A + C) + B`] ) THEN
     (ONCE_REWRITE_TAC [GSYM new2]) THEN
     (BETA_TAC) THEN
     (ONCE_REWRITE_TAC [lem001]) THEN
     (CONV_TAC ((RAND_CONV o ABS_CONV o RATOR_CONV o RAND_CONV o RATOR_CONV) (PURE_ONCE_REWRITE_CONV [lem6]))) THEN
     (ONCE_REWRITE_TAC [REAL_ARITH `(A:real) + B - A = B`]) THEN
     (ONCE_REWRITE_TAC [REAL_ARITH `(EL 0 c) * (poly (SOD f) (&0))  = (EL 0 c) * (poly (SOD f) (&0)) * (&1)`]) THEN
     (ONCE_REWRITE_TAC [GSYM REAL_EXP_0]) THEN
     (ONCE_REWRITE_TAC [GSYM (BETA_CONV `(\x.(EL x c) * (poly (SOD f) (&0)) * exp (&x)) (0)`)]) THEN
     (ONCE_REWRITE_TAC [GSYM (ISPEC `\x.(EL x c) * (poly (SOD f) (&0)) * exp (&x)` SUM_SING)]) THEN
     (ONCE_REWRITE_TAC [GSYM (NUMSEG_CONV `0..0`)]) THEN
     (ONCE_REWRITE_TAC [REAL_ADD_AC]) THEN
     (ONCE_REWRITE_TAC [lem100]) THEN
     (ONCE_REWRITE_TAC [REAL_ARITH `(A:real) * B * C = B * A * C`]) THEN
     (ONCE_REWRITE_TAC [ SUM_LMUL_NUMSEG ]) THEN
     (ONCE_REWRITE_TAC [GSYM E_POW_N]) THEN
     (ONCE_REWRITE_TAC [GSYM lem0004]) THEN
     (ASM_SIMP_TAC[]) THEN
     (REAL_ARITH_TAC)
     )

end;;
```

### Informal statement
For any function $f$ and positive natural number $\nu$, the following equation holds:
$$\text{poly}(\text{SOD}(f))(\,0\,) \cdot e^{\nu} = \text{poly}(\text{SOD}(f))(\,\nu\,) + \nu \cdot e^{\nu - \xi(\nu, f)} \cdot \text{poly}(f)(\xi(\nu, f))$$

Where:
- $\text{poly}(p)(x)$ represents the evaluation of polynomial $p$ at point $x$
- $\text{SOD}(f)$ is a derivative-based transformation of function $f$
- $\xi(\nu, f)$ is a point related to function $f$ and number $\nu$
- $e^x$ represents the exponential function

### Informal proof
The proof is straightforward. It starts by defining `RW` as a specialized version of the real number inequality theorem `REAL_OF_NUM_LT` for numbers 0 and $\nu$, establishing that $0 < \nu$.

Then, the proof applies a rewrite using `RW` to a more general theorem called `PLANETMATH_LEMMA_1` (from the module `Pm_lemma1`), which has already established the desired equation. This is done by specializing the lemma with the real number value of $\nu$.

In essence, this theorem is a direct consequence of a previously proven, more general result.

### Mathematical insight
This equation is part of a sequence of results leading to the proof that $e$ is transcendental. It relates polynomial evaluations at different points through exponential functions.

The equation provides a specific relationship between:
1. The polynomial evaluation of $\text{SOD}(f)$ at 0, scaled by $e^{\nu}$
2. The polynomial evaluation of $\text{SOD}(f)$ at $\nu$
3. A correctional term involving the original function evaluated at a special point $\xi(\nu, f)$

This relationship is crucial in the transcendence proof because it connects polynomial behavior with exponential function properties in a way that will later create a contradiction if $e$ were algebraic.

### Dependencies
- `REAL_OF_NUM_LT` - Theorem about inequality between real numbers converted from natural numbers
- `Pm_lemma1.PLANETMATH_LEMMA_1` - A more general form of the equation proven elsewhere

### Porting notes
When implementing this in other proof assistants:
1. Ensure that the `SOD` and `xi` functions are properly defined first
2. The proof relies on the more fundamental `PLANETMATH_LEMMA_1`, so that result needs to be ported first
3. The notation for polynomial evaluation might differ in other systems

---

## POLY_MUL_ITER

### Name of formal statement
POLY_MUL_ITER

### Type of the formal statement
new_recursive_definition

### Formal Content
```ocaml
let POLY_MUL_ITER = new_recursive_definition num_RECURSION
    `(poly_mul_iter f 0 = [&1]) /\
     (!n . poly_mul_iter f (SUC n) = (f (SUC n)) ** (poly_mul_iter f n))`

let PLANETMATH_EQN_5 =
    new_definition
      `g n p  = (&1/(&(FACT (p  -1)))) ##
                   ((poly_exp [&0;&1] (p-1)) **
                       (poly_exp (poly_mul_iter (\i.[-- &i; &1]) n) p))`

end;;
```

### Informal statement
For a function $f : \mathbb{N} \to \text{polynomial}$, the recursive function `poly_mul_iter` is defined as:

$$\text{poly\_mul\_iter}(f, 0) = [1]$$

$$\text{poly\_mul\_iter}(f, n+1) = f(n+1) \cdot \text{poly\_mul\_iter}(f, n)$$

where $[1]$ represents the constant polynomial 1, and $\cdot$ represents polynomial multiplication.

### Informal proof
This is a recursive definition created using `num_RECURSION`, which allows defining functions by primitive recursion over natural numbers. The definition consists of:

- Base case: When $n=0$, the result is the constant polynomial $[1]$.
- Recursive case: For $n+1$, we multiply the polynomial $f(n+1)$ with the previously computed result for $n$.

The definition sets up a way to iteratively multiply a sequence of polynomials produced by the function $f$.

### Mathematical insight
This definition creates a mechanism for multiplying a sequence of polynomials together, with each polynomial determined by the function $f$ applied to successive natural numbers.

The pattern is effectively computing:
$$\text{poly\_mul\_iter}(f, n) = f(n) \cdot f(n-1) \cdot \ldots \cdot f(2) \cdot f(1) \cdot [1]$$

This is useful in polynomial manipulation contexts, particularly when working with products of polynomials with a specific pattern. The related definition `PLANETMATH_EQN_5` suggests this might be used in a context related to polynomial exponentiation and factorial calculations, possibly for generating special classes of polynomials or series expansions.

### Dependencies
No specific dependencies were provided in the input.

### Porting notes
When porting this definition:
- Ensure the target system has appropriate support for polynomial operations, particularly multiplication (denoted by `**` in HOL Light).
- Verify that primitive recursion over natural numbers is properly supported.
- The constant polynomial $[1]$ might be represented differently in other systems - adjust accordingly.

Note that `PLANETMATH_EQN_5` is defined in the same block but appears to be a separate definition that depends on `POLY_MUL_ITER`. When porting, you may need to port both definitions to maintain functionality.

---

## ABS_LE_MUL2

### Name of formal statement
ABS_LE_MUL2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ABS_LE_MUL2 = PROVE(
  `!(w:real) x y z. abs(w) <= y /\ abs(x) <= z ==> abs(w * x) <= (y * z)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_REWRITE_TAC[ABS_POS])

let SEPTEMBER_2009_LEMMA = PROVE(
    `!x f n n'.
    (!i.(0 <= i /\ i <= n) ==> (abs (poly (f i) x)) <= &(n')) ==>
    (abs (poly (poly_mul_iter f n) x)) <= (&(n') pow n)`,
    let lem0 = ASSUME `!i. 0 <= i /\ i <= SUC n ==> abs (poly (f i) x) <= &n'` in
    let lem1 = SPEC `SUC n` lem0 in
    let lem2 = SIMP_RULE [ARITH_RULE `0 <= SUC n /\ SUC n <= SUC n`] lem1 in
    let lem3 = PROVE(`(!i:num.(P0 i) ==> (P1 i)) ==> (!i:num.((P1 i) ==> (Q i))) ==> (!i:num.((P0 i) ==> (Q i)))`, MESON_TAC[]) in
    let lem4 = ARITH_RULE `!i.(0 <= i /\ i <= n) ==> (0 <= i /\ i <= SUC n)` in
    let lem5 = GEN `Q:num->bool` (MATCH_MP lem3 lem4) in
    let lem6 = ASSUME `!n'. (!i. 0 <= i /\ i <= n ==> abs (poly (f i) x) <= &n') ==> abs (poly (poly_mul_iter f n) x) <= &n' pow n` in
    let lem7 = SPEC `n':num` lem6 in
    let lem9 = UNDISCH (BETA_RULE (SPEC `\i. abs (poly (f (i:num)) x) <= &n'` lem5)) in
    let lem11 = MP (lem7) (lem9) in
    STRIP_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
    [ (REWRITE_TAC ([Pm_eqn5.POLY_MUL_ITER;poly;real_pow]@rewrites0))
      THEN (REAL_ARITH_TAC);
      (STRIP_TAC) THEN (STRIP_TAC) THEN
      (REWRITE_TAC [Pm_eqn5.POLY_MUL_ITER;POLY_MUL;real_pow]) THEN
      (MATCH_MP_TAC ABS_LE_MUL2) THEN
      (SIMP_TAC [lem2;lem11])
    ]
)
let SEPTEMBER_2009_LEMMA_2 = PROVE(
    `&0 < x /\ x < &n
      ==> (!i. 0 <= i /\ i <= n ==> abs(poly [-- &i; &1] x) <= &n)`,
    (REWRITE_TAC [GSYM REAL_LE]) THEN (REPEAT STRIP_TAC) THEN
    (REWRITE_TAC ([poly]@rewrites0)) THEN
    (REWRITE_TAC [REAL_ARITH `&0 <= -- &i + (x:real) <=>  &i <= x`;real_abs]) THEN (ASM_CASES_TAC `&i <= (x:real)`) THENL
    [ (ASM_SIMP_TAC []) THEN
      (REWRITE_TAC [REAL_ARITH `-- &i + (x:real) =  x - &i `]) THEN
      (ASM_REAL_ARITH_TAC);
      (ASM_SIMP_TAC []) THEN
      (REWRITE_TAC [REAL_ARITH `--(-- &i + (x:real)) =  &i - x `]) THEN
      (ASM_REAL_ARITH_TAC)
    ]
)

let FACT_DIV_LCANCELS = PROVE(
    `!n x.  &(FACT n) * x / &(FACT n)  = x`,
    let lem0 = SPECL [`0`;`FACT n`] REAL_OF_NUM_LT in
    let lem1 = ONCE_REWRITE_RULE [GSYM lem0] FACT_LT in
    let lem2 = SPECL [`x:real`;`(&(FACT n)):real`] REAL_DIV_LMUL in
    let lem3 = REAL_ARITH `!x:real. &0 < x ==> ~(x = &0)` in
    let lem4 = MATCH_MP lem3 (SPEC_ALL lem1) in
    ACCEPT_TAC (GEN_ALL (MP lem2 lem4))
)
let NOVEMBER_LEMMA_1 = PROVE(
    `p > 1 ==>
      &0 < x /\ x < &n ==>
       (abs(poly (g n p) x)) <=
           (&1/(&(FACT (p  -1)))) * ((&n) pow (p - 1)) * ((&n pow n) pow p)`,
   let l0 = SPECL [`0`;`FACT (p-1)`] REAL_OF_NUM_LT in
   let l2 = snd (EQ_IMP_RULE l0) in
   let l3 = MP l2 (SPEC `(p:num) - 1` FACT_LT)  in
   let l4 = SPEC `(&(FACT (p - 1))):real` REAL_LE_LCANCEL_IMP in
   let l5 = SIMP_RULE [l3] l4 in
   let ll0 = snd (EQ_IMP_RULE (SPEC_ALL REAL_ABS_REFL)) in
   let ll1 = IMP_TRANS (REAL_ARITH `(&0):real < x ==> &0 <= x`) ll0 in
   let ll2 = UNDISCH ll1 in
   let asses = [`(p:num) > 1`;`&0 < (x:real)`; `(x:real) < &n`] in
   let j0 = SPECL [`p - 1`;`x:real`;`(&n):real`] REAL_POW_LE2 in
   let j1 = REAL_ARITH `(&0) < (x:real) /\ x < (&n) ==> (&0 <=x /\ x <= (&n))` in
   let j2 = UNDISCH_ALL (BRW1 (IMP_TRANS j1 j0)) in
   let ll4 = SPECL [`(x:real) pow (p - 1)`;`((&n):real) pow (p - 1)`;`(abs (r:real)) pow p`] REAL_LE_MUL2 in
   let ll5 = (SPECL [`x:real`;`(p:num) - 1`] REAL_POW_LE) in
   let ll50 = UNDISCH (IMP_TRANS (REAL_ARITH `&0 < x ==> (&0) <= (x:real)`) ll5;) in
   let ll6  = ADD_ASSUMS asses ll4 in
   let ll7 = REAL_ARITH `(x:real) < y ==> x <= y` in
   let ll8 = SIMP_RULE [j2;ll50;ll7;REAL_POW_LE;REAL_ABS_POS] ll6 in
   let ll9 = ADD_ASSUM `p > 1` (SPEC `p:num` REAL_POW_LE2) in
   let ll10 = UNDISCH (ARITH_RULE `p > 1 ==> ~(p = 0)`) in
   let ll11 = SIMP_RULE [ll10] ll9 in
   let ll12 = SPEC `abs (r:real)` ll11 in
   let ll13 = SIMP_RULE [REAL_ABS_POS] ll12 in
   let lem0 = UNDISCH (UNDISCH (BRW1 SEPTEMBER_2009_LEMMA_2)) in
   let lem1 = MATCH_MP SEPTEMBER_2009_LEMMA lem0 in
   let lem2 = DISCH_ALL (DISCH `(&0) < (x:real)` lem1) in
   let lem3 = SPEC `SUC n` (GEN (`n:num`) lem2) in
   (STRIP_TAC) THEN (STRIP_TAC) THEN
   (ONCE_REWRITE_TAC [Pm_eqn5.PLANETMATH_EQN_5]) THEN
   (ONCE_REWRITE_TAC [POLY_CMUL]) THEN
   (ONCE_REWRITE_TAC [POLY_MUL]) THEN
   (ONCE_REWRITE_TAC [POLY_EXP]) THEN
   (ONCE_REWRITE_TAC [poly]) THEN
   (ONCE_REWRITE_TAC [poly]) THEN
   (ONCE_REWRITE_TAC [poly]) THEN
   (REWRITE_TAC rewrites0) THEN
   (ONCE_REWRITE_TAC [REAL_ABS_MUL]) THEN
   (ONCE_REWRITE_TAC [REAL_ABS_MUL]) THEN
   (ONCE_REWRITE_TAC [REAL_ABS_POW]) THEN
   (ONCE_REWRITE_TAC [REAL_ABS_DIV]) THEN
   (ONCE_REWRITE_TAC [ABS_N]) THEN
   (MATCH_MP_TAC l5) THEN
   (ONCE_REWRITE_TAC [REAL_MUL_ASSOC]) THEN
   (SIMP_TAC [FACT_DIV_LCANCELS;REAL_ARITH `&1 * (x:real) = x`]) THEN
   (SIMP_TAC [ll2]) THEN
   (MATCH_MP_TAC ll8) THEN
   (MATCH_MP_TAC ll13) THEN
   (UNDISCH_TAC `&0 < (x:real)`) THEN
   (UNDISCH_TAC `(x:real) < &n`) THEN
   (SPEC_TAC (`n:num`,`n:num`)) THEN
   INDUCT_TAC THENL [(REAL_ARITH_TAC); (ACCEPT_TAC lem3)]
)

let NOVEMBER_LEMMA_2 = PROVE(
    ` 1 <= v /\ v <= n
       ==> ((&0) < ( xi (&v) f)  /\ (xi (&v) f) < (&n))`,
    let l0 = SPECL [`(&v):real`;`f:(real)list`] Pm_lemma1.xi_DEF in
    let l1 = UNDISCH (ONCE_REWRITE_RULE [REAL_OF_NUM_LT] l0) in
    let [l2;l3;_] = CONJUNCTS l1 in
    let l4 = GEN_ALL (REAL_ARITH `(&v) <= y ==> z < (&v) ==> (z:real) < y`) in
    let l6 = SPECL [`v:num`;`z:real`;`(&n):real`] l4 in
    let l7 = UNDISCH  l6 in
    (ONCE_REWRITE_TAC [ TAUT `(X /\ Y ==> Z) <=> (X ==> Y ==> Z)`;ARITH_RULE `1 <= v <=> 0 < v` ]) THEN
    (ONCE_REWRITE_TAC [GSYM REAL_OF_NUM_LE;GSYM REAL_OF_NUM_LT]) THEN
    (STRIP_TAC) THEN (STRIP_TAC) THEN (SIMP_TAC [l2]) THEN
    (MATCH_MP_TAC l7) THEN (ACCEPT_TAC  l3)
)

let REAL_LE_MUL3 = PROVE(
    `! w0 x0 y0 w1 x1 (y1:real).
     (&0 <= w0) ==> (&0 <= x0) ==> (&0 <= y0) ==>
     (w0 <= w1) ==> (x0 <= x1) ==> (y0 <= y1) ==>
     (w0 * x0 * y0) <= (w1 * x1 * y1)`,
     let lst = [`w0:real`;`w1:real`;`(x0 * y0):real`;`(x1 * y1):real`] in
     let c0 = SPECL lst REAL_LE_MUL2 in
     MESON_TAC [c0;REAL_LE_MUL2;REAL_LE_MUL]
)

let MAX_ABS_DEF =
    new_recursive_definition list_RECURSION
       `    (max_abs [] = &0)
        /\  (max_abs (CONS h t) = real_max (real_abs h) (max_abs t))`

let MAX_ABS_LE = PROVE(
    `! cs i.
     (0 <= i /\ i < (LENGTH cs) ==>
       (real_abs (EL i cs)) <= (max_abs cs))`,
    let l0 = UNDISCH (REAL_ARITH `~((abs h) <= max_abs t) ==> x <= (max_abs t) ==> x <= (abs h)`) in
    LIST_INDUCT_TAC THENL
    [ (SIMP_TAC [LENGTH]) THEN ARITH_TAC;
      INDUCT_TAC THENL
      [ (SIMP_TAC [HD;EL;MAX_ABS_DEF;REAL_MAX_MAX]);
        (SIMP_TAC [TL;EL;MAX_ABS_DEF;REAL_MAX_MAX;LENGTH;LT_SUC]) THEN
        (ASM_CASES_TAC `(real_abs h) <= (max_abs t)`) THEN
        (ASM_SIMP_TAC [real_max;ARITH_RULE `0 <= y`;l0])
      ]
    ]
)
let KEATS_PART_1 = PROVE(
    `1 <= i /\ i <= PRE (LENGTH c) ==> ( &i * abs (EL i c) <= &i * max_abs c)`,
    let keats12 = ARITH_RULE `1 <= i /\ i <= (PRE (LENGTH (c:(real)list))) ==> (0 <= i /\ i < LENGTH c)` in
    let keats13 = IMP_TRANS keats12 (SPECL [`c:(real)list`;`i:num`] MAX_ABS_LE) in
    let keats14 = SPECL [`real_of_num i`] REAL_LE_LMUL in
    let keats15 = ARITH_RULE `(&0) <= (real_of_num i)` in
    let keats16 = SIMP_RULE [keats15] keats14 in
    let keats17 = UNDISCH keats13 in
    let keats18 = MATCH_MP keats16 keats17 in
    ACCEPT_TAC (DISCH_ALL keats18)
)
let KEATS_PART_2 = PROVE(
    `(1 <= v /\ v <= PRE (LENGTH (c:(real)list))) ==>
       abs (exp ((&v) - xi (&v) (g (PRE (LENGTH c)) p))) <= abs (exp (&(PRE (LENGTH (c:(real)list)))))`,
    let j0 = ASSUME `1 <= v /\ (v:num) <= (PRE (LENGTH (c:(real)list)))` in
    let j00 = ONCE_REWRITE_RULE [GSYM REAL_OF_NUM_LE] (CONJUNCT2 j0) in
    let j1 = REAL_ARITH `!n .(real_of_num v <= &n) ==> (&0 > --xi (&v) (g n p)) ==> (&n) > (&v) - (xi (&v) (g n p))` in
let j2 = MP (SPEC `PRE (LENGTH (c:(real)list))` j1) j00 in
    let g_term = `g (PRE (LENGTH (c:(real)list))) p` in
    let k33 = SPEC `PRE (LENGTH (c:(real)list))` (GEN `n:num` NOVEMBER_LEMMA_2) in
    let k34 = SPEC g_term (GEN `f:(real)list` k33) in
    let k35 = DISCH `1 <= v /\ v <= (PRE (LENGTH (c:(real)list)))` (CONJUNCT1 (UNDISCH k34)) in
    let k36 = UNDISCH (SPEC `PRE (LENGTH (c:(real)list))` (GEN `n:num` k35)) in
    let k37 = REAL_ARITH `!x. (real_of_num 0) < x ==> (real_of_num 0) > -- x` in
    let k38 = MATCH_MP k37 k36 in
    let k40 = MP j2 k38 in
    let k41 = REAL_ARITH `!x (y:real).x > y ==> y <= x` in
    let k42 = MATCH_MP k41 k40 in
    let k42 = ONCE_REWRITE_RULE [GSYM REAL_EXP_MONO_LE] k42 in
    let k43 = REAL_ARITH `!(x:real) . (&0) <= x ==> abs x = x` in
    let k44 = GEN `x:real` (MATCH_MP k43 (SPEC `x:real` REAL_EXP_POS_LE)) in
    let k45 = ONCE_REWRITE_RULE [GSYM k44] k42 in
    let k46 = DISCH_ALL k45 in
    let k47 = BRW0 (SIMP_RULE [ARITH_RULE `0 < v <=> 1 <= v`] k46) in
    ACCEPT_TAC k47
)
let KEATS_PART_3 =
    UNDISCH
    (PROVE(
    `p > 1 ==> (1 <= i /\ i <= PRE (LENGTH (c:(real)list)))
     ==> abs (poly (g (PRE (LENGTH c)) p) (xi (&i) (g (PRE (LENGTH c)) p))) <=
         &1 / &(FACT (p - 1)) *
         &(PRE (LENGTH c)) pow (p - 1) *
         &(PRE (LENGTH c)) pow PRE (LENGTH c) pow p`,
    let k0 = UNDISCH NOVEMBER_LEMMA_2 in
    let k1 = UNDISCH NOVEMBER_LEMMA_1 in
    let k2 = GEN `x:real` k1 in
    let k3 = SPEC `xi (real_of_num i) f` k2 in
    let k5 = MATCH_MP k3 k0 in
    let g_term = `g (PRE (LENGTH (c:(real)list))) p` in
    let k6 = SPEC g_term (GEN `f:(real)list` k5) in
    let k7 = SPEC `PRE (LENGTH (c:(real)list))` (GEN `n:num` (DISCH `1 <= v /\ v <= n` k6)) in
    let k8 = DISCH `0 < v` k7 in
    let k9 = BRW0 (SIMP_RULE [ARITH_RULE `0 < v <=> 1 <= v`] k8) in
    MATCH_ACCEPT_TAC (DISCH_ALL k9)
))

let RHS_4_F5_LE_SUM = PROVE(
    `abs (RHS c (g (PRE (LENGTH c)) p)) <=
     sum (1..PRE (LENGTH c))
     (\i. &i *
          abs (EL i c) *
          abs (exp (&i - xi (&i) (g (PRE (LENGTH c)) p))) *
          abs
          (poly (g (PRE (LENGTH c)) p) (xi (&i) (g (PRE (LENGTH c)) p))))`,
    let keats4 = REFL `abs (RHS c f)` in
    let keats5 = (CONV_RULE (RAND_CONV (REWRITE_CONV [Pm_eqn4.RHS]))) keats4 in
    let keats6 = REWRITE_RULE [REAL_ABS_NEG] keats5 in
    let keats7 =
        SPECL [`(\i.(&i) * (EL i c) * (exp (&i - (xi (&i) f))) * (poly f (xi
        (&i) f)))`;`1`;`PRE (LENGTH (c:(real)list))`] SUM_ABS_NUMSEG in
    let keats8 = ONCE_REWRITE_RULE  [GSYM keats6] keats7 in
    let keats9 = REWRITE_RULE  [REAL_ABS_NUM;REAL_ABS_MUL] keats8 in
    let g_term = `g (PRE (LENGTH (c:(real)list))) p` in
    let keats10 = SPEC g_term (GEN `f:(real)list` keats9) in
    ACCEPT_TAC  keats10
)


let RHS_4_BOUND_PRE = PROVE(
        `abs (RHS c (g (PRE (LENGTH c)) p)) <=
          (sum (1..PRE (LENGTH c)) &) *
               (max_abs c *
               abs (exp (&(PRE (LENGTH c)))) *
               &1 / &(FACT (p - 1)) *
               &(PRE (LENGTH c)) pow (p - 1) *
               &(PRE (LENGTH c)) pow PRE (LENGTH c) pow p)`,
      let w0 = `(real_of_num i) * (real_abs (EL i c))` in
      let w1 = `(real_of_num i) * (max_abs c)` in
      let x0 = `abs (exp (&v - xi (&v) (g (PRE (LENGTH (c:(real)list))) p)))`
      in
      let x1 = `abs (exp (&(PRE (LENGTH (c:(real)list)))))` in
      let y0 = `abs (poly (g (PRE (LENGTH (c:(real)list))) p) (xi (&i) (g (PRE
      (LENGTH c)) p)))` in
      let y1 = ` &1 / &(FACT (p - 1)) * &(PRE (LENGTH (c:(real)list))) pow (p -
      1) * &(PRE (LENGTH c)) pow PRE (LENGTH c) pow p` in
      let rename_free_var oo nn tt = SPEC nn (GEN oo tt) in
      let v2i tt = rename_free_var `v:num` `i:num` tt in
      let josh0  = SPECL [w0;x0;y0;w1;x1;y1] REAL_LE_MUL3 in
      let josh2 = SPECL [`real_of_num i`;`real_abs (EL i c)`] REAL_LE_MUL in
      let josh3 = SIMP_RULE [REAL_ABS_POS;REAL_ARITH `(real_of_num 0) <= &i`] josh2
      in
      let josh4 = v2i (SIMP_RULE [josh3;REAL_ABS_POS] josh0) in
      let josh5 = SIMP_RULE [UNDISCH KEATS_PART_1] josh4 in
      let josh6 = SIMP_RULE [UNDISCH (v2i KEATS_PART_2)] josh5 in
      let josh7 = SIMP_RULE [UNDISCH KEATS_PART_3] josh6 in
      let josh8 = DISCH `1 <= i /\ i <= (PRE (LENGTH (c:(real)list)))` josh7 in
      let f0 = `(\i.
             &i *
             abs (EL i c) *
             abs (exp (&i - xi (&i) (g (PRE (LENGTH c)) p))) *
             abs (poly (g (PRE (LENGTH c)) p) (xi (&i) (g (PRE (LENGTH c))
             p))))` in
      let f1 = `(\i.
                 (&i * max_abs c) *
                 abs (exp (&(PRE (LENGTH c)))) *
                 &1 / &(FACT (p - 1)) *
                 &(PRE (LENGTH c)) pow (p - 1) *
                 &(PRE (LENGTH c)) pow PRE (LENGTH c) pow p)` in
      let josh9 = SPECL [f0;f1;`1`;`PRE (LENGTH (c:(real)list))`] SUM_LE_NUMSEG
      in
      let josh10 = REWRITE_RULE [GSYM REAL_MUL_ASSOC] (BETA_RULE josh9) in
      let josh11 = REWRITE_RULE [GSYM REAL_MUL_ASSOC] (GEN `i:num` josh8) in
      let josh12 = MP josh10 josh11 in
      let josh13 = CONJ RHS_4_F5_LE_SUM josh12 in
      let josh14 = MATCH_MP REAL_LE_TRANS josh13 in
      let josh15 = ONCE_REWRITE_RULE [SUM_RMUL] josh14 in
      ACCEPT_TAC josh15
)

(* A reviewer of the Journal of Formalized Reasoning paper for this proof
 * pointed out that the "abs" in "abs (exp (&(PRE (LENGTH c))))" of
 * RHS_4_BOUND_PRE is redundant.  So here that theorem is rewritten to
 * remove that abs.
 *)
let RHS_4_BOUND =
    let l1 = MATCH_MP (SPEC `&0:real` REAL_LT_IMP_LE)
                      (SPEC `x:real` REAL_EXP_POS_LT) in
    let l2 = REWRITE_RULE [GSYM REAL_ABS_REFL] l1 in
    ONCE_REWRITE_RULE [l2] RHS_4_BOUND_PRE
;;
```

### Informal statement
For all real numbers $w$, $x$, $y$, and $z$, if $|w| \leq y$ and $|x| \leq z$, then $|w \cdot x| \leq y \cdot z$.

### Informal proof
We need to prove that if $|w| \leq y$ and $|x| \leq z$, then $|w \cdot x| \leq y \cdot z$.

The proof begins by using the multiplicative property of absolute value: $|w \cdot x| = |w| \cdot |x|$ (by `ABS_MUL`).

Next, we use the fact that if $a \leq c$ and $b \leq d$ where $a,b,c,d \geq 0$, then $a \cdot b \leq c \cdot d$. This is handled by `REAL_LE_MUL2`. 

Since we know that $|w| \leq y$ and $|x| \leq z$ (from our assumptions), and absolute values are always non-negative (by `ABS_POS`), we can apply `REAL_LE_MUL2` to get $|w| \cdot |x| \leq y \cdot z$.

Therefore, $|w \cdot x| = |w| \cdot |x| \leq y \cdot z$, which proves our theorem.

### Mathematical insight
This theorem establishes an important inequality for absolute values of products. It extends the basic property that absolute value of a product equals the product of absolute values (|ab| = |a|·|b|) by providing an upper bound when we have bounds on individual factors.

The result is useful in analysis for error estimates, convergence proofs, and bounds on complex expressions. It's particularly valuable when working with polynomial bounds, approximation theory, and numerical analysis where controlling the absolute value of products is often crucial.

### Dependencies
- `REAL_LT_IMP_LE`: If $x < y$, then $x \leq y$.
- `REAL_LE_TRANS`: Transitivity of $\leq$ for real numbers.
- `REAL_LE_MUL`: If $0 \leq x$ and $0 \leq y$, then $0 \leq x \cdot y$.
- `ABS_POS`: For all real $x$, $0 \leq |x|$.
- `ABS_MUL`: For all real $x$ and $y$, $|x \cdot y| = |x| \cdot |y|$.

### Porting notes
This theorem should be straightforward to port to other proof assistants as it relies on basic properties of absolute values and inequalities that are standard in most mathematical libraries. The proof is direct and doesn't use any unusual tactics or constructs specific to HOL Light.

---

## JESSE_POW_LEMMA

### Name of formal statement
JESSE_POW_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let JESSE_POW_LEMMA = PROVE(
     `(p:num) > 1 ==> !x.real_pow x p = x * (real_pow x (p-1))`,
     let c0 = UNDISCH (ARITH_RULE `(p:num) > 1 ==> p = SUC (p - 1) `) in
     STRIP_TAC THEN STRIP_TAC THEN
     (CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [c0]))) THEN
     (SIMP_TAC [real_pow])
)
let JESSE_REAL_ABS_LE = PROVE(
    `!(x:real) y.(abs x) <= y ==> (abs x) <= (abs y)`,
    let int10 = UNDISCH (REAL_ARITH `(real_abs x) <= y ==>  y = real_abs y`) in
    (REPEAT STRIP_TAC) THEN (ASM_SIMP_TAC [GSYM int10])
)
let OLDGERMAN_LEMMA = PROVE(
  ` !C2 C e.
        &0 < e
        ==> (?N . !n. n >= N ==>
        abs (C2 * inv (&(FACT n)) * C pow n - &0) < e)`,
   let w0 = MATCH_MP SUM_SUMMABLE (SPEC `C:real` REAL_EXP_CONVERGES) in
   let w1 = MATCH_MP SER_ZERO w0 in
   let w2 = BETA_RULE w1 in
   let w3 = SPEC `C2:real` SEQ_CONST in
   let w4 = CONJ w3 w2 in
   let w5 = BETA_RULE (MATCH_MP SEQ_MUL w4) in
   let w6 = ONCE_REWRITE_RULE [REAL_ARITH `(C2:real) * (&0) = &0`] w5 in
   let w7 = ONCE_REWRITE_RULE [SEQ] w6 in
   let w8 = GEN_ALL (BETA_RULE w7) in
   (REPEAT STRIP_TAC) THEN
   (CHOOSE_TAC (UNDISCH (SPEC_ALL w8))) THEN
   (EXISTS_TAC `SUC N`) THEN
   (ASM_SIMP_TAC [ARITH_RULE `n' >= SUC n ==> n' >= n`])
)

let RHS_4_LT_ONE_MESSY = PROVE(
   `?p0. !p. p > 1 ==> p> p0 ==> abs (RHS c (g (PRE (LENGTH c)) p)) < &1`,
   let c1 = ONCE_REWRITE_RULE [ UNDISCH JESSE_POW_LEMMA ] RHS_4_BOUND in
   let c2 = SPECL [`real_pow (&(PRE (LENGTH (c:(real)list)))) (p-1)`]
   REAL_MUL_SYM in
   let c3 = ONCE_REWRITE_RULE [ c2] c1 in
   let c4 = ONCE_REWRITE_RULE [ GSYM REAL_MUL_ASSOC ] c3 in
   let c5 = ONCE_REWRITE_RULE [ GSYM REAL_POW_MUL ] c4 in
   let c6 = ONCE_REWRITE_RULE [REAL_MUL_SYM] (CONJUNCT2 real_pow) in
   let c7 = ONCE_REWRITE_RULE [GSYM c6] c5 in
   let c8 = REAL_ARITH `!x. (real_of_num 1)/x = inv x` in
   let c9 = ONCE_REWRITE_RULE [c8] c7 in
   let c10 = REAL_ARITH `!x y z.(inv x) * y * z = y * inv x * z` in
   let c11 = ONCE_REWRITE_RULE [c10] c9 in
   let t0 =
    `sum (1..PRE (LENGTH c)) & *
     max_abs c *
     (exp (&(PRE (LENGTH c)))) *
     &(PRE (LENGTH c)) pow PRE (LENGTH c)` in
   let t1 = `real_of_num (PRE (LENGTH (c:(real)list))) pow SUC (PRE (LENGTH c))`
   in
   let int0 = SPECL [t0;t1;`real_of_num 1`]  OLDGERMAN_LEMMA in
   let int1 = SIMP_RULE [REAL_ARITH `(real_of_num 0) < &1`] int0 in
   let int2 = SIMP_RULE [REAL_ARITH `x - (real_of_num 0) = x`] int1 in
   let t8 = `!n. n >= N
        ==> abs
            ((sum (1..PRE (LENGTH c)) & *
              max_abs c *
              (exp (&(PRE (LENGTH c)))) *
              &(PRE (LENGTH c)) pow PRE (LENGTH c)) *
             inv (&(FACT n)) *
             &(PRE (LENGTH c)) pow SUC (PRE (LENGTH c)) pow n) <
            &1` in
   let int5 = ASSUME t8 in
   let int50 = REAL_ARITH `((x:real) * y * z * w) * (a * b) = x * y * z * w * a *
   b` in
   let int51 = ONCE_REWRITE_RULE [int50] int5 in
   let int6 = SPEC `p - 1` int51 in
   let int7 = ARITH_RULE ` (p > N ==> p - 1 >= N)` in
   let int8 = UNDISCH (IMP_TRANS int7 int6) in
   let int9 = ARITH_RULE `(x:real) <= y ==> y < (real_of_num 1) ==> x < (&1)` in
   let int10 = MATCH_MP JESSE_REAL_ABS_LE c11 in
   let int11 = MATCH_MP int9 int10 in
   let int12 = MP int11 int8 in
   (CHOOSE_TAC int2) THEN
   (EXISTS_TAC `N:num`) THEN
   (STRIP_TAC) THEN
   (STRIP_TAC) THEN
   (ONCE_REWRITE_TAC [ARITH_RULE `p > 0 ==> ((p:num)  > N <=> p - 1 >= N)`]) THEN
   (DISCH_TAC) THEN
   (MATCH_ACCEPT_TAC int12)
)
let LT_ONE = PROVE(
        `!c. ?p0. !p. p> p0 ==> abs (RHS c (g (PRE (LENGTH c)) p)) < &1`,
    STRIP_TAC THEN (CHOOSE_TAC RHS_4_LT_ONE_MESSY) THEN (EXISTS_TAC `SUC p0`) THEN
    (ASM_MESON_TAC [ARITH_RULE `p > SUC p0 ==> (p > p0 /\ p > 1)`])
)
end;;
```

### Informal statement
For any natural number $p > 1$ and any real number $x$, the power $x^p$ can be expressed as $x \cdot x^{p-1}$.

Formally:
$$\forall p > 1, \forall x \in \mathbb{R}, x^p = x \cdot x^{p-1}$$

### Informal proof
The proof proceeds as follows:

1. First, we use the fact that if $p > 1$, then $p = p-1+1 = \operatorname{SUC}(p-1)$.
2. Then we apply this equality to rewrite the left-hand side using the successor form of $p$.
3. Finally, we apply the definition of real powers, which states that $x^{\operatorname{SUC}(n)} = x \cdot x^n$.

The proof uses the basic properties of real powers and simple arithmetic manipulation.

### Mathematical insight
This lemma establishes a basic recurrence relation for powers of real numbers. It's a fundamental property that allows us to decompose higher powers into products of lower powers, which is essential for inductive proofs involving powers. While this property might seem obvious, having it formally proven allows it to be used in other formal proofs that involve manipulation of powers.

The lemma is particularly useful when working with polynomial expressions or when analyzing the behavior of power functions in real analysis.

### Dependencies
- `real_pow`: Definition of real number exponentiation
- `ARITH_RULE`: Arithmetic reasoning in HOL Light

### Porting notes
This theorem should be straightforward to port to other proof assistants, as it represents a basic property of exponentiation that is typically part of standard libraries. In systems with built-in power operations, this might already be a basic lemma or could be proven directly from the definition of exponentiation.

---

## N_IS_INT



### N_IS_INT
- The exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let N_IS_INT = PROVE(
    `!n . integer (&n)`,
    MESON_TAC [is_int]
)
let NEG_N_IS_INT = PROVE(
    `!n . integer (--(&n))`,
    MESON_TAC [is_int]
)
let INT_OF_REAL_ADD = PROVE(
    `!x y.(integer x) /\ (integer y)
           ==> (int_of_real (x + y)) =
               (int_of_real x) + (int_of_real y)`,
    SIMP_TAC[integer;int_add;int_rep;N_IS_INT;NEG_N_IS_INT]
)
let INT_OF_REAL_MUL = PROVE(
    `!x y.(integer x) /\ (integer y)
           ==> (int_of_real (x * y)) =
               (int_of_real x) * (int_of_real y)`,
    SIMP_TAC[is_int;int_mul;int_rep;N_IS_INT;NEG_N_IS_INT]
)

let rec INT_OF_REAL_CONV_helper t =
    let real_op_2_int_op t =
        if (t = `real_add`) then `int_add`
        else if (t = `real_sub`) then `int_sub`
        else if (t = `real_mul`) then `int_mul`
        else if (t = `real_pow`) then `int_pow`
        else if (t = `real_neg`) then `int_neg`
        else t
    in
    if (is_var t) then (mk_comb (`int_of_real`,t),[],[t])
    else if ((rator t) = `real_of_num`) then
      (mk_comb (`int_of_real`, t),[t],[])
    else if ((rator t) = `real_neg`) then
      let rand1 = rand t in
      let (expr1,lst1,lst2) = INT_OF_REAL_CONV_helper rand1 in
      let lst = lst1 @ [t] in
      let expr = mk_comb (`int_neg`, expr1) in
      (expr,lst,lst2)
    else if ((rator (rator t)) = `real_pow`) then
      let rand1 = rand (rator t) in
      let exponent = rand t in
      let (expr1,lst1,lst2) = INT_OF_REAL_CONV_helper rand1 in
      let lst = lst1 @ [t] in
      let expr = mk_comb (mk_comb (`int_pow`,expr1),exponent) in
      (expr,lst,lst2)
    else if (   ((rator (rator t)) = `real_add`)
             || ((rator (rator t)) = `real_mul`)
             || ((rator (rator t)) = `real_sub`)  ) then
      let int_op = real_op_2_int_op (rator (rator t)) in
      let rand1 = rand (rator t) in
      let rand2 = rand t in
      let (expr1,lst11,lst12) = INT_OF_REAL_CONV_helper rand1 in
      let (expr2,lst21,lst22) = INT_OF_REAL_CONV_helper rand2 in
      let lst1 = lst11 @ lst21 @ [t] in
      let lst2 = lst12 @ lst22 in
      let expr = mk_comb (mk_comb (int_op,expr1),expr2) in
      (expr,lst1,lst2)
    else (t,[],[t])


(* ------------------------------------------------------------------------- *)
(* I wrote an initial version of this, but John Harrison proposed this       *)
(* version which is faster and also requires less theorems.                  *)
(* ------------------------------------------------------------------------- *)
let INT_OF_REAL_CONV =
  let final_tweak = MATCH_MP(MESON[int_tybij] `real_of_int x = y ==> int_of_real y = x`) in
  fun t ->
    let (exp,real_sub_terms,is_int_assumpts) = INT_OF_REAL_CONV_helper t in
    let is_int_assumpts = List.map (fun x -> mk_comb (`integer`,x)) is_int_assumpts in
    let fexp = rand(concl(PURE_REWRITE_CONV[GSYM int_of_num] exp)) in
    let rexp = mk_comb(`real_of_int`,fexp)
    and ths = map (GEN_REWRITE_RULE I [CONJUNCT2 int_tybij] o ASSUME) is_int_assumpts in
    let th3 = PURE_REWRITE_CONV(ths @ [int_pow_th; int_add_th; int_mul_th; int_sub_th; int_neg_th; int_of_num_th]) rexp in
    itlist DISCH is_int_assumpts (final_tweak th3)

let ALL_IS_INT = PROVE(
    `! h t . (ALL integer (CONS h t)) ==> (integer h)  /\ (ALL integer t)`,
    SIMP_TAC [ALL]
)

let ALL_IS_INT_POLY_ADD = PROVE(
    `! p1 p2 . (ALL integer p1) /\ (ALL integer p2) ==> (ALL integer (p1 ++ p2))`,
    let lem01 = UNDISCH (SPECL [`h:real`;`t:(real)list`] ALL_IS_INT) in
    let [lem02;lem03] = CONJUNCTS lem01 in
    let lem04 = UNDISCH (SPECL [`h':real`;`t':(real)list`] ALL_IS_INT) in
    let [lem05;lem06] = CONJUNCTS lem04 in
    let lem07 = CONJ lem02 lem05 in
    let lem08 = MATCH_MP INTEGER_ADD lem07 in
    let lem09 = ASSUME `! p2. ALL integer t /\ ALL integer p2 ==> ALL integer (t ++ p2)` in
    let lem10 = SPEC `t':(real)list` lem09 in
    let lem11 = CONJ lem03 lem06 in
    let lem12 = MP lem10 lem11 in
    LIST_INDUCT_TAC THENL
    [ (SIMP_TAC [poly_add]);
      LIST_INDUCT_TAC THENL
      [ (SIMP_TAC [poly_add]);
        (SIMP_TAC [poly_add]) THEN (ONCE_REWRITE_TAC [NOT_CONS_NIL]) THEN
        (SIMP_TAC []) THEN (SIMP_TAC [HD;TL]) THEN (STRIP_TAC) THEN
        (SIMP_TAC [ALL]) THEN
        (CONJ_TAC) THENL [(ACCEPT_TAC lem08); (ACCEPT_TAC lem12)]
      ]
    ]
)
let ALL_IS_INT_POLY_CMUL = PROVE(
    `! p c. (integer c) /\ (ALL integer p) ==> (ALL integer (c ## p))`,
    (LIST_INDUCT_TAC) THEN (ASM_SIMP_TAC [poly_cmul;ALL;INTEGER_MUL])
)

let ALL_IS_INT_POLY_MUL = PROVE(
    `! p1 p2 . (ALL integer p1) /\ (ALL integer p2) ==> (ALL integer (p1 ** p2))`,
    let lem01 = UNDISCH (SPECL [`h:real`;`t:(real)list`] ALL_IS_INT) in
    let lem02 = UNDISCH (SPECL [`h':real`;`t':(real)list`] ALL_IS_INT) in
    let [lem03;lem04] = CONJUNCTS lem01 in
    let [lem05;lem06] = CONJUNCTS lem02 in
    let lem07 = MATCH_MP INTEGER_MUL (CONJ lem03 lem05) in
    let lem08 = MATCH_MP ALL_IS_INT_POLY_CMUL (CONJ lem03 lem06) in
    let lem09 = ASSUME `! p2. ALL integer t /\ ALL integer p2 ==> ALL integer (t ** p2)` in
    let lem10 = SPEC `(CONS h' t'):(real)list` lem09 in
    LIST_INDUCT_TAC THENL
    [ (LIST_INDUCT_TAC THENL [(SIMP_TAC [ALL;poly_mul]);(SIMP_TAC [poly_mul])]);
      LIST_INDUCT_TAC THENL
      [ (SIMP_TAC [poly_mul]) THEN
        ((ASM_CASES_TAC `(t:(real)list) = []`) THENL
        [ (ASM_SIMP_TAC [ALL;poly_cmul]) THEN (SIMP_TAC [poly_cmul]);
          (ASM_SIMP_TAC [ALL;poly_cmul;poly_add]) THEN (SIMP_TAC [SPEC `0` N_IS_INT])
        ]);
        (STRIP_TAC) THEN (ONCE_REWRITE_TAC [poly_mul] ) THEN
        (ASM_CASES_TAC `(t:(real)list) = []`) THENL
        [ (ASM_SIMP_TAC [ALL;poly_cmul]) THEN STRIP_TAC THENL
          [(ACCEPT_TAC lem07) ;(ACCEPT_TAC lem08)];
          (ASM_SIMP_TAC []) THEN (MATCH_MP_TAC ALL_IS_INT_POLY_ADD) THEN
          (CONJ_TAC) THENL
          [ (MATCH_MP_TAC ALL_IS_INT_POLY_CMUL) THEN (CONJ_TAC) THENL
            [(ACCEPT_TAC lem03) ; (ASM_SIMP_TAC[])];
            (SIMP_TAC [ALL]) THEN (CONJ_TAC) THENL
            [(ACCEPT_TAC (SPEC `0` N_IS_INT)); (ASM_SIMP_TAC [lem04;lem10])]
          ]
        ]
      ]
    ]
)
let NOT_POLY_MUL_ITER_NIL = PROVE(
    `! n . ~((poly_mul_iter (\i.[ -- &i; &1]) n) = [])`,
    let lem02 = SIMP_RULE [NOT_CONS_NIL] (ISPEC `[ -- &(SUC n); &1]` NOT_POLY_MUL_NIL ) in
    let lem03 = ISPEC `(poly_mul_iter (\i.[ -- &i; &1]) n)` lem02 in
    let lem04 = UNDISCH  lem03 in
    INDUCT_TAC THENL
    [ (SIMP_TAC [Pm_eqn5.POLY_MUL_ITER;NOT_CONS_NIL]);
      (SIMP_TAC [Pm_eqn5.POLY_MUL_ITER;lem04])
    ]
)

let ALL_IS_INT_POLY_MUL_ITER = PROVE(
    `! n. (ALL integer (poly_mul_iter (\i.[-- &i; &1]) n))`,
    let FOOBAR_LEMMA =  PROVE(
        `ALL integer [-- &(SUC n); &1]`,
        (SIMP_TAC [ALL]) THEN (SIMP_TAC [N_IS_INT;NEG_N_IS_INT])) in
    INDUCT_TAC THENL
    [ (ONCE_REWRITE_TAC [Pm_eqn5.POLY_MUL_ITER]) THEN
      (ONCE_REWRITE_TAC [ALL]) THEN (SIMP_TAC [ALL;N_IS_INT]);
      (ONCE_REWRITE_TAC [Pm_eqn5.POLY_MUL_ITER]) THEN (BETA_TAC) THEN
      (MATCH_MP_TAC ALL_IS_INT_POLY_MUL) THEN (CONJ_TAC) THENL
      [(ACCEPT_TAC (FOOBAR_LEMMA)); (ASM_SIMP_TAC [])]
    ]
)

let ALL_IS_INT_POLY_EXP = PROVE(
    `!n p. (ALL integer p) ==> (ALL integer (poly_exp p n))`,
    let lem01 = ASSUME `! p. ALL integer p ==> ALL integer (poly_exp p n)` in
    let lem02 = ASSUME ` ALL integer p` in
    let lem03 = MP (SPEC_ALL lem01) lem02 in
    let lem04 = CONJ lem02 lem03 in
    let lem05 = MATCH_MP ALL_IS_INT_POLY_MUL lem04 in
    INDUCT_TAC THENL
    [ (ONCE_REWRITE_TAC [poly_exp]) THEN (ONCE_REWRITE_TAC [ALL]) THEN
      (ONCE_REWRITE_TAC [ALL]) THEN (SIMP_TAC [SPEC `1` N_IS_INT]);
      (ONCE_REWRITE_TAC [poly_exp]) THEN (REPEAT STRIP_TAC) THEN (ACCEPT_TAC lem05)
   ]
)

let BLAHBLAH = PROVE(
    `! p1 p2. (LENGTH p1 <= LENGTH p2) ==> (&0 ## p1 ++ p2) = p2`,
     LIST_INDUCT_TAC THENL
     [ (SIMP_TAC [LENGTH;poly_cmul;poly_add]);
       LIST_INDUCT_TAC THENL
       [ (SIMP_TAC [LENGTH]) THEN ARITH_TAC;
         (ASM_SIMP_TAC [poly_cmul;poly_add;NOT_CONS_NIL;HD;TL;
                        REAL_ARITH `&0 * h + h' = h'`;LENGTH;
                        ARITH_RULE `(SUC x) <= (SUC y) <=> x <= y`]) ]
     ]
)

let BLAHBLAH3 = PROVE(
    `! n h t. (LENGTH t) <= LENGTH (poly_exp [&0;&1] n ** CONS h t)`,
    let lem04 = ASSUME `! h t . LENGTH t <= LENGTH (poly_exp [&0;&1] n ** CONS h t)` in
    let lem05 = SPECL [`h:real`;`t:(real)list`] lem04  in
    let lem06 = ARITH_RULE `!(x:num) y . x <= y ==> x <= SUC y` in
    let lem07 = MATCH_MP lem06 lem05   in
    let lem08 = GEN_ALL lem07  in
     INDUCT_TAC THENL
     [ (SIMP_TAC [poly_exp;poly_mul;poly_cmul;POLY_CMUL_LID;LENGTH]) THEN ARITH_TAC;
       (SIMP_TAC [POLY_EXP_X_REC;poly_mul;NOT_POLY_EXP_X_NIL;poly_cmul;poly_add;NOT_CONS_NIL;LENGTH;TL]) THEN
       (ASM_SIMP_TAC [BLAHBLAH]) THEN (ACCEPT_TAC lem08)
    ]
)
let TELEVISION = PROVE (
    `!n p.(~ (p = [])) ==>  EL n (poly_exp [&0;&1] n ** p) = HD p`,
    let lem = MATCH_MP BLAHBLAH (SPEC_ALL BLAHBLAH3) in
    INDUCT_TAC THENL
    [ (SIMP_TAC [EL;poly_exp;POLY_MUL_CLAUSES]) THEN (LIST_INDUCT_TAC) THENL
      [ (SIMP_TAC[]); (SIMP_TAC [NOT_CONS_NIL;POLY_CMUL_LID])];
        (SIMP_TAC [EL;POLY_EXP_X_REC;poly_mul;NOT_POLY_EXP_X_NIL]) THEN
        LIST_INDUCT_TAC THENL
        [ (SIMP_TAC []);
          (SIMP_TAC [poly_cmul;poly_add;NOT_CONS_NIL;TL;HD]) THEN
          (ASM_SIMP_TAC [lem;NOT_CONS_NIL;HD])
        ]
    ]
)
let JOSHUA = PROVE(
    `!i n p.(~ (p = [])) /\ (i < n) ==>  EL i (poly_exp [&0;&1] n ** p) = &0`,
    let lem0000 = SPECL [`t:(real)list`;`poly_exp [&0;&1] n ** (CONS h t)`] BLAHBLAH in
    let lem0001 = MATCH_MP lem0000 (SPEC_ALL BLAHBLAH3)  in
    let lem0002 = ASSUME `! n p . ~(p = []) /\ i < n ==> EL i (poly_exp [&0;&1] n ** p) = &0` in
    let lem0003 = SIMP_RULE [NOT_CONS_NIL] (SPECL [`n:num`;`(CONS (h:real) t)`] lem0002) in
    INDUCT_TAC THENL
    [ INDUCT_TAC THENL
      [ ARITH_TAC ;
        LIST_INDUCT_TAC THENL
        [ (SIMP_TAC[]);
          (SIMP_TAC [POLY_EXP_X_REC;EL;HD;poly_mul;NOT_POLY_EXP_NIL;NOT_CONS_NIL;HD_POLY_ADD;poly_cmul]) THEN
           REAL_ARITH_TAC
        ]
      ];
      INDUCT_TAC THENL
      [ ARITH_TAC;
       (SIMP_TAC [EL;POLY_EXP_X_REC;poly_mul;NOT_POLY_EXP_NIL;NOT_CONS_NIL]) THEN
       LIST_INDUCT_TAC THENL
       [ (SIMP_TAC[]);
         (SIMP_TAC [poly_cmul;poly_add;NOT_CONS_NIL;TL;lem0001]) THEN
         (SIMP_TAC [ARITH_RULE `(SUC i) < (SUC n) <=> i < n`;lem0003])
       ]
      ]
    ]
)
let POLY_MUL_HD = PROVE(
    `! p1 p2. (~(p1 = []) /\ ~(p2 = [])) ==> (HD (p1 ** p2)) = (HD p1) * (HD p2)`,
    LIST_INDUCT_TAC THENL
    [ (SIMP_TAC[]);
      (LIST_INDUCT_TAC) THENL
      [ (SIMP_TAC[]);
        (SIMP_TAC [NOT_CONS_NIL]) THEN (ONCE_REWRITE_TAC [poly_mul]) THEN
        (ASM_CASES_TAC `(t:(real)list) = []`) THENL
        [ (ASM_SIMP_TAC [HD;poly_cmul]);
          (ASM_SIMP_TAC [HD;poly_cmul;poly_add]) THEN
          (SIMP_TAC [NOT_CONS_NIL;HD]) THEN (REAL_ARITH_TAC)
        ]
      ]
    ]
)
let POLY_MUL_ITER_HD_FACTORIAL = PROVE(
    `! n. (HD (poly_mul_iter (\i.[-- &i; &1]) n)) = ((-- &1) pow n) * (&(FACT n))`,
    let lem01 = PROVE(`~([-- &(SUC n); &1] = [])`,SIMP_TAC [NOT_CONS_NIL]) in
    let lem02 = ISPECL
                  [`[-- &(SUC n); &1]`;`poly_mul_iter (\i.[-- &i; &1]) n`]
                  POLY_MUL_HD in
    let lem03 = CONJ lem01 (SPEC_ALL NOT_POLY_MUL_ITER_NIL) in
    let lem04 = MP lem02 lem03 in
    let lem05 = PROVE(
        `!n. ((-- &1) pow n) = -- ((-- &1) pow (SUC n))`,
        STRIP_TAC THEN (ONCE_REWRITE_TAC [pow]) THEN REAL_ARITH_TAC
    ) in
    INDUCT_TAC THENL
    [ (ONCE_REWRITE_TAC [Pm_eqn5.POLY_MUL_ITER]) THEN (SIMP_TAC [HD;FACT]) THEN REAL_ARITH_TAC;
      (ONCE_REWRITE_TAC [Pm_eqn5.POLY_MUL_ITER]) THEN BETA_TAC THEN
      (ONCE_REWRITE_TAC [lem04]) THEN (ONCE_REWRITE_TAC [HD]) THEN
      (ASM_SIMP_TAC []) THEN (ONCE_REWRITE_TAC [FACT]) THEN
      (ONCE_REWRITE_TAC [GSYM REAL_OF_NUM_MUL]) THEN
      (CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [lem05]))) THEN REAL_ARITH_TAC
    ]
)
let PLANETMATH_THM_5_1 =  PROVE(
    `! n p.
       p > 0 ==>
       n > 0 ==>
       ? As .
          ((g n p) = (&1/(&(FACT (p  - 1)))) ## As)
       /\ (! i. i< (p-1) ==> (EL i As) = &0)
       /\ ((EL (p-1) As) = ((-- &1) pow (n * p)) * ((&(FACT n)) pow p))
       /\ (ALL integer As)`,
    let lem01 = SPECL [`poly_exp [&0;&1] (p - 1)`;`poly_exp (poly_mul_iter (\i.[-- &i; &1]) n) p`] ALL_IS_INT_POLY_MUL in
    let lem02 = SPECL [`p-1`;`[&0;&1]`] ALL_IS_INT_POLY_EXP in
    let lem03 = PROVE(`ALL integer [&0;&1]`, (REWRITE_TAC [ALL]) THEN (SIMP_TAC [N_IS_INT])) in
    let lem04 = MP lem02 lem03 in
    let lem05 = SPECL [`p:num`;`poly_mul_iter (\i.[-- &i; &1]) n`] ALL_IS_INT_POLY_EXP in
    let lem06 = MP lem05 (SPEC_ALL ALL_IS_INT_POLY_MUL_ITER)  in
    let lem07 = MP lem01 (CONJ lem04 lem06)  in
    let lem08 = SPECL [`p-1`;`poly_exp (poly_mul_iter (\i.[-- &i; &1]) n) p`] TELEVISION in
    let lem09 = SIMP_RULE [ NOT_POLY_EXP_NIL;NOT_POLY_MUL_ITER_NIL] lem08 in
    let lem10 = SPECL [`i:num`;`p - 1`;`poly_exp (poly_mul_iter (\i. [ -- &i; &1]) n ) p`] JOSHUA in
    let lem11 = SIMP_RULE [NOT_POLY_MUL_ITER_NIL;NOT_POLY_EXP_NIL] lem10 in
    (REPEAT STRIP_TAC) THEN
    (EXISTS_TAC `((poly_exp [&0;&1] (p-1)) ** (poly_exp (poly_mul_iter (\i.[-- &i; &1]) n) p))`) THEN
    CONJ_TAC THENL
    [ (ONCE_REWRITE_TAC [Pm_eqn5.PLANETMATH_EQN_5]) THEN (SIMP_TAC[]);
      CONJ_TAC THENL
      [ (SIMP_TAC [lem11]);
        CONJ_TAC THENL
        [ (ONCE_REWRITE_TAC [lem09]) THEN
          (SPEC_TAC (`n:num`,`n:num`)) THEN
          (INDUCT_TAC) THENL
          [ (SIMP_TAC [NOT_CONS_NIL;HD_POLY_EXP;HD;Pm_eqn5.POLY_MUL_ITER;FACT;pow;
                       REAL_POW_ONE;ARITH_RULE `0 * p = 0`;REAL_ARITH `&1 * &1 = &1`]);
            (SIMP_TAC [HD_POLY_EXP; NOT_POLY_MUL_ITER_NIL; POLY_MUL_ITER_HD_FACTORIAL]) THEN
            (SIMP_TAC [REAL_POW_MUL;REAL_POW_POW;BLAHBLAH3]) ];
          ACCEPT_TAC lem07 ]
      ]
    ]
)
let as_def =
    let ll01 = SPEC_ALL PLANETMATH_THM_5_1 in
    let FO_LEMMA1 = PROVE(`((p > 0) ==> (n > 0) ==> (? z. C p n z))
                            <=> (? z. (p > 0) ==> (n > 0) ==> C p n z)`,MESON_TAC[]) in
    let ll02 = GEN_ALL (SIMP_RULE [FO_LEMMA1] ll01) in
    let ll03 = ONCE_REWRITE_RULE [SKOLEM_CONV (concl ll02)] ll02 in
    new_specification ["As"] ll03
(* split up def of As into its four conjuncts *)
let g_eq_As
    = (GEN_ALL o DISCH_ALL o CONJUNCT1 o  UNDISCH o UNDISCH o SPEC_ALL) as_def
let prefix_As_zero
    = (GEN_ALL o DISCH_ALL o CONJUNCT1 o CONJUNCT2 o  UNDISCH o UNDISCH o SPEC_ALL) as_def
let fact_As
    = (GEN_ALL o DISCH_ALL o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o  UNDISCH o UNDISCH o SPEC_ALL) as_def
let ALL_integer_As
    = (GEN_ALL o DISCH_ALL o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o  UNDISCH o UNDISCH o SPEC_ALL) as_def

let POLY_DIFF_AUX_LEM1 = PROVE(
    `! i p k. i < (LENGTH p) ==> EL i (poly_diff_aux k p) = (EL i p) * &(i + k)`,
    let lem0001 = ASSUME `! p k . i < LENGTH p ==> EL i (poly_diff_aux k p ) = EL i p * &(i + k)` in
    let lem0002 = SPECL [` t:(real)list`;`SUC k`] lem0001 in
    let lem0003 = PROVE(`SUC i < LENGTH (CONS (h:real) t) <=> i < LENGTH t`,(SIMP_TAC [LENGTH]) THEN ARITH_TAC) in
    INDUCT_TAC THENL
    [ LIST_INDUCT_TAC THENL
      [ (SIMP_TAC [poly_diff_aux;LENGTH]) THEN ARITH_TAC;
        (SIMP_TAC [poly_diff_aux;ARITH_RULE `0 + k = k`;poly_diff;LENGTH;EL;HD;TL]) THEN REAL_ARITH_TAC ];
      LIST_INDUCT_TAC THENL
      [ (SIMP_TAC [LENGTH]) THEN ARITH_TAC;
        (SIMP_TAC [poly_diff_aux;EL;TL]) THEN STRIP_TAC THEN
        (SIMP_TAC [lem0003;lem0002;ARITH_RULE `i + SUC k = SUC i + k`]) ]
    ]
)
let EL_POLY_DIFF = PROVE(
    `! i p. i < (LENGTH (poly_diff p)) ==> EL i (poly_diff p) = (EL (SUC i) p) * &(SUC i)`,
    let lem01 =  SPECL [`SUC i`;`t:(real)list`;`1`] POLY_DIFF_AUX_LEM1  in
    INDUCT_TAC THENL
    [ LIST_INDUCT_TAC THENL
      [ ((SIMP_TAC [LENGTH;poly_diff]) THEN ARITH_TAC);
        (SIMP_TAC [LENGTH;PRE;EL;HD;TL;ARITH_RULE `SUC 0 = 1`;REAL_ARITH `x * &1 = x`;poly_diff;NOT_CONS_NIL]) THEN
        (SPEC_TAC (`t:(real)list`,`t:(real)list`)) THEN
        LIST_INDUCT_TAC THENL [(SIMP_TAC [LENGTH;poly_diff_aux]) THEN ARITH_TAC;
                               (SIMP_TAC [HD;poly_diff_aux;REAL_ARITH `&1 * h = h`])]
     ];
     LIST_INDUCT_TAC THENL
     [ ((SIMP_TAC [LENGTH;HD;poly_diff;REAL_ARITH `&1 * h = h`])) THEN ARITH_TAC;
        (SIMP_TAC [poly_diff;NOT_CONS_NIL;TL;LENGTH_POLY_DIFF_AUX ]) THEN (SIMP_TAC [lem01;EL;TL]) THEN ARITH_TAC ]
     ]
)
let POLY_AT_ZERO = PROVE(
    `!p .(~(p = [])) ==> poly p (&0) = HD p`,
    LIST_INDUCT_TAC THENL [ SIMP_TAC []; (SIMP_TAC [poly;HD]) THEN REAL_ARITH_TAC ]
)
let PDI_POLY_DIFF_COMM = PROVE(
    `! p n.(poly_diff_iter (poly_diff p) n) = (poly_diff (poly_diff_iter p n))`,
    STRIP_TAC THEN INDUCT_TAC THENL
    [(SIMP_TAC [Pm_lemma1.PDI_DEF]);
     (ONCE_REWRITE_TAC [Pm_lemma1.PDI_DEF]) THEN (ASM_SIMP_TAC [])]
)
let EL_PDI_AT_ZERO = PROVE(
     `!i p. (i < (LENGTH p))
         ==> ( poly (poly_diff_iter p i) (&0)) = ((EL i p) * (&(FACT i)))`,
    let lem03 = PROVE(`SUC i < LENGTH (CONS (h:real) t) <=> i < LENGTH t`,(SIMP_TAC [LENGTH]) THEN ARITH_TAC) in
    let lem04 = ASSUME `!p . i < LENGTH p ==> poly (poly_diff_iter p i) (&0) = EL i p * &(FACT i)` in
    let lem05 = SIMP_RULE [LENGTH_POLY_DIFF;LENGTH;PRE] (SPEC `poly_diff (CONS h t)` lem04) in
    let lem06 = PROVE(`i < LENGTH t ==> i < LENGTH (poly_diff (CONS h t))`,SIMP_TAC [LENGTH_POLY_DIFF;PRE;LENGTH]) in
    INDUCT_TAC THENL
    [ (LIST_INDUCT_TAC THENL
      [(SIMP_TAC [LENGTH]) THEN ARITH_TAC; (SIMP_TAC [Pm_lemma1.PDI_DEF;FACT;EL;NOT_CONS_NIL;POLY_AT_ZERO]) THEN REAL_ARITH_TAC]);
      LIST_INDUCT_TAC THENL
      [ (SIMP_TAC [LENGTH]) THEN ARITH_TAC;
        (SIMP_TAC [Pm_lemma1.PDI_DEF;GSYM PDI_POLY_DIFF_COMM;lem03;lem05]) THEN
        (SIMP_TAC [lem06;EL_POLY_DIFF;FACT;REAL_OF_NUM_MUL;GSYM REAL_MUL_ASSOC])
      ]
    ]
)
let EL_PDI_AT_ZERO2 = PROVE(
    `!i p. ((~ (p = [])) /\ (i <= (LENGTH p) - 1)) ==> ( poly (poly_diff_iter p i) (&0)) = ((EL i p) * (&(FACT i)))`,
    STRIP_TAC THEN LIST_INDUCT_TAC THEN
    (SIMP_TAC [NOT_CONS_NIL;LENGTH;ARITH_RULE `(i <= (SUC x) -1) <=> (i < (SUC x))`;EL_PDI_AT_ZERO])
)
let POLY_CMUL_PDI = PROVE(
    `!p c i. (poly_diff_iter (c ## p) i) = c ##(poly_diff_iter p i)`,
    STRIP_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN (ASM_SIMP_TAC [Pm_lemma1.PDI_DEF;POLY_CMUL_POLY_DIFF])
)
let LENGTH_g = PROVE(
    `! n p . (LENGTH (g n p)) >= p `,
    let lem00 = ARITH_RULE `SUC ((SUC p ) - 1) = SUC p` in
    let lem01 = PROVE(`! n p. ~((poly_exp (poly_mul_iter (\i.[-- &i; &1]) n ) (SUC p)) = [])`,
                       SIMP_TAC [NOT_POLY_EXP_NIL; NOT_POLY_MUL_ITER_NIL]) in
    let lem02 = MATCH_MP POLY_MUL_LENGTH2 (SPEC_ALL lem01) in
    let lem03 = SPECL [`poly_exp [&0;&1] (SUC p - 1)`] lem02 in
    let lem04 = SIMP_RULE [POLY_EXP_X_LENGTH] lem03 in
    let lem05 = SIMP_RULE [lem00] lem04 in
     (SIMP_TAC [Pm_eqn5.PLANETMATH_EQN_5;POLY_CMUL_LENGTH]) THEN STRIP_TAC THEN INDUCT_TAC THENL
     [ ARITH_TAC; SIMP_TAC [lem05]]
)
let LENGTH_As = PROVE(
    `! n p . p > 0 ==> n > 0 ==> LENGTH (As n p) >= p`,
    let lem50 = ADD_ASSUM `p > 0` (ADD_ASSUM `n > 0` (SPEC_ALL LENGTH_g)) in
    let lem51 = ONCE_REWRITE_RULE [UNDISCH_ALL (SPEC_ALL g_eq_As)] lem50 in
    let lem52 = ONCE_REWRITE_RULE [POLY_CMUL_LENGTH] lem51 in
    SIMP_TAC [lem52]
)
let REAL_MUL_RDIV = PROVE(
    `!x y. ~(y = &0) ==> ((x * y) / y = x)`,
    SIMP_TAC[real_div; GSYM REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_MUL_RID]
)
let REAL_MUL_DIV_ASSOC = PROVE(
    `!x y z.((x * z) / y = x * (z / y))`,
    SIMP_TAC [real_div;GSYM REAL_MUL_ASSOC]
)
let IS_INT_FACT_DIV = PROVE(
    `! n m. n >= m ==> integer ( (&(FACT n))/(&(FACT m)) )`,
    let lem0 = SPEC_ALL (ONCE_REWRITE_RULE [GSYM (SPECL [`FACT n`;`0`] REAL_OF_NUM_EQ)] FACT_NZ) in
    let lem1 = SPECL [`&(SUC n)`;`&(FACT n)`]  REAL_MUL_RDIV in
    let lem2 = MP lem1 lem0 in
    let lem4 = ASSUME `! m. n >= m ==> integer (&(FACT n)/ &(FACT m))` in
    let lem5 = UNDISCH (SPEC_ALL lem4) in
    let lem6 = PROVE(`integer(&(SUC n))`,SIMP_TAC [N_IS_INT]) in
    let lem7 = CONJ lem6 lem5 in
    let lem8 = MATCH_MP INTEGER_MUL lem7  in
    let lem9 = UNDISCH_ALL (ARITH_RULE `(~(n >= m)) ==> (SUC n >= m) ==>  m = SUC n`) in
    INDUCT_TAC THENL
    [ (SIMP_TAC [ARITH_RULE `0 >= m ==> m = 0`;FACT_NZ;REAL_OF_NUM_EQ;REAL_DIV_REFL;N_IS_INT]);
      (STRIP_TAC) THEN (ASM_CASES_TAC `(n:num) >= m`) THENL
      [ (ASM_SIMP_TAC [FACT;GSYM REAL_OF_NUM_MUL;lem2;N_IS_INT]) THEN
        (SIMP_TAC [FACT;GSYM REAL_OF_NUM_MUL;REAL_MUL_DIV_ASSOC;lem8]);
        (STRIP_TAC) THEN
        (SIMP_TAC [lem9;FACT_NZ;REAL_OF_NUM_EQ;REAL_DIV_REFL;N_IS_INT])
      ]
    ]
)
let SATURDAY_LEMMA = PROVE(
    `!x. p > 1 ==> m >= p ==> x * ((&(FACT m))/(&(FACT (p-1)))) = x * (&p) * ((&(FACT m))/(&(FACT p)))`,
    let lem01 = UNDISCH (ARITH_RULE `p > 1 ==> SUC (p -1) = p`) in
    let lem02 = ADD_ASSUM `p > 1` (SPEC `p - 1` (CONJUNCT2 FACT)) in
    let lem03 = GSYM (ONCE_REWRITE_RULE [lem01] lem02) in
    let lem04 =  SPEC `&p` REAL_DIV_REFL in
    let lem05 = ADD_ASSUM `p > 1` (SPECL [`p:num`;`0`] REAL_OF_NUM_EQ) in
    let lem06 = SIMP_RULE [UNDISCH (ARITH_RULE `p > 1 ==> ~(p = 0)`)] lem05 in
    let lem07 = GSYM (MP lem04 lem06) in
    (REPEAT STRIP_TAC) THEN
    (CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [GSYM REAL_MUL_LID]))) THEN
    (ONCE_REWRITE_TAC [lem07]) THEN
    (ONCE_REWRITE_TAC [real_div]) THEN
    (ONCE_REWRITE_TAC [REAL_ARITH `((x1:real) * x2) * x * (x3 * x4) = x * x1 * (x3 * (x2 * x4))`]) THEN
    (ONCE_REWRITE_TAC [GSYM REAL_INV_MUL]) THEN
    (ONCE_REWRITE_TAC [REAL_OF_NUM_MUL]) THEN
    (SIMP_TAC [REAL_MUL_ASSOC;GSYM REAL_INV_MUL]) THEN
    (ONCE_REWRITE_TAC [lem03]) THEN
    (SIMP_TAC [REAL_MUL_ASSOC;GSYM REAL_OF_NUM_MUL])
)
let SHRIVER = PROVE(
    `!f0. (!i. m <= i /\ i <= SUC n ==> (f0 i))
       ==> (!i. m <= i /\ i <= n ==> (f0 i)) `,
    let lem01 = UNDISCH_ALL (ARITH_RULE `i <= n ==> i <= SUC n`) in
    let lem02 = CONJ (ASSUME `(m:num) <= (i:num)`) lem01  in
    let lem03 = ASSUME `!i. m <= i /\ i <= SUC n ==> (f0 i)` in
    let lem04 = SPEC_ALL lem03 in
    let lem05 = MP lem04 lem02 in
    (REPEAT STRIP_TAC) THEN (ACCEPT_TAC lem05)
)
let IS_INT_SUM = PROVE(
 `!f n m.(!i.m <= i /\  i <= n ==> integer (f i)) ==> integer (sum (m..n) f)`,
  let l0 = SPECL [`m:num`;`n:num`;`i:num`] IN_NUMSEG in
  let l1 = SPECL [`m:num`;`SUC n`] NUMSEG_EMPTY in
  let l2 = ADD_ASSUM `SUC n < m` l1 in
  let l3 = ASM_REWRITE_RULE [] l2 in
  let l4 = (UNDISCH o ARITH_RULE) `~(SUC n < m) ==> m <= SUC n` in
  let l5 = ONCE_REWRITE_RULE [GSYM IN_NUMSEG] SHRIVER in
  let l6 = SPEC `\(i:num).(integer (f i))` l5 in
  let l7 = BETA_RULE l6 in
  let l8 = ASSUME `! m. (!i. i IN m..n ==> integer (f i)) ==> integer (sum (m..n) f)` in
  let l9 = SPEC_ALL l8 in
  let l10 = UNDISCH (IMP_TRANS l7 l9) in
  let jj0 = ARITH_RULE `(~(SUC n < m)) ==> m <= SUC n /\ (SUC n) <= SUC n` in
  let jj1 = UNDISCH (ONCE_REWRITE_RULE [GSYM IN_NUMSEG] jj0) in
  let jj2 = SPEC `SUC n` (ASSUME `!i. i IN m.. SUC n ==> integer (f i)`) in
  let jj3 = (MP jj2 jj1) in
  let l18 = CONJ l10 jj3 in
  let l19 = MATCH_MP INTEGER_ADD l18 in
  let l20 = DISCH `!i. i IN m..SUC n ==> integer (f i)` l19 in
  let l21 = ASSUME `!i . i = 0 ==> integer (f 0)` in
  let l22 = SIMP_RULE [] (SPEC `0` l21) in
  (ONCE_REWRITE_TAC [GSYM l0]) THEN STRIP_TAC THEN
  INDUCT_TAC THENL
  [ STRIP_TAC THEN
    (ASM_CASES_TAC `m = 0`) THENL
    [ (ASM_SIMP_TAC []) THEN
      (ONCE_REWRITE_TAC [NUMSEG_CONV `0..0`]) THEN
      (ONCE_REWRITE_TAC [ SUM_SING]) THEN
      (SIMP_TAC [IN_SING]) THEN (DISCH_TAC) THEN (SIMP_TAC [l22]);
      (ASM_SIMP_TAC [NUMSEG_CLAUSES;SUM_CLAUSES;N_IS_INT])
    ];
    STRIP_TAC THEN (ASM_CASES_TAC `SUC n < m`) THENL
    [ (ASM_SIMP_TAC [l3;SUM_CLAUSES;N_IS_INT]);
      (ASM_SIMP_TAC [l4;SUM_CLAUSES_NUMSEG]) THEN
      (ACCEPT_TAC l20)
    ]
  ]
)
let ALL_IMP_EL = PROVE(
    `! (l:(a)list) i P. (ALL P l) ==> (i < LENGTH l) ==> P (EL i l)`,
    SIMP_TAC[GSYM ALL_EL]
)
let KEY_LEMMA = PROVE(
    `n > 0 ==>
     p > 0 ==>
    ! i . p <= i /\ i <= (LENGTH (As n p) - 1) ==> integer ((&(FACT i)/ &(FACT p)) * (EL i (As n p)))`,
    let jem0 = ISPECL [`(As n p)`;`i:num`;`integer`] ALL_IMP_EL in
    let jem1 = MP jem0 (UNDISCH (UNDISCH (SPEC_ALL ALL_integer_As)))  in
    let jem3 = ARITH_RULE `LENGTH (As n p) > 0 ==> ((i < LENGTH (As n p)) <=> i <= LENGTH (As n p) - 1)` in
    let jem4 = UNDISCH_ALL ((SPEC_ALL LENGTH_As)) in
    let jem5 = UNDISCH (ARITH_RULE `p > 0 ==> (LENGTH (As n p) >= p) ==> (LENGTH (As n p) > 0)`) in
    let jem6 = MP jem5 jem4 in
    let jem7 = MP jem3 jem6 in
    let jem8 = ONCE_REWRITE_RULE [jem7] jem1 in
    let kem0 = SPECL [`i:num`;`p:num`] IS_INT_FACT_DIV in
    let kem1 = ADD_ASSUM  `p <= (i:num)` (ADD_ASSUM `i <= (LENGTH (As n p) - 1)` kem0) in
    let kem2 = SIMP_RULE [UNDISCH_ALL (ARITH_RULE `p <= i ==> i <= LENGTH (As n p) -1 ==> i >= p`)] kem1 in
    (REPEAT STRIP_TAC) THEN (SIMP_TAC[UNDISCH jem8;kem2;INTEGER_MUL])
)

let KEY_LEMMA2 = PROVE(
    `p > 1 ==>
     n > 0 ==>
     ? K0 .   integer K0
           /\ (&1 / &(FACT ( p - 1))) * (sum (p.. LENGTH (As n p) -1) (\m. EL m (As n p) * &(FACT m))) = (&p) * K0`,
    let lem0000 = SPEC `EL m (As n p)` SATURDAY_LEMMA in
    let lem1000 = DISCH `m <= LENGTH (As n p) -1` (ADD_ASSUM `m <= LENGTH (As n p) -1` (UNDISCH_ALL lem0000)) in
    let lem2000 = DISCH `(m:num) >= p` lem1000 in
    let lem3000 = ONCE_REWRITE_RULE [ARITH_RULE `(m:num) >= p <=> p <= m`] lem2000 in
    let lem4000 = ONCE_REWRITE_RULE [TAUT `(a ==> b ==> c) <=> ((a  /\ b) ==> c)`] (GEN `m:num` lem3000) in
    let lem5000 = MATCH_MP SUM_EQ_NUMSEG lem4000 in
    let nem2 = SPECL [`\x.(&(FACT x)/ &(FACT p)) * (EL x (As n p))`;`LENGTH (As n p) - 1`;`p:num`] IS_INT_SUM in
    let nem3 = BETA_RULE nem2 in
    let nem4 = SIMP_RULE [UNDISCH (UNDISCH KEY_LEMMA)] nem3 in
    let nem5 = ADD_ASSUM `p > 1` (DISCH `p > 0` nem4) in
    let nem6 = SIMP_RULE [(UNDISCH o ARITH_RULE) `(p:num) > 1 ==> p > 0`] nem5 in
    STRIP_TAC THEN STRIP_TAC THEN (ONCE_REWRITE_TAC [GSYM SUM_LMUL]) THEN
    (BETA_TAC) THEN (ONCE_REWRITE_TAC [real_div]) THEN (ONCE_REWRITE_TAC [REAL_MUL_LID]) THEN
    (ONCE_REWRITE_TAC [REAL_ARITH `(x1:real) * x2 * x3 = x2 * (x3 * x1)`]) THEN
    (ONCE_REWRITE_TAC [GSYM real_div]) THEN (ONCE_REWRITE_TAC [lem5000]) THEN
    (ONCE_REWRITE_TAC [REAL_ARITH `(x1:real) * x2 * x3 = x2 * (x3 * x1)`]) THEN
    (ONCE_REWRITE_TAC [SUM_LMUL]) THEN
    (EXISTS_TAC `sum (p .. LENGTH (As n p) -1) (\x. &(FACT x) / &(FACT p) * EL x (As n p))`) THEN
    (SIMP_TAC [nem6])
)
let NOT_g_NIL = PROVE(
    `!n p . ~ ((g n p ) = [])`,
     SIMP_TAC [Pm_eqn5.PLANETMATH_EQN_5; NOT_CONS_NIL; NOT_POLY_EXP_NIL; NOT_POLY_CMUL_NIL;
               NOT_POLY_MUL_NIL;NOT_POLY_MUL_ITER_NIL]
)
let FACT_DIV_RCANCELS = PROVE(
    `!n x. x / &(FACT n) * &(FACT n) = x`,
    MESON_TAC [REAL_ARITH `!x. &0 < x ==> ~(x = &0)`;
               REAL_DIV_RMUL;FACT_LT;REAL_OF_NUM_LT]
)

let PSUM_ITERATE = PROVE(
    `! n m f. psum (m,n) f
              = if (n > 0) then (iterate (+) (m..((n+m)-1)) f) else &0`,
    let lem01 = ARITH_RULE `~(n+m=0) ==> (SUC n + m) -1 = SUC ((n + m) -1)` in
    let lem02 = MP (ISPEC `(+)` ITERATE_SING) MONOIDAL_REAL_ADD in
    let lem03 = PROVE(
          `iterate (+) (m..SUC ((n + m) - 1)) f
           = f (SUC ((n+m)-1)) + iterate (+) (m..(n+m)-1) f`,
           MESON_TAC [ARITH_RULE `m <= SUC ((n+m)-1)`;ITERATE_CLAUSES_NUMSEG;
                      MONOIDAL_REAL_ADD;REAL_ADD_SYM]) in
    let lem04 = UNDISCH (UNDISCH (ARITH_RULE `~(n+m=0) ==> n=0 ==> m-1 < m`)) in
    let lem05 = SIMP_RULE [lem04] (SPECL [`m:num`;`m-1`] NUMSEG_EMPTY) in
    INDUCT_TAC THENL
    [ SIMP_TAC [ARITH_RULE `~(0 > 0)`;sum_DEF];
      (SIMP_TAC [ARITH_RULE `(SUC n) > 0`]) THEN (REPEAT STRIP_TAC) THEN
      (ASM_CASES_TAC `n + m =0`) THENL
      [ (REWRITE_TAC [UNDISCH (ARITH_RULE `n + m = 0 ==> n = 0`)]) THEN
        (REWRITE_TAC [lem02;NUMSEG_SING;ARITH_RULE `(SUC 0 +m) -1 = m`]) THEN
        (MESON_TAC [sum_DEF; ADD_CLAUSES;REAL_ARITH `&0 + x = x`]) ;
        (ONCE_REWRITE_TAC [sum_DEF;UNDISCH lem01]) THEN
        (REWRITE_TAC [lem03]) THEN (ASM_CASES_TAC `n = 0`) THEN
        (ASM_SIMP_TAC
          [ARITH_RULE `~(0 > 0)`;ADD_CLAUSES;REAL_ADD_LID;REAL_ADD_RID;
           lem05;ITERATE_CLAUSES_GEN; MONOIDAL_REAL_ADD;NEUTRAL_REAL_ADD;
           REAL_ADD_SYM;ADD_SYM;ARITH_RULE `~(n=0) ==> n>0 /\ SUC (n-1) = n`])
      ]
    ]
)


let PLANETMATH_EQN_5_2 = PROVE(
    `p > 1 ==>
     n > 0 ==>
     (? K0.   integer K0
           /\ poly (SOD (g n p)) (&0) =
              &(FACT n) pow p * -- &1 pow (n * p) + &p * K0)`,
    let lem01 = SPECL [`g n p`;`x:real`;`(&0):real`] Pm_lemma2.PLANETMATH_LEMMA_2_B in
    let lem02 = GEN_ALL lem01 in
    let lem03 = SPEC_ALL (BETA_RULE lem02) in
    let lem04 = SIMP_RULE [FACT_DIV_RCANCELS] lem03 in
    let lem05 = SIMP_RULE [PSUM_ITERATE] lem04 in
    let lem06 = SIMP_RULE [ARITH_RULE `(n:num) + 0 = n`] lem05 in
    let lem07 = ADD_ASSUM `n > 0` (ADD_ASSUM `p > 0` lem06) in
    let lem08 = REWRITE_RULE [GSYM LENGTH_EQ_NIL;ARITH_RULE `~(x = 0) <=> x > 0`] NOT_g_NIL in
    let lem09 = SIMP_RULE [lem08] lem07 in
    let lem10 = CONV_RULE (RAND_CONV (REWRITE_CONV [UNDISCH_ALL (SPEC_ALL g_eq_As)])) lem09 in
    let lem11 = SIMP_RULE [POLY_CMUL_LENGTH] lem10 in
    let lem12 = SPECL [`m:num`;`(As n p)`] EL_PDI_AT_ZERO in
    let lem13 = SIMP_RULE [POLY_CMUL_PDI;POLY_CMUL;lem12] lem11 in
    let lem14 = GSYM (BETA `(\m. poly (poly_diff_iter (As n p) m) (&0)) m`) in
    let lem15 = ISPECL [`(\m. poly (poly_diff_iter (As n p) m) (&0))`;`&1/ &(FACT (p - 1))`;`0..LENGTH (As n p) -1`] SUM_LMUL in
    let lem16 = ONCE_REWRITE_RULE [lem14] lem13 in
    let lem17 = ONCE_REWRITE_RULE [GSYM sum] lem16 in
    let lem18 = SIMP_RULE [GSYM lem17] lem15 in
    let lem20 = SPECL [`(\m.  poly (poly_diff_iter (As n p) m) (&0))`;`(\m. EL m (As n p) * &(FACT m))`;`0`;`LENGTH (As n p) - 1`] SUM_EQ_NUMSEG in
    let lem21 = ONCE_REWRITE_RULE [ARITH_RULE `0 <= i`] (BETA_RULE lem20) in
    let lem22 = ADD_ASSUM `~(As n p = [])` (ONCE_REWRITE_RULE [EL_PDI_AT_ZERO2] lem21) in
    let lem30 = SPECL [`i:num`;`As n p`] EL_PDI_AT_ZERO2 in
    let lem31 = ASM_REWRITE_RULE [] (ADD_ASSUM `~(As n p = [])` lem30) in
    let lem23 = ONCE_REWRITE_RULE [lem31] lem22 in
    let lem24 = REWRITE_RULE [GSYM lem16] lem23 in
    let lem25 = ONCE_REWRITE_RULE [lem24] lem18 in
    let lem30 = ISPECL [`\m. EL m (As n p) * &(FACT m)`;`0`;`p-1`;`(LENGTH (As n p) - 1) - (p - 1)`] SUM_ADD_SPLIT in
    let lem31 = SIMP_RULE [ARITH_RULE `0 <= x`] lem30 in
    let lem32 = UNDISCH_ALL (ARITH_RULE `! x. x  >= p ==> (p - 1) + (x - 1) - (p -1)=  x - 1`) in
    let lem33 = UNDISCH_ALL (SPEC_ALL LENGTH_As) in
    let lem34 = SPEC `LENGTH (As n p)` lem32 in
    let lem35 = MP lem34 lem33 in
    let lem36 = ONCE_REWRITE_RULE [UNDISCH (ARITH_RULE `p > 1 ==> (p - 1) + 1 = p`);lem35] lem31 in
    let lem37 = ONCE_REWRITE_RULE [lem36] lem25 in
    let lem38 = SIMP_RULE [UNDISCH (ARITH_RULE `p > 1 ==> p > 0`)] (DISCH `p > 0` lem37) in
    let lem39 = ISPECL [`\m. EL m (As n p) * &(FACT m)`;`0`;`p-2`;`1`] SUM_ADD_SPLIT in
    let lem40 = ADD_ASSUM `n > 0` (ADD_ASSUM `p > 1` lem39) in
    let lem41 = SIMP_RULE (map (UNDISCH o ARITH_RULE) [`p > 1 ==> p - 2 + 1 = p-1`;`p > 1 ==> (p - 2) + 1 = p - 1`]) lem40 in
    let lem42 = SIMP_RULE [SUM_SING_NUMSEG;ARITH_RULE `0 <= x`] lem41 in
    let lem45 = ADD_ASSUM `p > 1` (SPEC_ALL prefix_As_zero) in
    let lem46 = SIMP_RULE [UNDISCH_ALL (ARITH_RULE `p > 1 ==> p > 0`)] lem45 in
    let lem47 = UNDISCH (ONCE_REWRITE_RULE [UNDISCH_ALL (ARITH_RULE `p > 1 ==> (i < p-1 <=> i <= p-2)`)] lem46) in
    let lem48 = SIMP_RULE [REAL_ARITH `((&0):real) + x = x`; SUM_EQ_0_NUMSEG;REAL_ARITH `((&0):real) * x = &0`;lem47] lem42 in
    let lem49 = SIMP_RULE [UNDISCH (ARITH_RULE `p > 1 ==> p > 0`)] (ADD_ASSUM `p > 1` (SPEC_ALL fact_As)) in
    let lem50 = SIMP_RULE [UNDISCH lem49] lem48 in
    let lem51 = ONCE_REWRITE_RULE [lem50] lem38 in
    let lem52 = SPECL [`p - 1`;`(&1):real`] FACT_DIV_RCANCELS in
    let lem53 = SIMP_RULE [REAL_ARITH `(x:real) * (y * z) = (x * z) * y`;lem52;REAL_ARITH `(x:real) * (y + z) = (x * y) + (x * z)`] lem51 in
    let lem54 = SIMP_RULE [REAL_ARITH `&1 * x = (x:real)`] lem53 in
    let josh0 = UNDISCH_ALL KEY_LEMMA2 in
    let josh1 = REAL_ARITH `!(y:real) x1 x2 . x1  = x2 <=> y + x1 = y + x2` in
    let josh2 = SPEC `(&(FACT n) pow p * -- &1 pow (n * p)):real` josh1 in
    let josh3 = ONCE_REWRITE_RULE [josh2] josh0 in
    let josh4 = ONCE_REWRITE_RULE [GSYM lem54] josh3 in
    let josh5 = DISCH `~ (As n p = [])` josh4 in
    let jem4 = ADD_ASSUM `p > 1` ((SPEC_ALL LENGTH_As)) in
    (* JOHN: the UNDISCH here is necessary... i don't think it should be *)
    let jem5 = UNDISCH (SIMP_RULE [UNDISCH (ARITH_RULE `(p:num) > 1 ==> p > 0`)] jem4) in
    let jem6 = UNDISCH (ARITH_RULE `p > 1 ==> (LENGTH (As n p) >= p) ==> ~((LENGTH (As n p) = 0))`)  in
    let jem7 = MP jem6 jem5  in
    let jem8 = SIMP_RULE [LENGTH_EQ_NIL] jem7 in
    let josh6 = MP josh5 jem8 in
    let josh7 = DISCH_ALL josh6 in
    let josh11 = ONCE_REWRITE_RULE [GSYM OLD_SUM] lem17 in
    let josh12 = REWRITE_RULE [GSYM josh11] josh7 in
    let josh13 =  SIMP_RULE [] (DISCH_ALL josh12) in
    let josh14 = BRW `(X ==> Y ==> Z ==> W) <=> ((X /\ Y /\ Z) ==> W)` josh13 in
    let josh15 = ONCE_REWRITE_RULE [ARITH_RULE `(p > 0 /\ n > 0 /\ p > 1) <=> (p > 1 /\ n > 0)`] (DISCH_ALL josh14) in
    let josh16 = BRW1 josh15 in
    let josh17 = SIMP_RULE [PSUM_ITERATE;ARITH_RULE `~(0 > 0)`] josh16 in
    ACCEPT_TAC josh17
)
let PLANETMATH_DIVIDES_FACT_PRIME_1 = PROVE (
    `!p n. (prime p) /\ p > n ==> ~(num_divides p (FACT n))`,
    (SIMP_TAC [DIVIDES_FACT_PRIME]) THEN ARITH_TAC
)
let INT_OF_REAL_NEG_NUM = PROVE(
    `!(n:num).int_of_real (-- (real_of_num n)) = -- (int_of_real (real_of_num n))`,
    SIMP_TAC [GSYM int_of_num;GSYM int_of_num_th;GSYM int_neg]
)
let ABS_EQ_ONE = PROVE(
    `!(x:real) .((abs x) = &1) ==> ((x = &1) \/ (x = -- &1))`,
    ARITH_TAC
)
let POW_NEG_1 = PROVE(
   `!(x:num). (((-- (&1 :real)) pow x) = -- &1) \/  (((-- (&1 : real)) pow x) = &1)`,
    let lem00 = ONCE_REWRITE_RULE [TAUT `x \/ y <=> y \/ x`] ABS_EQ_ONE in
    let lem01 = (SPEC `(-- (&1 :real)) pow x` lem00) in
    let lem02 = (SPEC `x:num` POW_M1) in
    let lem03 = MP lem01 lem02 in
    STRIP_TAC THEN (ACCEPT_TAC lem03)
)
let NUM_DIVIDES_INT_DIVIDES = PROVE(
    `!(x:num) (y:num).(x divides y) <=> ((&x):int divides ((&y):int))`,
    (ONCE_REWRITE_TAC [num_divides])  THEN (SIMP_TAC [])
)
let SON_OF_A_GUN = PROVE(
    `! (p:num) (n:num) .
     p > n
     ==> (prime p)
     ==> ~(int_divides (& p) (&(FACT n) pow p * -- &1 pow (n * p) ))`,
    let POW_INT_NEG_1 = INT_OF_REAL_THM POW_NEG_1 in
    let lem0000 = TAUT `(A /\ B ==> C) <=> (A ==> B ==> C)` in
    let lem0001 = ONCE_REWRITE_RULE [lem0000] PLANETMATH_DIVIDES_FACT_PRIME_1 in
    let lem0002 = UNDISCH_ALL (SPEC_ALL lem0001) in
    let lem0008 = ONCE_REWRITE_RULE [TAUT `(x /\ y ==> z) <=> (x ==> ~z ==> ~y)`]  PRIME_DIVEXP in
    let lem0009 = SPECL [`p:num`;`p:num`;`FACT n`] lem0008 in
    let lem0010 = UNDISCH lem0009 in
    let lem0011 = MP lem0010 lem0002 in
     STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
     (DISJ_CASES_TAC (SPEC `(n * p):num` POW_INT_NEG_1))  THENL
     [ (ASM_SIMP_TAC [INT_OF_NUM_POW; ARITH_RULE `x * (--(&1):int) = -- x`;ARITH_RULE `x * ((&1):int) = x`]) THEN
       (ONCE_REWRITE_TAC [GSYM INT_DIVIDES_RNEG]) THEN
       (ONCE_REWRITE_TAC [ARITH_RULE `-- -- (x:int) = x`]) THEN
       (ONCE_REWRITE_TAC [GSYM NUM_DIVIDES_INT_DIVIDES]) THEN
       (ACCEPT_TAC lem0011);
       (ASM_SIMP_TAC [INT_OF_NUM_POW; ARITH_RULE `x * (--(&1):int) = -- x`;ARITH_RULE `x * ((&1):int) = x`]) THEN
       (ONCE_REWRITE_TAC [GSYM NUM_DIVIDES_INT_DIVIDES]) THEN
       (ACCEPT_TAC lem0011)
     ]
)
let MAY_LEMMA = PROVE(
    `(p:num) > (n:num)
      ==> (prime p)
      ==> ~(int_divides (& p) ((int_of_num (FACT n)) pow p * -- &1 pow (n * p) + &p * K0))`,
      let lem00 = BRW `(x /\ y ==> z) <=> (x ==> ~z ==> ~y)` INT_DIVIDES_ADD_REVR in
      let lem0 = PROVE(`int_divides ((&p):int) (&p * K0)`,INTEGER_TAC) in
      let lem1 = (UNDISCH_ALL o SPEC_ALL) SON_OF_A_GUN in
      let lem2 = SPECL [`(&p):int`;`((&p):int) * K0`; `(&(FACT n) pow p):int *
      -- &1 pow (n * p)` ] lem00 in
      let lem3 = MP (MP lem2 lem0) lem1 in
      let lem4 = (DISCH_ALL lem3) in
      let lem5 = ONCE_REWRITE_RULE [ARITH_RULE `(x:int) + y = y + x`] lem4 in
      (ACCEPT_TAC lem5)
)
let PLANET_MATH_alpha_1 = PROVE(
    `n > 0 ==> p > n ==> prime p ==> (integer (poly (SOD (g n p )) (&0)))`,
    let a1 = UNDISCH (UNDISCH (ARITH_RULE `n > 0 ==> p > n ==> p > 1`)) in
    let a2 = UNDISCH (SIMP_RULE [] (DISCH `n > 0` (MP PLANETMATH_EQN_5_2 a1))) in
    let t1 = `integer K0 /\
              poly (SOD (g n p)) (&0) =
              &(FACT n) pow p * -- &1 pow (n * p) + &p * K0` in
    (STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC) THEN (CHOOSE_TAC a2) THEN
    (SPLIT_CONJOINED_ASSUMPT_TAC t1) THEN (ASM_REWRITE_TAC[]) THEN
    (ASM_SIMP_TAC [N_IS_INT;INTEGER_ADD;NEG_N_IS_INT;INTEGER_POW;INTEGER_MUL])
)
let PLANET_MATH_alpha_2 = PROVE(
    `n > 0 ==> p > n ==> prime p ==>
     ( ~((&p) divides (int_of_real (poly (SOD (g n p )) (&0)))))`,
    let t1 = `integer K0 /\
              poly (SOD (g n p)) (&0) =
              &(FACT n) pow p * -- &1 pow (n * p) + &p * K0` in
    let t = `((real_of_num (FACT n)) pow p) * (-- &1 pow (n * p)) + (&p * K0)` in
    let arch0 = INT_OF_REAL_CONV t in
    let a1 = UNDISCH (UNDISCH (ARITH_RULE `n > 0 ==> p > n ==> p > 1`)) in
    let a2 = UNDISCH (SIMP_RULE [] (DISCH `n > 0` (MP PLANETMATH_EQN_5_2 a1))) in
    let a3 = SPEC `int_of_real K0` (GEN `K0:int` MAY_LEMMA) in
    let a4 = GSYM (UNDISCH arch0) in
    let a5 = ONCE_REWRITE_RULE [a4] a3 in
    STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN (CHOOSE_TAC a2) THEN
    (SPLIT_CONJOINED_ASSUMPT_TAC t1) THEN (ASM_SIMP_TAC [a5])
)
let INT_OF_REAL_NEG_INT_OF_NUM = PROVE(
    `!n. int_of_real(-- (real_of_num n)) = -- int_of_num n`,
    SIMP_TAC [int_of_num;INT_OF_REAL_NEG_NUM]
)
let PLANET_MATH_alpha_3 = PROVE(
     `n > 0 ==> p > n ==> prime p ==>
      (~((poly (SOD (g n p)) (&0)) = &0))`,
      let lem0 = PROVE(
            `!(x:num) (y:real).
               (x > 0) ==>
               (integer y) ==>
               (~(&x divides (int_of_real y))) ==>
               ~(y = &0)`,
              MESON_TAC [is_int;INT_OF_NUM_GT;INT_DIVIDES_RNEG;REAL_OF_NUM_EQ;int_of_num;INT_OF_REAL_NEG_INT_OF_NUM;INT_OF_NUM_EQ;INT_DIVIDES_0]) in
      let lem1 = ARITH_RULE `n > 0 ==> p > n ==> p > 0` in
      MESON_TAC [lem0;lem1; PLANET_MATH_alpha_1; PLANET_MATH_alpha_2]
)
let PLANET_MATH_alpha = PROVE(
    `n > 0 ==> p > n ==> prime p ==>
     (     (integer (poly (SOD (g n p )) (&0)))
       /\ ~((&p) divides (int_of_real (poly (SOD (g n p )) (&0))))
       /\ ~((poly (SOD (g n p)) (&0)) = &0))`,
     SIMP_TAC [PLANET_MATH_alpha_1; PLANET_MATH_alpha_2; PLANET_MATH_alpha_3]
)
let REAL_FACT_NZ = PROVE(
    `~((&(FACT n)) = (real_of_num 0))`,
    let l0 = GSYM (SPECL [`FACT n`;`0`] REAL_OF_NUM_EQ) in
    ACCEPT_TAC (SPEC_ALL (ONCE_REWRITE_RULE [l0] FACT_NZ))
)

let IS_INT_FACT_DIV_FACT_DIV_FACT = PROVE(
    `! i k.integer ((&(FACT (i+k)))/(&(FACT i))/(&(FACT k)))`,
    let l0 = MATCH_MP (ARITH_RULE `(~(x=0)) ==> 0 < x`) (SPEC `k:num` FACT_NZ) in
    let l1 = ONCE_REWRITE_RULE [GSYM REAL_OF_NUM_LT] l0 in
    let l2 = MATCH_MP REAL_EQ_LDIV_EQ l1 in
    (REPEAT STRIP_TAC) THEN (REWRITE_TAC [is_int;l2]) THEN
    (EXISTS_TAC ` (binom(i+k,k))`) THEN DISJ1_TAC THEN
    (MESON_TAC [BINOM_FACT;MULT_SYM;MULT_ASSOC;REAL_OF_NUM_MUL;REAL_OF_NUM_EQ])
)

(*  if you replace the second SIMP_TAC with MESON_TAC, it fails!!
 *  (i alwasy thought MESON_TAC was strictly stronger than SIMP_TAC
 *)
let POLY_CMUL_EL = PROVE(
    `!p c i.(i < (LENGTH p)) ==> (EL i (c ## p)) = c * (EL i p)`,
    let l0 = ARITH_RULE `(SUC i) < (SUC j) <=> i < j` in
    LIST_INDUCT_TAC THENL
    [ (SIMP_TAC [LENGTH;ARITH_RULE `~(n < (0:num))`]);
      STRIP_TAC THEN INDUCT_TAC THENL
      [ (SIMP_TAC [poly_cmul;HD;EL]);
        (ASM_SIMP_TAC [LENGTH;poly_cmul;TL;EL;l0])
      ]
    ]
)
let PDI_COEFF_FACT = PROVE(
    `! k q i.(i < LENGTH (poly_diff_iter q k)) ==>
            (EL i (poly_diff_iter q k)) = ((&(FACT (i+k)))/(&(FACT i))) * (EL (i+k) q)`,
    let t0 = `!q i.  i < LENGTH (poly_diff_iter q k)
                  ==> EL i (poly_diff_iter q k) = &(FACT (i + k)) / &(FACT i) * EL (i + k) q` in
    let l0 = SPECL [`q:(real)list`;`SUC i`] ( ASSUME t0) in
    let l1 = ONCE_REWRITE_RULE [ARITH_RULE `(SUC i) < x <=> i < (PRE x)`] l0 in
    let l2 = ONCE_REWRITE_RULE [GSYM LENGTH_POLY_DIFF] l1 in
    let l3 = ONCE_REWRITE_RULE [FACT;GSYM REAL_OF_NUM_MUL] l2 in
    let l4 = ONCE_REWRITE_RULE [GSYM REAL_OF_NUM_MUL] l3 in
    let l5 =  REWRITE_RULE [real_div;REAL_INV_MUL] l4 in
    let l6 = REAL_ARITH `(w * (inv x) * y ) * z = (w * y * z) * (inv x)` in
    let l9 = ONCE_REWRITE_RULE [GSYM REAL_OF_NUM_LT] (ARITH_RULE `0 < SUC i`) in
    let l10 = MATCH_MP REAL_EQ_RDIV_EQ l9 in
    let l11 = ONCE_REWRITE_RULE [l6] l5 in
    let l12 = ONCE_REWRITE_RULE [real_div] l10 in
    let l13 = ONCE_REWRITE_RULE [l12] l11 in
    INDUCT_TAC THENL
    [ (REWRITE_TAC [Pm_lemma1.PDI_DEF;ARITH_RULE `i + 0 = i`]) THEN
      (MESON_TAC [REAL_DIV_REFL;FACT_NZ;REAL_OF_NUM_EQ;REAL_ARITH `(real_of_num 1) * x = x`]);
      (ONCE_REWRITE_TAC [Pm_lemma1.PDI_DEF]) THEN (SIMP_TAC [EL_POLY_DIFF]) THEN
      (ONCE_REWRITE_TAC [ARITH_RULE `i + (SUC k) = (SUC i) + k`]) THEN
      (ONCE_REWRITE_TAC [FACT]) THEN (ONCE_REWRITE_TAC [real_div]) THEN
      (SIMP_TAC [l13;real_div;REAL_MUL_ASSOC])
    ]
)
(* I think this should hold if we replace [--a;&1] with an arbitrary polynomial q,
 * however the existing ORDER* theorems would not be sufficient to prove it and
 * I don't feel like putting in the effort right now
 *)
let POLY_DIVIDES_POLY_DIFF = PROVE(
    `!p n a.
         (poly_divides (poly_exp [--a;&1] (SUC n)) p)
         ==> (poly_divides (poly_exp [--a;&1] n) (poly_diff p))`,
    let l0 = ARITH_RULE `op = SUC odp ==> SUC n <= op ==> n <= odp` in
    let l1 = ARITH_RULE `(SUC n <= m ) ==> ~(m = 0)` in
    MESON_TAC [l0;l1;POLY_DIFF_ZERO;ORDER_DIVIDES;ORDER_DIFF]
)
let POLY_DIVIDES_MUL = PROVE(
    `!p1 p2 p3.poly_divides p1 p2 ==> poly_divides p1 (p2 ** p3)`,
    (ONCE_REWRITE_TAC [divides]) THEN (REPEAT STRIP_TAC) THEN
    (EXISTS_TAC `q ** p3`) THEN
    (ASM_MESON_TAC [FUN_EQ_THM;POLY_MUL;POLY_MUL_ASSOC])
)
let POLY_DIVIDES_MUL3 = PROVE(
    `!p1 p2 p3.(poly_divides p1 p2) ==> (poly_divides p1 (p3 ** p2))`,
    (ONCE_REWRITE_TAC [divides]) THEN (REPEAT STRIP_TAC) THEN
    (EXISTS_TAC `p3 ** q`) THEN (UNDISCH_TAC `poly (p2) = poly (p1 ** q)`) THEN
    (ONCE_REWRITE_TAC [FUN_EQ_THM]) THEN (REWRITE_TAC [POLY_MUL]) THEN
    (MESON_TAC [REAL_MUL_ASSOC;REAL_MUL_SYM])
)
let POLY_DIVIDES_POLY_MUL_ITER = PROVE(
    `!f n v. 1 <= v ==> v <= n ==> poly_divides (f v) (poly_mul_iter f n)`,
    let l1 = ARITH_RULE `~(v <= n) ==> (v <= SUC n) ==> v = SUC n` in
    let l2 = UNDISCH (UNDISCH l1) in
    STRIP_TAC THEN INDUCT_TAC THENL
    [ ARITH_TAC;
      (ONCE_REWRITE_TAC [Pm_eqn5.POLY_MUL_ITER]) THEN STRIP_TAC THEN
      (ASM_CASES_TAC `v <= (n:num)`) THENL
      [ ASM_MESON_TAC [POLY_DIVIDES_MUL3];
        STRIP_TAC THEN STRIP_TAC THEN
        (MESON_TAC [l2;POLY_DIVIDES_MUL;POLY_DIVIDES_REFL]) ]
    ]
)
(*
 *  This one was suprisingly tricky to prove...
 *)
let POLY_DIVIDES_POLY_EXP2 = PROVE(
    `!n p1 p2.(poly_divides p1 p2) ==> poly_divides (poly_exp p1 n) (poly_exp p2 n)`,
    let t0 = `!p1 p2.
                (?q. poly p2 = poly (p1 ** q))
                ==> (?q. poly (poly_exp p2 n) = poly (poly_exp p1 n ** q))` in
    let l0 = ASSUME t0 in
    let l1 = UNDISCH (REWRITE_RULE [divides] (SPEC_ALL l0)) in
    let l3 = PROVE(
        `(x2 = x5 * x6 /\ x1 = x4 * x7) ==> (x1:real) * x2 = (x4 * x5) * x6 * x7`,
         MESON_TAC [REAL_MUL_SYM;REAL_MUL_ASSOC]) in
   (ONCE_REWRITE_TAC [divides]) THEN INDUCT_TAC THENL
   [ (MESON_TAC [divides;poly_exp;POLY_DIVIDES_REFL]);
     (STRIP_TAC THEN STRIP_TAC THEN DISCH_TAC) THEN (CHOOSE_TAC l1) THEN
     (UNDISCH_TAC `?q. poly p2 = poly (p1 ** q)`) THEN STRIP_TAC THEN
     (ONCE_REWRITE_TAC [poly_exp]) THEN (EXISTS_TAC `q ** q'`) THEN
     (REWRITE_TAC [poly_exp;FUN_EQ_THM;POLY_MUL]) THEN
     (ASM_MESON_TAC [l3;FUN_EQ_THM;POLY_MUL])
   ]
)
let POLY_EXP_ONE = PROVE(
    `!p .p = poly_exp p 1`,
    MESON_TAC [poly_exp;ARITH_RULE `1 = SUC 0`;POLY_MUL_RID]
)
let POLY_DIVIDES_ROOT = PROVE(
    `!p a.poly_divides [--a;&1] p ==> (poly p a) = &0`,
    MESON_TAC [ORDER_ROOT;ORDER_DIVIDES;POLY_EXP_ONE;
               ARITH_RULE `1 <= ord ==> ~(ord = 0)`]
)

let POLY_DIVIDES_PDI = PROVE(
    `!n p a.
         (poly_divides (poly_exp [--a;&1] (SUC n)) p)
         ==> (poly_divides [--a;&1] (poly_diff_iter p n))`,
    let t0 = `!p a.  poly_divides (poly_exp [--a; &1] (SUC n)) p
                     ==> poly_divides [--a; &1] (poly_diff_iter p n)` in
    let l0 = ASSUME t0 in
    let l1 = SPEC `poly_diff p` l0 in
    let l2 = SPECL [`p:(real)list`;`SUC n`;`a:real`] POLY_DIVIDES_POLY_DIFF in
    let l3 = UNDISCH l2 in
    let l4 = MATCH_MP l1 l3 in
    INDUCT_TAC THENL
    [ (SIMP_TAC [poly_exp;POLY_MUL_RID;Pm_lemma1.PDI_DEF]);
      (REPEAT STRIP_TAC) THEN (ASM_MESON_TAC [l4;Pm_lemma1.PDI_DEF;PDI_POLY_DIFF_COMM])
    ]
)
let POLY_DIVIDES_PDI2 = PROVE(
     `!n m p a.
          m > n
          ==> (poly_divides (poly_exp [--a;&1] m) p)
          ==> (poly_divides [--a;&1] (poly_diff_iter p n))`,
     MESON_TAC [POLY_EXP_DIVIDES;POLY_DIVIDES_PDI;
                ARITH_RULE `m > n <=> (SUC n) <= m`]
)
let TAIL_GUNNER = PROVE(
    ` x < p ==> 1 <= v ==> v <= n ==>
      poly (poly_diff_iter
           (poly_exp [&0; &1] (p - 1) **
            poly_exp (poly_mul_iter (\i. [-- &i; &1]) n) p)
          x)
          (&v)
       = &0 `,
     MESON_TAC [POLY_DIVIDES_ROOT; ARITH_RULE `x < p <=> (p:num) > x`;
                POLY_DIVIDES_PDI2; POLY_DIVIDES_MUL3; POLY_DIVIDES_POLY_EXP2;
                POLY_DIVIDES_POLY_MUL_ITER]
)

let IS_INT_POLY = PROVE(
    `!p x.(integer x) ==> (ALL integer p) ==> integer (poly p x)`,
    LIST_INDUCT_TAC THEN
    (ASM_MESON_TAC [N_IS_INT;ALL;poly;INTEGER_ADD;INTEGER_MUL])
)
(*  surprising the MESON needs so much help with the rewrites here
 *  (i.e. i though i could just hit it with ASM_MESON_TAC with all four thms
 *)
let INV_POLY_CMUL = PROVE(
    `!y x . (~(x = &0)) ==> (x) ## (inv x) ## y = y`,
    LIST_INDUCT_TAC THENL
    [ ASM_MESON_TAC [poly_cmul];
      (REPEAT STRIP_TAC) THEN
      (REWRITE_TAC [poly_cmul;REAL_MUL_ASSOC]) THEN
      (ASM_MESON_TAC [REAL_MUL_RINV;REAL_MUL_LID])
    ]
)
let INV_POLY_CMUL2 = PROVE(
    `!y x . (~(x = &0)) ==> (inv x) ## (x) ## y = y`,
    MESON_TAC [INV_POLY_CMUL;REAL_INV_INV;REAL_INV_EQ_0]
)
(* the final ASM_MESON_TAC fails if poly_cmul is rolled into the thm list *)
let POLY_CMUL_EQUALS = PROVE(
    `!z x y. (~(z = &0)) ==> ((x = y) <=> (z ## x = z ## y))`,
    (REPEAT STRIP_TAC) THEN EQ_TAC THENL
    [ (SIMP_TAC[]);
      (SPEC_TAC (`x:(real)list`,`x:(real)list`)) THEN
      (SPEC_TAC (`y:(real)list`,`y:(real)list`)) THEN
      (LIST_INDUCT_TAC) THENL
      [ LIST_INDUCT_TAC THENL
        [ (SIMP_TAC [POLY_CMUL_CLAUSES]);
          (ASM_MESON_TAC [POLY_CMUL_CLAUSES;NOT_CONS_NIL])];
        LIST_INDUCT_TAC THENL [
          (ASM_MESON_TAC [POLY_CMUL_CLAUSES;NOT_CONS_NIL]);
          (ONCE_REWRITE_TAC [poly_cmul]) THEN
          (ASM_MESON_TAC [REAL_EQ_LCANCEL_IMP;CONS_11])]
      ]
    ]
)
let PDI_LENGTH_THM = PROVE(
    `!f n. LENGTH(poly_diff_iter f n) = (LENGTH f) - n`,
    STRIP_TAC THEN INDUCT_TAC THENL
    [ (SIMP_TAC [Pm_lemma1.PDI_DEF;ARITH_RULE `(x:num) - 0 = x`]);
      (ONCE_REWRITE_TAC [Pm_lemma1.PDI_DEF]) THEN
      (ONCE_REWRITE_TAC [LENGTH_POLY_DIFF]) THEN ASM_ARITH_TAC ]
)
let CAPTAINS_CLOTHES = PROVE(
    `! k q.
     (ALL integer q) ==>
     ? r .(ALL integer r) /\ r = (inv (&(FACT k))) ## (poly_diff_iter q k)`
    ,
    let e0 = `(inv (&(FACT k))) ## (poly_diff_iter q k)` in
    let l1 = ONCE_REWRITE_RULE [GSYM (SPEC `inv (&(FACT k))` POLY_CMUL_LENGTH)]
                               PDI_COEFF_FACT in
    let l2 = UNDISCH (SPEC_ALL l1) in
    let l3 = PROVE(`i < LENGTH( inv (&(FACT k)) ## poly_diff_iter q k)
                     ==> (i + k) < LENGTH q`,
                    MESON_TAC [PDI_LENGTH_THM;POLY_CMUL_LENGTH;
                               ARITH_RULE `(i:num) < f -k ==> (i+k) < f`]) in
    (REPEAT STRIP_TAC) THEN (EXISTS_TAC e0) THEN (SIMP_TAC []) THEN
    (ASM_SIMP_TAC [ONCE_REWRITE_RULE [GSYM POLY_CMUL_LENGTH] POLY_CMUL_EL]) THEN
    (ONCE_REWRITE_TAC [GSYM ALL_EL]) THEN (REPEAT STRIP_TAC) THEN
    (ASM_SIMP_TAC [ONCE_REWRITE_RULE [GSYM POLY_CMUL_LENGTH] POLY_CMUL_EL]) THEN
    (ONCE_REWRITE_TAC [l2]) THEN (ONCE_REWRITE_TAC [REAL_MUL_ASSOC]) THEN
    (MATCH_MP_TAC INTEGER_MUL) THEN STRIP_TAC THENL
    [ (MESON_TAC [IS_INT_FACT_DIV_FACT_DIV_FACT;REAL_MUL_SYM;real_div;REAL_MUL_ASSOC]);
      (ASM_MESON_TAC  [l3;ALL_IMP_EL]) ]
)
let MESSY_JESSE2 = PROVE(
  `n > 0 ==> p > n ==>
     (? (Bs:num->num->real). ! v .
         (1 <= v) ==> (v <= n) ==>
         (    (! i . (integer (Bs v i)))
           /\ (poly (SOD (g n p)) (&v)) =
                 ((real_of_num 1) / (&(FACT (p - 1)))) *
                   (psum (0,LENGTH (g n p))
                      (\i. (&(FACT i)) * (Bs v i)))
           /\ (! i. (i < p) ==> (Bs v i) = &0)  ))`,
    let root_canal = REAL_ARITH `(x:real) * (&0) = &0` in
    let bs = `\(v:num) . \(x:num).
               if (x <= (LENGTH (g n p)) ) then
                    (poly
                       ((inv (&(FACT x))) ##
                        (poly_diff_iter
                        (poly_exp [&0; &1] (p - 1) **
                         poly_exp (poly_mul_iter (\i. [-- &i; &1]) n) p)
                        x))
                       (&v))
               else (&0)` in
    let l0 = PROVE(`ALL integer [&0;&1]`,MESON_TAC [ALL;N_IS_INT]) in
    let t0 = `(poly_exp [&0; &1] (p - 1) **
              poly_exp (poly_mul_iter (\i. [-- &i; &1]) n) p)` in
    let l2 = SPECL [`i:num`;t0] CAPTAINS_CLOTHES in
    let l3 = PROVE(`ALL integer (poly_exp [&0; &1] (p - 1) ** poly_exp (poly_mul_iter (\i. [-- &i; &1]) n) p)`,MESON_TAC[l0;ALL_IS_INT_POLY_MUL;ALL_IS_INT_POLY_EXP;ALL_IS_INT_POLY_MUL_ITER]) in
    let l4 = MP l2 l3 in
    let l7 = ONCE_REWRITE_RULE [GSYM REAL_OF_NUM_EQ] FACT_NZ in
    let l8 = (SIMP_RULE [l7]) (SPEC `(&(FACT i)):real` POLY_CMUL_EQUALS) in
    (* these are not true for x =0, however we only use it for x= &(FACT i) *)
    let l10_0 = SPECL [`y:(real)list`;`(real_of_num (FACT i))`] INV_POLY_CMUL in
    let l12_0 = SPECL [`y:(real)list`;`(real_of_num (FACT i))`] INV_POLY_CMUL2 in
    let l10 = SIMP_RULE [REAL_FACT_NZ] l10_0 in
    let l12 = SIMP_RULE [REAL_FACT_NZ] l12_0 in
    let l9 = ONCE_REWRITE_RULE [l8] l4 in
    let l11 = GSYM (ONCE_REWRITE_RULE [l10] l9) in
    let l133 = PROVE(`
      (psum (0,m) (\i.(x i) * (if i <= m then (y i) else c))) =
      (psum (0,m) (\i.(x i) * (y i)))`,
      MESON_TAC [SUM_EQ;ARITH_RULE `(0 <= i /\ i < (m:num) + 0) ==> i <= m`]) in
    let l18 = MATCH_MP REAL_MUL_RINV (SPEC `i:num` l7) in
    let lass2 = SPECL [`g n p`;`x:real`;`v:real`] Pm_lemma2.PLANETMATH_LEMMA_2_B in
    let lass3 = BETA_RULE lass2 in
    let lass4 = CONV_RULE (RAND_CONV (RAND_CONV (REWRITE_CONV [Pm_eqn5.PLANETMATH_EQN_5]))) lass3 in
    let lass5 = REWRITE_RULE [POLY_CMUL;POLY_CMUL_PDI] lass4 in
    let lass6 = CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV [GSYM (ISPEC `f:num->real` ETA_AX)])) (SPEC_ALL SUM_CMUL) in
    let lass7 = ONCE_REWRITE_RULE [GSYM REAL_MUL_ASSOC] lass5 in
    let lass8 = REWRITE_RULE [lass6] lass7 in
    let lass10 = ONCE_REWRITE_RULE [REAL_MUL_DIV_ASSOC] lass8 in
    let lass11 =  ONCE_REWRITE_RULE [real_div] lass10 in
    let lass12 = REAL_ARITH `((w:real) * x * y) * z = w * x * y * z` in
    let lass13 = ONCE_REWRITE_RULE [lass12] lass11 in
    let lass14 = REWRITE_RULE [lass6] lass13 in
    let MUL_ONE = REAL_ARITH `! x.(&1) * x = x /\ x * (&1) = x` in
    let lass15 = SIMP_RULE [REAL_MUL_LINV;REAL_FACT_NZ;MUL_ONE] lass14 in
    STRIP_TAC THEN STRIP_TAC THEN (EXISTS_TAC bs) THEN (REPEAT STRIP_TAC) THENL
    [
      (BETA_TAC THEN BETA_TAC) THEN (ASM_CASES_TAC `(i <= LENGTH (g n p))`) THENL
      [ (ASM_SIMP_TAC[]) THEN (ASM_CASES_TAC `((i:num) < p)`) THENL
        [ (ASM_MESON_TAC [POLY_CMUL;TAIL_GUNNER;
                          N_IS_INT;REAL_ARITH `(x:real) * (&0) = &0`]);
          (ASSUME_TAC (UNDISCH (ARITH_RULE `~(i < (p:num)) ==> (p <= i)`))) THEN
          (CHOOSE_TAC l11) THEN
          (SPLIT_CONJOINED_ASSUMPT_TAC (snd (dest_exists (concl l11)))) THEN
          (ASM_REWRITE_TAC[l12]) THEN
          (ASM_MESON_TAC [N_IS_INT;IS_INT_POLY])
        ];
        (ASM_MESON_TAC [N_IS_INT])
      ];
      (BETA_TAC) THEN (SIMP_TAC [l133]) THEN
      (SIMP_TAC [POLY_CMUL;l18;REAL_MUL_ASSOC;REAL_MUL_LID]) THEN
      (SIMP_TAC [lass15;REAL_INV_1OVER]);
      BETA_TAC THEN (ASM_MESON_TAC [TAIL_GUNNER;POLY_CMUL;root_canal])
    ]
)
let INTEGER_PSUM = PROVE(
    `!f m.(! i . i < m ==> integer (f i)) ==> (integer (psum (0,m) f))`,
    let l0 = ASSUME `!i. i < SUC m ==> integer (f i)` in
    let l1 = SPEC `m:num` l0 in
    let l2 = SIMP_RULE [ARITH_RULE `m < SUC m`] l1 in
    STRIP_TAC THEN INDUCT_TAC THENL
    [ (MESON_TAC [sum;int_of_num;int_of_num_th;N_IS_INT]);
      (SIMP_TAC [sum;ARITH_RULE `0 + (x:num) = x`]) THEN
      (STRIP_TAC) THEN (MATCH_MP_TAC INTEGER_ADD) THEN
      (ASM_MESON_TAC[l2;ARITH_RULE `(i:num) < m ==> i < SUC m`])
    ]
)
let INT_DIVIDES_PSUM = PROVE(
    `!f m p.(! i . i < m ==>
             ((integer (f i)) /\ (int_divides p (int_of_real (f i)))))
                ==> (int_divides p (int_of_real (psum (0,m) f)))`,
    let l0 = ASSUME `!i. i < SUC m ==> integer (f i) /\ p divides int_of_real (f i)` in
    let l1 = SPEC `m:num` l0 in
    let l2 = SIMP_RULE [ARITH_RULE `m < SUC m`] l1 in
    let l3 = ASSUME `(!i. i < m ==> integer (f i)) ==> integer (psum (0,m) f)` in
    let l4 = SPEC `i:num` l0 in
    let l5 = DISCH `i < SUC m` ((CONJUNCT1 (UNDISCH l4))) in
    let l8 = PROVE(`(!i.i < SUC m
                         ==> (integer (f i))) ==> (!i.i < m ==> (integer (f i)))`,
                   MESON_TAC [ARITH_RULE `i < m ==> i < SUC m`]) in
    let ll1 = MP l8 (GEN_ALL l5) in
    let ll2 = MP l3 ll1 in
    let ll3 = MATCH_MP INT_OF_REAL_ADD (CONJ ll2 (CONJUNCT1 l2))  in
    STRIP_TAC THEN INDUCT_TAC THENL
    [ (MESON_TAC [sum;int_of_num;int_of_num_th;INT_DIVIDES_0]);
      (SIMP_TAC [sum;ARITH_RULE `0 + (x:num) = x`]) THEN
      (ASSUME_TAC (SPECL [`f:num->real`;`m:num`] INTEGER_PSUM)) THEN
      (STRIP_TAC) THEN
      (STRIP_TAC) THEN
      (ONCE_REWRITE_TAC [ll3]) THEN
      (MATCH_MP_TAC INT_DIVIDES_ADD) THEN
      (CONJ_TAC) THENL
      [ (ASM_MESON_TAC [ARITH_RULE `i < m ==> i < SUC m`]);
        (ASM_MESON_TAC [ARITH_RULE `m < SUC m`])
      ]
    ]
)
let PLANET_MATH_beta = PROVE(
    `p > n ==>
     n > 0 ==>
     (! v.
       (1 <= v /\ v <= n) ==>
       (   (integer (poly (SOD (g n p )) (&v)))
        /\ ((&p) divides (int_of_real (poly (SOD (g n p )) (&v))))
       )
     )`,
    let l2 = GSYM (ONCE_REWRITE_RULE [REAL_MUL_SYM] real_div) in
    let ll3 = ARITH_RULE `(int_of_num p) * &0 = &0` in
    let l7 = UNDISCH (SPECL [`i:num`;`p:num`] IS_INT_FACT_DIV) in
    let l11 = PROVE(`p > 0 ==> FACT p = p * (FACT (p-1))`,
                    MESON_TAC [FACT; ARITH_RULE `p > 0 ==> SUC (p -1) = p `]) in
    let l12 = UNDISCH (UNDISCH (ARITH_RULE `(p:num) > n ==> n > 0 ==> p > 0`)) in
    let l13 = MP l11 l12 in
    let t9 =
      `1 <= (v:num) ==>
       v <= (n:num) ==>
       (!v. 1 <= v
              ==> v <= n
              ==> (!i. integer (Bs v i)) /\
                  poly (SOD (g n p)) (&v) =
                  &1 / &(FACT (p - 1)) *
                  psum (0,LENGTH (g n p)) (\i. &(FACT i) * Bs v i) /\
                  (!i. i < p ==> Bs v i = &0)) ==>
        (integer (Bs v i))` in
    let lll0 = UNDISCH (UNDISCH (UNDISCH (PROVE(t9,MESON_TAC[])))) in
    let l8 = REWRITE_RULE [l13;real_div;REAL_INV_MUL] l7 in
    let l9 = REWRITE_RULE [N_IS_INT;GSYM REAL_OF_NUM_MUL] l8 in
    let l10 = REWRITE_RULE [REAL_INV_MUL] l9 in
    let l11 = MATCH_MP (INTEGER_MUL) (CONJ l10 lll0) in
    let l12 = MATCH_MP INT_OF_REAL_MUL (CONJ (SPEC `p:num` N_IS_INT) l11) in
    let l15 = GSYM l12 in
    let lll8 = ARITH_RULE `p > n ==> n > 0 ==> ~(p = 0)` in
    let lll9 = ONCE_REWRITE_RULE [GSYM REAL_OF_NUM_EQ] lll8 in
    let lll10 = UNDISCH (UNDISCH lll9) in

    let sc1 = PROVE (`(~((x:real) = &0)) ==> (x * y * inv x) = y`,
                      MESON_TAC [REAL_MUL_RID;REAL_MUL_ASSOC;
                                 REAL_MUL_SYM;REAL_MUL_LINV;REAL_MUL_LID]) in
    let sc2 = PROVE (`(~((x:real) = &0)) ==> (x * y * (inv x) * z) = y * z`,
                      MESON_TAC [sc1;REAL_MUL_ASSOC]) in
    (REPEAT STRIP_TAC) THENL
      [ (CHOOSE_TAC (UNDISCH (UNDISCH MESSY_JESSE2))) THEN
        (ASM_SIMP_TAC []) THEN
        (ONCE_REWRITE_TAC [GSYM SUM_CMUL]) THEN
        (MATCH_MP_TAC INTEGER_PSUM) THEN
        (REPEAT STRIP_TAC) THEN
        BETA_TAC THEN
        (ASM_CASES_TAC `i < (p:num)`) THENL
        [ (ASM_SIMP_TAC [N_IS_INT;REAL_ARITH `(x:real) * (&0) = &0`]);
          (ASSUME_TAC (UNDISCH (ARITH_RULE `(~((i:num) < p)) ==> i >= p-1`))) THEN
          (ASM_MESON_TAC [REAL_INV_1OVER;REAL_MUL_ASSOC;
                          IS_INT_FACT_DIV; l2;INTEGER_MUL])
        ];
        (CHOOSE_TAC (UNDISCH (UNDISCH MESSY_JESSE2))) THEN
        (ASM_SIMP_TAC []) THEN
        (ONCE_REWRITE_TAC [GSYM SUM_CMUL]) THEN
        (MATCH_MP_TAC INT_DIVIDES_PSUM) THEN
        (REPEAT STRIP_TAC) THENL
        [ BETA_TAC THEN
          (ASM_CASES_TAC `i < (p:num)`) THENL
          [ (ASM_SIMP_TAC [N_IS_INT;REAL_ARITH `(x:real) * (&0) = &0`]);
            (ASSUME_TAC (UNDISCH (ARITH_RULE `(~((i:num) < p)) ==> i >= p-1`))) THEN
            (ASM_MESON_TAC [REAL_INV_1OVER;REAL_MUL_ASSOC;
                            IS_INT_FACT_DIV; l2;INTEGER_MUL])
          ];
          (ONCE_REWRITE_TAC [int_divides]) THEN BETA_TAC THEN
          (ASM_CASES_TAC `i < (p:num)`) THENL
          [ (ASM_SIMP_TAC [N_IS_INT;REAL_ARITH `(x:real) * (&0) = &0`]) THEN
            (EXISTS_TAC `int_of_num 0`) THEN
            (MESON_TAC [ll3;int_of_num_th;int_of_num]);
            (ASSUME_TAC (UNDISCH (ARITH_RULE `(~((i:num) < p)) ==> i >= p`))) THEN
            (EXISTS_TAC `int_of_real (((&(FACT i))/(&(FACT p))) * (Bs (v:num) i))`) THEN
            (ONCE_REWRITE_TAC [int_of_num]) THEN
            (ONCE_REWRITE_TAC [l13]) THEN
            (ONCE_REWRITE_TAC [N_IS_INT;GSYM REAL_OF_NUM_MUL]) THEN
            (SIMP_TAC [ real_div]) THEN
            (ONCE_REWRITE_TAC [ REAL_INV_MUL]) THEN
            (ONCE_REWRITE_TAC [ REAL_MUL_LID]) THEN
            (ONCE_REWRITE_TAC [l15]) THEN
            (ASSUME_TAC lll10) THEN
            (ONCE_REWRITE_TAC [REAL_MUL_ASSOC]) THEN
            (ASM_MESON_TAC [sc2;REAL_MUL_SYM])
          ]
        ]
      ]
)

let JUNE_LEMMA = PROVE(
    `n > 0 ==> p > n ==> v <= n ==> integer (poly (SOD (g n p)) (&v))`,
    let lem0 = CONJUNCT1 (UNDISCH_ALL PLANET_MATH_alpha) in
    let lem1 = UNDISCH_ALL (SPEC_ALL (UNDISCH_ALL PLANET_MATH_beta)) in
    let lem2 = DISCH `1 <= v /\ v <= n` (CONJUNCT1 lem1) in
    let lem3 = SPEC `SUC v` (GEN `v:num` lem2) in
    let lem4 = SIMP_RULE [ARITH_RULE `1 <= SUC v`] lem3 in
    (STRIP_TAC THEN STRIP_TAC) THEN
    (SPEC_TAC (`v:num`,`v:num`)) THEN
    (INDUCT_TAC THENL [(SIMP_TAC [lem0]);(ACCEPT_TAC lem4)])
)
let DIVIDES_SUM_NOT_ZERO = PROVE(
    `!(x:int) (y:int) (z:int).
         (~(z divides x)) /\  (z divides y) ==> ~(x + y = &0)`,
    let l0 = ASSUME `(x:int) + y = &0` in
    let l1 = ONCE_REWRITE_RULE [ARITH_RULE `((x:int) + y = &0) <=> (x = --y)`] l0 in
    (REPEAT STRIP_TAC) THEN (UNDISCH_TAC `~((z:int) divides x)`) THEN
    (REWRITE_TAC [l1]) THEN (UNDISCH_TAC `((z:int) divides y)`) THEN
    (INTEGER_TAC)
)
let NUM_OF_INT_ABS = PROVE(
    `!(x:num) (y:int).num_of_int (abs y)  = x <=> abs y = &x`,
(* stupid... *)
    let j0 = UNDISCH (PROVE(`(num_of_int (abs y) = x) ==> x = num_of_int (abs y)`,MESON_TAC [])) in
    let j1 = ARITH_RULE `&0 <= ((abs y):int)` in
    let j2 = MATCH_MP INT_OF_NUM_OF_INT j1 in
    (REPEAT STRIP_TAC) THEN EQ_TAC THENL
    [ (STRIP_TAC THEN SIMP_TAC [j0;j2]);
      (ASM_SIMP_TAC [NUM_OF_INT_OF_NUM])]
)
let INT_DIVIDES_IMP_ABS_NUM_DIVIDES = PROVE(
    `! (x:int) (y:num).
       (x divides (&y)) ==> ((num_of_int (abs x)) divides y)`,
    let w0 = ARITH_RULE `((&0):int) <= abs x` in
    let w1 = fst (EQ_IMP_RULE (SPEC `abs (x:int)` NUM_OF_INT)) in
    let w2 = MP w1 w0 in
    let w3 = ARITH_RULE `((&0):int) <= x ==> abs x = x` in
    let w4 = ARITH_RULE `(~(((&0):int) <= x)) ==> abs x = -- x` in
    (REWRITE_TAC [int_divides;num_divides]) THEN
    (REPEAT STRIP_TAC) THEN (ASM_REWRITE_TAC [w2]) THEN
    (ASM_CASES_TAC `((&0):int) <= x`) THENL
    [ (ONCE_REWRITE_TAC [UNDISCH w3]) THEN
      (EXISTS_TAC `x':int`) THEN (REFL_TAC);
      (ONCE_REWRITE_TAC [UNDISCH w4]) THEN
      (EXISTS_TAC `--x':int`) THEN (ARITH_TAC)
    ]
)
let INT_PRIME_NUM_PRIME = PROVE(
    `!p. int_prime (&p) <=> prime p`,
    (ONCE_REWRITE_TAC [int_prime;prime]) THEN
    (MESON_TAC [divides;num_divides;
                INT_ABS;INT_POS;INT_OF_NUM_EQ;INT_LT_IMP_NE;INT_GT;
                ARITH_RULE `2 <= p ==> abs((&p):int) > &1`;
                INT_DIVIDES_IMP_ABS_NUM_DIVIDES;NUM_OF_INT_ABS;PRIME_GE_2;
                prime;int_prime ])
)

let DIVIDES_INT_OF_REAL_ADD = PROVE(
         `!x y p.integer x /\
                 integer y /\
                 p divides (int_of_real x) /\
                 p divides (int_of_real y)
                 ==> p divides (int_of_real (x + y))`,
         SIMP_TAC [INT_OF_REAL_ADD;INT_DIVIDES_ADD]
)
let ITCHY_LEMMA = PROVE(
    `! f p n.
       (!v.1<= v /\ v <=  n ==>
        integer (f v) /\
        &p divides int_of_real (f v)) ==>
        (&p divides int_of_real (sum (1..n) f))`,
    let l0 = fst (EQ_IMP_RULE (SPECL [`1`;`0`] (GSYM NUMSEG_EMPTY))) in
    let l1 = INTEGER_RULE `&p divides ((&0))` in
    let l2 = SPEC `0` (GEN_ALL int_of_num) in
    let l3 = ONCE_REWRITE_RULE [l2] l1 in
    let l4 = SPECL [`f:num->real`;`n:num`;`1`] IS_INT_SUM in
    let l5 = PROVE(`(!v. 1 <= v /\ v <= SUC n ==> integer (f v)) ==> (!i. 1 <= i /\ i <= n ==> integer (f i))`,MESON_TAC [ARITH_RULE `v <= n ==> v <= SUC n`]) in
    let l6 = IMP_TRANS l5 l4 in
    let l7 = PROVE(`(!v. 1 <= v /\ v <= SUC n ==> (integer (f v)) /\  (&p) divides int_of_real (f v)) ==> (&p) divides int_of_real (f (SUC n))`,MESON_TAC [ARITH_RULE `1 <= (SUC n) /\ SUC n <= SUC n`]) in
    let l9 = PROVE(`(!v. 1 <= v /\ v <= SUC n ==> integer (f v)) ==> integer (f (SUC n))`,MESON_TAC [ARITH_RULE `1 <= SUC n /\ SUC n <= SUC n`]) in
    let tm = `\(v:num).integer (f v) /\ (&p) divides int_of_real (f v)` in
    let l10 = BETA_RULE (SPEC tm SHRIVER) in
    let l11 = UNDISCH (SPEC `1` (GEN `m:num` l10)) in
     STRIP_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
     [ SIMP_TAC  [ARITH_RULE `0 < 1`;l0;SUM_CLAUSES;l3];
       DISCH_TAC THEN
       (SIMP_TAC [SUM_CLAUSES_NUMSEG;ARITH_RULE `1 <= SUC n`]) THEN
       (MATCH_MP_TAC DIVIDES_INT_OF_REAL_ADD) THEN (CONJ_TAC) THENL
       [ ASM_SIMP_TAC [l6];
         CONJ_TAC THENL
         [ ASM_SIMP_TAC [l9];
           CONJ_TAC THENL
           [ ASM_SIMP_TAC [l11];
             ASM_SIMP_TAC [l7] ]]]]
)
let GOTTA_DO_DISHES_LEMMA = PROVE(
    `!(x:real) (y:real).
       (integer x) /\ (integer y) ==>
       (?(z:int).(~(z divides (int_of_real x)))
           /\ (z divides (int_of_real y)))
       ==> ~(x + y = &0)`,
    let mk_lemma x y =
        let lem0 = SPECL [x;y;`z:int`] DIVIDES_SUM_NOT_ZERO in
        let lem1 = TAUT `(X /\ Y ==> Z) <=> (X ==> Y ==> Z)` in
        UNDISCH (UNDISCH (ONCE_REWRITE_RULE [lem1] lem0))
    in
    let mk_tac x y =
        (ASM_REWRITE_TAC [GSYM int_of_num;INT_OF_REAL_NEG_INT_OF_NUM]) THEN
        (STRIP_TAC) THEN
        (REWRITE_TAC [GSYM int_neg_th;GSYM int_eq; GSYM int_add_th;GSYM int_of_num_th]) THEN
        (ACCEPT_TAC (mk_lemma  x y))
    in
    (ONCE_REWRITE_TAC [is_int]) THEN
    (STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC ) THENL
    [ mk_tac `(&n):int` `(&n'):int` ;
      mk_tac `(&n):int` `--(&n'):int` ;
      mk_tac `--(&n):int` `(&n'):int` ;
      mk_tac `--(&n):int` `--(&n'):int`
     ]
)

let RAINY_DAY = PROVE(
    `! p x y.
       prime p ==>
       (&p) > x ==>
       integer x ==>
       x > (&0) ==>
       integer y ==>
       (((&p) divides (int_of_real (x * y)))
        <=> ((&p) divides int_of_real y))`,
    let ss3 = SPECL [`int_of_num n`;`(&p):int`] INT_PRIME_COPRIME_LT in
    let ss4 = ONCE_REWRITE_RULE [ARITH_RULE `abs ((&x):int) = &x`] ss3 in
    let ss40 = PROVE(`!(x:num) (y:num).  (int_of_num x) < (int_of_num y) <=> (real_of_num x) < (real_of_num y)`,SIMP_TAC [INT_OF_NUM_LT;REAL_OF_NUM_LT]) in
    let ss5 = ONCE_REWRITE_RULE [ss40;INT_COPRIME_SYM;INT_PRIME_NUM_PRIME] ss4 in
    let ss6 = SPECL [`(&p):int`;`(&n):int`;`int_of_real y`] INT_COPRIME_DIVPROD in
    let ss7 = ONCE_REWRITE_RULE [TAUT `(X /\ Y ==> Z) <=> (Y ==> X ==> Z)`] ss6 in
    let ss8 = IMP_TRANS ss5 ss7 in
    let ss9 = ONCE_REWRITE_RULE [TAUT `(A /\ B /\ C ==> D ==> E) <=> (A ==> B ==> C ==> D ==> E)`] ss8 in
    let ss10 = UNDISCH ss9 in
    (REPEAT STRIP_TAC) THEN (ASM_SIMP_TAC [INT_OF_REAL_MUL]) THEN
    (EQ_TAC) THENL
    [ (SIMP_TAC [INT_DIVIDES_LMUL]) THEN
      (UNDISCH_TAC `integer x`) THEN
      (ONCE_REWRITE_TAC [is_int]) THEN
      (STRIP_TAC) THENL
      [ (ASM_REWRITE_TAC[]) THEN
        (ONCE_REWRITE_TAC [GSYM int_of_num]) THEN
        (UNDISCH_TAC `(&(p:num)) > (x:real)`) THEN
        (UNDISCH_TAC `(x:real) > &0`) THEN
        (ASM_REWRITE_TAC []) THEN
        (ONCE_REWRITE_TAC [REAL_ARITH `(y:real) > z <=> z < y`]) THEN
        (ACCEPT_TAC ss10);
        (ASM_ARITH_TAC)
      ];
      (SIMP_TAC [INT_DIVIDES_LMUL])
    ]
)
let PLANET_MATH_gamma = PROVE(
    `n > 0 ==>
     p > n ==>
     prime p ==>
     &p > (EL 0 c) ==>
     (EL 0 c) > (&0) ==>
     n = PRE (LENGTH (c)) ==>
     (ALL integer c) ==>
     ( (integer (LHS c (g n p))) /\ ~((LHS c (g n p)) = &0))`,
     let lemma01 = SPECL [`\i. EL i c * poly (SOD (g n p)) (&i)`;`n:num`;`k:num` ] IS_INT_SUM in
     let lemma02 = BETA_RULE lemma01 in
     let lemma021 = UNDISCH JUNE_LEMMA in
     let lemma022 = UNDISCH_ALL (ARITH_RULE `n > 0 ==> p > n ==> p > 1`) in
     let lemma023 = DISCH_ALL (SIMP_RULE [lemma022] lemma021) in
     let lemma04 = UNDISCH (UNDISCH lemma023) in
     let lemma08 = ISPECL [`c:(real)list`;`v:num`;`integer`] ALL_IMP_EL in
     let lemma09 = ADD_ASSUM `n > 0` (UNDISCH lemma08) in
     let lemma10 = ADD_ASSUM `n = PRE (LENGTH (c:(real)list))` lemma09 in
     let lemma11 = ARITH_RULE `n > 0 ==> (n = PRE (LENGTH (c:(real)list))) ==> ((v < LENGTH c) <=> (v <= n))` in
     let lemma12 = UNDISCH (UNDISCH lemma11) in
     let lemma13 = ONCE_REWRITE_RULE [lemma12] lemma10 in
     let lemma15 = CONJ (UNDISCH (UNDISCH lemma04)) (UNDISCH lemma13) in
     let lemma16 = MATCH_MP INTEGER_MUL (ONCE_REWRITE_RULE [CONJ_SYM] lemma15) in
     let lemma17 = DISCH `v <= (n:num)` lemma16 in
     let lemma18 = ADD_ASSUM_DISCH `k <= (v:num)` lemma17 in
     let lemma19 = ONCE_REWRITE_RULE [TAUT `(X ==> Y ==> Z) <=> ((X /\ Y) ==> Z)`] lemma18 in
     let lemma20 = GEN `v:num` lemma19 in
     let lemma21 = GEN `k:num` (MATCH_MP lemma02 lemma20) in
     let lemma29 = SPEC `0` lemma21 in
     let lemma30 = GSYM (ASSUME `n = PRE (LENGTH (c:(real)list))`) in
     let lemma300 = SPECL [`f:(num -> real)`;`0`;`PRE (LENGTH (c:(real)list))`] SUM_CLAUSES_LEFT in
     let lemma31 = ADD_ASSUM `n > 0` (ADD_ASSUM `n = PRE (LENGTH (c:(real)list))` lemma300) in
     let lemma32 = MP lemma31 (ARITH_RULE `0 <= PRE (LENGTH (c:(real)list))`) in
     let lemma0000 = BRW `(X ==> Y ==> Z) <=> ((X /\ Y) ==> Z)` GOTTA_DO_DISHES_LEMMA in
     let lemmaa00 = UNDISCH PLANET_MATH_alpha in
     let lemmaa03 = ARITH_RULE `n >0 ==> ((n = PRE (LENGTH (c:(real)list))) ==> 0 < (LENGTH c))` in
     let lemmaa04 = ISPECL [`c:(real)list`;`0`;`integer`] ALL_IMP_EL in
     let lemmaa05 = MP (UNDISCH lemmaa04) (UNDISCH (UNDISCH lemmaa03))  in
     let c1 = ARITH_RULE `n > 0 ==> n = PRE (LENGTH (c:(real)list)) ==> 0 < (LENGTH (c:(real)list))` in
     let c2 = UNDISCH (UNDISCH c1) in
     let c3 = MP (UNDISCH lemmaa04) c2 in
     let c4 = CONJUNCT1 (UNDISCH (UNDISCH (UNDISCH PLANET_MATH_alpha))) in
     let c40 = CONJUNCT2 (UNDISCH (UNDISCH (UNDISCH PLANET_MATH_alpha))) in
     let c5 = SPECL [`p:num`;`(EL 0 c):real`;`poly (SOD (g n p)) (&0)`] RAINY_DAY in
     let c7 = ((UNDISCH (UNDISCH c5))) in
     let c8 = SIMP_RULE [c3] c7 in
     let c9 = UNDISCH c8 in
     let c10 = SIMP_RULE [c4] c9 in
     let d0 = UNDISCH PLANET_MATH_beta in
     let d1 = BRW `(X ==> Y ==> Z) <=> (Y ==> X ==> Z)` d0 in
     let d2 = SIMP_RULE [UNDISCH (ARITH_RULE `p > (n:num) ==> n > 0 ==> p > 1`)] d1 in
     let d3 = UNDISCH d2 in
     let d8 = CONJUNCT2 (UNDISCH (SPEC_ALL d3)) in
     let d9 = SPECL [`(&p):int`;`int_of_real (EL v c)`;`int_of_real (poly (SOD (g n p)) (&v))`] INT_DIVIDES_LMUL in
     let d10 = ADD_ASSUM `ALL integer c` d9 in
     let d11 = ADD_ASSUM `n = PRE (LENGTH (c:(real)list))` d10 in
     let d12 = ADD_ASSUM `1 <= v /\ v <= n` d11 in
     let d13 = CONJUNCT1 (UNDISCH (SPEC_ALL d3)) in
     let d14 = DISCH `1 <= v` (ADD_ASSUM `1 <= v` lemma13) in
     let d15 = BRW `(X ==> Y ==> Z) <=> (X /\ Y ==> Z)` d14 in
     let d16 = UNDISCH d15 in
     let d17 = CONJ d16 d13 in
     let d18 = GSYM (MATCH_MP INT_OF_REAL_MUL d17) in
     let d19 = ONCE_REWRITE_RULE [d18] d12 in
     let d20 = MP d19 d8 in
     let d21 = UNDISCH (SPECL [`1`;`v:num`] (GEN `k:num` lemma20)) in
     let d22 = CONJ d21 d20 in
     let d23 = DISCH `1 <=v /\ v <= n` d22 in
     let d24 = GEN `v:num` d23 in
     let d25 = MATCH_MP ITCHY_LEMMA d24 in
     ((REPEAT STRIP_TAC) THENL
      [ (ONCE_REWRITE_TAC [Pm_eqn4.LHS]) THEN (SIMP_TAC [lemma30;lemma29]);
        (UNDISCH_TAC `LHS c (g n p) = &0`) THEN
        (REWRITE_TAC [Pm_eqn4.LHS]) THEN
        (SIMP_TAC [lemma32;ARITH_RULE `0 + 1 = 1`]) THEN
        (ONCE_REWRITE_TAC [lemma30]) THEN
        (MATCH_MP_TAC lemma0000) THEN
        (CONJ_TAC) THENL
        [ (CONJ_TAC) THENL
          [ (MATCH_MP_TAC INTEGER_MUL) THEN (ASM_SIMP_TAC [lemmaa00;lemmaa05]);
            (ACCEPT_TAC (SPEC `1` lemma21))
          ];
          (EXISTS_TAC `(&p):int`) THEN (CONJ_TAC) THENL
          [(ONCE_REWRITE_TAC [c10]) THEN (ASM_SIMP_TAC [c40]);
           (ACCEPT_TAC d25)
          ]
        ]
      ] )
)
end;;
```

### Informal statement
This theorem states that for any natural number $n$, the real number $\&n$ (real_of_num $n$) is an integer.

Formally: 
$$\forall n \in \mathbb{N}. \text{integer}(\&n)$$

### Informal proof
The proof follows directly from the definition of an integer as implemented in HOL Light. The `is_int` predicate defines what it means to be an integer, and applying this to a natural number converted to a real number satisfies the integer condition. The proof is completed using MESON_TAC with the `is_int` definition.

### Mathematical insight
This theorem establishes a fundamental relationship between natural numbers and integers in the HOL Light type system. While HOL Light represents reals as a separate type from integers and naturals, this theorem confirms that real values obtained by converting natural numbers (via `&n` or `real_of_num n`) are integers according to the `integer` predicate.

The theorem is used extensively in proving properties about arithmetic operations involving real numbers that are actually integers. It serves as a bridge between the natural numbers and the reals, allowing for the application of integer properties to real number expressions that represent integers.

### Dependencies
- `is_int`: Definition of what it means for a real number to be an integer

### Porting notes
When porting this to other systems, note that:
- Different proof assistants have different type structures for numbers
- In systems with a distinct integer type (like Lean), this relationship might be established through coercions or explicit conversion functions
- The equivalent theorem would state that applying the natural-to-real conversion preserves the "integerness" property

In Lean, a similar statement might look like: `∀ n : ℕ, ∃ m : ℤ, ↑n = ↑m` with appropriate coercions.

Most formal systems need to establish this or similar relationships between their numeric types to enable smooth reasoning about arithmetic.

### Name of formal statement
N_IS_INT

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let N_IS_INT = PROVE(
    `!n . integer (&n)`,
    MESON_TAC [is_int]
)
let NEG_N_IS_INT = PROVE(
    `!n . integer (--(&n))`,
    MESON_TAC [is_int]
)
let INT_OF_REAL_ADD = PROVE(
    `!x y.(integer x) /\ (integer y)
           ==> (int_of_real (x + y)) =
               (int_of_real x) + (int_of_real y)`,
    SIMP_TAC[integer;int_add;int_rep;N_IS_INT;NEG_N_IS_INT]
)
let INT_OF_REAL_MUL = PROVE(
    `!x y.(integer x) /\ (integer y)
           ==> (int_of_real (x * y)) =
               (int_of_real x) * (int_of_real y)`,
    SIMP_TAC[is_int;int_mul;int_rep;N_IS_INT;NEG_N_IS_INT]
)

let rec INT_OF_REAL_CONV_helper t =
    let real_op_2_int_op t =
        if (t = `real_add`) then `int_add`
        else if (t = `real_sub`) then `int_sub`
        else if (t = `real_mul`) then `int_mul`
        else if (t = `real_pow`) then `int_pow`
        else if (t = `real_neg`) then `int_neg`
        else t
    in
    if (is_var t) then (mk_comb (`int_of_real`,t),[],[t])
    else if ((rator t) = `real_of_num`) then
      (mk_comb (`int_of_real`, t),[t],[])
    else if ((rator t) = `real_neg`) then
      let rand1 = rand t in
      let (expr1,lst1,lst2) = INT_OF_REAL_CONV_helper rand1 in
      let lst = lst1 @ [t] in
      let expr = mk_comb (`int_neg`, expr1) in
      (expr,lst,lst2)
    else if ((rator (rator t)) = `real_pow`) then
      let rand1 = rand (rator t) in
      let exponent = rand t in
      let (expr1,lst1,lst2) = INT_OF_REAL_CONV_helper rand1 in
      let lst = lst1 @ [t] in
      let expr = mk_comb (mk_comb (`int_pow`,expr1),exponent) in
      (expr,lst,lst2)
    else if (   ((rator (rator t)) = `real_add`)
             || ((rator (rator t)) = `real_mul`)
             || ((rator (rator t)) = `real_sub`)  ) then
      let int_op = real_op_2_int_op (rator (rator t)) in
      let rand1 = rand (rator t) in
      let rand2 = rand t in
      let (expr1,lst11,lst12) = INT_OF_REAL_CONV_helper rand1 in
      let (expr2,lst21,lst22) = INT_OF_REAL_CONV_helper rand2 in
      let lst1 = lst11 @ lst21 @ [t] in
      let lst2 = lst12 @ lst22 in
      let expr = mk_comb (mk_comb (int_op,expr1),expr2) in
      (expr,lst1,lst2)
    else (t,[],[t])


(* ------------------------------------------------------------------------- *)
(* I wrote an initial version of this, but John Harrison proposed this       *)
(* version which is faster and also requires less theorems.                  *)
(* ------------------------------------------------------------------------- *)
let INT_OF_REAL_CONV =
  let final_tweak = MATCH_MP(MESON[int_tybij] `real_of_int x = y ==> int_of_real y = x`) in
  fun t ->
    let (exp,real_sub_terms,is_int_assumpts) = INT_OF_REAL_CONV_helper t in
    let is_int_assumpts = List.map (fun x -> mk_comb (`integer`,x)) is_int_assumpts in
    let fexp = rand(concl(PURE_REWRITE_CONV[GSYM int_of_num] exp)) in
    let rexp = mk_comb(`real_of_int`,fexp)
    and ths = map (GEN_REWRITE_RULE I [CONJUNCT2 int_tybij] o ASSUME) is_int_assumpts in
    let th3 = PURE_REWRITE_CONV(ths @ [int_pow_th; int_add_th; int_mul_th; int_sub_th; int_neg_th; int_of_num_th]) rexp in
    itlist DISCH is_int_assumpts (final_tweak th3)

let ALL_IS_INT = PROVE(
    `! h t . (ALL integer (CONS h t)) ==> (integer h)  /\ (ALL integer t)`,
    SIMP_TAC [ALL]
)

let ALL_IS_INT_POLY_ADD = PROVE(
    `! p1 p2 . (ALL integer p1) /\ (ALL integer p2) ==> (ALL integer (p1 ++ p2))`,
    let lem01 = UNDISCH (SPECL [`h:real`;`t:(real)list`] ALL_IS_INT) in
    let [lem02;lem03] = CONJUNCTS lem01 in
    let lem04 = UNDISCH (SPECL [`h':real`;`t':(real)list`] ALL_IS_INT) in
    let [lem05;lem06] = CONJUNCTS lem04 in
    let lem07 = CONJ lem02 lem05 in
    let lem08 = MATCH_MP INTEGER_ADD lem07 in
    let lem09 = ASSUME `! p2. ALL integer t /\ ALL integer p2 ==> ALL integer (t ++ p2)` in
    let lem10 = SPEC `t':(real)list` lem09 in
    let lem11 = CONJ lem03 lem06 in
    let lem12 = MP lem10 lem11 in
    LIST_INDUCT_TAC THENL
    [ (SIMP_TAC [poly_add]);
      LIST_INDUCT_TAC THENL
      [ (SIMP_TAC [poly_add]);
        (SIMP_TAC [poly_add]) THEN (ONCE_REWRITE_TAC [NOT_CONS_NIL]) THEN
        (SIMP_TAC []) THEN (SIMP_TAC [HD;TL]) THEN (STRIP_TAC) THEN
        (SIMP_TAC [ALL]) THEN
        (CONJ_TAC) THENL [(ACCEPT_TAC lem08); (ACCEPT_TAC lem12)]
      ]
    ]
)
let ALL_IS_INT_POLY_CMUL = PROVE(
    `! p c. (integer c) /\ (ALL integer p) ==> (ALL integer (c ## p))`,
    (LIST_INDUCT_TAC) THEN (ASM_SIMP_TAC [poly_cmul;ALL;INTEGER_MUL])
)

let ALL_IS_INT_POLY_MUL = PROVE(
    `! p1 p2 . (ALL integer p1) /\ (ALL integer p2) ==> (ALL integer (p1 ** p2))`,
    let lem01 = UNDISCH (SPECL [`h:real`;`t:(real)list`] ALL_IS_INT) in
    let lem02 = UNDISCH (SPECL [`h':real`;`t':(real)list`] ALL_IS_INT) in
    let [lem03;lem04] = CONJUNCTS lem01 in
    let [lem05;lem06] = CONJUNCTS lem02 in
    let lem07 = MATCH_MP INTEGER_MUL (CONJ lem03 lem05) in
    let lem08 = MATCH_MP ALL_IS_INT_POLY_CMUL (CONJ lem03 lem06) in
    let lem09 = ASSUME `! p2. ALL integer t /\ ALL integer p2 ==> ALL integer (t ** p2)` in
    let lem10 = SPEC `(CONS h' t'):(real)list` lem09 in
    LIST_INDUCT_TAC THENL
    [ (LIST_INDUCT_TAC THENL [(SIMP_TAC [ALL;poly_mul]);(SIMP_TAC [poly_mul])]);
      LIST_INDUCT_TAC THENL
      [ (SIMP_TAC [poly_mul]) THEN
        ((ASM_CASES_TAC `(t:(real)list) = []`) THENL
        [ (ASM_SIMP_TAC [ALL;poly_cmul]) THEN (SIMP_TAC [poly_cmul]);
          (ASM_SIMP_TAC [ALL;poly_cmul;poly_add]) THEN (SIMP_TAC [SPEC `0` N_IS_INT])
        ]);
        (STRIP_TAC) THEN (ONCE_REWRITE_TAC [poly_mul] ) THEN
        (ASM_CASES_TAC `(t:(real)list) = []`) THENL
        [ (ASM_SIMP_TAC [ALL;poly_cmul]) THEN STRIP_TAC THENL
          [(ACCEPT_TAC lem07) ;(ACCEPT_TAC lem08)];
          (ASM_SIMP_TAC []) THEN (MATCH_MP_TAC ALL_IS_INT_POLY_ADD) THEN
          (CONJ_TAC) THENL
          [ (MATCH_MP_TAC ALL_IS_INT_POLY_CMUL) THEN (CONJ_TAC) THENL
            [(ACCEPT_TAC lem03) ; (ASM_SIMP_TAC[])];
            (SIMP_TAC [ALL]) THEN (CONJ_TAC) THENL
            [(ACCEPT_TAC (SPEC `0` N_IS_INT)); (ASM_SIMP_TAC [lem04;lem10])]
          ]
        ]
      ]
    ]
)
let NOT_POLY_MUL_ITER_NIL = PROVE(
    `! n . ~((poly_mul_iter (\i.[ -- &i; &1]) n) = [])`,
    let lem02 = SIMP_RULE [NOT_CONS_NIL] (ISPEC `[ -- &(SUC n); &1]` NOT_POLY_MUL_NIL ) in
    let lem03 = ISPEC `(poly_mul_iter (\i.[ -- &i; &1]) n)` lem02 in
    let lem04 = UNDISCH  lem03 in
    INDUCT_TAC THENL
    [ (SIMP_TAC [Pm_eqn5.POLY_MUL_ITER;NOT_CONS_NIL]);
      (SIMP_TAC [Pm_eqn5.POLY_MUL_ITER;lem04])
    ]
)

let ALL_IS_INT_POLY_MUL_ITER = PROVE(
    `! n. (ALL integer (poly_mul_iter (\i.[-- &i; &1]) n))`,
    let FOOBAR_LEMMA =  PROVE(
        `ALL integer [-- &(SUC n); &1]`,
        (SIMP_TAC [ALL]) THEN (SIMP_TAC [N_IS_INT;NEG_N_IS_INT])) in
    INDUCT_TAC THENL
    [ (ONCE_REWRITE_TAC [Pm_eqn5.POLY_MUL_ITER]) THEN
      (ONCE_REWRITE_TAC [ALL]) THEN (SIMP_TAC [ALL;N_IS_INT]);
      (ONCE_REWRITE_TAC [Pm_eqn5.POLY_MUL_ITER]) THEN (BETA_TAC) THEN
      (MATCH_MP_TAC ALL_IS_INT_POLY_MUL) THEN (CONJ_TAC) THENL
      [(ACCEPT_TAC (FOOBAR_LEMMA)); (ASM_SIMP_TAC [])]
    ]
)

let ALL_IS_INT_POLY_EXP = PROVE(
    `!n p. (ALL integer p) ==> (ALL integer (poly_exp p n))`,
    let lem01 = ASSUME `! p. ALL integer p ==> ALL integer (poly_exp p n)` in
    let lem02 = ASSUME ` ALL integer p` in
    let lem03 = MP (SPEC_ALL lem01) lem02 in
    let lem04 = CONJ lem02 lem03 in
    let lem05 = MATCH_MP ALL_IS_INT_POLY_MUL lem04 in
    INDUCT_TAC THENL
    [ (ONCE_REWRITE_TAC [poly_exp]) THEN (ONCE_REWRITE_TAC [ALL]) THEN
      (ONCE_REWRITE_TAC [ALL]) THEN (SIMP_TAC [SPEC `1` N_IS_INT]);
      (ONCE_REWRITE_TAC [poly_exp]) THEN (REPEAT STRIP_TAC) THEN (ACCEPT_TAC lem05)
   ]
)

let BLAHBLAH = PROVE(
    `! p1 p2. (LENGTH p1 <= LENGTH p2) ==> (&0 ## p1 ++ p2) = p2`,
     LIST_INDUCT_TAC THENL
     [ (SIMP_TAC [LENGTH;poly_cmul;poly_add]);
       LIST_INDUCT_TAC THENL
       [ (SIMP_TAC [LENGTH]) THEN ARITH_TAC;
         (ASM_SIMP_TAC [poly_cmul;poly_add;NOT_CONS_NIL;HD;TL;
                        REAL_ARITH `&0 * h + h' = h'`;LENGTH;
                        ARITH_RULE `(SUC x) <= (SUC y) <=> x <= y`]) ]
     ]
)

let BLAHBLAH3 = PROVE(
    `! n h t. (LENGTH t) <= LENGTH (poly_exp [&0;&1] n ** CONS h t)`,
    let lem04 = ASSUME `! h t . LENGTH t <= LENGTH (poly_exp [&0;&1] n ** CONS h t)` in
    let lem05 = SPECL [`h:real`;`t:(real)list`] lem04  in
    let lem06 = ARITH_RULE `!(x:num) y . x <= y ==> x <= SUC y` in
    let lem07 = MATCH_MP lem06 lem05   in
    let lem08 = GEN_ALL lem07  in
     INDUCT_TAC THENL
     [ (SIMP_TAC [poly_exp;poly_mul;poly_cmul;POLY_CMUL_LID;LENGTH]) THEN ARITH_TAC;
       (SIMP_TAC [POLY_EXP_X_REC;poly_mul;NOT_POLY_EXP_X_NIL;poly_cmul;poly_add;NOT_CONS_NIL;LENGTH;TL]) THEN
       (ASM_SIMP_TAC [BLAHBLAH]) THEN (ACCEPT_TAC lem08)
    ]
)
let TELEVISION = PROVE (
    `!n p.(~ (p = [])) ==>  EL n (poly_exp [&0;&1] n ** p) = HD p`,
    let lem = MATCH_MP BLAHBLAH (SPEC_ALL BLAHBLAH3) in
    INDUCT_TAC THENL
    [ (SIMP_TAC [EL;poly_exp;POLY_MUL_CLAUSES]) THEN (LIST_INDUCT_TAC) THENL
      [ (SIMP_TAC[]); (SIMP_TAC [NOT_CONS_NIL;POLY_CMUL_LID])];
        (SIMP_TAC [EL;POLY_EXP_X_REC;poly_mul;NOT_POLY_EXP_X_NIL]) THEN
        LIST_INDUCT_TAC THENL
        [ (SIMP_TAC []);
          (SIMP_TAC [poly_cmul;poly_add;NOT_CONS_NIL;TL;HD]) THEN
          (ASM_SIMP_TAC [lem;NOT_CONS_NIL;HD])
        ]
    ]
)
let JOSHUA = PROVE(
    `!i n p.(~ (p = [])) /\ (i < n) ==>  EL i (poly_exp [&0;&1] n ** p) = &0`,
    let lem0000 = SPECL [`t:(real)list`;`poly_exp [&0;&1] n ** (CONS h t)`] BLAHBLAH in
    let lem0001 = MATCH_MP lem0000 (SPEC_ALL BLAHBLAH3)  in
    let lem0002 = ASSUME `! n p . ~(p = []) /\ i < n ==> EL i (poly_exp [&0;&1] n ** p) = &0` in
    let lem0003 = SIMP_RULE [NOT_CONS_NIL] (SPECL [`n:num`;`(CONS (h:real) t)`] lem0002) in
    INDUCT_TAC THENL
    [ INDUCT_TAC THENL
      [ ARITH_TAC ;
        LIST_INDUCT_TAC THENL
        [ (SIMP_TAC[]);
          (SIMP_TAC [POLY_EXP_X_REC;EL;HD;poly_mul;NOT_POLY_EXP_NIL;NOT_CONS_NIL;HD_POLY_ADD;poly_cmul]) THEN
           REAL_ARITH_TAC
        ]
      ];
      INDUCT_TAC THENL
      [ ARITH_TAC;
       (SIMP_TAC [EL;POLY_EXP_X_REC;poly_mul;NOT_POLY_EXP_NIL;NOT_CONS_NIL]) THEN
       LIST_INDUCT_TAC THENL
       [ (SIMP_TAC[]);
         (SIMP_TAC [poly_cmul;poly_add;NOT_CONS_NIL;TL;lem0001]) THEN
         (SIMP_TAC [ARITH_RULE `(SUC i) < (SUC n) <=> i < n`;lem0003])
       ]
      ]
    ]
)
let POLY_MUL_HD = PROVE(
    `! p1 p2. (~(p1 = []) /\ ~(p2 = [])) ==> (HD (p1 ** p2)) = (HD p1) * (HD p2)`,
    LIST_INDUCT_TAC THENL
    [ (SIMP_TAC[]);
      (LIST_INDUCT_TAC) THENL
      [ (SIMP_TAC[]);
        (SIMP_TAC [NOT_CONS_NIL]) THEN (ONCE_REWRITE_TAC [poly_mul]) THEN
        (ASM_CASES_TAC `(t:(real)list) = []`) THENL
        [ (ASM_SIMP_TAC [HD;poly_cmul]);
          (ASM_SIMP_TAC [HD;poly_cmul;poly_add]) THEN
          (SIMP_TAC [NOT_CONS_NIL;HD]) THEN (REAL_ARITH_TAC)
        ]
      ]
    ]
)
let POLY_MUL_ITER_HD_FACTORIAL = PROVE(
    `! n. (HD (poly_mul_iter (\i.[-- &i; &1]) n)) = ((-- &1) pow n) * (&(FACT n))`,
    let lem01 = PROVE(`~([-- &(SUC n); &1] = [])`,SIMP_TAC [NOT_CONS_NIL]) in
    let lem02 = ISPECL
                  [`[-- &(SUC n); &1]`;`poly_mul_iter (\i.[-- &i; &1]) n`]
                  POLY_MUL_HD in
    let lem03 = CONJ lem01 (SPEC_ALL NOT_POLY_MUL_ITER_NIL) in
    let lem04 = MP lem02 lem03 in
    let lem05 = PROVE(
        `!n. ((-- &1) pow n) = -- ((-- &1) pow (SUC n))`,
        STRIP_TAC THEN (ONCE_REWRITE_TAC [pow]) THEN REAL_ARITH_TAC
    ) in
    INDUCT_TAC THENL
    [ (ONCE_REWRITE_TAC [Pm_eqn5.POLY_MUL_ITER]) THEN (SIMP_TAC [HD;FACT]) THEN REAL_ARITH_TAC;
      (ONCE_REWRITE_TAC [Pm_eqn5.POLY_MUL_ITER]) THEN BETA_TAC THEN
      (ONCE_REWRITE_TAC [lem04]) THEN (ONCE_REWRITE_TAC [HD]) THEN
      (ASM_SIMP_TAC []) THEN (ONCE_REWRITE_TAC [FACT]) THEN
      (ONCE_REWRITE_TAC [GSYM REAL_OF_NUM_MUL]) THEN
      (CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [lem05]))) THEN REAL_ARITH_TAC
    ]
)
let PLANETMATH_THM_5_1 =  PROVE(
    `! n p.
       p > 0 ==>
       n > 0 ==>
       ? As .
          ((g n p) = (&1/(&(FACT (p  - 1)))) ## As)
       /\ (! i. i< (p-1) ==> (EL i As) = &0)
       /\ ((EL (p-1) As) = ((-- &1) pow (n * p)) * ((&(FACT n)) pow p))
       /\ (ALL integer As)`,
    let lem01 = SPECL [`poly_exp [&0;&1] (p - 1)`;`poly_exp (poly_mul_iter (\i.[-- &i; &1]) n) p`] ALL_IS_INT_POLY_MUL in
    let lem02 = SPECL [`p-1`;`[&0;&1]`] ALL_IS_INT_POLY_EXP in
    let lem03 = PROVE(`ALL integer [&0;&1]`, (REWRITE_TAC [ALL]) THEN (SIMP_TAC [N_IS_INT])) in
    let lem04 = MP lem02 lem03 in
    let lem05 = SPECL [`p:num`;`poly_mul_iter (\i.[-- &i; &1]) n`] ALL_IS_INT_POLY_EXP in
    let lem06 = MP lem05 (SPEC_ALL ALL_IS_INT_POLY_MUL_ITER)  in
    let lem07 = MP lem01 (CONJ lem04 lem06)  in
    let lem08 = SPECL [`p-1`;`poly_exp (poly_mul_iter (\i.[-- &i; &1]) n) p`] TELEVISION in
    let lem09 = SIMP_RULE [ NOT_POLY_EXP_NIL;NOT_POLY_MUL_ITER_NIL] lem08 in
    let lem10 = SPECL [`i:num`;`p - 1`;`poly_exp (poly_mul_iter (\i. [ -- &i; &1]) n ) p`] JOSHUA in
    let lem11 = SIMP_RULE [NOT_POLY_MUL_ITER_NIL;NOT_POLY_EXP_NIL] lem10 in
    (REPEAT STRIP_TAC) THEN
    (EXISTS_TAC `((poly_exp [&0;&1] (p-1)) ** (poly_exp (poly_mul_iter (\i.[-- &i; &1]) n) p))`) THEN
    CONJ_TAC THENL
    [ (ONCE_REWRITE_TAC [Pm_eqn5.PLANETMATH_EQN_5]) THEN (SIMP_TAC[]);
      CONJ_TAC THENL
      [ (SIMP_TAC [lem11]);
        CONJ_TAC THENL
        [ (ONCE_REWRITE_TAC [lem09]) THEN
          (SPEC_TAC (`n:num`,`n:num`)) THEN
          (INDUCT_TAC) THENL
          [ (SIMP_TAC [NOT_CONS_NIL;HD_POLY_EXP;HD;Pm_eqn5.POLY_MUL_ITER;FACT;pow;
                       REAL_POW_ONE;ARITH_RULE `0 * p = 0`;REAL_ARITH `&1 * &1 = &1`]);
            (SIMP_TAC [HD_POLY_EXP; NOT_POLY_MUL_ITER_NIL; POLY_MUL_ITER_HD_FACTORIAL]) THEN
            (SIMP_TAC [REAL_POW_MUL;REAL_POW_POW;BLAHBLAH3]) ];
          ACCEPT_TAC lem07 ]
      ]
    ]
)
let as_def =
    let ll01 = SPEC_ALL PLANETMATH_THM_5_1 in
    let FO_LEMMA1 = PROVE(`((p > 0) ==> (n > 0) ==> (? z. C p n z))
                            <=> (? z. (p > 0) ==> (n > 0) ==> C p n z)`,MESON_TAC[]) in
    let ll02 = GEN_ALL (SIMP_RULE [FO_LEMMA1] ll01) in
    let ll03 = ONCE_REWRITE_RULE [SKOLEM_CONV (concl ll02)] ll02 in
    new_specification ["As"] ll03
(* split up def of As into its four conjuncts *)
let g_eq_As
    = (GEN_ALL o DISCH_ALL o CONJUNCT1 o  UNDISCH o UNDISCH o SPEC_ALL) as_def
let prefix_As_zero
    = (GEN_ALL o DISCH_ALL o CONJUNCT1 o CONJUNCT2 o  UNDISCH o UNDISCH o SPEC_ALL) as_def
let fact_As
    = (GEN_ALL o DISCH_ALL o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o  UNDISCH o UNDISCH o SPEC_ALL) as_def
let ALL_integer_As
    = (GEN_ALL o DISCH_ALL o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o  UNDISCH o UNDISCH o SPEC_ALL) as_def

let POLY_DIFF_AUX_LEM1 = PROVE(
    `! i p k. i < (LENGTH p) ==> EL i (poly_diff_aux k p) = (EL i p) * &(i + k)`,
    let lem0001 = ASSUME `! p k . i < LENGTH p ==> EL i (poly_diff_aux k p ) = EL i p * &(i + k)` in
    let lem0002 = SPECL [` t:(real)list`;`SUC k`] lem0001 in
    let lem0003 = PROVE(`SUC i < LENGTH (CONS (h:real) t) <=> i < LENGTH t`,(SIMP_TAC [LENGTH]) THEN ARITH_TAC) in
    INDUCT_TAC THENL
    [ LIST_INDUCT_TAC THENL
      [ (SIMP_TAC [poly_diff_aux;LENGTH]) THEN ARITH_TAC;
        (SIMP_TAC [poly_diff_aux;ARITH_RULE `0 + k = k`;poly_diff;LENGTH;EL;HD;TL]) THEN REAL_ARITH_TAC ];
      LIST_INDUCT_TAC THENL
      [ (SIMP_TAC [LENGTH]) THEN ARITH_TAC;
        (SIMP_TAC [poly_diff_aux;EL;TL]) THEN STRIP_TAC THEN
        (SIMP_TAC [lem0003;lem0002;ARITH_RULE `i + SUC k = SUC i + k`]) ]
    ]
)
let EL_POLY_DIFF = PROVE(
    `! i p. i < (LENGTH (poly_diff p)) ==> EL i (poly_diff p) = (EL (SUC i) p) * &(SUC i)`,
    let lem01 =  SPECL [`SUC i`;`t:(real)list`;`1`] POLY_DIFF_AUX_LEM1  in
    INDUCT_TAC THENL
    [ LIST_INDUCT_TAC THENL
      [ ((SIMP_TAC [LENGTH;poly_diff]) THEN ARITH_TAC);
        (SIMP_TAC [LENGTH;PRE;EL;HD;TL;ARITH_RULE `SUC 0 = 1`;REAL_ARITH `x * &1 = x`;poly_diff;NOT_CONS_NIL]) THEN
        (SPEC_TAC (`t:(real)list`,`t:(real)list`)) THEN
        LIST_INDUCT_TAC THENL [(SIMP_TAC [LENGTH;poly_diff_aux]) THEN ARITH_TAC;
                               (SIMP_TAC [HD;poly_diff_aux;REAL_ARITH `&1 * h = h`])]
     ];
     LIST_INDUCT_TAC THENL
     [ ((SIMP_TAC [LENGTH;HD;poly_diff;REAL_ARITH `&1 * h = h`])) THEN ARITH_TAC;
        (SIMP_TAC [poly_diff;NOT_CONS_NIL;TL;LENGTH_POLY_DIFF_AUX ]) THEN (SIMP_TAC [lem01;EL;TL]) THEN ARITH_TAC ]
     ]
)
let POLY_AT_ZERO = PROVE(
    `!p .(~(p = [])) ==> poly p (&0) = HD p`,
    LIST_INDUCT_TAC THENL [ SIMP_TAC []; (SIMP_TAC [poly;HD]) THEN REAL_ARITH_TAC ]
)
let PDI_POLY_DIFF_COMM = PROVE(
    `! p n.(poly_diff_iter (poly_diff p) n) = (poly_diff (poly_diff_iter p n))`,
    STRIP_TAC THEN INDUCT_TAC THENL
    [(SIMP_TAC [Pm_lemma1.PDI_DEF]);
     (ONCE_REWRITE_TAC [Pm_lemma1.PDI_DEF]) THEN (ASM_SIMP_TAC [])]
)
let EL_PDI_AT_ZERO = PROVE(
     `!i p. (i < (LENGTH p))
         ==> ( poly (poly_diff_iter p i) (&0)) = ((EL i p) * (&(FACT i)))`,
    let lem03 = PROVE(`SUC i < LENGTH (CONS (h:real) t) <=> i < LENGTH t`,(SIMP_TAC [LENGTH]) THEN ARITH_TAC) in
    let lem04 = ASSUME `!p . i < LENGTH p ==> poly (poly_diff_iter p i) (&0) = EL i p * &(FACT i)` in
    let lem05 = SIMP_RULE [LENGTH_POLY_DIFF;LENGTH;PRE] (SPEC `poly_diff (CONS h t)` lem04) in
    let lem06 = PROVE(`i < LENGTH t ==> i < LENGTH (poly_diff (CONS h t))`,SIMP_TAC [LENGTH_POLY_DIFF;PRE;LENGTH]) in
    INDUCT_TAC THENL
    [ (LIST_INDUCT_TAC THENL
      [(SIMP_TAC [LENGTH]) THEN ARITH_TAC; (SIMP_TAC [Pm_lemma1.PDI_DEF;FACT;EL;NOT_CONS_NIL;POLY_AT_ZERO]) THEN REAL_ARITH_TAC]);
      LIST_INDUCT_TAC THENL
      [ (SIMP_TAC [LENGTH]) THEN ARITH_TAC;
        (SIMP_TAC [Pm_lemma1.PDI_DEF;GSYM PDI_POLY_DIFF_COMM;lem03;lem05]) THEN
        (SIMP_TAC [lem06;EL_POLY_DIFF;FACT;REAL_OF_NUM_MUL;GSYM REAL_MUL_ASSOC])
      ]
    ]
)
let EL_PDI_AT_ZERO2 = PROVE(
    `!i p. ((~ (p = [])) /\ (i <= (LENGTH p) - 1)) ==> ( poly (poly_diff_iter p i) (&0)) = ((EL i p) * (&(FACT i)))`,
    STRIP_TAC THEN LIST_INDUCT_TAC THEN
    (SIMP_TAC [NOT_CONS_NIL;LENGTH;ARITH_RULE `(i <= (SUC x) -1) <=> (i < (SUC x))`;EL_PDI_AT_ZERO])
)
let POLY_CMUL_PDI = PROVE(
    `!p c i. (poly_diff_iter (c ## p) i) = c ##(poly_diff_iter p i)`,
    STRIP_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN (ASM_SIMP_TAC [Pm_lemma1.PDI_DEF;POLY_CMUL_POLY_DIFF])
)
let LENGTH_g = PROVE(
    `! n p . (LENGTH (g n p)) >= p `,
    let lem00 = ARITH_RULE `SUC ((SUC p ) - 1) = SUC p` in
    let lem01 = PROVE(`! n p. ~((poly_exp (poly_mul_iter (\i.[-- &i; &1]) n ) (SUC p)) = [])`,
                       SIMP_TAC [NOT_POLY_EXP_NIL; NOT_POLY_MUL_ITER_NIL]) in
    let lem02 = MATCH_MP POLY_MUL_LENGTH2 (SPEC_ALL lem01) in
    let lem03 = SPECL [`poly_exp [&0;&1] (SUC p - 1)`] lem02 in
    let lem04 = SIMP_RULE [POLY_EXP_X_LENGTH] lem03 in
    let lem05 = SIMP_RULE [lem00] lem04 in
     (SIMP_TAC [Pm_eqn5.PLANETMATH_EQN_5;POLY_CMUL_LENGTH]) THEN STRIP_TAC THEN INDUCT_TAC THENL
     [ ARITH_TAC; SIMP_TAC [lem05]]
)
let LENGTH_As = PROVE(
    `! n p . p > 0 ==> n > 0 ==> LENGTH (As n p) >= p`,
    let lem50 = ADD_ASSUM `p > 0` (ADD_ASSUM `n > 0` (SPEC_ALL LENGTH_g)) in
    let lem51 = ONCE_REWRITE_RULE [UNDISCH_ALL (SPEC_ALL g_eq_As)] lem50 in
    let lem52 = ONCE_REWRITE_RULE [POLY_CMUL_LENGTH] lem51 in
    SIMP_TAC [lem52]
)
let REAL_MUL_RDIV = PROVE(
    `!x y. ~(y = &0) ==> ((x * y) / y = x)`,
    SIMP_TAC[real_div; GSYM REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_MUL_RID]
)
let REAL_MUL_DIV_ASSOC = PROVE(
    `!x y z.((x * z) / y = x * (z / y))`,
    SIMP_TAC [real_div;GSYM REAL_MUL_ASSOC]
)
let IS_INT_FACT_DIV = PROVE(
    `! n m. n >= m ==> integer ( (&(FACT n))/(&(FACT m)) )`,
    let lem0 = SPEC_ALL (ONCE_REWRITE_RULE [GSYM (SPECL [`FACT n`;`0`] REAL_OF_NUM_EQ)] FACT_NZ) in
    let lem1 = SPECL [`&(SUC n)`;`&(FACT n)`]  REAL_MUL_RDIV in
    let lem2 = MP lem1 lem0 in
    let lem4 = ASSUME `! m. n >= m ==> integer (&(FACT n)/ &(FACT m))` in
    let lem5 = UNDISCH (SPEC_ALL lem4) in
    let lem6 = PROVE(`integer(&(SUC n))`,SIMP_TAC [N_IS_INT]) in
    let lem7 = CONJ lem6 lem5 in
    let lem8 = MATCH_MP INTEGER_MUL lem7  in
    let lem9 = UNDISCH_ALL (ARITH_RULE `(~(n >= m)) ==> (SUC n >= m) ==>  m = SUC n`) in
    INDUCT_TAC THENL
    [ (SIMP_TAC [ARITH_RULE `0 >= m ==> m = 0`;FACT_NZ;REAL_OF_NUM_EQ;REAL_DIV_REFL;N_IS_INT]);
      (STRIP_TAC) THEN (ASM_CASES_TAC `(n:num) >= m`) THENL
      [ (ASM_SIMP_TAC [FACT;GSYM REAL_OF_NUM_MUL;lem2;N_IS_INT]) THEN
        (SIMP_TAC [FACT;GSYM REAL_OF_NUM_MUL;REAL_MUL_DIV_ASSOC;lem8]);
        (STRIP_TAC) THEN
        (SIMP_TAC [lem9;FACT_NZ;REAL_OF_NUM_EQ;REAL_DIV_REFL;N_IS_INT])
      ]
    ]
)
let SATURDAY_LEMMA = PROVE(
    `!x. p > 1 ==> m >= p ==> x * ((&(FACT m))/(&(FACT (p-1)))) = x * (&p) * ((&(FACT m))/(&(FACT p)))`,
    let lem01 = UNDISCH (ARITH_RULE `p > 1 ==> SUC (p -1) = p`) in
    let lem02 = ADD_ASSUM `p > 1` (SPEC `p - 1` (CONJUNCT2 FACT)) in
    let lem03 = GSYM (ONCE_REWRITE_RULE [lem01] lem02) in
    let lem04 =  SPEC `&p` REAL_DIV_REFL in
    let lem05 = ADD_ASSUM `p > 1` (SPECL [`p:num`;`0`] REAL_OF_NUM_EQ) in
    let lem06 = SIMP_RULE [UNDISCH (ARITH_RULE `p > 1 ==> ~(p = 0)`)] lem05 in
    let lem07 = GSYM (MP lem04 lem06) in
    (REPEAT STRIP_TAC) THEN
    (CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [GSYM REAL_MUL_LID]))) THEN
    (ONCE_REWRITE_TAC [lem07]) THEN
    (ONCE_REWRITE_TAC [real_div]) THEN
    (ONCE_REWRITE_TAC [REAL_ARITH `((x1:real) * x2) * x * (x3 * x4) = x * x1 * (x3 * (x2 * x4))`]) THEN
    (ONCE_REWRITE_TAC [GSYM REAL_INV_MUL]) THEN
    (ONCE_REWRITE_TAC [REAL_OF_NUM_MUL]) THEN
    (SIMP_TAC [REAL_MUL_ASSOC;GSYM REAL_INV_MUL]) THEN
    (ONCE_REWRITE_TAC [lem03]) THEN
    (SIMP_TAC [REAL_MUL_ASSOC;GSYM REAL_OF_NUM_MUL])
)
let SHRIVER = PROVE(
    `!f0. (!i. m <= i /\ i <= SUC n ==> (f0 i))
       ==> (!i. m <= i /\ i <= n ==> (f0 i)) `,
    let lem01 = UNDISCH_ALL (ARITH_RULE `i <= n ==> i <= SUC n`) in
    let lem02 = CONJ (ASSUME `(m:num) <= (i:num)`) lem01  in
    let lem03 = ASSUME `!i. m <= i /\ i <= SUC n ==> (f0 i)` in
    let lem04 = SPEC_ALL lem03 in
    let lem05 = MP lem04 lem02 in
    (REPEAT STRIP_TAC) THEN (ACCEPT_TAC lem05)
)
let IS_INT_SUM = PROVE(
 `!f n m.(!i.m <= i /\  i <= n ==> integer (f i)) ==> integer (sum (m..n) f)`,
  let l0 = SPECL [`m:num`;`n:num`;`i:num`] IN_NUMSEG in
  let l1 = SPECL [`m:num`;`SUC n`] NUMSEG_EMPTY in
  let l2 = ADD_ASSUM `SUC n < m` l1 in
  let l3 = ASM_REWRITE_RULE [] l2 in
  let l4 = (UNDISCH o ARITH_RULE) `~(SUC n < m) ==> m <= SUC n` in
  let l5 = ONCE_REWRITE_RULE [GSYM IN_NUMSEG] SHRIVER in
  let l6 = SPEC `\(i:num).(integer (f i))` l5 in
  let l7 = BETA_RULE l6 in
  let l8 = ASSUME `! m. (!i. i IN m..n ==> integer (f i)) ==> integer (sum (m..n) f)` in
  let l9 = SPEC_ALL l8 in
  let l10 = UNDISCH (IMP_TRANS l7 l9) in
  let jj0 = ARITH_RULE `(~(SUC n < m)) ==> m <= SUC n /\ (SUC n) <= SUC n` in
  let jj1 = UNDISCH (ONCE_REWRITE_RULE [GSYM IN_NUMSEG] jj0) in
  let jj2 = SPEC `SUC n` (ASSUME `!i. i IN m.. SUC n ==> integer (f i)`) in
  let jj3 = (MP jj2 jj1) in
  let l18 = CONJ l10 jj3 in
  let l19 = MATCH_MP INTEGER_ADD l18 in
  let l20 = DISCH `!i. i IN m..SUC n ==> integer (f i)` l19 in
  let l21 = ASSUME `!i . i = 0 ==> integer (f 0)` in
  let l22 = SIMP_RULE [] (SPEC `0` l21) in
  (ONCE_REWRITE_TAC [GSYM l0]) THEN STRIP_TAC THEN
  INDUCT_TAC THENL
  [ STRIP_TAC THEN
    (ASM_CASES_TAC `m = 0`) THENL
    [ (ASM_SIMP_TAC []) THEN
      (ONCE_REWRITE_TAC [NUMSEG_CONV `0..0`]) THEN
      (ONCE_REWRITE_TAC [ SUM_SING]) THEN
      (SIMP_TAC [IN_SING]) THEN (DISCH_TAC) THEN (SIMP_TAC [l22]);
      (ASM_SIMP_TAC [NUMSEG_CLAUSES;SUM_CLAUSES;N_IS_INT])
    ];
    STRIP_TAC THEN (ASM_CASES_TAC `SUC n < m`) THENL
    [ (ASM_SIMP_TAC [l3;SUM_CLAUSES;N_IS_INT]);
      (ASM_SIMP_TAC [l4;SUM_CLAUSES_NUMSEG]) THEN
      (ACCEPT_TAC l20)
    ]
  ]
)
let ALL_IMP_EL = PROVE(
    `! (l:(a)list) i P. (ALL P l) ==> (i < LENGTH l) ==> P (EL i l)`,
    SIMP_TAC[GSYM ALL_EL]
)
let KEY_LEMMA = PROVE(
    `n > 0 ==>
     p > 0 ==>
    ! i . p <= i /\ i <= (LENGTH (As n p) - 1) ==> integer ((&(FACT i)/ &(FACT p)) * (EL i (As n p)))`,
    let jem0 = ISPECL [`(As n p)`;`i:num`;`integer`] ALL_IMP_EL in
    let jem1 = MP jem0 (UNDISCH (UNDISCH (SPEC_ALL ALL_integer_As)))  in
    let jem3 = ARITH_RULE `LENGTH (As n p) > 0 ==> ((i < LENGTH (As n p)) <=> i <= LENGTH (As n p) - 1)` in
    let jem4 = UNDISCH_ALL ((SPEC_ALL LENGTH_As)) in
    let jem5 = UNDISCH (ARITH_RULE `p > 0 ==> (LENGTH (As n p) >= p) ==> (LENGTH (As n p) > 0)`) in
    let jem6 = MP jem5 jem4 in
    let jem7 = MP jem3 jem6 in
    let jem8 = ONCE_REWRITE_RULE [jem7] jem1 in
    let kem0 = SPECL [`i:num`;`p:num`] IS_INT_FACT_DIV in
    let kem1 = ADD_ASSUM  `p <= (i:num)` (ADD_ASSUM `i <= (LENGTH (As n p) - 1)` kem0) in
    let kem2 = SIMP_RULE [UNDISCH_ALL (ARITH_RULE `p <= i ==> i <= LENGTH (As n p) -1 ==> i >= p`)] kem1 in
    (REPEAT STRIP_TAC) THEN (SIMP_TAC[UNDISCH jem8;kem2;INTEGER_MUL])
)

let KEY_LEMMA2 = PROVE(
    `p > 1 ==>
     n > 0 ==>
     ? K0 .   integer K0
           /\ (&1 / &(FACT ( p - 1))) * (sum (p.. LENGTH (As n p) -1) (\m. EL m (As n p) * &(FACT m))) = (&p) * K0`,
    let lem0000 = SPEC `EL m (As n p)` SATURDAY_LEMMA in
    let lem1000 = DISCH `m <= LENGTH (As n p) -1` (ADD_ASSUM `m <= LENGTH (As n p) -1` (UNDISCH_ALL lem0000)) in
    let lem2000 = DISCH `(m:num) >= p` lem1000 in
    let lem3000 = ONCE_REWRITE_RULE [ARITH_RULE `(m:num) >= p <=> p <= m`] lem2000 in
    let lem4000 = ONCE_REWRITE_RULE [TAUT `(a ==> b ==> c) <=> ((a  /\ b) ==> c)`] (GEN `m:num` lem3000) in
    let lem5000 = MATCH_MP SUM_EQ_NUMSEG lem4000 in
    let nem2 = SPECL [`\x.(&(FACT x)/ &(FACT p)) * (EL x (As n p))`;`LENGTH (As n p) - 1`;`p:num`] IS_INT_SUM in
    let nem3 = BETA_RULE nem2 in
    let nem4 = SIMP_RULE [UNDISCH (UNDISCH KEY_LEMMA)] nem3 in
    let nem5 = ADD_ASSUM `p > 1` (DISCH `p > 0` nem4) in
    let nem6 = SIMP_RULE [(UNDISCH o ARITH_RULE) `(p:num) > 1 ==> p > 0`] nem5 in
    STRIP_TAC THEN STRIP_TAC THEN (ONCE_REWRITE_TAC [GSYM SUM_LMUL]) THEN
    (BETA_TAC) THEN (ONCE_REWRITE_TAC [real_div]) THEN (ONCE_REWRITE_TAC [REAL_MUL_LID]) THEN
    (ONCE_REWRITE_TAC [REAL_ARITH `(x1:real) * x2 * x3 = x2 * (x3 * x1)`]) THEN
    (ONCE_REWRITE_TAC [GSYM real_div]) THEN (ONCE_REWRITE_TAC [lem5000]) THEN
    (ONCE_REWRITE_TAC [REAL_ARITH `(x1:real) * x2 * x3 = x2 * (x3 * x1)`]) THEN
    (ONCE_REWRITE_TAC [SUM_LMUL]) THEN
    (EXISTS_TAC `sum (p .. LENGTH (As n p) -1) (\x. &(FACT x) / &(FACT p) * EL x (As n p))`) THEN
    (SIMP_TAC [nem6])
)
let NOT_g_NIL = PROVE(
    `!n p . ~ ((g n p ) = [])`,
     SIMP_TAC [Pm_eqn5.PLANETMATH_EQN_5; NOT_CONS_NIL; NOT_POLY_EXP_NIL; NOT_POLY_CMUL_NIL;
               NOT_POLY_MUL_NIL;NOT_POLY_MUL_ITER_NIL]
)
let FACT_DIV_RCANCELS = PROVE(
    `!n x. x / &(FACT n) * &(FACT n) = x`,
    MESON_TAC [REAL_ARITH `!x. &0 < x ==> ~(x = &0)`;
               REAL_DIV_RMUL;FACT_LT;REAL_OF_NUM_LT]
)

let PSUM_ITERATE = PROVE(
    `! n m f. psum (m,n) f
              = if (n > 0) then (iterate (+) (m..((n+m)-1)) f) else &0`,
    let lem01 = ARITH_RULE `~(n+m=0) ==> (SUC n + m) -1 = SUC ((n + m) -1)` in
    let lem02 = MP (ISPEC `(+)` ITERATE_SING) MONOIDAL_REAL_ADD in
    let lem03 = PROVE(
          `iterate (+) (m..SUC ((n + m) - 1)) f
           = f (SUC ((n+m)-1)) + iterate (+) (m..(n+m)-1) f`,
           MESON_TAC [ARITH_RULE `m <= SUC ((n+m)-1)`;ITERATE_CLAUSES_NUMSEG;
                      MONOIDAL_REAL_ADD;REAL_ADD_SYM]) in
    let lem04 = UNDISCH (UNDISCH (ARITH_RULE `~(n+m=0) ==> n=0 ==> m-1 < m`)) in
    let lem05 = SIMP_RULE [lem04] (SPECL [`m:num`;`m-1`] NUMSEG_EMPTY) in
    INDUCT_TAC THENL
    [ SIMP_TAC [ARITH_RULE `~(0 > 0)`;sum_DEF];
      (SIMP_TAC [ARITH_RULE `(SUC n) > 0`]) THEN (REPEAT STRIP_TAC) THEN
      (ASM_CASES_TAC `n + m =0`) THENL
      [ (REWRITE_TAC [UNDISCH (ARITH_RULE `n + m = 0 ==> n = 0`)]) THEN
        (REWRITE_TAC [lem02;NUMSEG_SING;ARITH_RULE `(SUC 0 +m) -1 = m`]) THEN
        (MESON_TAC [sum_DEF; ADD_CLAUSES;REAL_ARITH `&0 + x = x`]) ;
        (ONCE_REWRITE_TAC [sum_DEF;UNDISCH lem01]) THEN
        (REWRITE_TAC [lem03]) THEN (ASM_CASES_TAC `n = 0`) THEN
        (ASM_SIMP_TAC
          [ARITH_RULE `~(0 > 0)`;ADD_CLAUSES;REAL_ADD_LID;REAL_ADD_RID;
           lem05;ITERATE_CLAUSES_GEN; MONOIDAL_REAL_ADD;NEUTRAL_REAL_ADD;
           REAL_ADD_SYM;ADD_SYM;ARITH_RULE `~(n=0) ==> n>0 /\ SUC (n-1) = n`])
      ]
    ]
)


let PLANETMATH_EQN_5_2 = PROVE(
    `p > 1 ==>
     n > 0 ==>
     (? K0.   integer K0
           /\ poly (SOD (g n p)) (&0) =
              &(FACT n) pow p * -- &1 pow (n * p) + &p * K0)`,
    let lem01 = SPECL [`g n p`;`x:real`;`(&0):real`] Pm_lemma2.PLANETMATH_LEMMA_2_B in
    let lem02 = GEN_ALL lem01 in
    let lem03 = SPEC_ALL (BETA_RULE lem02) in
    let lem04 = SIMP_RULE [FACT_DIV_RCANCELS] lem03 in
    let lem05 = SIMP_RULE [PSUM_ITERATE] lem04 in
    let lem06 = SIMP_RULE [ARITH_RULE `(n:num) + 0 = n`] lem05 in
    let lem07 = ADD_ASSUM `n > 0` (ADD_ASSUM `p > 0` lem06) in
    let lem08 = REWRITE_RULE [GSYM LENGTH_EQ_NIL;ARITH_RULE `~(x = 0) <=> x > 0`] NOT_g_NIL in
    let lem09 = SIMP_RULE [lem08] lem07 in
    let lem10 = CONV_RULE (RAND_CONV (REWRITE_CONV [UNDISCH_ALL (SPEC_ALL g_eq_As)])) lem09 in
    let lem11 = SIMP_RULE [POLY_CMUL_LENGTH] lem10 in
    let lem12 = SPECL [`m:num`;`(As n p)`] EL_PDI_AT_ZERO in
    let lem13 = SIMP_RULE [POLY_CMUL_PDI;POLY_CMUL;lem12] lem11 in
    let lem14 = GSYM (BETA `(\m. poly (poly_diff_iter (As n p) m) (&0)) m`) in
    let lem15 = ISPECL [`(\m. poly (poly_diff_iter (As n p) m) (&0))`;`&1/ &(FACT (p - 1))`;`0..LENGTH (As n p) -1`] SUM_LMUL in
    let lem16 = ONCE_REWRITE_RULE [lem14] lem13 in
    let lem17 = ONCE_REWRITE_RULE [GSYM sum] lem16 in
    let lem18 = SIMP_RULE [GSYM lem17] lem15 in
    let lem20 = SPECL [`(\m.  poly (poly_diff_iter (As n p) m) (&0))`;`(\m. EL m (As n p) * &(FACT m))`;`0`;`LENGTH (As n p) - 1`] SUM_EQ_NUMSEG in
    let lem21 = ONCE_REWRITE_RULE [ARITH_RULE `0 <= i`] (BETA_RULE lem20) in
    let lem22 = ADD_ASSUM `~(As n p = [])` (ONCE_REWRITE_RULE [EL_PDI_AT_ZERO2] lem21) in
    let lem30 = SPECL [`i:num`;`As n p`] EL_PDI_AT_ZERO2 in
    let lem31 = ASM_REWRITE_RULE [] (ADD_ASSUM `~(As n p = [])` lem30) in
    let lem23 = ONCE_REWRITE_RULE [lem31] lem22 in
    let lem24 = REWRITE_RULE [GSYM lem16] lem23 in
    let lem25 = ONCE_REWRITE_RULE [lem24] lem18 in
    let lem30 = ISPECL [`\m. EL m (As n p) * &(FACT m)`;`0`;`p-1`;`(LENGTH (As n p) - 1) - (p - 1)`] SUM_ADD_SPLIT in
    let lem31 = SIMP_RULE [ARITH_RULE `0 <= x`] lem30 in
    let lem32 = UNDISCH_ALL (ARITH_RULE `! x. x  >= p ==> (p - 1) + (x - 1) - (p -1)=  x - 1`) in
    let lem33 = UNDISCH_ALL (SPEC_ALL LENGTH_As) in
    let lem34 = SPEC `LENGTH (As n p)` lem32 in
    let lem35 = MP lem34 lem33 in
    let lem36 = ONCE_REWRITE_RULE [UNDISCH (ARITH_RULE `p > 1 ==> (p - 1) + 1 = p`);lem35] lem31 in
    let lem37 = ONCE_REWRITE_RULE [lem36] lem25 in
    let lem38 = SIMP_RULE [UNDISCH (ARITH_RULE `p > 1 ==> p > 0`)] (DISCH `p > 0` lem37) in
    let lem39 = ISPECL [`\m. EL m (As n p) * &(FACT m)`;`0`;`p-2`;`1`] SUM_ADD_SPLIT in
    let lem40 = ADD_ASSUM `n > 0` (ADD_ASSUM `p > 1` lem39) in
    let lem41 = SIMP_RULE (map (UNDISCH o ARITH_RULE) [`p > 1 ==> p - 2 + 1 = p-1`;`p > 1 ==> (p - 2) + 1 = p - 1`]) lem40 in
    let lem42 = SIMP_RULE [SUM_SING_NUMSEG;ARITH_RULE `0 <= x`] lem41 in
    let lem45 = ADD_ASSUM `p > 1` (SPEC_ALL prefix_As_zero) in
    let lem46 = SIMP_RULE [UNDISCH_ALL (ARITH_RULE `p > 1 ==> p > 0`)] lem45 in
    let lem47 = UNDISCH (ONCE_REWRITE_RULE [UNDISCH_ALL (ARITH_RULE `p > 1 ==> (i < p-1 <=> i <= p-2)`)] lem46) in
    let lem48 = SIMP_RULE [REAL_ARITH `((&0):real) + x = x`; SUM_EQ_0_NUMSEG;REAL_ARITH `((&0):real) * x = &0`;lem47] lem42 in
    let lem49 = SIMP_RULE [UNDISCH (ARITH_RULE `p > 1 ==> p > 0`)] (ADD_ASSUM `p > 1` (SPEC_ALL fact_As)) in
    let lem50 = SIMP_RULE [UNDISCH lem49] lem48 in
    let lem51 = ONCE_REWRITE_RULE [lem50] lem38 in
    let lem52 = SPECL [`p - 1`;`(&1):real`] FACT_DIV_RCANCELS in
    let lem53 = SIMP_RULE [REAL_ARITH `(x:real) * (y * z) = (x * z) * y`;lem52;REAL_ARITH `(x:real) * (y + z) = (x * y) + (x * z)`] lem51 in
    let lem54 = SIMP_RULE [REAL_ARITH `&1 * x = (x:real)`] lem53 in
    let josh0 = UNDISCH_ALL KEY_LEMMA2 in
    let josh1 = REAL_ARITH `!(y:real) x1 x2 . x1  = x2 <=> y + x1 = y + x2` in
    let josh2 = SPEC `(&(FACT n) pow p * -- &1 pow (n * p)):real` josh1 in
    let josh3 = ONCE_REWRITE_RULE [josh2] josh0 in
    let josh4 = ONCE_REWRITE_RULE [GSYM lem54] josh3 in
    let josh5 = DISCH `~ (As n p = [])` josh4 in
    let jem4 = ADD_ASSUM `p > 1` ((SPEC_ALL LENGTH_As)) in
    (* JOHN: the UNDISCH here is necessary... i don't think it should be *)
    let jem5 = UNDISCH (SIMP_RULE [UNDISCH (ARITH_RULE `(p:num) > 1 ==> p > 0`)] jem4) in
    let jem6 = UNDISCH (ARITH_RULE `p > 1 ==> (LENGTH (As n p) >= p) ==> ~((LENGTH (As n p) = 0))`)  in
    let jem7 = MP jem6 jem5  in
    let jem8 = SIMP_RULE [LENGTH_EQ_NIL] jem7 in
    let josh6 = MP josh5 jem8 in
    let josh7 = DISCH_ALL josh6 in
    let josh11 = ONCE_REWRITE_RULE [GSYM OLD_SUM] lem17 in
    let josh12 = REWRITE_RULE [GSYM josh11] josh7 in
    let josh13 =  SIMP_RULE [] (DISCH_ALL josh12) in
    let josh14 = BRW `(X ==> Y ==> Z ==> W) <=> ((X /\ Y /\ Z) ==> W)` josh13 in
    let josh15 = ONCE_REWRITE_RULE [ARITH_RULE `(p > 0 /\ n > 0 /\ p > 1) <=> (p > 1 /\ n > 0)`] (DISCH_ALL josh14) in
    let josh16 = BRW1 josh15 in
    let josh17 = SIMP_RULE [PSUM_ITERATE;ARITH_RULE `~(0 > 0)`] josh16 in
    ACCEPT_TAC josh17
)
let PLANETMATH_DIVIDES_FACT_PRIME_1 = PROVE (
    `!p n. (prime p) /\ p > n ==> ~(num_divides p (FACT n))`,
    (SIMP_TAC [DIVIDES_FACT_PRIME]) THEN ARITH_TAC
)
let INT_OF_REAL_NEG_NUM = PROVE(
    `!(n:num).int_of_real (-- (real_of_num n)) = -- (int_of_real (real_of_num n))`,
    SIMP_TAC [GSYM int_of_num;GSYM int_of_num_th;GSYM int_neg]
)
let ABS_EQ_ONE = PROVE(
    `!(x:real) .((abs x) = &1) ==> ((x = &1) \/ (x = -- &1))`,
    ARITH_TAC
)
let POW_NEG_1 = PROVE(
   `!(x:num). (((-- (&1 :real)) pow x) = -- &1) \/  (((-- (&1 : real)) pow x) = &1)`,
    let lem00 = ONCE_REWRITE_RULE [TAUT `x \/ y <=> y \/ x`] ABS_EQ_ONE in
    let lem01 = (SPEC `(-- (&1 :real)) pow x` lem00) in
    let lem02 = (SPEC `x:num` POW_M1) in
    let lem03 = MP lem01 lem02 in
    STRIP_TAC THEN (ACCEPT_TAC lem03)
)
let NUM_DIVIDES_INT_DIVIDES = PROVE(
    `!(x:num) (y:num).(x divides y) <=> ((&x):int divides ((&y):int))`,
    (ONCE_REWRITE_TAC [num_divides])  THEN (SIMP_TAC [])
)
let SON_OF_A_GUN = PROVE(
    `! (p:num) (n:num) .
     p > n
     ==> (prime p)
     ==> ~(int_divides (& p) (&(FACT n) pow p * -- &1 pow (n * p) ))`,
    let POW_INT_NEG_1 = INT_OF_REAL_THM POW_NEG_1 in
    let lem0000 = TAUT `(A /\ B ==> C) <=> (A ==> B ==> C)` in
    let lem0001 = ONCE_REWRITE_RULE [lem0000] PLANETMATH_DIVIDES_FACT_PRIME_1 in
    let lem0002 = UNDISCH_ALL (SPEC_ALL lem0001) in
    let lem0008 = ONCE_REWRITE_RULE [TAUT `(x /\ y ==> z) <=> (x ==> ~z ==> ~y)`]  PRIME_DIVEXP in
    let lem0009 = SPECL [`p:num`;`p:num`;`FACT n`] lem0008 in
    let lem0010 = UNDISCH lem0009 in
    let lem0011 = MP lem0010 lem0002 in
     STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
     (DISJ_CASES_TAC (SPEC `(n * p):num` POW_INT_NEG_1))  THENL
     [ (ASM_SIMP_TAC [INT_OF_NUM_POW; ARITH_RULE `x * (--(&1):int) = -- x`;ARITH_RULE `x * ((&1):int) = x`]) THEN
       (ONCE_REWRITE_TAC [GSYM INT_DIVIDES_RNEG]) THEN
       (ONCE_REWRITE_TAC [ARITH_RULE `-- -- (x:int) = x`]) THEN
       (ONCE_REWRITE_TAC [GSYM NUM_DIVIDES_INT_DIVIDES]) THEN
       (ACCEPT_TAC lem0011);
       (ASM_SIMP_TAC [INT_OF_NUM_POW; ARITH_RULE `x * (--(&1):int) = -- x`;ARITH_RULE `x * ((&1):int) = x`]) THEN
       (ONCE_REWRITE_TAC [GSYM NUM_DIVIDES_INT_DIVIDES]) THEN
       (ACCEPT_TAC lem0011)
     ]
)
let MAY_LEMMA = PROVE(
    `(p:num) > (n:num)
      ==> (prime p)
      ==> ~(int_divides (& p) ((int_of_num (FACT n)) pow p * -- &1 pow (n * p) + &p * K0))`,
      let lem00 = BRW `(x /\ y ==> z) <=> (x ==> ~z ==> ~y)` INT_DIVIDES_ADD_REVR in
      let lem0 = PROVE(`int_divides ((&p):int) (&p * K0)`,INTEGER_TAC) in
      let lem1 = (UNDISCH_ALL o SPEC_ALL) SON_OF_A_GUN in
      let lem2 = SPECL [`(&p):int`;`((&p):int) * K0`; `(&(FACT n) pow p):int *
      -- &1 pow (n * p)` ] lem00 in
      let lem3 = MP (MP lem2 lem0) lem1 in
      let lem4 = (DISCH_ALL lem3) in
      let lem5 = ONCE_REWRITE_RULE [ARITH_RULE `(x:int) + y = y + x`] lem4 in
      (ACCEPT_TAC lem5)
)
let PLANET_MATH_alpha_1 = PROVE(
    `n > 0 ==> p > n ==> prime p ==> (integer (poly (SOD (g n p )) (&0)))`,
    let a1 = UNDISCH (UNDISCH (ARITH_RULE `n > 0 ==> p > n ==> p > 1`)) in
    let a2 = UNDISCH (SIMP_RULE [] (DISCH `n > 0` (MP PLANETMATH_EQN_5_2 a1))) in
    let t1 = `integer K0 /\
              poly (SOD (g n p)) (&0) =
              &(FACT n) pow p * -- &1 pow (n * p) + &p * K0` in
    (STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC) THEN (CHOOSE_TAC a2) THEN
    (SPLIT_CONJOINED_ASSUMPT_TAC t1) THEN (ASM_REWRITE_TAC[]) THEN
    (ASM_SIMP_TAC [N_IS_INT;INTEGER_ADD;NEG_N_IS_INT;INTEGER_POW;INTEGER_MUL])
)
let PLANET_MATH_alpha_2 = PROVE(
    `n > 0 ==> p > n ==> prime p ==>
     ( ~((&p) divides (int_of_real (poly (SOD (g n p )) (&0)))))`,
    let t1 = `integer K0 /\
              poly (SOD (g n p)) (&0) =
              &(FACT n) pow p * -- &1 pow (n * p) + &p * K0` in
    let t = `((real_of_num (FACT n)) pow p) * (-- &1 pow (n * p)) + (&p * K0)` in
    let arch0 = INT_OF_REAL_CONV t in
    let a1 = UNDISCH (UNDISCH (ARITH_RULE `n > 0 ==> p > n ==> p > 1`)) in
    let a2 = UNDISCH (SIMP_RULE [] (DISCH `n > 0` (MP PLANETMATH_EQN_5_2 a1))) in
    let a3 = SPEC `int_of_real K0` (GEN `K0:int` MAY_LEMMA) in
    let a4 = GSYM (UNDISCH arch0) in
    let a5 = ONCE_REWRITE_RULE [a4] a3 in
    STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN (CHOOSE_TAC a2) THEN
    (SPLIT_CONJOINED_ASSUMPT_TAC t1) THEN (ASM_SIMP_TAC [a5])
)
let INT_OF_REAL_NEG_INT_OF_NUM = PROVE(
    `!n. int_of_real(-- (real_of_num n)) = -- int_of_num n`,
    SIMP_TAC [int_of_num;INT_OF_REAL_NEG_NUM]
)
let PLANET_MATH_alpha_3 = PROVE(
     `n > 0 ==> p > n ==> prime p ==>
      (~((poly (SOD (g n p)) (&0)) = &0))`,
      let lem0 = PROVE(
            `!(x:num) (y:real).
               (x > 0) ==>
               (integer y) ==>
               (~(&x divides (int_of_real y))) ==>
               ~(y = &0)`,
              MESON_TAC [is_int;INT_OF_NUM_GT;INT_DIVIDES_RNEG;REAL_OF_NUM_EQ;int_of_num;INT_OF_REAL_NEG_INT_OF_NUM;INT_OF_NUM_EQ;INT_DIVIDES_0]) in
      let lem1 = ARITH_RULE `n > 0 ==> p > n ==> p > 0` in
      MESON_TAC [lem0;lem1; PLANET_MATH_alpha_1; PLANET_MATH_alpha_2]
)
let PLANET_MATH_alpha = PROVE(
    `n > 0 ==> p > n ==> prime p ==>
     (     (integer (poly (SOD (g n p )) (&0)))
       /\ ~((&p) divides (int_of_real (poly (SOD (g n p )) (&0))))
       /\ ~((poly (SOD (g n p)) (&0)) = &0))`,
     SIMP_TAC [PLANET_MATH_alpha_1; PLANET_MATH_alpha_2; PLANET_MATH_alpha_3]
)
let REAL_FACT_NZ = PROVE(
    `~((&(FACT n)) = (real_of_num 0))`,
    let l0 = GSYM (SPECL [`FACT n`;`0`] REAL_OF_NUM_EQ) in
    ACCEPT_TAC (SPEC_ALL (ONCE_REWRITE_RULE [l0] FACT_NZ))
)

let IS_INT_FACT_DIV_FACT_DIV_FACT = PROVE(
    `! i k.integer ((&(FACT (i+k)))/(&(FACT i))/(&(FACT k)))`,
    let l0 = MATCH_MP (ARITH_RULE `(~(x=0)) ==> 0 < x`) (SPEC `k:num` FACT_NZ) in
    let l1 = ONCE_REWRITE_RULE [GSYM REAL_OF_NUM_LT] l0 in
    let l2 = MATCH_MP REAL_EQ_LDIV_EQ l1 in
    (REPEAT STRIP_TAC) THEN (REWRITE_TAC [is_int;l2]) THEN
    (EXISTS_TAC ` (binom(i+k,k))`) THEN DISJ1_TAC THEN
    (MESON_TAC [BINOM_FACT;MULT_SYM;MULT_ASSOC;REAL_OF_NUM_MUL;REAL_OF_NUM_EQ])
)

(*  if you replace the second SIMP_TAC with MESON_TAC, it fails!!
 *  (i alwasy thought MESON_TAC was strictly stronger than SIMP_TAC
 *)
let POLY_CMUL_EL = PROVE(
    `!p c i.(i < (LENGTH p)) ==> (EL i (c ## p)) = c * (EL i p)`,
    let l0 = ARITH_RULE `(SUC i) < (SUC j) <=> i < j` in
    LIST_INDUCT_TAC THENL
    [ (SIMP_TAC [LENGTH;ARITH_RULE `~(n < (0:num))`]);
      STRIP_TAC THEN INDUCT_TAC THENL
      [ (SIMP_TAC [poly_cmul;HD;EL]);
        (ASM_SIMP_TAC [LENGTH;poly_cmul;TL;EL;l0])
      ]
    ]
)
let PDI_COEFF_FACT = PROVE(
    `! k q i.(i < LENGTH (poly_diff_iter q k)) ==>
            (EL i (poly_diff_iter q k)) = ((&(FACT (i+k)))/(&(FACT i))) * (EL (i+k) q)`,
    let t0 = `!q i.  i < LENGTH (poly_diff_iter q k)
                  ==> EL i (poly_diff_iter q k) = &(FACT (i + k)) / &(FACT i) * EL (i + k) q` in
    let l0 = SPECL [`q:(real)list`;`SUC i`] ( ASSUME t0) in
    let l1 = ONCE_REWRITE_RULE [ARITH_RULE `(SUC i) < x <=> i < (PRE x)`] l0 in
    let l2 = ONCE_REWRITE_RULE [GSYM LENGTH_POLY_DIFF] l1 in
    let l3 = ONCE_REWRITE_RULE [FACT;GSYM REAL_OF_NUM_MUL] l2 in
    let l4 = ONCE_REWRITE_RULE [GSYM REAL_OF_NUM_MUL] l3 in
    let l5 =  REWRITE_RULE [real_div;REAL_INV_MUL] l4 in
    let l6 = REAL_ARITH `(w * (inv x) * y ) * z = (w * y * z) * (inv x)` in
    let l9 = ONCE_REWRITE_RULE [GSYM REAL_OF_NUM_LT] (ARITH_RULE `0 < SUC i`) in
    let l10 = MATCH_MP REAL_EQ_RDIV_EQ l9 in
    let l11 = ONCE_REWRITE_RULE [l6] l5 in
    let l12 = ONCE_REWRITE_RULE [real_div] l10 in
    let l13 = ONCE_REWRITE_RULE [l12] l11 in
    INDUCT_TAC THENL
    [ (REWRITE_TAC [Pm_lemma1.PDI_DEF;ARITH_RULE `i + 0 = i`]) THEN
      (MESON_TAC [REAL_DIV_REFL;FACT_NZ;REAL_OF_NUM_EQ;REAL_ARITH `(real_of_num 1) * x = x`]);
      (ONCE_REWRITE_TAC [Pm_lemma1.PDI_DEF]) THEN (SIMP_TAC [EL_POLY_DIFF]) THEN
      (ONCE_REWRITE_TAC [ARITH_RULE `i + (SUC k) = (SUC i) + k`]) THEN
      (ONCE_REWRITE_TAC [FACT]) THEN (ONCE_REWRITE_TAC [real_div]) THEN
      (SIMP_TAC [l13;real_div;REAL_MUL_ASSOC])
    ]
)
(* I think this should hold if we replace [--a;&1] with an arbitrary polynomial q,
 * however the existing ORDER* theorems would not be sufficient to prove it and
 * I don't feel like putting in the effort right now
 *)
let POLY_DIVIDES_POLY_DIFF = PROVE(
    `!p n a.
         (poly_divides (poly_exp [--a;&1] (SUC n)) p)
         ==> (poly_divides (poly_exp [--a;&1] n) (poly_diff p))`,
    let l0 = ARITH_RULE `op = SUC odp ==> SUC n <= op ==> n <= odp` in
    let l1 = ARITH_RULE `(SUC n <= m ) ==> ~(m = 0)` in
    MESON_TAC [l0;l1;POLY_DIFF_ZERO;ORDER_DIVIDES;ORDER_DIFF]
)
let POLY_DIVIDES_MUL = PROVE(
    `!p1 p2 p3.poly_divides p1 p2 ==> poly_divides p1 (p2 ** p3)`,
    (ONCE_REWRITE_TAC [divides]) THEN (REPEAT STRIP_TAC) THEN
    (EXISTS_TAC `q ** p3`) THEN
    (ASM_MESON_TAC [FUN_EQ_THM;POLY_MUL;POLY_MUL_ASSOC])
)
let POLY_DIVIDES_MUL3 = PROVE(
    `!p1 p2 p3.(poly_divides p1 p2) ==> (poly_divides p1 (p3 ** p2))`,
    (ONCE_REWRITE_TAC [divides]) THEN (REPEAT STRIP_TAC) THEN
    (EXISTS_TAC `p3 ** q`) THEN (UNDISCH_TAC `poly (p2) = poly (p1 ** q)`) THEN
    (ONCE_REWRITE_TAC [FUN_EQ_THM]) THEN (REWRITE_TAC [POLY_MUL]) THEN
    (MESON_TAC [REAL_MUL_ASSOC;REAL_MUL_SYM])
)
let POLY_DIVIDES_POLY_MUL_ITER = PROVE(
    `!f n v. 1 <= v ==> v <= n ==> poly_divides (f v) (poly_mul_iter f n)`,
    let l1 = ARITH_RULE `~(v <= n) ==> (v <= SUC n) ==> v = SUC n` in
    let l2 = UNDISCH (UNDISCH l1) in
    STRIP_TAC THEN INDUCT_TAC THENL
    [ ARITH_TAC;
      (ONCE_REWRITE_TAC [Pm_eqn5.POLY_MUL_ITER]) THEN STRIP_TAC THEN
      (ASM_CASES_TAC `v <= (n:num)`) THENL
      [ ASM_MESON_TAC [POLY_DIVIDES_MUL3];
        STRIP_TAC THEN STRIP_TAC THEN
        (MESON_TAC [l2;POLY_DIVIDES_MUL;POLY_DIVIDES_REFL]) ]
    ]
)
(*
 *  This one was suprisingly tricky to prove...
 *)
let POLY_DIVIDES_POLY_EXP2 = PROVE(
    `!n p1 p2.(poly_divides p1 p2) ==> poly_divides (poly_exp p1 n) (poly_exp p2 n)`,
    let t0 = `!p1 p2.
                (?q. poly p2 = poly (p1 ** q))
                ==> (?q. poly (poly_exp p2 n) = poly (poly_exp p1 n ** q))` in
    let l0 = ASSUME t0 in
    let l1 = UNDISCH (REWRITE_RULE [divides] (SPEC_ALL l0)) in
    let l3 = PROVE(
        `(x2 = x5 * x6 /\ x1 = x4 * x7) ==> (x1:real) * x2 = (x4 * x5) * x6 * x7`,
         MESON_TAC [REAL_MUL_SYM;REAL_MUL_ASSOC]) in
   (ONCE_REWRITE_TAC [divides]) THEN INDUCT_TAC THENL
   [ (MESON_TAC [divides;poly_exp;POLY_DIVIDES_REFL]);
     (STRIP_TAC THEN STRIP_TAC THEN DISCH_TAC) THEN (CHOOSE_TAC l1) THEN
     (UNDISCH_TAC `?q. poly p2 = poly (p1 ** q)`) THEN STRIP_TAC THEN
     (ONCE_REWRITE_TAC [poly_exp]) THEN (EXISTS_TAC `q ** q'`) THEN
     (REWRITE_TAC [poly_exp;FUN_EQ_THM;POLY_MUL]) THEN
     (ASM_MESON_TAC [l3;FUN_EQ_THM;POLY_MUL])
   ]
)
let POLY_EXP_ONE = PROVE(
    `!p .p = poly_exp p 1`,
    MESON_TAC [poly_exp;ARITH_RULE `1 = SUC 0`;POLY_MUL_RID]
)
let POLY_DIVIDES_ROOT = PROVE(
    `!p a.poly_divides [--a;&1] p ==> (poly p a) = &0`,
    MESON_TAC [ORDER_ROOT;ORDER_DIVIDES;POLY_EXP_ONE;
               ARITH_RULE `1 <= ord ==> ~(ord = 0)`]
)

let POLY_DIVIDES_PDI = PROVE(
    `!n p a.
         (poly_divides (poly_exp [--a;&1] (SUC n)) p)
         ==> (poly_divides [--a;&1] (poly_diff_iter p n))`,
    let t0 = `!p a.  poly_divides (poly_exp [--a; &1] (SUC n)) p
                     ==> poly_divides [--a; &1] (poly_diff_iter p n)` in
    let l0 = ASSUME t0 in
    let l1 = SPEC `poly_diff p` l0 in
    let l2 = SPECL [`p:(real)list`;`SUC n`;`a:real`] POLY_DIVIDES_POLY_DIFF in
    let l3 = UNDISCH l2 in
    let l4 = MATCH_MP l1 l3 in
    INDUCT_TAC THENL
    [ (SIMP_TAC [poly_exp;POLY_MUL_RID;Pm_lemma1.PDI_DEF]);
      (REPEAT STRIP_TAC) THEN (ASM_MESON_TAC [l4;Pm_lemma1.PDI_DEF;PDI_POLY_DIFF_COMM])
    ]
)
let POLY_DIVIDES_PDI2 = PROVE(
     `!n m p a.
          m > n
          ==> (poly_divides (poly_exp [--a;&1] m) p)
          ==> (poly_divides [--a;&1] (poly_diff_iter p n))`,
     MESON_TAC [POLY_EXP_DIVIDES;POLY_DIVIDES_PDI;
                ARITH_RULE `m > n <=> (SUC n) <= m`]
)
let TAIL_GUNNER = PROVE(
    ` x < p ==> 1 <= v ==> v <= n ==>
      poly (poly_diff_iter
           (poly_exp [&0; &1] (p - 1) **
            poly_exp (poly_mul_iter (\i. [-- &i; &1]) n) p)
          x)
          (&v)
       = &0 `,
     MESON_TAC [POLY_DIVIDES_ROOT; ARITH_RULE `x < p <=> (p:num) > x`;
                POLY_DIVIDES_PDI2; POLY_DIVIDES_MUL3; POLY_DIVIDES_POLY_EXP2;
                POLY_DIVIDES_POLY_MUL_ITER]
)

let IS_INT_POLY = PROVE(
    `!p x.(integer x) ==> (ALL integer p) ==> integer (poly p x)`,
    LIST_INDUCT_TAC THEN
    (ASM_MESON_TAC [N_IS_INT;ALL;poly;INTEGER_ADD;INTEGER_MUL])
)
(*  surprising the MESON needs so much help with the rewrites here
 *  (i.e. i though i could just hit it with ASM_MESON_TAC with all four thms
 *)
let INV_POLY_CMUL = PROVE(
    `!y x . (~(x = &0)) ==> (x) ## (inv x) ## y = y`,
    LIST_INDUCT_TAC THENL
    [ ASM_MESON_TAC [poly_cmul];
      (REPEAT STRIP_TAC) THEN
      (REWRITE_TAC [poly_cmul;REAL_MUL_ASSOC]) THEN
      (ASM_MESON_TAC [REAL_MUL_RINV;REAL_MUL_LID])
    ]
)
let INV_POLY_CMUL2 = PROVE(
    `!y x . (~(x = &0)) ==> (inv x) ## (x) ## y = y`,
    MESON_TAC [INV_POLY_CMUL;REAL_INV_INV;REAL_INV_EQ_0]
)
(* the final ASM_MESON_TAC fails if poly_cmul is rolled into the thm list *)
let POLY_CMUL_EQUALS = PROVE(
    `!z x y. (~(z = &0)) ==> ((x = y) <=> (z ## x = z ## y))`,
    (REPEAT STRIP_TAC) THEN EQ_TAC THENL
    [ (SIMP_TAC[]);
      (SPEC_TAC (`x:(real)list`,`x:(real)list`)) THEN
      (SPEC_TAC (`y:(real)list`,`y:(real)list`)) THEN
      (LIST_INDUCT_TAC) THENL
      [ LIST_INDUCT_TAC THENL
        [ (SIMP_TAC [POLY_CMUL_CLAUSES]);
          (ASM_MESON_TAC [POLY_CMUL_CLAUSES;NOT_CONS_NIL])];
        LIST_INDUCT_TAC THENL [
          (ASM_MESON_TAC [POLY_CMUL_CLAUSES;NOT_CONS_NIL]);
          (ONCE_REWRITE_TAC [poly_cmul]) THEN
          (ASM_MESON_TAC [REAL_EQ_LCANCEL_IMP;CONS_11])]
      ]
    ]
)
let PDI_LENGTH_THM = PROVE(
    `!f n. LENGTH(poly_diff_iter f n) = (LENGTH f) - n`,
    STRIP_TAC THEN INDUCT_TAC THENL
    [ (SIMP_TAC [Pm_lemma1.PDI_DEF;ARITH_RULE `(x:num) - 0 = x`]);
      (ONCE_REWRITE_TAC [Pm_lemma1.PDI_DEF]) THEN
      (ONCE_REWRITE_TAC [LENGTH_POLY_DIFF]) THEN ASM_ARITH_TAC ]
)
let CAPTAINS_CLOTHES = PROVE(
    `! k q.
     (ALL integer q) ==>
     ? r .(ALL integer r) /\ r = (inv (&(FACT k))) ## (poly_diff_iter q k)`
    ,
    let e0 = `(inv (&(FACT k))) ## (poly_diff_iter q k)` in
    let l1 = ONCE_REWRITE_RULE [GSYM (SPEC `inv (&(FACT k))` POLY_CMUL_LENGTH)]
                               PDI_COEFF_FACT in
    let l2 = UNDISCH (SPEC_ALL l1) in
    let l3 = PROVE(`i < LENGTH( inv (&(FACT k)) ## poly_diff_iter q k)
                     ==> (i + k) < LENGTH q`,
                    MESON_TAC [PDI_LENGTH_THM;POLY_CMUL_LENGTH;
                               ARITH_RULE `(i:num) < f -k ==> (i+k) < f`]) in
    (REPEAT STRIP_TAC) THEN (EXISTS_TAC e0) THEN (SIMP_TAC []) THEN
    (ASM_SIMP_TAC [ONCE_REWRITE_RULE [GSYM POLY_CMUL_LENGTH] POLY_CMUL_EL]) THEN
    (ONCE_REWRITE_TAC [GSYM ALL_EL]) THEN (REPEAT STRIP_TAC) THEN
    (ASM_SIMP_TAC [ONCE_REWRITE_RULE [GSYM POLY_CMUL_LENGTH] POLY_CMUL_EL]) THEN
    (ONCE_REWRITE_TAC [l2]) THEN (ONCE_REWRITE_TAC [REAL_MUL_ASSOC]) THEN
    (MATCH_MP_TAC INTEGER_MUL) THEN STRIP_TAC THENL
    [ (MESON_TAC [IS_INT_FACT_DIV_FACT_DIV_FACT;REAL_MUL_SYM;real_div;REAL_MUL_ASSOC]);
      (ASM_MESON_TAC  [l3;ALL_IMP_EL]) ]
)
let MESSY_JESSE2 = PROVE(
  `n > 0 ==> p > n ==>
     (? (Bs:num->num->real). ! v .
         (1 <= v) ==> (v <= n) ==>
         (    (! i . (integer (Bs v i)))
           /\ (poly (SOD (g n p)) (&v)) =
                 ((real_of_num 1) / (&(FACT (p - 1)))) *
                   (psum (0,LENGTH (g n p))
                      (\i. (&(FACT i)) * (Bs v i)))
           /\ (! i. (i < p) ==> (Bs v i) = &0)  ))`,
    let root_canal = REAL_ARITH `(x:real) * (&0) = &0` in
    let bs = `\(v:num) . \(x:num).
               if (x <= (LENGTH (g n p)) ) then
                    (poly
                       ((inv (&(FACT x))) ##
                        (poly_diff_iter
                        (poly_exp [&0; &1] (p - 1) **
                         poly_exp (poly_mul_iter (\i. [-- &i; &1]) n) p)
                        x))
                       (&v))
               else (&0)` in
    let l0 = PROVE(`ALL integer [&0;&1]`,MESON_TAC [ALL;N_IS_INT]) in
    let t0 = `(poly_exp [&0; &1] (p - 1) **
              poly_exp (poly_mul_iter (\i. [-- &i; &1]) n) p)` in
    let l2 = SPECL [`i:num`;t0] CAPTAINS_CLOTHES in
    let l3 = PROVE(`ALL integer (poly_exp [&0; &1] (p - 1) ** poly_exp (poly_mul_iter (\i. [-- &i; &1]) n) p)`,MESON_TAC[l0;ALL_IS_INT_POLY_MUL;ALL_IS_INT_POLY_EXP;ALL_IS_INT_POLY_MUL_ITER]) in
    let l4 = MP l2 l3 in
    let l7 = ONCE_REWRITE_RULE [GSYM REAL_OF_NUM_EQ] FACT_NZ in
    let l8 = (SIMP_RULE [l7]) (SPEC `(&(FACT i)):real` POLY_CMUL_EQUALS) in
    (* these are not true for x =0, however we only use it for x= &(FACT i) *)
    let l10_0 = SPECL [`y:(real)list`;`(real_of_num (FACT i))`] INV_POLY_CMUL in
    let l12_0 = SPECL [`y:(real)list`;`(real_of_num (FACT i))`] INV_POLY_CMUL2 in
    let l10 = SIMP_RULE [REAL_FACT_NZ] l10_0 in
    let l12 = SIMP_RULE [REAL_FACT_NZ] l12_0 in
    let l9 = ONCE_REWRITE_RULE [l8] l4 in
    let l11 = GSYM (ONCE_REWRITE_RULE [l10] l9) in
    let l133 = PROVE(`
      (psum (0,m) (\i.(x i) * (if i <= m then (y i) else c))) =
      (psum (0,m) (\i.(x i) * (y i)))`,
      MESON_TAC [SUM_EQ;ARITH_RULE `(0 <= i /\ i < (m:num) + 0) ==> i <= m`]) in
    let l18 = MATCH_MP REAL_MUL_RINV (SPEC `i:num` l7) in
    let lass2 = SPECL [`g n p`;`x:real`;`v:real`] Pm_lemma2.PLANETMATH_LEMMA_2_B in
    let lass3 = BETA_RULE lass2 in
    let lass4 = CONV_RULE (RAND_CONV (RAND_CONV (REWRITE_CONV [Pm_eqn5.PLANETMATH_EQN_5]))) lass3 in
    let lass5 = REWRITE_RULE [POLY_CMUL;POLY_CMUL_PDI] lass4 in
    let lass6 = CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV [GSYM (ISPEC `f:num->real` ETA_AX)])) (SPEC_ALL SUM_CMUL) in
    let lass7 = ONCE_REWRITE_RULE [GSYM REAL_MUL_ASSOC] lass5 in
    let lass8 = REWRITE_RULE [lass6] lass7 in
    let lass10 = ONCE_REWRITE_RULE [REAL_MUL_DIV_ASSOC] lass8 in
    let lass11 =  ONCE_REWRITE_RULE [real_div] lass10 in
    let lass12 = REAL_ARITH `((w:real) * x * y) * z = w * x * y * z` in
    let lass13 = ONCE_REWRITE_RULE [lass12] lass11 in
    let lass14 = REWRITE_RULE [lass6] lass13 in
    let MUL_ONE = REAL_ARITH `! x.(&1) * x = x /\ x * (&1) = x` in
    let lass15 = SIMP_RULE [REAL_MUL_LINV;REAL_FACT_NZ;MUL_ONE] lass14 in
    STRIP_TAC THEN STRIP_TAC THEN (EXISTS_TAC bs) THEN (REPEAT STRIP_TAC) THENL
    [
      (BETA_TAC THEN BETA_TAC) THEN (ASM_CASES_TAC `(i <= LENGTH (g n p))`) THENL
      [ (ASM_SIMP_TAC[]) THEN (ASM_CASES_TAC `((i:num) < p)`) THENL
        [ (ASM_MESON_TAC [POLY_CMUL;TAIL_GUNNER;
                          N_IS_INT;REAL_ARITH `(x:real) * (&0) = &0`]);
          (ASSUME_TAC (UNDISCH (ARITH_RULE `~(i < (p:num)) ==> (p <= i)`))) THEN
          (CHOOSE_TAC l11) THEN
          (SPLIT_CONJOINED_ASSUMPT_TAC (snd (dest_exists (concl l11)))) THEN
          (ASM_REWRITE_TAC[l12]) THEN
          (ASM_MESON_TAC [N_IS_INT;IS_INT_POLY])
        ];
        (ASM_MESON_TAC [N_IS_INT])
      ];
      (BETA_TAC) THEN (SIMP_TAC [l133]) THEN
      (SIMP_TAC [POLY_CMUL;l18;REAL_MUL_ASSOC;REAL_MUL_LID]) THEN
      (SIMP_TAC [lass15;REAL_INV_1OVER]);
      BETA_TAC THEN (ASM_MESON_TAC [TAIL_GUNNER;POLY_CMUL;root_canal])
    ]
)
let INTEGER_PSUM = PROVE(
    `!f m.(! i . i < m ==> integer (f i)) ==> (integer (psum (0,m) f))`,
    let l0 = ASSUME `!i. i < SUC m ==> integer (f i)` in
    let l1 = SPEC `m:num` l0 in
    let l2 = SIMP_RULE [ARITH_RULE `m < SUC m`] l1 in
    STRIP_TAC THEN INDUCT_TAC THENL
    [ (MESON_TAC [sum;int_of_num;int_of_num_th;N_IS_INT]);
      (SIMP_TAC [sum;ARITH_RULE `0 + (x:num) = x`]) THEN
      (STRIP_TAC) THEN (MATCH_MP_TAC INTEGER_ADD) THEN
      (ASM_MESON_TAC[l2;ARITH_RULE `(i:num) < m ==> i < SUC m`])
    ]
)
let INT_DIVIDES_PSUM = PROVE(
    `!f m p.(! i . i < m ==>
             ((integer (f i)) /\ (int_divides p (int_of_real (f i)))))
                ==> (int_divides p (int_of_real (psum (0,m) f)))`,
    let l0 = ASSUME `!i. i < SUC m ==> integer (f i) /\ p divides int_of_real (f i)` in
    let l1 = SPEC `m:num` l0 in
    let l2 = SIMP_RULE [ARITH_RULE `m < SUC m`] l1 in
    let l3 = ASSUME `(!i. i < m ==> integer (f i)) ==> integer (psum (0,m) f)` in
    let l4 = SPEC `i:num` l0 in
    let l5 = DISCH `i < SUC m` ((CONJUNCT1 (UNDISCH l4))) in
    let l8 = PROVE(`(!i.i < SUC m
                         ==> (integer (f i))) ==> (!i.i < m ==> (integer (f i)))`,
                   MESON_TAC [ARITH_RULE `i < m ==> i < SUC m`]) in
    let ll1 = MP l8 (GEN_ALL l5) in
    let ll2 = MP l3 ll1 in
    let ll3 = MATCH_MP INT_OF_REAL_ADD (CONJ ll2 (CONJUNCT1 l2))  in
    STRIP_TAC THEN INDUCT_TAC THENL
    [ (MESON_TAC [sum;int_of_num;int_of_num_th;INT_DIVIDES_0]);
      (SIMP_TAC [sum;ARITH_RULE `0 + (x:num) = x`]) THEN
      (ASSUME_TAC (SPECL [`f:num->real`;`m:num`] INTEGER_PSUM)) THEN
      (STRIP_TAC) THEN
      (STRIP_TAC) THEN
      (ONCE_REWRITE_TAC [ll3]) THEN
      (MATCH_MP_TAC INT_DIVIDES_ADD) THEN
      (CONJ_TAC) THENL
      [ (ASM_MESON_TAC [ARITH_RULE `i < m ==> i < SUC m`]);
        (ASM_MESON_TAC [ARITH_RULE `m < SUC m`])
      ]
    ]
)
let PLANET_MATH_beta = PROVE(
    `p > n ==>
     n > 0 ==>
     (! v.
       (1 <= v /\ v <= n) ==>
       (   (integer (poly (SOD (g n p )) (&v)))
        /\ ((&p) divides (int_of_real (poly (SOD (g n p )) (&v))))
       )
     )`,
    let l2 = GSYM (ONCE_REWRITE_RULE [REAL_MUL_SYM] real_div) in
    let ll3 = ARITH_RULE `(int_of_num p) * &0 = &0` in
    let l7 = UNDISCH (SPECL [`i:num`;`p:num`] IS_INT_FACT_DIV) in
    let l11 = PROVE(`p > 0 ==> FACT p = p * (FACT (p-1))`,
                    MESON_TAC [FACT; ARITH_RULE `p > 0 ==> SUC (p -1) = p `]) in
    let l12 = UNDISCH (UNDISCH (ARITH_RULE `(p:num) > n ==> n > 0 ==> p > 0`)) in
    let l13 = MP l11 l12 in
    let t9 =
      `1 <= (v:num) ==>
       v <= (n:num) ==>
       (!v. 1 <= v
              ==> v <= n
              ==> (!i. integer (Bs v i)) /\
                  poly (SOD (g n p)) (&v) =
                  &1 / &(FACT (p - 1)) *
                  psum (0,LENGTH (g n p)) (\i. &(FACT i) * Bs v i) /\
                  (!i. i < p ==> Bs v i = &0)) ==>
        (integer (Bs v i))` in
    let lll0 = UNDISCH (UNDISCH (UNDISCH (PROVE(t9,MESON_TAC[])))) in
    let l8 = REWRITE_RULE [l13;real_div;REAL_INV_MUL] l7 in
    let l9 = REWRITE_RULE [N_IS_INT;GSYM REAL_OF_NUM_MUL] l8 in
    let l10 = REWRITE_RULE [REAL_INV_MUL] l9 in
    let l11 = MATCH_MP (INTEGER_MUL) (CONJ l10 lll0) in
    let l12 = MATCH_MP INT_OF_REAL_MUL (CONJ (SPEC `p:num` N_IS_INT) l11) in
    let l15 = GSYM l12 in
    let lll8 = ARITH_RULE `p > n ==> n > 0 ==> ~(p = 0)` in
    let lll9 = ONCE_REWRITE_RULE [GSYM REAL_OF_NUM_EQ] lll8 in
    let lll10 = UNDISCH (UNDISCH lll9) in

    let sc1 = PROVE (`(~((x:real) = &0)) ==> (x * y * inv x) = y`,
                      MESON_TAC [REAL_MUL_RID;REAL_MUL_ASSOC;
                                 REAL_MUL_SYM;REAL_MUL_LINV;REAL_MUL_LID]) in
    let sc2 = PROVE (`(~((x:real) = &0)) ==> (x * y * (inv x) * z) = y * z`,
                      MESON_TAC [sc1;REAL_MUL_ASSOC]) in
    (REPEAT STRIP_TAC) THENL
      [ (CHOOSE_TAC (UNDISCH (UNDISCH MESSY_JESSE2))) THEN
        (ASM_SIMP_TAC []) THEN
        (ONCE_REWRITE_TAC [GSYM SUM_CMUL]) THEN
        (MATCH_MP_TAC INTEGER_PSUM) THEN
        (REPEAT STRIP_TAC) THEN
        BETA_TAC THEN
        (ASM_CASES_TAC `i < (p:num)`) THENL
        [ (ASM_SIMP_TAC [N_IS_INT;REAL_ARITH `(x:real) * (&0) = &0`]);
          (ASSUME_TAC (UNDISCH (ARITH_RULE `(~((i:num) < p)) ==> i >= p-1`))) THEN
          (ASM_MESON_TAC [REAL_INV_1OVER;REAL_MUL_ASSOC;
                          IS_INT_FACT_DIV; l2;INTEGER_MUL])
        ];
        (CHOOSE_TAC (UNDISCH (UNDISCH MESSY_JESSE2))) THEN
        (ASM_SIMP_TAC []) THEN
        (ONCE_REWRITE_TAC [GSYM SUM_CMUL]) THEN
        (MATCH_MP_TAC INT_DIVIDES_PSUM) THEN
        (REPEAT STRIP_TAC) THENL
        [ BETA_TAC THEN
          (ASM_CASES_TAC `i < (p:num)`) THENL
          [ (ASM_SIMP_TAC [N_IS_INT;REAL_ARITH `(x:real) * (&0) = &0`]);
            (ASSUME_TAC (UNDISCH (ARITH_RULE `(~((i:num) < p)) ==> i >= p-1`))) THEN
            (ASM_MESON_TAC [REAL_INV_1OVER;REAL_MUL_ASSOC;
                            IS_INT_FACT_DIV; l2;INTEGER_MUL])
          ];
          (ONCE_REWRITE_TAC [int_divides]) THEN BETA_TAC THEN
          (ASM_CASES_TAC `i < (p:num)`) THENL
          [ (ASM_SIMP_TAC [N_IS_INT;REAL_ARITH `(x:real) * (&0) = &0`]) THEN
            (EXISTS_TAC `int_of_num 0`) THEN
            (MESON_TAC [ll3;int_of_num_th;int_of_num]);
            (ASSUME_TAC (UNDISCH (ARITH_RULE `(~((i:num) < p)) ==> i >= p`))) THEN
            (EXISTS_TAC `int_of_real (((&(FACT i))/(&(FACT p))) * (Bs (v:num) i))`) THEN
            (ONCE_REWRITE_TAC [int_of_num]) THEN
            (ONCE_REWRITE_TAC [l13]) THEN
            (ONCE_REWRITE_TAC [N_IS_INT;GSYM REAL_OF_NUM_MUL]) THEN
            (SIMP_TAC [ real_div]) THEN
            (ONCE_REWRITE_TAC [ REAL_INV_MUL]) THEN
            (ONCE_REWRITE_TAC [ REAL_MUL_LID]) THEN
            (ONCE_REWRITE_TAC [l15]) THEN
            (ASSUME_TAC lll10) THEN
            (ONCE_REWRITE_TAC [REAL_MUL_ASSOC]) THEN
            (ASM_MESON_TAC [sc2;REAL_MUL_SYM])
          ]
        ]
      ]
)

let JUNE_LEMMA = PROVE(
    `n > 0 ==> p > n ==> v <= n ==> integer (poly (SOD (g n p)) (&v))`,
    let lem0 = CONJUNCT1 (UNDISCH_ALL PLANET_MATH_alpha) in
    let lem1 = UNDISCH_ALL (SPEC_ALL (UNDISCH_ALL PLANET_MATH_beta)) in
    let lem2 = DISCH `1 <= v /\ v <= n` (CONJUNCT1 lem1) in
    let lem3 = SPEC `SUC v` (GEN `v:num` lem2) in
    let lem4 = SIMP_RULE [ARITH_RULE `1 <= SUC v`] lem3 in
    (STRIP_TAC THEN STRIP_TAC) THEN
    (SPEC_TAC (`v:num`,`v:num`)) THEN
    (INDUCT_TAC THENL [(SIMP_TAC [lem0]);(ACCEPT_TAC lem4)])
)
let DIVIDES_SUM_NOT_ZERO = PROVE(
    `!(x:int) (y:int) (z:int).
         (~(z divides x)) /\  (z divides y) ==> ~(x + y = &0)`,
    let l0 = ASSUME `(x:int) + y = &0` in
    let l1 = ONCE_REWRITE_RULE [ARITH_RULE `((x:int) + y = &0) <=> (x = --y)`] l0 in
    (REPEAT STRIP_TAC) THEN (UNDISCH_TAC `~((z:int) divides x)`) THEN
    (REWRITE_TAC [l1]) THEN (UNDISCH_TAC `((z:int) divides y)`) THEN
    (INTEGER_TAC)
)
let NUM_OF_INT_ABS = PROVE(
    `!(x:num) (y:int).num_of_int (abs y)  = x <=> abs y = &x`,
(* stupid... *)
    let j0 = UNDISCH (PROVE(`(num_of_int (abs y) = x) ==> x = num_of_int (abs y)`,MESON_TAC [])) in
    let j1 = ARITH_RULE `&0 <= ((abs y):int)` in
    let j2 = MATCH_MP INT_OF_NUM_OF_INT j1 in
    (REPEAT STRIP_TAC) THEN EQ_TAC THENL
    [ (STRIP_TAC THEN SIMP_TAC [j0;j2]);
      (ASM_SIMP_TAC [NUM_OF_INT_OF_NUM])]
)
let INT_DIVIDES_IMP_ABS_NUM_DIVIDES = PROVE(
    `! (x:int) (y:num).
       (x divides (&y)) ==> ((num_of_int (abs x)) divides y)`,
    let w0 = ARITH_RULE `((&0):int) <= abs x` in
    let w1 = fst (EQ_IMP_RULE (SPEC `abs (x:int)` NUM_OF_INT)) in
    let w2 = MP w1 w0 in
    let w3 = ARITH_RULE `((&0):int) <= x ==> abs x = x` in
    let w4 = ARITH_RULE `(~(((&0):int) <= x)) ==> abs x = -- x` in
    (REWRITE_TAC [int_divides;num_divides]) THEN
    (REPEAT STRIP_TAC) THEN (ASM_REWRITE_TAC [w2]) THEN
    (ASM_CASES_TAC `((&0):int) <= x`) THENL
    [ (ONCE_REWRITE_TAC [UNDISCH w3]) THEN
      (EXISTS_TAC `x':int`) THEN (REFL_TAC);
      (ONCE_REWRITE_TAC [UNDISCH w4]) THEN
      (EXISTS_TAC `--x':int`) THEN (ARITH_TAC)
    ]
)
let INT_PRIME_NUM_PRIME = PROVE(
    `!p. int_prime (&p) <=> prime p`,
    (ONCE_REWRITE_TAC [int_prime;prime]) THEN
    (MESON_TAC [divides;num_divides;
                INT_ABS;INT_POS;INT_OF_NUM_EQ;INT_LT_IMP_NE;INT_GT;
                ARITH_RULE `2 <= p ==> abs((&p):int) > &1`;
                INT_DIVIDES_IMP_ABS_NUM_DIVIDES;NUM_OF_INT_ABS;PRIME_GE_2;
                prime;int_prime ])
)

let DIVIDES_INT_OF_REAL_ADD = PROVE(
         `!x y p.integer x /\
                 integer y /\
                 p divides (int_of_real x) /\
                 p divides (int_of_real y)
                 ==> p divides (int_of_real (x + y))`,
         SIMP_TAC [INT_OF_REAL_ADD;INT_DIVIDES_ADD]
)
let ITCHY_LEMMA = PROVE(
    `! f p n.
       (!v.1<= v /\ v <=  n ==>
        integer (f v) /\
        &p divides int_of_real (f v)) ==>
        (&p divides int_of_real (sum (1..n) f))`,
    let l0 = fst (EQ_IMP_RULE (SPECL [`1`;`0`] (GSYM NUMSEG_EMPTY))) in
    let l1 = INTEGER_RULE `&p divides ((&0))` in
    let l2 = SPEC `0` (GEN_ALL int_of_num) in
    let l3 = ONCE_REWRITE_RULE [l2] l1 in
    let l4 = SPECL [`f:num->real`;`n:num`;`1`] IS_INT_SUM in
    let l5 = PROVE(`(!v. 1 <= v /\ v <= SUC n ==> integer (f v)) ==> (!i. 1 <= i /\ i <= n ==> integer (f i))`,MESON_TAC [ARITH_RULE `v <= n ==> v <= SUC n`]) in
    let l6 = IMP_TRANS l5 l4 in
    let l7 = PROVE(`(!v. 1 <= v /\ v <= SUC n ==> (integer (f v)) /\  (&p) divides int_of_real (f v)) ==> (&p) divides int_of_real (f (SUC n))`,MESON_TAC [ARITH_RULE `1 <= (SUC n) /\ SUC n <= SUC n`]) in
    let l9 = PROVE(`(!v. 1 <= v /\ v <= SUC n ==> integer (f v)) ==> integer (f (SUC n))`,MESON_TAC [ARITH_RULE `1 <= SUC n /\ SUC n <= SUC n`]) in
    let tm = `\(v:num).integer (f v) /\ (&p) divides int_of_real (f v)` in
    let l10 = BETA_RULE (SPEC tm SHRIVER) in
    let l11 = UNDISCH (SPEC `1` (GEN `m:num` l10)) in
     STRIP_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
     [ SIMP_TAC  [ARITH_RULE `0 < 1`;l0;SUM_CLAUSES;l3];
       DISCH_TAC THEN
       (SIMP_TAC [SUM_CLAUSES_NUMSEG;ARITH_RULE `1 <= SUC n`]) THEN
       (MATCH_MP_TAC DIVIDES_INT_OF_REAL_ADD) THEN (CONJ_TAC) THENL
       [ ASM_SIMP_TAC [l6];
         CONJ_TAC THENL
         [ ASM_SIMP_TAC [l9];
           CONJ_TAC THENL
           [ ASM_SIMP_TAC [l11];
             ASM_SIMP_TAC [l7] ]]]]
)
let GOTTA_DO_DISHES_LEMMA = PROVE(
    `!(x:real) (y:real).
       (integer x) /\ (integer y) ==>
       (?(z:int).(~(z divides (int_of_real x)))
           /\ (z divides (int_of_real y)))
       ==> ~(x + y = &0)`,
    let mk_lemma x y =
        let lem0 = SPECL [x;y;`z:int`] DIVIDES_SUM_NOT_ZERO in
        let lem1 = TAUT `(X /\ Y ==> Z) <=> (X ==> Y ==> Z)` in
        UNDISCH (UNDISCH (ONCE_REWRITE_RULE [lem1] lem0))
    in
    let mk_tac x y =
        (ASM_REWRITE_TAC [GSYM int_of_num;INT_OF_REAL_NEG_INT_OF_NUM]) THEN
        (STRIP_TAC) THEN
        (REWRITE_TAC [GSYM int_neg_th;GSYM int_eq; GSYM int_add_th;GSYM int_of_num_th]) THEN
        (ACCEPT_TAC (mk_lemma  x y))
    in
    (ONCE_REWRITE_TAC [is_int]) THEN
    (STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC ) THENL
    [ mk_tac `(&n):int` `(&n'):int` ;
      mk_tac `(&n):int` `--(&n'):int` ;
      mk_tac `--(&n):int` `(&n'):int` ;
      mk_tac `--(&n):int` `--(&n'):int`
     ]
)

let RAINY_DAY = PROVE(
    `! p x y.
       prime p ==>
       (&p) > x ==>
       integer x ==>
       x > (&0) ==>
       integer y ==>
       (((&p) divides (int_of_real (x * y)))
        <=> ((&p) divides int_of_real y))`,
    let ss3 = SPECL [`int_of_num n`;`(&p):int`] INT_PRIME_COPRIME_LT in
    let ss4 = ONCE_REWRITE_RULE [ARITH_RULE `abs ((&x):int) = &x`] ss3 in
    let ss40 = PROVE(`!(x:num) (y:num).  (int_of_num x) < (int_of_num y) <=> (real_of_num x) < (real_of_num y)`,SIMP_TAC [INT_OF_NUM_LT;REAL_OF_NUM_LT]) in
    let ss5 = ONCE_REWRITE_RULE [ss40;INT_COPRIME_SYM;INT_PRIME_NUM_PRIME] ss4 in
    let ss6 = SPECL [`(&p):int`;`(&n):int`;`int_of_real y`] INT_COPRIME_DIVPROD in
    let ss7 = ONCE_REWRITE_RULE [TAUT `(X /\ Y ==> Z) <=> (Y ==> X ==> Z)`] ss6 in
    let ss8 = IMP_TRANS ss5 ss7 in
    let ss9 = ONCE_REWRITE_RULE [TAUT `(A /\ B /\ C ==> D ==> E) <=> (A ==> B ==> C ==> D ==> E)`] ss8 in
    let ss10 = UNDISCH ss9 in
    (REPEAT STRIP_TAC) THEN (ASM_SIMP_TAC [INT_OF_REAL_MUL]) THEN
    (EQ_TAC) THENL
    [ (SIMP_TAC [INT_DIVIDES_LMUL]) THEN
      (UNDISCH_TAC `integer x`) THEN
      (ONCE_REWRITE_TAC [is_int]) THEN
      (STRIP_TAC) THENL
      [ (ASM_REWRITE_TAC[]) THEN
        (ONCE_REWRITE_TAC [GSYM int_of_num]) THEN
        (UNDISCH_TAC `(&(p:num)) > (x:real)`) THEN
        (UNDISCH_TAC `(x:real) > &0`) THEN
        (ASM_REWRITE_TAC []) THEN
        (ONCE_REWRITE_TAC [REAL_ARITH `(y:real) > z <=> z < y`]) THEN
        (ACCEPT_TAC ss10);
        (ASM_ARITH_TAC)
      ];
      (SIMP_TAC [INT_DIVIDES_LMUL])
    ]
)
let PLANET_MATH_gamma = PROVE(
    `n > 0 ==>
     p > n ==>
     prime p ==>
     &p > (EL 0 c) ==>
     (EL 0 c) > (&0) ==>
     n = PRE (LENGTH (c)) ==>
     (ALL integer c) ==>
     ( (integer (LHS c (g n p))) /\ ~((LHS c (g n p)) = &0))`,
     let lemma01 = SPECL [`\i. EL i c * poly (SOD (g n p)) (&i)`;`n:num`;`k:num` ] IS_INT_SUM in
     let lemma02 = BETA_RULE lemma01 in
     let lemma021 = UNDISCH JUNE_LEMMA in
     let lemma022 = UNDISCH_ALL (ARITH_RULE `n > 0 ==> p > n ==> p > 1`) in
     let lemma023 = DISCH_ALL (SIMP_RULE [lemma022] lemma021) in
     let lemma04 = UNDISCH (UNDISCH lemma023) in
     let lemma08 = ISPECL [`c:(real)list`;`v:num`;`integer`] ALL_IMP_EL in
     let lemma09 = ADD_ASSUM `n > 0` (UNDISCH lemma08) in
     let lemma10 = ADD_ASSUM `n = PRE (LENGTH (c:(real)list))` lemma09 in
     let lemma11 = ARITH_RULE `n > 0 ==> (n = PRE (LENGTH (c:(real)list))) ==> ((v < LENGTH c) <=> (v <= n))` in
     let lemma12 = UNDISCH (UNDISCH lemma11) in
     let lemma13 = ONCE_REWRITE_RULE [lemma12] lemma10 in
     let lemma15 = CONJ (UNDISCH (UNDISCH lemma04)) (UNDISCH lemma13) in
     let lemma16 = MATCH_MP INTEGER_MUL (ONCE_REWRITE_RULE [CONJ_SYM] lemma15) in
     let lemma17 = DISCH `v <= (n:num)` lemma16 in
     let lemma18 = ADD_ASSUM_DISCH `k <= (v:num)` lemma17 in
     let lemma19 = ONCE_REWRITE_RULE [TAUT `(X ==> Y ==> Z) <=> ((X /\ Y) ==> Z)`] lemma18 in
     let lemma20 = GEN `v:num` lemma19 in
     let lemma21 = GEN `k:num` (MATCH_MP lemma02 lemma20) in
     let lemma29 = SPEC `0` lemma21 in
     let lemma30 = GSYM (ASSUME `n = PRE (LENGTH (c:(real)list))`) in
     let lemma300 = SPECL [`f:(num -> real)`;`0`;`PRE (LENGTH (c:(real)list))`] SUM_CLAUSES_LEFT in
     let lemma31 = ADD_ASSUM `n > 0` (ADD_ASSUM `n = PRE (LENGTH (c:(real)list))` lemma300) in
     let lemma32 = MP lemma31 (ARITH_RULE `0 <= PRE (LENGTH (c:(real)list))`) in
     let lemma0000 = BRW `(X ==> Y ==> Z) <=> ((X /\ Y) ==> Z)` GOTTA_DO_DISHES_LEMMA in
     let lemmaa00 = UNDISCH PLANET_MATH_alpha in
     let lemmaa03 = ARITH_RULE `n >0 ==> ((n = PRE (LENGTH (c:(real)list))) ==> 0 < (LENGTH c))` in
     let lemmaa04 = ISPECL [`c:(real)list`;`0`;`integer`] ALL_IMP_EL in
     let lemmaa05 = MP (UNDISCH lemmaa04) (UNDISCH (UNDISCH lemmaa03))  in
     let c1 = ARITH_RULE `n > 0 ==> n = PRE (LENGTH (c:(real)list)) ==> 0 < (LENGTH (c:(real)list))` in
     let c2 = UNDISCH (UNDISCH c1) in
     let c3 = MP (UNDISCH lemmaa04) c2 in
     let c4 = CONJUNCT1 (UNDISCH (UNDISCH (UNDISCH PLANET_MATH_alpha))) in
     let c40 = CONJUNCT2 (UNDISCH (UNDISCH (UNDISCH PLANET_MATH_alpha))) in
     let c5 = SPECL [`p:num`;`(EL 0 c):real`;`poly (SOD (g n p)) (&0)`] RAINY_DAY in
     let c7 = ((UNDISCH (UNDISCH c5))) in
     let c8 = SIMP_RULE [c3] c7 in
     let c9 = UNDISCH c8 in
     let c10 = SIMP_RULE [c4] c9 in
     let d0 = UNDISCH PLANET_MATH_beta in
     let d1 = BRW `(X ==> Y ==> Z) <=> (Y ==> X ==> Z)` d0 in
     let d2 = SIMP_RULE [UNDISCH (ARITH_RULE `p > (n:num) ==> n > 0 ==> p > 1`)] d1 in
     let d3 = UNDISCH d2 in
     let d8 = CONJUNCT2 (UNDISCH (SPEC_ALL d3)) in
     let d9 = SPECL [`(&p):int`;`int_of_real (EL v c)`;`int_of_real (poly (SOD (g n p)) (&v))`] INT_DIVIDES_LMUL in
     let d10 = ADD_ASSUM `ALL integer c` d9 in
     let d11 = ADD_ASSUM `n = PRE (LENGTH (c:(real)list))` d10 in
     let d12 = ADD_ASSUM `1 <= v /\ v <= n` d11 in
     let d13 = CONJUNCT1 (UNDISCH (SPEC_ALL d3)) in
     let d14 = DISCH `1 <= v` (ADD_ASSUM `1 <= v` lemma13) in
     let d15 = BRW `(X ==> Y ==> Z) <=> (X /\ Y ==> Z)` d14 in
     let d16 = UNDISCH d15 in
     let d17 = CONJ d16 d13 in
     let d18 = GSYM (MATCH_MP INT_OF_REAL_MUL d17) in
     let d19 = ONCE_REWRITE_RULE [d18] d12 in
     let d20 = MP d19 d8 in
     let d21 = UNDISCH (SPECL [`1`;`v:num`] (GEN `k:num` lemma20)) in
     let d22 = CONJ d21 d20 in
     let d23 = DISCH `1 <=v /\ v <= n` d22 in
     let d24 = GEN `v:num` d23 in
     let d25 = MATCH_MP ITCHY_LEMMA d24 in
     ((REPEAT STRIP_TAC) THENL
      [ (ONCE_REWRITE_TAC [Pm_eqn4.LHS]) THEN (SIMP_TAC [lemma30;lemma29]);
        (UNDISCH_TAC `LHS c (g n p) = &0`) THEN
        (REWRITE_TAC [Pm_eqn4.LHS]) THEN
        (SIMP_TAC [lemma32;ARITH_RULE `0 + 1 = 1`]) THEN
        (ONCE_REWRITE_TAC [lemma30]) THEN
        (MATCH_MP_TAC lemma0000) THEN
        (CONJ_TAC) THENL
        [ (CONJ_TAC) THENL
          [ (MATCH_MP_TAC INTEGER_MUL) THEN (ASM_SIMP_TAC [lemmaa00;lemmaa05]);
            (ACCEPT_TAC (SPEC `1` lemma21))
          ];
          (EXISTS_TAC `(&p):int`) THEN (CONJ_TAC) THENL
          [(ONCE_REWRITE_TAC [c10]) THEN (ASM_SIMP_TAC [c40]);
           (ACCEPT_TAC d25)
          ]
        ]
      ] )
)
end;;
```

### Informal statement
This theorem states that for any natural number $n$, the real number $\&n$ (real_of_num $n$) is an integer.

Formally: 
$$\forall n \in \mathbb{N}. \text{integer}(\&n)$$

### Informal proof
The proof follows directly from the definition of an integer as implemented in HOL Light. The `is_int` predicate defines what it means to be an integer, and applying this to a natural number converted to a real number satisfies the integer condition. The proof is completed using MESON_TAC with the `is_int` definition.

### Mathematical insight
This theorem establishes a fundamental relationship between natural numbers and integers in the HOL Light type system. While HOL Light represents reals as a separate type from integers and naturals, this theorem confirms that real values obtained by converting natural numbers (via `&n` or `real_of_num n`) are integers according to the `integer` predicate.

The theorem is used extensively in proving properties about arithmetic operations involving real numbers that are actually integers. It serves as a bridge between the natural numbers and the reals, allowing for the application of integer properties to real number expressions that represent integers.

### Dependencies
- `is_int`: Definition of what it means for a real number to be an integer

### Porting notes
When porting this to other systems, note that:
- Different proof assistants have different type structures for numbers
- In systems with a distinct integer type (like Lean), this relationship might be established through coercions or explicit conversion functions
- The equivalent theorem would state that applying the natural-to-real conversion preserves the "integerness" property

In Lean, a similar statement might look like: `∀ n : ℕ, ∃ m : ℤ, ↑n = ↑m` with appropriate coercions.

Most formal systems need to establish this or similar relationships between their numeric types to enable smooth reasoning about arithmetic.

---

## IS_INT_NZ_ABS_GE_1

### IS_INT_NZ_ABS_GE_1

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let IS_INT_NZ_ABS_GE_1 = PROVE (
    `!x. ((integer x) /\ ~(x = &0)) ==> ~(abs x < &1)`,
    let lemmy0 = REAL_ARITH `(x:real) < y <=> ~(y <= x)` in
    let lemmy1 = ONCE_REWRITE_RULE [lemmy0] REAL_NZ_IMP_LT in
    let lemmy2 = REAL_ARITH `(real_neg x) = &0 <=> x = &0` in
    let lemmy3 = REAL_ARITH `&0 <= (real_neg x) <=> x <= &0` in
    (ONCE_REWRITE_TAC [is_int]) THEN
    (ONCE_REWRITE_TAC [TAUT `(X /\ Y ==> Z) <=> (X ==> Y ==> Z)`]) THEN
    (STRIP_TAC) THEN (STRIP_TAC) THENL
    [ (ASM_REWRITE_TAC[]) THEN (SIMP_TAC [REAL_ABS_NUM] ) THEN
      (ONCE_REWRITE_TAC [REAL_OF_NUM_LT;REAL_OF_NUM_EQ]) THEN
      (ARITH_TAC);
      (ASM_REWRITE_TAC[]) THEN (ONCE_REWRITE_TAC [real_abs]) THEN
      (ONCE_REWRITE_TAC [lemmy2;lemmy3]) THEN
      (ONCE_REWRITE_TAC [REAL_OF_NUM_EQ]) THEN
      (SIMP_TAC [lemmy1;REAL_NEG_NEG]) THEN
      (ONCE_REWRITE_TAC [REAL_OF_NUM_LT]) THEN (ARITH_TAC)
    ]
)
let PBR_LEMMA = PROVE(
    `!n1 n2 n3 p. p > MAX n1 (MAX n2 n3) ==> (p > n1 /\ p > n2 /\ p > n3)`,
    (REWRITE_TAC [MAX]) THEN ARITH_TAC

)
let BIGGER_PRIME_EXISTS = PROVE(
  `!(n:num). ?p. prime p /\ p > n`,
   let lem0 = PROVE(`{x | prime x} = prime`,SET_TAC[]) in
   let lem1 = ARITH_RULE `p > n <=> ~(p <= (n:num))` in
   MESON_TAC [PRIMES_INFINITE;lem0;lem1;IN_ELIM_THM;num_FINITE;INFINITE]
)
let BUD_LEMMA = PROVE(
    `!(f:num->bool) (n1:num) (n2:num).((?(N:num) . !(p:num).p > N ==> f p)
      ==> (? (p0:num).prime p0 /\ p0 > n1 /\ p0 > n2 /\ f p0))`,
    let amigo3 = SPECL [`N:num`;`n1:num`;`n2:num`;`p:num`] PBR_LEMMA in
    let amigo4 = UNDISCH amigo3  in
    (REPEAT STRIP_TAC) THEN
    (CHOOSE_TAC (SPEC  `MAX N (MAX n1 n2)` BIGGER_PRIME_EXISTS )) THEN
    (EXISTS_TAC `p:num`) THEN
    (UNDISCH_TAC `prime p /\ p > MAX N (MAX n1 n2)`) THEN
    (ONCE_REWRITE_TAC [TAUT `(X /\ Y ==> Z) <=> (X ==> Y ==> Z)`]) THEN
    (DISCH_TAC THEN DISCH_TAC) THEN
    (ASM_SIMP_TAC [amigo4])
)

let ALL_IMP_EL = PROVE(
    `! (l:(a)list) i P. (ALL P l) ==> (i < LENGTH l) ==> P (EL i l)`,
    SIMP_TAC[GSYM ALL_EL]
)

let HAMMS_LEMMA = PROVE(
     `~(?c. ALL integer c /\
            LENGTH c > 1 /\
            EL 0 c > &0 /\
            (!f. LHS c f = RHS c f))`,
     let erica0  = UNDISCH_ALL Pm_eqn4_lhs.PLANET_MATH_gamma in
     let erica1  = MATCH_MP IS_INT_NZ_ABS_GE_1 erica0  in
     let erica2  = ASM_REWRITE_RULE [] erica1 in
     let erica3 = SPEC_ALL Pm_eqn4_rhs.LT_ONE in
     let erica4 = MATCH_MP BUD_LEMMA erica3 in
     let erica5 = ADD_ASSUM `ALL integer c` erica4 in
     let erica8 = ARITH_RULE `(n = PRE (LENGTH (c:(real)list))) ==> n > 0 ==>
     0 < (LENGTH c) ` in
     let erica9 = UNDISCH (UNDISCH erica8) in
     let erica10 = UNDISCH (ISPECL [`c:(real)list`;`0`;`integer`] ALL_IMP_EL) in
     let erica11 = MP erica10 erica9 in
     let erica12 = ONCE_REWRITE_RULE [is_int] erica11 in
     let erica13 = ARITH_RULE `!n. ~(( -- (real_of_num n)) > &0)` in
     let erica14 = PROVE(
         `n = PRE (LENGTH c) ==>
          n > 0 ==>
          ALL integer c ==>
          (EL 0 c) > &0 ==>
          ?n. EL 0 c = &n`,
          MESON_TAC [DISCH_ALL erica12;erica13]
     ) in
     let erica15 = UNDISCH_ALL erica14 in
     let sim0 = SELECT_RULE (ASSUME (concl erica15)) in
     let sim1 = DISCH (concl erica15) sim0 in
     let sim2 = MP sim1 erica15 in
     let erica18 = SPECL [`n:num`;`@n. EL 0 c = (real_of_num n)`] erica5 in
     let erica19 = ONCE_REWRITE_RULE [GSYM REAL_OF_NUM_GT] erica18 in
     let erica20 =  ONCE_REWRITE_RULE [GSYM sim2] erica19 in
     let erica21 =  ONCE_REWRITE_RULE [REAL_OF_NUM_GT] erica20 in
     let erica22 = DISCH `(real_of_num p) > EL 0 c` erica2 in
     let erica23 = DISCH `(p:num) > n` erica22 in
     let erica24 = DISCH `prime (p:num)` erica23 in
     let erica25 = GEN `p:num` erica24 in
     let erica28 = UNDISCH (ARITH_RULE `n = PRE (LENGTH (c:(real)list)) ==> ((n > 0) <=> (LENGTH c) > 1)`) in
     let erica29 = UNDISCH (ONCE_REWRITE_RULE [erica28] (DISCH `n > 0` (erica25))) in
     let erica30 = UNDISCH (ONCE_REWRITE_RULE [erica28] (DISCH `n > 0` (erica21))) in
      (CONV_TAC NNF_CONV) THEN
      (REPEAT STRIP_TAC) THEN
      (ASM_MESON_TAC [DISCH_ALL erica29;DISCH_ALL erica30])
)

let TRANSCENDENTAL_E = PROVE(
    `transcendental (exp (&1))`,
    MESON_TAC [HAMMS_LEMMA;Pm_eqn4.PLANETMATH_EQN_4]
)

end;;
```

### Informal statement
For any real number $x$, if $x$ is an integer and $x \neq 0$, then $|x| \geq 1$.

More precisely: For any real number $x$, if $x$ is an integer and $x \neq 0$, then it is not the case that $|x| < 1$.

### Informal proof
The proof distinguishes two cases: positive integers and negative integers.

* First case: $x$ is a positive integer (numeral).
  - If $x$ is a positive integer, then $x = n$ for some natural number $n > 0$.
  - For positive integers, the absolute value is the number itself: $|x| = x = n$.
  - Since $n > 0$ and $n$ is a natural number, we have $n \geq 1$.
  - Therefore, $|x| = n \geq 1$, which means $|x| < 1$ is false.

* Second case: $x$ is a negative integer.
  - If $x$ is a negative integer, then $x = -n$ for some natural number $n > 0$.
  - For negative numbers, the absolute value is the negation: $|x| = |-n| = n$.
  - Since $n > 0$ and $n$ is a natural number, we have $n \geq 1$.
  - Therefore, $|x| = n \geq 1$, which means $|x| < 1$ is false.

In both cases, we conclude that $|x| \geq 1$ when $x$ is a non-zero integer.

### Mathematical insight
This is a basic property of integers: any non-zero integer has an absolute value of at least 1. The result is important because it establishes a lower bound for the absolute value of non-zero integers, which is useful in many contexts, particularly in number theory and analysis.

This theorem is used in proofs related to transcendental numbers (as seen in the dependencies and subsequent theorems in the file), where it helps establish that certain expressions involving integers cannot be arbitrarily small.

### Dependencies
- `is_int` - Definition of an integer
- `REAL_ABS_NUM` - Theorem about absolute value of natural numbers
- `REAL_NZ_IMP_LT` - Theorem stating that if a natural number is non-zero, then its real representation is positive
- `REAL_NEG_NEG` - Theorem stating the double negation of a real number equals the original number

### Porting notes
- When implementing this in other systems, keep in mind the representation of integers as reals (in HOL Light, `&n` converts a natural number to a real).
- The proof relies on case analysis for positive and negative integers, which should transfer straightforwardly to other systems.
- The theorem is stated in a negated form (`~(abs x < &1)` rather than `&1 <= abs x`), which might be worth restating in a more direct form in other systems.

---

