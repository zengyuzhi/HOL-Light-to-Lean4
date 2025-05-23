# ramsey.ml

## Overview

Number of statements: 186

The file `ramsey.ml` presents a formalization of the Infinite Ramsey's Theorem in HOL Light, ported from an earlier HOL88 proof from 1994. This theorem is a significant result in combinatorial mathematics, which states that for any coloring of the edges of a complete infinite graph, there must exist an infinite complete subgraph whose edges are all the same color. The file likely contains definitions of graphs, colorings, and the formal statement and proof of Ramsey's theorem, maintaining compatibility with HOL88 constructs.

## is_neg_imp

### is_neg_imp

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let is_neg_imp tm =
  is_neg tm || is_imp tm;;
```

### Informal statement
This function determines whether a term `tm` is either a negation or an implication. It returns `true` if the term is either a negation (identified by `is_neg tm`) or an implication (identified by `is_imp tm`), and `false` otherwise.

Formally:
```
is_neg_imp(tm) = is_neg(tm) ∨ is_imp(tm)
```

### Informal proof
This is a definition, not a theorem, so it does not have a proof. The function simply performs a logical OR operation between the results of two predicate functions: `is_neg` which checks if the term is a negation, and `is_imp` which checks if the term is an implication.

### Mathematical insight
This function serves as a utility for recognizing terms that are either negations or implications, which is common when manipulating logical formulas syntactically. In formal logic and theorem proving, it's often necessary to identify specific syntactic structures for transformations, simplifications, or other operations.

The definition is part of the infrastructure for the proof of Infinite Ramsey's Theorem, as mentioned in the comment. Being able to identify specific syntactic forms is crucial in automated theorem proving to apply appropriate transformation rules or tactics.

### Dependencies
#### Definitions
- `is_neg` - Function that checks if a term is a negation
- `is_imp` - Function that checks if a term is an implication

### Porting notes
When porting to another system:
- Ensure the target system has equivalent functionality to identify negations and implications in terms/expressions
- The implementation might differ based on how terms are represented in the target system
- This is a simple utility function that should be straightforward to implement in most proof assistants

---

## dest_neg_imp

### dest_neg_imp

### Type of the formal statement
- This is a function definition in HOL Light's ML code (not a theorem or formal definition within the HOL Light logic itself).

### Formal Content
```ocaml
let dest_neg_imp tm =
  try dest_imp tm with Failure _ ->
  try (dest_neg tm,mk_const("F",[]))
  with Failure _ -> failwith "dest_neg_imp";;
```

### Informal statement
This function `dest_neg_imp` takes a term `tm` and attempts to decompose it in one of two ways:

1. First, it tries to decompose `tm` as an implication using `dest_imp`, which would return a pair of the antecedent and consequent if `tm` has the form `p ⟹ q`.

2. If that fails, it tries to decompose `tm` as a negation using `dest_neg`. If successful, it returns a pair consisting of the negated term and the constant `F` (representing falsehood). This effectively treats `¬p` as equivalent to `p ⟹ F`.

3. If both attempts fail, it raises a "dest_neg_imp" failure exception.

### Informal proof
This is a function definition rather than a theorem, so it doesn't have a formal proof. The function performs the following operations:

- It first attempts to use `dest_imp tm` to decompose `tm` as an implication.
- If that fails (catches a `Failure` exception), it attempts to use `dest_neg tm` to decompose `tm` as a negation.
- If the second attempt succeeds, it returns a pair of the negated term and the falsehood constant (`F`).
- If both attempts fail, it raises a "dest_neg_imp" failure exception.

### Mathematical insight
This utility function implements the logical equivalence between negation and implication: `¬p` is equivalent to `p ⟹ false`. This equivalence is fundamental in classical logic.

The function is used in HOL Light for processing terms that might be either explicit implications or negations (which can be viewed as implications to falsehood). It provides a uniform way to handle both forms, which is useful in many theorem-proving contexts where these forms need to be treated similarly.

### Dependencies
- `dest_imp`: A function that destruct an implication term into its antecedent and consequent
- `dest_neg`: A function that destructs a negation term into the negated subterm
- `mk_const`: A function that creates constants in the HOL Light term language

### Porting notes
When porting to other systems:
- This is a utility function for term manipulation in the meta-language, not a formal definition within the logic.
- Most proof assistants have similar facilities for analyzing the structure of terms.
- The exception handling mechanism might need adaptation depending on the target language.
- The equivalent functions for destructing implications and negations in the target system should be used.

---

## PROVE

### PROVE
- `PROVE`

### Type of the formal statement
- Definition

### Formal Content
```ocaml
let PROVE = prove;;
```

### Informal statement
`PROVE` is an alias for the `prove` function in HOL Light. It serves as a debugging function that helps in proving theorems. The function `prove` takes a term and a tactic as inputs and attempts to prove the term using the given tactic.

### Informal proof
There is no formal proof for this definition as it is a simple alias or binding of the existing `prove` function.

### Mathematical insight
This definition is a utility function used in the HOL Light system for interactive theorem proving. It allows users to apply tactics to prove theorems. By setting `PROVE = prove`, it provides a convenient shorthand or alias for the `prove` function, which is a fundamental part of the HOL Light infrastructure for constructing proofs.

In interactive theorem proving, the process typically involves stating a goal (a term to be proven) and then applying tactics (proof strategies) to transform the goal into simpler subgoals until they can be resolved using basic axioms or previously proven theorems.

### Dependencies
- This definition depends on the core HOL Light function `prove`, which is a primitive proof function in the system.

### Porting notes
When porting to another proof assistant:
- This is a simple utility binding rather than a mathematical result.
- Most proof assistants have similar functionality, though the exact interface may differ.
- In Lean, this would correspond to the `by` tactic or other tactical frameworks.
- In Isabelle, it would be similar to the `apply` proof method.
- In Coq, it would be similar to various proof tactics.

---

## prove_thm((s:string),g,t)

### prove_thm

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let prove_thm((s:string),g,t) = prove(g,t);;
```

### Informal statement
The function `prove_thm` takes a triple as input where:
- `s` is a string (the name of the theorem)
- `g` is a goal (the statement to be proven)
- `t` is a tactic (the proof procedure)

It calls the `prove` function with the goal `g` and tactic `t`, effectively proving the goal while ignoring the theorem name provided in `s`.

### Informal proof
This is a function definition, not a theorem, so it does not have a proof. The function simply calls the existing `prove` function with the goal and tactic components of the input triple, discarding the string name component.

### Mathematical insight
The `prove_thm` function is a wrapper around the `prove` function that allows specification of a theorem name alongside the goal and proof tactic. However, in this implementation the name is actually ignored and not used. This suggests it might be a simplified version of a more complete function that would normally register the proven theorem under the given name in a theorem database.

In proof assistant systems, it's common to have functions that both prove theorems and register them with names. This function appears to be part of such a mechanism, though in a minimal form where the naming aspect is not fully implemented.

### Dependencies
- `prove`: The core function that proves a goal using a given tactic

### Porting notes
When porting this to another system, consider whether the target system already has built-in mechanisms for naming theorems during proof. Most modern proof assistants have more sophisticated theorem registration systems than this simple wrapper suggests.

---

## (CONV_OF_RCONV:

### CONV_OF_RCONV
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- Let-binding (function definition)

### Formal Content
```ocaml
let (CONV_OF_RCONV: conv -> conv) =
  let rec get_bv tm =
    if is_abs tm then bndvar tm
    else if is_comb tm then try get_bv (rand tm) with Failure _ -> get_bv (rator tm)
    else failwith "" in
  fun conv tm ->
  let v = get_bv tm in
  let th1 = conv tm in
  let th2 = ONCE_DEPTH_CONV (GEN_ALPHA_CONV v) (rhs(concl th1)) in
  TRANS th1 th2;;
```

### Informal statement
The `CONV_OF_RCONV` is a higher-order function that converts a conversion (`conv`) into another conversion. In HOL Light, a conversion is a function that maps a term to a theorem establishing the equality of that term with another term.

Given a conversion `conv`, `CONV_OF_RCONV conv` applies `conv` to a term `tm`, then performs alpha-conversion on the right-hand side of the resulting theorem to ensure that bound variables match a specific variable `v` extracted from the original term. It returns the transitive composition of these two theorems.

More specifically, it:
1. Extracts a bound variable `v` from the input term `tm` using a recursive helper function `get_bv`
2. Applies the input conversion `conv` to `tm` to get theorem `th1`
3. Performs alpha-conversion on the right-hand side of `th1` using `v` to get theorem `th2`
4. Returns the transitive composition of `th1` and `th2`

### Informal proof
This is a function definition rather than a theorem, so there is no proof. The implementation works as follows:

- First, it defines a recursive helper function `get_bv` that extracts a bound variable from a term:
  - If the term is an abstraction (`is_abs tm`), it returns the bound variable of that abstraction
  - If the term is a combination (`is_comb tm`), it tries to extract a bound variable from the argument first, otherwise from the operator
  - Otherwise, it fails

- The main function takes a conversion `conv` and returns a new conversion that:
  1. Extracts a bound variable `v` from the input term `tm` using `get_bv`
  2. Applies `conv` to `tm` to get a theorem `th1`
  3. Uses `ONCE_DEPTH_CONV (GEN_ALPHA_CONV v)` to perform alpha-conversion on the right-hand side of `th1`, ensuring bound variables match `v`
  4. Returns the transitive composition of `th1` and `th2` using `TRANS`

### Mathematical insight
This function is part of HOL Light's quantifier movement conversions. It's designed to ensure consistent naming of bound variables after applying a conversion.

When manipulating terms with bound variables (like quantifiers or lambda abstractions), it's important to maintain consistent variable naming to avoid variable capture issues. This function helps ensure that after applying a conversion, the resulting term uses the same bound variable names as the original term.

This is particularly useful in the context of quantifier movement, where transformations on formulas with quantifiers need to carefully manage bound variable names to preserve the logical meaning.

### Dependencies
- **Conversions and operations**:
  - `TRANS`: Transitivity of equality
  - `ONCE_DEPTH_CONV`: Applies a conversion once at the deepest possible position
  - `GEN_ALPHA_CONV`: Performs alpha-conversion (renaming bound variables)

### Porting notes
When porting this to another proof assistant:
1. You'll need equivalent functionality for:
   - Identifying bound variables in terms
   - Alpha-conversion (renaming bound variables)
   - Composing equality theorems transitively
   
2. Be aware that different systems handle variable binding and alpha-equivalence differently:
   - Some systems (like Coq and Lean) use de Bruijn indices internally
   - Others have different naming conventions for variables
   
3. The error handling in `get_bv` uses HOL Light's exception mechanism - you'll need to adapt this to the target system's error handling approach.

---

## (CONV_OF_THM:

### Name of formal statement
CONV_OF_THM

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let (CONV_OF_THM: thm -> conv) =
  CONV_OF_RCONV o REWR_CONV;;
```

### Informal statement
`CONV_OF_THM` is a function that takes a theorem `thm` and returns a conversion function (`conv`). It does this by composing `CONV_OF_RCONV` with `REWR_CONV` applied to the theorem.

In mathematical terms, if we have a theorem establishing an equality $t_1 = t_2$, this function creates a conversion that, when applied to a term matching $t_1$, rewrites it to $t_2$.

### Informal proof
This is a definition that composes two existing functions:
1. `REWR_CONV thm` creates a rewrite conversion based on the theorem `thm`
2. `CONV_OF_RCONV` converts this rewrite conversion to a regular conversion

The composition `CONV_OF_RCONV o REWR_CONV` thus takes a theorem as input and returns a conversion that applies the rewriting specified by that theorem.

### Mathematical insight
This utility function provides a convenient way to turn theorems stating equalities into conversions that can be used in term manipulation. It bridges the gap between the declarative world of theorems and the procedural world of conversions (functions that transform terms).

In the HOL Light framework, conversions are fundamental tools for term manipulation. This function allows theorems to be seamlessly integrated into the conversion machinery, enabling proved equalities to be directly used in term rewriting.

### Dependencies
- `CONV_OF_RCONV`: Converts a rewrite conversion to a regular conversion
- `REWR_CONV`: Creates a rewrite conversion from a theorem

### Porting notes
When porting to other proof assistants:
- Most proof assistants have similar concepts of rewrite rules and conversion functions, though terminology may differ
- Check if the target system has built-in functions that accomplish the same goal, as this is a utility function rather than a core mathematical definition

---

## (X_FUN_EQ_CONV:term->conv)

### X_FUN_EQ_CONV

### Type of the formal statement
- new_definition (converter function)

### Formal Content
```ocaml
let (X_FUN_EQ_CONV:term->conv) =
  fun v -> (REWR_CONV FUN_EQ_THM) THENC GEN_ALPHA_CONV v;;
```

### Informal statement
`X_FUN_EQ_CONV` is a conversion function that takes a term `v` and returns a conversion that:
1. First applies the rewriting conversion using the function equality theorem `FUN_EQ_THM`
2. Then applies the alpha conversion `GEN_ALPHA_CONV` with the provided variable `v`

This conversion is used to handle function equality expressions by first rewriting them using the standard function extensionality principle and then performing alpha conversion with respect to a specific variable.

### Informal proof
As this is a definition rather than a theorem, there is no proof to translate. The function is defined as a composition of two conversions:
1. `REWR_CONV FUN_EQ_THM` - applies the function extensionality theorem
2. `GEN_ALPHA_CONV v` - performs alpha conversion with respect to the variable `v`

The composition is achieved using the `THENC` operator, which sequences conversions.

### Mathematical insight
This conversion implements function extensionality with variable renaming control. The function extensionality principle states that two functions are equal if they produce the same outputs for all inputs. The `FUN_EQ_THM` theorem formalizes this principle in HOL Light.

The key insight is that when working with function equality, it's often necessary to:
1. First convert the equality of functions `f = g` to the extensional form `∀x. f x = g x`
2. Then ensure the bound variable `x` is chosen appropriately to avoid variable capture issues

This conversion handles both steps in a single operation, allowing for controlled application of function extensionality.

### Dependencies
- Theorems:
  - `FUN_EQ_THM` - The function extensionality theorem

- Conversions:
  - `REWR_CONV` - Rewriting conversion
  - `GEN_ALPHA_CONV` - Alpha conversion for quantified terms
  - `THENC` - Conversion sequencing operator

### Porting notes
When porting to other proof assistants:
- Ensure the target system has an equivalent function extensionality theorem
- Handle variable renaming carefully to avoid capture issues
- Consider how the target system sequences conversions or tactics
- In systems with dependent types (like Lean or Coq), function extensionality might not be a theorem but an axiom or derived from other principles

---

## (FUN_EQ_CONV:conv)

### FUN_EQ_CONV

### Type of the formal statement
- conv (conversion function)

### Formal Content
```ocaml
let (FUN_EQ_CONV:conv) =
  fun tm ->
    let vars = frees tm in
    let op,[ty1;ty2] = dest_type(type_of (lhs tm)) in
    if op = "fun"
       then let varnm =
                if (is_vartype ty1) then "x" else
                   hd(explode(fst(dest_type ty1))) in
            let x = variant vars (mk_var(varnm,ty1)) in
            X_FUN_EQ_CONV x tm
       else failwith "FUN_EQ_CONV";;
```

### Informal statement
This is a conversion function that proves the extensional equality of two functions. Given a term of the form `f = g` where `f` and `g` are functions of type `α -> β`, it returns a theorem stating that the equality holds if and only if `∀x. f(x) = g(x)`.

The conversion works by:
1. Determining the domain type `α` of the functions
2. Creating a fresh variable of type `α`
3. Applying the `X_FUN_EQ_CONV` conversion with this variable

If the input term is not an equality between functions, the conversion fails with the message "FUN_EQ_CONV".

### Informal proof
This is a conversion function implementation, not a theorem with a proof. The implementation:

- Takes a term `tm` representing a function equality
- Extracts free variables from the term to avoid variable capture
- Determines the type of the left-hand side of the equality
- Checks if the type is a function type (`α -> β`)
- If it is a function type:
  - Creates a suitable variable name based on the domain type
  - Creates a fresh variable of the domain type (avoiding name collisions with existing free variables)
  - Applies the `X_FUN_EQ_CONV` conversion with this variable
- If the input is not a function equality, fails with an error message

### Mathematical insight
The conversion implements function extensionality, which is a fundamental principle in mathematics and type theory. It states that two functions are equal if and only if they yield the same outputs for all possible inputs.

This conversion automates the process of converting between the intensional equality of functions (as abstract objects) and their extensional equality (equality of outputs for all inputs). This is particularly useful in higher-order theorem proving, where reasoning about function equality is common.

The implementation is designed to be robust against variable capture by carefully selecting fresh variable names.

### Dependencies
- `X_FUN_EQ_CONV`: The core conversion that actually proves the extensional equality for a given variable

### Porting notes
When porting to another system:
- Ensure the target system has a way to represent and handle conversions (functions that transform theorems)
- Check how function extensionality is handled in the target system - some systems may have it built-in or require explicit axioms
- Pay attention to how variable capture is avoided in the target system
- The equivalent functionality might already exist in the target system under a different name (e.g., in Lean it might be part of the extensionality tactics)

---

## (SINGLE_DEPTH_CONV:conv->conv)

### SINGLE_DEPTH_CONV

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let (SINGLE_DEPTH_CONV:conv->conv) =
  let rec SINGLE_DEPTH_CONV conv tm =
    try conv tm with Failure _ ->
    (SUB_CONV (SINGLE_DEPTH_CONV conv) THENC (TRY_CONV conv)) tm in
  SINGLE_DEPTH_CONV;;
```

### Informal statement
This is a conversion (`conv`) combinator that applies the given conversion `conv` at a single depth in the term structure. Specifically, `SINGLE_DEPTH_CONV conv tm` will:
1. First attempt to apply `conv` directly to `tm`
2. If that fails, it recursively applies `SINGLE_DEPTH_CONV conv` to all immediate subterms of `tm`, and then tries to apply `conv` to the resulting term.

### Informal proof
This is a recursive function definition, not a theorem with a proof. The implementation works as follows:

- First, it attempts to apply the given conversion `conv` directly to the term `tm`
- If that fails (caught by the `try...with Failure` construct), it:
  - Applies `SINGLE_DEPTH_CONV conv` recursively to all immediate subterms of `tm` using `SUB_CONV`
  - Then attempts to apply `conv` to the resulting term using `TRY_CONV` (which will not fail even if `conv` fails)
  - These two steps are combined using the `THENC` operator, which sequences conversions

### Mathematical insight
`SINGLE_DEPTH_CONV` provides a way to apply a conversion at a controlled depth in the term structure. Unlike `DEPTH_CONV` which will try to apply a conversion repeatedly at all levels until it can't be applied anymore, `SINGLE_DEPTH_CONV` is more restrained and applies the conversion at most once at each level.

This controlled approach is useful when you want to transform terms in a more predictable way, particularly:
- When you want to apply a conversion at a specific depth but not deeper
- When you want to avoid infinite recursion that might occur with more aggressive conversions
- When you want finer control over the transformation process

### Dependencies
- `SUB_CONV`: Applies a conversion to all immediate subterms
- `THENC`: Sequences two conversions
- `TRY_CONV`: Attempts to apply a conversion, returning the identity if it fails

### Porting notes
When porting this to other systems:
- Ensure proper handling of exceptions/failure cases
- Consider how the target system implements conversions and recursive operations on terms
- Be aware of potential performance considerations when recursively traversing term structures

---

## (SKOLEM_CONV:conv)

### SKOLEM_CONV
- SKOLEM_CONV

### Type of the formal statement
- conversion function

### Formal Content
```ocaml
let (SKOLEM_CONV:conv) =
  SINGLE_DEPTH_CONV (REWR_CONV SKOLEM_THM);;
```

### Informal statement
SKOLEM_CONV is a conversion function that applies Skolemization to a formula once at the top level. Specifically, it replaces a formula of the form $\forall y. \exists x. P[x,y]$ with $\exists f. \forall y. P[f(y),y]$, introducing a Skolem function $f$ that depends on the universally quantified variable $y$.

### Informal proof
The implementation is straightforward:
- SKOLEM_CONV applies SINGLE_DEPTH_CONV to a rewrite conversion that uses SKOLEM_THM
- SINGLE_DEPTH_CONV ensures the transformation is applied exactly once at the top level
- SKOLEM_THM is the theorem that establishes the equivalence between $\forall y. \exists x. P[x,y]$ and $\exists f. \forall y. P[f(y),y]$

This conversion effectively performs a single step of Skolemization on the input formula.

### Mathematical insight
Skolemization is a fundamental transformation in automated theorem proving and logic. It eliminates existential quantifiers in favor of Skolem functions, which depend on the universally quantified variables that precede the existential quantifier. 

The key insight is that if we know $\forall y. \exists x. P[x,y]$, then for each value of $y$, we can choose some $x$ that makes $P[x,y]$ true. This choice can be represented by a function $f$ such that $P[f(y),y]$ is true for all $y$. 

This transformation preserves satisfiability and is particularly useful in resolution-based theorem proving and when converting formulas to forms like conjunctive normal form.

### Dependencies
- **Theorems:**
  - `SKOLEM_THM`: The theorem that establishes the equivalence between $\forall y. \exists x. P[x,y]$ and $\exists f. \forall y. P[f(y),y]$
- **Conversion Functions:**
  - `SINGLE_DEPTH_CONV`: Applies a conversion exactly once at the top level
  - `REWR_CONV`: Creates a conversion from a rewrite theorem

### Porting notes
When porting this to other proof assistants, note that some systems might:
1. Have built-in Skolemization tactics or functions, making a direct port unnecessary
2. Handle variable dependencies differently - ensure the Skolem function correctly depends on all universal variables
3. Require explicit function types to be provided for the Skolem function
4. Need additional handling for type constraints or polymorphic functions depending on the type system

For implementations with dependent types (like Coq or Lean), you might need to consider how to appropriately represent the choice function axioms.

---

## (X_SKOLEM_CONV:term->conv)

### X_SKOLEM_CONV
- X_SKOLEM_CONV

### Type of the formal statement
- Definition (function)

### Formal Content
```ocaml
let (X_SKOLEM_CONV:term->conv) =
  fun v -> SKOLEM_CONV THENC GEN_ALPHA_CONV v;;
```

### Informal statement
This defines a conversion function `X_SKOLEM_CONV` that takes a term `v` and applies two conversions in sequence:
1. First applies `SKOLEM_CONV`, which performs Skolemization on quantified formulas
2. Then applies `GEN_ALPHA_CONV v`, which performs alpha-conversion (renaming of bound variables) with respect to the variable `v`

The type signature `term->conv` indicates that `X_SKOLEM_CONV` takes a term as input and returns a conversion function.

### Informal proof
This is a definition rather than a theorem, so there is no proof. The definition combines two existing conversion functions using the `THENC` operator, which composes conversions sequentially.

### Mathematical insight
`X_SKOLEM_CONV` is designed to process quantified formulas by first Skolemizing them (converting existential quantifiers to functions that satisfy the existential claim) and then performing variable renaming to avoid potential name conflicts with respect to the variable `v`.

This conversion is useful in theorem proving when manipulating formulas with quantifiers, particularly when:
1. You need to eliminate existential quantifiers by introducing Skolem functions
2. You want to ensure that variable names are properly managed to avoid capture issues

The composition of Skolemization with alpha-conversion helps ensure that the resulting terms have clean variable bindings that don't interfere with the variable `v`, which might be important in the context where this conversion is applied.

### Dependencies
- **Conversions**: `SKOLEM_CONV`, `GEN_ALPHA_CONV`, `THENC`

### Porting notes
When implementing this in other proof assistants:
- Ensure the target system has equivalents for Skolemization and alpha-conversion
- Be aware of how the system handles variable capture and renaming
- Note that some systems might have more integrated approaches to handling quantifiers that don't require explicit Skolemization and alpha-conversion steps

---

## EXISTS_UNIQUE_CONV

### Name of formal statement
EXISTS_UNIQUE_CONV

### Type of the formal statement
Conversion function

### Formal Content
```ocaml
let EXISTS_UNIQUE_CONV tm =
  let v = bndvar(rand tm) in
  let th1 = REWR_CONV EXISTS_UNIQUE_THM tm in
  let tm1 = rhs(concl th1) in
  let vars = frees tm1 in
  let v = variant vars v in
  let v' = variant (v::vars) v in
  let th2 =
   (LAND_CONV(GEN_ALPHA_CONV v) THENC
    RAND_CONV(BINDER_CONV(GEN_ALPHA_CONV v') THENC
              GEN_ALPHA_CONV v)) tm1 in
  TRANS th1 th2;;
```

### Informal statement
`EXISTS_UNIQUE_CONV` is a conversion function that transforms a term of the form `∃! x. P[x]` (exists unique) into a more explicit form using standard quantifiers:

`∃x. P[x] ∧ ∀y. P[y] ⇒ (y = x)`

This makes the uniqueness assertion explicit by using universal and existential quantifiers together with an equality.

### Informal proof
The implementation works as follows:

1. Extract the bound variable `v` from the term.
2. Apply the `EXISTS_UNIQUE_THM` rewrite theorem to transform the exists-unique statement into the standard form.
3. Extract the resulting right-hand side term.
4. Get all free variables in this term to avoid variable capture.
5. Generate two fresh variants of `v` that don't clash with existing variables.
6. Apply a series of alpha-conversions to rename bound variables:
   - First, rename the bound variable in the left part (the existential quantifier)
   - Then, rename both bound variables in the right part (the universal quantifier)
   - Finally, rename the outermost bound variable
7. Create the final theorem by transitivity from the original rewrite and the alpha-conversions.

The conversion ensures that bound variables are properly renamed to avoid capture and maintain the logical meaning of the original statement.

### Mathematical insight
This conversion implements the standard way of expressing uniqueness quantification in terms of basic logical quantifiers. The statement "there exists a unique x such that P(x)" is logically equivalent to "there exists an x such that P(x), and for any y, if P(y) then y equals x."

The conversion is useful for proof automation and term manipulation, as it reduces a specialized quantifier to more basic logical constructs. This allows theorem provers to work with exists-unique statements using standard quantifier reasoning rules.

The careful handling of variable names through alpha-conversion is essential to maintain logical correctness when transforming quantified expressions.

### Dependencies
No specific theorems or definitions were listed in the dependencies, but the implementation uses:
- `EXISTS_UNIQUE_THM`: The theorem that states the logical equivalence between "exists unique" and its expanded form
- Various conversion combinators like `LAND_CONV`, `RAND_CONV`, `BINDER_CONV` for structuring the term transformations
- `GEN_ALPHA_CONV` for alpha-converting bound variables to avoid capture
- `TRANS` for transitivity of equality to combine conversions

### Porting notes
When porting to other systems:
1. Ensure the target system has an equivalent theorem for `EXISTS_UNIQUE_THM`.
2. Check how the target system handles variable capture and alpha-conversion - this is a key aspect of this conversion.
3. Many systems have built-in handling for exists-unique quantifiers, so this conversion might not be needed or might be implemented differently.
4. The conversion combinators like `LAND_CONV` (applies conversion to left side of binary operator) might have different names or implementations in other systems.

---

## NOT_FORALL_CONV

### Name of formal statement
NOT_FORALL_CONV

### Type of the formal statement
Conversion function

### Formal Content
```ocaml
let NOT_FORALL_CONV = CONV_OF_THM NOT_FORALL_THM;;
```

### Informal statement
`NOT_FORALL_CONV` is a conversion function that transforms a negated universal quantification into an existential quantification with a negated body.

Specifically, it converts formulas of the form $\neg(\forall x. P(x))$ to $\exists x. \neg P(x)$.

### Informal proof
`NOT_FORALL_CONV` is defined as a conversion function created from the theorem `NOT_FORALL_THM` using the `CONV_OF_THM` function.

The conversion applies the logical equivalence between:
- $\neg(\forall x. P(x))$
- $\exists x. \neg P(x)$

When applied to a term matching the pattern $\neg(\forall x. P(x))$, it returns a theorem asserting the equality between this term and $\exists x. \neg P(x)$.

### Mathematical insight
This conversion implements a fundamental logical equivalence from first-order logic. The negation of a universal statement "not everything has property P" is equivalent to the existential statement "there exists something that does not have property P."

This conversion is useful for normalization of formulas and for certain proof techniques where it's advantageous to eliminate negated universal quantifiers.

### Dependencies
- `NOT_FORALL_THM`: Theorem asserting the equivalence between $\neg(\forall x. P(x))$ and $\exists x. \neg P(x)$
- `CONV_OF_THM`: Function that converts a theorem stating an equality into a conversion function

### Porting notes
When porting to other proof assistants:
- Check if the target system already has a built-in tactic or conversion for this transformation
- Ensure the system has a theorem equivalent to `NOT_FORALL_THM`
- If creating a similar conversion, understand how the target system handles conversions or rewriting

---

## NOT_EXISTS_CONV

### NOT_EXISTS_CONV

### Type of the formal statement
- Definition/converter

### Formal Content
```ocaml
let NOT_EXISTS_CONV = CONV_OF_THM NOT_EXISTS_THM;;
```

### Informal statement
This is a conversion function that transforms a term of the form `~(∃x. P[x])` into the equivalent form `∀x. ~P[x]`, using the theorem `NOT_EXISTS_THM` as its basis.

### Informal proof
This is not a theorem but a definition that creates a converter using `CONV_OF_THM` applied to the theorem `NOT_EXISTS_THM`. The `CONV_OF_THM` function converts a theorem of the form `⊢ s = t` into a conversion function that, when applied to a term matching the pattern of `s`, returns the theorem `⊢ s = t` instantiated appropriately.

In this case, `NOT_EXISTS_THM` is the theorem asserting `⊢ (~(∃x. P[x])) = (∀x. ~P[x])`. When `NOT_EXISTS_CONV` is applied to a term of the form `~(∃x. P[x])`, it returns the theorem stating that this term is equal to `∀x. ~P[x]`.

### Mathematical insight
This conversion implements the logical equivalence between "it's not the case that there exists an x such that P(x)" and "for all x, P(x) is not true." This is a fundamental first-order logic equivalence known as one of De Morgan's laws for quantifiers.

The converter provides a convenient way to apply this logical transformation in proofs, allowing the conversion between these equivalent forms of quantified statements.

### Dependencies
- `NOT_EXISTS_THM`: The theorem stating the logical equivalence between `~(∃x. P[x])` and `∀x. ~P[x]`
- `CONV_OF_THM`: A function that converts theorems of the form `⊢ s = t` into conversions

### Porting notes
When porting to another system, ensure that:
1. The target system has an equivalent theorem for the negation of existential quantification
2. The system provides a way to create conversion functions from equational theorems
3. If the target system doesn't have conversion tactics like HOL Light does, consider implementing this as a rewrite rule or simplification rule instead

---

## RIGHT_IMP_EXISTS_CONV

### RIGHT_IMP_EXISTS_CONV

### Type of the formal statement
- Conversion (value definition)

### Formal Content
```ocaml
let RIGHT_IMP_EXISTS_CONV = CONV_OF_THM RIGHT_IMP_EXISTS_THM;;
```

### Informal statement
This definition creates a conversion function `RIGHT_IMP_EXISTS_CONV` that transforms formulas of the form `P ⇒ ∃x. Q[x]` into an equivalent form `∀x. P ⇒ Q[x]`. This conversion is created from the theorem `RIGHT_IMP_EXISTS_THM`.

### Informal proof
This is a definition rather than a theorem, so it doesn't have a proof. The definition creates a conversion function using the `CONV_OF_THM` operator applied to the theorem `RIGHT_IMP_EXISTS_THM`.

The conversion works by applying the logical equivalence:

$$P \Rightarrow (\exists x. Q[x]) \iff \forall x. (P \Rightarrow Q[x])$$

where the variable $x$ is not free in $P$.

### Mathematical insight
This conversion implements a common logical equivalence that is useful when rearranging formulas involving implications and existential quantifiers. The equivalence changes the order of the implication and existential quantifier, expressing the original formula in a form that's often more convenient for further manipulation.

This transformation is particularly useful in proof automation because it allows converting a goal with an existential quantifier on the right of an implication into a universally quantified implication, which can sometimes be easier to work with.

### Dependencies
- `RIGHT_IMP_EXISTS_THM`: The theorem stating the logical equivalence used by this conversion
- `CONV_OF_THM`: Function that converts a theorem about logical equivalence into a conversion function

### Porting notes
When porting to other systems:
- Check if the target system has a similar built-in conversion for this logical equivalence
- If not, create a function that applies the equivalent logical rule
- Note that in some systems, this kind of transformation might be handled automatically by the simplifier or rewriter

---

## FORALL_IMP_CONV

### FORALL_IMP_CONV
- FORALL_IMP_CONV

### Type of the formal statement
- Conversion function definition

### Formal Content
```ocaml
let FORALL_IMP_CONV = CONV_OF_RCONV
  (REWR_CONV TRIV_FORALL_IMP_THM ORELSEC
   REWR_CONV RIGHT_FORALL_IMP_THM ORELSEC
   REWR_CONV LEFT_FORALL_IMP_THM);;
```

### Informal statement
The `FORALL_IMP_CONV` is a conversion function that attempts to apply one of three rewrite conversions to a term:
1. First, it tries `TRIV_FORALL_IMP_THM` (which handles the case $\forall x. P \Rightarrow Q$ when $x$ is not free in $P$)
2. If that fails, it tries `RIGHT_FORALL_IMP_THM` (which handles $P \Rightarrow \forall x. Q$)
3. If both fail, it tries `LEFT_FORALL_IMP_THM` (which handles $\forall x. P \Rightarrow Q$ when $x$ is not free in $Q$)

The function uses `REWR_CONV` to apply each theorem as a rewrite rule, and these attempts are combined using the `ORELSEC` combinator. The result is wrapped with `CONV_OF_RCONV` to convert from a raw conversion to a standard conversion.

### Informal proof
This is a function definition rather than a theorem, so it doesn't have a proof. The definition constructs a conversion that performs rewriting based on three theorems about the interaction between universal quantifiers and implications.

### Mathematical insight
This conversion helps simplify or transform logical formulas involving universal quantifiers and implications. The three theorems it uses represent common logical equivalences:

1. When a quantified variable doesn't appear in the antecedent of an implication: $\forall x. P \Rightarrow Q$ can be simplified
2. When a quantifier appears in the consequent: $P \Rightarrow \forall x. Q$ can be transformed
3. When a quantified variable doesn't appear in the consequent: $\forall x. P \Rightarrow Q$ can be simplified

This conversion is useful for normalizing logical formulas and for performing steps in automated reasoning. It's part of HOL Light's suite of tools for manipulating higher-order logic formulas.

### Dependencies
- `TRIV_FORALL_IMP_THM`: A theorem about simplifying $\forall x. P \Rightarrow Q$ when $x$ is not free in $P$
- `RIGHT_FORALL_IMP_THM`: A theorem about transforming $P \Rightarrow \forall x. Q$
- `LEFT_FORALL_IMP_THM`: A theorem about simplifying $\forall x. P \Rightarrow Q$ when $x$ is not free in $Q$
- `CONV_OF_RCONV`: Converts a raw conversion to a standard conversion
- `REWR_CONV`: Applies a theorem as a rewrite rule
- `ORELSEC`: Combines conversions, trying the second if the first fails

### Porting notes
When porting this to another system, you would need to:
1. Ensure equivalent theorems about universal quantifiers and implications exist
2. Check if the target system has similar conversion combinators (like `ORELSEC`)
3. Make sure the target system has a way to convert between raw and standard conversions (if the distinction exists)

The functionality is relatively straightforward, but the exact implementation will depend on how the target system organizes its conversions and rewriting infrastructure.

---

## EXISTS_AND_CONV

### Name of formal statement
EXISTS_AND_CONV

### Type of the formal statement
Conversion function

### Formal Content
```ocaml
let EXISTS_AND_CONV = CONV_OF_RCONV
  (REWR_CONV TRIV_EXISTS_AND_THM ORELSEC
   REWR_CONV LEFT_EXISTS_AND_THM ORELSEC
   REWR_CONV RIGHT_EXISTS_AND_THM);;
```

### Informal statement
`EXISTS_AND_CONV` is a conversion function that distributes existential quantification over conjunction. It transforms expressions of the form:

1. $(\exists x. p(x) \land q(x))$ where $x$ does not appear in either $p$ or $q$
2. $(\exists x. p(x) \land q)$ where $x$ does not appear in $q$
3. $(\exists x. p \land q(x))$ where $x$ does not appear in $p$

into the equivalent forms:

1. $((\exists x. p(x)) \land (\exists x. q(x)))$ if $x$ is not free in either $p$ or $q$
2. $((\exists x. p(x)) \land q)$ if $x$ is not free in $q$
3. $(p \land (\exists x. q(x)))$ if $x$ is not free in $p$

### Informal proof
The conversion is implemented by combining three specific rewrite rules using the `ORELSEC` operator, which tries each conversion in sequence until one succeeds:

1. `TRIV_EXISTS_AND_THM` handles the case where the bound variable doesn't appear in either conjunct
2. `LEFT_EXISTS_AND_THM` handles the case where the bound variable appears only in the left conjunct
3. `RIGHT_EXISTS_AND_THM` handles the case where the bound variable appears only in the right conjunct

The function `CONV_OF_RCONV` is used to convert the raw conversion to a standard conversion function.

### Mathematical insight
This conversion implements the standard logical equivalences for distributing existential quantification over conjunction. These are important properties in first-order logic that allow for simplifying formulas and reasoning about quantifiers more effectively.

The three transformations correspond to these logical equivalences:
- When $x$ is not free in either $p$ or $q$: $\exists x. (p \land q) \iff (\exists x. p) \land (\exists x. q)$
- When $x$ is not free in $q$: $\exists x. (p(x) \land q) \iff (\exists x. p(x)) \land q$
- When $x$ is not free in $p$: $\exists x. (p \land q(x)) \iff p \land (\exists x. q(x))$

These equivalences are useful in theorem proving when simplifying formulas or when transforming goals into more manageable forms.

### Dependencies
- `CONV_OF_RCONV`: Converts a raw conversion to a standard conversion
- `REWR_CONV`: Applies rewrite rules
- `ORELSEC`: Combines conversions, trying each in sequence until one succeeds
- `TRIV_EXISTS_AND_THM`: Theorem for the case where the bound variable doesn't appear in either conjunct
- `LEFT_EXISTS_AND_THM`: Theorem for the case where the bound variable appears only in the left conjunct
- `RIGHT_EXISTS_AND_THM`: Theorem for the case where the bound variable appears only in the right conjunct

### Porting notes
When porting to other systems:
1. Ensure the target system has equivalent theorems for the three cases of distributing existential quantifiers over conjunctions
2. The implementation may need to be adapted based on how the target system handles conversions or rewrite rules
3. In some systems, you might need to explicitly check for variable occurrences rather than relying on theorems that encode the side conditions

---

## LEFT_IMP_EXISTS_CONV

### LEFT_IMP_EXISTS_CONV

### Type of the formal statement
- new_definition (conversion definition)

### Formal Content
```ocaml
let LEFT_IMP_EXISTS_CONV = CONV_OF_THM LEFT_IMP_EXISTS_THM;;
```

### Informal statement
`LEFT_IMP_EXISTS_CONV` is a conversion that transforms formulas of the form 
$$(\exists x. P(x)) \Rightarrow Q$$
into the equivalent form
$$\forall x. P(x) \Rightarrow Q$$

This conversion implements the logical equivalence that allows moving an existential quantifier from the antecedent of an implication to a universal quantifier over the entire implication.

### Informal proof
The definition creates a conversion from the theorem `LEFT_IMP_EXISTS_THM` using the `CONV_OF_THM` function. 

The underlying theorem `LEFT_IMP_EXISTS_THM` provides the logical equivalence:
$$(\exists x. P(x)) \Rightarrow Q \iff \forall x. P(x) \Rightarrow Q$$

The conversion directly applies this equivalence to transform formulas of the appropriate form.

### Mathematical insight
This conversion implements a fundamental quantifier manipulation rule in predicate logic. The equivalence can be understood intuitively as follows:

If we claim that "the existence of an object with property P implies Q", this is logically the same as saying "for any object, if it has property P, then Q holds". This is because:

1. If some x makes P(x) true, then Q must follow
2. The universal statement precisely captures this: for any x, if P(x) is true, then Q must be true

This conversion is particularly useful in simplifying goals in interactive theorem proving, allowing for more direct manipulation of quantifiers during proofs.

### Dependencies
- Core theorems:
  - `LEFT_IMP_EXISTS_THM` - The theorem establishing the logical equivalence
- Functions:
  - `CONV_OF_THM` - Function that converts a theorem stating an equivalence into a conversion

### Porting notes
When porting to other systems:
- Ensure the target system has the equivalent logical theorem for the quantifier manipulation
- If the target system uses a different approach to conversions or rewriting, the functionality might need to be implemented using the system's native rewriting mechanisms rather than as a direct conversion

---

## LEFT_AND_EXISTS_CONV

### LEFT_AND_EXISTS_CONV

### Type of the formal statement
- Conversion (function)

### Formal Content
```ocaml
let LEFT_AND_EXISTS_CONV tm =
  let v = bndvar(rand(rand(rator tm))) in
  (REWR_CONV LEFT_AND_EXISTS_THM THENC TRY_CONV (GEN_ALPHA_CONV v)) tm;;
```

### Informal statement
This is a conversion function that handles expressions of the form `p ∧ (∃x. q)` by applying the theorem `LEFT_AND_EXISTS_THM`, which allows moving the existential quantifier outside the conjunction. The conversion attempts to:

1. Apply rewriting using the theorem `LEFT_AND_EXISTS_THM` to transform `p ∧ (∃x. q)` into `∃x. (p ∧ q)`
2. Optionally apply alpha conversion using `GEN_ALPHA_CONV` to the bound variable `v` to avoid potential variable capture

The function expects an input term `tm` of the form `p ∧ (∃x. q)` and returns the converted term.

### Informal proof
This is a function definition rather than a theorem, so there is no proof. The implementation:

1. First extracts the bound variable `v` from the existential part of the input term using `bndvar(rand(rand(rator tm)))`.
2. Then applies a sequential conversion that:
   - First applies the rewrite conversion using `LEFT_AND_EXISTS_THM` to move the existential outside the conjunction
   - Then tries to apply alpha conversion to the bound variable `v` to avoid potential variable capture

The function composition is accomplished using the `THENC` operator which chains conversions together.

### Mathematical insight
This conversion implements a common logical manipulation where an existential quantifier can be "pulled out" from the right side of a conjunction. This is a standard logical equivalence:

$$p \land (\exists x. q) \equiv \exists x. (p \land q)$$

The conversion is important because:
1. It helps normalize logical expressions by bringing quantifiers to the outermost level
2. It can simplify reasoning with existential statements in conjunction contexts
3. The alpha conversion step helps prevent variable capture, which is essential for maintaining logical correctness when manipulating terms with bound variables

The conversion is part of HOL Light's infrastructure for manipulating logical formulas in automated reasoning.

### Dependencies
- Theorems:
  - `LEFT_AND_EXISTS_THM`: Likely a theorem stating the equivalence: `p ∧ (∃x. q) ⇔ ∃x. (p ∧ q)`

- Conversions:
  - `REWR_CONV`: Applies a rewrite using a given theorem
  - `TRY_CONV`: Attempts to apply a conversion, returning the identity if it fails
  - `GEN_ALPHA_CONV`: Performs alpha conversion to rename bound variables

### Porting notes
When porting this conversion to other systems:

1. Ensure the target system has an equivalent theorem to `LEFT_AND_EXISTS_THM`
2. Check if the target system has a mechanism for alpha conversion to avoid variable capture
3. Most proof assistants will have their own way of composing conversions/tactics, so adapt the `THENC` composition accordingly
4. The term structure extraction (`bndvar(rand(rand(rator tm)))`) is HOL Light specific - you'll need to use the appropriate term inspection functions in the target system

---

## RIGHT_AND_EXISTS_CONV

### RIGHT_AND_EXISTS_CONV

### Type of the formal statement
- conversion function

### Formal Content
```ocaml
let RIGHT_AND_EXISTS_CONV =
  CONV_OF_THM RIGHT_AND_EXISTS_THM;;
```

### Informal statement
This is a conversion function that transforms formulas of the form `P ∧ (∃x. Q(x))` into equivalent formulas of the form `∃x. P ∧ Q(x)`, where `x` is not free in `P`. The conversion applies the theorem `RIGHT_AND_EXISTS_THM` to the input formula.

### Informal proof
This is a direct application of the theorem `RIGHT_AND_EXISTS_THM` using the `CONV_OF_THM` function, which converts a theorem into a conversion function. No additional proof is needed since the conversion simply applies the established theorem.

### Mathematical insight
This conversion implements the logical equivalence between `P ∧ (∃x. Q(x))` and `∃x. P ∧ Q(x)` when `x` is not free in `P`. This transformation is useful in theorem proving as it allows for moving existential quantifiers outward in a formula, which can simplify the structure and make it easier to manipulate. This is a common logical equivalence used in various formal proofs.

The transformation corresponds to the logical principle that if a conjunction has an existentially quantified component, and the quantified variable doesn't appear in the other component, then the quantifier can be moved outside the entire conjunction.

### Dependencies
- Theorems:
  - `RIGHT_AND_EXISTS_THM`: Theorem establishing the equivalence between `P ∧ (∃x. Q(x))` and `∃x. P ∧ Q(x)` when `x` is not free in `P`
- Functions:
  - `CONV_OF_THM`: Function that converts a theorem into a conversion function

### Porting notes
When porting this conversion to other proof assistants:
- Ensure that the target system has an equivalent theorem to `RIGHT_AND_EXISTS_THM`
- The implementation will depend on how conversions or rewriting rules are handled in the target system
- Some systems might already have built-in tactics or simplification rules that handle this logical equivalence automatically

---

## AND_FORALL_CONV

### Name of formal statement
AND_FORALL_CONV

### Type of the formal statement
Conversion

### Formal Content
```ocaml
let AND_FORALL_CONV = CONV_OF_THM AND_FORALL_THM;;
```

### Informal statement
`AND_FORALL_CONV` is a conversion function that applies the equivalence from the theorem `AND_FORALL_THM`. This conversion transforms a formula of the form 
$(\forall x. P(x)) \land (\forall x. Q(x))$ 
to its equivalent form 
$\forall x. P(x) \land Q(x)$.

### Informal proof
This is a conversion definition rather than a theorem, so there's no proof. The conversion is defined by converting the theorem `AND_FORALL_THM` into a conversion function using `CONV_OF_THM`.

The underlying theorem `AND_FORALL_THM` establishes that:
$(\forall x. P(x)) \land (\forall x. Q(x)) \Leftrightarrow \forall x. (P(x) \land Q(x))$

This conversion applies that theorem as a rewrite rule.

### Mathematical insight
This conversion implements a standard logical equivalence that allows merging two universal quantifiers joined by conjunction into a single universal quantifier with a conjunction inside its body. This transformation is often useful in simplifying formulas and in proof steps where we need to work with universally quantified statements.

The conversion helps normalize logical formulas by reducing the number of quantifiers, which can make subsequent reasoning steps more straightforward. It's part of HOL Light's suite of conversions for manipulating logical formulas.

### Dependencies
- `AND_FORALL_THM` - The theorem stating the equivalence $(\forall x. P(x)) \land (\forall x. Q(x)) \Leftrightarrow \forall x. (P(x) \land Q(x))$
- `CONV_OF_THM` - Converts a theorem into a conversion

### Porting notes
When porting this to another system, you'll need to:
1. Ensure the target system has the equivalent theorem to `AND_FORALL_THM`
2. Implement a similar conversion mechanism that applies the theorem as a rewrite rule
3. In some systems, this might be implemented as part of a general simplification or rewriting tactic rather than as a standalone conversion

---

## AND1_THM

### AND1_THM
- `AND1_THM`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let AND1_THM = TAUT `!t1 t2. t1 /\ t2 ==> t1`;;
```

### Informal statement
The theorem states that for all propositions $t_1$ and $t_2$, if $t_1 \land t_2$ (the conjunction of $t_1$ and $t_2$) is true, then $t_1$ is true.

Formally: $\forall t_1, t_2. (t_1 \land t_2) \Rightarrow t_1$

### Informal proof
This theorem is proved using `TAUT`, which is HOL Light's tautology prover. The theorem is a basic logical tautology that follows directly from the definition of conjunction. 

The conjunction $t_1 \land t_2$ is true if and only if both $t_1$ and $t_2$ are true. Therefore, if $t_1 \land t_2$ is true, then $t_1$ must be true.

### Mathematical insight
This theorem captures one of the fundamental properties of logical conjunction: if a conjunction is true, then each of its components must be true. It's part of the basic rules of propositional logic and is used as a building block for more complex logical reasoning.

In formal systems, this theorem is often used to extract the first component of a conjunction, allowing us to simplify expressions and advance proofs by focusing on relevant parts of compound statements.

### Dependencies
- Functions:
  - `TAUT`: A function that proves tautologies in propositional logic

### Porting notes
This theorem should be straightforward to port to any system supporting propositional logic. In many systems, this might be a built-in rule or easily derivable from the definition of conjunction. The logical structure is universally recognized across formal systems.

---

## AND2_THM

### AND2_THM
- `AND2_THM`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let AND2_THM = TAUT `!t1 t2. t1 /\ t2 ==> t2`;;
```

### Informal statement
This theorem states that for any propositions $t_1$ and $t_2$, if the conjunction $t_1 \land t_2$ holds, then $t_2$ holds.

Formally:
$$\forall t_1 \, t_2 : \text{bool}. \, (t_1 \land t_2) \Rightarrow t_2$$

### Informal proof
This theorem is proved using the `TAUT` tactic, which automatically proves tautologies in propositional logic. The result follows directly from the definition of conjunction: if we know that $t_1 \land t_2$ is true, then by the definition of conjunction, both $t_1$ and $t_2$ must be true individually.

### Mathematical insight
This theorem represents one of the fundamental properties of logical conjunction - the ability to extract the right component from a conjunction. Along with its companion theorem (extracting the left component), it forms the basis of the elimination rule for conjunction in natural deduction systems.

In practical reasoning, this theorem allows us to use either part of a conjunction separately once we have established the conjunction as a whole.

### Dependencies
No explicit dependencies were provided, but this theorem relies on:
- The definition of logical conjunction
- The `TAUT` tactic in HOL Light, which handles propositional tautologies

### Porting notes
This theorem is a trivial propositional logic result that should be available in any proof assistant. In some systems, it might already be built into the core logic or available as part of the standard library. When porting, this could be proven using the system's equivalent of a propositional tautology solver or directly from the conjunction elimination rules.

---

## AND_IMP_INTRO

### AND_IMP_INTRO

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let AND_IMP_INTRO = TAUT `!t1 t2 t3. t1 ==> t2 ==> t3 = t1 /\ t2 ==> t3`;;
```

### Informal statement
This theorem establishes the logical equivalence:
$$\forall t_1, t_2, t_3. \; (t_1 \Rightarrow t_2 \Rightarrow t_3) \; \equiv \; ((t_1 \land t_2) \Rightarrow t_3)$$

where $t_1$, $t_2$, and $t_3$ are propositional variables.

### Informal proof
This theorem is proved using the `TAUT` tactic, which automatically proves tautologies in propositional logic. 

The equivalence follows directly from the definition of implication in classical logic:
- The left side $(t_1 \Rightarrow t_2 \Rightarrow t_3)$ means "if $t_1$ holds, then if $t_2$ holds, then $t_3$ holds"
- The right side $((t_1 \land t_2) \Rightarrow t_3)$ means "if both $t_1$ and $t_2$ hold, then $t_3$ holds"

These are logically equivalent statements in classical propositional logic.

### Mathematical insight
This theorem formalizes a common pattern of reasoning in mathematical proofs. It shows that nested implications can be rewritten as a single implication with a conjunctive antecedent. 

This equivalence is particularly useful in simplifying logical expressions and in the mechanical manipulation of formal proofs. It allows us to convert between a curried form of implication (where implications are chained) and an uncurried form (where multiple premises are combined with conjunction).

The theorem is part of the basic infrastructure of propositional logic reasoning in HOL Light.

### Dependencies
No explicit dependencies are listed, but the theorem relies on:
- `TAUT` tactic from HOL Light, which proves tautologies in propositional logic

### Porting notes
This is a standard result in propositional logic and should be readily available in most proof assistants. If not directly available, it can be proven easily using the system's propositional logic tactics.

---

## AND_INTRO_THM

### AND_INTRO_THM
- `AND_INTRO_THM`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let AND_INTRO_THM = TAUT `!t1 t2. t1 ==> t2 ==> t1 /\ t2`;;
```

### Informal statement
The theorem states that for all propositions $t_1$ and $t_2$:
$$t_1 \Rightarrow (t_2 \Rightarrow (t_1 \wedge t_2))$$

This is the introduction rule for conjunction, which says that if we have $t_1$ and we have $t_2$, then we can derive their conjunction $t_1 \wedge t_2$.

### Informal proof
This theorem is established using the `TAUT` tactic in HOL Light, which automatically proves tautologies in propositional logic. 

The statement is indeed a tautology because:
- If $t_1$ is true and $t_2$ is true, then clearly $t_1 \wedge t_2$ is true.
- If either $t_1$ or $t_2$ is false, then the corresponding implication becomes trivially true (since an implication with a false antecedent is true).

### Mathematical insight
This theorem formalizes one of the basic rules of natural deduction in propositional logic - the conjunction introduction rule. It captures the intuitive idea that to establish a conjunction, you need to establish each of its components individually.

In the context of formal proofs, this theorem allows us to derive a conjunction when we have separate proofs for each conjunct. This is a fundamental building block for constructing more complex proofs.

In terms of typed lambda calculus interpretations (via the Curry-Howard correspondence), this corresponds to the construction of a pair from two terms.

### Dependencies
The theorem relies on the `TAUT` tactical which automatically proves tautologies in propositional logic.

### Porting notes
This theorem is a basic propositional logic tautology that should be trivial to port to any other proof assistant. Most proof assistants will either have this theorem built-in or can prove it automatically with their propositional logic solvers.

---

## BOOL_EQ_DISTINCT

### BOOL_EQ_DISTINCT
- BOOL_EQ_DISTINCT

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let BOOL_EQ_DISTINCT = TAUT `~(T <=> F) /\ ~(F <=> T)`;;
```

### Informal statement
The theorem states that:
$\lnot(T \Leftrightarrow F) \land \lnot(F \Leftrightarrow T)$

This means that the boolean values True and False are not equivalent to each other. In other words, it establishes that logical True and logical False are distinct values.

### Informal proof
This theorem is proved using the `TAUT` tactic, which automatically proves tautologies in propositional logic. 

The statement is indeed a tautology because:
- $T \Leftrightarrow F$ would mean that True is equivalent to False, which is a contradiction
- $F \Leftrightarrow T$ would mean that False is equivalent to True, which is also a contradiction

The negations of these contradictions are therefore true, and their conjunction forms the theorem.

### Mathematical insight
This theorem establishes a fundamental property of boolean logic: the distinct nature of the truth values True and False. It formally proves that these values cannot be equivalent to each other, which is a basic axiom in boolean algebra and propositional logic.

This fact is essential for the consistency of the logical system, as conflating True and False would lead to a trivial logic where every statement is both true and false simultaneously (a contradiction).

### Dependencies
No explicit dependencies are listed, but the theorem relies on:
- The built-in `TAUT` tactic in HOL Light that proves propositional tautologies
- The basic definitions of logical operators (negation, conjunction, and equivalence)
- The fundamental boolean values T (True) and F (False)

### Porting notes
This theorem should be trivial to port to other proof assistants, as it represents a fundamental property of boolean logic that is built into most logical foundations. Many systems might already have this as part of their core library or might derive it automatically from more basic axioms about boolean values.

---

## EQ_EXPAND

### Name of formal statement
EQ_EXPAND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EQ_EXPAND = TAUT `!t1 t2. (t1 <=> t2) <=> t1 /\ t2 \/ ~t1 /\ ~t2`;;
```

### Informal statement
For all propositions $t_1$ and $t_2$:
$$(t_1 \Leftrightarrow t_2) \Leftrightarrow (t_1 \land t_2) \lor (\lnot t_1 \land \lnot t_2)$$

This theorem states that the logical equivalence between two propositions is itself equivalent to either both propositions being true or both being false.

### Informal proof
This theorem is proven using `TAUT`, which is a HOL Light tactic that proves tautologies in propositional logic. The statement is a basic tautology in propositional logic that can be verified through a truth table analysis.

For propositions $t_1$ and $t_2$:
- When both $t_1$ and $t_2$ are true, both $(t_1 \Leftrightarrow t_2)$ and $(t_1 \land t_2)$ are true.
- When both $t_1$ and $t_2$ are false, both $(t_1 \Leftrightarrow t_2)$ and $(\lnot t_1 \land \lnot t_2)$ are true.
- When $t_1$ is true and $t_2$ is false, or vice versa, $(t_1 \Leftrightarrow t_2)$ is false, and both disjuncts on the right side are false.

Thus, the equivalence holds in all possible truth value assignments.

### Mathematical insight
This theorem provides an expansion of the logical equivalence operator ($\Leftrightarrow$) in terms of conjunction ($\land$), disjunction ($\lor$), and negation ($\lnot$). It's useful for simplifying logical expressions or rewriting them in normal forms.

The theorem captures the essential meaning of equivalence: two propositions are equivalent precisely when they have the same truth value - either both are true or both are false.

### Dependencies
None explicitly listed in the provided dependency list. The theorem is proven using the `TAUT` tactic which is a built-in HOL Light mechanism for proving tautologies in propositional logic.

### Porting notes
This theorem should be straightforward to port to other proof assistants as it represents a basic propositional logic identity. Most systems would have:

1. Built-in tactics for automatic propositional logic reasoning (similar to HOL Light's `TAUT`)
2. Direct support for the equivalence operator and its definition

In systems without specific automation for propositional logic tautologies, this could be proven through case analysis on the truth values of $t_1$ and $t_2$.

---

## EQ_IMP_THM

### EQ_IMP_THM
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let EQ_IMP_THM = TAUT `!t1 t2. (t1 <=> t2) <=> (t1 ==> t2) /\ (t2 ==> t1)`;;
```

### Informal statement
For any propositions $t_1$ and $t_2$, the logical equivalence $t_1 \Leftrightarrow t_2$ holds if and only if both implications hold: $(t_1 \Rightarrow t_2) \land (t_2 \Rightarrow t_1)$.

### Informal proof
This theorem is proven using the `TAUT` tactic, which automatically proves tautologies in propositional logic. The statement is a basic property of logical equivalence, showing that an equivalence can be decomposed into two implications in both directions.

### Mathematical insight
This theorem formalizes the fundamental definition of logical equivalence: two propositions are equivalent precisely when each implies the other. This is a basic principle in logic used extensively in formal reasoning. It allows breaking down equivalence statements into two separate implications, which is often easier to work with in proofs.

### Dependencies
- `TAUT` - Tautology prover in HOL Light

### Porting notes
This is a fundamental logical property that should be available in any formal logic system. In some systems, it might be part of the core logic rather than a named theorem. When porting, check if the target system already has this theorem or an equivalent one.

---

## FALSITY

### FALSITY
- FALSITY

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FALSITY = TAUT `!t. F ==> t`;;
```

### Informal statement
This theorem states that falsehood (denoted as $F$) implies any proposition. Formally, it asserts:

$$\forall t. F \Rightarrow t$$

Where:
- $F$ is the logical constant for falsehood
- $t$ is any proposition
- $\Rightarrow$ is the logical implication

### Informal proof
This is a tautology in classical propositional logic. In classical logic, the principle of explosion (ex falso quodlibet) states that from a contradiction, anything follows. The theorem is proved using the `TAUT` procedure in HOL Light, which automatically proves tautologies of propositional logic.

The underlying reasoning is straightforward: since $F$ is always false, the implication $F \Rightarrow t$ is vacuously true for any proposition $t$, as the antecedent is never satisfied.

### Mathematical insight
This theorem formalizes the principle of explosion (ex falso quodlibet), which is a fundamental principle in classical logic. It asserts that from a contradiction, any proposition can be derived.

The principle is sometimes summarized as "from falsehood, anything follows" or "once a contradiction is asserted, any proposition can be inferred."

This theorem is particularly useful in proof systems as it allows reasoning from contradictory assumptions. When proving a statement by contradiction, for instance, the ability to derive anything from a false assumption is crucial to complete the proof.

### Dependencies
No explicit dependencies beyond HOL Light's built-in propositional logic tautology prover (`TAUT`).

### Porting notes
This theorem should be easily portable to any proof assistant that supports classical logic. In constructive/intuitionistic logic systems, this principle is still valid and usually a basic axiom or an early theorem.

---

## F_IMP

### F_IMP
- F_IMP

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let F_IMP = TAUT `!t. ~t ==> t ==> F`;;
```

### Informal statement
This theorem states that for any proposition $t$:
$$\lnot t \implies (t \implies \text{F})$$

where $\text{F}$ represents the logical constant false.

### Informal proof
This is a tautology (proved using the `TAUT` tactic), which follows directly from the principles of propositional logic:

If we assume $\lnot t$ and $t$ simultaneously, we reach a contradiction, which allows us to derive falsehood $\text{F}$.

In more detail:
- Assume $\lnot t$ (first premise)
- Assume $t$ (second premise)
- These assumptions directly contradict each other
- From a contradiction, we can derive any proposition, including $\text{F}$ (principle of explosion)

### Mathematical insight
This theorem represents a basic principle in classical logic: assuming a proposition and its negation simultaneously leads to a contradiction, which implies falsehood.

It demonstrates the principle of explosion (ex falso quodlibet), which states that from a contradiction, anything can be derived. In this case, when we have both $\lnot t$ and $t$, we can derive falsehood.

This theorem is useful in proofs by contradiction and when working with implications in various logical contexts.

### Dependencies
None explicitly listed in the given information. The proof relies only on the built-in `TAUT` tactic, which proves tautologies in propositional logic.

---

## IMP_DISJ_THM

### IMP_DISJ_THM
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem 

### Formal Content
```ocaml
let IMP_DISJ_THM = TAUT `!t1 t2. t1 ==> t2 <=> ~t1 \/ t2`;;
```

### Informal statement
This theorem states that for all propositions $t_1$ and $t_2$, the implication $t_1 \Rightarrow t_2$ is logically equivalent to the disjunction $\lnot t_1 \lor t_2$.

Formally:
$\forall t_1, t_2. (t_1 \Rightarrow t_2) \Leftrightarrow (\lnot t_1 \lor t_2)$

### Informal proof
This theorem is proven using the `TAUT` function in HOL Light, which automatically proves tautologies in propositional logic.

The proof relies on the truth table for implication, which can be derived as follows:
- When $t_1$ is true and $t_2$ is true, both $t_1 \Rightarrow t_2$ and $\lnot t_1 \lor t_2$ evaluate to true.
- When $t_1$ is true and $t_2$ is false, both $t_1 \Rightarrow t_2$ and $\lnot t_1 \lor t_2$ evaluate to false.
- When $t_1$ is false and $t_2$ is true, both $t_1 \Rightarrow t_2$ and $\lnot t_1 \lor t_2$ evaluate to true.
- When $t_1$ is false and $t_2$ is false, both $t_1 \Rightarrow t_2$ and $\lnot t_1 \lor t_2$ evaluate to true.

Since the two expressions have the same truth value in all possible interpretations, they are logically equivalent.

### Mathematical insight
This theorem expresses the material implication in terms of disjunction and negation, which is a fundamental equivalence in propositional logic. It shows that implication can be reduced to more basic logical operations.

This equivalence is particularly useful in formal reasoning systems because it allows us to convert implications to a form that can be manipulated using rules for disjunctions, which are often simpler to work with.

### Dependencies
- The theorem is proven using `TAUT`, which is HOL Light's automated prover for propositional tautologies.

### Porting notes
This is a standard result in propositional logic that should be available in most proof assistants or can be easily proven. In systems like Lean, Coq, or Isabelle, this theorem might already exist in the standard library or can be proven using basic propositional logic tactics.

---

## IMP_F

### IMP_F
- `IMP_F`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let IMP_F = TAUT `!t. (t ==> F) ==> ~t`;;
```

### Informal statement
For all propositions $t$:
$$(t \Rightarrow \text{False}) \Rightarrow \neg t$$

This theorem states that if a proposition $t$ implies falsehood, then $t$ is false (i.e., $\neg t$ is true).

### Informal proof
This is a tautology in propositional logic. It follows from the definition of negation: $\neg t$ is defined as $t \Rightarrow \text{False}$. Therefore, the theorem is simply stating that $(t \Rightarrow \text{False}) \Rightarrow (t \Rightarrow \text{False})$, which is trivially true.

The theorem is proved using the `TAUT` tactic, which automatically proves tautologies in propositional logic.

### Mathematical insight
This theorem captures a fundamental principle of classical logic: if a proposition implies falsehood, then the proposition must be false. This is closely related to proof by contradiction, where we assume a proposition and derive a contradiction, thereby showing the negation of the proposition.

The theorem also reflects the definition of negation in many logical systems, where $\neg t$ is defined as $t \Rightarrow \text{False}$.

### Dependencies
No explicit dependencies beyond the `TAUT` tactic which is built into HOL Light's propositional logic reasoning system.

### Porting notes
This theorem should be trivial to port to other proof assistants, as it represents a basic tautology of classical logic. In systems based on intuitionistic logic (like Coq), this theorem would still hold since it's a constructively valid principle.

---

## IMP_F_EQ_F

### Name of formal statement
IMP_F_EQ_F

### Type of the formal statement
theorem

### Formal Content
```ocaml
let IMP_F_EQ_F = TAUT `!t. t ==> F <=> (t <=> F)`;;
```

### Informal statement
For any proposition $t$, the statement $t \Rightarrow \text{False}$ is logically equivalent to $t \Leftrightarrow \text{False}$.

### Informal proof
This theorem is established using the `TAUT` tactic, which proves tautologies in propositional logic. 

The proof relies on a truth-table analysis:
- When $t$ is true, $t \Rightarrow \text{False}$ is false, and $t \Leftrightarrow \text{False}$ is also false.
- When $t$ is false, $t \Rightarrow \text{False}$ is true, and $t \Leftrightarrow \text{False}$ is also true.

Thus, the two expressions $t \Rightarrow \text{False}$ and $t \Leftrightarrow \text{False}$ have the same truth values in all possible cases, making them logically equivalent.

### Mathematical insight
This theorem captures an important relationship between implication and logical equivalence when the consequent is False. It shows that negation can be expressed either as "implies false" or "equivalent to false," which is useful in logical transformations and proof strategies.

This is part of basic propositional calculus but provides a useful identity when manipulating logical expressions, especially when dealing with negations in different forms.

### Dependencies
None explicitly mentioned in the provided dependency list.

---

## LEFT_AND_OVER_OR

### LEFT_AND_OVER_OR

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LEFT_AND_OVER_OR = TAUT
  `!t1 t2 t3. t1 /\ (t2 \/ t3) <=> t1 /\ t2 \/ t1 /\ t3`;;
```

### Informal statement
For all boolean expressions $t_1$, $t_2$, and $t_3$, the following equivalence holds:
$t_1 \wedge (t_2 \vee t_3) \Leftrightarrow (t_1 \wedge t_2) \vee (t_1 \wedge t_3)$

This expresses the distributivity of conjunction ($\wedge$) over disjunction ($\vee$).

### Informal proof
This theorem is proved using `TAUT`, which automatically proves tautologies in propositional logic.

The statement is a basic law of boolean algebra and can be verified by considering all possible truth values for $t_1$, $t_2$, and $t_3$. It can also be proven directly:

- If $t_1$ is false, both sides evaluate to false.
- If $t_1$ is true, then the left side becomes $(t_2 \vee t_3)$ and the right side becomes $t_2 \vee t_3$, which are equal.

### Mathematical insight
The distributivity of conjunction over disjunction is a fundamental property in propositional logic and Boolean algebra. It allows us to rewrite logical expressions in different but equivalent forms, which can be useful for simplification or for putting formulas into specific normal forms like conjunctive normal form (CNF) or disjunctive normal form (DNF).

This property has analogues in other algebraic structures, such as the distributivity of multiplication over addition in arithmetic.

### Dependencies
- `TAUT`: A tactic in HOL Light that proves tautologies in propositional logic.

### Porting notes
This theorem should be relatively straightforward to port to other proof assistants, as distributivity of conjunction over disjunction is a basic property that is often built into propositional logic libraries or can be proven easily. In systems with automation for propositional logic (like Coq's `tauto` or Isabelle's `simp`), this might be proven automatically without needing an explicit statement.

---

## LEFT_OR_OVER_AND

### LEFT_OR_OVER_AND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LEFT_OR_OVER_AND = TAUT
  `!t1 t2 t3. t1 \/ t2 /\ t3 <=> (t1 \/ t2) /\ (t1 \/ t3)`;;
```

### Informal statement
For any propositions $t_1$, $t_2$, and $t_3$, the following logical equivalence holds:
$$t_1 \lor (t_2 \land t_3) \Leftrightarrow (t_1 \lor t_2) \land (t_1 \lor t_3)$$

This is the distributive law for logical disjunction over conjunction, stating that disjunction distributes over conjunction.

### Informal proof
This theorem is proven using `TAUT`, a HOL Light primitive for proving tautologies in propositional logic. The distributive law of disjunction over conjunction is a standard tautology in propositional logic and can be verified by a truth table analysis or using standard propositional logic rules.

### Mathematical insight
This theorem formalizes the distributive law of disjunction over conjunction, a fundamental property in propositional logic. The result allows simplification of logical formulas by distributing disjunction over conjunction. This law is dual to the distributive law of conjunction over disjunction ($(t_1 \land t_2) \lor t_3 \Leftrightarrow (t_1 \lor t_3) \land (t_2 \lor t_3)$).

This property is useful in various contexts including:
- Simplifying logical expressions
- Normal form manipulations (converting to CNF/DNF)
- Logical reasoning in formal verification

### Dependencies
The theorem is proven using the `TAUT` tactic, which is a primitive in HOL Light for proving tautologies in propositional logic.

### Porting notes
This theorem should be straightforward to port to any theorem prover with basic propositional logic support. In many systems, this might already exist as a built-in theorem or be provable using automated tactics for propositional logic (such as `tauto` in Coq or `simp` in Isabelle).

---

## NOT_AND

### NOT_AND
- NOT_AND

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let NOT_AND = TAUT `~(t /\ ~t)`;;
```

### Informal statement
The theorem states that a proposition and its negation cannot both be true simultaneously. Formally:

$$\neg (t \wedge \neg t)$$

where $t$ is a proposition.

### Informal proof
This theorem is proved using the `TAUT` tactic in HOL Light, which automatically proves tautologies of propositional logic. The statement $\neg (t \wedge \neg t)$ is a basic tautology that follows directly from the law of non-contradiction.

No explicit proof steps are provided as this is handled automatically by the `TAUT` decision procedure.

### Mathematical insight
This theorem represents the law of non-contradiction, a fundamental principle in classical logic. It states that a proposition cannot be both true and false at the same time. This principle is often taken as axiomatic in logical systems.

The theorem serves as a basic building block for formal reasoning and is used frequently in proofs by contradiction or cases.

### Dependencies
This theorem is proved using the `TAUT` tactic, which automatically proves tautologies of propositional logic.

### Porting notes
This theorem should be trivial to port to other systems, as it represents a basic principle of classical logic. In most systems, this would be either:
- Part of the core logical framework
- Provable using basic automated tactics (such as `tauto` in Coq or `simp` in Lean)
- Derivable as a simple consequence of the law of non-contradiction

Note that in constructive/intuitionistic logic systems, this theorem would still be provable, as the law of non-contradiction is accepted in both classical and intuitionistic logic.

---

## NOT_F

### Name of formal statement
NOT_F

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NOT_F = TAUT `!t. ~t ==> (t <=> F)`;;
```

### Informal statement
For any proposition $t$, if $\neg t$ holds, then $t$ is logically equivalent to $F$ (false).

Formally:
$\forall t. \neg t \Rightarrow (t \Leftrightarrow F)$

### Informal proof
This theorem is established using the HOL Light tautology prover `TAUT`. The statement is a basic logical tautology that follows directly from the semantics of propositional logic:

If $\neg t$ is true (i.e., $t$ is false), then $t$ and $F$ have the same truth value (both are false), which means they are logically equivalent.

### Mathematical insight
This theorem expresses a fundamental property in propositional logic: when a proposition is known to be false (i.e., its negation is true), it is logically equivalent to the constant false ($F$). This is a basic building block for logical simplification and normalization in formal reasoning.

The theorem allows for replacing any proposition known to be false with the explicit false constant, which can simplify expressions in automated theorem proving and logical reasoning.

### Dependencies
No explicit dependencies beyond HOL Light's built-in logical machinery, as this is established directly using the `TAUT` tactic which resolves propositional tautologies.

---

## OR_ELIM_THM

### Name of formal statement
OR_ELIM_THM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let OR_ELIM_THM = TAUT
  `!t t1 t2. t1 \/ t2 ==> (t1 ==> t) ==> (t2 ==> t) ==> t`;;
```

### Informal statement
For all propositions $t$, $t_1$, and $t_2$, if $t_1 \lor t_2$ holds, and $t_1 \Rightarrow t$ holds, and $t_2 \Rightarrow t$ holds, then $t$ holds.

In other words, this theorem formalizes the principle of case analysis or proof by cases: if we know that either $t_1$ or $t_2$ is true, and we can derive $t$ from either case, then $t$ must be true.

### Informal proof
This theorem is proven using the `TAUT` tactic in HOL Light, which automatically proves tautologies in propositional logic.

The statement is indeed a tautology in propositional logic. To see why:
- If $t_1 \lor t_2$ is true, then either $t_1$ is true or $t_2$ is true.
- If $t_1$ is true and $t_1 \Rightarrow t$ holds, then $t$ is true.
- If $t_2$ is true and $t_2 \Rightarrow t$ holds, then $t$ is true.
- Therefore, regardless of which disjunct is true, $t$ must be true.

### Mathematical insight
This theorem captures the fundamental logical principle of proof by cases (or disjunction elimination). It states that to prove a conclusion from a disjunctive premise, it suffices to prove that the conclusion follows from each disjunct separately.

This is one of the basic inference rules in natural deduction systems and appears in various forms across different logical systems. In practical theorem proving, it enables case analysis, which is a common proof technique where one splits the proof into separate cases and shows that the desired conclusion holds in each case.

### Dependencies
No explicit dependencies are listed for this theorem. It is proven directly using the `TAUT` tactic, which relies on HOL Light's built-in propositional logic solver.

### Porting notes
This theorem should be straightforward to port to other proof assistants since:
- It represents a fundamental principle of propositional logic
- It requires minimal infrastructure (just the basic logical connectives)
- Most systems either have this as a built-in rule or can prove it easily with their automation

In systems like Lean, Coq, or Isabelle, similar theorems might already exist in their standard libraries, possibly with slightly different names or formulations.

---

## OR_IMP_THM

### OR_IMP_THM
- `OR_IMP_THM`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let OR_IMP_THM = TAUT `!t1 t2. (t1 <=> t2 \/ t1) <=> t2 ==> t1`;;
```

### Informal statement
This theorem states that for any propositions $t_1$ and $t_2$:

$$\forall t_1, t_2. \, ((t_1 \Leftrightarrow (t_2 \vee t_1)) \Leftrightarrow (t_2 \Rightarrow t_1))$$

In other words, the statement "$t_1$ is equivalent to $t_2$ or $t_1$" is itself equivalent to "if $t_2$ then $t_1$".

### Informal proof
This theorem is proved using the `TAUT` tactic, which automatically proves tautologies in propositional logic.

The proof relies on basic propositional logic equivalences:
- $t_1 \Leftrightarrow (t_2 \vee t_1)$ means $t_1$ is true if and only if either $t_2$ is true or $t_1$ is true
- Since $t_1 \vee t_1 \Leftrightarrow t_1$ (idempotence of disjunction), the left side reduces to $t_1 \Leftrightarrow (t_2 \vee t_1) \Leftrightarrow t_1 \Rightarrow (t_2 \Rightarrow t_1)$
- By propositional logic, $t_2 \vee t_1 \Leftrightarrow \neg t_2 \Rightarrow t_1$, which is equivalent to $t_2 \Rightarrow t_1$

The `TAUT` tactic automatically validates this equivalence through truth table analysis or other propositional calculus methods.

### Mathematical insight
This theorem captures an important logical equivalence in propositional logic. It demonstrates the relationship between disjunction and implication, which is fundamental in many logical systems.

The theorem is useful in simplifying expressions in theorem proving, particularly when dealing with complex logical formulas involving disjunctions and implications. It allows for the transformation of certain patterns involving disjunctions into implications, which can sometimes be easier to work with in proof steps.

### Dependencies
- `TAUT`: A decision procedure for propositional tautologies in HOL Light

### Porting notes
This theorem should be relatively straightforward to port to other systems as it relies only on basic propositional logic. Most proof assistants have built-in tactics similar to `TAUT` for proving propositional tautologies, so the proof could be simply replaced with the equivalent tactic in the target system.

---

## OR_INTRO_THM1

### Name of formal statement
OR_INTRO_THM1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let OR_INTRO_THM1 = TAUT `!t1 t2. t1 ==> t1 \/ t2`;;
```

### Informal statement
For any propositions $t_1$ and $t_2$, if $t_1$ is true, then the disjunction $t_1 \lor t_2$ is also true.

### Informal proof
This theorem is established through tautology checking using HOL Light's `TAUT` function. 

The proof relies on the basic principles of propositional logic: if one disjunct in a logical disjunction is true, then the entire disjunction is true, regardless of the truth value of the other disjunct.

In particular, if $t_1$ is true, then $t_1 \lor t_2$ must be true by the definition of logical disjunction.

### Mathematical insight
This theorem captures one of the fundamental introduction rules for logical disjunction in propositional logic. It formalizes the intuitive notion that having evidence for one alternative is sufficient to claim that "at least one of the alternatives is true."

This rule is essential in formal reasoning systems and is commonly known as "or-introduction" or "disjunction introduction" in natural deduction systems. It allows us to weaken a statement by adding an additional disjunct.

In practical theorem proving, this rule is often used when we need to establish a disjunction but only have evidence for one of the disjuncts, or when we want to generalize a specific result to a more general form.

### Dependencies
No explicit dependencies are listed, but this theorem relies on the built-in propositional logic capabilities of HOL Light through the `TAUT` function, which automatically proves tautologies.

### Porting notes
This theorem should be trivial to port to any proof assistant that supports propositional logic. In many systems, this might already be a built-in rule or easily provable using the system's basic propositional logic tactics or decision procedures.

---

## OR_INTRO_THM2

### OR_INTRO_THM2
- OR_INTRO_THM2

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let OR_INTRO_THM2 = TAUT `!t1 t2. t2 ==> t1 \/ t2`;;
```

### Informal statement
The theorem states that for all propositions $t_1$ and $t_2$, if $t_2$ is true, then the disjunction $t_1 \lor t_2$ is true.

Formally, $\forall t_1, t_2. \; t_2 \Rightarrow (t_1 \lor t_2)$

### Informal proof
This theorem is proven using `TAUT`, which means it is a tautology (a logical formula that is true in all possible interpretations). 

The proof follows from the logical properties of disjunction:
- If one of the disjuncts is true, then the entire disjunction is true
- Specifically, if $t_2$ is true, then $t_1 \lor t_2$ is true regardless of the truth value of $t_1$

### Mathematical insight
This theorem captures a fundamental property of logical disjunction (OR): if one of the disjuncts is true, then the entire disjunction is true. Specifically, this theorem focuses on the right introduction rule for disjunction, stating that if we know $t_2$ is true, we can conclude $t_1 \lor t_2$.

This is one of the basic inference rules in propositional logic and is part of the natural deduction system. It is a fundamental building block for logical reasoning and proof construction.

The theorem is paired with `OR_INTRO_THM` (which likely states $t_1 \Rightarrow (t_1 \lor t_2)$) to provide the complete introduction rules for disjunction.

### Dependencies
- No explicit dependencies beyond the core logical system

### Porting notes
This theorem should be easy to port to any system as it's a basic logical principle. In many proof assistants, this might already exist as a built-in rule or be trivially provable using the system's basic deduction mechanisms.

---

## RIGHT_AND_OVER_OR

### RIGHT_AND_OVER_OR

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let RIGHT_AND_OVER_OR = TAUT
  `!t1 t2 t3. (t2 \/ t3) /\ t1 <=> t2 /\ t1 \/ t3 /\ t1`;;
```

### Informal statement
This theorem states that for all propositions $t1$, $t2$, and $t3$:
$$(t2 \lor t3) \land t1 \Leftrightarrow (t2 \land t1) \lor (t3 \land t1)$$

The theorem establishes the distributivity of conjunction over disjunction from the right side.

### Informal proof
This theorem is established using the `TAUT` tactic in HOL Light, which automatically proves tautologies (propositional formulas that are always true regardless of the truth values of their variables).

The distributivity of conjunction over disjunction is a well-known property in propositional logic and can be verified using a truth table:
- When $t1$ is false, both sides of the equivalence are false
- When $t1$ is true:
  * The left side $(t2 \lor t3) \land t1$ simplifies to $t2 \lor t3$
  * The right side $(t2 \land t1) \lor (t3 \land t1)$ simplifies to $t2 \lor t3$
  * Therefore, they are equivalent

### Mathematical insight
This theorem expresses the distributivity property of conjunction over disjunction from the right side. It's a fundamental property in propositional logic that allows us to rewrite expressions in different but equivalent forms.

While the more commonly stated form of distributivity is $(t1 \land (t2 \lor t3)) \Leftrightarrow ((t1 \land t2) \lor (t1 \land t3))$ (distribution from the left), this theorem provides the analogous property for distribution from the right.

This property is important for simplifying logical expressions and is often used in formal reasoning, Boolean algebra, and circuit design.

### Dependencies
None explicitly listed, as the theorem is proven directly using the `TAUT` tactic.

---

## RIGHT_OR_OVER_AND

### RIGHT_OR_OVER_AND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RIGHT_OR_OVER_AND = TAUT
  `!t1 t2 t3. t2 /\ t3 \/ t1 <=> (t2 \/ t1) /\ (t3 \/ t1)`;;
```

### Informal statement
For any propositions $t_1$, $t_2$, and $t_3$, the following logical equivalence holds:
$$(t_2 \wedge t_3) \vee t_1 \Leftrightarrow (t_2 \vee t_1) \wedge (t_3 \vee t_1)$$

### Informal proof
This formula is a tautology in propositional logic, which means it is true under all possible truth value assignments to $t_1$, $t_2$, and $t_3$. The proof follows from the distributive property of disjunction over conjunction.

We can verify this by considering the truth tables for both sides of the equivalence:

* For any assignment of truth values to $t_1$, $t_2$, and $t_3$, if $t_1$ is true, then both sides of the equivalence are true.
* If $t_1$ is false, then the left side $(t_2 \wedge t_3) \vee t_1$ simplifies to $t_2 \wedge t_3$.
* Similarly, if $t_1$ is false, the right side $(t_2 \vee t_1) \wedge (t_3 \vee t_1)$ simplifies to $t_2 \wedge t_3$.

Therefore, the equivalence holds for all possible truth value assignments.

### Mathematical insight
This theorem expresses the distributive property of disjunction over conjunction from the right side. It is a fundamental law in propositional logic and is useful for simplifying logical expressions.

The theorem allows us to transform a disjunction with a conjunction on one side into a conjunction of disjunctions, which can be helpful in various logical manipulations, particularly in normal form conversions and formula simplifications.

This distributive property is dual to the more commonly stated distributive property of conjunction over disjunction.

### Dependencies
The theorem is proven using the `TAUT` function in HOL Light, which confirms that the statement is a tautology in propositional logic.

---

## is_type

### Name of formal statement
is_type

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let is_type = can get_type_arity;;
```

### Informal statement
`is_type` is a boolean-valued function that tests whether a given term represents a valid type in HOL Light. It is defined as:

```
is_type(t) = can get_type_arity(t)
```

where `can` is a higher-order function that tests whether a function application succeeds without raising an exception, and `get_type_arity` is a function that returns the arity of a type constructor if the input is a valid type, and raises an exception otherwise.

### Informal proof
This is a definition, not a theorem, so it does not have a proof. The definition uses the auxiliary function `can` to test whether `get_type_arity` successfully executes on the input term without raising an exception.

### Mathematical insight
The `is_type` function provides a way to test whether a term represents a valid type in the HOL Light type system. This is a fundamental utility function used throughout the HOL Light system for type checking and validation.

In HOL Light's implementation, many operations can fail by raising exceptions. The `can` combinator transforms a potentially failing operation into a boolean test, with `true` indicating success and `false` indicating failure. This pattern is common in HOL Light for predicates that test syntactic properties.

The function is used extensively in the system to verify that expressions are well-formed types before performing operations that require valid types.

### Dependencies
- `can`: A higher-order function that tests whether a function application succeeds without raising an exception.
- `get_type_arity`: A function that retrieves the arity of a type constructor if given a valid type.

### Porting notes
When porting to other proof assistants:
1. Most systems have built-in type checking that would replace this functionality
2. If implementing in a system without exceptions (like Lean or Isabelle), replace this exception-based validation with option types or explicit validity checks
3. The implementation heavily depends on HOL Light's specific representation of types, so a direct port might not be meaningful in systems with different internal representations

---

## is_constant

### is_constant
- `is_constant`

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let is_constant = can get_const_type;;
```

### Informal statement
The predicate `is_constant` determines whether a term is a constant. It checks if the term can be assigned a constant type, returning `true` if it can and `false` otherwise.

### Informal proof
This is a definition rather than a theorem, so there is no formal proof to translate. The definition uses the `can` combinator applied to the `get_const_type` function. The `can` operator turns a function that might fail into a predicate that returns `true` if the function succeeds and `false` if it fails. So `is_constant` applies `get_const_type` to its argument, and returns `true` if and only if `get_const_type` succeeds.

### Mathematical insight
This is a basic predicate used in HOL Light's term manipulation infrastructure. It provides a simple way to check if a term is a constant (as opposed to a variable, lambda abstraction, or function application). Such checks are essential when traversing or analyzing the structure of HOL Light terms during proof automation, simplification, or other meta-operations.

The definition is pragmatic: rather than using a dedicated constructor test, it leverages the existing `get_const_type` function, which already throws an exception for non-constants.

### Dependencies
- `can`: A combinator that turns a function into a predicate indicating whether the function succeeds
- `get_const_type`: A function that returns the type of a constant term, failing if the input is not a constant

### Porting notes
When porting this to other proof assistants:
- Most systems provide direct ways to test if a term is a constant, often through pattern matching on the term structure or dedicated predicates
- The implementation strategy of leveraging exception handling (`can`) is somewhat HOL Light-specific; other systems might prefer explicit constructor tests or pattern matching

---

## null

### null

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let null l = l = [];;
```

### Informal statement
The function `null` checks if a list is empty. For a list `l`, `null l` returns `true` if and only if `l` is equal to the empty list `[]`.

Formally:
$$\text{null}(l) \iff l = []$$

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
This is a standard utility function found in many programming languages and libraries. It provides a simple way to test whether a list is empty. In mathematics, this corresponds to checking if a sequence has length zero.

The name "null" is commonly used in functional programming languages to refer to this operation, especially in the Haskell and ML families of languages.

### Dependencies
No explicit dependencies beyond the primitive operations of HOL Light.

### Porting notes
This function is straightforward to port to any system that has lists. Most proof assistants have either built-in functions for this operation or provide it in standard libraries. When porting:

- In Isabelle/HOL, there is `null` in the List library
- In Coq, it might be called `is_empty` or similar in the standard library
- In Lean, `list.empty` or similar would be the equivalent

---

## type_tyvars

### type_tyvars

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let type_tyvars = type_vars_in_term o curry mk_var "x";;
```

### Informal statement
This definition `type_tyvars` extracts the type variables from a term. Specifically, it takes a term and returns the set of type variables present in the term's type.

Mathematically, given a term $x$, `type_tyvars` returns $\text{type\_vars\_in\_term}(x)$, which is the set of all type variables occurring in the type of $x$.

### Informal proof
This is a definition, not a theorem, so there's no proof to translate.

### Mathematical insight
This is a utility function for extracting type variables from a term. Type variables are crucial in HOL Light's polymorphic type system. The function is useful in various contexts where knowing the type variables of a term is important, such as type inference, polymorphic instantiation, or checking type constraints.

The implementation creates a variable named "x" with a given type using `mk_var`, then extracts the type variables from that term using `type_vars_in_term`.

### Dependencies
- `type_vars_in_term`: A function that extracts the set of type variables from a term's type
- `mk_var`: A function that creates a variable given a name and type
- `curry`: A higher-order function that transforms a function taking a pair as an argument into a function taking two arguments

### Porting notes
When porting to another proof assistant, you'll need an equivalent function that can extract type variables from terms. The implementation approach may differ based on how the target system represents polymorphic types and how it exposes its internal data structures.

---

## find_match

### Name of formal statement
find_match

### Type of the formal statement
function definition (let binding)

### Formal Content
```ocaml
let find_match u =
  let rec find_mt t =
    try term_match [] u t with Failure _ ->
    try find_mt(rator t) with Failure _ ->
    try find_mt(rand  t) with Failure _ ->
    try find_mt(snd(dest_abs t))
    with Failure _ -> failwith "find_match" in
  fun t -> let _,tmin,tyin = find_mt t in
           tmin,tyin;;
```

### Informal statement
`find_match` is a higher-order function that takes a term pattern `u` and returns a function that searches for matches of pattern `u` in a target term `t`. The returned function, when applied to `t`, returns a pair `(tmin, tyin)` where:
- `tmin` is a term-level instantiation mapping
- `tyin` is a type-level instantiation mapping

These instantiation mappings describe how to transform the pattern `u` to match a part of the term `t`.

### Informal proof
This is a function definition rather than a theorem, so there is no proof. However, the implementation works as follows:

- The inner recursive function `find_mt` attempts to match the pattern `u` against target term `t` or its subterms:
  1. First, it tries to directly match `u` against the entire term `t`
  2. If that fails, it recursively tries to match `u` against the operator part of `t` (obtained via `rator t`)
  3. If that fails, it recursively tries to match `u` against the operand part of `t` (obtained via `rand t`)
  4. If that fails, it recursively tries to match `u` against the body of `t` if `t` is an abstraction (obtained via `dest_abs t`)
  5. If all attempts fail, it raises the exception "find_match"

- The outer function takes the input pattern `u`, defines the recursive search function `find_mt`, and returns a function that:
  1. Takes a term `t`
  2. Calls `find_mt t` which returns a triple `(_, tmin, tyin)`
  3. Returns just the pair `(tmin, tyin)`, discarding the first component of the triple

### Mathematical insight
This function implements a depth-first search for pattern matching within a HOL Light term. Pattern matching is fundamental to term manipulation in theorem provers, allowing one to identify subterms that match a given pattern.

The function is particularly useful for implementing tactics and conversions that need to find instances of certain patterns within terms. Rather than just determining if a pattern matches, it returns the instantiations needed to make the pattern match, which can then be used for further term transformations.

The returned instantiation maps (`tmin` for term variables and `tyin` for type variables) capture exactly what substitutions would be needed to make the pattern `u` match the relevant part of `t`.

### Dependencies
- `term_match`: Used to attempt matching the pattern against a term
- `rator`: Extracts the operator from an application term
- `rand`: Extracts the operand from an application term
- `dest_abs`: Decomposes an abstraction into variable and body

### Porting notes
When porting this function:
1. Ensure your target system has analogous pattern matching capabilities
2. Be aware of how the target system represents instantiation maps for terms and types
3. Consider how exceptions are handled in the target system - this function uses exceptions for control flow
4. The recursive search strategy may need adjustment based on how terms are structured in the target system

---

## rec

I'll revise the documentation, specifically fixing the heading inconsistency and ensuring everything else is properly formatted.

### Name of formal statement
mk_primed_var

### Type of the formal statement
function definition (recursive)

### Formal Content
```ocaml
let rec mk_primed_var(name,ty) =
  if can get_const_type name then mk_primed_var(name^"'",ty)
  else mk_var(name,ty);;
```

### Informal statement
`mk_primed_var` is a recursive function that takes a pair `(name, ty)` where `name` is a string and `ty` is a type, and returns a variable with a modified name and the given type. The function performs the following operations:

1. It checks if `name` is already the name of a constant in the current environment using the `can get_const_type` function
2. If it is a constant name:
   - It appends a prime symbol (`'`) to `name`
   - It recursively calls itself with the new name and the same type
3. If it is not a constant name:
   - It creates and returns a variable with the name `name` and type `ty` using `mk_var`

### Informal sketch
This is a recursive function definition, not a theorem that requires a proof.

### Mathematical insight
This utility function is used for creating fresh variable names by appending prime symbols (`'`) to avoid name conflicts with existing constants. This is a common naming convention in mathematics where variables like $x'$ or $y'$ are used to denote related but distinct variables.

The function ensures that the generated variable name doesn't clash with any existing constant in the current environment. This is important in theorem provers to maintain logical consistency and avoid unintended variable capture or confusion.

This kind of name generation is particularly useful when:
- Creating fresh variables during substitution operations
- Converting bound variables to free variables
- Generating new variables during proof automation

### Dependencies
- Functions:
  - `can`: Converts exception-raising functions into boolean-returning functions
  - `get_const_type`: Retrieves the type of a named constant
  - `mk_var`: Creates a variable term with a specified name and type

### Porting notes
When porting this function:
1. Ensure your target system has an equivalent way to check if a name is already used as a constant
2. Consider how variable naming and creation are handled in the target system
3. The implementation should respect the target system's approach to name generation and collision avoidance
4. Some systems might have built-in facilities for generating fresh names, which could be used instead of this explicit approach

---

## subst_occs

### Name of formal statement
subst_occs

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let subst_occs =
  let rec subst_occs slist tm =
    let applic,noway = partition (fun (i,(t,x)) -> aconv tm x) slist in
    let sposs = map (fun (l,z) -> let l1,l2 = partition ((=) 1) l in
                                  (l1,z),(l2,z)) applic in
    let racts,rrest = unzip sposs in
    let acts = filter (fun t -> not (fst t = [])) racts in
    let trest = map (fun (n,t) -> (map (C (-) 1) n,t)) rrest in
    let urest = filter (fun t -> not (fst t = [])) trest in
    let tlist = urest @ noway in
      if acts = [] then
      if is_comb tm then
        let l,r = dest_comb tm in
        let l',s' = subst_occs tlist l in
        let r',s'' = subst_occs s' r in
        mk_comb(l',r'),s''
      else if is_abs tm then
        let bv,bod = dest_abs tm in
        let gv = genvar(type_of bv) in
        let nbod = vsubst[gv,bv] bod in
        let tm',s' = subst_occs tlist nbod in
        alpha bv (mk_abs(gv,tm')),s'
      else
        tm,tlist
    else
      let tm' = (fun (n,(t,x)) -> subst[t,x] tm) (hd acts) in
      tm',tlist in
  fun ilist slist tm -> fst(subst_occs (zip ilist slist) tm);;
```

### Informal statement
The function `subst_occs` is defined to substitute specific occurrences of subterms in a term. Given:
- `ilist`: a list of indices specifying which occurrences to substitute
- `slist`: a list of pairs `(t,x)` where each `t` is a term to substitute for the corresponding occurrence of `x`
- `tm`: the target term in which substitution takes place

The function substitutes the specified occurrences of each subtopic `x` with the corresponding term `t` in the term `tm`.

### Informal proof
This definition constructs `subst_occs` through a recursive inner function that processes each part of the term:

- The function first partitions the substitution list into applicable substitutions (where the current term matches a substitution pattern) and non-applicable ones.

- For applicable substitutions:
  - It splits occurrence indices into those that are `1` (current occurrence) and those greater than `1` (later occurrences).
  - It performs substitution if there's a current occurrence to replace (`1` in the index list).
  - It decrements indices for later occurrences since we've processed one occurrence.

- For non-applicable substitutions:
  - If the term is a function application (`is_comb`), it recursively processes both parts.
  - If the term is an abstraction (`is_abs`), it substitutes the bound variable with a fresh one, recursively processes the body, and rebuilds the abstraction.
  - Otherwise, it returns the term unchanged along with the remaining substitution list.

- The outer `subst_occs` function prepares the substitution list by zipping the indices with the substitution pairs and returns only the modified term.

### Mathematical insight
The `subst_occs` function provides fine-grained control over term substitution by allowing users to specify which occurrences of a subterm should be replaced. This is more flexible than simple substitution which would replace all occurrences.

The function handles all term constructs including function applications and abstractions, properly managing variable bindings by using alpha conversion when necessary. This ensures that substitutions don't accidentally capture free variables.

The implementation maintains an index-based tracking system to identify which occurrence of a subterm is being processed at any given point. This lets users target specific occurrences (like the 2nd or 3rd occurrence) rather than all instances.

This function is particularly useful in theorem proving when selectively rewriting parts of a goal or theorem, allowing for more precise control than global substitution operations.

### Dependencies
No explicit dependencies were provided in the input.

### Porting notes
When porting this function to other proof assistants:

1. Consider whether the target system handles term substitution differently - some systems might have built-in selective substitution facilities.

2. Ensure proper implementation of variable capture avoidance during substitution in abstractions - the function uses alpha-conversion to prevent variable capture.

3. The index-tracking mechanism might need adaptation based on how terms are traversed in the target system.

4. The implementation uses pattern matching and recursive term traversal which should be expressible in most functional languages underlying theorem provers.

---

## INST_TY_TERM(substl,insttyl)

### INST_TY_TERM

### Type of the formal statement
new_definition (function)

### Formal Content
```ocaml
let INST_TY_TERM(substl,insttyl) th =
  let th' = INST substl (INST_TYPE insttyl th) in
  if hyp th' = hyp th then th'
  else failwith "INST_TY_TERM: Free term and/or type variables in hypotheses";;
```

### Informal statement
Function `INST_TY_TERM(substl, insttyl) th` performs both term substitution and type instantiation on a theorem `th`.

Given:
- `substl`: a list of term substitutions
- `insttyl`: a list of type instantiations
- `th`: a theorem

It first applies type instantiation using `INST_TYPE insttyl th` and then applies term substitution using `INST substl` on the result. 

The function ensures that the hypotheses remain unchanged after the substitutions. If any free term variables or free type variables appear in the hypotheses after substitution, the function fails with an error message.

### Informal proof
This is a function definition rather than a theorem, so there's no formal proof. The function:

1. Applies type instantiation first with `INST_TYPE insttyl th`
2. Then applies term substitution with `INST substl` on the result
3. Checks if the hypotheses of the resulting theorem (`th'`) are the same as the original theorem (`th`)
4. If the hypotheses remain unchanged, it returns the transformed theorem `th'`
5. Otherwise, it fails with an error message indicating that free term or type variables were introduced in the hypotheses

### Mathematical insight
This function combines two common operations in HOL Light:
1. Type instantiation (`INST_TYPE`)
2. Term substitution (`INST`)

The key insight is that instantiation and substitution need to be performed carefully to maintain the logical validity of theorems. The function checks that no new assumptions are introduced through the instantiation process, which could otherwise lead to unsound reasoning.

This function is particularly useful when you need to specialize both terms and types in a theorem simultaneously, while ensuring the operation remains sound.

### Dependencies
- `INST`: Term substitution function in HOL Light
- `INST_TYPE`: Type instantiation function in HOL Light

### Porting notes
When porting this function to other proof assistants:
1. Ensure that the order of operations (type instantiation first, then term substitution) is preserved
2. Implement the hypothesis check to prevent introducing new free variables
3. Be aware that different systems may handle substitution and instantiation differently, especially regarding free variable capture

---

## RIGHT_CONV_RULE

### RIGHT_CONV_RULE

### Type of the formal statement
New definition

### Formal Content
```ocaml
let RIGHT_CONV_RULE (conv:conv) th =
  TRANS th (conv(rhs(concl th)));;
```

### Informal statement
`RIGHT_CONV_RULE` is a function that takes a conversion `conv` and a theorem `th`, and applies the conversion to the right-hand side of the conclusion of the theorem. It then returns the transitive combination of the original theorem and the result of the conversion.

Specifically, if `th` is a theorem of the form `⊢ s = t`, and `conv` is a conversion that transforms `t` into `t'` (resulting in the theorem `⊢ t = t'`), then `RIGHT_CONV_RULE conv th` produces the theorem `⊢ s = t'`.

### Informal proof
This is a definition, not a theorem, so there's no proof to translate. The implementation uses:
- `rhs(concl th)` to extract the right-hand side `t` of the theorem's conclusion
- `conv` to convert `t` to `t'`, producing a theorem `⊢ t = t'`
- `TRANS th (conv(rhs(concl th)))` to transitively combine the original theorem `⊢ s = t` with the conversion result `⊢ t = t'` to yield `⊢ s = t'`

### Mathematical insight
This is a utility function that allows for targeted transformations of the right-hand side of an equation. It's a common operation when working with equational reasoning in theorem proving.

The rule enables stepwise refinement of terms by applying conversions only to the right-hand sides of equations, which is particularly useful when building simplification chains or rewriting sequences. This helps maintain the logical flow from an original term to its final transformed version.

In practice, `RIGHT_CONV_RULE` is often used in simplification procedures, term normalization, and when chaining together equational reasoning steps in proofs.

### Dependencies
The function depends on fundamental HOL Light components:
- `TRANS`: Transitivity rule for equality
- `rhs`: Function to extract the right-hand side of an equation
- `concl`: Function to extract the conclusion of a theorem

### Porting notes
When porting to other systems:
- This is a simple utility function that should be straightforward to implement in any system that has support for transitivity of equality and the ability to analyze the structure of theorems.
- The implementation relies on the specific representation of theorems and the availability of functions to decompose equations, which might differ between systems.
- In systems with more sophisticated rewriting capabilities, this functionality might already be available through built-in tactics or rules.

---

## NOT_EQ_SYM

### NOT_EQ_SYM

### Type of the formal statement
Derived rule (function definition)

### Formal Content
```ocaml
let NOT_EQ_SYM =
  let pth = GENL [`a:A`; `b:A`]
    (GEN_REWRITE_RULE I [GSYM CONTRAPOS_THM] (DISCH_ALL(SYM(ASSUME`a:A = b`))))
  and aty = `:A` in
  fun th -> try let l,r = dest_eq(dest_neg(concl th)) in
                MP (SPECL [r; l] (INST_TYPE [type_of l,aty] pth)) th
            with Failure _ -> failwith "NOT_EQ_SYM";;
```

### Informal statement
`NOT_EQ_SYM` is a derived rule that reverses the order of terms in a negated equality. Given a theorem of the form $\vdash \lnot(a = b)$, it produces the theorem $\vdash \lnot(b = a)$.

### Informal proof
The implementation creates a parametric theorem that establishes the general principle: for all $a$ and $b$ of type $A$, if $\lnot(a = b)$ then $\lnot(b = a)$.

The proof constructs this as follows:
1. Start with the assumption $a = b$
2. Apply symmetry (`SYM`) to get $b = a$
3. Discharge all assumptions to get $a = b \Rightarrow b = a$
4. Use the contrapositive form (`GSYM CONTRAPOS_THM`) to get $\lnot(b = a) \Rightarrow \lnot(a = b)$
5. Generalize over $a$ and $b$ to get $\forall a~b.~\lnot(b = a) \Rightarrow \lnot(a = b)$

When applying this rule to a theorem $\vdash \lnot(l = r)$:
- It instantiates the parametric theorem with the specific terms $r$ and $l$ (in reverse order)
- Uses modus ponens (`MP`) to derive $\vdash \lnot(r = l)$

### Mathematical insight
This rule captures the intuitive property that the symmetry of equality extends to negated equalities as well. In classical logic, $\lnot(a = b)$ and $\lnot(b = a)$ are equivalent statements.

The function is implemented as a derived rule rather than proving a general theorem because it operates on the structure of theorems directly. This approach allows for direct manipulation of negated equalities in HOL Light proofs without needing explicit rewrite steps.

### Dependencies
- `CONTRAPOS_THM`: The contrapositive theorem stating $(\phi \Rightarrow \psi) \Rightarrow (\lnot\psi \Rightarrow \lnot\phi)$
- `SYM`: The symmetry rule for equality which converts $a = b$ to $b = a$

### Porting notes
When porting this to other systems:
- In systems with more powerful rewrite engines, this might be unnecessary as the symmetry of equality may be automatically applied.
- The implementation uses HOL Light's direct theorem manipulation style. In systems like Lean or Coq, this would likely be implemented as a lemma and tactic rather than a derived rule.
- Pay attention to how the type variables are instantiated - this implementation handles polymorphic types properly.

---

## NOT_MP

### Name of formal statement
NOT_MP

### Type of the formal statement
Utility function (ML implementation)

### Formal Content
```ocaml
let NOT_MP thi th =
  try MP thi th with Failure _ ->
  try let t = dest_neg (concl thi) in
      MP(MP (SPEC t F_IMP) thi) th
  with Failure _ -> failwith "NOT_MP";;
```

### Informal statement
`NOT_MP` is a utility function that performs a logical operation between two theorems. Given two theorems `thi` and `th`, it attempts one of the following actions:

1. First, it tries to apply Modus Ponens (`MP`) directly between `thi` and `th`.
2. If that fails, it attempts to treat `thi` as a negation theorem (of form `¬t`), and applies a specialized version of Modus Ponens using the theorem `¬t ⇒ (t ⇒ F)`.
3. If both attempts fail, it raises the "NOT_MP" failure message.

### Informal proof
This is an ML implementation rather than a theorem with a formal proof. The function implements the following logic:

1. First attempt: Try standard Modus Ponens between the theorems `thi` and `th`.
2. If the first attempt fails (caught by exception handling):
   - Extract the negated term `t` from the conclusion of `thi`, which should be of the form `¬t`
   - Apply the theorem `¬t ⇒ (t ⇒ F)` specialized to the term `t` (via `SPEC t F_IMP`)
   - Use this specialized theorem with `thi` to create an intermediate result
   - Apply Modus Ponens between this intermediate result and `th`
3. If either extraction fails or the second MP fails, raise the "NOT_MP" failure.

The function effectively provides a way to use a negated theorem in a Modus Ponens operation by leveraging the logical equivalence between `¬t` and `t ⇒ F`.

### Mathematical insight
This utility function implements a derived rule of inference that extends the standard Modus Ponens rule to work with negation. The key insight is that a negation `¬t` is logically equivalent to the implication `t ⇒ F` (falsum). 

The function is particularly useful in automated reasoning and proof simplification, as it allows for direct application of negated theorems in inference chains without requiring separate transformation steps. It encapsulates the common pattern where we want to use a negated premise to derive a contradiction or further implications.

The implementation handles potential failures gracefully, making it robust for use in larger proof automation tactics.

### Dependencies
#### Theorems
- `F_IMP`: Likely represents the theorem `⊢ ∀p. (¬p ⇔ (p ⇒ F))` or similar

#### Built-in functions
- `MP`: Standard Modus Ponens operation
- `SPEC`: Specializes a universally quantified theorem
- `dest_neg`: Destructor function for negation
- `concl`: Returns the conclusion of a theorem

### Porting notes
When porting to other proof assistants:
- Ensure the target system has equivalent exception handling mechanisms
- The target system should support a similar notion of Modus Ponens and negation handling
- Check if the target system already has a built-in function with similar functionality
- The equivalence `¬p ⇔ (p ⇒ F)` is standard in most logical systems, but the specific theorem might have a different name

---

## FORALL_EQ

### FORALL_EQ
- `FORALL_EQ`

### Type of the formal statement
- Inference rule/tactic

### Formal Content
```ocaml
let FORALL_EQ x =
  let mkall = AP_TERM (mk_const("!",[type_of x,mk_vartype "A"])) in
  fun th -> try mkall (ABS x th)
            with Failure _ -> failwith "FORALL_EQ";;
```

### Informal statement
This is a function that takes a variable `x` and a theorem `th`, and returns a new theorem where the variable `x` is universally quantified. Specifically:

Given a variable `x` and a theorem `th` of the form `Γ |- t`, where `t` potentially contains free occurrences of `x`, it produces a new theorem of the form `Γ |- ∀x. t`.

The function works by:
1. Creating a universal quantifier term with the appropriate type 
2. Using functional application to bind the variable in an abstraction

### Informal proof
This is not a theorem but a derived inference rule implemented as a Higher Order Logic function. The implementation:

1. First creates a term representing the universal quantifier (`∀`) with the appropriate types:
   - Takes `x`'s type and an arbitrary type `A` representing the body's type
   - Creates a constant for the universal quantifier with these types

2. Returns a function that:
   - Takes a theorem `th`
   - Tries to create an abstraction `λx. th` using the HOL Light `ABS` function
   - Applies the universal quantifier to this abstraction using `AP_TERM`
   - Returns the resulting theorem `Γ |- ∀x. t`
   - Fails with an appropriate error message if the operation is not possible

### Mathematical insight
This inference rule implements universal generalization, which is a fundamental rule in higher-order logic:
- It allows moving from a proven statement `t` to its universally quantified form `∀x. t`
- This corresponds to the introduction rule for universal quantifiers in natural deduction

The function is designed to maintain logical soundness by ensuring that appropriate abstraction conditions are met (which is why it has error handling).

### Dependencies
None explicitly listed, but implicitly uses:
- `AP_TERM`: A basic inference rule in HOL Light that applies a function to both sides of an equation
- `ABS`: An inference rule for creating lambda abstractions

### Porting notes
When porting to another proof assistant:
- Ensure proper handling of variable capture and free variables in the theorem
- Some systems may have built-in universal generalization rules that could be used directly
- The error handling might need to be adapted to the target system's conventions
- The implementation details will vary based on how the target system represents and manipulates quantifiers

---

## EXISTS_EQ

### EXISTS_EQ
- EXISTS_EQ

### Type of the formal statement
- Theorem or function

### Formal Content
```ocaml
let EXISTS_EQ x =
  let mkex = AP_TERM (mk_const("?",[type_of x,mk_vartype "A"])) in
  fun th -> try mkex (ABS x th)
            with Failure _ -> failwith "EXISTS_EQ";;
```

### Informal statement
The function `EXISTS_EQ` implements existential quantification over an equation. Given a variable `x` and a theorem `th` containing an equation where `x` appears as a free variable, `EXISTS_EQ x th` produces a new theorem that wraps the equation in `th` with an existential quantifier for `x`.

Mathematically, if `th` is a theorem stating $t_1 = t_2$ where `x` appears free in either $t_1$ or $t_2$, then `EXISTS_EQ x th` corresponds to the theorem $\exists x. (t_1 = t_2)$.

### Informal proof
This is an implementation function rather than a theorem with a proof. It works as follows:

1. First, it creates a function `mkex` that applies the existential quantifier operator to an abstraction.
2. Given a theorem `th`, it:
   - Creates an abstraction `ABS x th` that binds the variable `x` in the theorem
   - Applies the existential quantifier to this abstraction using `mkex`
   - Returns the resulting theorem representing $\exists x. (t_1 = t_2)$
3. If the abstraction fails (e.g., if `x` is not a free variable in the theorem), it returns an error.

### Mathematical insight
This function implements existential quantification over equations, which is a fundamental operation in formal logic and theorem proving. It's part of HOL Light's core infrastructure for manipulating quantified formulas.

The key insight is that existential quantification can be viewed as an operation on abstractions. The function creates the abstraction $\lambda x. (t_1 = t_2)$ and then applies the existential quantifier to it, yielding $\exists x. (t_1 = t_2)$.

This operation follows the standard logical rule that if we know some property holds for a specific value, we can deduce that there exists a value for which the property holds.

### Dependencies
- `AP_TERM` - Function that applies a function term to both sides of an equation
- `ABS` - Function that creates a lambda abstraction

### Porting notes
When porting this function:
- Ensure the target system can handle abstractions and applications properly
- Pay attention to how existential quantifiers are represented in the target system
- Consider error handling for the case where the variable isn't free in the theorem
- Note that this implementation uses higher-order abstract syntax (applying a quantifier to an abstraction), which might need to be adapted in systems with different approaches to binding

---

## SELECT_EQ

### SELECT_EQ
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- Function definition

### Formal Content
```ocaml
let SELECT_EQ x =
  let mksel = AP_TERM (mk_const("@",[type_of x,mk_vartype "A"])) in
  fun th -> try mksel (ABS x th)
            with Failure _ -> failwith "SELECT_EQ";;
```

### Informal statement
The function `SELECT_EQ` is a derived rule for constructing a theorem using Hilbert's choice operator (`@`). Specifically:

Given a variable `x` and a theorem `th` that proves a proposition involving `x`, `SELECT_EQ x th` returns a theorem where the variable `x` has been replaced by a term of the form `(@x. P[x])` where `P[x]` is the proposition in `th`.

Mathematically, it converts a theorem of the form `⊢ P[x]` to `⊢ P[(@x. P[x])]`, where `@x. P[x]` represents "the `x` such that `P[x]`" using Hilbert's choice operator.

### Informal proof
This is a function definition rather than a theorem, so it doesn't have a proof in the traditional sense. The implementation:

1. Creates a function `mksel` that applies the Hilbert choice operator (`@`) to a lambda abstraction
2. Returns a function that:
   - Takes a theorem `th`
   - Abstracts the variable `x` from the theorem using `ABS x th`
   - Applies `mksel` to the resulting abstraction
   - Returns the resulting theorem
   - Handles failure by raising a "SELECT_EQ" error

### Mathematical insight
This function implements a formalization of the Hilbert choice principle that allows selecting a witness for a proven statement. The key insight is that if we can prove `P[x]` for some `x`, then we can replace `x` with "the specific `x` such that `P[x]`" (written as `@x. P[x]`), and the theorem remains valid.

The function is particularly useful in formal developments because:
1. It allows moving from existential statements to specific witnesses
2. It helps in defining functions where the output is characterized by a property
3. It bridges the gap between existence proofs and constructions

The Hilbert choice operator is a powerful but non-constructive tool - it asserts the existence of a selection function without providing an algorithm for it.

### Dependencies
- Relies on the HOL Light implementation of the choice operator (`@`)
- Uses the `ABS` function for lambda abstraction
- Uses the `AP_TERM` function for applying a function to terms in theorems

### Porting notes
When porting this to other proof assistants:
1. In systems with different choice implementations than HOL (like Coq or Lean), you'll need to use their equivalent axioms or constructs for selection
2. Some systems might require explicit type annotations for the choice operator
3. Systems without built-in choice operators might require additional axioms or the construction of choice principles
4. The error handling approach may need adaptation to match the target system's conventions

---

## RIGHT_BETA

### RIGHT_BETA

### Type of the formal statement
Theorem (transformation function)

### Formal Content
```ocaml
let RIGHT_BETA th =
  try TRANS th (BETA_CONV(rhs(concl th)))
  with Failure _ -> failwith "RIGHT_BETA";;
```

### Informal statement
`RIGHT_BETA` is a transformation function that takes a theorem `th` of the form `⊢ t = t'` where `t'` contains a beta-redex (a function application that can be simplified), and returns the theorem `⊢ t = t''` where `t''` is the result of performing beta-reduction on `t'`.

Specifically, if `th` is a theorem of the form `⊢ t = t'`, then `RIGHT_BETA th` returns `⊢ t = t''` where `t''` is obtained from `t'` by beta-reducing any beta-redexes in `t'`.

### Informal proof
The function works as follows:

- Given an input theorem `th` of the form `⊢ t = t'`
- First, it attempts to apply the `TRANS` function to `th` and the result of applying `BETA_CONV` to the right-hand side of `th`
- The `TRANS` function combines two theorems: `⊢ t = t'` and `⊢ t' = t''` to get `⊢ t = t''`
- The `BETA_CONV` function performs beta-reduction on a term, returning a theorem of the form `⊢ term = reduced_term`
- If this process fails (e.g., if there's no beta-redex in the right-hand side), it raises a "RIGHT_BETA" failure message

This is essentially combining transitivity of equality with beta-reduction on the right-hand side of an equation.

### Mathematical insight
`RIGHT_BETA` is a tactical function that automates the application of beta-reduction (function application) to the right-hand side of an equation. Beta-reduction is one of the fundamental computation rules in lambda calculus and functional programming.

This transformation is particularly useful in simplification steps during proofs, allowing for the evaluation of function applications on the right side of equations without requiring separate lemmas or multiple proof steps.

The function encapsulates a common pattern in proofs involving higher-order logic: applying computational rules to unfold definitions or simplify expressions after substitutions have been made.

### Dependencies
- Core HOL Light functions:
  - `TRANS`: Transitivity of equality
  - `BETA_CONV`: Beta-reduction conversion
  - `rhs`: Extracts the right-hand side of an equation
  - `concl`: Extracts the conclusion of a theorem

### Porting notes
When porting to other proof assistants:
- Most theorem provers have similar functionality for transitivity of equality and beta-reduction
- The implementation relies on exception handling for control flow, which might need to be implemented differently in systems without exception mechanisms
- In systems with more advanced rewriting capabilities, this functionality might be subsumed by more general rewriting tactics

---

## rec

### Name of formal statement
LIST_BETA_CONV

### Type of the formal statement
Conversion function (recursive algorithm)

### Formal Content
```ocaml
let rec LIST_BETA_CONV tm =
  try let rat,rnd = dest_comb tm in
      RIGHT_BETA(AP_THM(LIST_BETA_CONV rat)rnd)
  with Failure _ -> REFL tm;;
```

### Informal statement
`LIST_BETA_CONV` is a recursive conversion function that performs beta-reduction on terms containing nested function applications. Given a term $t$, it recursively beta-reduces any function applications within $t$ by:
1. Attempting to decompose $t$ into a function part `rat` and an argument part `rnd`
2. Recursively applying itself to the function part
3. Applying the resulting conversion to the argument part
4. If the decomposition fails (i.e., $t$ is not a function application), it returns the reflexivity theorem for $t$

### Informal proof
This is a recursive algorithm definition, not a theorem with a proof. The algorithm works as follows:

- Given a term $t$, it attempts to decompose it as $t = f(x)$ where $f$ is the function part (`rat`) and $x$ is the argument part (`rnd`)
- If successful:
  1. It recursively applies `LIST_BETA_CONV` to the function part $f$, producing a theorem of the form $\vdash f = f'$
  2. It then uses `AP_THM` to apply this theorem to the argument $x$, giving $\vdash f(x) = f'(x)$
  3. Finally, it uses `RIGHT_BETA` to perform beta-reduction if possible
- If the term cannot be decomposed as a function application (the `with Failure _` case), it simply returns the reflexivity theorem $\vdash t = t$

### Mathematical insight
`LIST_BETA_CONV` implements a strategy for beta-reducing nested function applications in HOL Light terms. It works by recursively reducing the function part of applications before applying beta-reduction to the entire application. This ensures that beta-reduction is performed from the inside out, which is often more efficient than a naive approach.

The conversion is particularly useful for handling terms with multiple nested applications, as it ensures that beta-reductions are performed at all levels of the term structure. This is a building block for more complex term simplification and evaluation in the proof assistant.

### Dependencies
- Conversions:
  - `REFL`: Creates a reflexivity theorem $\vdash t = t$
  - `AP_THM`: Applies a conversion to a function in an application
  - `RIGHT_BETA`: Performs beta-reduction on the right side of an equation

### Porting notes
When porting this function to other proof assistants:
1. Consider how the target system handles term decomposition and beta-reduction
2. Most systems have built-in utilities for beta-reduction, but may implement them differently
3. The error handling through the `try-with` mechanism might need adaptation depending on how the target system manages exceptions or failure cases
4. The recursive structure is straightforward and should be maintainable across different systems

---

## RIGHT_LIST_BETA

### RIGHT_LIST_BETA
- RIGHT_LIST_BETA

### Type of the formal statement
- Definition of a function (conversion function)

### Formal Content
```ocaml
let RIGHT_LIST_BETA th = TRANS th (LIST_BETA_CONV(snd(dest_eq(concl th))));;
```

### Informal statement
The function `RIGHT_LIST_BETA` takes a theorem `th` of the form `Γ ⊢ t = s` and performs a beta-reduction on any applications of list combinators in `s` (the right-hand side of the equation). It returns a new theorem that is the result of transitively combining `th` with the result of applying `LIST_BETA_CONV` to the right-hand side of the conclusion of `th`.

In other words, if `th` is the theorem `Γ ⊢ t = s`, then `RIGHT_LIST_BETA th` returns the theorem `Γ ⊢ t = s'` where `s'` is the beta-reduced form of `s` with respect to list combinators.

### Informal proof
This is a definition, not a theorem, so it doesn't have a proof. The definition specifies that:

1. Given a theorem `th`, we extract the right-hand side of the equation in its conclusion using `dest_eq(concl th)`.
2. We apply `LIST_BETA_CONV` to that right-hand side to perform beta-reduction on list combinators.
3. We use the `TRANS` rule to transitively combine the original theorem with the result of applying `LIST_BETA_CONV`, yielding a new theorem that equates the left-hand side of the original theorem with the beta-reduced form of the right-hand side.

### Mathematical insight
This function is a utility for simplifying theorems by beta-reducing list combinators on the right-hand side of equations. It's particularly useful in simplification procedures or in contexts where you have derived an equation and want to simplify its right-hand side to obtain a more canonical or readable form.

The function is part of HOL Light's infrastructure for manipulating theorems involving list operations. It automates a common pattern: taking a theorem of the form `t = s` and rewriting it to `t = s'` where `s'` is a simplified version of `s`.

### Dependencies
- Conversion functions:
  - `LIST_BETA_CONV`: Performs beta-reduction on applications of list combinators
- Theorem manipulation functions:
  - `TRANS`: Transitive property of equality
  - `dest_eq`: Destructs an equation, extracting its left and right sides
  - `concl`: Extracts the conclusion of a theorem

### Porting notes
When porting this function to another proof assistant:
1. You need to ensure that the target system has equivalent functionality for beta-reduction of list combinators (equivalent to `LIST_BETA_CONV`).
2. The function relies on the ability to extract parts of theorems and recombine them, which is a standard capability in most proof assistants but may have different syntax.
3. In strongly typed systems, you may need to add explicit type annotations when extracting and manipulating the parts of the theorem.

---

## LIST_CONJ

### Name of formal statement
LIST_CONJ

### Type of the formal statement
Theorem (Definition)

### Formal Content
```ocaml
let LIST_CONJ = end_itlist CONJ ;;
```

### Informal statement
`LIST_CONJ` is a function that converts a list of theorems into a single theorem consisting of the conjunction of all theorems in the list.

Given a list of theorems $[A_1, A_2, \ldots, A_n]$, `LIST_CONJ` returns the theorem $A_1 \land A_2 \land \ldots \land A_n$.

More specifically, `LIST_CONJ` applies the `CONJ` operator (which conjoins two theorems) to the elements of the list using `end_itlist`, which folds a binary operation from right to left over a list.

### Informal proof
This is a definition rather than a theorem that needs to be proven. The definition uses:

- `end_itlist`: A function that applies a binary operation to elements of a list from right to left
- `CONJ`: A theorem constructor that takes theorems $A$ and $B$ and returns the theorem $A \land B$

The definition `LIST_CONJ = end_itlist CONJ` means that for a list `[t1; t2; ...; tn]`, it will apply `CONJ` as follows:
$\text{CONJ}\ t1\ (\text{CONJ}\ t2\ (\ldots (\text{CONJ}\ t_{n-1}\ t_n) \ldots))$

This creates a right-associative conjunction of all theorems in the list.

### Mathematical insight
`LIST_CONJ` provides a convenient way to combine multiple theorems into a single theorem by conjoining them. This is particularly useful when:

1. You want to bundle related theorems together
2. You need to pass multiple facts to a tactic or conversion that accepts only a single theorem
3. You are building a larger proof where the conjunction will later be broken down using `CONJUNCT1` and `CONJUNCT2`

The definition uses `end_itlist` rather than `itlist` to ensure that the conjunction is built from right to left, which is a common convention in HOL Light. The function handles the empty list case through `end_itlist`, which will raise an exception for an empty list since conjunctions must have at least one conjunct.

### Dependencies
#### Functions
- `end_itlist`: Fold a binary operation over a list from right to left
- `CONJ`: Create a conjunction from two theorems

### Porting notes
When porting to other proof assistants:

1. Most systems have similar list-folding operations (e.g., `foldr` in Lean, `fold_right` in Coq)
2. The `CONJ` operation might be named differently or have different syntax
3. Consider how the empty list case should be handled - in HOL Light it raises an exception, but other systems might prefer to return a default value or use an option type
4. Some systems might prefer to use a left-associative conjunction, which would require `itlist` instead of `end_itlist`

---

## rec

### Name of formal statement
CONJ_LIST

### Type of the formal statement
Function definition (let rec)

### Formal Content
```ocaml
let rec CONJ_LIST n th =
  try if n=1 then [th] else (CONJUNCT1 th)::(CONJ_LIST (n-1) (CONJUNCT2 th))
  with Failure _ -> failwith "CONJ_LIST";;
```

### Informal statement
`CONJ_LIST` is a recursive function that takes a natural number `n` and a theorem `th` as inputs, and returns a list of theorems by splitting a conjunction into its components.

More specifically, if `th` is a theorem of the form $A_1 \wedge (A_2 \wedge (\ldots \wedge A_n))$, then `CONJ_LIST n th` returns the list $[A_1, A_2, \ldots, A_n]$.

The function handles the following cases:
- If `n = 1`, it returns a singleton list containing just `th`.
- If `n > 1`, it recursively breaks down the conjunction by:
  1. Taking the first conjunct using `CONJUNCT1 th` (which gives $A_1$)
  2. Taking the remaining conjuncts using `CONJUNCT2 th` (which gives $A_2 \wedge (\ldots \wedge A_n)$)
  3. Recursively applying itself to get the remaining `n-1` conjuncts

If the function fails (typically because `th` does not have enough conjuncts or is not a conjunction), it raises the "CONJ_LIST" failure message.

### Informal proof
This is a recursive function definition rather than a theorem, so there is no proof to translate.

### Mathematical insight
`CONJ_LIST` provides a convenient utility for working with conjunctions in HOL Light. When dealing with a theorem that consists of multiple conjoined statements, this function allows you to split it into a list of individual theorems, each corresponding to one conjunct.

The function assumes a right-associative structure of conjunctions, which is the standard representation in HOL Light. That is, a conjunction $A_1 \wedge A_2 \wedge A_3 \wedge \ldots \wedge A_n$ is internally represented as $A_1 \wedge (A_2 \wedge (A_3 \wedge (\ldots \wedge A_n)))$.

This function is particularly useful when you have proved a theorem with multiple conjoined statements and need to use each of those statements separately.

### Dependencies
#### Theorem manipulation functions
- `CONJUNCT1` - Extracts the first conjunct from a conjunction
- `CONJUNCT2` - Extracts the second conjunct from a conjunction

### Porting notes
When porting this function to other proof assistants:
1. Ensure that the target system has equivalent functions to `CONJUNCT1` and `CONJUNCT2` for breaking down conjunctions.
2. Consider how the target system represents conjunctions (right-associative, left-associative, or flat lists).
3. The error handling mechanism will likely need to be adapted to match the error handling style of the target system.
4. Some systems might already have built-in functions for splitting conjunctions into lists, making this function unnecessary.

---

## rec

### BODY_CONJUNCTS

### Type of the formal statement
- Function definition (let rec)

### Formal Content
```ocaml
let rec BODY_CONJUNCTS th =
  if is_forall(concl th) then
    BODY_CONJUNCTS (SPEC_ALL th) else
  if is_conj (concl th) then
      BODY_CONJUNCTS (CONJUNCT1 th) @ BODY_CONJUNCTS (CONJUNCT2 th)
  else [th];;
```

### Informal statement
The `BODY_CONJUNCTS` function takes a theorem `th` as input and returns a list of theorems by:
1. First recursively eliminating all universal quantifiers from the conclusion of the theorem by applying the `SPEC_ALL` function.
2. Then recursively breaking down any conjunctions in the conclusion of the resulting theorem by applying `CONJUNCT1` and `CONJUNCT2` functions.
3. If the conclusion is neither universally quantified nor a conjunction, it returns a singleton list containing the theorem.

### Informal proof
This is a recursive function definition, not a theorem with a proof. The function works recursively in the following way:

- Base case: If the conclusion of the theorem is neither a universal quantification nor a conjunction, return the theorem as a singleton list.
- Recursive cases:
  - If the conclusion of `th` is universally quantified (detected with `is_forall`), apply `SPEC_ALL` to instantiate all universal quantifiers and recursively call `BODY_CONJUNCTS` on the result.
  - If the conclusion of `th` is a conjunction (detected with `is_conj`), split it using `CONJUNCT1` and `CONJUNCT2` to get both conjuncts, recursively call `BODY_CONJUNCTS` on each conjunct, and concatenate the resulting lists.

### Mathematical insight
The `BODY_CONJUNCTS` function is a utility that extracts all the "atomic" theorems from a compound theorem containing universal quantifications and conjunctions. This is useful for theorem proving and simplification as it allows working with individual components of a complex statement.

The function can be seen as "flattening" a tree of conjunctions after eliminating universal quantifiers, turning nested conjunctions into a flat list of individual theorems. This is a common operation in interactive theorem provers where breaking down complex statements into simpler components facilitates further reasoning.

### Dependencies
- **HOL Light core functions**:
  - `is_forall`: Tests if a term is a universal quantification
  - `concl`: Extracts the conclusion of a theorem
  - `SPEC_ALL`: Specializes all universal quantifiers in a theorem
  - `is_conj`: Tests if a term is a conjunction
  - `CONJUNCT1`: Extracts the first part of a conjunction
  - `CONJUNCT2`: Extracts the second part of a conjunction

### Porting notes
When porting to other proof assistants:
1. Ensure the target system has equivalent functions for manipulating theorems (extracting conclusions, testing term structure, etc.)
2. In some systems, the handling of theorems might differ - rather than operating directly on theorems, you might need to work with tactics or explicit proof terms
3. Consider how the target system represents lists of theorems - some systems might prefer sequences or other collection types
4. The recursive structure should be preserved, but the implementation details may vary depending on the theorem representation in the target system

---

## rec

### Name of formal statement
IMP_CANON

### Type of the formal statement
Function definition

### Formal Content
```ocaml
let rec IMP_CANON th =
    let w = concl th in
    if is_conj w then IMP_CANON (CONJUNCT1 th) @ IMP_CANON (CONJUNCT2 th)
    else if is_imp w then
        let ante,conc = dest_neg_imp w in
        if is_conj ante then
            let a,b = dest_conj ante in
            IMP_CANON
            (DISCH a (DISCH b (NOT_MP th (CONJ (ASSUME a) (ASSUME b)))))
        else if is_disj ante then
            let a,b = dest_disj ante in
            IMP_CANON (DISCH a (NOT_MP th (DISJ1 (ASSUME a) b))) @
            IMP_CANON (DISCH b (NOT_MP th (DISJ2 a (ASSUME b))))
        else if is_exists ante then
            let x,body = dest_exists ante in
            let x' = variant (thm_frees th) x in
            let body' = subst [x',x] body in
            IMP_CANON
            (DISCH body' (NOT_MP th (EXISTS (ante, x') (ASSUME body'))))
        else
        map (DISCH ante) (IMP_CANON (UNDISCH th))
    else if is_forall w then
        IMP_CANON (SPEC_ALL th)
    else [th];;
```

### Informal statement
`IMP_CANON` is a recursive function that canonicalizes a theorem by breaking down complex implication structures into a list of simpler theorems. Given a theorem `th`, it processes it according to the following cases:

1. If the conclusion of `th` is a conjunction `A ∧ B`, it returns the concatenation of canonicalizing both conjuncts separately.

2. If the conclusion is an implication `ante ⇒ conc`, it further examines the antecedent:
   - If `ante` is a conjunction `a ∧ b`, it transforms into a version with separate assumptions.
   - If `ante` is a disjunction `a ∨ b`, it splits into cases for each disjunct.
   - If `ante` is an existential `∃x. body`, it instantiates with a variant of `x` and processes.
   - Otherwise, it processes the result of assuming `ante`.

3. If the conclusion is a universal quantification `∀x. P(x)`, it specializes the theorem and recursively canonicalizes.

4. Otherwise, it returns a singleton list containing the theorem itself.

### Informal proof
This function definition provides a constructive algorithm for converting theorems into canonical form rather than proving a property. The implementation follows these key steps:

- For conjunctions, it recursively processes each conjunct and combines the results.
- For implications with complex antecedents, it applies logical transformations to break them down:
  - `(A ∧ B) ⇒ C` becomes separate theorems `A ⇒ (B ⇒ C)`
  - `(A ∨ B) ⇒ C` becomes separate theorems for each case: `A ⇒ C` and `B ⇒ C`
  - `(∃x. P(x)) ⇒ C` becomes `P(x') ⇒ C` with a fresh variable `x'`
- For universally quantified theorems, it applies universal instantiation first
- Base case: theorems that don't match any of the complex patterns are returned as-is

Each transformation preserves logical equivalence through the application of HOL Light's primitive inference rules.

### Mathematical insight
`IMP_CANON` implements a logical normalization process that converts theorems into a canonical form suitable for automated reasoning. The function systematically breaks down complex logical structures (conjunctions, disjunctions, existentials in antecedents) into simpler implications that are easier to work with.

This transformation is particularly useful for:
1. Simplifying theorems for proof automation
2. Preparing theorems for use in resolution or other inference methods
3. Making logical dependencies more explicit by separating complex premises

The function effectively implements part of the normalization process used in converting formulas to conjunctive normal form (CNF), but working at the theorem level rather than just the formula level.

### Dependencies
#### Theorems
- Not explicitly listed in dependencies, but using:
  - `CONJUNCT1`, `CONJUNCT2` - Extract theorems from a conjunction
  - `NOT_MP` - Apply modus ponens involving a negation
  - `CONJ`, `DISJ1`, `DISJ2` - Logical connective introduction rules
  - `EXISTS` - Existential introduction rule
  - `DISCH` - Discharge an assumption
  - `UNDISCH` - Remove an implication by assuming the antecedent
  - `SPEC_ALL` - Specialize all universal quantifiers

#### Functions
- `concl` - Extract the conclusion of a theorem
- `is_conj`, `is_imp`, `is_disj`, `is_exists`, `is_forall` - Type predicates
- `dest_neg_imp`, `dest_conj`, `dest_disj`, `dest_exists` - Destructors
- `variant`, `thm_frees`, `subst` - Variable manipulation functions

### Porting notes
When porting to other proof assistants:
1. Consider how the target system handles theorem manipulation - HOL Light treats theorems as first-class values that can be transformed and combined, which isn't universal across all systems.
2. Be aware that the function manipulates the structure of theorems directly, which may require different approaches in systems with different proof representations.
3. The variable renaming with `variant` ensures fresh variables - equivalent functionality will be needed in the target system.
4. The recursion pattern might need explicit termination proof in systems with stricter termination checking.

---

## LIST_MP

### LIST_MP
- `LIST_MP`

### Type of the formal statement
- Function definition

### Formal Content
```ocaml
let LIST_MP  = rev_itlist (fun x y -> MP y x);;
```

### Informal statement
The function `LIST_MP` applies modus ponens iteratively through a list of theorems.

Given a list of theorems `[thm₁, thm₂, ..., thmₙ]`, it applies modus ponens (MP) in sequence:
- Starting with theorem thmₙ
- For each theorem thmᵢ in the list (moving from right to left), it applies modus ponens (MP) with the current theorem as the first argument and thmᵢ as the second argument

Specifically, it computes:
```
MP (... (MP (MP thmₙ thmₙ₋₁) thmₙ₋₂) ...) thm₁
```

### Informal proof
This is a direct definition using `rev_itlist`, which applies a given binary function to a list in right-to-left order. In this case, the binary function is a variant of modus ponens where the arguments are reversed: `fun x y -> MP y x`.

### Mathematical insight
This utility function implements sequentially chaining multiple implications together. When given a list of theorems where:
- `thm₁` proves `A₁`
- `thm₂` proves `A₁ ⇒ A₂`
- `thm₃` proves `A₂ ⇒ A₃`
- etc.

Applying `LIST_MP` to this list yields a theorem proving the final conclusion `Aₙ`.

This is useful because it automates a common pattern in natural deduction proofs where multiple implications need to be chained together. It's more concise than writing multiple sequential applications of modus ponens.

### Dependencies
- Standard list functions:
  - `rev_itlist` - A right-to-left fold function
- Logical inference rules:
  - `MP` - The modus ponens rule

### Porting notes
When porting to other systems:
1. Most systems will have a similar fold or iteration function like `rev_itlist`, but the argument order might differ
2. In some systems, you might need to handle empty lists specifically
3. The order of arguments in MP might need to be adjusted to match the target system's implementation

---

## DISJ_IMP

### Name of formal statement
DISJ_IMP

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DISJ_IMP =
  let pth = TAUT`!t1 t2. t1 \/ t2 ==> ~t1 ==> t2` in
  fun th ->
    try let a,b = dest_disj(concl th) in MP (SPECL [a;b] pth) th
    with Failure _ -> failwith "DISJ_IMP";;
```

### Informal statement
For any propositions $t_1$ and $t_2$, `DISJ_IMP` is a rule that transforms a theorem of the form $t_1 \lor t_2$ into the implication $\lnot t_1 \Rightarrow t_2$.

### Informal proof
The proof involves the following steps:

1. First, the proof uses the tautology $\forall t_1, t_2 : (t_1 \lor t_2) \Rightarrow (\lnot t_1 \Rightarrow t_2)$ which is stored as `pth`.

2. Given a theorem `th` with conclusion of form $t_1 \lor t_2$, the function:
   - Extracts the disjuncts $t_1$ and $t_2$ using `dest_disj`
   - Specializes the tautology `pth` with $t_1$ and $t_2$ using `SPECL [a;b] pth`
   - Applies modus ponens (`MP`) with the original theorem `th` to obtain $\lnot t_1 \Rightarrow t_2$

3. If the conclusion of `th` is not a disjunction, the function fails with an appropriate error message.

### Mathematical insight
This is a fundamental rule of inference derived from the disjunctive syllogism. The function implements the logical principle that if we know $t_1 \lor t_2$ is true, then when $t_1$ is false, $t_2$ must be true. 

This rule is particularly useful in proof automation and case analysis, where we often need to transform disjunctions into implications to proceed with different branches of a proof. It's a basic building block for more complex proof strategies in automated theorem proving.

### Dependencies
#### Theorems
- `TAUT` - Used to create the tautology that forms the basis of this rule
- `MP` - Modus ponens rule
- `SPECL` - Rule for specializing universal quantifiers with specific terms

### Porting notes
This function should be straightforward to port to other proof assistants:
- It relies on basic propositional logic rules available in most systems
- The main challenge might be in handling the pattern matching and error handling that occurs when the conclusion isn't a disjunction
- In Lean or Coq, this might be implemented as a tactic rather than a function

---

## IMP_ELIM

### Name of formal statement
IMP_ELIM

### Type of the formal statement
Theorem (conversion function)

### Formal Content
```ocaml
let IMP_ELIM =
  let pth = TAUT`!t1 t2. (t1 ==> t2) ==> ~t1 \/ t2` in
  fun th ->
    try let a,b = dest_imp(concl th) in MP (SPECL [a;b] pth) th
    with Failure _ -> failwith "IMP_ELIM";;
```

### Informal statement
`IMP_ELIM` is a conversion function that transforms a theorem of the form $\vdash t_1 \Rightarrow t_2$ into the equivalent theorem $\vdash \lnot t_1 \lor t_2$.

### Informal proof
The proof constructs a conversion function using the tautology $\forall t_1, t_2: (t_1 \Rightarrow t_2) \Rightarrow (\lnot t_1 \lor t_2)$:

1. First, a theorem `pth` is defined using `TAUT` that establishes the propositional tautology:
   $\forall t_1, t_2: (t_1 \Rightarrow t_2) \Rightarrow (\lnot t_1 \lor t_2)$

2. For a theorem `th` with conclusion of the form $t_1 \Rightarrow t_2$:
   - The function extracts the antecedent $t_1$ and consequent $t_2$ using `dest_imp`
   - It then specializes the tautology to these specific terms using `SPECL [a;b] pth`
   - Finally, it applies modus ponens (`MP`) with the specialized tautology and the original theorem `th`
   
3. If the theorem's conclusion is not an implication, the function fails with an error message.

### Mathematical insight
This conversion implements the logical equivalence between implication and disjunction, specifically the transformation from $p \Rightarrow q$ to $\lnot p \lor q$. This is one of the fundamental equivalences in propositional logic.

The function is useful in proof automation when working with disjunctive normal form (DNF) or when transforming implications to disjunctions is needed for certain proof strategies. This conversion allows for smooth transitions between different logical connectives, which is essential in formal reasoning systems.

### Dependencies
#### Theorems
- `TAUT` - Creates a theorem from a propositional tautology
- `MP` - Modus Ponens rule
- `SPECL` - Specializes universal quantifiers with a list of terms

### Porting notes
When porting to other systems:
- Most proof assistants have built-in functions for these common logical transformations
- The implementation is straightforward and uses standard logical operations
- The error handling pattern with `try` and `with Failure` should be adapted to match the target system's exception handling mechanism

---

## DISJ_CASES_UNION

### Name of formal statement
DISJ_CASES_UNION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DISJ_CASES_UNION dth ath bth =
    DISJ_CASES dth (DISJ1 ath (concl bth)) (DISJ2 (concl ath) bth);;
```

### Informal statement
The `DISJ_CASES_UNION` is a function that combines three theorems:
- `dth`: A theorem of the form `Γ ⊢ P ∨ Q`
- `ath`: A theorem of the form `Γ₁ ⊢ P ⇒ R`
- `bth`: A theorem of the form `Γ₂ ⊢ Q ⇒ S`

It applies disjunction elimination to produce a theorem of the form `Γ ∪ Γ₁ ∪ Γ₂ ⊢ R ∨ S`.

### Informal proof
This function composes two inference rules:

1. First, it applies `DISJ_CASES` to the disjunction theorem `dth: Γ ⊢ P ∨ Q` with two theorems:
   - `DISJ1 ath (concl bth)`, which gives `Γ₁ ⊢ P ⇒ (R ∨ S)`
   - `DISJ2 (concl ath) bth`, which gives `Γ₂ ⊢ Q ⇒ (R ∨ S)`

2. The `DISJ1` rule takes the theorem `ath: Γ₁ ⊢ P ⇒ R` and transforms it to `Γ₁ ⊢ P ⇒ (R ∨ S)` by adding disjunction on the right.

3. Similarly, the `DISJ2` rule takes `bth: Γ₂ ⊢ Q ⇒ S` and transforms it to `Γ₂ ⊢ Q ⇒ (R ∨ S)` by adding disjunction on the left.

4. The `DISJ_CASES` rule performs disjunction elimination using these implications to derive `Γ ∪ Γ₁ ∪ Γ₂ ⊢ R ∨ S`.

### Mathematical insight
This utility function implements a common proof pattern when working with disjunctions: case analysis followed by building a new disjunction from the results of each case. It's essentially a more specific version of disjunction elimination that preserves the disjunctive structure in the conclusion.

The pattern is:
- If we know `P ∨ Q`
- And `P` implies `R`
- And `Q` implies `S`
- Then we can conclude `R ∨ S`

This corresponds to the natural deduction rule for disjunction elimination, but specifically builds a disjunction in the conclusion, which is a common pattern in formal proofs.

### Dependencies
#### Inference rules
- `DISJ_CASES`: Disjunction elimination rule
- `DISJ1`: Left introduction rule for disjunction
- `DISJ2`: Right introduction rule for disjunction
- `concl`: Function to extract the conclusion of a theorem

### Porting notes
When porting to other systems:
- This is essentially a specialized version of disjunction elimination, so it might already exist in other proof assistants with a different name.
- In systems with more sophisticated tactic languages, this might be implemented as part of a general disjunction elimination tactic.
- The implementation is straightforward and should transfer easily to other systems, as it just composes basic inference rules for disjunctions.

---

## MK_ABS

### Name of formal statement
MK_ABS

### Type of the formal statement
Conversion function (function definition)

### Formal Content
```ocaml
let MK_ABS qth =
  try let ov = bndvar(rand(concl qth)) in
      let bv,rth = SPEC_VAR qth in
      let sth = ABS bv rth in
      let cnv = ALPHA_CONV ov in
      CONV_RULE(BINOP_CONV cnv) sth
  with Failure _ -> failwith "MK_ABS";;
```

### Informal statement
`MK_ABS` is a function that takes a quantified theorem `qth` of the form `⊢ ∀x. t = s` and produces a theorem of the form `⊢ (λy. t[y/x]) = (λy. s[y/x])`, where `y` is the bound variable in the right-hand side of the original theorem.

### Informal proof
The function works as follows:

1. First, it extracts the bound variable `ov` from the right-hand side of the conclusion of the quantified theorem.
2. Then it uses `SPEC_VAR` to instantiate the universally quantified variable in the theorem, resulting in a new variable `bv` and a theorem `rth` of the form `⊢ t[bv/x] = s[bv/x]`.
3. It applies `ABS bv` to `rth` to get a theorem `sth` of the form `⊢ (λbv. t[bv/x]) = (λbv. s[bv/x])`.
4. It creates a conversion `cnv` that will alpha-convert to use the original bound variable `ov`.
5. Finally, it applies this conversion to both sides of the equality in `sth` to get the result `⊢ (λov. t[ov/x]) = (λov. s[ov/x])`.

If any step fails, it raises the error "MK_ABS".

### Mathematical insight
This function is a utility for handling abstraction over equalities. It carefully manages variable binding to ensure that the resulting lambda abstractions use the desired variable name. The function is part of HOL Light's infrastructure for working with higher-order logic terms and theorems.

The key insight is that it preserves the variable name from the right-hand side of the original theorem, which helps maintain readability and consistency in the resulting theorem. This is particularly useful when working with complex higher-order terms where variable naming can affect readability.

### Dependencies
No direct dependencies were specified in the provided information, but the function uses several standard HOL Light operations:
- `bndvar`: Extracts the bound variable from a term
- `rand`: Extracts the right-hand side of an application
- `concl`: Gets the conclusion of a theorem
- `SPEC_VAR`: Specializes a universal quantifier with a variable
- `ABS`: Creates a lambda abstraction
- `ALPHA_CONV`: Performs alpha-conversion
- `CONV_RULE` and `BINOP_CONV`: Apply conversions to theorems

### Porting notes
When porting this function to another system:
1. Ensure the target system has equivalents for extracting components of terms and theorems.
2. Pay attention to how the system handles variable binding and alpha-conversion.
3. The error handling may need adaptation according to the target system's conventions.
4. Some proof assistants might have different approaches to managing bound variables in abstractions.

---

## HALF_MK_ABS

### Name of formal statement
HALF_MK_ABS

### Type of the formal statement
Function definition

### Formal Content
```ocaml
let HALF_MK_ABS th =
  try let th1 = MK_ABS th in
      CONV_RULE(LAND_CONV ETA_CONV) th1
  with Failure _ -> failwith "HALF_MK_ABS";;
```

### Informal statement
HALF_MK_ABS is a function that takes a theorem `th` and attempts to apply the MK_ABS function to it. If successful, it then applies ETA_CONV conversion to the left-hand side of the resulting theorem. If MK_ABS fails, it raises a "HALF_MK_ABS" failure message.

### Informal proof
This is a function definition rather than a theorem, so it doesn't have a proof. The function:

1. Takes a theorem `th` as input
2. Attempts to apply `MK_ABS` to `th` to get a new theorem `th1`
3. If successful, applies `CONV_RULE(LAND_CONV ETA_CONV)` to `th1` and returns the result
4. If `MK_ABS` fails, it raises a "HALF_MK_ABS" failure message

### Mathematical insight
HALF_MK_ABS is a utility function that combines the abstraction operation (MK_ABS) with eta-conversion (ETA_CONV) on the left-hand side of a theorem. This is useful in tactical theorem proving when one wants to abstract a variable and then apply eta-conversion in a single step.

Eta-conversion is based on the principle that in lambda calculus, functions that have the same behavior on all inputs are considered equal. Specifically, `λx. f x` is equivalent to `f` when `x` doesn't occur free in `f`. The ETA_CONV applies this simplification.

This function appears to be a "half" version of a more complete abstraction process, handling just one part of potentially more complex abstraction operations.

### Dependencies
- Functions:
  - `MK_ABS`: Creates lambda abstractions in theorems
  - `CONV_RULE`: Applies conversions to theorems
  - `LAND_CONV`: Applies a conversion to the left-hand side of a theorem
  - `ETA_CONV`: Performs eta-conversion

### Porting notes
When porting to other proof assistants:
- Ensure the target system has equivalent functionality for lambda abstraction and eta-conversion
- Check how the target system handles failure cases - some systems may require explicit pattern matching rather than exception handling
- The eta-conversion step might be handled differently in other systems, possibly automatically or through a different strategy

---

## MK_EXISTS

### MK_EXISTS
- `MK_EXISTS`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let MK_EXISTS qth =
  try let ov = bndvar(rand(concl qth)) in
      let bv,rth = SPEC_VAR qth in
      let sth = EXISTS_EQ bv rth in
      let cnv = GEN_ALPHA_CONV ov in
      CONV_RULE(BINOP_CONV cnv) sth
  with Failure _ -> failwith "MK_EXISTS";;
```

### Informal statement
This is a conversion function that takes a theorem `qth` of the form `∀y. P[y]` and returns a theorem stating the equality: `∃x. P[x] ⇔ P[y]`.

The function handles the alpha-conversion needed when the bound variable in the original theorem might conflict with the variable chosen for the existential quantification.

### Informal proof
The implementation works as follows:

1. First, it extracts `ov`, which is the bound variable from the original universally quantified theorem `qth`.

2. It applies `SPEC_VAR` to `qth` to specialize the universal quantifier, obtaining a new bound variable `bv` and the resulting theorem `rth`.

3. It then applies the `EXISTS_EQ` conversion to `bv` and `rth` to create a theorem of the form `(∃x. P[x]) ⇔ P[bv]`.

4. To handle potential variable name conflicts, it creates an alpha-conversion `cnv` targeting the original variable `ov`.

5. Finally, it applies this conversion to both sides of the equivalence in `sth` using `BINOP_CONV` and returns the resulting theorem.

If any step fails, the function raises the "MK_EXISTS" failure message.

### Mathematical insight
This function provides a convenient way to convert from universal statements to existential equivalence statements, which is a common pattern in formal theorem proving. It encapsulates the logical principle that if a property holds for an arbitrary value, then there exists a value for which the property holds.

The key insight is that this function handles the potentially complex variable renaming that might be needed when working with quantifiers, ensuring that variable capture is avoided. This is particularly important in higher-order logic systems like HOL Light.

### Dependencies
- `EXISTS_EQ` - Theorem for converting a term into an existential equivalence
- `SPEC_VAR` - Specializes a universally quantified theorem with a variable
- `GEN_ALPHA_CONV` - Conversion for alpha-renaming bound variables
- `BINOP_CONV` - Applies a conversion to both sides of a binary operation
- `CONV_RULE` - Applies a conversion as a rule to a theorem

### Porting notes
When porting this to other proof assistants:
- Ensure the target system has equivalent functionality for variable specialization and alpha-conversion
- Be aware of how the target system handles variable capture and renaming
- The implementation may need adaptation based on how the target system represents and manipulates quantifiers

---

## LIST_MK_EXISTS

### Name of formal statement
LIST_MK_EXISTS

### Type of the formal statement
Function definition

### Formal Content
```ocaml
let LIST_MK_EXISTS l th = itlist (fun x th -> MK_EXISTS(GEN x th)) l th;;
```

### Informal statement
`LIST_MK_EXISTS` is a function that takes a list of variables `l` and a theorem `th`, and iteratively applies existential quantification to theorem `th` for each variable in list `l`.

More precisely, for a list of variables `l = [x₁, x₂, ..., xₙ]` and a theorem `th`:
- `LIST_MK_EXISTS l th` produces a new theorem that is equivalent to `∃x₁. ∃x₂. ... ∃xₙ. P`, where `P` is the conclusion of `th`
- Each variable is quantified by applying the `MK_EXISTS` operation after generalizing the variable with `GEN`

### Informal proof
This is a recursive function definition using `itlist` (iterate over a list from right to left):

1. The function applies `MK_EXISTS(GEN x th)` for each variable `x` in the list `l`.
2. For each variable `x`:
   - First, `GEN x th` generalizes the variable `x` in theorem `th`
   - Then, `MK_EXISTS` introduces an existential quantifier for this generalized variable
3. This process is applied iteratively, working through each variable in the list.

The result is a theorem with all variables in `l` existentially quantified.

### Mathematical insight
This utility function automates the common operation of introducing multiple existential quantifiers in a theorem. Rather than applying existential introduction repeatedly by hand, this function allows batch quantification over a list of variables.

The order of quantification follows the order of variables in the input list, which is significant because in predicate logic, the order of quantifiers matters when mixing different quantifier types.

This function is particularly useful in formal proof development when dealing with theorems that need multiple existential quantifications, such as when proving the existence of mathematical objects with multiple parameters.

### Dependencies
- `itlist`: Higher-order function that iterates through a list, applying a binary operation
- `MK_EXISTS`: Function that introduces an existential quantifier to a theorem
- `GEN`: Function that universally quantifies a variable in a theorem

### Porting notes
When porting to other proof assistants:
- Most systems will have equivalent functions for existential quantification and universal generalization
- The implementation may need to be adjusted based on how the target system handles variable binding and theorem manipulation
- Pay attention to the order of operations, as the function applies generalization before existential introduction

---

## IMP_CONJ

### IMP_CONJ
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- Function for creating theorems

### Formal Content
```ocaml
let IMP_CONJ th1 th2 =
  let A1,C1 = dest_imp (concl th1) and A2,C2 = dest_imp (concl th2) in
  let a1,a2 = CONJ_PAIR (ASSUME (mk_conj(A1,A2))) in
      DISCH (mk_conj(A1,A2)) (CONJ (MP th1 a1) (MP th2 a2));;
```

### Informal statement
Given two theorems `th1` of the form `A1 ⟹ C1` and `th2` of the form `A2 ⟹ C2`, the function `IMP_CONJ` creates a new theorem of the form `A1 ∧ A2 ⟹ C1 ∧ C2`.

### Informal proof
The proof constructs the desired theorem through the following steps:

1. Extract the antecedents and consequents of both input theorems:
   - From `th1`, extract `A1` and `C1` where `th1` proves `A1 ⟹ C1`
   - From `th2`, extract `A2` and `C2` where `th2` proves `A2 ⟹ C2`

2. Create a temporary assumption `A1 ∧ A2` and use `CONJ_PAIR` to split it into two separate assumptions:
   - `a1` which is `A1`
   - `a2` which is `A2`

3. Apply modus ponens (`MP`) to both input theorems:
   - `MP th1 a1` yields `C1`
   - `MP th2 a2` yields `C2`

4. Use the `CONJ` rule to combine these results into `C1 ∧ C2`

5. Finally, discharge the assumption `A1 ∧ A2` to get the theorem `A1 ∧ A2 ⟹ C1 ∧ C2`

### Mathematical insight
This function implements a basic derived rule of inference that combines two conditional theorems into a single conditional theorem with a conjunctive antecedent and consequent. It's a natural way to combine implications when both need to be applied simultaneously.

The rule corresponds to the following logical principle:
- If `A1` implies `C1` and `A2` implies `C2`, then having both `A1` and `A2` together implies having both `C1` and `C2`.

This function is useful for combining conditional results while maintaining their dependence on assumptions.

### Dependencies
- Core inference rules:
  - `dest_imp` (for destructing implications)
  - `CONJ_PAIR` (for splitting a conjunction into separate theorems)
  - `ASSUME` (for creating assumption theorems)
  - `DISCH` (for discharging assumptions)
  - `CONJ` (for creating conjunctions)
  - `MP` (modus ponens)
- Term constructors:
  - `mk_conj` (for creating conjunction terms)

### Porting notes
This is a basic derived rule that should be straightforward to port to other systems. The implementation relies only on fundamental inference rules found in most proof assistants. When porting, ensure that the handling of discharge and assumptions follows the target system's conventions.

---

## EXISTS_IMP

### Name of formal statement
EXISTS_IMP

### Type of the formal statement
Theorem tactic

### Formal Content
```ocaml
let EXISTS_IMP x =
  if not (is_var x) then failwith "EXISTS_IMP: first argument not a variable"
  else fun th ->
         try let ante,cncl = dest_imp(concl th) in
             let th1 = EXISTS (mk_exists(x,cncl),x) (UNDISCH th) in
             let asm = mk_exists(x,ante) in
             DISCH asm (CHOOSE (x,ASSUME asm) th1)
         with Failure _ -> failwith "EXISTS_IMP: variable free in assumptions";;
```

### Informal statement
The function `EXISTS_IMP` transforms a theorem of the form:

$$\Gamma, P(x) \vdash Q(x)$$

into a new theorem:

$$\Gamma, \exists x.P(x) \vdash \exists x.Q(x)$$

where:
- $x$ is a variable not free in $\Gamma$
- The first argument to `EXISTS_IMP` is the variable $x$
- The second argument is the theorem $\Gamma, P(x) \vdash Q(x)$

The function fails if:
1. The first argument is not a variable
2. The variable is free in the assumptions $\Gamma$

### Informal proof
The implementation of `EXISTS_IMP` works as follows:

1. First, it checks that the first argument `x` is a variable, failing otherwise.

2. For a theorem `th` with conclusion of the form `P(x) ⇒ Q(x)`:
   - Use `dest_imp` to separate the antecedent `ante` and consequent `cncl` of the implication.
   - Apply `EXISTS` to introduce an existential quantifier for `x` in the conclusion, giving:
     $$\Gamma, P(x) \vdash \exists x. Q(x)$$
   - Create the assumption `∃x. P(x)`.
   - Use `CHOOSE` to eliminate the existential quantifier from this assumption.
   - Apply `DISCH` to discharge the assumption, yielding the final theorem:
     $$\Gamma, \exists x.P(x) \vdash \exists x.Q(x)$$

3. The function fails if:
   - `x` is not a variable
   - `x` is free in assumptions of the theorem

### Mathematical insight
This theorem tactic is a formalization of an important logical principle: if a property $Q(x)$ can be derived from $P(x)$ for a specific but arbitrary $x$ (not depending on other assumptions), then the existence of an object satisfying $Q$ follows from the existence of an object satisfying $P$.

This principle is commonly used in mathematical reasoning. For example, if we know that for any prime number $p$, some property $Q(p)$ holds, and we know that there exists a prime number satisfying some condition $P(p)$, then there exists a prime number satisfying $Q(p)$.

The tactic automates this reasoning pattern in HOL Light, helping to maintain a high level of abstraction in formal proofs.

### Dependencies
- Core inference rules:
  - `EXISTS` - Introduces an existential quantifier
  - `UNDISCH` - Moves an implication antecedent to the assumption list
  - `DISCH` - Discharges an assumption to form an implication
  - `CHOOSE` - Eliminates an existential quantifier
  - `ASSUME` - Creates a theorem with an assumption

### Porting notes
When porting this tactic to other systems:
- Ensure proper variable capture prevention - the variable `x` must not be free in the assumptions of the theorem.
- Check that the target system's inference rules handle discharged assumptions and existential quantifiers in a compatible way.
- The tactic manipulates implicational form, so in systems with different native implication handling, adjustments might be needed.
- Error handling for invalid inputs should be preserved.

---

## CONJUNCTS_CONV

### CONJUNCTS_CONV
- `CONJUNCTS_CONV`

### Type of the formal statement
- Conversion (a HOL Light function that returns theorems)

### Formal Content
```ocaml
let CONJUNCTS_CONV (t1,t2) =
  let rec build_conj thl t =
    try let l,r = dest_conj t in
        CONJ (build_conj thl l) (build_conj thl r)
    with Failure _ -> find (fun th -> concl th = t) thl in
  try IMP_ANTISYM_RULE
     (DISCH t1 (build_conj (CONJUNCTS (ASSUME t1)) t2))
     (DISCH t2 (build_conj (CONJUNCTS (ASSUME t2)) t1))
  with Failure _ -> failwith "CONJUNCTS_CONV";;
```

### Informal statement
`CONJUNCTS_CONV` is a conversion that takes a pair of terms $(t_1, t_2)$ and attempts to prove their logical equivalence ($t_1 \Leftrightarrow t_2$) by decomposing them into conjunctions and showing that both have the same set of conjuncts. It succeeds if both terms can be split into the same set of conjuncts, and fails otherwise.

### Informal proof
The function works as follows:

1. Define a recursive helper function `build_conj` that:
   - Takes a list of theorems `thl` and a term `t`
   - Attempts to decompose `t` into conjunctions recursively
   - If successful, applies the `CONJ` rule to build a proof
   - If `t` is not a conjunction, finds a theorem in `thl` whose conclusion matches `t`

2. To prove $t_1 \Leftrightarrow t_2$, the function:
   - Assumes $t_1$ and breaks it into conjuncts using `CONJUNCTS`
   - Uses the helper function to build up $t_2$ from those conjuncts
   - This gives a proof of $t_1 \Rightarrow t_2$
   - Similarly, it assumes $t_2$ and builds $t_1$ to get $t_2 \Rightarrow t_1$
   - Combines these using `IMP_ANTISYM_RULE` to get $t_1 \Leftrightarrow t_2$

3. If any step fails, the conversion returns `failwith "CONJUNCTS_CONV"`

### Mathematical insight
This conversion implements the principle that logical formulas with the same set of conjuncts are equivalent. This is useful for normalizing conjunctive expressions when the order or nesting of conjunctions differs but the actual atomic formulas are the same.

The key insight is that conjunction is associative and commutative in classical logic, so $(A \land B) \land C$, $A \land (B \land C)$, and even $C \land (A \land B)$ are all logically equivalent. This conversion allows automated proofs of such equivalences without having to manually apply associativity and commutativity.

The implementation uses a recursive approach to flatten nested conjunctions and match individual conjuncts, which is more efficient than explicitly applying associativity and commutativity rules.

### Dependencies
- Core theorem manipulation:
  - `CONJUNCTS` - used to break a conjunction into its components
  - `ASSUME` - used to assume hypotheses
  - `CONJ` - used to build conjunctions from parts
  - `IMP_ANTISYM_RULE` - used to prove logical equivalence from implications
  - `DISCH` - used to discharge assumptions

### Porting notes
When porting to other systems:
1. Be aware that some systems might have built-in rewriters for handling conjunctions that could replace this function.
2. The error handling approach using `try-with` constructs is specific to OCaml/HOL Light. Other systems will have different exception handling.
3. The function `find` used to locate a matching theorem might need to be defined or replaced with an equivalent in the target system.
4. The approach assumes classical logic; constructive proof assistants might require different handling.

---

## CONJ_SET_CONV

### Name of formal statement
CONJ_SET_CONV

### Type of the formal statement
Function definition (not a formal declaration like `new_definition`, but a standard HOL Light ML function)

### Formal Content
```ocaml
let CONJ_SET_CONV l1 l2 =
  try CONJUNCTS_CONV (list_mk_conj l1, list_mk_conj l2)
  with Failure _ -> failwith "CONJ_SET_CONV";;
```

### Informal statement
`CONJ_SET_CONV` is a conversion function that takes two lists of terms `l1` and `l2`, and attempts to match the conjunctions formed from these lists. It creates two terms by forming the conjunction of all elements in `l1` and the conjunction of all elements in `l2`, then applies the `CONJUNCTS_CONV` conversion to this pair of terms. If this operation fails, the function raises a "CONJ_SET_CONV" failure.

Specifically, for lists of terms $l_1 = [a_1, a_2, \ldots, a_n]$ and $l_2 = [b_1, b_2, \ldots, b_m]$, it attempts to convert:
$(a_1 \land a_2 \land \ldots \land a_n, b_1 \land b_2 \land \ldots \land b_m)$

### Informal proof
This is not a theorem but a function definition, so there's no proof. The function:

1. Takes two lists of terms `l1` and `l2`
2. Attempts to:
   - Create conjunctions from both lists using `list_mk_conj`
   - Apply `CONJUNCTS_CONV` to the pair of conjunctions
3. If any failure occurs during execution, it raises a "CONJ_SET_CONV" failure

### Mathematical insight
This function is a utility that handles sets represented as conjunctions. It provides a convenient way to compare or process two sets of propositions when they are represented as conjunctions.

The function serves as a higher-level abstraction over the `CONJUNCTS_CONV` conversion, allowing for operations on conjunctions constructed from arbitrary lists of terms. This makes it useful in theorem proving contexts where multiple propositions need to be grouped and processed together.

### Dependencies
- Functions:
  - `CONJUNCTS_CONV` - A conversion for handling the components of conjunctions
  - `list_mk_conj` - Converts a list of terms into a conjunction
  - `failwith` - Error handling function

### Porting notes
When porting to other proof assistants:
- Ensure the target system has equivalent functionality for building conjunctions from lists of terms
- Implement appropriate error handling for cases when the conversion cannot be applied
- Consider how conjunctions are represented in the target system, as the representation might differ from HOL Light

---

## FRONT_CONJ_CONV

### FRONT_CONJ_CONV
- FRONT_CONJ_CONV

### Type of the formal statement
- Conversion function

### Formal Content
```ocaml
let FRONT_CONJ_CONV tml t =
 let rec remove x l =
    if hd l = x then tl l else (hd l)::(remove x (tl l)) in
 try CONJ_SET_CONV tml (t::(remove t tml))
 with Failure _ -> failwith "FRONT_CONJ_CONV";;
```

### Informal statement
This is a conversion function that takes two arguments:
- `tml`: a list of terms (theorems)
- `t`: a single term

It attempts to move the term `t` to the front position of a conjunction of terms from the list `tml`. Specifically, it first removes `t` from `tml` if it's present in the list, then tries to apply `CONJ_SET_CONV` to transform a conjunction with `t` as the first conjunct followed by the remaining terms.

If `CONJ_SET_CONV` fails, the function throws a "FRONT_CONJ_CONV" failure message.

### Informal proof
This is a function definition rather than a theorem, so it doesn't have a formal proof. However, we can explain its implementation:

1. The function defines a helper function `remove` that removes the first occurrence of element `x` from a list `l`:
   - If the head of `l` equals `x`, return the tail of `l`
   - Otherwise, keep the head of `l` and recursively apply `remove` to the tail

2. The main function tries to:
   - Apply `CONJ_SET_CONV` to reorder a conjunction so that `t` appears first, followed by all terms in `tml` except for `t` itself
   - If `CONJ_SET_CONV` fails, it raises the "FRONT_CONJ_CONV" failure message

### Mathematical insight
This conversion serves a specific purpose in theorem manipulation - it allows reordering the conjuncts of a conjunction so that a particular term appears at the front. This is useful in proof automation and simplification when working with conjunctions where the order of conjuncts matters for subsequent proof steps.

The function is essentially syntactic manipulation of terms in the logic, moving a specific term to the front position in a conjunction without changing the logical meaning (since conjunction in logic is commutative).

### Dependencies
- `CONJ_SET_CONV`: A conversion that likely reorders conjunctions according to a specific arrangement

### Porting notes
When porting this function to other systems:
- Ensure the target system has an equivalent to `CONJ_SET_CONV` for manipulating conjunctions
- The error handling approach may need adaptation depending on how the target system handles exceptions
- The list manipulation pattern might be implemented differently in systems with different list APIs or functional programming paradigms

---

## CONJ_DISCH

### Name of formal statement
CONJ_DISCH

### Type of the formal statement
theorem and utility function

### Formal Content
```ocaml
let CONJ_DISCH =
  let pth = TAUT`!t t1 t2. (t ==> (t1 <=> t2)) ==> (t /\ t1 <=> t /\ t2)` in
  fun t th ->
    try let t1,t2 = dest_eq(concl th) in
        MP (SPECL [t; t1; t2] pth) (DISCH t th)
    with Failure _ -> failwith "CONJ_DISCH";;
```

### Informal statement
`CONJ_DISCH` is a utility function that takes a term `t` and a theorem `th` where `th` has the form `t1 <=> t2`, and produces the theorem `t /\ t1 <=> t /\ t2`.

Specifically, it applies the tautology:
$$\forall t, t_1, t_2.\; (t \Rightarrow (t_1 \Leftrightarrow t_2)) \Rightarrow (t \land t_1 \Leftrightarrow t \land t_2)$$

### Informal proof
The proof is a straightforward computational implementation:

1. First, a tautology is established as `pth`:
   $$\forall t, t_1, t_2.\; (t \Rightarrow (t_1 \Leftrightarrow t_2)) \Rightarrow (t \land t_1 \Leftrightarrow t \land t_2)$$

2. Given a term `t` and theorem `th` of the form `t1 <=> t2`:
   - Extract `t1` and `t2` from the conclusion of `th`
   - Instantiate the variables in `pth` with `t`, `t1`, and `t2`
   - Use `DISCH t th` to produce `t ==> (t1 <=> t2)`
   - Apply Modus Ponens (`MP`) to obtain the desired result: `t /\ t1 <=> t /\ t2`

3. Error handling is included to fail with the message "CONJ_DISCH" if the theorem doesn't have the expected form.

### Mathematical insight
This utility function implements a basic logical transformation that is useful in proofs involving conjunctions and equivalences. It's a specialized theorem that helps extend an equivalence by conjoining the same term to both sides.

The tautology it uses is a standard result in propositional logic that shows that if `t1` and `t2` are equivalent under the assumption `t`, then `t /\ t1` and `t /\ t2` are equivalent without that assumption. This is useful for manipulating conjunctions within conditional contexts.

This is a tactical component of HOL Light that helps automate certain logical transformations, rather than a mathematical theorem in the traditional sense.

### Dependencies
#### Theorems
- `TAUT`: Used to derive the tautology for the propositional formula
- `MP`: Modus Ponens
- `SPECL`: Specializes universally quantified variables with specific terms
- `DISCH`: Discharges an assumption

### Porting notes
When porting this to another proof assistant:
1. Ensure the target system has corresponding tactics for Modus Ponens, specialization, and discharge operations
2. Make sure error handling matches the conventions of the target system
3. In strongly typed proof assistants, you may need to add explicit type annotations for the variables `t`, `t1`, and `t2`

---

## rec

### CONJ_DISCHL

### Type of the formal statement
Function definition

### Formal Content
```ocaml
let rec CONJ_DISCHL l th =
  if l = [] then th else CONJ_DISCH (hd l) (CONJ_DISCHL (tl l) th);;
```

### Informal statement
`CONJ_DISCHL` is a recursive function that applies the `CONJ_DISCH` operation repeatedly to a theorem `th` using a list of assumptions `l`.

For a list of formulas `l = [p₁, p₂, ..., pₙ]` and a theorem `th`, the function produces:
- If `l` is empty, it returns `th` unchanged
- Otherwise, it applies `CONJ_DISCH p₁` to the result of recursively processing the rest of the list `[p₂, ..., pₙ]` with `th`

In other words, it transforms `th` into `CONJ_DISCH p₁ (CONJ_DISCH p₂ (... (CONJ_DISCH pₙ th)...))`.

### Informal proof
This is a recursive function definition, not a theorem, so there is no proof.

The function is defined by case analysis on the input list:
- Base case: If the list is empty, return the theorem unchanged.
- Recursive case: Apply `CONJ_DISCH` using the head of the list, with the result of recursively processing the tail of the list.

### Mathematical insight
`CONJ_DISCHL` serves as a utility function that allows applying `CONJ_DISCH` over a list of assumptions. 

The `CONJ_DISCH` operation takes a formula `p` and a theorem `th` and creates a theorem that discharges an assumption `p ∧ q` in `th` by replacing it with an assumption `q`, while adding `p` as an antecedent to the conclusion. `CONJ_DISCHL` extends this operation to work with a list of formulas.

This function is particularly useful in proofs that involve manipulating multiple conjunctive assumptions, allowing for more concise proof scripts by processing lists of assumptions rather than handling them one by one.

### Dependencies
#### Functions
- `CONJ_DISCH`: A function that discharges conjunctive assumptions

### Porting notes
When porting this function to another proof assistant:
- Ensure that the target system has an equivalent to `CONJ_DISCH` or implement it first
- The function uses basic list operations (`hd`, `tl`, `[]`) and recursion, which should be available in most proof assistants
- Consider whether the target system has built-in list iteration functions that could simplify the implementation

---

## rec

### Name of formal statement
GSPEC

### Type of the formal statement
function definition

### Formal Content
```ocaml
let rec GSPEC th =
  let wl,w = dest_thm th in
  if is_forall w then
      GSPEC (SPEC (genvar (type_of (fst (dest_forall w)))) th)
  else th;;
```

### Informal statement
`GSPEC` is a recursive function that takes a theorem `th` as input and repeatedly specializes universal quantifiers in the theorem with fresh generic variables until no universal quantifiers remain in the conclusion of the theorem.

Specifically, if `th` is a theorem of the form `Γ ⊢ ∀x. P(x)`, then `GSPEC th` returns a theorem where all universal quantifiers in the conclusion have been specialized with fresh generic variables.

### Informal proof
This is a recursive function definition rather than a theorem, so there is no proof. The function operates as follows:

1. It extracts the hypotheses `wl` and conclusion `w` from the input theorem `th`.
2. If the conclusion `w` is a universally quantified formula (i.e., of the form `∀x. P(x)`), then:
   - It creates a fresh generic variable of the same type as the bound variable in the quantification.
   - It specializes `th` with this generic variable using the `SPEC` function.
   - It recursively calls `GSPEC` on the resulting theorem.
3. If the conclusion is not universally quantified, it returns the theorem unchanged.

### Mathematical insight
`GSPEC` is a utility function that automatically instantiates all universally quantified variables in a theorem with fresh generic variables. This is useful in interactive theorem proving when working with theorems that have multiple universally quantified variables, as it saves the user from having to manually apply the `SPEC` rule multiple times.

Generic variables in HOL Light are useful because they can be later instantiated with specific terms as needed, while maintaining logical soundness. The function essentially converts a universally quantified theorem into a more directly applicable form with placeholder variables.

### Dependencies
#### Functions
- `dest_thm`: Extracts the hypotheses and conclusion from a theorem
- `is_forall`: Checks if a term is a universal quantification
- `dest_forall`: Breaks apart a universal quantification into the bound variable and body
- `genvar`: Creates a fresh generic variable of a specified type
- `type_of`: Determines the type of a term
- `SPEC`: Specializes a universally quantified theorem with a specific term

### Porting notes
When porting this function to other proof assistants:
1. Consider how the target system handles generic/schematic variables, as these concepts might differ between systems.
2. In systems without explicit generic variables (like some type theories), you might need to use meta-variables or other mechanisms instead.
3. The function assumes that specializing quantified variables with generic variables is a sound operation in the logic, which might require different implementation details in other systems.

---

## ANTE_CONJ_CONV

### ANTE_CONJ_CONV

### Type of the formal statement
Conversion function

### Formal Content
```ocaml
let ANTE_CONJ_CONV tm =
  try let (a1,a2),c = (dest_conj F_F I) (dest_imp tm) in
      let imp1 = MP (ASSUME tm) (CONJ (ASSUME a1) (ASSUME a2)) and
          imp2 = LIST_MP [CONJUNCT1 (ASSUME (mk_conj(a1,a2)));
                          CONJUNCT2 (ASSUME (mk_conj(a1,a2)))]
                         (ASSUME (mk_imp(a1,mk_imp(a2,c)))) in
      IMP_ANTISYM_RULE (DISCH_ALL (DISCH a1 (DISCH a2 imp1)))
                       (DISCH_ALL (DISCH (mk_conj(a1,a2)) imp2))
  with Failure _ -> failwith "ANTE_CONJ_CONV";;
```

### Informal statement
`ANTE_CONJ_CONV` is a conversion function that transforms implications of the form $(a_1 \land a_2) \Rightarrow c$ into the equivalent formula $a_1 \Rightarrow (a_2 \Rightarrow c)$. If the input term is not of the expected form, it fails with the error message "ANTE_CONJ_CONV".

### Informal proof
The proof establishes the equivalence between $(a_1 \land a_2) \Rightarrow c$ and $a_1 \Rightarrow (a_2 \Rightarrow c)$ by proving the implication in both directions:

1. First, it assumes $(a_1 \land a_2) \Rightarrow c$, $a_1$, and $a_2$.
   - From $a_1$ and $a_2$, it constructs $a_1 \land a_2$ using `CONJ`.
   - It then applies the assumption $(a_1 \land a_2) \Rightarrow c$ to derive $c$.
   - This proves $(a_1 \land a_2) \Rightarrow c \vdash a_1 \Rightarrow (a_2 \Rightarrow c)$.

2. Second, it assumes $a_1 \Rightarrow (a_2 \Rightarrow c)$ and $a_1 \land a_2$.
   - From $a_1 \land a_2$, it extracts $a_1$ and $a_2$ using `CONJUNCT1` and `CONJUNCT2`.
   - It then applies these to the assumption $a_1 \Rightarrow (a_2 \Rightarrow c)$ to derive $c$.
   - This proves $a_1 \Rightarrow (a_2 \Rightarrow c) \vdash (a_1 \land a_2) \Rightarrow c$.

3. Finally, it uses `IMP_ANTISYM_RULE` to combine these implications into an equivalence.

### Mathematical insight
This conversion implements the logical equivalence between $(a_1 \land a_2) \Rightarrow c$ and $a_1 \Rightarrow (a_2 \Rightarrow c)$, which is a standard form of the currying/uncurrying transformation in logic. This equivalence is fundamental in natural deduction systems and plays a key role in transforming formulas for easier manipulation in proof assistants.

The transformation allows treating multi-premise implications in a more modular way, handling one premise at a time, which is often more convenient in interactive theorem proving.

### Dependencies
- `MP`: Modus ponens rule
- `ASSUME`: Rule for introducing assumptions
- `CONJ`: Rule for conjunction introduction
- `CONJUNCT1`, `CONJUNCT2`: Rules for extracting components of a conjunction
- `LIST_MP`: Multi-argument version of modus ponens
- `IMP_ANTISYM_RULE`: Rule for proving equivalence from implications in both directions
- `DISCH`, `DISCH_ALL`: Rules for discharging assumptions

### Porting notes
When porting this conversion to other proof assistants:
1. Ensure the target system has equivalents for all the inference rules used here.
2. Be aware that some systems may have built-in tactics for this kind of transformation.
3. In systems with more explicit type information, you may need to handle type annotations carefully.
4. The error handling approach might need adaptation depending on the host language's exception mechanisms.

---

## bool_EQ_CONV

### Name of formal statement
bool_EQ_CONV

### Type of the formal statement
Conversion function (a HOL Light utility function, not a formal theorem or definition)

### Formal Content
```ocaml
let bool_EQ_CONV =
  let check = let boolty = `:bool` in check (fun tm -> type_of tm = boolty) in
  let clist = map (GEN `b:bool`)
                  (CONJUNCTS(SPEC `b:bool` EQ_CLAUSES)) in
  let tb = hd clist and bt = hd(tl clist) in
  let T = `T` and F = `F` in
  fun tm ->
    try let l,r = (I F_F check) (dest_eq tm) in
        if l = r then EQT_INTRO (REFL l) else
        if l = T then SPEC r tb else
        if r = T then SPEC l bt else fail()
    with Failure _ -> failwith "bool_EQ_CONV";;
```

### Informal statement
`bool_EQ_CONV` is a conversion function that simplifies Boolean equalities. Given a term of the form `t1 = t2` where both `t1` and `t2` have type `:bool`, it returns a theorem that proves the equality simplifies to either `T` or `F` based on the following rules:
- If `t1` and `t2` are identical, it simplifies to `T`
- If `t1` is `T`, it simplifies to `t2`
- If `t2` is `T`, it simplifies to `t1`

### Informal proof
This is a utility conversion function that constructs proofs using existing theorems. The implementation follows these steps:

- The function first creates a type-checking helper that verifies its input has type `:bool`.
- It then extracts two key theorems from `EQ_CLAUSES` by specializing to a Boolean variable and breaking apart the conjuncts:
  1. `∀b. (T = b) ⇔ b` (stored as `tb`)
  2. `∀b. (b = T) ⇔ b` (stored as `bt`)
- When the conversion is applied to a term:
  - First, it attempts to decompose the term as an equality `l = r`.
  - If the left and right sides are identical (`l = r`), it returns a theorem proving `l = r ⇔ T` using reflexivity.
  - If the left side is `T` (i.e., `T = r`), it applies the specialized theorem `tb` with `r`.
  - If the right side is `T` (i.e., `l = T`), it applies the specialized theorem `bt` with `l`.
  - If none of these conditions hold, the conversion fails.

### Mathematical insight
`bool_EQ_CONV` implements a straightforward logical simplification of Boolean equalities, which is a fundamental operation in automated reasoning. The conversion embodies basic logical principles:

1. Any expression equals itself (reflexivity)
2. `T = P` is logically equivalent to `P` itself
3. `P = T` is logically equivalent to `P` itself

This conversion is part of HOL Light's basic simplification toolkit, helping to normalize Boolean expressions in proofs. It's particularly useful when dealing with the simplification of larger logical formulas where Boolean equalities need to be reduced to their simplest form.

### Dependencies
- Theorems:
  - `EQ_CLAUSES`: fundamental theorem about Boolean equality
  - `REFL`: reflexivity theorem
  - `EQT_INTRO`: theorem for introducing equivalence with `T`

### Porting notes
When porting this conversion to another system:
- Ensure the target system has corresponding theorems for Boolean equalities similar to `EQ_CLAUSES`
- Consider the error handling approach - HOL Light uses exceptions, which might need adjustment in other systems
- The implementation uses pattern matching on term structure, which is common across most proof assistants but syntax will differ

---

## COND_CONV

### Name of formal statement
COND_CONV

### Type of the formal statement
Conversion function (HOL Light custom tactic)

### Formal Content
```ocaml
let COND_CONV =
  let T = `T` and F = `F` and vt = genvar`:A` and vf = genvar `:A` in
  let gen = GENL [vt;vf] in
  let CT,CF = (gen F_F gen) (CONJ_PAIR (SPECL [vt;vf] COND_CLAUSES)) in
  fun tm ->
    let P,(u,v) = try dest_cond tm
                  with Failure _ -> failwith "COND_CONV: not a conditional" in
    let ty = type_of u in
    if (P=T) then SPEC v (SPEC u (INST_TYPE [ty,`:A`] CT)) else
    if (P=F) then SPEC v (SPEC u (INST_TYPE [ty,`:A`] CF)) else
    if (u=v) then SPEC u (SPEC P (INST_TYPE [ty,`:A`] COND_ID)) else
    if (aconv u v) then
       let cnd = AP_TERM (rator tm) (ALPHA v u) in
       let thm = SPEC u (SPEC P (INST_TYPE [ty,`:A`] COND_ID)) in
           TRANS cnd thm else
  failwith "COND_CONV: can't simplify conditional";;
```

### Informal statement
`COND_CONV` is a conversion function that simplifies conditional expressions of the form `P ? u : v` (where `?` represents the conditional operator) in the following cases:
1. If `P` is `T` (true), it returns the theorem `⊢ (T ? u : v) = u`
2. If `P` is `F` (false), it returns the theorem `⊢ (F ? u : v) = v`
3. If `u` and `v` are the same expression or alpha-equivalent, it returns the theorem `⊢ (P ? u : u) = u`

If the input expression is not a conditional or doesn't match any of these patterns, the conversion fails with an appropriate error message.

### Informal proof
This is a conversion function implementation rather than a theorem, so it doesn't have a traditional mathematical proof. However, I'll explain its implementation:

The function uses the following theorems:
- `COND_CLAUSES`: Contains the basic properties of the conditional operator
- `COND_ID`: States that `(P ? u : u) = u` for any predicate `P` and value `u`

The implementation:
1. First extracts the components `T ? u : v = u` and `F ? u : v = v` from `COND_CLAUSES`
2. Then analyzes the input term:
   - If the condition `P` is `T`, returns the theorem `⊢ (T ? u : v) = u`
   - If the condition `P` is `F`, returns the theorem `⊢ (F ? u : v) = v`
   - If `u` and `v` are identical, returns the theorem `⊢ (P ? u : u) = u`
   - If `u` and `v` are alpha-equivalent (differ only in bound variable names), applies alpha conversion and then uses the identity property

The function fails if none of these cases apply.

### Mathematical insight
`COND_CONV` is a conversion function that implements basic simplification rules for conditional expressions in HOL Light. It represents three fundamental properties of conditionals:
1. A conditional with a true condition selects the "then" branch
2. A conditional with a false condition selects the "else" branch
3. A conditional with identical branches can be simplified to just that branch

This conversion is useful as a building block in more complex proof automation. By identifying and simplifying conditionals that can be reduced based on these patterns, it helps eliminate unnecessary conditional expressions in proofs.

### Dependencies
- Theorems:
  - `COND_CLAUSES`: Basic properties of the conditional operator
  - `COND_ID`: The identity property of conditionals `(P ? u : u) = u`
- Functions:
  - `dest_cond`: Destructuring a conditional term
  - Various HOL Light built-in tactics like `GENL`, `SPECL`, `INST_TYPE`, etc.

### Porting notes
When porting this conversion to another system:
1. Ensure the target system has equivalent theorems for conditional operator properties
2. The alpha-equivalence check (`aconv`) and handling may need special attention in systems with different bound variable representations
3. The error handling approach may need adjustment to match the conventions of the target system

---

## SUBST_MATCH

### SUBST_MATCH
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- Theorem/utility function

### Formal Content
```ocaml
let SUBST_MATCH eqth th =
 let tm_inst,ty_inst = find_match (lhs(concl eqth)) (concl th) in
 SUBS [INST tm_inst (INST_TYPE ty_inst eqth)] th;;
```

### Informal statement
This function takes two theorems: 
1. An equation theorem `eqth` of the form `⊢ lhs = rhs`
2. Another theorem `th`

It matches the left-hand side `lhs` of the equation to a subterm in `th` by finding appropriate term and type instantiations, then applies the substitution to transform `th` according to the equality given in `eqth`.

Specifically, `SUBST_MATCH eqth th` works by:
- Finding a match between the left-hand side of `eqth` and some subterm in `th`
- Creating the instantiated version of `eqth` using the found term and type instantiations
- Applying this instantiated equality as a substitution to transform `th`

### Informal proof
The function is implemented as follows:

1. First, find a match between the left-hand side of the equation `eqth` and the conclusion of theorem `th`:
   ```
   let tm_inst,ty_inst = find_match (lhs(concl eqth)) (concl th)
   ```
   This returns term instantiations `tm_inst` and type instantiations `ty_inst` that make the left-hand side of `eqth` match some subterm in the conclusion of `th`.

2. Then, apply these instantiations to `eqth` to create a properly instantiated version of the equation:
   ```
   INST tm_inst (INST_TYPE ty_inst eqth)
   ```

3. Finally, apply this instantiated equation as a substitution to transform `th`:
   ```
   SUBS [INST tm_inst (INST_TYPE ty_inst eqth)] th
   ```
   
The `SUBS` function applies the substitutions given by the instantiated equation to the theorem `th`.

### Mathematical insight
`SUBST_MATCH` is a utility function that implements a common pattern in theorem proving: finding a subterm in a theorem that matches some known equality, and then applying that equality to rewrite the theorem.

This operation is fundamental in equational reasoning and term rewriting. It provides a convenient way to apply equational theorems without having to manually specify the exact instantiations needed. The function essentially automates the process of:
1. Pattern matching to find where an equality can be applied
2. Instantiating the variables in that equality appropriately
3. Applying the equality as a substitution

This kind of automation is essential in interactive theorem proving to reduce the manual effort required during proof development.

### Dependencies
- Core theorem proving functions:
  - `lhs`: Extracts the left-hand side of an equation
  - `concl`: Extracts the conclusion of a theorem
  - `find_match`: Finds term and type instantiations to match two terms
  - `INST`: Instantiates term variables in a theorem
  - `INST_TYPE`: Instantiates type variables in a theorem
  - `SUBS`: Applies substitutions to a theorem

### Porting notes
When porting to other proof assistants:
- Ensure the target system has similar pattern matching capabilities
- The equivalent in other systems might require more explicit handling of term traversal if they lack built-in pattern matching
- Systems with different approaches to substitution may need to adapt the implementation accordingly
- In some systems, this functionality might be built into the rewriting tactics, making a direct port unnecessary

---

## SUBST

### SUBST
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- Function definition

### Formal Content
```ocaml
let SUBST thl pat th =
  let eqs,vs = unzip thl in
  let gvs = map (genvar o type_of) vs in
  let gpat = subst (zip gvs vs) pat in
  let ls,rs = unzip (map (dest_eq o concl) eqs) in
  let ths = map (ASSUME o mk_eq) (zip gvs rs) in
  let th1 = ASSUME gpat in
  let th2 = SUBS ths th1 in
  let th3 = itlist DISCH (map concl ths) (DISCH gpat th2) in
  let th4 = INST (zip ls gvs) th3 in
  MP (rev_itlist (C MP) eqs th4) th;;
```

### Informal statement
The `SUBST` function is a theorem transformer that performs substitution according to a list of equations. It takes three arguments:
- `thl`: a list of theorems, each proving an equation of the form `⊢ s = t`
- `pat`: a pattern term
- `th`: a theorem

The function substitutes occurrences of the left-hand sides of the equations in `thl` with their corresponding right-hand sides within the pattern `pat`, and then uses this substituted pattern to derive a new theorem from `th`.

### Informal proof
The function is implemented through the following steps:

1. Extract the equations `eqs` and variables `vs` from the input theorem list `thl`.

2. Create generic variables `gvs` with the same types as `vs`.

3. Substitute `vs` with `gvs` in the pattern `pat` to create a generic pattern `gpat`.

4. Extract the left-hand sides `ls` and right-hand sides `rs` from the conclusions of the equation theorems.

5. Create assumption theorems `ths` of the form `gv = r` for each generic variable and corresponding right-hand side.

6. Assume the generic pattern to get `th1`.

7. Apply the substitutions from `ths` to `th1` using `SUBS` to get `th2`.

8. Create an implication theorem `th3` by discharging the assumptions in `ths` and the generic pattern.

9. Instantiate `th4` by substituting the left-hand sides `ls` for the generic variables `gvs` in `th3`.

10. Use the original equation theorems to eliminate the assumptions and produce the final theorem.

### Mathematical insight
`SUBST` implements a form of equational reasoning where we can substitute equals for equals in a pattern. It generalizes standard substitution by allowing multiple substitutions specified by theorems.

The key insight is using generic variables as placeholders to properly handle the substitution process. By first generalizing the pattern with fresh variables, performing the substitutions, and then instantiating back with the original terms, we maintain logical soundness while enabling complex term transformations.

This function is valuable for rewriting terms according to a collection of equations, which is a fundamental operation in interactive theorem proving.

### Dependencies
The implementation uses several core HOL Light theorem manipulation functions:
- `unzip`: Separates a list of pairs into two lists
- `genvar`: Generates a fresh variable of a given type
- `subst`: Performs term substitution
- `dest_eq`: Extracts the left and right sides of an equation
- `concl`: Returns the conclusion of a theorem
- `ASSUME`: Creates an assumption theorem
- `SUBS`: Applies a list of equations as substitutions
- `DISCH`: Discharges an assumption
- `itlist`: Folds a function over a list
- `INST`: Instantiates variables in a theorem
- `MP`: Applies modus ponens
- `C`: Function composition with reversed arguments
- `rev_itlist`: Folds a function over a list from right to left

### Porting notes
When porting this function:
1. Be aware of the variable capture issues - the use of generic variables is essential to avoid unwanted variable captures during substitution.
2. The order of operations is crucial - first generalizing, then substituting, then instantiating back.
3. Different proof assistants have different approaches to handling substitution and variable binding, so adaptations might be necessary.
4. Pay attention to how assumptions are managed in the target system, as this function heavily manipulates assumptions.

---

## SUBST_CONV

### SUBST_CONV
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- Definition (let-binding in HOL Light)

### Formal Content
```ocaml
let SUBST_CONV thvars template tm =
  let thms,vars = unzip thvars in
  let gvs = map (genvar o type_of) vars in
  let gtemplate = subst (zip gvs vars) template in
  SUBST (zip thms gvs) (mk_eq(template,gtemplate)) (REFL tm);;
```

### Informal statement
This defines a conversion function `SUBST_CONV` that performs substitution in terms. It takes three parameters:
- `thvars`: A list of pairs `(thm, var)` where each `thm` is presumably of the form `⊢ t = s` and each `var` is a variable.
- `template`: A term containing the variables from `thvars` that will be used as a pattern.
- `tm`: The term to which the conversion will be applied.

The function:
1. Separates the theorem-variable pairs into separate lists `thms` and `vars`.
2. Creates generic variables `gvs` matching the types of the variables in `vars`.
3. Creates a template `gtemplate` by substituting the original variables `vars` with the generic variables `gvs`.
4. Applies the `SUBST` inference rule with:
   - The theorems paired with the generic variables
   - A reflexivity theorem asserting `template = gtemplate`
   - The term `tm` to which the substitution will be applied

### Informal proof
This is a definition, not a theorem, so it doesn't have a proof. However, the function implements a conversion that uses the `SUBST` inference rule in a specific way:

1. It first prepares the substitution by splitting theorem-variable pairs.
2. It creates fresh variables and substitutes them for the original variables in the template.
3. It then uses the HOL Light `SUBST` rule to perform the actual substitution in the term `tm`.

The use of generic variables allows the substitution to avoid variable capture problems.

### Mathematical insight
The `SUBST_CONV` function provides a conversion interface to the `SUBST` inference rule, making it easier to use in certain contexts. Conversions in HOL Light are functions that transform terms and produce theorems of the form `⊢ t = t'`.

This function provides a more controlled way to perform substitutions compared to using `SUBST` directly. It allows substitutions to be applied in a specific context (the template) rather than throughout a term. This is useful for transforming specific parts of terms in a more targeted manner.

The comment "A poor thing but mine own" and the mention of old versions using `mk_thm` suggest that this is a replacement for previous implementation(s) that might have used unsafe tactics or had other issues.

### Dependencies
- Core inference rules:
  - `SUBST`: The substitution inference rule
  - `REFL`: The reflexivity inference rule (to create `⊢ tm = tm`)

- Utility functions:
  - `unzip`: Separates a list of pairs into two lists
  - `map`: Applies a function to each element of a list
  - `genvar`: Generates a fresh variable of a given type
  - `type_of`: Gets the type of a term
  - `subst`: Performs substitution in terms
  - `zip`: Pairs corresponding elements of two lists
  - `mk_eq`: Creates an equality term

### Porting notes
When porting this to other systems:
1. Ensure the target system has a similar substitution rule or provides means to implement one.
2. The handling of generic variables might differ between systems - some may have built-in mechanisms to avoid variable capture.
3. The conversion pattern (functions producing theorems of form `⊢ t = t'`) may need adaptation to fit the target system's architecture.
4. In systems with stronger type systems (like Lean or Coq), the explicit type handling might need additional care.

---

## FILTER_PURE_ASM_REWRITE_RULE

### FILTER_PURE_ASM_REWRITE_RULE

### Type of the formal statement
Function definition

### Formal Content
```ocaml
let FILTER_PURE_ASM_REWRITE_RULE f thl th =
    PURE_REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th

and FILTER_ASM_REWRITE_RULE f thl th =
    REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th

and FILTER_PURE_ONCE_ASM_REWRITE_RULE f thl th =
    PURE_ONCE_REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th

and FILTER_ONCE_ASM_REWRITE_RULE f thl th =
    ONCE_REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th;;
```

### Informal statement
These functions implement various forms of rewriting using a filtered subset of the hypotheses from a theorem:

1. `FILTER_PURE_ASM_REWRITE_RULE f thl th`: Applies pure rewriting using a filtered subset of the theorem's hypotheses alongside additional theorems.
   - `f` is a predicate function that filters which hypotheses to use for rewriting
   - `thl` is a list of theorems to use for rewriting
   - `th` is the theorem to be rewritten

2. `FILTER_ASM_REWRITE_RULE f thl th`: Similar to the first function but uses normal rewriting instead of pure rewriting.

3. `FILTER_PURE_ONCE_ASM_REWRITE_RULE f thl th`: Applies pure rewriting once using filtered hypotheses and additional theorems.

4. `FILTER_ONCE_ASM_REWRITE_RULE f thl th`: Applies rewriting once using filtered hypotheses and additional theorems.

### Informal proof
These are function definitions, not theorems requiring proofs.

Each function works by:
1. Extracting the hypotheses from the input theorem `th` using `hyp th`
2. Filtering these hypotheses using the predicate function `f`
3. Converting each selected hypothesis into an assumption using `ASSUME`
4. Appending these assumptions to the additional theorems `thl`
5. Applying the appropriate rewriting rule (`PURE_REWRITE_RULE`, `REWRITE_RULE`, `PURE_ONCE_REWRITE_RULE`, or `ONCE_REWRITE_RULE`) with this combined list of theorems

### Mathematical insight
These functions provide a flexible way to perform rewriting using a selective subset of a theorem's hypotheses. This addresses a common need in interactive theorem proving where only certain hypotheses are useful for rewriting, while others might lead to unnecessary or undesirable rewrites.

The different variants offer:
- Pure rewriting (which preserves exact term structure) vs. normal rewriting (which may normalize terms)
- Complete rewriting (which rewrites exhaustively) vs. once rewriting (which applies rewrites only once)

The filtering capability allows the user to precisely control which hypotheses participate in rewriting, which can be crucial for managing complex proofs where some hypotheses might cause loops or other problems if used indiscriminately for rewriting.

### Dependencies
- Core rewriting rules:
  - `PURE_REWRITE_RULE`
  - `REWRITE_RULE`
  - `PURE_ONCE_REWRITE_RULE`
  - `ONCE_REWRITE_RULE`
- Theorem manipulation:
  - `ASSUME`
  - `hyp`
- Standard list operations:
  - `map`
  - `filter`

### Porting notes
When porting to other theorem provers:
1. Ensure the target system has equivalent notions of hypotheses and rewriting
2. Check how the target system handles assumptions and if they need special treatment
3. Consider whether the target system's rewriting tactics already support hypothesis filtering
4. The distinction between "pure" and regular rewriting may be handled differently in other systems

---

## (FILTER_PURE_ASM_REWRITE_TAC:

### FILTER_PURE_ASM_REWRITE_TAC

### Type of the formal statement
Tactic definition

### Formal Content
```ocaml
let (FILTER_PURE_ASM_REWRITE_TAC: (term->bool) -> thm list -> tactic) =
  fun f thl (asl,w) ->
    PURE_REWRITE_TAC (filter (f o concl) (map snd asl) @ thl) (asl,w)

and (FILTER_ASM_REWRITE_TAC: (term->bool) -> thm list -> tactic) =
  fun f thl (asl,w) ->
    REWRITE_TAC (filter (f o concl) (map snd asl) @ thl) (asl,w)

and (FILTER_PURE_ONCE_ASM_REWRITE_TAC: (term->bool) -> thm list -> tactic) =
  fun f thl (asl,w) ->
    PURE_ONCE_REWRITE_TAC (filter (f o concl) (map snd asl) @ thl) (asl,w)

and (FILTER_ONCE_ASM_REWRITE_TAC: (term->bool) -> thm list -> tactic) =
  fun f thl (asl,w) ->
    ONCE_REWRITE_TAC (filter (f o concl) (map snd asl) @ thl) (asl,w);;
```

### Informal statement
This is a family of four tactic definitions:

1. `FILTER_PURE_ASM_REWRITE_TAC f thl`: A tactic that applies rewriting using both filtered assumptions and the given theorems list `thl`. The filtering is done by applying the predicate function `f` to the conclusion of each assumption, keeping only those that satisfy the predicate. It uses pure rewriting, which doesn't handle conditional rewrites.

2. `FILTER_ASM_REWRITE_TAC f thl`: Similar to the first tactic, but uses regular rewriting which handles conditional rewrites.

3. `FILTER_PURE_ONCE_ASM_REWRITE_TAC f thl`: Similar to the first tactic, but applies each rewrite rule only once.

4. `FILTER_ONCE_ASM_REWRITE_TAC f thl`: Similar to the second tactic, but applies each rewrite rule only once.

In all cases, the tactic takes a predicate function `f: term -> bool` and a theorem list `thl`, and returns a tactic that operates on a goal consisting of assumptions `asl` and target `w`.

### Informal proof
These are tactical definitions rather than theorems, so there is no proof. Each definition specifies how to construct a new tactic from existing tactics:

1. `FILTER_PURE_ASM_REWRITE_TAC f thl` applies `PURE_REWRITE_TAC` with the concatenation of:
   - Filtered assumptions: `filter (f o concl) (map snd asl)`
   - The input theorem list: `thl`

2. `FILTER_ASM_REWRITE_TAC f thl` applies `REWRITE_TAC` in a similar way.

3. `FILTER_PURE_ONCE_ASM_REWRITE_TAC f thl` applies `PURE_ONCE_REWRITE_TAC` in a similar way.

4. `FILTER_ONCE_ASM_REWRITE_TAC f thl` applies `ONCE_REWRITE_TAC` in a similar way.

In each case, the filtering process consists of:
- Extracting the conclusions of assumptions using `map snd asl`
- Applying the predicate `f` to each conclusion using `f o concl`
- Keeping only those assumptions that satisfy the predicate using `filter`

### Mathematical insight
These tactics provide fine-grained control over which assumptions are used in rewriting. This is useful in complex proofs where only certain assumptions should be used as rewrite rules, while others might lead to unhelpful or infinite rewriting loops.

The four variants cover different rewriting strategies:
- Pure vs. regular rewriting (handling conditional rewrites)
- Exhaustive vs. once-only application of rewrite rules

This family of tactics exemplifies how HOL Light's tactic system allows combining primitive tactics with higher-order functions to create more sophisticated proof automation tools.

### Dependencies
- Basic tactics
  - `PURE_REWRITE_TAC`
  - `REWRITE_TAC`
  - `PURE_ONCE_REWRITE_TAC`
  - `ONCE_REWRITE_TAC`
- Standard library functions
  - `filter`
  - `map`
  - `concl`
  - `snd`

### Porting notes
When porting these tactics to another system:
1. Ensure the target system has equivalents for the basic rewriting tactics
2. Check that the target system supports filtering of assumptions based on arbitrary predicates
3. The composition operator `o` might need to be adjusted for the target system's syntax
4. Consider whether the target system's rewriting tactics already have built-in filtering capabilities

---

## (X_CASES_THENL:

### X_CASES_THENL
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let (X_CASES_THENL: term list list -> thm_tactic list -> thm_tactic) =
  fun varsl ttacl ->
    end_itlist DISJ_CASES_THEN2
       (map (fun (vars,ttac) -> EVERY_TCL (map X_CHOOSE_THEN vars) ttac)
        (zip varsl ttacl));;
```

### Informal statement
This is a tactical (proof tactic combinator) that combines disjunction elimination with variable binding. For a given list of variable lists `varsl` and a corresponding list of theorem tactics `ttacl`, `X_CASES_THENL varsl ttacl` creates a tactic that:

1. Applies disjunction elimination to the goal
2. For each disjunct, binds the corresponding variables in `varsl` using `X_CHOOSE_THEN`
3. Then applies the corresponding theorem tactic from `ttacl`

Specifically, if `varsl = [vars₁, vars₂, ..., varsₙ]` and `ttacl = [ttac₁, ttac₂, ..., ttacₙ]`, the tactic will handle a goal with $n$ disjuncts, binding the variables in `varsᵢ` for the ith disjunct and applying `ttacᵢ` to it.

### Informal proof
The definition is implemented as follows:

1. Use `zip varsl ttacl` to pair each list of variables with its corresponding theorem tactic
2. Map over these pairs with the function `(vars,ttac) ↦ EVERY_TCL (map X_CHOOSE_THEN vars) ttac`, which:
   - Creates a sequence of variable bindings using `X_CHOOSE_THEN` for each variable in the list
   - Combines these bindings with the theorem tactic using `EVERY_TCL`
3. Finally, combine all of these tactics using `end_itlist DISJ_CASES_THEN2`, which builds a nested application of `DISJ_CASES_THEN2` to handle the disjunctive elimination

### Mathematical insight
This tactical is designed to handle disjunctive theorems where each disjunct may introduce different bound variables. It provides a structured way to specify how to handle each case in a disjunction, allowing different variables to be extracted and used in different branches of the proof.

This pattern is common when dealing with existential statements within disjunctions, where you want to extract the witnesses and then continue the proof differently for each case.

The main benefit is avoiding repetitive code when handling disjunctive cases with different bound variables, making complex proofs more concise and readable.

### Dependencies
- **Tacticals and tactics:**
  - `DISJ_CASES_THEN2`
  - `X_CHOOSE_THEN`
  - `EVERY_TCL`
  - `end_itlist`

### Porting notes
When porting to other systems:
1. Most theorem provers have similar concepts for handling disjunctions and binding variables, but the exact API may differ
2. The implementation makes heavy use of higher-order function composition, which may need to be adapted to the host system's tactical combinators
3. Be aware that different systems may have different approaches to variable binding in tactics
4. In systems with dependent types (like Coq or Lean), the variable binding might need to be handled carefully regarding types

---

## (X_CASES_THEN:

### X_CASES_THEN

### Type of the formal statement
Function definition (let-binding)

### Formal Content
```ocaml
let (X_CASES_THEN: term list list -> thm_tactical) =
  fun varsl ttac ->
    end_itlist DISJ_CASES_THEN2
       (map (fun vars -> EVERY_TCL (map X_CHOOSE_THEN vars) ttac) varsl);;
```

### Informal statement
`X_CASES_THEN` is a theorem tactical (a function that transforms theorem tactics) that handles case splits with existential variables.

Given:
- `varsl`: A list of lists of variables, where each inner list represents variables to be chosen in a particular case
- `ttac`: A theorem tactic to be applied after the variables are chosen

The function returns a theorem tactical that:
1. Applies a case split using disjunction (OR) elimination
2. For each case, chooses the corresponding existential variables in the inner list
3. Applies the provided theorem tactic to each case after choosing the variables

### Informal proof
The function is defined by combining several HOL Light tactical combinators:

- `end_itlist DISJ_CASES_THEN2` applies a disjunction elimination tactical over a list, handling all cases of an OR statement
- `map (fun vars -> EVERY_TCL (map X_CHOOSE_THEN vars) ttac) varsl` creates a list of tactics where:
  - For each list of variables `vars` in `varsl`, it maps `X_CHOOSE_THEN` over those variables
  - `EVERY_TCL` sequences these `X_CHOOSE_THEN` tactics to choose all variables in a particular case
  - Each resulting tactic is then composed with the input theorem tactic `ttac`

The overall effect is to create a tactic that performs case analysis, chooses the appropriate existential variables in each case, and then applies the given tactic.

### Mathematical insight
This tactical is part of HOL Light's tactical system for handling complex proof structures. It specifically addresses the common pattern where a proof has multiple cases (represented by a disjunction), and each case involves existential quantifiers that need to be instantiated.

The power of this tactical comes from automating what would otherwise be a tedious and repetitive process:
1. Splitting a proof into cases
2. For each case, choosing the appropriate existential witnesses  
3. Continuing the proof with those witnesses

Without this tactical, proofs with multiple cases and existential witnesses would require much more verbose scripting.

### Dependencies
- Tactical combinators:
  - `DISJ_CASES_THEN2`: For handling disjunction elimination
  - `X_CHOOSE_THEN`: For existential variable instantiation
  - `EVERY_TCL`: For sequencing theorem-continuing tacticals
  - `end_itlist`: For folding a binary operation over a list from right to left

### Porting notes
When porting this to another system:
1. Ensure the target system has corresponding tactics for disjunction elimination and existential instantiation
2. The equivalent in other systems might use pattern matching on the structure of the theorem rather than explicit tactical combinators
3. Some systems might have more integrated ways of handling case analysis with existential variables
4. The implementation may be simpler in systems with more powerful pattern matching capabilities

---

## (CASES_THENL:

### CASES_THENL

### Type of the formal statement
HOL Light tactic definition

### Formal Content
```ocaml
let (CASES_THENL: thm_tactic list -> thm_tactic) =
  fun ttacl -> end_itlist DISJ_CASES_THEN2 (map (REPEAT_TCL CHOOSE_THEN) ttacl);;
```

### Informal statement
This is a tactic definition that combines disjunction elimination with multiple branches. Given a list of tactics `ttacl`, it applies the `DISJ_CASES_THEN2` tactic to handle each disjunction case, after preparing each tactic in the list by repeatedly applying `CHOOSE_THEN` to handle existential quantifiers.

Specifically, `CASES_THENL` takes a list of tactics and produces a new tactic that:
1. Processes each tactic in the list by repeatedly applying `CHOOSE_THEN` to handle any existential quantifiers
2. Combines these processed tactics using `DISJ_CASES_THEN2` in a right-associative manner (due to `end_itlist`)

### Informal proof
The implementation is straightforward:

For a given list of tactics `ttacl`:
1. Apply `REPEAT_TCL CHOOSE_THEN` to each tactic in the list to handle existential quantifiers, producing a new list of tactics
2. Use `end_itlist DISJ_CASES_THEN2` to combine these tactics, which processes them right-associatively

The `end_itlist` function takes a binary operation `f` and applies it to the list elements from right to left:
- For a list `[a; b; c; d]`, it computes `a f (b f (c f d))`

### Mathematical insight
The `CASES_THENL` tactic provides a convenient way to handle disjunctive reasoning with potentially existential variables in each branch. It's particularly useful for case analysis where each case may introduce new existentially quantified variables.

This tactic represents the familiar mathematical reasoning pattern where we:
1. Split a proof into cases based on a disjunction
2. Handle each case separately, potentially using different proof strategies
3. Deal with any "witnesses" (existentially quantified variables) that may appear in each case

It automates the common proof pattern of elimination rules for disjunctions combined with handling of existential quantifiers.

### Dependencies
- **Tactics**:
  - `DISJ_CASES_THEN2` - Tactic for disjunction elimination with different tactics for each branch
  - `CHOOSE_THEN` - Tactic for existential elimination
  - `REPEAT_TCL` - Higher-order tactic combinator that repeatedly applies a tactic converter
  - `end_itlist` - Function that applies an operation right-associatively to a list

### Porting notes
When porting to other systems:
- Ensure the target system has equivalent tactics for disjunction elimination and existential elimination
- Consider how the target system handles tactic combinators and right-associative list operations
- The exact behavior of repeated existential elimination followed by disjunction cases might need careful implementation in systems with different tactical frameworks

---

## (DISCARD_TAC:

### Name of formal statement
DISCARD_TAC

### Type of the formal statement
Tactic definition

### Formal Content
```ocaml
let (DISCARD_TAC: thm_tactic) =
  let truth = `T` in
  fun th (asl,w) ->
    if exists (aconv (concl th)) (truth::(map (concl o snd) asl))
    then ALL_TAC (asl,w)
    else failwith "DISCARD_TAC";;
```

### Informal statement
`DISCARD_TAC` is a tactic that takes a theorem `th` as input and, when applied to a goal `(asl,w)`:
- If the conclusion of `th` is alpha-equivalent (identical up to variable renaming) to either the constant `T` or the conclusion of any assumption in the assumption list `asl`, then it applies `ALL_TAC` (which does nothing) to the goal.
- Otherwise, it fails with the message "DISCARD_TAC".

In other words, this tactic discards (ignores) a theorem if it is trivially true or already appears as an assumption in the current goal.

### Informal proof
This is a tactic definition, not a theorem, so it doesn't have a proof. However, we can explain how it works:

1. It first defines `truth` as the constant `T` (logical truth).
2. The tactic takes a theorem `th` and a goal state `(asl,w)` (assumptions and target).
3. It checks if the conclusion of `th` is alpha-equivalent to either:
   - The constant `T`, or
   - The conclusion of any assumption in the assumption list `asl`
4. If the condition is met, it applies `ALL_TAC` which leaves the goal unchanged.
5. Otherwise, it fails with an error message "DISCARD_TAC".

### Mathematical insight
This tactic implements a common proof heuristic: ignore theorems that are trivially true or already known from the assumptions. It serves as a filter to prevent the prover from considering redundant information.

The tactic is useful in proof automation where multiple theorems might be tried, but some may be irrelevant because their conclusions are either trivially true or already part of the assumptions. In such cases, `DISCARD_TAC` allows the prover to quickly recognize and skip such theorems without wasting computational resources on them.

### Dependencies
#### Core functions
- `exists`: Checks if any element of a list satisfies a given predicate
- `aconv`: Checks for alpha-equivalence between terms
- `concl`: Extracts the conclusion of a theorem
- `map`: Applies a function to each element of a list
- `ALL_TAC`: The identity tactic that makes no changes to a goal
- `failwith`: Raises an exception with a specified message

### Porting notes
When porting to other systems:
- This is a utility tactic that can be implemented in any system that has a notion of tactics, goals, and alpha-equivalence.
- The tactic relies on the ability to inspect assumptions in the goal state and to test for alpha-equivalence between terms, which most proof assistants support.
- In some systems (like Lean or Coq), this might be implemented as part of a larger automation framework rather than as a standalone tactic.

---

## (CHECK_ASSUME_TAC:

### CHECK_ASSUME_TAC

### Type of the formal statement
- new_definition (tactic)

### Formal Content
```ocaml
let (CHECK_ASSUME_TAC: thm_tactic) =
  fun gth ->
    FIRST [CONTR_TAC gth;  ACCEPT_TAC gth;
           DISCARD_TAC gth; ASSUME_TAC gth];;
```

### Informal statement
`CHECK_ASSUME_TAC` is a higher-order tactic that takes a theorem `gth` and applies the first applicable tactic from a sequence of tactics:
1. `CONTR_TAC gth`: Attempts to prove a goal by deriving a contradiction from `gth`
2. `ACCEPT_TAC gth`: Attempts to directly prove the goal using `gth`
3. `DISCARD_TAC gth`: Adds `gth` as an assumption and continues if it cannot be used to solve the goal directly
4. `ASSUME_TAC gth`: Adds `gth` to the assumptions and continues

The tactic attempts each of these in order, stopping at the first one that succeeds.

### Informal proof
This is a tactic definition, not a theorem, so it doesn't have a proof. The definition constructs a tactic using the `FIRST` tactical, which tries each tactic in the list in order and applies the first one that succeeds.

### Mathematical insight
`CHECK_ASSUME_TAC` provides a convenient way to utilize a theorem in a proof, with a preference order for how to use it most effectively:
1. First, it checks if the theorem leads to a contradiction, which would solve the goal immediately
2. Next, it checks if the theorem directly proves the goal
3. If not, it checks if the theorem can be discarded after adding it to assumptions
4. Finally, it adds the theorem to the assumptions and continues

This ordering represents a most-to-least effective use of a theorem in a proof, trying the most powerful applications first. It provides a single tactic that automatically selects the most appropriate way to use a given theorem.

### Dependencies
- `FIRST`: A tactical that tries each tactic in a list until one succeeds
- `CONTR_TAC`: Tactic that derives a contradiction
- `ACCEPT_TAC`: Tactic that completes a goal using a theorem
- `DISCARD_TAC`: Tactic that adds a theorem to assumptions if it's not directly useful
- `ASSUME_TAC`: Tactic that adds a theorem to the assumptions

### Porting notes
When porting to other systems:
- This kind of multi-purpose tactic may need to be adapted to the tactic framework of the target system
- The order of operations is significant and should be preserved
- Consider how each of the component tactics (`CONTR_TAC`, `ACCEPT_TAC`, etc.) map to equivalent tactics in the target system
- In some systems, tactics may handle contradictions or goal solving automatically, so the explicit check order may need adjustment

---

## (FILTER_GEN_TAC:

### FILTER_GEN_TAC

### Type of the formal statement
- tactic definition

### Formal Content
```ocaml
let (FILTER_GEN_TAC: term -> tactic) =
  fun tm (asl,w) ->
    if is_forall w && not (tm = fst(dest_forall w)) then
        GEN_TAC (asl,w)
    else failwith "FILTER_GEN_TAC";;
```

### Informal statement
This is a custom tactic `FILTER_GEN_TAC` that takes a term `tm` as input and produces a tactic. The tactic applies to a goal with universally quantified formula when the bound variable is not equal to the input term `tm`. In that case, it calls the built-in `GEN_TAC` tactic. If the goal is not universally quantified or if the bound variable equals `tm`, the tactic fails with the message "FILTER_GEN_TAC".

### Informal proof
This is a tactic definition, not a theorem proof. The implementation:

1. Takes a term `tm` and a goal consisting of assumptions `asl` and conclusion `w`
2. Checks if the goal's conclusion `w` is a universal quantification (using `is_forall`)
3. Checks if the bound variable of the universal quantification is different from `tm`
4. If both conditions are true, applies the standard `GEN_TAC` tactic to the goal
5. Otherwise, fails with the message "FILTER_GEN_TAC"

### Mathematical insight
This tactic serves as a selective version of the standard `GEN_TAC` tactic in HOL Light. The standard `GEN_TAC` automatically handles any universally quantified formula by instantiating the outermost bound variable. `FILTER_GEN_TAC` adds a filter that only processes quantified variables that don't match a specified term.

This is useful in proof automation where you want to instantiate certain quantified variables but leave others untouched. For example, when processing a complex formula with multiple quantifiers, you might want to handle some variables differently than others based on their names or properties.

### Dependencies
- `GEN_TAC`: The standard tactic that instantiates the bound variable in a universally quantified formula with a new variable

### Porting notes
When porting to other proof assistants:
- Make sure the target system has a way to inspect the bound variable in a quantified formula
- Check if the target system allows selective application of tactics based on term structure
- The equivalent in other systems might require different implementation approaches depending on how tactics are represented
- Some systems may already have more sophisticated tactics for selective instantiation of quantifiers

---

## (FILTER_DISCH_THEN:

### Name of formal statement
FILTER_DISCH_THEN

### Type of the formal statement
Tactic definition (let binding)

### Formal Content
```ocaml
let (FILTER_DISCH_THEN: thm_tactic -> term -> tactic) =
  fun ttac tm (asl,w) ->
    if is_neg_imp w && not (free_in tm (fst(dest_neg_imp w))) then
      DISCH_THEN ttac (asl,w)
    else failwith "FILTER_DISCH_THEN";;
```

### Informal statement
`FILTER_DISCH_THEN` is a specialized tactic combinator that takes:
- A theorem-tactic function `ttac` (which applies a tactic based on a theorem)
- A term `tm`
- A goal represented as `(asl,w)` where `asl` is the assumption list and `w` is the goal formula

It applies `DISCH_THEN ttac` to the goal if:
1. The goal `w` is a negative implication (of the form `¬(P ⇒ Q)`)
2. The term `tm` does not appear free in `P` (the antecedent of the negative implication)

Otherwise, it fails with the message "FILTER_DISCH_THEN".

### Informal proof
This is a tactic definition rather than a theorem, so it doesn't have a formal proof. The implementation logic works as follows:

- The tactic checks if the goal `w` is of the form `¬(P ⇒ Q)` using the `is_neg_imp` function
- It then checks that the specified term `tm` doesn't appear free in `P` (the antecedent of the implication inside the negation) using the `free_in` function and `fst(dest_neg_imp w)`
- If both conditions are satisfied, it applies the `DISCH_THEN ttac` tactic to the goal
- Otherwise, it fails with an error message

### Mathematical insight
This tactic is a specialized combinator used in HOL Light's proof automation. It's particularly useful in situations where you want to apply a theorem-producing tactic to a goal with a negated implication, but only when the specified term doesn't appear in the antecedent.

The tactic acts as a filter - it allows the application of `DISCH_THEN ttac` only when certain structural conditions are met. This provides a way to make proof scripts more robust by preventing the application of tactics in situations where they would lead to unwanted proof states.

The functionality is particularly useful in conditional rewriting and other automation contexts where controlling when and how tactics are applied is important for guiding the proof effectively.

### Dependencies
#### Functions Used
- `is_neg_imp`: Tests if a term is a negative implication
- `free_in`: Checks if a term appears free in another term
- `dest_neg_imp`: Destructs a negative implication term
- `DISCH_THEN`: The base tactic that this function filters/wraps

### Porting notes
When porting this tactic to another proof assistant:
- Ensure the target system has support for examining the structure of goals (negative implications)
- The concept of free variables and checking for their presence needs to be available
- The equivalent of `DISCH_THEN` needs to exist in the target system, or you may need to implement it
- The failure mechanism should be handled appropriately in the target system's tactic language

In systems with different goal representations or tactic models, you might need to adjust the implementation significantly while preserving the core functionality of conditional application based on goal structure.

---

## FILTER_STRIP_THEN

### FILTER_STRIP_THEN

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let FILTER_STRIP_THEN ttac tm =
  FIRST [FILTER_GEN_TAC tm; FILTER_DISCH_THEN ttac tm; CONJ_TAC];;
```

### Informal statement
`FILTER_STRIP_THEN` is a higher-order tactic that applies one of three possible tactics to a term `tm`:
1. Try `FILTER_GEN_TAC tm` first
2. If that fails, try `FILTER_DISCH_THEN ttac tm`
3. If both fail, try `CONJ_TAC`

This tactic takes two arguments:
- `ttac`: A tactic transformer (a function that takes a theorem and returns a tactic)
- `tm`: A term to be used with the filtering tactics

### Informal proof
This is a definition, not a theorem, so it doesn't have a proof. The definition creates a tactic that attempts three different tactics in sequence using the `FIRST` combinator, which tries each tactic in the list and stops at the first one that succeeds.

### Mathematical insight
`FILTER_STRIP_THEN` is a tactical function used in interactive theorem proving to handle stripping off outer logical connectives in one step. It's designed to:

1. First try to handle universal quantification with `FILTER_GEN_TAC`
2. If that fails, try to handle implications with `FILTER_DISCH_THEN`
3. If both fail, try to handle conjunctions with `CONJ_TAC`

This pattern is extremely common in interactive theorem proving - stripping away outer logical connectives to get to the core of a goal. This tactical automates that process in a flexible way by allowing the user to specify what should be done with assumptions that are created during the stripping process.

The name "STRIP" in HOL Light typically refers to tactics that strip off various outer connectives from a goal.

### Dependencies
- Tactical: `FIRST`
- Tactics: `FILTER_GEN_TAC`, `FILTER_DISCH_THEN`, `CONJ_TAC`

### Porting notes
When porting this to other systems:
1. Most theorem provers have similar tactical combinators like `FIRST` that try tactics in sequence
2. The filtering tactics would need to be ported first
3. The exact semantics of how tactics handle failure might differ between systems, which could affect the behavior of this tactic

---

## FILTER_DISCH_TAC

### FILTER_DISCH_TAC

### Type of the formal statement
- Tactical (a proof tactic definition)

### Formal Content
```ocaml
let FILTER_DISCH_TAC = FILTER_DISCH_THEN STRIP_ASSUME_TAC;;
```

### Informal statement
FILTER_DISCH_TAC is a tactic that processes a goal with an implication by moving the antecedent to the assumption list, then applies STRIP_ASSUME_TAC to break down this assumption if it has conjunctive structure.

Specifically, if the current goal is of the form `p ⇒ q`, this tactic:
1. Moves the antecedent `p` to the assumption list
2. Applies STRIP_ASSUME_TAC to break down `p` into its components if it contains conjunctions

### Informal proof
This is a tactical definition rather than a theorem, so it doesn't have a proof in the traditional sense. The definition simply composes two existing tactics:

```
FILTER_DISCH_TAC = FILTER_DISCH_THEN STRIP_ASSUME_TAC
```

This defines FILTER_DISCH_TAC as an application of FILTER_DISCH_THEN with STRIP_ASSUME_TAC as its argument, creating a new tactic that performs both operations in sequence.

### Mathematical insight
- This tactical is a convenience combination that handles implication-based goals by moving the antecedent to assumptions and then breaking it down.
- It's part of HOL Light's collection of tactics for manipulating implications and assumptions in a goal.
- This tactical is useful for automatically handling implications where the antecedent has a conjunctive structure, saving the user from writing multiple tactic applications.
- This pattern (moving an antecedent to assumptions and then decomposing it) is common enough in proofs to warrant its own dedicated tactical.

### Dependencies
- Tacticals:
  - `FILTER_DISCH_THEN`: A tactical that processes an implication by moving the antecedent to the assumption list and then applies a provided tactic to the assumption
  - `STRIP_ASSUME_TAC`: A tactic that breaks down assumptions with conjunctive structure

### Porting notes
- When implementing this in other proof assistants, ensure the system has similar concepts for:
  1. Moving antecedents to assumptions
  2. Breaking down conjunctive assumptions
- In systems with different tactical models, you may need to adapt this to match the host system's approach to tactic composition.
- This tactical is relatively straightforward and should have analogs in most theorem provers, though the exact syntax and behavior might differ.

---

## FILTER_STRIP_TAC

### FILTER_STRIP_TAC
- FILTER_STRIP_TAC

### Type of the formal statement
- Tactic/conversion definition

### Formal Content
```ocaml
let FILTER_STRIP_TAC = FILTER_STRIP_THEN STRIP_ASSUME_TAC;;
```

### Informal statement
This defines a tactic `FILTER_STRIP_TAC` as a specialized application of the `FILTER_STRIP_THEN` tactic with the `STRIP_ASSUME_TAC` tactic as its argument.

In more detail, `FILTER_STRIP_TAC` applies the `STRIP_ASSUME_TAC` tactic to the theorems that pass through the filtering logic of `FILTER_STRIP_THEN`. This means it will:
1. Filter theorems according to some criteria (handled by `FILTER_STRIP_THEN`)
2. Apply the strip and assume tactic to the theorems that pass the filter

### Informal proof
This is a direct definition that binds the identifier `FILTER_STRIP_TAC` to the expression `FILTER_STRIP_THEN STRIP_ASSUME_TAC`. No proof is needed as this is a definition.

### Mathematical insight
`FILTER_STRIP_TAC` is a utility tactical that combines filtering with assumption stripping in HOL Light. It's a convenience tactic that allows users to filter theorems and then immediately strip and assume them in a single step.

This tactic is particularly useful when processing theorems where you want to:
1. Only consider certain theorems based on some criteria
2. Break down the structure of those theorems (using `STRIP_TAC`)
3. Add the resulting components to the assumptions

By combining these operations, it reduces the verbosity of proof scripts and makes them more readable.

### Dependencies
#### Tactics
- `FILTER_STRIP_THEN`: The filtering tactical that determines which theorems are processed
- `STRIP_ASSUME_TAC`: The tactic that breaks down and assumes theorems

### Porting notes
When porting to other systems, consider:
1. Whether the target system has similar filtering mechanisms for tactics
2. How assumption handling differs in the target system
3. Whether the target system has equivalent strip tactics for breaking down complex theorems

This tactic would be straightforward to implement in systems with good tactical support, but might require more work in systems where filtering and tactical composition is less flexible.

---

## RES_CANON

### RES_CANON
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- Function

### Formal Content
```ocaml
let RES_CANON =
    let not_elim th =
      if is_neg (concl th) then true,(NOT_ELIM th) else (false,th) in
    let rec canon fl th =
       let w = concl th in
       if (is_conj w) then
          let (th1,th2) = CONJ_PAIR th in (canon fl th1) @ (canon fl th2) else
       if ((is_imp w) && not(is_neg w)) then
          let ante,conc = dest_neg_imp w in
          if (is_conj ante) then
             let a,b = dest_conj ante in
             let cth = NOT_MP th (CONJ (ASSUME a) (ASSUME b)) in
             let th1 = DISCH b cth and th2 = DISCH a cth in
                 (canon true (DISCH a th1)) @ (canon true (DISCH b th2)) else
          if (is_disj ante) then
             let a,b = dest_disj ante in
             let ath = DISJ1 (ASSUME a) b and bth = DISJ2 a (ASSUME b) in
             let th1 = DISCH a (NOT_MP th ath) and
                 th2 = DISCH b (NOT_MP th bth) in
                 (canon true th1) @ (canon true th2) else
          if (is_exists ante) then
             let v,body = dest_exists ante in
             let newv = variant (thm_frees th) v in
             let newa = subst [newv,v] body in
             let th1 = NOT_MP th (EXISTS (ante, newv) (ASSUME newa)) in
                 canon true (DISCH newa th1) else
             map (GEN_ALL o (DISCH ante)) (canon true (UNDISCH th)) else
       if (is_eq w && (type_of (rand w) = `:bool`)) then
          let (th1,th2) = EQ_IMP_RULE th in
          (if fl then [GEN_ALL th] else []) @ (canon true th1) @ (canon true th2) else
       if (is_forall w) then
           let vs,body = strip_forall w in
           let fvs = thm_frees th in
           let vfn = fun l -> variant (l @ fvs) in
           let nvs = itlist (fun v nv -> let v' = vfn nv v in (v'::nv)) vs [] in
               canon fl (SPECL nvs th) else
       if fl then [GEN_ALL th] else [] in
    fun th -> try let args = map (not_elim o SPEC_ALL) (CONJUNCTS (SPEC_ALL th)) in
                  let imps = flat (map (map GEN_ALL o (uncurry canon)) args) in
                  check (fun l -> l <> []) imps
              with Failure _ ->
                failwith "RES_CANON: no implication is derivable from input thm.";;
```

### Informal statement

`RES_CANON` is a function that transforms a theorem into a list of clausal form theorems suitable for resolution. The function performs the following operations:

1. It converts the theorem into conjunctive normal form by:
   - Breaking conjunctions (`∧`) into separate theorems
   - Converting implications (`⇒`) by handling special cases for:
     - Conjunctive antecedents (`a ∧ b ⇒ c`)
     - Disjunctive antecedents (`a ∨ b ⇒ c`)
     - Existential antecedents (`∃x. P(x) ⇒ c`)
   - Transforming equivalences (`⇔`)
   - Instantiating universal quantifiers (`∀`)

2. It applies the appropriate rules to put formulas into a canonical resolution form.

The function returns a list of generalized clausal theorems derived from the input theorem, throwing an error if no implications can be derived.

### Informal proof

The implementation follows these key steps:

- An auxiliary function `not_elim` determines if a formula is a negation and, if so, eliminates the negation.
- The main recursive function `canon` traverses the formula structure:
  - For conjunctions (`a ∧ b`), it splits them and applies `canon` to each part
  - For implications with complex antecedents, it:
    - For conjunctive antecedents (`(a ∧ b) ⇒ c`), converts to `a ⇒ (b ⇒ c)`
    - For disjunctive antecedents (`(a ∨ b) ⇒ c`), converts to `(a ⇒ c) ∧ (b ⇒ c)`
    - For existential antecedents (`(∃x. P(x)) ⇒ c`), instantiates with a fresh variable
  - For boolean equivalences, converts to bidirectional implications
  - For universal quantifiers, instantiates with fresh variables
  
- The main function:
  1. Takes the input theorem and applies `SPEC_ALL` and `CONJUNCTS` to break it into its component parts
  2. For each part, applies `not_elim` and then `canon` to transform it into clausal form
  3. Generalizes each resulting theorem and returns the non-empty list or fails

The transformation ensures the resulting theorems are in a format conducive to resolution-based theorem proving.

### Mathematical insight

This function is a crucial component for implementing resolution-based theorem proving in HOL Light. Resolution is a rule of inference used extensively in automated theorem proving, particularly for first-order logic.

The key insight is that resolution works on clauses (disjunctions of literals), so theorems must be converted to a specific canonical form. `RES_CANON` transforms arbitrary HOL theorems into appropriate clausal representations, handling the complexity of logical connectives, quantifiers, and their interactions.

The transformation applies a series of logical equivalences to systematically convert formulas into clausal normal form, similar to the process often used in resolution-based theorem provers but adapted to the specifics of HOL Light's theorem representation.

This function bridges the gap between HOL Light's general theorem representation and the specialized form needed for resolution techniques.

### Dependencies

#### Theorems
- `NOT_ELIM`: Eliminates negation from a negated theorem
- `CONJ_PAIR`: Splits a conjunction into its components
- `NOT_MP`: Specialized modus ponens with negation
- `DISCH`: Discharges an assumption
- `DISJ1`, `DISJ2`: Introduction rules for disjunction
- `EXISTS`: Existential introduction
- `UNDISCH`: Removes an assumption
- `GEN_ALL`: Universally quantifies all free variables
- `EQ_IMP_RULE`: Converts an equivalence into two implications
- `SPECL`: Specializes multiple universal quantifiers
- `CONJUNCTS`: Splits conjunctions into a list of theorems
- `SPEC_ALL`: Specializes all universal quantifiers

### Porting notes
When porting to other systems:
1. Be aware that handling of free variables and variable capture may differ between systems
2. The conversion process relies heavily on HOL Light's theorem manipulation primitives - in other systems you may need alternative approaches
3. The implementation makes assumptions about the representation of logical connectives that may not hold in other systems
4. The function implements DNF-to-CNF conversion techniques that may be available as built-in tactics in other systems
5. Resolution-specific transformations may need adjustment based on how the target system implements resolution

---

## IMP_RES_THEN,RES_THEN

### NAME OF FORMAL STATEMENT
IMP_RES_THEN, RES_THEN

### TYPE OF THE FORMAL STATEMENT
new_definition (pair of tactics)

### FORMAL CONTENT
```ocaml
let IMP_RES_THEN,RES_THEN =
  let MATCH_MP impth =
      let sth = SPEC_ALL impth in
      let matchfn = (fun (a,b,c) -> b,c) o
                    term_match [] (fst(dest_neg_imp(concl sth))) in
         fun th -> NOT_MP (INST_TY_TERM (matchfn (concl th)) sth) th in
  let check st l = (if l = [] then failwith st else l) in
  let IMP_RES_THEN ttac impth =
      let ths = try RES_CANON impth with Failure _ -> failwith "IMP_RES_THEN: no implication" in
      ASSUM_LIST
       (fun asl ->
        let l = itlist (fun th -> (@) (mapfilter (MATCH_MP th) asl)) ths [] in
        let res = check "IMP_RES_THEN: no resolvents " l in
        let tacs = check "IMP_RES_THEN: no tactics" (mapfilter ttac res) in
        EVERY tacs) in
  let RES_THEN ttac (asl,g) =
      let asm = map snd asl in
      let ths = itlist (@) (mapfilter RES_CANON asm) [] in
      let imps = check "RES_THEN: no implication" ths in
      let l = itlist (fun th -> (@) (mapfilter (MATCH_MP th) asm)) imps [] in
      let res = check "RES_THEN: no resolvents " l in
      let tacs = check "RES_THEN: no tactics" (mapfilter ttac res) in
          EVERY tacs (asl,g) in
  IMP_RES_THEN,RES_THEN;;
```

### INFORMAL STATEMENT
This definition creates two higher-order tactics for resolution-style reasoning in HOL Light:

1. `IMP_RES_THEN`: A tactic that takes a tactic-producing function `ttac` and an implication theorem `impth`, resolves `impth` with assumptions in the goal to produce new theorems, applies `ttac` to each resolved theorem, and applies all resulting tactics in sequence.

2. `RES_THEN`: A tactic that takes a tactic-producing function `ttac`, finds implications among the assumptions in the current goal, resolves these implications with other assumptions to produce new theorems, applies `ttac` to each resolved theorem, and applies all resulting tactics in sequence.

Both tactics implement resolution, a proof technique from automated theorem proving, where we derive new facts by combining implication theorems with known facts.

### INFORMAL PROOF
The definition implements two resolution tactics through several helper functions:

1. The `MATCH_MP` helper function:
   - Takes an implication theorem `impth`
   - Makes it fully specialized with `SPEC_ALL`
   - Creates a term matching function for the antecedent of the implication
   - Returns a function that matches a theorem against this antecedent and applies modus ponens

2. The `check` helper function:
   - Validates that a list is non-empty, raising a specific failure message if it is

3. `IMP_RES_THEN` implementation:
   - Canonicalizes the implication theorem using `RES_CANON`
   - Retrieves assumptions from the goal using `ASSUM_LIST`
   - For each canonicalized theorem, attempts to match it with every assumption
   - Collects all successfully resolved theorems
   - Applies the provided tactic function `ttac` to each resolved theorem
   - Combines all resulting tactics with `EVERY`

4. `RES_THEN` implementation:
   - Extracts assumptions from the goal
   - Canonicalizes all implications in the assumptions
   - Resolves each canonicalized implication with each assumption
   - Applies the provided tactic function `ttac` to each resolved theorem
   - Combines all resulting tactics with `EVERY`

### MATHEMATICAL INSIGHT
Resolution is a fundamental proof technique in automated theorem proving. These tactics implement a form of forward reasoning where new facts are derived by combining existing implications with known facts. 

The key differences between the two tactics are:
- `IMP_RES_THEN` applies a given implication theorem against assumptions in the goal
- `RES_THEN` finds implications among the assumptions themselves and resolves them with other assumptions

These tactics are particularly useful for developing derived rules that extract information from assumptions and apply appropriate tactics based on that information. They represent a bridge between the declarative nature of theorems and the procedural nature of proof tactics, allowing the user to specify how to use derived facts in a flexible way.

### DEPENDENCIES
#### Tactics and transformations
- `RES_CANON`: Canonicalizes theorems into a form suitable for resolution
- `SPEC_ALL`: Specializes all universally quantified variables in a theorem
- `NOT_MP`: Modus ponens for implications with negated conclusions
- `INST_TY_TERM`: Instantiates type variables and terms in a theorem
- `ASSUM_LIST`: Retrieves assumptions from a goal
- `EVERY`: Sequentially applies a list of tactics

#### Term manipulation
- `dest_neg_imp`: Destructs a negated implication
- `term_match`: Matches terms and creates substitutions
- `mapfilter`: Maps a function over a list and filters out failures

### PORTING NOTES
When porting these tactics to another system:

1. Many proof assistants have different paradigms for tactics and may not directly support this style of forward reasoning. Consider adapting the resolution concept to match the target system's idioms.

2. The error handling approach using `failwith` and exception catching is HOL Light specific. Other systems may have more structured ways to handle tactic failures.

3. `RES_CANON` is a key dependency that normalizes theorems for resolution. Ensure you understand how it works when porting, as different systems might have different canonical forms for implications.

4. The term matching mechanism (`term_match`) might have different interfaces in other systems, especially regarding how type variables are handled.

5. These tactics handle polymorphic theorems through type instantiation, which might need different approaches in systems with different type systems.

---

## IMP_RES_TAC

### IMP_RES_TAC
- IMP_RES_TAC

### Type of the formal statement
- Tactic definition

### Formal Content
```ocaml
let IMP_RES_TAC th g =
  try IMP_RES_THEN (REPEAT_GTCL IMP_RES_THEN STRIP_ASSUME_TAC) th g
  with Failure _ -> ALL_TAC g;;
```

### Informal statement
`IMP_RES_TAC` is a tactic that takes a theorem `th` and applies it to a goal `g` by:

1. Trying to apply `IMP_RES_THEN` with a complex composition of tactics to the theorem `th` on goal `g`
2. If that fails, applying the identity tactic `ALL_TAC` to goal `g`

Specifically, it tries to:
- Apply the theorem as a resolution rule
- Extract the resulting implications 
- Repeatedly apply resolution
- Assume and strip the resulting theorems

### Informal proof
This is a tactic definition rather than a theorem, so it doesn't have a proof in the traditional sense. 

The tactic is defined as a function that:
1. Attempts to apply the more complex tactic `IMP_RES_THEN (REPEAT_GTCL IMP_RES_THEN STRIP_ASSUME_TAC) th` to the goal
2. If this application fails (caught by the exception handler), it falls back to applying `ALL_TAC`, which leaves the goal unchanged

The nested structure of tactics works as follows:
- `STRIP_ASSUME_TAC` strips conjunctions and existentials while adding assumptions to the goal's context
- `IMP_RES_THEN` applies resolution with the given theorem and passes the resulting theorems to another tactic
- `REPEAT_GTCL` repeatedly applies a goal-then-continuation tactic
- The composition creates a powerful tactic that tries to thoroughly apply the theorem by resolution and assumption

### Mathematical insight
`IMP_RES_TAC` is a higher-level tactic designed for convenient forward reasoning in proofs. It applies a theorem as an implication and uses the conclusions to make progress on the goal. Some key insights:

1. It embodies forward reasoning - using known facts to derive new ones that help with the goal
2. The error handling makes it safe to use even when the theorem doesn't apply
3. It combines multiple simpler tactics to create a more powerful compound tactic
4. It's particularly useful for applying conditional theorems (implications) where the antecedent matches facts already known in the goal context

This tactic is part of HOL Light's standard tactical library and represents an important tool for managing complex implications during interactive proof development.

### Dependencies
- Tactics and tacticals: `IMP_RES_THEN`, `REPEAT_GTCL`, `STRIP_ASSUME_TAC`, `ALL_TAC`

### Porting notes
When porting to other proof assistants:
1. Many systems have similar concepts for applying resolution and handling assumptions
2. The error handling pattern (try/with) may need adaptation to the target system's exception mechanism
3. The exact behavior might need adjustment based on how the target system handles implications and assumptions
4. Some systems might have built-in tacticals that achieve similar results with different names

---

## RES_TAC

### Name of formal statement
RES_TAC

### Type of the formal statement
Theorem proving tactic (ML function)

### Formal Content
```ocaml
let RES_TAC g =
  try RES_THEN (REPEAT_GTCL IMP_RES_THEN STRIP_ASSUME_TAC) g
  with Failure _ -> ALL_TAC g;;
```

### Informal statement
`RES_TAC` is a theorem proving tactic in HOL Light that applies resolution with all available theorems (hypotheses) in the goal. It works as follows:

1. It applies `RES_THEN` to each hypothesis in the goal.
2. For each hypothesis, it repeatedly resolves it with other hypotheses using `IMP_RES_THEN`.
3. After resolution, it attempts to strip the resulting theorem and add the components as new assumptions using `STRIP_ASSUME_TAC`.
4. If the resolution process fails at any point, the tactic falls back to `ALL_TAC` (which does nothing).

The tactic attempts to derive new facts from existing assumptions by applying modus ponens (implication elimination) repeatedly, essentially performing forward chaining inference.

### Informal proof
The implementation of `RES_TAC` is straightforward:

1. It first attempts to use `RES_THEN` with a composition of `REPEAT_GTCL`, `IMP_RES_THEN`, and `STRIP_ASSUME_TAC`:
   - `RES_THEN` operates on each hypothesis in the goal
   - `IMP_RES_THEN` applies modus ponens between hypotheses
   - `STRIP_ASSUME_TAC` breaks down the results into simpler assumptions
   - `REPEAT_GTCL` applies this process repeatedly

2. If this process fails for any reason, it falls back to `ALL_TAC`, which is the identity tactic that leaves the goal unchanged.

This implementation creates an automated forward reasoning mechanism that tries to extract as much information as possible from the existing hypotheses.

### Mathematical insight
`RES_TAC` implements a form of automated forward reasoning through resolution, which is a fundamental method in automated theorem proving. The tactic performs a depth-first exploration of what can be derived from the available hypotheses.

The key idea behind `RES_TAC` is to automatically derive all possible consequences from the current set of assumptions without requiring the user to manually apply modus ponens or similar rules. This is particularly useful when:

1. There are many assumptions in the goal that could potentially interact
2. The user wants to see what follows from the assumptions before deciding on the next step
3. The proof requires chained implications where the intermediate steps aren't obvious

This tactic embodies the principle of exhaustive forward reasoning, which complements the more common backward reasoning style in interactive theorem provers. While backward reasoning starts from the goal and works toward the assumptions, forward reasoning starts from the assumptions and derives new facts that might help prove the goal.

### Dependencies
- **Tactics**:
  - `RES_THEN` - Applies resolution with a given tactic to hypotheses
  - `IMP_RES_THEN` - Performs implication resolution
  - `STRIP_ASSUME_TAC` - Breaks down complex formulas into simpler assumptions
  - `REPEAT_GTCL` - Repeatedly applies a tactic transformer
  - `ALL_TAC` - The identity tactic that does nothing

### Porting notes
When porting `RES_TAC` to other proof assistants:

1. The concept of resolution might be implemented differently in other systems. For example, Isabelle has "Classical Reasoner" techniques, and Lean uses its "simp" tactic framework.

2. The error handling approach (falling back to `ALL_TAC`) is specific to HOL Light's tactic framework. Other systems might require different patterns for graceful failure.

3. The tactic might be less necessary in systems with more powerful automation. For example, Lean's `simp` or Isabelle's `auto` might subsume much of what `RES_TAC` does.

4. The exact behavior of repeatedly applying resolution until no further progress is made might need special attention to ensure termination in other systems.

---

## prove_rep_fn_one_one

### prove_rep_fn_one_one

### Type of the formal statement
- Utility function

### Formal Content
```ocaml
let prove_rep_fn_one_one th =
  try let thm = CONJUNCT1 th in
      let A,R = (I F_F rator) (dest_comb(lhs(snd(dest_forall(concl thm))))) in
      let _,[aty;rty] = dest_type (type_of R) in
      let a = mk_primed_var("a",aty) in let a' = variant [a] a in
      let a_eq_a' = mk_eq(a,a') and
          Ra_eq_Ra' = mk_eq(mk_comb(R,a),mk_comb (R,a')) in
      let th1 = AP_TERM A (ASSUME Ra_eq_Ra') in
      let ga1 = genvar aty and ga2 = genvar aty in
      let th2 = SUBST [SPEC a thm,ga1;SPEC a' thm,ga2] (mk_eq(ga1,ga2)) th1 in
      let th3 = DISCH a_eq_a' (AP_TERM R (ASSUME a_eq_a')) in
          GEN a (GEN a' (IMP_ANTISYM_RULE (DISCH Ra_eq_Ra' th2) th3))
  with Failure _ -> failwith "prove_rep_fn_one_one";;
```

### Informal statement
The `prove_rep_fn_one_one` function takes a theorem `th` and attempts to prove that a representation function is injective.

Given a theorem `th` of the form `∀a. P (R a)` where `R` is the representation function, this utility proves:
```
∀a a'. R(a) = R(a') ⇒ a = a'
```

The function expects `th` to be a theorem that contains a conjunct asserting a property about the image of a representation function.

### Informal proof
This utility function constructs a proof of injectivity using the following steps:

1. Extract the first conjunct of the input theorem `th`.
2. Identify the representation function `R` and its domain type `A`.
3. Generate two variables `a` and `a'` of the appropriate type.
4. To prove the injectivity property, the function builds bidirectional implications:
   - First, assume `R(a) = R(a')` and derive `a = a'` using substitution and the properties from the input theorem.
   - Second, assume `a = a'` and derive `R(a) = R(a')` by applying congruence.
5. Combine these implications into a bidirectional implication using `IMP_ANTISYM_RULE`.
6. Generalize the result for all `a` and `a'`.

The proof relies on the following HOL Light operations:
- `CONJUNCT1` to extract the first conjunct
- `ASSUME`, `DISCH`, and `IMP_ANTISYM_RULE` for implication handling
- `AP_TERM` for congruence application
- `SUBST` for substitution
- `GEN` for universal quantification

### Mathematical insight
This utility function is part of HOL Light's type definition machinery. When defining a new type in HOL, it's often constructed as a subset of an existing type with a bijection between the new type and the subset. This function proves the injectivity (one-to-one) direction of that bijection.

The function works by extracting key information from a characteristic theorem provided when defining a new type, and then constructs a formal proof that the representation function is injective. This is a critical property to ensure the soundness of type definitions in HOL.

The injectivity of the representation function guarantees that distinct elements of the new type map to distinct elements in the host type, which is essential for the proper behavior of the newly defined type.

### Dependencies
- HOL Light's theorem manipulation primitives (`CONJUNCT1`, `AP_TERM`, `SUBST`, etc.)
- Type handling functions (`dest_type`, `type_of`)
- Term construction utilities (`mk_primed_var`, `variant`, `mk_eq`, etc.)

### Porting notes
When porting this to another proof assistant:
1. Consider the type definition mechanism of the target system, which might differ significantly from HOL Light's approach.
2. The proof construction is highly specific to HOL Light's representation of theorems and proofs. Other systems may have different primitive operations.
3. The error handling is minimal - in more robust systems, you might want to add better diagnostic information.
4. The function expects a very specific format for the input theorem - ensure this assumption holds in the target system or modify accordingly.

---

## prove_rep_fn_onto

### Name of formal statement
prove_rep_fn_onto

### Type of the formal statement
theorem/proof procedure

### Formal Content
```ocaml
let prove_rep_fn_onto th =
  try let [th1;th2] = CONJUNCTS th in
      let r,eq = (I F_F rhs)(dest_forall(concl th2)) in
      let RE,ar = dest_comb(lhs eq) and
          sr = (mk_eq o (fun (x,y) -> y,x) o dest_eq) eq in
      let a = mk_primed_var ("a",type_of ar) in
      let sra = mk_eq(r,mk_comb(RE,a)) in
      let ex = mk_exists(a,sra) in
      let imp1 = EXISTS (ex,ar) (SYM(ASSUME eq)) in
      let v = genvar (type_of r) and
          A = rator ar and
          s' = AP_TERM RE (SPEC a th1) in
      let th = SUBST[SYM(ASSUME sra),v](mk_eq(mk_comb(RE,mk_comb(A,v)),v))s' in
      let imp2 = CHOOSE (a,ASSUME ex) th in
      let swap = IMP_ANTISYM_RULE (DISCH eq imp1) (DISCH ex imp2) in
          GEN r (TRANS (SPEC r th2) swap)
  with Failure _ -> failwith "prove_rep_fn_onto";;
```

### Informal statement
`prove_rep_fn_onto` is a HOL Light procedure that takes a theorem `th` and proves that a representation function is onto (surjective). 

Given a theorem `th` that contains two conjuncts:
1. A theorem about a representation function `RE`
2. A theorem of form `∀r. RE(ar) = sr`

The procedure proves that the representation function `RE` is surjective, showing that `∀r. ∃a. r = RE(a)`.

### Informal proof
The proof procedure works as follows:

1. First, it extracts the two conjuncts from theorem `th`: `th1` and `th2`.

2. From `th2`, it extracts the variable `r` and equation `eq` where `eq` is of the form `RE(ar) = sr`.

3. It constructs an existential statement `∃a. r = RE(a)` (called `ex`).

4. The proof proceeds in two directions to establish logical equivalence:

   * Forward direction (`imp1`): Using `eq` (which states `RE(ar) = sr`), it shows that `∃a. r = RE(a)` holds.
   
   * Backward direction (`imp2`): Assuming `∃a. r = RE(a)`, it uses `th1` (which likely contains behavior of the representation function) to show the original equation holds.

5. The procedure combines these implications using `IMP_ANTISYM_RULE` to establish equivalence.

6. Finally, it generalizes over `r` and uses transitivity to connect the result with the original theorem `th2`.

This proof effectively shows that for any `r`, there exists an `a` such that `r = RE(a)`, which is the definition of surjectivity for the representation function `RE`.

### Mathematical insight
This procedure is used in the context of quotient constructions or abstract data types in HOL Light. When defining a new type in HOL Light using `new_type_definition`, one needs to establish a bijection between the new type and a subset of an existing type. 

`prove_rep_fn_onto` helps establish the surjectivity part of this bijection, showing that every element in the codomain can be reached by applying the representation function to some element in the domain.

This is a crucial step in type definitions within HOL Light, as it ensures that the representation function properly maps between the abstract type and its concrete representation.

### Dependencies
#### Theorems
- `a` - A theorem involving logical manipulation

#### HOL Light Tactics and Procedures
- `CONJUNCTS` - Splits a conjunction into a list of theorems
- `dest_forall` - Destructs a universal quantification
- `dest_comb` - Destructs a function application
- `mk_primed_var` - Creates a primed variable
- `mk_eq` - Creates an equation
- `mk_exists` - Creates an existential quantification
- `EXISTS` - Introduces an existential quantifier
- `SYM` - Symmetry of equality
- `ASSUME` - Assumes a formula
- `genvar` - Generates a new variable
- `rator` - Extracts the operator from a combination
- `AP_TERM` - Applies a function to both sides of an equation
- `SPEC` - Instantiates a universal quantifier
- `SUBST` - Performs substitution
- `CHOOSE` - Uses the axiom of choice
- `IMP_ANTISYM_RULE` - Creates a logical equivalence from two implications
- `DISCH` - Discharges an assumption
- `GEN` - Generalizes a theorem
- `TRANS` - Transitivity of equality

### Porting notes
When porting this to another proof assistant:

1. Understand how the target system handles abstract data types and type definitions
2. Identify the equivalent of representation/abstraction functions in the target system
3. The proof relies on HOL Light's specific way of handling bijections for type definitions
4. Pay attention to the use of the axiom of choice (`CHOOSE`) which may be handled differently in other systems
5. This procedure is a higher-level proof tool rather than a theorem itself, so you may need to implement it as a tactic or automation in the target system

---

## prove_abs_fn_onto

### Name of formal statement
prove_abs_fn_onto

### Type of the formal statement
Function (theorem-producing function)

### Formal Content
```ocaml
let prove_abs_fn_onto th =
  try let [th1;th2] = CONJUNCTS th in
      let a,(A,R) = (I F_F ((I F_F rator)o dest_comb o lhs))
        (dest_forall(concl th1)) in
      let thm1 = EQT_ELIM(TRANS (SPEC (mk_comb (R,a)) th2)
                                (EQT_INTRO (AP_TERM R (SPEC a th1)))) in
      let thm2 = SYM(SPEC a th1) in
      let r,P = (I F_F (rator o lhs)) (dest_forall(concl th2)) in
      let ex = mk_exists(r,mk_conj(mk_eq(a,mk_comb(A,r)),mk_comb(P,r))) in
          GEN a (EXISTS(ex,mk_comb(R,a)) (CONJ thm2 thm1))
  with Failure _ -> failwith "prove_abs_fn_onto";;
```

### Informal statement
This is a theorem-producing function that takes a theorem `th` representing an abstraction-representation theorem pair and proves that the abstraction function is onto (surjective). 

Specifically, given a theorem of the form:
```
⊢ ∀a. A(R(a)) = a ∧ ∀r. P(r) ⇒ R(A(r)) = r
```
where:
- `A` is an abstraction function
- `R` is a representation function
- `P` is a predicate on representation values

The function produces the theorem:
```
⊢ ∀a. ∃r. a = A(r) ∧ P(r)
```
which states that for any `a` in the target type, there exists a representation `r` satisfying the predicate `P` such that `a` is the abstraction of `r`.

### Informal proof
The function works by unpacking the input theorem and constructing a proof as follows:

- First, split the input theorem `th` into its two conjuncts:
  - `th1`: `∀a. A(R(a)) = a`
  - `th2`: `∀r. P(r) ⇒ R(A(r)) = r`

- For a given `a`, we apply `R` to both sides of the instantiated `th1`: `A(R(a)) = a` to get `R(A(R(a))) = R(a)`

- We use `th2` with `r = R(a)` to show that `P(R(a)) ⇒ R(A(R(a))) = R(a)`, and from the previous step we can derive `P(R(a))` must be true

- We then use the instances of both theorems to construct:
  - `a = A(R(a))` (from the symmetry of instantiated `th1`)
  - `P(R(a))` (from the previous conclusion)

- Finally, we combine these to form the existential statement: `∃r. a = A(r) ∧ P(r)` by choosing `r = R(a)` and generalizing over `a`.

### Mathematical insight
This function is an important tool for establishing the surjectivity of abstraction functions when working with abstract data types or quotient types in HOL Light. It formalizes a key property of the abstraction-representation relationship: every element in the abstract type can be represented by at least one element in the representation type that satisfies the type invariant.

The theorem-producing function is particularly useful when defining new abstract types, as it proves that the abstraction function is surjective onto its codomain, which is often necessary to ensure the abstract type is well-defined and corresponds exactly to the intended mathematical concept.

### Dependencies
- CONJUNCTS - extracts the conjoined theorems from a conjunction
- SPEC - specializes a universally quantified theorem with a specific term
- SYM - takes a theorem of the form `⊢ s = t` and returns `⊢ t = s`
- TRANS - transitivity of equality
- AP_TERM - applies a function to both sides of an equation
- EQT_INTRO, EQT_ELIM - conversions between Boolean equality and truth
- EXISTS - existential introduction rule
- CONJ - forms the conjunction of two theorems
- GEN - universal generalization

### Porting notes
When porting this to other proof assistants:
1. The function assumes a specific format for the input theorem (a conjunction of two universally quantified implications). Ensure your formalization maintains this format.
2. Different systems may handle the relationship between boolean equality and logical implication differently.
3. The function uses pattern matching and exception handling for control flow, which may need adaptation in systems with different error handling models.
4. The representation-abstraction pattern is common in type definitions, but different systems may have built-in mechanisms for defining abstract types that automatically provide surjectivity theorems.

---

## prove_abs_fn_one_one

### Name of formal statement
prove_abs_fn_one_one

### Type of the formal statement
theorem

### Formal Content
```ocaml
let prove_abs_fn_one_one th =
  try let [th1;th2] = CONJUNCTS th in
      let r,P = (I F_F (rator o lhs)) (dest_forall(concl th2)) and
          A,R = (I F_F rator) (dest_comb(lhs(snd(dest_forall(concl th1))))) in
      let r' = variant [r] r in
      let as1 = ASSUME(mk_comb(P,r)) and as2 = ASSUME(mk_comb(P,r')) in
      let t1 = EQ_MP (SPEC r th2) as1 and t2 = EQ_MP (SPEC r' th2) as2 in
      let eq = (mk_eq(mk_comb(A,r),mk_comb(A,r'))) in
      let v1 = genvar(type_of r) and v2 = genvar(type_of r) in
      let i1 = DISCH eq
               (SUBST [t1,v1;t2,v2] (mk_eq(v1,v2)) (AP_TERM R (ASSUME eq))) and
          i2 = DISCH (mk_eq(r,r')) (AP_TERM A (ASSUME (mk_eq(r,r')))) in
      let thm = IMP_ANTISYM_RULE i1 i2 in
      let disch =  DISCH (mk_comb(P,r)) (DISCH (mk_comb(P,r')) thm) in
          GEN r (GEN r' disch)
  with Failure _ -> failwith "prove_abs_fn_one_one";;
```

### Informal statement
This function `prove_abs_fn_one_one` takes a theorem `th` and proves that an abstraction function `A` is injective on values satisfying a predicate `P`.

Given a theorem `th` of the form:
- `⊢ ∀r. P(r) ⇒ R(A(r)) = r`  (representation)
- `⊢ ∀a. P(R(a))`  (totality)

The function returns:
`⊢ ∀r r'. P(r) ⇒ P(r') ⇒ (A(r) = A(r') ⇔ r = r')`

This establishes that the abstraction function `A` is one-to-one on the domain defined by predicate `P`.

### Informal proof
The proof proceeds as follows:

1. Let `th1` and `th2` be the two conjuncts of the input theorem `th`:
   - `th1` : `⊢ ∀r. P(r) ⇒ R(A(r)) = r`
   - `th2` : `⊢ ∀a. P(R(a))`

2. For any `r` and `r'` satisfying `P`, we need to show `A(r) = A(r') ⇔ r = r'`.

3. For the direction `A(r) = A(r') ⇒ r = r'`:
   - Assume `A(r) = A(r')`
   - From `th1`, we know that `P(r) ⇒ R(A(r)) = r` and `P(r') ⇒ R(A(r')) = r'`
   - Since we assume `P(r)` and `P(r')`, we have `R(A(r)) = r` and `R(A(r')) = r'`
   - By our assumption `A(r) = A(r')`, we get `R(A(r)) = R(A(r'))`
   - Therefore, `r = r'`

4. For the direction `r = r' ⇒ A(r) = A(r')`:
   - This is straightforward: if `r = r'`, then obviously `A(r) = A(r')`

5. Combine both directions using the logical equivalence to get the final result:
   `⊢ ∀r r'. P(r) ⇒ P(r') ⇒ (A(r) = A(r') ⇔ r = r')`

### Mathematical insight
This theorem establishes injectivity of the abstraction function `A` on values satisfying a predicate `P`. In type theory and formal representations, the pair of functions `A` (abstraction) and `R` (representation) often forms an isomorphism between two types, where one type represents an abstraction of the other.

The condition `R(A(r)) = r` for all `r` satisfying `P` shows that `R` is a left inverse of `A` on the domain defined by `P`. This theorem then proves that `A` is injective on this domain, which is a necessary condition for `A` and `R` to form an isomorphism between the subtype defined by `P` and its image under `A`.

This is often used in HOL Light to establish type definitions and to prove properties about abstract data types. The theorem is particularly useful when defining new types as subsets of existing types, ensuring the proper correspondence between elements.

### Dependencies
- `CONJUNCTS`: Splits a conjunction into a list of its conjuncts
- `I`, `F_F`, `rator`, `lhs`, `dest_forall`, `dest_comb`: Various utility functions for term manipulation
- `variant`: Creates a variable with a fresh name
- `ASSUME`, `EQ_MP`, `SPEC`, `AP_TERM`, `DISCH`: Logical inference rules
- `IMP_ANTISYM_RULE`: Proves equivalence from implications in both directions
- `GEN`: Universal generalization

### Porting notes
When implementing this in another proof assistant:
1. The function manipulates terms directly using HOL Light's term manipulation functions, which might need different approaches in other systems.
2. The proof technique relies on extracting conjuncts and applying various rewrite rules, which should be adapted to the tactics available in the target system.
3. The handling of variable names and variant creation might differ in other systems.
4. The proof relies on logical equivalence through implications in both directions, a common pattern that should be available in most proof assistants.

---

## AC_CONV(assoc,sym)

### AC_CONV(assoc,sym)

### Type of the formal statement
- Conversion function

### Formal Content
```ocaml
let AC_CONV(assoc,sym) =
  let th1 = SPEC_ALL assoc
  and th2 = SPEC_ALL sym in
  let th3 = GEN_REWRITE_RULE (RAND_CONV o LAND_CONV) [th2] th1 in
  let th4 = SYM th1 in
  let th5 = GEN_REWRITE_RULE RAND_CONV [th4] th3 in
  EQT_INTRO o AC(end_itlist CONJ [th2; th4; th5]);;
```

### Informal statement
The `AC_CONV(assoc,sym)` is a conversion function that creates an AC (Associative-Commutative) conversion using the provided theorems for associativity (`assoc`) and commutativity (`sym`).

This conversion can be used to prove equality between terms that are equivalent modulo the AC properties of the operation. It takes two theorems as input:
1. `assoc` - A theorem proving the associativity property (typically in the form `∀x y z. x • (y • z) = (x • y) • z`)
2. `sym` - A theorem proving the commutativity property (typically in the form `∀x y. x • y = y • x`)

### Informal proof
The conversion is constructed as follows:

1. First, we fully specialize the theorems with `SPEC_ALL`:
   - `th1` = the specialized associativity theorem
   - `th2` = the specialized commutativity theorem

2. Then we apply the commutativity theorem to the left side of the right-hand side of the associativity theorem:
   - `th3` = result of rewriting `(x • y) • z` to `(y • x) • z` in the associativity theorem

3. Take the symmetric version of the associativity theorem:
   - `th4` = `(x • y) • z = x • (y • z)`

4. Apply this symmetric version to the right-hand side of `th3`:
   - `th5` = result of rewriting `th3` using `th4`

5. Finally, construct an AC conversion using the combined theorems:
   - Combine the commutativity theorem `th2`, the symmetric associativity `th4`, and the derived theorem `th5`
   - Create an AC conversion function with these theorems
   - Wrap the result in `EQT_INTRO` to convert the equation to a term of the form `⊢ t ⇔ T`

### Mathematical insight
This conversion provides a way to reason about terms involving associative and commutative operators. In mathematics, when dealing with operations that have these properties (like addition or multiplication), we often freely rearrange terms without explicitly mentioning the associative or commutative properties being used. 

The AC conversion automates this process in HOL Light, allowing the system to automatically recognize that expressions like `(a + b) + c`, `a + (b + c)`, `(b + a) + c`, etc., are all equivalent when `+` is associative and commutative.

This is particularly useful for simplifying complex expressions and for automated theorem proving where rearrangement of terms according to AC properties is frequently needed.

### Dependencies
- Dependent on the supplied associativity and commutativity theorems
- HOL Light utility functions:
  - `SPEC_ALL`
  - `GEN_REWRITE_RULE`
  - `RAND_CONV`
  - `LAND_CONV`
  - `SYM`
  - `EQT_INTRO`
  - `AC`
  - `end_itlist`
  - `CONJ`

### Porting notes
When porting to other proof assistants:
- The implementation relies heavily on HOL Light's conversion infrastructure
- Other proof assistants might have different mechanisms for handling associative-commutative rewriting
- Lean, Coq, and Isabelle have their own tactics or libraries for AC rewriting that might be more idiomatic to use than a direct port
- The specific rewriting strategy used here (applying commutativity to parts of terms) might need adaptation depending on how the target system handles term rewriting

---

## AC_RULE

### AC_RULE
- `AC_RULE`

### Type of the formal statement
- Function definition (not via `new_definition`)

### Formal Content
```ocaml
let AC_RULE ths = EQT_ELIM o AC_CONV ths;;
```

### Informal statement
This function `AC_RULE` takes a list of theorems `ths` and applies the associative-commutative conversion `AC_CONV` to them, followed by the elimination of the resulting equation-with-true (`EQT_ELIM`).

In mathematical terms, it applies associative-commutative reasoning based on the theorems in `ths` to simplify a term, and then extracts the final result from an equation of the form `t = T` to just `t`.

### Informal proof
This is a function definition that composes two operations:

1. `AC_CONV ths` - This applies associative-commutative reasoning using the theorems in `ths` to transform an input term.
2. `EQT_ELIM` - This extracts term `t` from an equation of the form `t = T` (true).

The composition `EQT_ELIM o AC_CONV ths` means first apply `AC_CONV ths` to the input, then apply `EQT_ELIM` to the result.

### Mathematical insight
`AC_RULE` is a convenience function that combines the power of associative-commutative rewriting with post-processing to produce a cleaner result. It's used to simplify expressions that involve operations with associative and commutative properties (like addition and multiplication).

This function is particularly useful because many arithmetic and logical operations satisfy associativity and commutativity. Using `AC_RULE` allows the system to automatically handle reordering and regrouping of terms according to these properties without requiring explicit step-by-step reasoning by the user.

### Dependencies
- Functions:
  - `AC_CONV`: Conversion for associative-commutative rewriting
  - `EQT_ELIM`: Eliminates equations with true, extracting the term

### Porting notes
When porting to another system:
1. Identify the equivalent of `AC_CONV` in the target system (may be called AC rewriting, or need to be explicitly defined)
2. Find or implement `EQT_ELIM` functionality
3. Ensure function composition syntax is adapted to the target system's conventions
4. Note that many modern proof assistants have built-in tactics for associative-commutative rewriting, which might provide similar functionality through different means

---

## (COND_CASES_TAC

### COND_CASES_TAC
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- Tactic definition

### Formal Content
```ocaml
let (COND_CASES_TAC :tactic) =
    let is_good_cond tm =
      try not(is_const(fst(dest_cond tm)))
      with Failure _ -> false in
    fun (asl,w) ->
      let cond = find_term (fun tm -> is_good_cond tm && free_in tm w) w in
      let p,(t,u) = dest_cond cond in
      let inst = INST_TYPE [type_of t, `:A`] COND_CLAUSES in
      let (ct,cf) = CONJ_PAIR (SPEC u (SPEC t inst)) in
      DISJ_CASES_THEN2
         (fun th -> SUBST1_TAC (EQT_INTRO th) THEN
               SUBST1_TAC ct THEN ASSUME_TAC th)
         (fun th -> SUBST1_TAC (EQF_INTRO th) THEN
               SUBST1_TAC cf THEN ASSUME_TAC th)
         (SPEC p EXCLUDED_MIDDLE)
         (asl,w) ;;
```

### Informal statement
This defines a tactic `COND_CASES_TAC` that performs case analysis on conditionals in the goal. The tactic:

1. Finds a conditional expression `if p then t else u` in the goal where the condition `p` is not a constant.
2. Creates a case split on whether `p` is true or false.
3. In each branch:
   - Substitutes the appropriate simplification (`t` if `p` is true, `u` if `p` is false)
   - Adds the condition to the assumptions

### Informal proof
The tactic is implemented by:

- Finding a suitable conditional term `if p then t else u` in the goal
- Extracting the condition `p` and the branches `t` and `u`
- Instantiating the `COND_CLAUSES` theorem (which states basic properties of conditionals) to the specific types needed
- Splitting it into two theorems:
  - `ct`: states that `(if T then t else u) = t`
  - `cf`: states that `(if F then t else u) = u`
- Using `EXCLUDED_MIDDLE` to create a case split on `p`
- For the `p` case:
  - Converting `p` to `p = T` with `EQT_INTRO`
  - Substituting this in the goal
  - Applying `ct` to simplify the conditional
  - Adding `p` to the assumptions
- For the `¬p` case:
  - Converting `¬p` to `p = F` with `EQF_INTRO`
  - Substituting this in the goal
  - Applying `cf` to simplify the conditional
  - Adding `¬p` to the assumptions

### Mathematical insight
This tactic implements a natural proof technique: when encountering a conditional expression in a goal, it makes sense to analyze the two possible cases separately. This approach simplifies reasoning by eliminating conditionals and creating more direct subgoals.

The tactic is designed to avoid selecting conditionals whose conditions are constants (like `T` or `F`), as those would lead to trivial or impossible cases.

As noted in the comment, this tactic may select conditionals in a different order than similar tactics, which could affect proof development.

### Dependencies
- `COND_CLAUSES`: Basic properties of conditional expressions
- `EXCLUDED_MIDDLE`: The law of excluded middle (every proposition is either true or false)
- `EQT_INTRO`, `EQF_INTRO`: Tactics for converting propositions to equality with T or F
- `SUBST1_TAC`: Substitution tactic
- `ASSUME_TAC`: Adds an assumption to the goal
- `DISJ_CASES_THEN2`: Performs case analysis on a disjunction

### Porting notes
When porting this tactic:
- Ensure the target system has similar facilities for case analysis on conditionals
- Be mindful of how conditionals and boolean expressions are handled in the target system
- The order of selecting conditionals may need adjustment depending on the target system's conventions
- The implementation uses pattern matching and exception handling specific to HOL Light - these may require different approaches in other systems

---

## MATCH_MP_TAC

### MATCH_MP_TAC
- MATCH_MP_TAC

### Type of the formal statement
- HOL Light tactic definition

### Formal Content
```ocaml
let MATCH_MP_TAC th =
  MATCH_MP_TAC th ORELSE
  MATCH_MP_TAC(PURE_REWRITE_RULE[RIGHT_IMP_FORALL_THM] th);;
```

### Informal statement
This defines the `MATCH_MP_TAC` tactic, which applies a theorem as a goal-reduction rule, attempting to match the conclusion of the theorem with the current goal, and then reduces the goal to the hypotheses of the theorem. 

The definition extends the basic `MATCH_MP_TAC` behavior by trying two approaches:
1. First, it tries to apply the standard `MATCH_MP_TAC` to the theorem directly.
2. If that fails, it tries to preprocess the theorem by rewriting it with `RIGHT_IMP_FORALL_THM` before applying `MATCH_MP_TAC`.

This allows the tactic to handle theorems that have universal quantifiers on the right side of implications.

### Informal proof
This is a tactical definition, not a theorem with a proof. The definition creates a new tactic that:

1. First attempts to apply the original `MATCH_MP_TAC` with the given theorem
2. If that fails, it applies a transformation to the theorem using `PURE_REWRITE_RULE[RIGHT_IMP_FORALL_THM]` and then attempts to apply `MATCH_MP_TAC` again

The key transformation here is applying `RIGHT_IMP_FORALL_THM`, which converts implications with universally quantified consequents to universally quantified implications.

### Mathematical insight
This tactic definition addresses a common pattern in theorem proving where implications may have universally quantified conclusions. The standard `MATCH_MP_TAC` might fail in such cases because it expects to match the conclusion of the theorem directly with the goal.

The enhancement enables a more intuitive workflow when using implication-based theorems that contain universal quantifiers in their conclusions. For example, without this enhancement, to use a theorem of the form `A ⇒ ∀x. P(x)` to prove a goal of the form `P(t)`, a user would need to manually instantiate the universal quantifier. With this enhanced `MATCH_MP_TAC`, this preprocessing is handled automatically.

This is particularly useful in structured proofs where theorems are often stated in their most general form with universal quantification.

### Dependencies
- `RIGHT_IMP_FORALL_THM`: A theorem that relates implications with universally quantified consequents to universally quantified implications, likely of the form `(A ⇒ ∀x. B(x)) ⇔ ∀x. (A ⇒ B(x))`
- `PURE_REWRITE_RULE`: A function that performs rewriting without additional simplifications
- `ORELSE`: A tactical that tries the first tactic and, if it fails, applies the second tactic

### Porting notes
When porting this to another system:
1. Verify how the target system handles tactics that transform theorems with universally quantified conclusions
2. Check if the target system already has built-in support for this kind of behavior
3. Ensure that the equivalent of `RIGHT_IMP_FORALL_THM` exists in the target system
4. Consider whether the conversion between `A ⇒ ∀x. B(x)` and `∀x. (A ⇒ B(x))` is handled differently in the target system's logic

Most modern proof assistants have sophisticated tactics for handling implications with quantifiers, so this might be unnecessary or implemented differently depending on the system.

---

## ZERO_LESS_EQ

### ZERO_LESS_EQ
- Actual name of the formal item: `ZERO_LESS_EQ`

### Type of the formal statement
- Theorem (aliasing existing theorem)

### Formal Content
```ocaml
let ZERO_LESS_EQ = LE_0;;
```

### Informal statement
This theorem states that `ZERO_LESS_EQ` is an alias for the existing theorem `LE_0`. The theorem likely represents that $0 \leq n$ for all natural numbers $n$.

### Informal proof
No proof is provided in the formal content as this is simply an aliasing of an existing theorem `LE_0`. The theorem is established by direct assignment.

### Mathematical insight
This theorem appears to be a naming alias to provide a more descriptive or consistent name in the theorem library. Naming aliases are common in formal mathematics libraries to:

1. Provide alternative names that might be more intuitive in different contexts
2. Maintain backward compatibility when renaming theorems
3. Group related theorems under a consistent naming scheme

The name `ZERO_LESS_EQ` suggests the relation "$0 \leq n$", which is a fundamental property for natural numbers.

### Dependencies
- `LE_0` - The original theorem being aliased

### Porting notes
When porting this to another system, you should:
1. First ensure that the equivalent of `LE_0` is available
2. Determine if your target system supports theorem aliases or if you need to create a new theorem that simply references the original
3. Consider if both names are necessary in your target system, or if standardizing on one name is preferable

---

## LESS_EQ_MONO

### LESS_EQ_MONO
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LESS_EQ_MONO = LE_SUC;;
```

### Informal statement
The theorem `LESS_EQ_MONO` states that for all natural numbers `m` and `n`, if `m ≤ n`, then `m + 1 ≤ n + 1`.

In mathematical notation:
$$\forall m, n \in \mathbb{N} \, . \, m \leq n \implies m + 1 \leq n + 1$$

### Informal proof
This theorem is simply an alias for the theorem `LE_SUC`. No additional proof is provided as it directly references an existing theorem.

### Mathematical insight
This theorem expresses the monotonicity of the successor function with respect to the less-than-or-equal-to relation on natural numbers. It states that adding 1 to both sides of an inequality preserves the inequality, which is a fundamental property of ordered structures like the natural numbers.

This result is used as a basic building block in many proofs involving inequalities of natural numbers, particularly when manipulating expressions with successors.

### Dependencies
- `LE_SUC`: The base theorem that `LESS_EQ_MONO` is defined to be equivalent to. It likely states that if `m ≤ n` then `SUC m ≤ SUC n` where `SUC` is the successor function.

### Porting notes
When porting this theorem, check if the target system already has a similar theorem about monotonicity of addition with respect to inequality. In many formal systems, this property might be derived directly from more general theorems about monotonicity of functions or it might be a primitive fact about natural numbers.

---

## NOT_LESS

### Name of formal statement
NOT_LESS

### Type of the formal statement
Definition (let binding)

### Formal Content
```ocaml
let NOT_LESS = NOT_LT;;
```

### Informal statement
The definition `NOT_LESS` is an alias for `NOT_LT`. It represents the negation of the "less than" relation.

Mathematically, `NOT_LESS` corresponds to the relation $\neg(x < y)$, which is equivalent to $x \geq y$.

### Informal proof
This is a direct definition without a proof. It simply establishes `NOT_LESS` as an alternative name for the existing `NOT_LT` operation.

### Mathematical insight
This definition provides a convenient alias that may be useful in contexts where "not less than" is a more natural way to express the relationship than "greater than or equal to". By having multiple names for the same concept, HOL Light allows mathematicians to choose terminology that best fits their specific context.

In mathematics, the relation $\neg(x < y)$ is equivalent to $x \geq y$, which is the disjunction of $x > y$ and $x = y$.

### Dependencies
- `NOT_LT`: The existing definition for the negation of the less-than relation.

### Porting notes
When porting this to another system, you might consider whether having this alias is necessary. Some proof assistants favor having a single canonical name for each concept, while others support multiple ways to express the same idea. If the target system has a standard library with a similar concept, you might want to use that instead of introducing this alias.

---

## LESS_0

### Name of formal statement
LESS_0

### Type of formal statement
theorem

### Formal Content
```ocaml
let LESS_0 = LT_0;;
```

### Informal statement
This theorem states that the relation $<$ (less than) is equal to the relation $<_0$, where $<_0$ is a specific instance of the less-than relation focused on the natural number ordering.

### Informal proof
This is a simple definitional equality. The theorem `LESS_0` establishes that the general less-than relation `LT` is identical to the specific less-than relation `LT_0` that applies to natural numbers.

The proof is immediate as it directly refers to a basic definition in the system's arithmetic framework.

### Mathematical insight
This theorem establishes the connection between the general less-than relation and its specific instantiation for natural numbers. In HOL Light, different relations might be defined for different number systems, and this theorem confirms that the standard less-than relation matches its natural number counterpart.

This is important for consistency in the arithmetic hierarchy and allows theorems about the less-than relation to be applied in natural number contexts without additional conversion steps.

### Dependencies
- `LT_0` - The definition of the less-than relation for natural numbers

### Porting notes
When porting this to another system, ensure that the target system has corresponding definitions for both the general less-than relation and its natural number instantiation. In some proof assistants, these might be unified from the start, making this theorem unnecessary.

---

## LESS_EQ_REFL

### LESS_EQ_REFL
- `LESS_EQ_REFL`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LESS_EQ_REFL = LE_REFL;;
```

### Informal statement
This theorem states that for any number `n`, we have $n \leq n$. It asserts the reflexivity of the less-than-or-equal relation.

### Informal proof
The proof directly uses the theorem `LE_REFL`, which is the original name for the reflexivity of the less-than-or-equal relation. This is simply an alias or alternative name for an existing theorem.

### Mathematical insight
The reflexivity of the less-than-or-equal relation is a fundamental property of ordered structures. This theorem provides a convenient name `LESS_EQ_REFL` as an alternative to `LE_REFL`, likely to maintain naming consistency with other theorems in the library that use the `LESS_EQ` prefix rather than `LE`.

In mathematical terms, reflexivity is one of the core properties that define a partial order, along with antisymmetry and transitivity. It simply states that any element is comparable to itself under the relation.

### Dependencies
- **Theorems**:
  - `LE_REFL`: The original reflexivity theorem for the less-than-or-equal relation

### Porting notes
When porting this to another system, there are two approaches:
1. Define it as an alias to the existing reflexivity theorem for the less-than-or-equal relation
2. Prove it directly as a simple application of the reflexivity property of the ordering relation

This should be straightforward to port to any system that has a notion of ordered numbers.

---

## LESS_EQUAL_ANTISYM

### LESS_EQUAL_ANTISYM
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- Theorem

### Formal Content
```ocaml
let LESS_EQUAL_ANTISYM = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL LE_ANTISYM)));;
```

### Informal statement
For all real numbers `x` and `y`, if $x \leq y$ and $y \leq x$, then $x = y$.

Formally: $\forall x,y. (x \leq y \wedge y \leq x) \Rightarrow x = y$

### Informal proof
This theorem is derived directly from the antisymmetry property of the less-than-or-equal relation (LE_ANTISYM).

The proof extracts the forward implication from the equivalence statement in LE_ANTISYM using the EQ_IMP_RULE, which splits an equivalence into its two implications. The first component (forward direction) is then selected with the fst function.

The result is then generalized to all variables using GEN_ALL to produce the final theorem.

### Mathematical insight
This theorem represents the antisymmetry property of the less-than-or-equal relation on real numbers, which is a fundamental property of partial orders. Antisymmetry ensures that if two elements satisfy inequalities in both directions, they must be equal.

This property, along with reflexivity and transitivity, defines a partial order structure. For real numbers, these properties combine to create a total order.

The theorem is presented in implication form (if $x \leq y$ and $y \leq x$, then $x = y$) rather than the equivalence form that appears in LE_ANTISYM ($x = y \iff x \leq y \wedge y \leq x$).

### Dependencies
- `LE_ANTISYM`: The equivalence form of the antisymmetry property for the less-than-or-equal relation
- `EQ_IMP_RULE`: HOL Light rule for splitting an equivalence into its component implications
- `SPEC_ALL`: HOL Light rule for specializing all universally quantified variables
- `GEN_ALL`: HOL Light rule for generalizing over all free variables

### Porting notes
When porting to another system, ensure that the target system has an established concept of the less-than-or-equal relation on real numbers with its antisymmetry property. The theorem itself is straightforward to state in any system that supports basic logical operations and real numbers.

---

## NOT_LESS_0

### NOT_LESS_0

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let NOT_LESS_0 = GEN_ALL(EQF_ELIM(SPEC_ALL(CONJUNCT1 LT)));;
```

### Informal statement
For all numerical types, the statement $\neg(n < 0)$ holds for any number $n$.

### Informal proof
The proof uses the first conjunct of the `LT` theorem, which defines the "less than" relation. 

- First, we take the specific instance of this theorem for the case where the comparison is with 0.
- Then, the `EQF_ELIM` function is applied to eliminate the false equivalence, establishing that $n < 0$ is always false.
- Finally, the result is generalized using `GEN_ALL` to apply to all numerical values.

The proof essentially relies on the axiomatic properties of numerical ordering, specifically that no number is less than 0 in the defined ordering system.

### Mathematical insight
This theorem establishes a fundamental property of the HOL Light numerical ordering system. In many number systems (particularly natural numbers), this would be a basic axiom or immediate consequence of definitions. The statement that no number is less than zero is crucial for defining a well-ordered set.

Note that this reflects HOL Light's design choices for numerical types. In systems that include negative numbers, this theorem would not hold in general, but it's valid within the specific context of HOL Light's numerical representation.

### Dependencies
- `LT` - The basic definition of the less-than relation
- `CONJUNCT1` - For extracting the first part of a conjunction
- `SPEC_ALL` - For specializing universal quantifiers
- `EQF_ELIM` - For eliminating equivalence with false
- `GEN_ALL` - For generalizing variables

### Porting notes
When porting this theorem to other systems, it's important to understand how those systems define their numerical types and ordering relations. In systems that natively include integers or other number types that can be negative, this theorem would only apply to specific types like natural numbers, not all numerical types.

---

## LESS_TRANS

### Name of formal statement
LESS_TRANS

### Type of formal statement
theorem

### Formal Content
```ocaml
let LESS_TRANS = LT_TRANS;;
```

### Informal statement
LESS_TRANS is an alias for the theorem LT_TRANS, which states the transitivity of the "less than" relation.

For all real numbers $x$, $y$, and $z$, if $x < y$ and $y < z$, then $x < z$.

### Informal proof
Since LESS_TRANS is simply defined as an alias for LT_TRANS, there is no formal proof provided here. The proof would be found in the original LT_TRANS theorem.

### Mathematical insight
This theorem establishes that the "less than" relation on real numbers is transitive, which is a fundamental property of order relations. Transitivity is one of the key properties that makes the real numbers a totally ordered field.

The alias LESS_TRANS is likely provided for consistency with naming conventions or for backward compatibility with code that might reference this name rather than LT_TRANS.

### Dependencies
- `LT_TRANS`: The original theorem that establishes the transitivity of the "less than" relation

### Porting notes
When porting this to another proof assistant:
1. Verify that the basic order properties of real numbers are already established
2. This is a simple alias, so depending on the target system, you might:
   - Either directly use the existing transitivity theorem for the less-than relation
   - Or create an alias if the target system supports theorem aliases
3. Most proof assistants will have this theorem in their standard library, typically with a name indicating transitivity of the less-than relation

---

## LESS_LEMMA1

### Name of formal statement
LESS_LEMMA1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_LEMMA1 = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL(CONJUNCT2 LT))));;
```

### Informal statement
For all natural numbers `m` and `n`, if $m < n$, then there exists a natural number `p` such that $m + \text{SUC}(p) = n$.

### Informal proof
This theorem is derived from the second conjunct of the `LT` theorem, which defines the less-than relation for natural numbers.

The proof extracts the second conjunct of `LT` using `CONJUNCT2`, specializes it for any variables with `SPEC_ALL`, and then takes the forward direction of the resulting equivalence with `EQ_IMP_RULE`. Finally, we generalize over all free variables with `GEN_ALL`.

The second conjunct of `LT` states that $m < n$ is equivalent to there existing a `p` such that $m + \text{SUC}(p) = n$. This theorem extracts just the forward implication: if $m < n$ then there exists a `p` such that $m + \text{SUC}(p) = n$.

### Mathematical insight
This lemma formalizes a fundamental property of the less-than relation on natural numbers: if one number is less than another, we can express their difference in terms of a successor. 

This is the canonical way to convert from the less-than relation to an explicit arithmetic expression. It's particularly useful in formal contexts where we need to transform a comparison into an equation that can be manipulated algebraically.

The lemma essentially states that if $m < n$, then $n$ can be represented as $m$ plus some positive number (expressed as the successor of another natural number).

### Dependencies
- `LT` - The definition of the less-than relation for natural numbers
- `CONJUNCT2` - HOL Light function to extract the second component of a conjunction
- `SPEC_ALL` - HOL Light function to specialize all variables in a theorem
- `EQ_IMP_RULE` - HOL Light function to extract implications from an equivalence
- `GEN_ALL` - HOL Light function to generalize all free variables in a theorem

### Porting notes
When porting this to another system, ensure that the system's definition of the less-than relation for natural numbers is equivalent to HOL Light's `LT` definition. In many systems, this property might already exist or be more directly derivable from the definition of natural numbers and ordering.

---

## LESS_SUC_REFL

### LESS_SUC_REFL
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LESS_SUC_REFL = prove(`!n. n < SUC n`,REWRITE_TAC[LT]);;
```

### Informal statement
For all natural numbers $n$, $n < \text{SUC}(n)$.

Where:
- $n$ represents a natural number
- $\text{SUC}(n)$ represents the successor of $n$ (i.e., $n + 1$)
- $<$ represents the "less than" relation on natural numbers

### Informal proof
The proof is straightforward and uses the definition of the "less than" relation.

By rewriting with the definition of the "less than" relation (which is defined as $a < b \iff a + 1 \leq b$, or equivalently, $a < b \iff \text{SUC}(a) \leq b$), we get:

$n < \text{SUC}(n) \iff \text{SUC}(n) \leq \text{SUC}(n)$

Since $\text{SUC}(n) \leq \text{SUC}(n)$ is trivially true by reflexivity of $\leq$, the statement $n < \text{SUC}(n)$ is proven.

### Mathematical insight
This theorem establishes a fundamental property of the natural number ordering: every natural number is less than its successor. This is a basic axiom in Peano arithmetic and is essential for reasoning about the natural number ordering in formal systems.

This result might seem trivial, but it's a building block for more complex theorems about natural numbers and their ordering relationships. It captures the intuitive notion that adding 1 to any number yields a strictly larger number.

### Dependencies
- `LT`: Definition of the "less than" relation on natural numbers.

### Porting notes
This should be a straightforward theorem to port to other systems as it relies only on the basic definition of the "less than" relation and the successor function, which are standard in most formal systems dealing with natural numbers.

---

## FACT_LESS

### Name of formal statement
FACT_LESS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FACT_LESS = FACT_LT;;
```

### Informal statement
This theorem establishes that `FACT_LESS` is equivalent to `FACT_LT`.

### Informal proof
This is a simple theorem that equates two theorems, `FACT_LESS` and `FACT_LT`. No explicit proof is provided in the formal content, only the statement that these two theorems are equal.

### Mathematical insight
`FACT_LESS` appears to be an alternative name or alias for `FACT_LT`, which likely relates to factorial inequalities. Using different names for the same theorem can be useful for clarity in different contexts or maintaining backward compatibility when renaming theorems.

In mathematical libraries, it's common to have multiple names for the same concept - for example, "less than" and "lt" might be used interchangeably in different contexts, and this theorem appears to establish that equivalence for factorial-related inequalities.

### Dependencies
- `FACT_LT` - The theorem being aliased

### Porting notes
When porting this to another system, simply ensure that `FACT_LT` is ported first, and then create an alias or alternative name for it as `FACT_LESS`. This kind of aliasing is straightforward in most proof assistants.

---

## LESS_EQ_SUC_REFL

### Name of formal statement
LESS_EQ_SUC_REFL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_EQ_SUC_REFL = prove(`!n. n <= SUC n`,REWRITE_TAC[LE; LE_REFL]);;
```

### Informal statement
For all natural numbers $n$, $n \leq \text{SUC}(n)$.

Where:
- $\text{SUC}(n)$ represents the successor of $n$, which is $n + 1$
- $\leq$ is the less-than-or-equal-to relation on natural numbers

### Informal proof
The proof uses rewriting with the definition of $\leq$ and the reflexivity of $\leq$.

By definition of $\leq$ in HOL Light, $n \leq \text{SUC}(n)$ means $n < \text{SUC}(n) \vee n = \text{SUC}(n)$. 

Since $n < \text{SUC}(n)$ is true for all natural numbers (as $n < n+1$), the first disjunct is true, making the entire statement true.

Using the definition of $\leq$ and the reflexivity property, this trivially follows from the properties of natural numbers.

### Mathematical insight
This theorem states the basic property that any natural number is less than or equal to its successor. It's a fundamental property of the natural number ordering that follows directly from the definition of the successor function and the less-than-or-equal relation.

This property is essentially capturing the fact that adding 1 to a number produces a larger (or equal) number, which is a foundational property of ordering on natural numbers. It's used frequently in inductive proofs and reasoning about sequences.

### Dependencies
#### Theorems:
- `LE_REFL` - Reflexivity of less-than-or-equal relation

#### Definitions:
- `LE` - Definition of less-than-or-equal relation

### Porting notes
This theorem should be straightforward to port to other systems, as it represents a basic property of natural numbers that is typically built into most systems' standard libraries. In systems with a slightly different formalization of natural numbers, ensure that the definition of $\leq$ aligns with HOL Light's definition.

---

## LESS_EQ_ADD

### Name of formal statement
LESS_EQ_ADD

### Type of formal statement
theorem

### Formal Content
```ocaml
let LESS_EQ_ADD = LE_ADD;;
```

### Informal statement
This theorem states that for any natural numbers $m$, $n$, $p$, and $q$:

If $m \leq n$ and $p \leq q$, then $m + p \leq n + q$.

### Informal proof
This theorem is simply a reference to the previously proved theorem `LE_ADD`. It doesn't have its own distinct proof but instead points to an existing result.

The theorem `LE_ADD` establishes that the less-than-or-equal relation is preserved under addition of natural numbers.

### Mathematical insight
This theorem captures a fundamental monotonicity property of addition with respect to the natural number ordering. It formalizes the intuitive notion that adding larger numbers results in larger sums.

The theorem is important for several reasons:
- It establishes that addition on natural numbers is compatible with the ordering relation
- It serves as a basic building block for more complex inequalities
- It's frequently used in proofs involving ordered structures
- It helps automate reasoning about inequalities in theorem proving

`LESS_EQ_ADD` appears to be an alternative name for `LE_ADD`, potentially to provide a more descriptive or consistent naming convention.

### Dependencies
- `LE_ADD`: The theorem that actually establishes the inequality preservation property of addition.

### Porting notes
When porting this to another proof assistant:
- Ensure that the natural number addition operation and ordering relation are already defined
- This theorem should be straightforward to prove in any system with basic arithmetic capabilities
- The proof is typically very simple and automated in most systems
- Check if the target system already has this property as part of its standard library

---

## GREATER_EQ

### GREATER_EQ
- GREATER_EQ

### Type of the formal statement
- Definition (alias)

### Formal Content
```ocaml
let GREATER_EQ = GE;;
```

### Informal statement
GREATER_EQ is defined as an alias for GE, where GE is the "greater than or equal to" relation (≥) on real numbers.

### Informal proof
There is no proof involved as this is a simple alias definition that equates GREATER_EQ with the existing GE relation.

### Mathematical insight
This definition creates an alternate name (GREATER_EQ) for the "greater than or equal to" relation on real numbers. Such aliases are common in formal systems to provide more descriptive or intuitive names for fundamental operations. The name GREATER_EQ more explicitly indicates that this relation means "greater than or equal to" compared to the shorter name GE.

### Dependencies
- `GE` - The "greater than or equal to" relation on real numbers

### Porting notes
When porting to another system, simply ensure that the target system has a definition for the "greater than or equal to" relation, and then create an alias if needed. This is a straightforward definition that shouldn't pose any challenges during porting.

---

## LESS_EQUAL_ADD

### LESS_EQUAL_ADD
- less_eq_add

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LESS_EQUAL_ADD = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL LE_EXISTS)));;
```

### Informal statement
For natural numbers $m$ and $n$, $m \leq n$ if and only if there exists a natural number $d$ such that $m + d = n$.

### Informal proof
This theorem follows directly from the definition of less-than-or-equal relation (`LE_EXISTS`). 

The proof extracts the forward direction of the equivalence from `LE_EXISTS`, which states that for natural numbers $m$ and $n$, $m \leq n$ if and only if there exists a $d$ such that $m + d = n$. 

Specifically, the proof:
1. Specializes `LE_EXISTS` to specific variables using `SPEC_ALL`
2. Uses `EQ_IMP_RULE` to extract the implication in the forward direction
3. Generalizes the result using `GEN_ALL` to obtain the final theorem

### Mathematical insight
This theorem provides a fundamental characterization of the less-than-or-equal relation on natural numbers in terms of addition. It shows that one natural number is less than or equal to another precisely when we can add some amount to the smaller one to get the larger one.

This characterization is important because it connects the order relation (≤) to the algebraic operation of addition, making it possible to use algebraic techniques to reason about ordering relationships. It's a canonical way to define the less-than-or-equal relation on natural numbers in constructive mathematics.

### Dependencies
- `LE_EXISTS`: The equivalence that $m \leq n$ if and only if there exists a $d$ such that $m + d = n$

### Porting notes
When porting this theorem to other proof assistants, note that:
1. The statement relies on the definition of natural numbers and the less-than-or-equal relation
2. Different systems might define natural numbers differently (e.g., starting from 0 or 1)
3. The formal statement depends on how addition is defined in the target system

---

## LESS_EQ_IMP_LESS_SUC

### LESS_EQ_IMP_LESS_SUC
- `LESS_EQ_IMP_LESS_SUC`

### Type of the formal statement
- Theorem

### Formal Content
```ocaml
let LESS_EQ_IMP_LESS_SUC = GEN_ALL(snd(EQ_IMP_RULE(SPEC_ALL LT_SUC_LE)));;
```

### Informal statement
For all natural numbers `m` and `n`, if `m ≤ n`, then `m < SUC n`.

In mathematical notation:
$$\forall m\, n.\ m \leq n \Rightarrow m < \text{SUC}(n)$$

Where `SUC` represents the successor function, which adds 1 to a natural number.

### Informal proof
This theorem is derived directly from the theorem `LT_SUC_LE`, which states the equivalence between `m < SUC n` and `m ≤ n`. 

The proof proceeds by:
- Taking the theorem `LT_SUC_LE`, which states: `∀m n. m < SUC n ⟺ m ≤ n`
- Applying `SPEC_ALL` to instantiate the universal quantifiers with variable names
- Using `EQ_IMP_RULE` to separate the bidirectional implication into two implications
- Taking the second part of this result, which corresponds to the direction `m ≤ n ⇒ m < SUC n`
- Generalizing all free variables with `GEN_ALL` to restore the universal quantifiers

This gives us the theorem `∀m n. m ≤ n ⇒ m < SUC n`.

### Mathematical insight
This theorem expresses a fundamental relationship between the less-than-or-equal (`≤`) relation and the strict less-than (`<`) relation in the context of natural numbers. The insight is that adding 1 to the upper bound of an inequality converts a non-strict inequality to a strict one.

This property is a basic fact about natural numbers that is essential in many inductive proofs and algorithms dealing with natural number arithmetic.

### Dependencies
- `LT_SUC_LE`: Theorem stating that `m < SUC n` is equivalent to `m ≤ n`
- `EQ_IMP_RULE`: Inference rule that converts `p ⟺ q` to the pair of implications `p ⇒ q` and `q ⇒ p`
- `SPEC_ALL`: Specializes all universal quantifiers in a theorem
- `GEN_ALL`: Generalizes all free variables in a theorem with universal quantifiers

### Porting notes
This theorem should be straightforward to port to other systems, as it relies only on basic properties of natural numbers and their ordering relations. In most systems, this property might already be available as part of the standard library for natural numbers.

---

## LESS_IMP_LESS_OR_EQ

### LESS_IMP_LESS_OR_EQ
- LESS_IMP_LESS_OR_EQ

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LESS_IMP_LESS_OR_EQ = LT_IMP_LE;;
```

### Informal statement
For real numbers $x$ and $y$, if $x < y$ then $x \leq y$.

### Informal proof
This theorem is simply an alias for the theorem `LT_IMP_LE`, which states that the strict less-than relation implies the less-than-or-equal relation for real numbers.

The proof is immediate since `LESS_IMP_LESS_OR_EQ` is defined to be exactly the same as `LT_IMP_LE`.

### Mathematical insight
This theorem establishes the obvious but fundamental property that strict inequality implies non-strict inequality. It's a basic property of ordered fields like the real numbers. In formal systems, it's important to have this relationship explicitly stated as a theorem that can be referenced in other proofs.

The theorem appears to be an alias with a more descriptive name (`LESS_IMP_LESS_OR_EQ`) for the existing theorem `LT_IMP_LE`, showing the relationship between the strict less-than relation (`<`) and the less-than-or-equal relation (`≤`).

### Dependencies
- `LT_IMP_LE`: The original theorem stating that $x < y$ implies $x \leq y$ for real numbers.

### Porting notes
When porting to other proof assistants, check if the target system already has an equivalent theorem in its standard library, as this is a basic property of ordered structures. The naming might differ across systems, but the content should be fundamentally the same.

---

## LESS_MONO_ADD

### LESS_MONO_ADD
- `LESS_MONO_ADD`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LESS_MONO_ADD = GEN_ALL(snd(EQ_IMP_RULE(SPEC_ALL LT_ADD_RCANCEL)));;
```

### Informal statement
For all natural numbers $m$, $n$, and $p$, we have:
$m < n \iff m + p < n + p$

This theorem states that the less-than relation is preserved when adding the same number to both sides of the inequality.

### Informal proof
The proof derives this theorem from the existing theorem `LT_ADD_RCANCEL`, which states that right cancellation is valid for the less-than relation with addition on natural numbers.

Specifically:
1. We start with `LT_ADD_RCANCEL`, which states: $m + p < n + p \iff m < n$
2. By applying `SPEC_ALL`, we instantiate all universal quantifiers in this theorem
3. Then we use `EQ_IMP_RULE` to extract the implication in both directions
4. We take the second part (the reverse direction) of this bidirectional implication
5. Finally, we generalize the statement with `GEN_ALL` to reintroduce universal quantifiers

The resulting theorem states that for all natural numbers $m$, $n$, and $p$, we have $m < n \iff m + p < n + p$.

### Mathematical insight
This theorem establishes an important monotonicity property of the less-than relation with respect to addition. It allows us to manipulate inequalities by adding the same term to both sides without changing the truth of the inequality. This property is fundamental in arithmetic reasoning and is used extensively in proofs involving inequalities.

The theorem demonstrates that the less-than relation is compatible with addition in the sense that it respects the additive structure of natural numbers.

### Dependencies
- `LT_ADD_RCANCEL`: Theorem stating that $m + p < n + p \iff m < n$
- `SPEC_ALL`: Tactics for specializing all universal quantifiers
- `EQ_IMP_RULE`: Rule for extracting implications from equivalences
- `GEN_ALL`: Tactics for generalizing all free variables

### Porting notes
When porting this theorem to other proof assistants:
- In systems with a well-developed natural number theory, this property might already exist or be easily provable
- The theorem name might include a different convention (e.g., `add_lt_add_iff_right` in Lean)
- In some systems, this might be part of a more general monotonicity theorem about ordered structures

---

## LESS_SUC

### LESS_SUC
- LESS_SUC

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LESS_SUC = prove(`!m n. m < n ==> m < (SUC n)`,MESON_TAC[LT]);;
```

### Informal statement
For all natural numbers $m$ and $n$, if $m < n$, then $m < \text{SUC}(n)$.

Here, $\text{SUC}(n)$ denotes the successor of $n$, which is equivalent to $n + 1$.

### Informal proof
The theorem is proven using the MESON_TAC automated theorem prover with the LT theorem as a dependency.

The proof relies on the transitivity property of the less-than relation. Since $m < n$ and $n < \text{SUC}(n)$ (by definition of the successor function), we can deduce that $m < \text{SUC}(n)$.

### Mathematical insight
This theorem establishes a basic property of the less-than relation on natural numbers: if a number is already strictly less than another number, then it remains strictly less than the successor of that number. This is a straightforward consequence of the ordering of natural numbers and the successor function.

This property is useful in inductive proofs and arguments involving inequalities on natural numbers, serving as a stepping stone for more complex reasoning about ordering relationships.

### Dependencies
- `LT`: The theorem that defines properties of the less-than relation on natural numbers, particularly that for any natural number n, n < SUC(n).

### Porting notes
This theorem should be trivial to port to other proof assistants as it relies on basic properties of natural numbers and the less-than relation.

---

## LESS_CASES

### LESS_CASES
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LESS_CASES = LTE_CASES;;
```

### Informal statement
The theorem `LESS_CASES` establishes that for any two real numbers $x$ and $y$, exactly one of the following holds:
- $x < y$
- $x = y$
- $y < x$

This is a basic trichotomy property of the real number ordering.

### Informal proof
The proof directly uses the theorem `LTE_CASES`, which states the trichotomy property for the less-than-or-equal relation: for any real numbers $x$ and $y$, either $x \leq y$ or $y \leq x$.

### Mathematical insight
This theorem establishes the trichotomy law for real numbers, which is a fundamental property of totally ordered fields. It states that any two real numbers can be compared, and exactly one of three possible relationships holds between them. This property is essential for many mathematical arguments involving inequalities and case analysis.

The trichotomy law distinguishes total orders from partial orders, where some elements might be incomparable. This property is used extensively throughout real analysis and any field that relies on the order properties of real numbers.

### Dependencies
- `LTE_CASES`: Establishes that for any two real numbers $x$ and $y$, either $x \leq y$ or $y \leq x$.

### Porting notes
When porting to other systems, note that this is a fundamental property of ordered fields. Most proof assistants will either have this as a built-in theorem or can derive it easily from the axioms of ordered fields. Make sure the target system has the appropriate notion of strict inequality defined before porting this theorem.

---

## LESS_EQ

### LESS_EQ
- LESS_EQ

### Type of the formal statement
- Definition

### Formal Content
```ocaml
let LESS_EQ = GSYM LE_SUC_LT;;
```

### Informal statement
This definition establishes that `LESS_EQ` is equivalent to the symmetric form of `LE_SUC_LT`. In mathematical notation:

For natural numbers $m$ and $n$:
$m \leq n$ if and only if $m < n + 1$

### Informal proof
This is a definition rather than a theorem, so it doesn't have a proof. The definition makes use of the `GSYM` operator, which returns the symmetric version of the theorem `LE_SUC_LT`.

The theorem `LE_SUC_LT` states that $m \leq n$ if and only if $m < \text{SUC}(n)$ (where $\text{SUC}(n) = n + 1$). By taking the symmetric form with `GSYM`, we get the definition of `LESS_EQ`.

### Mathematical insight
This definition establishes the standard less-than-or-equal relation for natural numbers by using the relationship between the less-than-or-equal relation and the strictly-less-than relation.

The definition is useful because it connects two common ways of expressing inequality:
1. The direct less-than-or-equal relation ($\leq$)
2. The strictly-less-than relation with successor ($< \text{SUC}$)

This equivalence is fundamental in number theory and provides a clean way to convert between these two forms of inequality.

### Dependencies
- `LE_SUC_LT`: Theorem establishing that $m \leq n$ if and only if $m < \text{SUC}(n)$
- `GSYM`: HOL Light operator that returns the symmetric form of a theorem

### Porting notes
When porting to other systems:
- Ensure that the system has a notion of natural numbers with successor operation
- Check how the system handles symmetric versions of theorems, as there might be different mechanisms than HOL Light's `GSYM`
- This definition should be straightforward to port, as it simply defines a standard inequality relation

---

## LESS_OR_EQ

### LESS_OR_EQ
- The formal item name is `LESS_OR_EQ`.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LESS_OR_EQ = LE_LT;;
```

### Informal statement
This theorem establishes an equivalence between `LESS_OR_EQ` and `LE_LT`, essentially defining the less-than-or-equal relation in terms of its standard HOL Light definition.

### Informal proof
The theorem is established by direct equality assignment between `LESS_OR_EQ` and `LE_LT`. This is an identity proof where one name is defined to be equivalent to another.

### Mathematical insight
This theorem creates an alternate name for the less-than-or-equal relation. In HOL Light, `LE_LT` is the standard representation of the less-than-or-equal relation (≤), and this theorem simply makes `LESS_OR_EQ` an equivalent alias for this relation. Having multiple names for the same concept can be helpful for code readability in different contexts, allowing the programmer to choose the name that best communicates their intent.

### Dependencies
- `LE_LT` - The standard less-than-or-equal relation in HOL Light

### Porting notes
When porting to another proof assistant, you would simply need to define `LESS_OR_EQ` as an alias for the target system's less-than-or-equal relation. This is a trivial transformation as it's just a name equivalence, not a complex theorem.

---

## LESS_ADD_1

### LESS_ADD_1
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LESS_ADD_1 = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL
    (REWRITE_RULE[ADD1] LT_EXISTS))));;
```

### Informal statement
For any natural numbers $m$ and $n$, we have:
$m < n \implies \exists k. n = m + 1 + k$

This theorem provides a characterization of the less-than relation in terms of addition. It states that if a number $m$ is less than $n$, then there exists a natural number $k$ such that $n$ is equal to $m + 1 + k$.

### Informal proof
The proof proceeds as follows:

1. We start with the theorem `LT_EXISTS`, which states that $m < n \iff \exists k. n = m + SUC(k)$.
2. Apply `REWRITE_RULE` with `ADD1` to rewrite occurrences of `SUC` in terms of `+1`, yielding $m < n \iff \exists k. n = m + (k + 1)$.
3. Apply `SPEC_ALL` to instantiate universally quantified variables with free variables.
4. Use `EQ_IMP_RULE` to split the bi-implication into two implications: $m < n \implies \exists k. n = m + (k + 1)$ and its converse.
5. Take the first component using `fst` to extract only the forward direction: $m < n \implies \exists k. n = m + (k + 1)$.
6. Finally, apply `GEN_ALL` to re-generalize all free variables.

The result is the theorem $m < n \implies \exists k. n = m + 1 + k$ for any natural numbers $m$ and $n$, which provides one direction of the original bi-implication.

### Mathematical insight
This theorem provides an algebraic characterization of the less-than relation. Instead of viewing $m < n$ purely in terms of order, it expresses a consequence in terms of addition: if $m$ is less than $n$, then $n$ can be obtained by adding at least 1 to $m$. This connection between order and algebra is fundamental and allows for the application of algebraic techniques to problems involving order.

The theorem is particularly useful in inductive proofs about natural numbers where the use of addition is more convenient than working directly with the less-than relation.

### Dependencies
#### Theorems:
- `LT_EXISTS`: Characterizes the less-than relation in terms of the successor function: $m < n \iff \exists k. n = m + SUC(k)$.
- `ADD1`: Defines the relation between the successor function and addition: $SUC(n) = n + 1$.

#### HOL Light functions:
- `REWRITE_RULE`: Applies rewrite rules to a theorem.
- `SPEC_ALL`: Specializes all universally quantified variables in a theorem.
- `EQ_IMP_RULE`: Splits a bi-implication into two implications.
- `fst`: Extracts the first component of a pair.
- `GEN_ALL`: Generalizes over all free variables in a theorem.

### Porting notes
When porting this theorem:
- Ensure that your target system's definitions of less-than, addition, and successor function align with HOL Light's.
- The proof relies on rewriting and manipulation of logical connectives, which should be straightforward in most proof assistants.
- The extraction of the forward direction from a bi-implication might need different tactics in other systems.

---

## SUC_SUB1

### Name of formal statement
SUC_SUB1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUC_SUB1 = prove(`!m. SUC m - 1 = m`,
                     REWRITE_TAC[num_CONV `1`; SUB_SUC; SUB_0]);;
```

### Informal statement
For all natural numbers $m$, we have
$$\text{SUC}(m) - 1 = m$$

where $\text{SUC}(m)$ represents the successor of $m$, which is equivalent to $m + 1$.

### Informal proof
The proof uses rewriting with the following steps:

1. First, the theorem converts the constant `1` to its internal representation using `num_CONV`.
2. Then it applies the theorem `SUB_SUC`, which states that $(n + 1) - (m + 1) = n - m$.
3. Finally, it applies `SUB_0`, which states that $n - 0 = n$.

When these are applied in sequence, they transform $\text{SUC}(m) - 1$ to $m$, proving the theorem.

### Mathematical insight
This theorem establishes the fundamental arithmetic identity that subtracting 1 from the successor of a number gives back the original number. This is a basic property of natural numbers that's used extensively in arithmetic reasoning.

The result seems trivial from a mathematical perspective, but having it as a named theorem in the formal system allows for more concise proofs that require this specific operation.

### Dependencies
- `num_CONV`: Conversion for representing numeric literals
- `SUB_SUC`: Theorem stating that $(n + 1) - (m + 1) = n - m$
- `SUB_0`: Theorem stating that $n - 0 = n$

### Porting notes
This theorem should be straightforward to port to other systems. Most proof assistants have built-in properties of natural numbers that could be used to prove this result. In systems like Lean or Coq, this might even be automatically derivable from the basic arithmetic properties.

---

## LESS_MONO_EQ

### Name of formal statement
LESS_MONO_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_MONO_EQ = LT_SUC;;
```

### Informal statement
This theorem states that for any natural numbers `m` and `n`, 
$m < n \iff m + 1 \leq n$

### Informal proof
This theorem is defined as equal to the `LT_SUC` theorem, which establishes the same relationship between the "less than" relation and the successor function for natural numbers.

### Mathematical insight
This theorem establishes the equivalence between strict inequality (`<`) and non-strict inequality (`≤`) with an offset of 1. It's a fundamental property of the natural number ordering that connects the two types of inequalities.

The name `LESS_MONO_EQ` suggests that this is about the monotonicity and equivalence of the "less than" relation, showing how it can be reexpressed in terms of "less than or equal to."

This equivalence is useful in formal reasoning because it allows for converting between the two forms of inequality, which can be convenient depending on the context of a proof.

### Dependencies
- `LT_SUC` - The theorem which states that m < n ⟺ SUC m ≤ n

### Porting notes
This is a straightforward equivalence that should exist in any theorem prover with natural number definitions. Look for analogous theorems in the target system's standard library before reimplementing.

---

## LESS_ADD_SUC

### LESS_ADD_SUC
- `LESS_ADD_SUC`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LESS_ADD_SUC = prove (`!m n. m < m + SUC n`,
                          REWRITE_TAC[ADD_CLAUSES; LT_SUC_LE; LE_ADD]);;
```

### Informal statement
For all natural numbers $m$ and $n$, we have:
$$m < m + (n + 1)$$

This theorem states that a number is strictly less than itself plus a positive number (represented as the successor of some natural number).

### Informal proof
The proof uses rewriting tactics to establish that $m < m + (n + 1)$.

First, we apply rewriting with:
- `ADD_CLAUSES` which contains basic arithmetic properties of addition
- `LT_SUC_LE` which states that $m < (n + 1)$ is equivalent to $m \leq n$
- `LE_ADD` which states that $m \leq m + n$ for any natural numbers $m$ and $n$

The rewrite tactic transforms the goal as follows:
1. Starting with $m < m + (n + 1)$
2. Using `ADD_CLAUSES`, this becomes $m < m + (n + 1) = m < (m + n) + 1$
3. By `LT_SUC_LE`, this becomes $m \leq m + n$
4. Finally, this is proven by `LE_ADD`, which directly states that $m \leq m + n$

### Mathematical insight
This theorem demonstrates a fundamental property of the natural number ordering: adding a positive number to any number yields a strictly larger result. This is a basic building block for reasoning about inequalities in arithmetic contexts.

The result is straightforward but essential in many formalized proofs involving inequalities and natural numbers.

### Dependencies
- Theorems:
  - `ADD_CLAUSES` - basic properties of addition
  - `LT_SUC_LE` - relationship between strict inequality and successor
  - `LE_ADD` - adding a number preserves inequality

### Porting notes
This theorem should be straightforward to port to other proof assistants, as it relies only on basic properties of natural numbers. In systems with built-in support for arithmetic reasoning (like Lean's `linarith` or Coq's `lia`), this theorem might even be proven automatically.

---

## LESS_REFL

### LESS_REFL
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LESS_REFL = LT_REFL;;
```

### Informal statement
For any real number $x$, we have $x < x$ is false. This is the irreflexivity property of the "less than" relation on real numbers.

### Informal proof
This theorem appears to be a direct reference to another theorem `LT_REFL`, which states that the "less than" relation on real numbers is irreflexive.

The proof simply defines `LESS_REFL` as equivalent to `LT_REFL`.

### Mathematical insight
The irreflexivity of the "less than" relation is a fundamental property of real numbers. This theorem establishes that no real number can be strictly less than itself, which is a basic axiom in the theory of ordered fields.

`LESS_REFL` appears to be an alternative name for `LT_REFL`, likely provided for consistency with other naming conventions or to support different notational preferences in the development of real number theory in HOL Light.

### Dependencies
- `LT_REFL`: The source theorem establishing the irreflexivity of the less-than relation.

---

## INV_SUC_EQ

### INV_SUC_EQ
- `INV_SUC_EQ`

### Type of the formal statement
- Theorem

### Formal Content
```ocaml
let INV_SUC_EQ = SUC_INJ;;
```

### Informal statement
The theorem states that `INV_SUC_EQ` is equal to `SUC_INJ`. This means that `INV_SUC_EQ` is an alternative name for the theorem that states the successor function on natural numbers is injective.

### Informal proof
This theorem is simply defining an alternative name (`INV_SUC_EQ`) for the existing theorem `SUC_INJ`. There is no proof involved, just a direct equivalence declaration.

### Mathematical insight
This theorem provides an alternative name for the injectivity property of the successor function on natural numbers. Having multiple names for the same theorem can be useful when organizing libraries or when different naming conventions are preferred in different contexts.

The injectivity of the successor function is a fundamental property of the natural numbers. It states that if the successors of two natural numbers are equal, then the numbers themselves must be equal. This is equivalent to stating that $n + 1 = m + 1$ implies $n = m$, which is a basic property used in many proofs involving natural numbers.

### Dependencies
- Theorems:
  - `SUC_INJ`: The theorem stating that the successor function is injective

### Porting notes
When porting this to other proof assistants, it's simply a matter of creating an alternative name for the injectivity theorem of the successor function. This should be straightforward as most proof assistants will have an equivalent theorem about successor injectivity already available in their standard libraries.

---

## LESS_EQ_CASES

### Name of formal statement
LESS_EQ_CASES

### Type of the formal statement
Theorem (actually, seems to be an alias or renaming of an existing theorem)

### Formal Content
```ocaml
let LESS_EQ_CASES = LE_CASES;;
```

### Informal statement
The theorem states that for all real numbers $x$ and $y$, either $x \leq y$ or $y \leq x$. That is, any two real numbers are comparable under the less-than-or-equal-to relation.

### Informal proof
This theorem is defined as an alias to the existing theorem `LE_CASES`, so it inherits the proof from that theorem. The original theorem `LE_CASES` proves that the real number ordering is a total order, specifically that for any two real numbers, at least one is less than or equal to the other.

### Mathematical insight
This theorem expresses an essential property of the real numbers: the total ordering property. This property is one of the fundamental axioms of the real number system, stating that the real numbers form a totally ordered field. This property distinguishes real numbers from other number systems like complex numbers, which do not have a natural total ordering.

In formal systems, having a theorem that explicitly states this property is important as it allows proofs to use case analysis on whether one number is less than or equal to another, which is a common technique in real analysis.

### Dependencies
- `LE_CASES`: The original theorem that states the total ordering property of real numbers

### Porting notes
This is a straightforward renaming of the existing theorem `LE_CASES`. When porting to another system, one would typically just port `LE_CASES` and then define this as an alias if needed. In many systems, such aliases might not be necessary if the naming convention already uses a consistent terminology for ordering relations.

---

## LESS_EQ_TRANS

### LESS_EQ_TRANS
- LE_TRANS renamed to LESS_EQ_TRANS

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LESS_EQ_TRANS = LE_TRANS;;
```

### Informal statement
This theorem states the transitivity property of the less than or equal relation (≤) on real numbers: if $a \leq b$ and $b \leq c$, then $a \leq c$.

### Informal proof
This theorem is simply a renaming of the existing theorem `LE_TRANS`, which already establishes the transitivity of the less than or equal relation. No additional proof is needed as this is just an alternative name for an existing result.

### Mathematical insight
The transitivity property is a fundamental property of the order relation on real numbers. It allows us to chain inequalities together, which is essential in many mathematical proofs involving real numbers. This theorem provides a more descriptive name (LESS_EQ_TRANS) that clearly indicates its relation to the less-than-or-equal (≤) operator, making the codebase more readable and self-documenting.

### Dependencies
- `LE_TRANS` - The original theorem establishing transitivity of the less-than-or-equal relation

### Porting notes
When porting to another system, simply ensure that the transitivity of less-than-or-equal is available, which should be a standard property in any formalization of ordered fields or real numbers. The specific name (LESS_EQ_TRANS or LE_TRANS) is not important, though consistency in naming conventions within the target system should be maintained.

---

## LESS_THM

### Name of formal statement
LESS_THM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_THM = CONJUNCT2 LT;;
```

### Informal statement
This theorem establishes the definition of the less-than relation (`<`) in terms of the less-than-or-equal relation (`<=`).

For all real numbers `x` and `y`:
$x < y \iff x \leq y \land x \neq y$

### Informal proof
This result is obtained by extracting the second conjunct from the theorem `LT`, which defines the less-than relation. The `CONJUNCT2` function in HOL Light extracts the second part of a conjunction.

The proof simply applies `CONJUNCT2` to the theorem `LT`, which contains the definition of the less-than relation as a conjunction of properties.

### Mathematical insight
This theorem provides the standard definition of the strict less-than relation in terms of the non-strict less-than-or-equal relation. It captures the intuitive notion that "less than" means "less than or equal to, but not equal to."

The result is foundational for real number arithmetic and ordering, establishing the relationship between the strict and non-strict inequality operations. This definition ensures that the less-than relation has the proper properties for a strict total order on real numbers.

The relation between `<` and `<=` is important in many proof contexts, allowing conversion between strict and non-strict inequalities as needed.

### Dependencies
- `LT` - The theorem that defines the less-than relation as a conjunction
- `CONJUNCT2` - The HOL Light function that extracts the second part of a conjunction

### Porting notes
This theorem should be straightforward to port to other systems, as the definition of the less-than relation in terms of less-than-or-equal and inequality is standard. In systems where these relations are primitives, you may need to establish this as a lemma rather than a definition.

---

## GREATER

### GREATER
- State the exact name of the formal item: GREATER

### Type of the formal statement
- Definition (let binding)

### Formal Content
```ocaml
let GREATER = GT;;
```

### Informal statement
`GREATER` is defined as the "greater than" relation `GT`. It is an alternative name for the binary relation that determines when one value is greater than another.

### Informal proof
This is simply a naming definition that establishes `GREATER` as an alias for the predefined relation `GT`. No proof is required.

### Mathematical insight
This definition provides an alternative, more descriptive name for the "greater than" relation. Using `GREATER` instead of `GT` can make code more readable in certain contexts, especially in formal proof scripts where the intention behind using a specific relation should be clear. The definition follows the convention in HOL Light of providing alternative names for common operations to improve readability.

### Dependencies
- Built-in relation: `GT` (the built-in greater than relation)

### Porting notes
When porting to other proof assistants, you would typically use whatever "greater than" relation is provided by the target system. This is a simple alias definition that exists for readability purposes rather than introducing new functionality, so you might:
1. Use the target system's existing notation for "greater than" directly
2. Create a similar alias if the target system supports let-bindings or definitional equality
3. Skip this definition entirely if the target system already has sufficiently clear notation

---

## LESS_EQ_0

### LESS_EQ_0
- `LESS_EQ_0`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LESS_EQ_0 = CONJUNCT1 LE;;
```

### Informal statement
This theorem states that for any natural number `n`, we have $n \geq 0$.

### Informal proof
This theorem is extracted directly from the conjunction `LE` using `CONJUNCT1`, which selects the first part of a conjunction. The theorem `LE` defines the less-than-or-equal relation for natural numbers, and its first conjunct specifically states that every natural number is greater than or equal to zero.

### Mathematical insight
This is a basic property of natural numbers in the HOL Light formalization, where natural numbers are defined to start from 0. This theorem establishes the lower bound of the natural number domain and is fundamental for reasoning about natural numbers.

### Dependencies
- `LE`: The conjunction containing the definition of the less-than-or-equal relation for natural numbers
- `CONJUNCT1`: A theorem that extracts the first part of a conjunction

---

## OR_LESS

### Name of formal statement
OR_LESS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let OR_LESS = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL LE_SUC_LT)));;
```

### Informal statement
For all natural numbers $m$ and $n$, we have:
$m \leq n \iff m < n \lor m = n$

This theorem provides an alternative characterization of the less-than-or-equal relation ($\leq$) in terms of strict less-than ($<$) or equality.

### Informal proof
The proof derives this result from the theorem `LE_SUC_LT`, which states that $m \leq n \iff m < \text{SUC}(n)$.

From `LE_SUC_LT`, we have the equivalence $m \leq n \iff m < \text{SUC}(n)$. By the definition of the strict less-than relation, we know that $m < \text{SUC}(n)$ means $m$ is strictly less than the successor of $n$, which is equivalent to $m \leq n$.

Furthermore, we can elaborate this as follows:
$m \leq n$ holds if and only if either $m < n$ or $m = n$.

The proof formally extracts this equivalence by taking the `LE_SUC_LT` theorem, specializing it to all variables using `SPEC_ALL`, then extracting the implication in both directions using `EQ_IMP_RULE`. Finally, the result is generalized to all variables $m$ and $n$ using `GEN_ALL`.

### Mathematical insight
This theorem establishes the equivalence between two common ways to express the less-than-or-equal relationship:
1. Directly using the "less than or equal" relation ($\leq$)
2. Using the disjunction of "strictly less than" and "equality" ($< \lor =$)

This equivalence is fundamental in arithmetic reasoning, especially when working with natural numbers. The result is intuitive: for one number to be less than or equal to another, it must either be strictly less or exactly equal.

This conversion is often needed when refining inequalities during proofs, and many theorem provers use this characterization internally when reasoning about inequalities.

### Dependencies
- `LE_SUC_LT` - Theorem relating less-than-or-equal to successor and less-than
- `EQ_IMP_RULE` - Rule for extracting both directions of an equivalence
- `SPEC_ALL` - Specializes a theorem to all its variables
- `GEN_ALL` - Generalizes a theorem over all its free variables

### Porting notes
When porting this theorem to other systems:
- Most proof assistants will likely have this as a basic arithmetic fact in their standard libraries
- The proof is straightforward and should be easily reproducible in any system with basic arithmetic reasoning
- In type-theoretic systems, it might be necessary to ensure that the variables are properly typed as natural numbers

---

## SUB_EQUAL_0

### Name of formal statement
SUB_EQUAL_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUB_EQUAL_0 = SUB_REFL;;
```

### Informal statement
For all real numbers $x$, $x - x = 0$.

### Informal proof
This theorem is simply an application of `SUB_REFL`, which states that subtraction of a number from itself equals zero.

### Mathematical insight
This is a fundamental property of subtraction in the real number system. It establishes that the difference between a number and itself is always zero, which is essential for algebraic manipulations. This identity forms part of the basic arithmetic properties in any mathematical system.

### Dependencies
- `SUB_REFL`: States that $x - x = 0$ for any real number $x$.

### Porting notes
This theorem should be trivial to port to any system that has real number subtraction defined, as it represents a basic arithmetic property. In most formal systems, this might be available as a direct consequence of how subtraction is defined or as a basic lemma in the arithmetic library.

---

## SUB_MONO_EQ

### SUB_MONO_EQ
- SUB_MONO_EQ

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let SUB_MONO_EQ = SUB_SUC;;
```

### Informal statement
The theorem `SUB_MONO_EQ` states that the subtraction operation is monotonic with respect to equality on natural numbers. Specifically, it states that for natural numbers $m$, $n$, and $p$:

$$m - n = m - p \iff n = p \text{ or } m \leq n \land m \leq p$$

In other words, subtraction yields the same result if and only if either the subtrahends are equal, or both subtrahends are greater than or equal to the minuend (in which case both differences are 0).

### Informal proof
This theorem is defined as identical to the previously established theorem `SUB_SUC`.

Looking at the definition `SUB_SUC`, the theorem states that for natural numbers $m$, $n$, and $p$:

$$(m - n = m - p) \iff (n = p \lor (n \geq m \land p \geq m))$$

The proof relies on the properties of natural number subtraction, particularly that when the subtrahend is greater than or equal to the minuend, the result is 0.

### Mathematical insight
This theorem establishes an important property of subtraction on natural numbers - when two subtractions have the same result. It highlights the special case of natural number subtraction where subtracting a larger number from a smaller one results in 0.

The name `SUB_MONO_EQ` suggests that this is about the monotonicity of subtraction with respect to equality, which is a key property for reasoning about natural number arithmetic.

Understanding when $m - n = m - p$ is useful in many arithmetic proofs and algebraic manipulations involving natural numbers.

### Dependencies
- `SUB_SUC`: The theorem that this theorem is defined to be identical to, which states the conditions under which two subtractions yield the same result.

### Porting notes
When porting this theorem, ensure that your target system's definition of natural number subtraction truncates to zero when the subtrahend exceeds the minuend. Some systems might define subtraction differently or use integers instead of natural numbers, which would change the statement of this theorem.

---

## NOT_SUC_LESS_EQ

### NOT_SUC_LESS_EQ
- NOT_SUC_LESS_EQ

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let NOT_SUC_LESS_EQ = prove (`!n m. ~(SUC n <= m) <=> m <= n`,
                             REWRITE_TAC[NOT_LE; LT] THEN
                             MESON_TAC[LE_LT]);;
```

### Informal statement
For all natural numbers $n$ and $m$, we have:
$$\lnot(SUC(n) \leq m) \iff m \leq n$$

Where $SUC(n)$ represents the successor of $n$ (i.e., $n+1$).

### Informal proof
The proof proceeds as follows:

* First, we rewrite the negation of the less-than-or-equal relation (`~(SUC n <= m)`) using the `NOT_LE` theorem, which transforms it into `m < SUC n`.

* Then, we rewrite the less-than relation using the `LT` theorem, which defines `x < y` as `SUC x <= y`. This transforms `m < SUC n` into `SUC m <= SUC n`.

* Finally, using the property that for natural numbers, `SUC m <= SUC n` if and only if `m <= n` (which is related to the theorem `LE_LT`), we complete the proof.

### Mathematical insight
This theorem establishes the logical equivalence between the negation of "the successor of $n$ is less than or equal to $m$" and "$m$ is less than or equal to $n$". 

In more familiar terms, this says that $\lnot(n+1 \leq m)$ is equivalent to $m \leq n$. This is a basic property of the ordering relation on natural numbers and is useful for manipulating inequalities in proofs. It follows directly from the fact that for natural numbers, the ordering is total and the successor function increases values by exactly 1.

### Dependencies
- `NOT_LE`: Theorem relating negation of less-than-or-equal to the less-than relation.
- `LT`: Definition of the less-than relation.
- `LE_LT`: Properties of less-than-or-equal and less-than relations.

### Porting notes
When porting to other systems:
- Ensure that the system has a compatible definition of natural numbers with a successor function.
- Verify that the less-than and less-than-or-equal relations are defined in terms of each other in a compatible way.
- This theorem might already be a built-in property in some systems or might be proven as a direct consequence of the definitions.

---

## SUC_NOT

### Name of formal statement
SUC_NOT

### Type of the formal statement
theorem

### Formal content
```ocaml
let SUC_NOT = GSYM NOT_SUC;;
```

### Informal statement
The theorem states that for all natural numbers $n$:

$$\neg(\text{SUC}(n)) = \text{SUC}(\neg n)$$

where $\text{SUC}$ denotes the successor function on natural numbers and $\neg$ denotes logical negation.

### Informal proof
This theorem is established by applying the symmetric version of the theorem `NOT_SUC` using the `GSYM` function.

The theorem `NOT_SUC` states that $\text{SUC}(\neg n) = \neg(\text{SUC}(n))$, and `GSYM` reverses the equality to obtain $\neg(\text{SUC}(n)) = \text{SUC}(\neg n)$.

### Mathematical insight
This theorem expresses the relationship between the successor function and negation. It shows that negating the successor of a number is equivalent to taking the successor of the negated number.

In the context of HOL Light's representation of natural numbers and logical operations, this property is important for manipulating expressions involving both succession and negation.

### Dependencies
- `NOT_SUC`: The theorem stating that $\text{SUC}(\neg n) = \neg(\text{SUC}(n))$
- `GSYM`: Function that creates the symmetric version of a theorem

### Porting notes
When porting this theorem to other proof assistants, ensure that the representation of natural numbers and the definition of negation are consistent with HOL Light. The theorem is straightforward and should be easily provable in most systems that have similar definitions of natural numbers and negation.

---

## LESS_LESS_CASES

### Name of formal statement
LESS_LESS_CASES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_LESS_CASES = prove(`!m n:num. (m = n) \/ m < n \/ n < m`,
                            MESON_TAC[LT_CASES]);;
```

### Informal statement
For any natural numbers $m$ and $n$, exactly one of the following holds:
- $m = n$, or
- $m < n$, or
- $n < m$

This theorem establishes the trichotomy property for the less-than relation on natural numbers.

### Informal proof
This theorem is proved using the `LT_CASES` theorem, which states the trichotomy property for natural numbers. The proof uses the MESON tactical proof procedure to automatically derive the result from `LT_CASES`.

### Mathematical insight
This theorem formalizes the fundamental trichotomy property of the natural number ordering: for any two natural numbers, exactly one of three possibilities must hold - they are equal, the first is less than the second, or the second is less than the first. 

This property is central to the theory of ordered sets and specifically shows that the natural numbers form a totally ordered set. It enables case analysis when reasoning about numerical inequalities.

### Dependencies
- `LT_CASES`: The theorem establishing the trichotomy property for the less-than relation on natural numbers

### Porting notes
This theorem should be straightforward to port to other systems, as the trichotomy property for natural numbers is typically a basic property in any number theory formalization. In some systems, this might already exist as part of the standard library or might be directly derivable from the definition of natural numbers and their ordering.

---

## NOT_LESS_EQUAL

### NOT_LESS_EQUAL
- NOT_LESS_EQUAL

### Type of the formal statement
- Definition

### Formal Content
```ocaml
let NOT_LESS_EQUAL = NOT_LE;;
```

### Informal statement
This definition establishes `NOT_LESS_EQUAL` as an alias for `NOT_LE`, where:

`NOT_LESS_EQUAL a b` means "it is not the case that $a \leq b$" or equivalently "$a > b$".

Formally, `NOT_LESS_EQUAL a b` holds when $a > b$.

### Informal proof
This is a simple definitional equality that establishes `NOT_LESS_EQUAL` as an alias for `NOT_LE`. No proof is required for this definition.

### Mathematical insight
This definition provides a more descriptive name for the negation of the less-than-or-equal relation. Having both `NOT_LE` and `NOT_LESS_EQUAL` available gives flexibility in writing theorems and provides clarity in formal statements. 

The definition enables statements involving "not less than or equal" to be expressed with a name that directly conveys the intended meaning, which can improve the readability of formal proofs and statements.

### Dependencies
- `NOT_LE` - The negation of the less-than-or-equal relation

### Porting notes
When porting to another proof assistant:
- This is a straightforward definition that creates an alias
- Check if the target system has a convention for handling aliases or if you should create a new definition or notation
- Ensure that the underlying `NOT_LE` (or equivalent) is already properly defined in the target system

---

## LESS_EQ_EXISTS

### LESS_EQ_EXISTS
- `LESS_EQ_EXISTS`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LESS_EQ_EXISTS = LE_EXISTS;;
```

### Informal statement
The theorem `LESS_EQ_EXISTS` states that for all natural numbers $m$ and $n$, $m \leq n$ if and only if there exists a natural number $d$ such that $m + d = n$.

### Informal proof
This theorem is simply an alias for the theorem `LE_EXISTS`, which already establishes the equivalence between the less-than-or-equal relation on natural numbers and the existence of a difference.

### Mathematical insight
This theorem provides a fundamental characterization of inequality in terms of existence of a difference, which is a common approach in constructive mathematics. It allows us to transform a relational statement ($m \leq n$) into an existential statement about a specific number ($d$) that represents the difference between $n$ and $m$.

The existence of this alias might indicate that both naming conventions (with `LESS_EQ` and `LE`) are used in different contexts within HOL Light's standard library, and this theorem ensures compatibility between them.

### Dependencies
- `LE_EXISTS`: The original theorem establishing that $m \leq n$ if and only if there exists $d$ such that $m + d = n$.

### Porting notes
When porting this to another system, check if the target system already has a similar theorem about natural number inequality being equivalent to the existence of a difference. If so, you might not need to port both `LE_EXISTS` and `LESS_EQ_EXISTS` separately, but could just define one as an alias of the other as done here, or simply use the existing theorem directly.

---

## LESS_MONO_ADD_EQ

### LESS_MONO_ADD_EQ
- The formal item is `LESS_MONO_ADD_EQ`.

### Type of the formal statement
- Theorem

### Formal Content
```ocaml
let LESS_MONO_ADD_EQ = LT_ADD_RCANCEL;;
```

### Informal statement
This theorem states that addition is strictly monotonic with respect to the less-than relation. Specifically:

For all real numbers $a$, $b$, and $c$:
$a < b$ if and only if $a + c < b + c$

This is a statement about cancellation of addition with respect to the strict inequality relation.

### Informal proof
The theorem is simply defined as an alias to `LT_ADD_RCANCEL`, which already proves that for all real numbers $a$, $b$, and $c$:
$a < b$ if and only if $a + c < b + c$

No additional proof is needed as this is just a renaming of an existing theorem.

### Mathematical insight
This theorem establishes that adding the same value to both sides of an inequality preserves the inequality relationship. This is a fundamental property of ordered fields like the real numbers.

The name `LESS_MONO_ADD_EQ` emphasizes that this is about the monotonicity of addition with respect to the "less than" relation, and the "EQ" suffix indicates that this is an equivalence (if and only if) statement.

This result is useful in algebraic manipulations involving inequalities and forms part of the basic toolkit for working with ordered structures.

### Dependencies
- `LT_ADD_RCANCEL` - The theorem stating that adding the same value to both sides of a strict inequality preserves the inequality.

### Porting notes
When porting to other proof assistants, check if they already have built-in theorems for addition monotonicity. Most systems will have this basic property available, perhaps under different names:
- In Lean, this might be available as part of the ordered field axioms
- In Coq, it might be part of the standard library for real numbers
- In Isabelle/HOL, it might be in the theory of ordered fields

No special considerations are needed for porting this theorem as it's a basic property of ordered fields.

---

## LESS_LESS_EQ_TRANS

### Name of formal statement
LESS_LESS_EQ_TRANS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_LESS_EQ_TRANS = LTE_TRANS;;
```

### Informal statement
This theorem states that the "less than" relation and the "less than or equal" relation are transitive with respect to each other. 

Formally, for any real numbers $a$, $b$, and $c$:

If $a < b$ and $b \leq c$, then $a < c$.

### Informal proof
The proof simply applies the transitivity property of the "less than or equal" relation, which is established by the theorem `LTE_TRANS`.

The theorem `LTE_TRANS` states that for real numbers $a$, $b$, and $c$, if $a \leq b$ and $b \leq c$, then $a \leq c$.

Since $a < b$ implies $a \leq b$ (strict inequality implies non-strict inequality), we can apply transitivity of $\leq$ to conclude that $a \leq c$.

However, since the first relation is strict ($a < b$) and the transitivity property preserves strictness when combined with a non-strict inequality, we can conclude that $a < c$.

### Mathematical insight
This theorem establishes an important property about the interaction between strict ($<$) and non-strict ($\leq$) inequality relations. It's a fundamental property in real analysis and ordering relations.

The theorem is particularly useful in proof chains where we need to combine different types of inequalities. It allows us to maintain the strictness of an inequality through a transitive chain when appropriate.

This property is part of the basic framework of ordered fields and is essential for reasoning about inequalities in mathematical analysis.

### Dependencies
- Theorems:
  - `LTE_TRANS`: Transitivity of the "less than or equal" relation.

### Porting notes
When porting to another system, ensure that the system's library has the basic properties of ordered fields established. Most proof assistants will have these properties available in their standard libraries, possibly with different naming conventions.

---

## SUB_SUB

### Name of formal statement
SUB_SUB

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUB_SUB = ARITH_RULE
  `!b c. c <= b ==> (!a:num. a - (b - c) = (a + c) - b)`;;
```

### Informal statement
For all natural numbers $b$ and $c$ such that $c \leq b$, we have that for all natural numbers $a$:
$$a - (b - c) = (a + c) - b$$

### Informal proof
This theorem is proven using the `ARITH_RULE` tactic, which automatically proves arithmetic statements in HOL Light. The proof relies on basic properties of subtraction of natural numbers.

To prove this equality:
* When $c \leq b$, we have $b - c$ is well-defined in natural numbers
* For any natural number $a$:
  * Left side: $a - (b - c)$
  * Right side: $(a + c) - b$
* By the associative and commutative properties of addition and subtraction:
  * $(a + c) - b = a + c - b = a + (c - b) = a - (b - c)$
* The result follows from the arithmetic properties of natural numbers

### Mathematical insight
This theorem establishes a simple but useful identity for rearranging subtraction operations in natural numbers. It shows how to transform $a - (b - c)$ into $(a + c) - b$ when $c \leq b$.

The identity is useful when manipulating arithmetic expressions involving multiple subtractions. It allows for regrouping terms in a way that might simplify calculations or proofs. This kind of identity is particularly important in formalized mathematics where explicit manipulation of arithmetic expressions is often necessary.

### Dependencies
- **Tactics**:
  - `ARITH_RULE`: A decision procedure for linear arithmetic over natural numbers

### Porting notes
When porting to other proof assistants:
- Most systems have automated tactics for basic arithmetic, though they may have different names (e.g., `simp` in Isabelle, `omega` in Coq, `linarith` in Lean)
- Note that this theorem is specific to natural numbers where subtraction has specific properties (e.g., $a - b = 0$ when $a < b$). In other number systems, the theorem would need to be adjusted accordingly.
- Some proof assistants may already have this identity as part of their standard library.

---

## LESS_CASES_IMP

### Name of formal statement
LESS_CASES_IMP

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_CASES_IMP = ARITH_RULE
  `!m n:num. ~(m < n) /\ ~(m = n) ==> n < m`;;
```

### Informal statement
For all natural numbers $m$ and $n$, if it is not the case that $m < n$ and it is not the case that $m = n$, then $n < m$.

Formally:
$$\forall m, n \in \mathbb{N}. \neg(m < n) \wedge \neg(m = n) \Rightarrow n < m$$

### Informal proof
This theorem follows directly from the trichotomy property of the natural number ordering.

For any two natural numbers $m$ and $n$, exactly one of the following must be true:
- $m < n$
- $m = n$
- $n < m$

Therefore, if we know that $m < n$ is false and $m = n$ is also false, the only remaining possibility is that $n < m$ must be true.

The proof uses `ARITH_RULE`, which automatically proves arithmetic statements in HOL Light.

### Mathematical insight
This theorem expresses a fundamental property of the total ordering on natural numbers - the trichotomy property. It provides a way to deduce $n < m$ by ruling out the other possibilities in the relation between $m$ and $n$.

The result is particularly useful in case analysis proofs where the relation between two natural numbers needs to be determined. By eliminating two possibilities, we can conclusively establish the third possibility.

### Dependencies
- `ARITH_RULE`: HOL Light's arithmetic decision procedure that automatically proves statements in Presburger arithmetic.

### Porting notes
This theorem should be straightforward to port to other systems, as it relies only on the basic properties of natural numbers. In many theorem provers, this might already be available as part of the standard library, or it could be proven using basic natural number properties and case analysis.

---

## SUB_LESS_EQ

### SUB_LESS_EQ

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let SUB_LESS_EQ = ARITH_RULE
  `!n m:num. (n - m) <= n`;;
```

### Informal statement
For all natural numbers $n$ and $m$, we have $(n - m) \leq n$.

### Informal proof
This theorem follows immediately from arithmetic properties. The subtraction operation on natural numbers $n - m$ is defined such that:
- When $n \geq m$, it equals the difference between $n$ and $m$
- When $n < m$, it equals $0$

In both cases:
- If $n \geq m$, then $(n - m) = n - m \leq n$
- If $n < m$, then $(n - m) = 0 \leq n$

Therefore, $(n - m) \leq n$ holds for all natural numbers $n$ and $m$.

The proof uses HOL Light's arithmetic reasoning capabilities through `ARITH_RULE`, which automatically proves basic arithmetic facts.

### Mathematical insight
This theorem captures a fundamental property of natural number subtraction: the result of subtracting any natural number from another is always less than or equal to the original number. This follows from the definition of subtraction in the natural numbers, which is either standard subtraction when possible or zero when the subtrahend is larger than the minuend.

This property is particularly useful in algorithm analysis, number theory, and formal verification where reasoning about arithmetic bounds is common.

### Dependencies
- The proof relies on HOL Light's `ARITH_RULE` tactic, which uses built-in arithmetic decision procedures.

### Porting notes
When porting to other systems:
- Most proof assistants have built-in automation for simple arithmetic facts like this
- In systems with a different definition of natural number subtraction, make sure to account for the truncation at zero that occurs in HOL Light when $m > n$
- This theorem is simple enough that it should be provable with minimal effort in any system with decent arithmetic automation

---

## SUB_EQ_EQ_0

### Name of formal statement
SUB_EQ_EQ_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUB_EQ_EQ_0 = ARITH_RULE
 `!m n:num. (m - n = m) <=> (m = 0) \/ (n = 0)`;;
```

### Informal statement
For all natural numbers $m$ and $n$, the equality $m - n = m$ holds if and only if either $m = 0$ or $n = 0$.

### Informal proof
This theorem is proven using `ARITH_RULE`, which is an automated decision procedure for linear arithmetic in HOL Light. The procedure automatically handles the reasoning needed to establish this arithmetical fact, which follows from the basic properties of natural number subtraction.

To understand why this theorem holds:
- If $m = 0$, then $m - n = 0 - n = 0 = m$ for any $n$ (since subtraction in the natural numbers yields 0 when the result would otherwise be negative)
- If $n = 0$, then $m - n = m - 0 = m$ for any $m$
- Conversely, if $m - n = m$ and $m > 0$ and $n > 0$, we would have $m - n < m$ (since we're subtracting a positive number), which contradicts our assumption. Therefore, either $m = 0$ or $n = 0$.

### Mathematical insight
This theorem characterizes when natural number subtraction leaves a number unchanged. In the natural numbers, subtraction is truncated (it never goes below 0), which means $m - n = m$ occurs only in two cases: when $m = 0$ (since $0 - n = 0$ for any $n$) or when $n = 0$ (since $m - 0 = m$ for any $m$). 

This property distinguishes subtraction in the natural numbers from subtraction in other number systems like integers, where $m - n = m$ would imply simply that $n = 0$.

The result is often useful in formal verification contexts when reasoning about properties of natural number arithmetic, particularly when dealing with subtraction operations.

### Dependencies
The theorem is proven using `ARITH_RULE`, an automated decision procedure for linear arithmetic in HOL Light.

### Porting notes
When porting to other systems:
- Make sure the target system's natural number subtraction has the same truncation behavior as HOL Light (i.e., $m - n = 0$ when $m < n$)
- Most proof assistants have automated tactics for arithmetic reasoning that can likely prove this directly
- In systems with different arithmetic libraries or axiomatizations, you might need to explicitly reason about cases where $m < n$

---

## SUB_LEFT_LESS_EQ

### SUB_LEFT_LESS_EQ
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let SUB_LEFT_LESS_EQ = ARITH_RULE
  `!m n p:num. m <= (n - p) <=> (m + p) <= n \/ m <= 0`;;
```

### Informal statement
For all natural numbers $m$, $n$, and $p$, the following equivalence holds:
$$m \leq (n - p) \iff (m + p) \leq n \lor m \leq 0$$

This theorem relates an inequality involving subtraction to an alternative condition using addition, with a disjunctive case when $m = 0$.

### Informal proof
This theorem is proven using `ARITH_RULE`, which is a decision procedure for linear arithmetic over natural numbers in HOL Light. The proof itself is handled automatically by this decision procedure, which internally uses arithmetical reasoning to establish the equivalence.

The equivalence can be understood through the following reasoning:
- When $m \leq 0$, since $m$ is a natural number, this means $m = 0$, making the right side of the equivalence true.
- When $m > 0$:
  - If $n < p$, then $(n - p) = 0$ (by the definition of subtraction on natural numbers), so $m \leq (n - p)$ holds if and only if $m = 0$.
  - If $n \geq p$, then $m \leq (n - p) \iff m + p \leq n$ by adding $p$ to both sides.

### Mathematical insight
This theorem provides a useful way to rewrite inequalities involving subtraction in the natural numbers. The disjunct $m \leq 0$ handles the special case where subtraction in the natural numbers causes truncation at zero.

In the context of natural numbers, subtraction has the property that $n - p = 0$ whenever $n < p$, which makes working with inequalities involving subtraction more complex than in the integers. This theorem helps manage such situations by providing an equivalent condition that uses addition instead.

The theorem is particularly useful for theorem provers and formal systems that work with natural numbers, where managing the special behavior of subtraction is important for correct reasoning.

### Dependencies
Since this theorem is proven using `ARITH_RULE`, it directly depends on the built-in arithmetic reasoning capabilities of HOL Light.

### Porting notes
When porting to other systems:
- Ensure that natural number subtraction is properly handled in the target system, particularly with respect to truncation at zero.
- The proof might need to be expanded in systems without an equivalent to HOL Light's `ARITH_RULE` decision procedure.
- In systems with different treatments of natural number arithmetic (such as those based on Peano axioms), the proof might require more explicit reasoning steps.

---

## SUB_LEFT_GREATER_EQ

### SUB_LEFT_GREATER_EQ
- This is the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem (ARITH_RULE)

### Formal Content
```ocaml
let SUB_LEFT_GREATER_EQ =
  ARITH_RULE `!m n p:num. m >= (n - p) <=> (m + p) >= n`;;
```

### Informal statement
For all natural numbers $m$, $n$, and $p$, the following equivalence holds:
$$m \geq (n - p) \iff (m + p) \geq n$$

This theorem relates inequalities involving subtraction to inequalities involving addition.

### Informal proof
This is an arithmetic fact that follows directly from the properties of natural numbers. 

For natural numbers, we can rewrite the inequality $m \geq (n - p)$ in terms of addition.

If $n \geq p$, then $n - p$ is well-defined, and the equivalence becomes:
- $m \geq (n - p)$ means that $m + p \geq n - p + p = n$

If $n < p$, then $n - p = 0$ in natural number arithmetic (where subtraction is truncated at zero), so:
- $m \geq (n - p) = 0$ is always true since $m \geq 0$ for any natural number
- $(m + p) \geq n$ is also true because $p > n$ and $m \geq 0$, so $m + p > n$

Therefore, the equivalence holds in all cases.

### Mathematical insight
This theorem captures a fundamental property of inequalities in natural numbers when working with subtraction. It allows us to transform an inequality with subtraction on the right side into an inequality with addition on the left side.

The result is particularly useful when manipulating expressions involving differences of natural numbers, allowing them to be rewritten in a form that avoids potential issues with natural number subtraction (which is truncated at zero).

This theorem can be seen as a way to "move" a term from one side of an inequality to another, similar to how we solve algebraic inequalities, but properly accounting for the truncated subtraction in the natural numbers.

### Dependencies
No explicit dependencies are listed, but this theorem uses:
- Natural number arithmetic properties
- The definition of natural number subtraction (truncated at zero)
- `ARITH_RULE` tactic, which is HOL Light's automatic solver for linear arithmetic

### Porting notes
- When porting to other proof assistants, remember that natural number subtraction is often truncated at zero (i.e., $n - p = 0$ when $n < p$).
- Some proof assistants may have built-in arithmetic decision procedures similar to HOL Light's `ARITH_RULE` that can prove this directly.
- In systems with integers instead of natural numbers, you might need explicit non-negativity conditions.

---

## LESS_EQ_LESS_TRANS

### LESS_EQ_LESS_TRANS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- Theorem

### Formal Content
```ocaml
let LESS_EQ_LESS_TRANS = LET_TRANS;;
```

### Informal statement
This theorem states that the less-than-or-equal-to relation (`≤`) and the less-than relation (`<`) are transitive with respect to each other. In other words, if $a \leq b$ and $b < c$, then $a < c$.

### Informal proof
The theorem is defined as identical to `LET_TRANS`, which is a previously established theorem proving the transitivity between the less-than-or-equal-to and less-than relations. The definition simply creates an alias for the existing theorem.

### Mathematical insight
This theorem provides a fundamental property in ordered structures like real numbers or natural numbers. The transitivity between the less-than-or-equal-to relation and the less-than relation is essential in many mathematical proofs involving inequalities.

By having this theorem available as `LESS_EQ_LESS_TRANS`, the HOL Light library provides a more semantically clear name for this specific transitivity property, making proofs that use it more readable and understandable.

### Dependencies
- `LET_TRANS`: The theorem that establishes the transitivity between less-than-or-equal-to and less-than relations.

### Porting notes
When porting to other proof assistants, check if they already have built-in theorems for this property. Many systems would include this as part of their standard library for ordered structures. The name might differ in other systems, but the property is standard.

---

## LESS_0_CASES

### LESS_0_CASES
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LESS_0_CASES = ARITH_RULE `!m. (0 = m) \/ 0 < m`;;
```

### Informal statement
For all natural numbers $m$, either $0 = m$ or $0 < m$.

### Informal proof
This theorem is established using the `ARITH_RULE` tactic, which automatically proves arithmetic statements in HOL Light. The proof relies on the fundamental properties of natural numbers, specifically that every natural number is either equal to zero or greater than zero.

### Mathematical insight
This theorem expresses a basic property of natural numbers: any natural number is either equal to zero or strictly greater than zero. This is a fundamental case analysis that is often used in proofs involving natural numbers. The theorem provides a simple but essential dichotomy for reasoning about natural numbers.

### Dependencies
No explicitly listed dependencies, as this is proven directly with `ARITH_RULE`, which handles basic arithmetic reasoning automatically.

### Porting notes
This theorem should be straightforward to port to other proof assistants, as it represents a basic property of natural numbers that is typically axiomatized or easily provable in most systems. In some systems, this might already be a built-in lemma or derivable through basic automation.

---

## LESS_OR

### LESS_OR
- LESS_OR

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LESS_OR = ARITH_RULE `!m n. m < n ==> (SUC m) <= n`;;
```

### Informal statement
For all natural numbers $m$ and $n$, if $m < n$, then $\text{SUC}(m) \leq n$.

Where:
- $\text{SUC}(m)$ represents the successor of $m$ (i.e., $m + 1$)
- $<$ is the strict less-than relation on natural numbers
- $\leq$ is the less-than-or-equal-to relation on natural numbers

### Informal proof
This theorem is proven using `ARITH_RULE`, which is an automated procedure in HOL Light that resolves simple arithmetic statements. 

The proof relies on the basic property of natural numbers that if $m < n$, then $m + 1 \leq n$. This follows directly from the definition of the less-than relation on natural numbers, where $m < n$ means that there exists a positive natural number $k$ such that $m + k = n$. When $m < n$, we know there exists a $k > 0$ such that $m + k = n$, which means $m + 1 \leq n$.

### Mathematical insight
This theorem establishes a basic relationship between the strictly-less-than relation ($<$) and the less-than-or-equal relation ($\leq$) for natural numbers. It states that if $m$ is strictly less than $n$, then the successor of $m$ is less than or equal to $n$.

This is a fundamental property in arithmetic and is particularly useful in inductive proofs and algorithms that involve incrementing or iterating through natural numbers. The theorem captures the intuitive notion that if $m < n$, then $m + 1$ can be at most $n$ (and not greater).

### Dependencies
Since this theorem is proven using `ARITH_RULE`, it relies on the built-in arithmetic reasoning capabilities of HOL Light rather than specific previously proven theorems.

---

## SUB

### SUB
- SUB

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let SUB = ARITH_RULE
  `(!m. 0 - m = 0) /\
   (!m n. (SUC m) - n = (if m < n then 0 else SUC(m - n)))`;;
```

### Informal statement
This theorem establishes the basic properties of subtraction for natural numbers:

1. For all natural numbers $m$, $0 - m = 0$
2. For all natural numbers $m$ and $n$, $(SUC\ m) - n = \begin{cases} 0 & \text{if}\ m < n \\ SUC(m - n) & \text{otherwise} \end{cases}$

### Informal proof
This theorem is established using `ARITH_RULE`, which automatically proves basic arithmetic facts about natural numbers. The proof leverages the built-in decision procedure for Presburger arithmetic.

The statement combines two key properties of natural number subtraction:
- The first part states that zero minus any natural number is zero (since natural number subtraction is truncated).
- The second part provides a recursive definition for subtraction involving a successor, handling the case where the result would be negative by returning zero.

### Mathematical insight
This theorem formalizes the definition of truncated subtraction for natural numbers, where the result is never negative. This operation is sometimes called "monus" and denoted $m \dot{-} n$.

The key property captured is that natural number subtraction behaves differently from integer subtraction:
- When subtracting a larger number from a smaller one, the result is 0 rather than a negative number
- Otherwise, subtraction works as expected

This definition is essential for formalizing arithmetic operations on natural numbers in a type system without negative numbers.

### Dependencies
- Arithmetic rules and definitions for natural numbers
- HOL Light's natural number representation

### Porting notes
- When porting to systems with different natural number representations, be aware that this defines truncated subtraction
- In systems where natural numbers are a subtype of integers, you may need to explicitly define truncated subtraction as a separate operation from regular subtraction

---

## LESS_MULT_MONO

### LESS_MULT_MONO
- LESS_MULT_MONO

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LESS_MULT_MONO = prove
 (`!m i n. ((SUC n) * m) < ((SUC n) * i) <=> m < i`,
  REWRITE_TAC[LT_MULT_LCANCEL; NOT_SUC]);;
```

### Informal statement
For any natural numbers $m$, $i$, and $n$, the following equivalence holds:
$$(n+1) \cdot m < (n+1) \cdot i \iff m < i$$

This theorem states that multiplication by a positive constant (represented as $n+1$) preserves strict inequalities between natural numbers.

### Informal proof
The proof is straightforward:
- We apply the theorem `LT_MULT_LCANCEL`, which states that for any positive number $p$ (i.e., a successor), $p \cdot a < p \cdot b \iff a < b$.
- We also use `NOT_SUC` which asserts that a successor is never equal to zero (i.e., $\forall n. \neg(SUC(n) = 0)$), confirming that $n+1$ is indeed positive.
- The `REWRITE_TAC` tactic then automatically solves the goal by applying these two theorems.

### Mathematical insight
This theorem formalizes the basic algebraic property that multiplication by a positive constant preserves strict order. This is a fundamental result in ordered structures and is frequently used in arithmetic reasoning.

The result is intuitively clear: when multiplying both sides of an inequality by the same positive number, the relation between the terms remains unchanged. This property is essential in various mathematical contexts, particularly when manipulating and simplifying inequalities.

### Dependencies
- `LT_MULT_LCANCEL` - Left cancellation law for multiplication with respect to the less-than relation
- `NOT_SUC` - Axiom stating that a successor is never zero

### Porting notes
This theorem should be straightforward to port to other proof assistants. Most systems have built-in theorems about multiplication preserving order. The only consideration is to ensure that the target system also uses a similar representation of natural numbers (i.e., with a successor function) or to adapt the statement accordingly.

---

## LESS_MONO_MULT

### LESS_MONO_MULT
- `LESS_MONO_MULT`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LESS_MONO_MULT = prove
 (`!m n p. m <= n ==> (m * p) <= (n * p)`,
  SIMP_TAC[LE_MULT_RCANCEL]);;
```

### Informal statement
For all natural numbers $m$, $n$, and $p$, if $m \leq n$, then $m \cdot p \leq n \cdot p$.

### Informal proof
The proof is straightforward by applying the theorem `LE_MULT_RCANCEL`, which states that multiplication preserves the less-than-or-equal relation when performed with the same right operand.

The theorem is proved using simplification tactics that directly apply `LE_MULT_RCANCEL`.

### Mathematical insight
This theorem establishes the monotonicity of multiplication with respect to the less-than-or-equal relation. It shows that multiplication by a fixed natural number preserves ordering, which is a fundamental property of ordered rings. This result is often used in inequality proofs and algorithm analysis where we need to compare products of natural numbers.

### Dependencies
- Theorems:
  - `LE_MULT_RCANCEL`: States that for natural numbers $a$, $b$, and $c$, if $a \cdot c \leq b \cdot c$, then $a \leq b$ (when $c \neq 0$). In this proof, it's used in the reverse direction.

### Porting notes
This theorem should be straightforward to port to other proof assistants, as it relies on a basic property of natural numbers that is likely already available in the standard libraries of most systems. The porting would involve finding the equivalent of `LE_MULT_RCANCEL` in the target system and applying it appropriately.

---

## LESS_MULT2

### LESS_MULT2
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_MULT2 = prove
 (`!m n. 0 < m /\ 0 < n ==> 0 < (m * n)`,
  REWRITE_TAC[LT_MULT]);;
```

### Informal statement
For all integers $m$ and $n$, if $0 < m$ and $0 < n$, then $0 < m \times n$.

### Informal proof
The theorem is proved by directly applying the rewrite tactic with the theorem `LT_MULT`, which relates the ordering of products and is relevant to this specific goal.

The theorem `LT_MULT` likely states that the product of two positive numbers is positive, which directly proves our goal.

### Mathematical insight
This is a basic property of multiplication of positive integers, stating that the product of two positive numbers is also positive. This result is part of the foundational arithmetic properties and is used frequently in various proofs involving inequalities and products.

### Dependencies
- `LT_MULT`: A theorem that likely states the relationship between the ordering of numbers and their product.

### Porting notes
This theorem should be straightforward to port to other proof assistants as it represents a basic arithmetic property. Most proof assistants will have built-in tactics or lemmas that handle this directly, or it might even be part of the standard library.

---

## SUBSET_FINITE

### SUBSET_FINITE
- `SUBSET_FINITE`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let SUBSET_FINITE = prove
 (`!s. FINITE s ==> (!t. t SUBSET s ==> FINITE t)`,
  MESON_TAC[FINITE_SUBSET]);;
```

### Informal statement
For all sets $s$, if $s$ is finite, then for all sets $t$ such that $t \subseteq s$, $t$ is also finite.

In mathematical notation:
$$\forall s. \text{FINITE}(s) \Rightarrow (\forall t. t \subseteq s \Rightarrow \text{FINITE}(t))$$

### Informal proof
This theorem is proved using the previously established theorem `FINITE_SUBSET`, which states that if a set $t$ is a subset of a finite set $s$, then $t$ is also finite.

The proof uses the `MESON_TAC` (Model Elimination Search for Natural deduction) tactic with `FINITE_SUBSET` as the key lemma. The automated reasoning handles the straightforward logical deduction from the premise that $s$ is finite and $t \subseteq s$ to the conclusion that $t$ is finite.

### Mathematical insight
This theorem establishes the basic property that finiteness is preserved under the subset relation. In other words, any subset of a finite set is also finite. 

This result is foundational in set theory and is used extensively in proofs involving finite sets. The property is intuitive: if a set contains only finitely many elements, then any subset of it must contain at most that many elements, and therefore must also be finite.

In the context of formal mathematics, this theorem provides a basic inference rule that allows finiteness to be propagated through subset relationships.

### Dependencies
- theorems:
  - `FINITE_SUBSET`: If $t \subseteq s$ and $s$ is finite, then $t$ is finite.

### Porting notes
This theorem should be straightforward to port to other proof assistants, as the property it states is standard and the proof relies on automation applying a single lemma. Most proof assistants will have similar theorems about finiteness of subsets, possibly with different names but equivalent content.

---

## LESS_EQ_SUC

### LESS_EQ_SUC
- `LESS_EQ_SUC`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let LESS_EQ_SUC = prove
 (`!n. m <= SUC n <=> (m = SUC n) \/ m <= n`,
  REWRITE_TAC[LE]);;
```

### Informal statement
For any natural numbers $m$ and $n$, we have 
$$m \leq \text{SUC}(n) \iff (m = \text{SUC}(n)) \lor (m \leq n)$$

where $\text{SUC}(n)$ represents the successor of $n$, i.e., $n+1$.

### Informal proof
The proof is straightforward using the definition of the less-than-or-equal relation (`LE`). When we rewrite using the definition of `LE`, we get the desired equivalence directly.

### Mathematical insight
This theorem provides a case analysis for the inequality $m \leq n+1$. It states that $m$ is less than or equal to the successor of $n$ if and only if either $m$ equals the successor of $n$ (i.e., $m = n+1$), or $m$ is less than or equal to $n$ itself.

This is a standard property in Peano arithmetic that allows us to reason about inequalities involving successor terms. It's particularly useful in inductive proofs where we often need to analyze cases involving comparisons with successive natural numbers.

### Dependencies
- Definitions: 
  - `LE` (less-than-or-equal relation for natural numbers)

### Porting notes
When porting this to other proof assistants, note that:
- The theorem uses the `SUC` (successor) function and the `<=` (less-than-or-equal) relation for natural numbers.
- Most proof assistants have equivalent concepts, but the notation might differ.
- In systems with constructive foundations, ensure that the disjunction in the right-hand side of the equivalence is decidable.

---

## ANTE_RES_THEN

### ANTE_RES_THEN
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- Tactic definition

### Formal Content
```ocaml
let ANTE_RES_THEN ttac th = FIRST_ASSUM(fun t -> ttac (MATCH_MP t th));;
```

### Informal statement
This tactic definition `ANTE_RES_THEN` implements a higher-order tactic that:

1. Takes a tactic-producing function `ttac` and a theorem `th` as inputs
2. Searches through the assumption list using `FIRST_ASSUM`
3. For each assumption `t`, it attempts to match `t` with the antecedent of `th` using `MATCH_MP`
4. If successful, it applies `ttac` to the resulting theorem

More precisely, `ANTE_RES_THEN ttac th` applies the tactic-producing function `ttac` to the result of the `MATCH_MP` resolution between an assumption from the current goal and the given theorem `th`.

### Informal proof
This is a tactic definition, not a theorem, so it doesn't have a proof. The implementation:
- Uses `FIRST_ASSUM` to search through assumptions of the current goal
- For each assumption `t`, applies `MATCH_MP t th` to perform resolution
- If successful, passes the resulting theorem to the tactic-producing function `ttac`
- The resulting tactic is then applied to the goal

### Mathematical insight
`ANTE_RES_THEN` is a tactical (tactic combinator) that provides a convenient mechanism for forward reasoning in interactive theorem proving. It represents a common pattern where:

1. We have a conditional theorem `th` of the form `A ⟹ B`
2. We search the current assumptions for something that matches `A`
3. We derive `B` through modus ponens
4. We then use the derived proposition `B` in some way specified by `ttac`

This tactic is particularly useful for automating common patterns of forward reasoning in proofs, especially when combining implication elimination with further tactics. It helps reduce repetitive proof structure and keep proofs more concise and readable.

### Dependencies
- Tactics:
  - `FIRST_ASSUM`: Applies a tactic-producing function to the first assumption that succeeds
  - `MATCH_MP`: Resolution rule that matches and eliminates the antecedent of an implication

### Porting notes
When porting to other systems:
- This tactic requires good support for higher-order tactics (tactics that return tactics)
- The implementation depends on how assumptions are handled in the target system
- The exact behavior of `MATCH_MP` should be understood - it performs higher-order pattern matching between terms and handles instantiations
- In systems with explicit contexts rather than assumption lists, this might need adaptation to work with the local context

---

## IMP_RES_THEN

### IMP_RES_THEN

### Type of the formal statement
Tactic definition (functional value definition)

### Formal Content
```ocaml
let IMP_RES_THEN ttac th = FIRST_ASSUM(fun t -> ttac (MATCH_MP th t));;
```

### Informal statement
`IMP_RES_THEN` is a higher-order tactic that takes a tactic `ttac` and a theorem `th` as inputs, and returns a tactic that:
1. Finds the first assumption in the goal that can be combined with `th` using modus ponens (`MATCH_MP`)
2. Applies the tactic `ttac` to the result of this combination

More precisely, if:
- `ttac` is a tactic that expects a theorem as input
- `th` is a theorem of the form $P \Rightarrow Q$
- The goal contains an assumption matching $P$

Then `IMP_RES_THEN ttac th` will apply `ttac` to the theorem $Q$ derived from modus ponens.

### Informal proof
This is a direct definition that composes several operations:

```
IMP_RES_THEN ttac th = FIRST_ASSUM(fun t -> ttac (MATCH_MP th t))
```

The definition combines:
- `FIRST_ASSUM`: A tactic that finds the first assumption satisfying a condition
- `MATCH_MP`: HOL Light's implementation of modus ponens
- Function composition to apply `ttac` to the result of modus ponens

### Mathematical insight
`IMP_RES_THEN` provides a convenient way to apply modus ponens with an assumption and then use the resulting theorem. This tactic is particularly useful in proofs where you have implications (theorems of the form $P \Rightarrow Q$) and assumptions that match the antecedent.

The tactic encapsulates a common proof pattern:
1. Find an assumption that matches the antecedent of an implication
2. Apply modus ponens to derive a new theorem
3. Use that derived theorem in a specific way (via the provided tactic `ttac`)

This higher-order tactic is part of HOL Light's infrastructure for creating derived inference rules and tactics that chain reasoning steps together, making proofs more concise and readable.

### Dependencies
- Core tactics:
  - `FIRST_ASSUM`: Applies a tactic-producing function to the first assumption that doesn't fail
  - `MATCH_MP`: Implements modus ponens for matching theorems

### Porting notes
When porting to other proof assistants:
- Most theorem provers have similar concepts of assumptions within a goal
- The implementation details of modus ponens may differ between systems
- Consider how the target system handles higher-order tactics (tactics that produce or consume other tactics)
- Some systems might require explicit handling of assumption labels or contexts

---

## INFINITE_MEMBER

### INFINITE_MEMBER
- `INFINITE_MEMBER`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let INFINITE_MEMBER = prove(
  `!s. INFINITE(s:A->bool) ==> ?x. x IN s`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(s:A->bool = {})` MP_TAC THENL
   [UNDISCH_TAC `INFINITE (s:A->bool)` THEN
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INFINITE; FINITE_EMPTY];
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN
    PURE_ONCE_REWRITE_TAC[NOT_FORALL_THM] THEN
    REWRITE_TAC[]]);;
```

### Informal statement
For any set $s$ of type $A \to \text{bool}$, if $s$ is infinite, then there exists an element $x$ such that $x \in s$.

### Informal proof
The proof proceeds by contradiction:

1. We start with a set $s$ and assume it is infinite.
2. First, we prove that $s$ is non-empty using a contradiction approach:
   - We set up a sub-goal to show $s \neq \emptyset$.
   - If $s$ were empty, then it would be finite (since the empty set is finite).
   - This would contradict our assumption that $s$ is infinite.
3. Once we establish that $s$ is non-empty, we use the set extension principle:
   - By definition, $s \neq \emptyset$ means there exists some element in $s$ that is not in the empty set.
   - The statement $\exists x. x \in s$ follows directly.

### Mathematical insight
This theorem establishes the fundamental property that infinite sets contain at least one element. While this might seem obvious, it's a crucial bridge between the abstract notion of infinity and concrete elements. In formal systems, we need to explicitly establish that infinitude implies non-emptiness, as these are distinct concepts in axiomatic set theory.

### Dependencies
- Set theory definitions:
  - `INFINITE`: A predicate that holds when a set is not finite
  - `FINITE_EMPTY`: States that the empty set is finite
  - `EXTENSION`: The extensionality principle for sets
  - `NOT_IN_EMPTY`: States that no element belongs to the empty set

### Porting notes
When porting this theorem:
- Be aware that different proof assistants may have different definitions of infinitude.
- Some systems might already have this as a trivial consequence of their set theory foundations.
- The proof technique using contraposition and extensionality is standard and should translate well across systems.

---

## INFINITE_CHOOSE

### INFINITE_CHOOSE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INFINITE_CHOOSE = prove(
  `!s:A->bool. INFINITE(s) ==> ((@) s) IN s`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP INFINITE_MEMBER) THEN
  DISCH_THEN(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[IN] THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN REWRITE_TAC[]);;
```

### Informal statement
For any infinite set $s$ of type $A \to \text{bool}$ (a set of elements of type $A$), the element selected by the choice operator applied to $s$, denoted as $(\varepsilon) s$, belongs to the set $s$.

In formal notation:
$$\forall s: A \to \text{bool},\; \text{INFINITE}(s) \Rightarrow (\varepsilon) s \in s$$

### Informal proof
The proof establishes that for an infinite set, the element selected by the choice operator is a member of the set:

1. Start with an infinite set $s$.
2. Apply `INFINITE_MEMBER` theorem, which states that any infinite set contains at least one element, giving $\exists x.\, x \in s$.
3. Use the Select axiom (`SELECT_RULE`), which states that if $\exists x.\, P(x)$, then $P((\varepsilon) P)$, where $\varepsilon$ is the choice operator.
4. In our context, this means that if $\exists x.\, x \in s$, then $(\varepsilon) s \in s$.
5. The remaining steps perform simplification with ETA conversion and rewriting to conclude the result.

### Mathematical insight
This theorem provides a constructive way to extract an element from any infinite set using the choice operator. It's significant because:

1. It guarantees the existence of a canonical element in any infinite set.
2. It enables proofs by choosing a specific but arbitrary element from an infinite set.
3. It connects the choice operator with infinite sets, providing a mechanism to work with infinite collections constructively.

The choice operator (Hilbert's epsilon) selects a witness to an existential statement, and this theorem ensures that when applied to an infinite set, it selects an actual member of that set.

### Dependencies
- Theorems:
  - `INFINITE_MEMBER`: States that an infinite set has at least one member
  - `SELECT_RULE`: The axiom of choice principle for the epsilon operator
  - Implicit: ETA_CONV and other simplification rules

### Porting notes
When porting to other systems:
- Ensure the target system has a similar choice operator or Hilbert's epsilon
- Verify that the system has a compatible definition of infinite sets
- The ETA conversion simplification might need different handling in other proof assistants

---

## INFINITE_DELETE

### INFINITE_DELETE
- INFINITE_DELETE

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let INFINITE_DELETE = prove(
  `!(t:A->bool) x. INFINITE (t DELETE x) = INFINITE(t)`,
  REWRITE_TAC[INFINITE; FINITE_DELETE]);;
```

### Informal statement
For any set $t$ of type $A \to \text{bool}$ and any element $x$ of type $A$, the set $t \setminus \{x\}$ is infinite if and only if $t$ is infinite.

In formal terms:
$$\forall t: A \to \text{bool}, \forall x: A, \text{INFINITE}(t \setminus \{x\}) \Leftrightarrow \text{INFINITE}(t)$$

### Informal proof
The proof is straightforward:
- We use the definitions of `INFINITE` and `FINITE_DELETE` to rewrite the statement.
- By definition, a set is infinite if and only if it is not finite.
- The theorem `FINITE_DELETE` states that $t \setminus \{x\}$ is finite if and only if $t$ is finite.
- Therefore, $t \setminus \{x\}$ is infinite if and only if $t$ is infinite.

### Mathematical insight
This theorem establishes that the property of being an infinite set is preserved when removing a single element. This is a basic but important property of infinite sets - removing or adding finitely many elements doesn't change their cardinality class.

The result aligns with the intuitive understanding that infinite sets remain infinite after removing a finite number of elements, which is a fundamental concept in set theory and the study of cardinality.

### Dependencies
- `INFINITE`: Definition of what it means for a set to be infinite (not finite)
- `FINITE_DELETE`: Theorem stating that removing one element from a set preserves finiteness

---

## INFINITE_INSERT

### INFINITE_INSERT
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let INFINITE_INSERT = prove(
  `!(x:A) t. INFINITE(x INSERT t) = INFINITE(t)`,
  REWRITE_TAC[INFINITE; FINITE_INSERT]);;
```

### Informal statement
For any element $x$ of type $A$ and any set $t$, the set $\{x\} \cup t$ is infinite if and only if $t$ is infinite.

### Informal proof
The proof follows directly from the definitions of `INFINITE` and `FINITE_INSERT`.

By definition, a set is infinite if and only if it is not finite. The theorem `FINITE_INSERT` states that $\{x\} \cup t$ is finite if and only if $t$ is finite. Therefore, $\{x\} \cup t$ is infinite if and only if $t$ is infinite.

### Mathematical insight
This theorem establishes that adding a single element to a set does not change its infinite/finite status. This is intuitive because:
1. Adding one element to a finite set still results in a finite set
2. Adding one element to an infinite set still results in an infinite set

This is a basic property that helps reason about infinite sets and is used in cardinal arithmetic. The property reflects that for infinite cardinalities, adding a finite number does not change the cardinality.

### Dependencies
- Definitions:
  - `INFINITE`: A set is infinite if it is not finite
  - `FINITE_INSERT`: A set with an element inserted is finite if and only if the original set is finite

### Porting notes
This theorem should be straightforward to port to other proof assistants as it relies on basic set theory concepts. Most proof assistants have built-in notions of finite and infinite sets with similar properties.

---

## SIZE_INSERT

I'll revise the documentation to correct the semantic inaccuracy in the informal statement regarding the INSERT operation.

### SIZE_INSERT
- SIZE_INSERT

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let SIZE_INSERT = prove(
  `!(x:A) t. ~(x IN t) /\ t HAS_SIZE n ==> (x INSERT t) HAS_SIZE (SUC n)`,
  SIMP_TAC[HAS_SIZE; CARD_CLAUSES; FINITE_RULES]);;
```

### Informal statement
For any element $x$ of type $A$ and any set $t$, if $x \not\in t$ and $t$ has size $n$, then the set obtained by inserting $x$ into $t$ has size $n + 1$.

Formally:
$\forall (x:A) \, t. \, x \not\in t \land t \text{ HAS\_SIZE } n \implies (x \text{ INSERT } t) \text{ HAS\_SIZE } (n + 1)$

Where:
- $\text{HAS\_SIZE}$ is a relation stating that a set has a specific cardinality
- $\text{INSERT}$ denotes the insertion of an element into a set (i.e., $t \cup \{x\}$)
- $\text{SUC}$ is the successor function (i.e., $n + 1$)

### Informal proof
The theorem is proved by simplification using the definitions of `HAS_SIZE`, `CARD_CLAUSES`, and `FINITE_RULES`.

The proof relies on the following facts:
- `HAS_SIZE` defines that a set $t$ has size $n$ if $t$ is finite and the cardinality of $t$ is $n$
- `CARD_CLAUSES` provides that the cardinality of $t \cup \{x\}$ is $n + 1$ when $x \not\in t$ and $t$ has cardinality $n$
- `FINITE_RULES` ensures that inserting an element into a finite set results in a finite set

By combining these facts through simplification, we establish that adding a new element to a set of size $n$ yields a set of size $n+1$.

### Mathematical insight
This theorem captures a fundamental property of finite sets and cardinality: adding a new element to a finite set increases its cardinality by exactly 1. This is intuitive but formally important for reasoning about set operations and their effect on cardinality.

The theorem is particularly useful in inductive proofs about finite sets, where one often builds sets by adding elements one at a time. It establishes the base case for many counting arguments on sets.

### Dependencies
- **Definitions**: `HAS_SIZE`
- **Theorems**: `CARD_CLAUSES`, `FINITE_RULES`

### Porting notes
When porting to other proof assistants:
- Ensure that the target system has corresponding definitions for set cardinality and finiteness
- The simplification might need to be more explicit in systems with less powerful simplification tactics
- Note that HOL Light's `INSERT` operation adds a single element to a set; in some systems this might be represented differently

---

## SIZE_DELETE

### SIZE_DELETE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let SIZE_DELETE = prove(
  `!(x:A) t. x IN t /\ t HAS_SIZE (SUC n) ==> (t DELETE x) HAS_SIZE n`,
  SIMP_TAC[HAS_SIZE_SUC]);;
```

### Informal statement
For any element $x$ of type $A$ and any set $t$, if $x \in t$ and $t$ has size $\text{SUC}(n)$ (i.e., $n+1$), then the set $t \setminus \{x\}$ has size $n$.

In mathematical notation:
$$\forall x:A, \forall t. (x \in t \land |t| = n+1) \Rightarrow |t \setminus \{x\}| = n$$

### Informal proof
This theorem is proved by direct simplification using the theorem `HAS_SIZE_SUC`, which relates sets of size $n+1$ to removing an element from them.

The proof applies the simplification tactic with `HAS_SIZE_SUC`, which contains the logical equivalence:
$$t \text{ HAS_SIZE } (n+1) \iff \exists x. x \in t \land (t \setminus \{x\}) \text{ HAS_SIZE } n$$

Given our assumptions that $x \in t$ and $t$ has size $n+1$, the simplification directly establishes that $t \setminus \{x\}$ has size $n$.

### Mathematical insight
This theorem captures a basic property of finite sets: removing a single element from a set of size $n+1$ results in a set of size $n$. This is a fundamental counting principle used throughout discrete mathematics and set theory.

The result is particularly useful in inductive proofs about finite sets, where reducing the size of a set by exactly one element allows for applying an induction hypothesis.

### Dependencies
- Theorems:
  - `HAS_SIZE_SUC`: Establishes that a set has size $n+1$ if and only if there exists an element in the set such that removing it yields a set of size $n$.

### Porting notes
When porting this theorem:
- Ensure that your target system has a compatible notion of set size (cardinality for finite sets)
- Check that the deletion operation (`DELETE` in HOL Light) is defined similarly in the target system
- The proof should be straightforward in any system with good automation for set theory, possibly requiring just a simple application of the corresponding version of the `HAS_SIZE_SUC` theorem.

---

## SIZE_EXISTS

### SIZE_EXISTS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let SIZE_EXISTS = prove(
  `!s N. s HAS_SIZE (SUC N) ==> ?x:A. x IN s`,
  SIMP_TAC[HAS_SIZE_SUC; GSYM MEMBER_NOT_EMPTY]);;
```

### Informal statement
For any set $s$ and natural number $N$, if $s$ has size $N+1$ (i.e., $s$ contains exactly $N+1$ elements), then there exists an element $x$ of type $A$ such that $x \in s$.

### Informal proof
The proof follows directly by simplification using two key facts:
- By `HAS_SIZE_SUC`, a set has size $\text{SUC}(N) = N+1$ if and only if there exists an element $x$ in the set such that the set without $x$ has size $N$.
- By `MEMBER_NOT_EMPTY` (applied with `GSYM`), a set having a member is equivalent to the set not being empty.

These two facts together immediately establish that if a set has size $N+1$, it must contain at least one element.

### Mathematical insight
This theorem establishes a basic but important property of finite sets: any set with at least one element (specifically, with size $N+1$ for any $N$) is non-empty. This is a fundamental result connecting the cardinality of a set with the existence of elements in the set. While this result may seem trivial, it is often useful in formal reasoning about finite sets where we need to explicitly extract elements from sets known to have a certain size.

### Dependencies
- `HAS_SIZE_SUC`: Relates a set of size N+1 to a set of size N by adding one element
- `MEMBER_NOT_EMPTY`: Connects the existence of a member in a set with the set being non-empty

### Porting notes
When porting this theorem to other proof assistants, note that it depends on how set cardinality is defined in the target system. Most systems should have equivalent definitions for set size and membership, making this a straightforward port.

---

## SUBSET_DELETE

### SUBSET_DELETE

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let SUBSET_DELETE = prove(
  `!s t (x:A). s SUBSET t ==> (s DELETE x) SUBSET t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `s:A->bool` THEN ASM_REWRITE_TAC[DELETE_SUBSET]);;
```

### Informal statement
For all sets $s$, $t$ and element $x$ of type $A$, if $s \subseteq t$, then $(s \setminus \{x\}) \subseteq t$.

### Informal proof
The proof proceeds by demonstrating that $(s \setminus \{x\}) \subseteq s \subseteq t$, thus showing $(s \setminus \{x\}) \subseteq t$ by transitivity of subset relation.

- We begin with the hypothesis that $s \subseteq t$.
- Apply the transitivity of subset relation (`SUBSET_TRANS`): if $(s \setminus \{x\}) \subseteq s$ and $s \subseteq t$, then $(s \setminus \{x\}) \subseteq t$.
- For the first part, we use the fact that $(s \setminus \{x\}) \subseteq s$ (from `DELETE_SUBSET`).
- Combined with our hypothesis $s \subseteq t$, we obtain $(s \setminus \{x\}) \subseteq t$.

### Mathematical insight
This theorem establishes a basic property of set operations: removing an element from a set that is already a subset of another set preserves the subset relation. This is intuitive because removing elements from a set can only make the subset relation stronger, never invalidate it.

The theorem is a simple application of the transitivity property of the subset relation combined with the fundamental property that removing elements from a set yields a subset of the original set.

### Dependencies
- `SUBSET_TRANS`: Transitivity of subset relation
- `DELETE_SUBSET`: For any set $s$ and element $x$, $(s \setminus \{x\}) \subseteq s$

### Porting notes
This theorem should be straightforward to port to other systems as it relies on basic set theory properties. Most proof assistants have built-in libraries for set operations that include the necessary definitions for set deletion and subset relations.

---

## INFINITE_FINITE_CHOICE

### INFINITE_FINITE_CHOICE
- `INFINITE_FINITE_CHOICE`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let INFINITE_FINITE_CHOICE = prove(
  `!n (s:A->bool). INFINITE(s) ==> ?t. t SUBSET s /\ t HAS_SIZE n`,
  INDUCT_TAC THEN GEN_TAC THEN DISCH_TAC THENL
   [EXISTS_TAC `{}:A->bool` THEN
    REWRITE_TAC[HAS_SIZE; EMPTY_SUBSET; HAS_SIZE_0];
    FIRST_ASSUM(UNDISCH_TAC o check is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPEC `s DELETE ((@) s :A)`) THEN
    ASM_REWRITE_TAC[INFINITE_DELETE] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `((@) s :A) INSERT t` THEN CONJ_TAC THENL
     [REWRITE_TAC[INSERT_SUBSET] THEN CONJ_TAC THENL
       [MATCH_MP_TAC INFINITE_CHOOSE THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
        GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
        REWRITE_TAC[IN_DELETE] THEN CONV_TAC(EQT_INTRO o TAUT)];
        MATCH_MP_TAC SIZE_INSERT THEN ASM_REWRITE_TAC[] THEN
        DISCH_TAC THEN UNDISCH_TAC `t SUBSET (s DELETE ((@) s:A))` THEN
        REWRITE_TAC[SUBSET; IN_DELETE] THEN
        DISCH_THEN(IMP_RES_THEN MP_TAC) THEN REWRITE_TAC[]]]);;
```

### Informal statement
For any natural number $n$ and any infinite set $s$ of type $A$, there exists a subset $t$ of $s$ such that $t$ has exactly $n$ elements.

### Informal proof
The proof proceeds by induction on $n$.

Base case ($n = 0$):
- Assume $s$ is an infinite set.
- We choose $t = \emptyset$ (the empty set).
- Then $t \subseteq s$ (the empty set is a subset of any set).
- And $t$ has size 0 (the empty set has 0 elements).

Inductive step (assume true for $n$, prove for $n+1$):
- Assume $s$ is an infinite set.
- By the induction hypothesis, we know that for any infinite set, there exists a subset of size $n$.
- Consider the set $s \setminus \{(@)s\}$, where $(@)s$ is the arbitrarily chosen element from $s$ (using the choice operator).
- This set is still infinite by `INFINITE_DELETE`.
- By the induction hypothesis, there exists a subset $t \subseteq s \setminus \{(@)s\}$ with exactly $n$ elements.
- Let's define a new set $t' = \{(@)s\} \cup t$.
- We need to show that $t' \subseteq s$ and $t'$ has size $n+1$.
- For $t' \subseteq s$:
  - $(@)s \in s$ by `INFINITE_CHOOSE`.
  - For all elements $x \in t$, we have $x \in s \setminus \{(@)s\}$, which implies $x \in s$.
  - Therefore, $t' \subseteq s$.
- For $t'$ having size $n+1$:
  - We know $t$ has size $n$.
  - Since $t \subseteq s \setminus \{(@)s\}$, we know $(@)s \not\in t$.
  - By `SIZE_INSERT`, adding $(@)s$ to $t$ increases its size by 1, so $t'$ has size $n+1$.

### Mathematical insight
This theorem establishes that we can extract finite subsets of any size from an infinite set. It is a fundamental result in set theory that connects the notions of infinity and finite cardinality.

The proof uses a constructive approach by building the desired subset incrementally. Starting from the empty set, it repeatedly selects one element from the infinite set and adds it to the subset, ensuring at each step that we maintain the required cardinality.

This result is often used in combinatorial arguments where we need to work with finite subsets of specific sizes from an infinite collection.

### Dependencies
- Theorems:
  - `INFINITE_CHOOSE`: If a set is infinite, then the choice operator selects an element from the set.
  - `INFINITE_DELETE`: Removing one element from an infinite set leaves an infinite set.
  - `SIZE_INSERT`: If an element is not in a set of size n, then adding that element creates a set of size n+1.

### Porting notes
When porting this theorem:
- Make sure the choice operator or an equivalent mechanism is available in the target system to select an arbitrary element from an infinite set.
- The proof relies on set operations like DELETE, INSERT, and SUBSET, which should be translated to their equivalents in the target system.
- The induction is straightforward natural number induction, which should be available in any proof assistant.

---

## IMAGE_WOP_LEMMA

### IMAGE_WOP_LEMMA

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let IMAGE_WOP_LEMMA = prove(
  `!N (t:num->bool) (u:A->bool).
        u SUBSET (IMAGE f t) /\ u HAS_SIZE (SUC N) ==>
        ?n v. (u = (f n) INSERT v) /\
              !y. y IN v ==> ?m. (y = f m) /\ n < m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `\n:num. ?y:A. y IN u /\ (y = f n)` num_WOP) THEN BETA_TAC THEN
  DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `y:A` o MATCH_MP SIZE_EXISTS) THEN
  FIRST_ASSUM(MP_TAC o SPEC `y:A` o REWRITE_RULE[SUBSET]) THEN
  ASM_REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  W(C SUBGOAL_THEN (fun t ->REWRITE_TAC[t]) o
       funpow 2 (fst o dest_imp) o snd) THENL
   [MAP_EVERY EXISTS_TAC [`n:num`; `y:A`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`m:num`; `u DELETE (x:A)`] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC INSERT_DELETE THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    X_GEN_TAC `z:A` THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `z:A` o REWRITE_RULE[SUBSET]) THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[GSYM NOT_LESS_EQUAL] THEN
    REWRITE_TAC[LESS_OR_EQ; DE_MORGAN_THM] THEN CONJ_TAC THENL
     [DISCH_THEN(ANTE_RES_THEN (MP_TAC o CONV_RULE NOT_EXISTS_CONV)) THEN
      DISCH_THEN(MP_TAC o SPEC `z:A`) THEN REWRITE_TAC[] THEN
      CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~(z:A = x)` THEN ASM_REWRITE_TAC[]]]);;
```

### Informal statement
For any natural number $N$, set $t \subseteq \mathbb{N}$, and set $u \subseteq A$ where $A$ is a type, if $u \subseteq f[t]$ (i.e., $u$ is a subset of the image of $t$ under $f$) and $u$ has size $\text{SUC}(N)$ (i.e., $u$ has exactly $N+1$ elements), then there exists a natural number $n$ and a set $v$ such that:
1. $u = \{f(n)\} \cup v$
2. For all $y \in v$, there exists an $m$ such that $y = f(m)$ and $n < m$

In other words, if $u$ is a finite subset of the image of $f$ over $t$, then we can find the element with the smallest preimage and isolate it.

### Informal proof
This theorem is a consequence of the well-ordering principle for natural numbers.

* Let $u$ be a subset of the image of $f$ over $t$ with $N+1$ elements.

* We apply the well-ordering principle (`num_WOP`) to the predicate $P(n) = \exists y \in u. y = f(n)$, which characterizes natural numbers that are preimages of elements in $u$.

* Since $u$ has $N+1 > 0$ elements, we can choose some $y \in u$ (using `SIZE_EXISTS`).

* Since $u \subseteq f[t]$, this $y$ must be $f(n)$ for some $n \in t$.

* By the well-ordering principle, there exists a minimal such $n$.

* We claim that $u = \{f(n)\} \cup (u \setminus \{f(n)\})$ where $n$ is minimal.
  
* For the second condition, consider any $z \in u \setminus \{f(n)\}$. Since $u \subseteq f[t]$, we know $z = f(k)$ for some $k \in t$.

* We need to show that $n < k$. Suppose, for contradiction, that $k \leq n$. 
  * If $k = n$, then $z = f(k) = f(n)$, contradicting $z \neq f(n)$.
  * If $k < n$, then $k$ would be a smaller preimage than $n$, contradicting the minimality of $n$.
  
* Therefore, $n < k$ must hold, which completes the proof.

### Mathematical insight
This lemma is essentially an application of the well-ordering principle to the preimage of a set under a function. It allows us to decompose a finite subset of an image set by isolating the element with the smallest preimage. This is a powerful structural result that enables induction on the size of such sets.

The result is particularly useful when working with images of functions from natural numbers, as it provides a canonical way to "peel off" elements one by one from a finite set, starting with the element that has the smallest preimage.

### Dependencies
- Theorems:
  - `SIZE_EXISTS`: If a set has size $N+1$, then there exists an element in that set
  - `num_WOP`: The well-ordering principle for natural numbers
  - Other standard HOL Light theorems about sets and logic

### Porting notes
When porting this proof:
- Ensure the target system has a well-ordering principle for natural numbers
- The proof relies on set operations like `DELETE` and `INSERT` that should be available in most systems
- The manipulations of existential quantifiers and conjunction are straightforward but require careful tracking of the context

---

## COLOURING_LEMMA

### COLOURING_LEMMA
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let COLOURING_LEMMA = prove(
  `!M col s. (INFINITE(s) /\ !n:A. n IN s ==> col(n) <= M) ==>
          ?c t. t SUBSET s /\ INFINITE(t) /\ !n:A. n IN t ==> (col(n) = c)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[LESS_EQ_0] THEN REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`0`; `s:A->bool`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    REPEAT STRIP_TAC THEN SUBGOAL_THEN
     `INFINITE { x:A | x IN s /\ (col x = SUC M) } \/
      INFINITE { x:A | x IN s /\ col x <= M}`
    DISJ_CASES_TAC THENL
     [UNDISCH_TAC `INFINITE(s:A->bool)` THEN
      REWRITE_TAC[INFINITE; GSYM DE_MORGAN_THM; GSYM FINITE_UNION] THEN
      CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
      DISCH_THEN(MATCH_MP_TAC o MATCH_MP SUBSET_FINITE) THEN
      REWRITE_TAC[SUBSET; IN_UNION] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[GSYM LESS_EQ_SUC] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`SUC M`; `{ x:A | x IN s /\ (col x = SUC M)}`] THEN
      ASM_REWRITE_TAC[SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `!n:A. n IN { x | x IN s /\ col x <= M } ==> col(n) <= M`
      MP_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
        DISCH_THEN(MATCH_ACCEPT_TAC o CONJUNCT2);
        FIRST_X_ASSUM(MP_TAC o SPECL [`col:A->num`;
                                        `{ x:A | x IN s /\ col x <= M}`]) THEN
        ASM_SIMP_TAC[] THEN
        MATCH_MP_TAC(TAUT `(c ==> d) ==> (b ==> c) ==> b ==> d`) THEN
        DISCH_THEN(X_CHOOSE_THEN `c:num` (X_CHOOSE_TAC `t:A->bool`)) THEN
        MAP_EVERY EXISTS_TAC [`c:num`; `t:A->bool`] THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `{ x:A | x IN s /\ col x <= M }` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]]]);;
```

### Informal statement
For any natural number $M$, a coloring function $\text{col}$ and a set $s$, if $s$ is infinite and for every element $n \in s$ we have $\text{col}(n) \leq M$, then there exists a color $c$ and an infinite subset $t \subseteq s$ such that $\text{col}(n) = c$ for all $n \in t$.

In formal terms:
$\forall M, \text{col}, s. \left(\text{INFINITE}(s) \wedge \forall n \in s. \text{col}(n) \leq M\right) \implies \exists c, t. \left(t \subseteq s \wedge \text{INFINITE}(t) \wedge \forall n \in t. \text{col}(n) = c\right)$

### Informal proof
The proof proceeds by induction on $M$ (the upper bound on the colors).

**Base case $M = 0$:**
- If $M = 0$, then $\text{col}(n) \leq 0$ means $\text{col}(n) = 0$ for all $n \in s$.
- We can take $c = 0$ and $t = s$, which satisfies all requirements.

**Inductive case $M = \text{SUC}(M')$:**
- Assume the result holds for $M'$.
- Consider the sets:
  * $A = \{x \in s \mid \text{col}(x) = \text{SUC}(M')\}$
  * $B = \{x \in s \mid \text{col}(x) \leq M'\}$
- Since $s = A \cup B$ and $s$ is infinite, at least one of $A$ or $B$ must be infinite.
- If $A$ is infinite, we can take $c = \text{SUC}(M')$ and $t = A$.
- If $B$ is infinite, we apply the induction hypothesis to $B$ with the color bound $M'$.
  * This gives us a color $c \leq M'$ and an infinite subset $t \subseteq B$ with all elements colored $c$.
  * Since $B \subseteq s$, we have $t \subseteq s$ by transitivity.

In all cases, we obtain an infinite monochromatic subset, completing the proof.

### Mathematical insight
This theorem establishes a fundamental property of infinite sets with finite colorings (or finite partitions). It essentially states that any infinite set that is colored with a finite number of colors must contain an infinite monochromatic subset.

This result is a weak form of Ramsey's theorem for one dimension (often called the "Infinite Pigeonhole Principle"). It forms a building block for more complex Ramsey-theoretic results.

The key insight is that when partitioning an infinite set into finitely many parts (colors), at least one of these parts must be infinite. This is a straightforward consequence of the fact that a finite union of finite sets is finite.

### Dependencies
- `SUBSET_FINITE`: If a set $s$ is finite, then any subset $t \subseteq s$ is also finite.
- `LESS_EQ_SUC`: For any $m$ and $n$, $m \leq \text{SUC}(n) \iff (m = \text{SUC}(n)) \lor (m \leq n)$.

### Porting notes
- The proof uses induction on the color bound $M$, which is a natural number.
- The handling of infinite sets may require special attention in other proof assistants.
- This proof relies on the fact that if an infinite set is partitioned into finitely many classes, at least one class must be infinite. This is a relatively standard result, but the specific formalization might differ between systems.

---

## COLOURING_THM

### Name of formal statement
COLOURING_THM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COLOURING_THM = prove(
  `!M col. (!n. col n <= M) ==>
           ?c s. INFINITE(s) /\ !n:num. n IN s ==> (col(n) = c)`,
  REPEAT STRIP_TAC THEN MP_TAC
   (ISPECL [`M:num`; `col:num->num`; `UNIV:num->bool`] COLOURING_LEMMA) THEN
  ASM_REWRITE_TAC[num_INFINITE] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num` (X_CHOOSE_TAC `t:num->bool`)) THEN
  MAP_EVERY EXISTS_TAC [`c:num`; `t:num->bool`] THEN ASM_REWRITE_TAC[]);;
```

### Informal statement
For any $M \in \mathbb{N}$ and coloring function $\text{col} : \mathbb{N} \to \mathbb{N}$, if $\text{col}(n) \leq M$ for all $n \in \mathbb{N}$ (i.e., the coloring uses at most $M+1$ colors), then there exists a color $c$ and an infinite set $s \subseteq \mathbb{N}$ such that all elements in $s$ have color $c$, i.e., $\forall n \in s, \text{col}(n) = c$.

### Informal proof
This theorem is a direct application of the more general `COLOURING_LEMMA` to the specific case where the domain is the set of natural numbers.

We apply `COLOURING_LEMMA` with the following instantiations:
- Set $M$ to our given upper bound
- Set $\text{col}$ to our given coloring function
- Set $s$ to the universal set of natural numbers `UNIV:num->bool`

The lemma states that for any $M$, coloring function $\text{col}$, and infinite set $s$ where $\text{col}(n) \leq M$ for all $n \in s$, there exists a color $c$ and an infinite subset $t \subseteq s$ such that all elements in $t$ have color $c$.

Since we know that:
- The set of natural numbers is infinite (proven by `num_INFINITE`)
- Our coloring satisfies $\text{col}(n) \leq M$ for all $n$ (our assumption)

We get precisely the result we need: there exists a color $c$ and an infinite set $t$ of natural numbers where every element has color $c$.

### Mathematical insight
This theorem is a simple instance of the infinite pigeonhole principle: if we have a finite number of colors (at most $M+1$ colors here) and infinitely many natural numbers, then at least one color must be used infinitely often.

The result is important in Ramsey theory, which studies the conditions under which order must appear in various mathematical structures. Here, the "order" is the existence of an infinite monochromatic subset of natural numbers.

This theorem has applications in areas such as combinatorics, set theory, and theoretical computer science, where it helps establish the existence of structured patterns within seemingly arbitrary colorings.

### Dependencies
#### Theorems
- `COLOURING_LEMMA`: A more general version of this theorem that works for any infinite set with elements having bounded color values
- `num_INFINITE`: States that the set of natural numbers is infinite

### Porting notes
When porting this theorem:
1. Ensure that the port system has a corresponding version of the infinite pigeonhole principle or the more general `COLOURING_LEMMA`
2. The proof is straightforward, mainly requiring the application of the lemma to the universal set of natural numbers
3. Make sure the port system has a way to represent the universal set and infinity concept

---

## RAMSEY_LEMMA1

### Name of formal statement
RAMSEY_LEMMA1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RAMSEY_LEMMA1 = prove(
 `(!C s. INFINITE(s:A->bool) /\
         (!t. t SUBSET s /\ t HAS_SIZE N ==> C(t) <= M)
         ==> ?t c. INFINITE(t) /\ t SUBSET s /\
                   (!u. u SUBSET t /\ u HAS_SIZE N ==> (C(u) = c)))
  ==> !C s. INFINITE(s:A->bool) /\
            (!t. t SUBSET s /\ t HAS_SIZE (SUC N) ==> C(t) <= M)
            ==> ?t c. INFINITE(t) /\ t SUBSET s /\ ~(((@) s) IN t) /\
                      (!u. u SUBSET t /\ u HAS_SIZE N
                           ==> (C(((@) s) INSERT u) = c))`,
  DISCH_THEN((THEN) (REPEAT STRIP_TAC) o MP_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `\u. C (((@) s :A) INSERT u):num`) THEN
  DISCH_THEN(MP_TAC o SPEC `s DELETE ((@)s:A)`) THEN BETA_TAC THEN
  ASM_REWRITE_TAC[INFINITE_DELETE] THEN
  W(C SUBGOAL_THEN (fun t ->REWRITE_TAC[t]) o
        funpow 2 (fst o dest_imp) o snd) THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `t SUBSET (s DELETE ((@) s :A))` THEN
      REWRITE_TAC[SUBSET; IN_INSERT; IN_DELETE; NOT_IN_EMPTY] THEN
      DISCH_TAC THEN GEN_TAC THEN DISCH_THEN DISJ_CASES_TAC THEN
      ASM_REWRITE_TAC[] THENL
       [MATCH_MP_TAC INFINITE_CHOOSE;
        FIRST_ASSUM(ANTE_RES_THEN ASSUME_TAC)] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SIZE_INSERT THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN UNDISCH_TAC `t SUBSET (s DELETE ((@) s :A))` THEN
      ASM_REWRITE_TAC[SUBSET; IN_DELETE] THEN
      DISCH_THEN(MP_TAC o SPEC `(@)s:A`) THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `t:A->bool` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `c:num` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`t:A->bool`; `c:num`] THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_DELETE]) THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET] THEN
      GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN(fun th -> REWRITE_TAC[th]));
      DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN REWRITE_TAC[]]]);;
```

### Informal statement
This theorem states a lemma for Ramsey's theorem. Specifically, it shows that:

If for all coloring functions $C$ and all infinite sets $s$, whenever all $N$-sized subsets of $s$ have color values bounded by $M$, there exists an infinite subset $t \subseteq s$ and a color $c$ such that all $N$-sized subsets of $t$ have the same color $c$,

Then for all coloring functions $C$ and all infinite sets $s$, whenever all $(N+1)$-sized subsets of $s$ have color values bounded by $M$, there exists an infinite subset $t \subseteq s$ such that $(@)s \notin t$ and a color $c$ such that for all $N$-sized subsets $u$ of $t$, the set $(@)s \cup u$ has the same color $c$.

Here, $(@)s$ refers to some arbitrarily chosen element from the infinite set $s$.

### Informal proof
The proof proceeds by using the inductive hypothesis and careful set manipulation:

1. We need to show that if the premise holds for $N$-sized sets, then it holds for $(N+1)$-sized sets.

2. First, we apply the premise to a new coloring function $C'(u) = C((@)s \cup u)$ and the set $s \setminus \{(@)s\}$.

3. We need to verify that the conditions required by the premise are satisfied:
   * $s \setminus \{(@)s\}$ is infinite (follows from `INFINITE_DELETE`)
   * For any $t \subset s \setminus \{(@)s\}$ with $|t| = N$:
     * We need to show that $(@)s \cup t \subset s$ and $|(@)s \cup t| = N+1$
     * $(@)s \in s$ by the choice of $(@)s$ (using `INFINITE_CHOOSE`)
     * $t \subset s \setminus \{(@)s\}$ implies $t \subset s$ and $(@)s \notin t$
     * Since $(@)s \notin t$ and $|t| = N$, we have $|(@)s \cup t| = N+1$ (using `SIZE_INSERT`)
     * Therefore, by the assumption, $C((@)s \cup t) \leq M$

4. Applying the premise, we get an infinite set $t \subset s \setminus \{(@)s\}$ and a color $c$ such that for all $u \subset t$ with $|u| = N$, $C((@)s \cup u) = c$.

5. Since $t \subset s \setminus \{(@)s\}$, we have $t \subset s$ and $(@)s \notin t$.

6. This gives us exactly what we need: an infinite subset $t \subset s$ with $(@)s \notin t$ and a color $c$ such that all $N$-sized subsets $u$ of $t$ have the same color $c$ when $(@)s$ is added.

### Mathematical insight
This lemma is a key stepping stone in the proof of Ramsey's theorem. It establishes a relationship between colorings of $N$-sized sets and $(N+1)$-sized sets, which allows for an inductive approach to proving Ramsey's theorem.

The lemma shows that if we have a uniformity result for sets of size $N$, we can extend it to sets of size $N+1$ by using a special element (here denoted by $(@)s$) as a fixed "anchor" and then finding uniformity in the remaining $N$ elements.

This technique is commonly used in Ramsey theory: fixing some elements and then finding regularity in the remaining structure. It's particularly useful because it allows us to build larger monochromatic structures from smaller ones.

### Dependencies
- `INFINITE_CHOOSE`: For infinite sets $s$, the arbitrarily chosen element $(@)s$ is in $s$
- `INFINITE_DELETE`: Removing a single element from an infinite set preserves infiniteness
- `SIZE_INSERT`: If $x \notin t$ and $|t| = n$, then $|x \cup t| = n+1$

### Porting notes
When porting this theorem:
1. Be careful with the choice function notation `(@)s`. In other systems, this might need to be replaced with a more explicit choice function or a function that selects an arbitrary element from a non-empty set.
2. The theorem relies on the existence of arbitrarily chosen elements from infinite sets, which may require different formulation in systems with different foundations.
3. The handling of set sizes and subset relationships might require different tactics in other proof assistants.

---

## RAMSEY_LEMMA2

### Name of formal statement
RAMSEY_LEMMA2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RAMSEY_LEMMA2 = prove(
 `(!C s. INFINITE(s:A->bool) /\
         (!t. t SUBSET s /\ t HAS_SIZE (SUC N) ==> C(t) <= M)
        ==> ?t c. INFINITE(t) /\ t SUBSET s /\ ~(((@) s) IN t) /\
                  (!u. u SUBSET t /\ u HAS_SIZE N
                       ==> (C(((@) s) INSERT u) = c)))
  ==> !C s. INFINITE(s:A->bool) /\
            (!t. t SUBSET s /\ t HAS_SIZE (SUC N) ==> C(t) <= M)
            ==> ?t x col. (!n. col n <= M) /\
                          (!n. (t n) SUBSET s) /\
                          (!n. t(SUC n) SUBSET (t n)) /\
                          (!n. ~((x n) IN (t n))) /\
                          (!n. x(SUC n) IN (t n)) /\
                          (!n. (x n) IN s) /\
                          (!n u. u SUBSET (t n) /\ u HAS_SIZE N
                                 ==> (C((x n) INSERT u) = col n))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:A->bool`; `\s (n:num). @t:A->bool. ?c:num.
      INFINITE(t) /\
      t SUBSET s /\
      ~(((@) s) IN t) /\
      !u. u SUBSET t /\ u HAS_SIZE N ==> (C(((@) s) INSERT u) = c)`]
    num_Axiom) THEN DISCH_THEN(MP_TAC o BETA_RULE o EXISTENCE) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->(A->bool)` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!n:num. (f n) SUBSET (s:A->bool) /\
    ?c. INFINITE(f(SUC n)) /\ f(SUC n) SUBSET (f n) /\
        ~(((@)(f n)) IN (f(SUC n))) /\
        !u. u SUBSET (f(SUC n)) /\ u HAS_SIZE N ==>
          (C(((@)(f n)) INSERT u) = c:num)`
  MP_TAC THENL
   [MATCH_MP_TAC num_INDUCTION THEN REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_REFL];
      FIRST_ASSUM(SUBST1_TAC o SPEC `0`) THEN CONV_TAC SELECT_CONV THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `f(n:num):A->bool` THEN
      CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
      FIRST_ASSUM(SUBST1_TAC o SPEC `SUC n`) THEN CONV_TAC SELECT_CONV THEN
      FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THEN
      TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) THEN REPEAT STRIP_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC SUBSET_TRANS THEN
        FIRST_ASSUM(fun th -> EXISTS_TAC(rand(concl th)) THEN
        CONJ_TAC THENL [FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC])) THEN
      MATCH_ACCEPT_TAC SUBSET_REFL];
    PURE_REWRITE_TAC[LEFT_EXISTS_AND_THM; RIGHT_EXISTS_AND_THM;
                     FORALL_AND_THM] THEN
    DISCH_THEN(REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_TAC `col:num->num` o CONV_RULE SKOLEM_CONV) THEN
    MAP_EVERY EXISTS_TAC
      [`\n:num. f(SUC n):A->bool`; `\n:num. (@)(f n):A`] THEN
    BETA_TAC THEN EXISTS_TAC `col:num->num` THEN CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP INFINITE_FINITE_CHOICE o SPEC `n:num`) THEN
      DISCH_THEN(CHOOSE_THEN MP_TAC o SPEC `N:num`) THEN
      DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
          ANTE_RES_THEN MP_TAC th) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM MATCH_MP_TAC THEN
      CONJ_TAC THENL
       [REWRITE_TAC[INSERT_SUBSET] THEN CONJ_TAC THENL
         [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
          EXISTS_TAC `n:num` THEN MATCH_MP_TAC INFINITE_CHOOSE THEN
          SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
          TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `f(SUC n):A->bool` THEN ASM_REWRITE_TAC[]];
        MATCH_MP_TAC SIZE_INSERT THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `!n:num. ~(((@)(f n):A) IN (f(SUC n)))` THEN
        DISCH_THEN(MP_TAC o SPEC `n:num`) THEN CONV_TAC CONTRAPOS_CONV THEN
        REWRITE_TAC[] THEN
        FIRST_ASSUM(MATCH_ACCEPT_TAC o REWRITE_RULE[SUBSET])];
      REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM MATCH_ACCEPT_TAC) THENL
       [GEN_TAC; INDUCT_TAC THENL
         [ASM_REWRITE_TAC[];
          FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
          EXISTS_TAC `SUC n`]] THEN
      MATCH_MP_TAC INFINITE_CHOOSE THEN ASM_REWRITE_TAC[]]]);;
```

### Informal statement

The theorem states:

If we assume that for any coloring function $C$ and any infinite set $s$ of type $A$, such that for all subsets $t \subseteq s$ of size $N+1$, we have $C(t) \leq M$, then there exists an infinite subset $t$ of $s$, an element not in $t$ (namely $(@)s$, the choice element of $s$), and a color $c$ such that for all subsets $u \subseteq t$ of size $N$, the color $C((@)s \cup u) = c$.

Then we can conclude that for any coloring function $C$ and any infinite set $s$ of type $A$ with the same property that for all subsets $t \subseteq s$ of size $N+1$, we have $C(t) \leq M$, there exist:
- A sequence of sets $(t_n)$ where each $t_n \subseteq s$ and $t_{n+1} \subseteq t_n$
- A sequence of elements $(x_n)$ where each $x_n \in s$, with $x_n \not\in t_n$ and $x_{n+1} \in t_n$
- A sequence of colors $(col_n)$ where each $col_n \leq M$

Such that for all $n$ and all subsets $u \subseteq t_n$ of size $N$, we have $C(x_n \cup u) = col_n$.

### Informal proof

This theorem builds a sequence of sets and elements with special coloring properties through the following approach:

- We begin by applying `num_Axiom` to construct a function $f$ from natural numbers to sets of type $A$.
- We then prove by induction that for every natural number $n$:
  * $f(n) \subseteq s$
  * There exists a color $c$ such that $f(n+1)$ is an infinite subset of $f(n)$
  * The choice element $(@)f(n)$ is not in $f(n+1)$
  * For all subsets $u \subseteq f(n+1)$ of size $N$, $C((@)f(n) \cup u) = c$

- For the induction base case, we show $f(0) \subseteq s$ by reflexivity of the subset relation.
- For the induction step, we use the premise and transitivity of the subset relation.

- We then define our sequences:
  * $t_n = f(n+1)$
  * $x_n = (@)f(n)$ (the choice element of $f(n)$)
  * $col_n$ = the color associated with $f(n+1)$

- To show that $col_n \leq M$, we apply `INFINITE_FINITE_CHOICE` to obtain a subset of $f(n+1)$ of size $N$, create a set of size $N+1$ by adding $x_n$, and use our assumption about $C$.

- The remaining properties follow from our inductive construction:
  * $t_n \subseteq s$ and $t_{n+1} \subseteq t_n$ by transitivity of subset relation
  * $x_n \not\in t_n$ from our inductive proof
  * $x_{n+1} \in t_n$ because $x_{n+1}$ is the choice element of $f(n+1)$ which is contained in $f(n)$
  * $x_n \in s$ follows from our subset relationships
  * The coloring property follows directly from our construction

### Mathematical insight

This lemma is a key component in proving Ramsey's theorem for infinite sets. It establishes the existence of an infinite "monochromatic" structure within an arbitrary colored infinite set.

The key insight is that we can construct a decreasing sequence of infinite sets $(t_n)$ and a sequence of elements $(x_n)$ such that:
1. Each element $x_n$ assigns a consistent color $col_n$ to all $N$-sized subsets of $t_n$ when added to them
2. The sequence maintains useful structural properties (each $x_{n+1}$ comes from $t_n$)

This construction is crucial for building the infinite monochromatic substructures that Ramsey's theorem guarantees. The theorem demonstrates how to extract, from any colored infinite set, a sequence with consistent coloring behavior when combined with subsets of a specific size.

### Dependencies

- **Theorems**:
  - `INFINITE_CHOOSE`: If $s$ is infinite, then the choice element $(@)s$ belongs to $s$
  - `SIZE_INSERT`: If $x \not\in t$ and $t$ has size $n$, then $x \cup t$ has size $n+1$
  - `INFINITE_FINITE_CHOICE`: For any natural number $n$ and infinite set $s$, there exists a subset $t$ of $s$ that has size $n$

### Porting notes

When porting this theorem:
1. Be careful with the choice operator $(@)$ - different systems may have different syntax for choice operators
2. The theorem uses nested choice operators for constructing the sequences, which might need to be handled differently in other proof assistants
3. The proof relies on the axiom of choice (through `num_Axiom` and choice operators), so the target system must support it
4. The inductive construction and sequence definition might need to be formalized differently depending on how the target system handles sequences and recursive definitions

---

## RAMSEY_LEMMA3

### RAMSEY_LEMMA3
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let RAMSEY_LEMMA3 = prove(
 `(!C s. INFINITE(s:A->bool) /\
             (!t. t SUBSET s /\ t HAS_SIZE (SUC N) ==> C(t) <= M)
             ==> ?t x col. (!n. col n <= M) /\
                           (!n. (t n) SUBSET s) /\
                           (!n. t(SUC n) SUBSET (t n)) /\
                           (!n. ~((x n) IN (t n))) /\
                           (!n. x(SUC n) IN (t n)) /\
                           (!n. (x n) IN s) /\
                           (!n u. u SUBSET (t n) /\ u HAS_SIZE N
                                  ==> (C((x n) INSERT u) = col n)))
  ==> !C s. INFINITE(s:A->bool) /\
            (!t. t SUBSET s /\ t HAS_SIZE (SUC N) ==> C(t) <= M)
            ==> ?t c. INFINITE(t) /\ t SUBSET s /\
                      (!u. u SUBSET t /\ u HAS_SIZE (SUC N) ==> (C(u) = c))`,
  DISCH_THEN((THEN) (REPEAT STRIP_TAC) o MP_TAC) THEN
  DISCH_THEN(MP_TAC o SPECL [`C:(A->bool)->num`; `s:A->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->(A->bool)` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num->A` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `col:num->num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`M:num`; `col:num->num`; `UNIV:num->bool`]
    COLOURING_LEMMA) THEN ASM_REWRITE_TAC[num_INFINITE] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (x:num->A) t`; `c:num`] THEN
  SUBGOAL_THEN `!m n. m <= n ==> (t n:A->bool) SUBSET (t m)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[LESS_EQ_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
    SPEC_TAC(`d:num`,`d:num`) THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; SUBSET_REFL] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `t(m + d):A->bool` THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!m n. m < n ==> (x n:A) IN (t m)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
    FIRST_ASSUM(MP_TAC o SPECL [`m:num`; `m + d`]) THEN
    REWRITE_TAC[LESS_EQ_ADD; SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[GSYM ADD1; ADD_CLAUSES]; ALL_TAC] THEN
  SUBGOAL_THEN `!m n. ((x:num->A) m = x n) <=> (m = n)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EQ_TAC THENL
     [REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
       (SPECL [`m:num`; `n:num`] LESS_LESS_CASES) THEN
      ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
      FIRST_ASSUM(ANTE_RES_THEN MP_TAC) THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(UNDISCH_TAC o check is_eq o concl) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN REFL_TAC]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `INFINITE(t:num->bool)` THEN
    MATCH_MP_TAC INFINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN GEN_TAC THEN
    DISCH_THEN(CHOOSE_THEN (SUBST1_TAC o CONJUNCT1)) THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
    DISCH_THEN(MP_TAC o MATCH_MP IMAGE_WOP_LEMMA) THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `v:A->bool` MP_TAC)) THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `c = (col:num->num) n` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `u SUBSET (IMAGE (x:num->A) t)` THEN
      REWRITE_TAC[SUBSET; IN_IMAGE] THEN
      DISCH_THEN(MP_TAC o SPEC `(x:num->A) n`) THEN
      ASM_REWRITE_TAC[IN_INSERT] THEN
      DISCH_THEN(CHOOSE_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET] THEN GEN_TAC THEN
        DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
        DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `v = u DELETE ((x:num->A) n)` SUBST1_TAC THENL
         [ASM_REWRITE_TAC[] THEN REWRITE_TAC[DELETE_INSERT] THEN
          REWRITE_TAC[EXTENSION; IN_DELETE;
            TAUT `(a <=> a /\ b) <=> a ==> b`] THEN
          GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
          DISCH_THEN SUBST1_TAC THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
          ASM_REWRITE_TAC[] THEN
          DISCH_THEN(CHOOSE_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
          ASM_REWRITE_TAC[LESS_REFL];
          MATCH_MP_TAC SIZE_DELETE THEN CONJ_TAC THENL
           [ASM_REWRITE_TAC[IN_INSERT]; FIRST_ASSUM MATCH_ACCEPT_TAC]]]]]);;
```

### Informal statement
This theorem establishes a key result in Ramsey theory. It states that:

Given natural numbers $N$ and $M$, if for every coloring function $C$ and infinite set $s$ of type $A$ where any subset $t \subset s$ of size $N+1$ has $C(t) \leq M$, there exists a sequence of sets $\{t_n\}$, a sequence of elements $\{x_n\}$, and a coloring sequence $\{col_n\}$ satisfying:
- For all $n$, $col_n \leq M$
- For all $n$, $t_n \subset s$
- For all $n$, $t_{n+1} \subset t_n$
- For all $n$, $x_n \notin t_n$
- For all $n$, $x_{n+1} \in t_n$
- For all $n$, $x_n \in s$
- For all $n$ and any subset $u \subset t_n$ of size $N$, $C(\{x_n\} \cup u) = col_n$

Then for any coloring function $C$ and infinite set $s$ where any subset $t \subset s$ of size $N+1$ has $C(t) \leq M$, there exists an infinite subset $t \subset s$ and a color $c$ such that any subset $u \subset t$ of size $N+1$ has $C(u) = c$.

### Informal proof
This theorem is proved using the following steps:

1. We start by assuming the hypothesis and apply it to the given coloring function $C$ and set $s$.
   
2. This gives us sequences $\{t_n\}$, $\{x_n\}$, and $\{col_n\}$ with the stated properties.

3. Apply the `COLOURING_LEMMA` to the coloring function $col$ on the universal set of numbers. Since $col_n \leq M$ for all $n$, there exists a color $c$ and an infinite subset of indices $t \subset \mathbb{N}$ such that $col_n = c$ for all $n \in t$.

4. Define our desired set as $\{x_n : n \in t\}$ (the image of $t$ under the function $x$).

5. We prove key properties about the sequences $\{t_n\}$ and $\{x_n\}$:
   - If $m \leq n$ then $t_n \subset t_m$ (by induction on the difference)
   - If $m < n$ then $x_n \in t_m$ (from the properties of the sequence)
   - The function $x$ is injective: $x_m = x_n$ if and only if $m = n$

6. We then prove the three required properties of our constructed set:
   - The set $\{x_n : n \in t\}$ is infinite because $t$ is infinite and $x$ is injective.
   - This set is a subset of $s$ because each $x_n \in s$.
   - For any subset $u$ of $\{x_n : n \in t\}$ of size $N+1$, we use the Well-Ordering Principle to find the minimum index $n \in t$ such that $x_n \in u$. This gives us $u = \{x_n\} \cup v$ for some set $v$ where each element in $v$ is $x_m$ for some $m > n$. Since $m > n$, we have $x_m \in t_n$, so $v \subset t_n$. Also, $v$ has size $N$ since $u$ has size $N+1$. Therefore, $C(u) = C(\{x_n\} \cup v) = col_n = c$.

Thus, we have found an infinite subset $t \subset s$ and a color $c$ such that any subset of $t$ of size $N+1$ has color $c$.

### Mathematical insight
This theorem is a key step in proving Ramsey's theorem for infinite sets. It establishes the existence of an infinite monochromatic subset - that is, an infinite subset where all subsets of a certain size have the same color.

The proof uses standard techniques from infinitary combinatorics:
1. Finding sequences with desirable properties
2. Using an infinite pigeonhole principle (via the `COLOURING_LEMMA`) to extract an infinite subsequence with constant coloring
3. Applying the Well-Ordering Principle to identify the minimum element in a subset

This result is crucial in Ramsey theory, which studies the conditions under which order must emerge from disorder. It shows that even in arbitrary colorings of an infinite set, we can always find large structured subsets.

### Dependencies
- Theorems:
  - `LESS_LESS_CASES`: For any two natural numbers $m$ and $n$, either $m = n$ or $m < n$ or $n < m$
  - `SIZE_DELETE`: If $x \in t$ and $t$ has size $n+1$, then $t \setminus \{x\}$ has size $n$
  - `IMAGE_WOP_LEMMA`: A lemma using the Well-Ordering Principle on the image of a function
  - `COLOURING_LEMMA`: If $s$ is infinite and $col(n) \leq M$ for all $n \in s$, then there exists a color $c$ and an infinite subset $t \subset s$ such that $col(n) = c$ for all $n \in t$

### Porting notes
When porting this theorem:
1. Ensure that the target system has a suitable representation of infinity and infinite sets
2. The proof relies on sequence construction and well-ordering principles, which may require different approaches in constructive systems
3. The theorem uses higher-order functions (colorings on sets), so ensure the target system can handle this level of abstraction
4. The proof technique of creating sequences with specific properties and then extracting a subsequence is common in Ramsey theory but may need adaptation based on the target system's library support

---

## RAMSEY

### RAMSEY
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let RAMSEY = prove(
  `!M N C s.
        INFINITE(s:A->bool) /\
        (!t. t SUBSET s /\ t HAS_SIZE N ==> C(t) <= M)
        ==> ?t c. INFINITE(t) /\ t SUBSET s /\
                  (!u. u SUBSET t /\ u HAS_SIZE N ==> (C(u) = c))`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`s:A->bool`; `(C:(A->bool)->num) {}`] THEN
    ASM_REWRITE_TAC[HAS_SIZE_0] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL];
    MAP_EVERY MATCH_MP_TAC [RAMSEY_LEMMA3; RAMSEY_LEMMA2; RAMSEY_LEMMA1] THEN
    POP_ASSUM MATCH_ACCEPT_TAC]);;
```

### Informal statement
The theorem states Ramsey's theorem for hypergraphs. For all natural numbers $M$ and $N$, a coloring function $C$ that assigns colors to $N$-element subsets of an infinite set $s$ with at most $M$ colors, there exists an infinite subset $t$ of $s$ and a color $c$ such that all $N$-element subsets of $t$ are assigned the same color $c$.

More formally:
For all $M, N \in \mathbb{N}$ and for any function $C: \binom{s}{N} \rightarrow \{0,1,\ldots,M\}$ where $s$ is an infinite set, there exists an infinite subset $t \subseteq s$ and a color $c \in \{0,1,\ldots,M\}$ such that for all $N$-element subsets $u \subseteq t$, $C(u) = c$.

### Informal proof
The proof proceeds by induction on $N$.

* **Base case** ($N = 0$):
  When $N = 0$, the only $N$-element subset is the empty set $\{\}$. We choose $t = s$ and $c = C(\{\})$. Since $s$ is infinite, $t$ is infinite, and trivially $t \subseteq s$. For any $0$-element subset $u$ of $t$, we have $u = \{\}$, so $C(u) = C(\{\}) = c$.

* **Inductive step** (assume true for $N$, prove for $N+1$):
  The proof for the inductive step is built upon three lemmas:
  1. `RAMSEY_LEMMA1`: Shows that if the Ramsey property holds for $N$-element sets, then for any function coloring $(N+1)$-element sets, there exists an infinite subset where all $N$-element sets containing a specific element have the same color.
  
  2. `RAMSEY_LEMMA2`: Extends this to construct sequences of nested infinite sets with consistent coloring properties.
  
  3. `RAMSEY_LEMMA3`: Finally proves that from such sequences, we can extract an infinite monochromatic subset for $(N+1)$-element sets.
  
  These three lemmas are applied in sequence, completing the induction.

### Mathematical insight
Ramsey's theorem is a fundamental result in combinatorics that guarantees the existence of order in sufficiently large structures, no matter how they are colored. This theorem presents the infinite version of Ramsey's theorem for hypergraphs.

The theorem is important because it shows that complete disorder is impossible - no matter how we try to color a large enough structure, we will always find monochromatic substructures of the desired size. This has profound implications in many areas of mathematics, including graph theory, number theory, and logic.

In set theory terms, the theorem states that disorder cannot be maintained indefinitely - any coloring of an infinite set ultimately contains an infinite monochromatic subset.

### Dependencies
- `RAMSEY_LEMMA1`: First lemma used in the inductive step
- `RAMSEY_LEMMA2`: Second lemma used in the inductive step 
- `RAMSEY_LEMMA3`: Third lemma used in the inductive step
- Standard set-theoretic operations and infiniteness properties

### Porting notes
When porting this theorem:
- Ensure that the proper notion of set size (cardinality) is used
- The proof structure relies heavily on the three lemmas which should be ported first
- The notation `HAS_SIZE N` means a set has exactly N elements
- In most systems, you may need to explicitly define what it means for a function to color N-element sets

---

