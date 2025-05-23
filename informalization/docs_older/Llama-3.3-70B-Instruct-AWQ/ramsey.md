# ramsey.ml

## Overview

Number of statements: 186

The `ramsey.ml` file formalizes Infinite Ramsey's theorem, porting a proof from HOL88 to HOL Light. It provides a foundation for exploring Ramsey theory, a fundamental concept in combinatorics. The file contains definitions, theorems, and constructions related to Infinite Ramsey's theorem, serving as a self-contained module within the larger library. Its purpose is to establish a formal proof of this theorem in HOL Light.

## is_neg_imp

### Name of formal statement
is_neg_imp

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let is_neg_imp tm = is_neg tm || is_imp tm;;
```

### Informal statement
The `is_neg_imp` function takes a term `tm` and returns true if `tm` is either a negation or an implication, and false otherwise.

### Informal sketch
* The definition checks two conditions for the input term `tm`: 
  * Whether `tm` is a negation, as determined by the `is_neg` function
  * Whether `tm` is an implication, as determined by the `is_imp` function
* The function uses a logical disjunction (`||`) to combine these conditions, returning true if either condition is met

### Mathematical insight
This definition is a simple predicate that identifies terms in a logical expression that are either negations or implications. It is likely used in a larger context to analyze or manipulate logical formulas, possibly as part of a proof assistant or automated reasoning system.

### Dependencies
* `is_neg`
* `is_imp`

### Porting notes
When translating this definition into another proof assistant, ensure that the equivalents of `is_neg` and `is_imp` are correctly identified and used. The logical disjunction operator (`||`) should be translated to its equivalent in the target system. Note that the specific implementation of `is_neg` and `is_imp` may vary between systems, so their definitions should also be ported or reimplemented accordingly.

---

## dest_neg_imp

### Name of formal statement
dest_neg_imp

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let dest_neg_imp tm =
  try dest_imp tm with Failure _ ->
  try (dest_neg tm,mk_const("F",[]))
  with Failure _ -> failwith "dest_neg_imp"
```

### Informal statement
The function `dest_neg_imp` takes a term `tm` and attempts to decompose it into its components. It first tries to apply `dest_imp` to `tm`. If this fails, it attempts to apply `dest_neg` to `tm` and pairs the result with a constant `F` of empty type. If both attempts fail, it raises an exception with the message "dest_neg_imp".

### Informal sketch
* The function `dest_neg_imp` is defined to handle terms that may be implications or negations.
* It first attempts to apply `dest_imp` to decompose the term into its implication components.
* If `dest_imp` fails, it attempts to apply `dest_neg` to decompose the term into its negation components, pairing the result with a constant `F`.
* The use of `try` and `with Failure _` indicates that the function is designed to gracefully handle and recover from failures of `dest_imp` and `dest_neg`.
* The `failwith "dest_neg_imp"` clause provides a specific error message if both decomposition attempts fail.

### Mathematical insight
The `dest_neg_imp` function appears to be part of a larger system for decomposing logical terms into their constituent parts. It is designed to handle terms that are either implications or negations, providing a way to break down these terms into more basic components. This is likely useful in a proof assistant or automated reasoning system, where being able to manipulate and analyze the structure of logical terms is essential.

### Dependencies
* `dest_imp`
* `dest_neg`
* `mk_const`

### Porting notes
When porting this definition to another proof assistant, care should be taken to ensure that the equivalents of `dest_imp`, `dest_neg`, and `mk_const` are properly defined and accessible. Additionally, the error handling mechanism (`try`/`with Failure _`) may need to be adapted to the target system's exception handling model. The overall structure of the function, however, should be relatively straightforward to translate, as it involves basic term manipulation and decomposition.

---

## PROVE

### Name of formal statement
PROVE

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let PROVE = prove;;
```

### Informal statement
The `PROVE` definition is assigned the value of the `prove` function.

### Informal sketch
* The definition of `PROVE` is a straightforward assignment, where `PROVE` is set to be equal to the result of the `prove` function.
* The `prove` function is not defined in this snippet, so its exact behavior is unknown, but it is being used to initialize the `PROVE` definition.

### Mathematical insight
The `PROVE` definition appears to be a simple assignment, but its significance lies in its potential use as a building block for more complex proofs or definitions. The `prove` function likely plays a crucial role in the broader theory, and understanding its behavior is essential to grasping the context of this definition.

### Dependencies
* `prove`

### Porting notes
When translating this definition to other proof assistants, ensure that the equivalent of the `prove` function is properly defined and accessible. Note that different proof assistants may handle function assignments and definitions differently, so careful attention to the target system's syntax and semantics is necessary.

---

## prove_thm((s:string),g,t)

### Name of formal statement
prove_thm

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let prove_thm((s:string),g,t) = prove(g,t);;
```

### Informal statement
The function `prove_thm` takes a string `s`, and two arguments `g` and `t`, and applies the `prove` function to `g` and `t`.

### Informal sketch
* The `prove_thm` function is defined as a sequence of applications of the `prove` function to its arguments `g` and `t`, without any explicit dependency on the string `s`.
* The `prove` function is presumably a key component in the proof assistant, responsible for establishing the validity of a statement.
* The definition of `prove_thm` appears to be a straightforward application of `prove`, suggesting that the main logical stage is the execution of `prove` with the given arguments.

### Mathematical insight
The `prove_thm` function seems to be a simple wrapper around the `prove` function, which is likely a core component of the proof assistant. This function may be used to provide a layer of abstraction or to facilitate the application of the `prove` function in specific contexts.

### Dependencies
* `prove`

### Porting notes
When porting this definition to another proof assistant, it is essential to identify the equivalent of the `prove` function and ensure that it is correctly applied to the arguments `g` and `t`. The string `s` does not appear to be used in the definition, so its role and purpose should be clarified to ensure correct translation. Additionally, the `prove` function's behavior and any relevant tactics or automation should be carefully examined to guarantee a faithful translation.

---

## (CONV_OF_RCONV:

### Name of formal statement
CONV_OF_RCONV

### Type of the formal statement
new_definition

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
The `CONV_OF_RCONV` function takes a conversion `conv` as input and returns a new conversion. It first defines a recursive function `get_bv` that takes a term `tm` and returns a bound variable. If `tm` is an abstraction, it returns the bound variable of the abstraction. If `tm` is a combination, it tries to recursively call `get_bv` on the argument of the combination, and if that fails, it calls `get_bv` on the function part of the combination. If `tm` is neither an abstraction nor a combination, it raises an exception. The main function then applies the input conversion `conv` to the input term `tm` to obtain a theorem `th1`. It then applies the `ONCE_DEPTH_CONV` conversion with the `GEN_ALPHA_CONV` conversion for the bound variable `v` obtained by `get_bv` to the conclusion of `th1`, resulting in a new theorem `th2`. Finally, it composes `th1` and `th2` using the `TRANS` tactic.

### Informal sketch
* Define a recursive function `get_bv` to extract a bound variable from a term
* Apply the input conversion `conv` to the input term `tm`
* Apply `ONCE_DEPTH_CONV` with `GEN_ALPHA_CONV` for the extracted bound variable to the conclusion of the resulting theorem
* Compose the two theorems using `TRANS`
The key steps involve extracting a bound variable, applying a conversion, and then composing the results of two conversions.

### Mathematical insight
This definition is part of the quantifier movement conversions, which are essential in manipulating and simplifying expressions involving quantifiers in formal proofs. The `CONV_OF_RCONV` function specifically helps in applying conversions to terms while handling bound variables appropriately, which is crucial for maintaining the correctness and soundness of the proofs.

### Dependencies
* `is_abs`
* `is_comb`
* `bndvar`
* `rand`
* `rator`
* `GEN_ALPHA_CONV`
* `ONCE_DEPTH_CONV`
* `TRANS`

### Porting notes
When porting this definition to another proof assistant, special attention should be paid to how bound variables are handled and how conversions are composed. The `get_bv` function's recursive nature and its handling of different term types (abstractions and combinations) should be carefully translated. Additionally, understanding the equivalents of `ONCE_DEPTH_CONV`, `GEN_ALPHA_CONV`, and `TRANS` in the target system is crucial for a correct port.

---

## (CONV_OF_THM:

### Name of formal statement
CONV_OF_THM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let (CONV_OF_THM: thm -> conv) =
  CONV_OF_RCONV o REWR_CONV;;
```

### Informal statement
The function `CONV_OF_THM` takes a theorem as input and returns a conversion, which is defined as the composition of `CONV_OF_RCONV` and `REWR_CONV`.

### Informal sketch
* The definition of `CONV_OF_THM` relies on the `o` operator for function composition.
* `CONV_OF_RCONV` and `REWR_CONV` are applied sequentially to the input theorem.
* The `CONV_OF_THM` function essentially transforms a theorem into a conversion using rewriting rules.

### Mathematical insight
This definition provides a way to convert theorems into conversions, which is useful for applying rewriting rules in a proof assistant. The composition of `CONV_OF_RCONV` and `REWR_CONV` enables the application of rewriting conversions to theorems, facilitating proof construction.

### Dependencies
* `CONV_OF_RCONV`
* `REWR_CONV`

### Porting notes
When translating this definition to other proof assistants, ensure that the equivalent of function composition (`o`) is used correctly. Additionally, identify the corresponding concepts for `CONV_OF_RCONV` and `REWR_CONV` in the target system, as they may have different names or implementations.

---

## (X_FUN_EQ_CONV:term->conv)

### Name of formal statement
X_FUN_EQ_CONV

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let (X_FUN_EQ_CONV:term->conv) =
  fun v -> (REWR_CONV FUN_EQ_THM) THENC GEN_ALPHA_CONV v;;
```

### Informal statement
The `X_FUN_EQ_CONV` is a conversion function that takes a term `v` and applies two conversions sequentially: first, it applies the `REWR_CONV` conversion using the `FUN_EQ_THM` theorem, and then it applies the `GEN_ALPHA_CONV` conversion to the result, with `v` as an argument.

### Informal sketch
* The definition of `X_FUN_EQ_CONV` involves a sequential composition of two conversions: 
  * `REWR_CONV FUN_EQ_THM` applies a rewriting conversion based on the `FUN_EQ_THM` theorem, which likely establishes an equivalence between different representations of functions.
  * `GEN_ALPHA_CONV v` applies a conversion that generalizes or alpha-converts the result, taking into account the term `v`.
* The purpose of `X_FUN_EQ_CONV` appears to be simplifying or normalizing terms involving function equalities, leveraging the `FUN_EQ_THM` theorem and alpha-conversion.

### Mathematical insight
The `X_FUN_EQ_CONV` definition is important because it provides a systematic way to simplify or prove statements involving function equalities, which are fundamental in mathematical reasoning. By combining rewriting with alpha-conversion, it enables the manipulation of terms in a way that respects the underlying mathematical structure of functions.

### Dependencies
* Theorems:
  * `FUN_EQ_THM`
* Conversions:
  * `REWR_CONV`
  * `GEN_ALPHA_CONV`

### Porting notes
When translating `X_FUN_EQ_CONV` into another proof assistant, pay special attention to how function equality and alpha-conversion are handled. The `REWR_CONV` and `GEN_ALPHA_CONV` conversions might have direct analogs, but their behavior and application could differ. Additionally, the `FUN_EQ_THM` theorem must be translated or proven in the target system to support the rewriting step. Consider the specific mechanisms for term manipulation and conversion in the target proof assistant to ensure a faithful translation of `X_FUN_EQ_CONV`.

---

## (FUN_EQ_CONV:conv)

### Name of formal statement
FUN_EQ_CONV

### Type of the formal statement
Theorem/Conversion rule

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
The `FUN_EQ_CONV` conversion rule takes a term `tm` and checks if its type is a function type. If it is, `FUN_EQ_CONV` extracts the variable name from the domain type of the function, creates a fresh variable `x` of the same type, and then applies the `X_FUN_EQ_CONV` conversion to `x` and `tm`. If the type of `tm` is not a function type, it fails.

### Informal sketch
* Check if the type of the input term `tm` is a function type by examining the operator `op` of its type.
* If the type is a function type, extract the type of the domain `ty1` and determine a suitable variable name `varnm` based on whether `ty1` is a variable type or not.
* Create a fresh variable `x` with the determined name and type `ty1`, ensuring it does not clash with existing variables in `tm`.
* Apply the `X_FUN_EQ_CONV` conversion rule to `x` and `tm` to perform the actual conversion.
* If the type of `tm` is not a function type, the conversion fails, indicating it is not applicable.

### Mathematical insight
The `FUN_EQ_CONV` rule appears to be part of a system for converting or simplifying terms involving functions, particularly in the context of formalizing mathematical proofs. It ensures that function equations are handled consistently and can be transformed into appropriate forms for further reasoning. This kind of conversion is crucial in proof assistants for managing and simplifying expressions, especially when dealing with functions and their properties.

### Dependencies
* `frees`
* `dest_type`
* `type_of`
* `lhs`
* `is_vartype`
* `explode`
* `fst`
* `dest_type`
* `variant`
* `mk_var`
* `X_FUN_EQ_CONV`

### Porting notes
When porting `FUN_EQ_CONV` to another proof assistant like Lean, Coq, or Isabelle, pay close attention to how each system handles binders, variable naming, and type checking. The main challenge will be translating the `X_FUN_EQ_CONV` rule and ensuring that the variable creation and type manipulation logic is correctly implemented in the target system. Additionally, consider the differences in how function types and terms are represented and manipulated in the target proof assistant.

---

## (SINGLE_DEPTH_CONV:conv->conv)

### Name of formal statement
SINGLE_DEPTH_CONV

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let (SINGLE_DEPTH_CONV:conv->conv) =
  let rec SINGLE_DEPTH_CONV conv tm =
    try conv tm with Failure _ ->
    (SUB_CONV (SINGLE_DEPTH_CONV conv) THENC (TRY_CONV conv)) tm in
  SINGLE_DEPTH_CONV;;
```

### Informal statement
The `SINGLE_DEPTH_CONV` is a function that takes a conversion `conv` and returns a new conversion. This new conversion applies `conv` to a term `tm`. If `conv` fails, it then applies a substitution conversion using `SINGLE_DEPTH_CONV conv` followed by `TRY_CONV conv` to `tm`.

### Informal sketch
* The definition of `SINGLE_DEPTH_CONV` is recursive, indicating a self-referential application of conversions.
* The function first attempts to apply the input conversion `conv` to the term `tm`.
* Upon failure of `conv`, it employs a fallback strategy using `SUB_CONV` and `THENC` to combine `SINGLE_DEPTH_CONV conv` with `TRY_CONV conv`, effectively trying an alternative conversion path on `tm`.
* Key HOL Light terms involved include `SUB_CONV`, `THENC`, and `TRY_CONV`, which are used to compose and apply conversions conditionally.

### Mathematical insight
The `SINGLE_DEPTH_CONV` definition appears to implement a strategy for applying conversions in a context where direct application might fail, providing a layered approach to conversion that can handle more complex terms or situations by combining different conversion tactics.

### Dependencies
* `SUB_CONV`
* `THENC`
* `TRY_CONV`

### Porting notes
When translating `SINGLE_DEPTH_CONV` into another proof assistant, pay close attention to how recursive functions and conditional application of tactics are handled. The use of `try`-`with` for handling failures may need to be adapted, as different systems may have distinct mechanisms for dealing with tactic failures. Additionally, the equivalents of `SUB_CONV`, `THENC`, and `TRY_CONV` must be identified in the target system to ensure the conversion strategy is properly replicated.

---

## (SKOLEM_CONV:conv)

### Name of formal statement
SKOLEM_CONV

### Type of the formal statement
Theorem/Conv

### Formal Content
```ocaml
let SKOLEM_CONV =
  SINGLE_DEPTH_CONV (REWR_CONV SKOLEM_THM);;
```

### Informal statement
This defines a conversion `SKOLEM_CONV` that applies a single-depth conversion using the `SKOLEM_THM` theorem for rewriting.

### Informal sketch
* The `SKOLEM_CONV` conversion is defined using `SINGLE_DEPTH_CONV`, which applies a conversion to the top-level of a term.
* The conversion used is `REWR_CONV SKOLEM_THM`, indicating that it rewrites using the `SKOLEM_THM` theorem.
* The key logical stage involves applying `SKOLEM_THM` as a rewrite rule to transform terms.

### Mathematical insight
The Skolem theorem is a fundamental result in mathematical logic that allows existential quantifiers to be eliminated in favor of function symbols (Skolem functions) that witness the existence. This conversion likely facilitates the application of Skolem's theorem in proofs, enabling the elimination of existential quantifiers by introducing appropriate Skolem functions.

### Dependencies
#### Theorems
* `SKOLEM_THM`

### Porting notes
When porting `SKOLEM_CONV` to another proof assistant, ensure that an equivalent of `SINGLE_DEPTH_CONV` and `REWR_CONV` is used, and that `SKOLEM_THM` or its equivalent is defined and accessible. Note that different systems may handle conversions and rewrites differently, so the exact implementation may vary. Additionally, the representation of Skolem's theorem and its application might require adjustments based on the target system's handling of quantifiers and Skolemization.

---

## (X_SKOLEM_CONV:term->conv)

### Name of formal statement
X_SKOLEM_CONV

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let X_SKOLEM_CONV = fun v -> SKOLEM_CONV THENC GEN_ALPHA_CONV v;;
```

### Informal statement
The `X_SKOLEM_CONV` is a conversion function that takes a term `v` and applies the `SKOLEM_CONV` conversion followed by the `GEN_ALPHA_CONV` conversion to `v`.

### Informal sketch
* The definition involves a sequence of conversions starting with `SKOLEM_CONV`, which is typically used for Skolemization, a process of eliminating existential quantifiers by introducing new function symbols.
* This is then followed by `GEN_ALPHA_CONV`, which likely performs a generalization or renaming of bound variables to ensure alpha-equivalence, a crucial step for maintaining the integrity of the logical structure under variable changes.
* The purpose is to provide a conversion that can handle both the elimination of existential quantifiers and the renaming of variables in a term, potentially preparing it for further manipulation or proof steps.

### Mathematical insight
The `X_SKOLEM_CONV` definition is important because it combines two fundamental operations in formal proof manipulation: Skolemization and variable generalization. Skolemization is crucial for reducing existential quantifiers to function symbols, which can simplify proofs by eliminating quantifiers, while generalization over alpha-equivalence ensures that the resulting terms are properly normalized and can be compared or manipulated without concern for variable naming.

### Dependencies
- `SKOLEM_CONV`
- `GEN_ALPHA_CONV`
- `THENC`

### Porting notes
When porting this definition to another proof assistant like Lean, Coq, or Isabelle, pay special attention to how each system handles Skolemization and alpha-equivalence. Specifically, the equivalent of `SKOLEM_CONV` and `GEN_ALPHA_CONV` needs to be identified in the target system. Additionally, the sequential application of conversions (indicated by `THENC`) should be translated into the appropriate construct in the target system, which might involve tacticals or monadic constructs for composing proof transformations.

---

## EXISTS_UNIQUE_CONV

### Name of formal statement
EXISTS_UNIQUE_CONV

### Type of the formal statement
Theorem

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
This theorem states that there exists a unique conversion `EXISTS_UNIQUE_CONV` that takes a term `tm` and performs a series of transformations to yield a new term. The conversion first applies `REWR_CONV` with `EXISTS_UNIQUE_THM` to `tm`, then extracts the right-hand side of the resulting theorem `th1`. It then computes the free variables `vars` of the resulting term `tm1`, and generates a variant `v` of these variables. A new variant `v'` is generated from `v` and `vars`. The conversion then applies a series of transformations to `tm1` using `LAND_CONV`, `GEN_ALPHA_CONV`, `RAND_CONV`, `BINDER_CONV`, and `GEN_ALPHA_CONV` again, with `v` and `v'` as parameters, to yield a new theorem `th2`. Finally, the conversion combines `th1` and `th2` using `TRANS`.

### Informal sketch
* The proof starts by applying `REWR_CONV` with `EXISTS_UNIQUE_THM` to the input term `tm`, which yields a theorem `th1`.
* It then extracts the right-hand side of `th1` as `tm1` and computes the free variables `vars` of `tm1`.
* The proof generates a variant `v` of `vars` and another variant `v'` from `v` and `vars`.
* The main conversion applies a series of transformations to `tm1` using:
  + `LAND_CONV` with `GEN_ALPHA_CONV v`
  + `RAND_CONV` with `BINDER_CONV` and `GEN_ALPHA_CONV v'` and `GEN_ALPHA_CONV v`
* These transformations yield a new theorem `th2`.
* Finally, the conversion combines `th1` and `th2` using `TRANS` to produce the final result.

### Mathematical insight
The `EXISTS_UNIQUE_CONV` theorem provides a way to transform a term `tm` into a new form that asserts the existence and uniqueness of a witness for a given predicate. This is a fundamental concept in formal logic, as it allows for the expression of properties that require the existence of unique objects. The theorem is likely used in various proofs that involve existential quantification and uniqueness properties.

### Dependencies
* Theorems:
  + `EXISTS_UNIQUE_THM`
* Definitions:
  + `REWR_CONV`
  + `LAND_CONV`
  + `GEN_ALPHA_CONV`
  + `RAND_CONV`
  + `BINDER_CONV`
  + `TRANS`

### Porting notes
When porting this theorem to other proof assistants, special attention should be paid to the handling of binders and alpha-conversion, as these are critical components of the `EXISTS_UNIQUE_CONV` theorem. The `GEN_ALPHA_CONV` and `BINDER_CONV` tactics may need to be reimplemented or replaced with equivalent constructs in the target proof assistant. Additionally, the `REWR_CONV` and `TRANS` tactics may require careful handling to ensure that the resulting proof is sound and complete.

---

## NOT_FORALL_CONV

### Name of formal statement
NOT_FORALL_CONV

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let NOT_FORALL_CONV = CONV_OF_THM NOT_FORALL_THM;;
```

### Informal statement
The definition `NOT_FORALL_CONV` is the conversion of the theorem `NOT_FORALL_THM` into a conversion.

### Informal sketch
* The definition `NOT_FORALL_CONV` is constructed by applying the `CONV_OF_THM` function to the theorem `NOT_FORALL_THM`.
* This involves translating the theorem into a conversion, which can be used to transform terms in a proof.
* The `CONV_OF_THM` function is used to convert a theorem into a conversion, which can then be applied to terms in a proof.

### Mathematical insight
The definition `NOT_FORALL_CONV` is likely used to handle the negation of universal quantification in a formal proof system. The `NOT_FORALL_THM` theorem probably states a property about the negation of universal quantification, and the `CONV_OF_THM` function is used to convert this theorem into a conversion that can be applied to terms in a proof. This conversion can then be used to transform terms involving universal quantification into equivalent terms involving existential quantification.

### Dependencies
* Theorems:
	+ `NOT_FORALL_THM`
* Definitions:
	+ `CONV_OF_THM`

### Porting notes
When porting this definition to another proof assistant, care should be taken to ensure that the equivalent of the `CONV_OF_THM` function is used to convert the `NOT_FORALL_THM` theorem into a conversion. The ported definition should also handle the negation of universal quantification correctly, taking into account any differences in the handling of binders or automation between the source and target proof assistants.

---

## NOT_EXISTS_CONV

### Name of formal statement
NOT_EXISTS_CONV

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let NOT_EXISTS_CONV = CONV_OF_THM NOT_EXISTS_THM;;
```

### Informal statement
The `NOT_EXISTS_CONV` is defined as the conversion of the theorem `NOT_EXISTS_THM` to a conversion rule.

### Informal sketch
* The definition involves applying the `CONV_OF_THM` function to `NOT_EXISTS_THM`, which implies that `NOT_EXISTS_THM` is a previously established theorem.
* The `CONV_OF_THM` function is used to convert a theorem into a conversion rule, which can be used to transform terms in a proof.
* The key logical stage here is the application of `CONV_OF_THM` to `NOT_EXISTS_THM`, which suggests that `NOT_EXISTS_THM` has a specific form that makes it suitable for conversion into a rule for term transformation.

### Mathematical insight
The `NOT_EXISTS_CONV` definition is important because it enables the use of the `NOT_EXISTS_THM` theorem as a conversion rule in proofs, potentially simplifying or automating certain proof steps. The `NOT_EXISTS_THM` theorem likely deals with the negation of existential quantification, and converting it into a rule allows for more flexible application in various proof contexts.

### Dependencies
* Theorems: `NOT_EXISTS_THM`
* Definitions: `CONV_OF_THM`

### Porting notes
When porting `NOT_EXISTS_CONV` to another proof assistant, ensure that an equivalent of `CONV_OF_THM` exists or can be defined, and that `NOT_EXISTS_THM` or its equivalent has been established. The process may involve understanding how the target system handles theorem conversions and term transformations, potentially requiring adjustments to replicate the exact functionality of `CONV_OF_THM` and the role of `NOT_EXISTS_THM`.

---

## RIGHT_IMP_EXISTS_CONV

### Name of formal statement
RIGHT_IMP_EXISTS_CONV

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let RIGHT_IMP_EXISTS_CONV = CONV_OF_THM RIGHT_IMP_EXISTS_THM;;
```

### Informal statement
The `RIGHT_IMP_EXISTS_CONV` is defined as the conversion of the theorem `RIGHT_IMP_EXISTS_THM` to a conversion using the `CONV_OF_THM` function.

### Informal sketch
* The definition relies on the `CONV_OF_THM` function, which converts a theorem into a conversion.
* The `RIGHT_IMP_EXISTS_THM` theorem is used as the input to `CONV_OF_THM`.
* The resulting conversion is assigned to `RIGHT_IMP_EXISTS_CONV`.

### Mathematical insight
This definition is likely used to enable the application of the `RIGHT_IMP_EXISTS_THM` theorem in a more flexible way, allowing for conversions that can be used in various contexts within the proof assistant.

### Dependencies
* `CONV_OF_THM`
* `RIGHT_IMP_EXISTS_THM`

### Porting notes
When porting this definition to another proof assistant, ensure that an equivalent of `CONV_OF_THM` is available or can be defined. Additionally, the `RIGHT_IMP_EXISTS_THM` theorem must be ported or proven in the target system before this definition can be translated.

---

## FORALL_IMP_CONV

### Name of formal statement
FORALL_IMP_CONV

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let FORALL_IMP_CONV = CONV_OF_RCONV
  (REWR_CONV TRIV_FORALL_IMP_THM ORELSEC
   REWR_CONV RIGHT_FORALL_IMP_THM ORELSEC
   REWR_CONV LEFT_FORALL_IMP_THM)
```

### Informal statement
The `FORALL_IMP_CONV` definition introduces a conversion that combines three rewriting conversions for handling implications involving universal quantification. It applies `REWR_CONV` to `TRIV_FORALL_IMP_THM`, `RIGHT_FORALL_IMP_THM`, and `LEFT_FORALL_IMP_THM` in sequence, effectively creating a conversion that can rewrite expressions involving these theorems.

### Informal sketch
* The conversion starts by applying `REWR_CONV` to `TRIV_FORALL_IMP_THM`, which likely handles trivial cases of universal quantification implications.
* Then, it applies `REWR_CONV` to `RIGHT_FORALL_IMP_THM`, which probably addresses implications where the universal quantifier is on the right side of the implication.
* Finally, it applies `REWR_CONV` to `LEFT_FORALL_IMP_THM`, which likely deals with cases where the universal quantifier is on the left side of the implication.
* The `ORELSEC` operator is used to combine these rewriting conversions, allowing the `FORALL_IMP_CONV` conversion to handle a variety of cases involving universal quantification and implications.

### Mathematical insight
The `FORALL_IMP_CONV` definition provides a way to simplify and manipulate expressions involving universal quantification and implications. By combining different rewriting conversions, it enables the automation of proofs involving these constructs, making it a useful tool in formal reasoning.

### Dependencies
* Theorems:
  + `TRIV_FORALL_IMP_THM`
  + `RIGHT_FORALL_IMP_THM`
  + `LEFT_FORALL_IMP_THM`
* Definitions:
  + `REWR_CONV`
  + `CONV_OF_RCONV`
  + `ORELSEC`

### Porting notes
When porting this definition to another proof assistant, it is essential to understand the equivalent rewriting mechanisms and how they handle universal quantification and implications. The `REWR_CONV` and `CONV_OF_RCONV` functions, as well as the `ORELSEC` operator, may need to be translated to their corresponding constructs in the target system. Additionally, the theorems `TRIV_FORALL_IMP_THM`, `RIGHT_FORALL_IMP_THM`, and `LEFT_FORALL_IMP_THM` must be defined or imported in the target system before attempting to port the `FORALL_IMP_CONV` definition.

---

## EXISTS_AND_CONV

### Name of formal statement
EXISTS_AND_CONV

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let EXISTS_AND_CONV = CONV_OF_RCONV
  (REWR_CONV TRIV_EXISTS_AND_THM ORELSEC
   REWR_CONV LEFT_EXISTS_AND_THM ORELSEC
   REWR_CONV RIGHT_EXISTS_AND_THM)
```

### Informal statement
The definition `EXISTS_AND_CONV` is a conversion that applies a series of rewrites using `REWR_CONV` to theorems `TRIV_EXISTS_AND_THM`, `LEFT_EXISTS_AND_THM`, and `RIGHT_EXISTS_AND_THM`, combined with `ORELSEC`, to transform existential statements involving conjunctions.

### Informal sketch
* The definition starts with `CONV_OF_RCONV`, which suggests it is constructing a conversion from a list of rewrites.
* It applies `REWR_CONV` to three theorems: `TRIV_EXISTS_AND_THM`, `LEFT_EXISTS_AND_THM`, and `RIGHT_EXISTS_AND_THM`, indicating a sequence of rewrites related to existential quantification and conjunction.
* Each `REWR_CONV` is separated by `ORELSEC`, implying these rewrites are applied in a specific order, likely to handle different cases or transformations of existential statements involving `AND`.
* The overall structure indicates a strategic approach to simplifying or transforming existential statements with conjunctions, likely aiming for a more manageable or canonical form.

### Mathematical insight
This definition is important for simplifying or manipulating logical statements involving existential quantification and conjunction. It provides a structured way to apply known theorems (`TRIV_EXISTS_AND_THM`, `LEFT_EXISTS_AND_THM`, `RIGHT_EXISTS_AND_THM`) to transform such statements, potentially making them more amenable to further reasoning or proof.

### Dependencies
- Theorems:
  - `TRIV_EXISTS_AND_THM`
  - `LEFT_EXISTS_AND_THM`
  - `RIGHT_EXISTS_AND_THM`
- Definitions:
  - `CONV_OF_RCONV`
  - `REWR_CONV`
  - `ORELSEC`

### Porting notes
When translating `EXISTS_AND_CONV` into another proof assistant, pay attention to how existential quantification and conjunction are handled, as well as how rewrites or similar transformations are applied. The sequence and combination of these rewrites, as indicated by `ORELSEC`, are crucial for the correct application of the conversion. Additionally, ensure that the target system's equivalent of `CONV_OF_RCONV` and `REWR_CONV` can handle the specific theorems and logical connectives involved.

---

## LEFT_IMP_EXISTS_CONV

### Name of formal statement
LEFT_IMP_EXISTS_CONV

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let LEFT_IMP_EXISTS_CONV = CONV_OF_THM LEFT_IMP_EXISTS_THM;;
```

### Informal statement
This definition introduces a conversion `LEFT_IMP_EXISTS_CONV` that is derived from the theorem `LEFT_IMP_EXISTS_THM` using the `CONV_OF_THM` function, which converts a theorem into a conversion.

### Informal sketch
* The definition relies on the `CONV_OF_THM` function to transform the `LEFT_IMP_EXISTS_THM` theorem into a conversion.
* The `LEFT_IMP_EXISTS_THM` theorem is not defined in this snippet, but it is assumed to be a previously established result that can be converted into a `CONV` type, which represents a conversion in HOL Light.
* The conversion `LEFT_IMP_EXISTS_CONV` can then be used to transform terms in a goal or hypothesis, leveraging the logical content of `LEFT_IMP_EXISTS_THM`.

### Mathematical insight
This definition is important because it enables the application of the `LEFT_IMP_EXISTS_THM` theorem as a conversion, which can simplify or transform terms within a proof, potentially discharging obligations or revealing new paths forward in a proof development. The ability to convert theorems into conversions provides flexibility in proof strategy and tactic application.

### Dependencies
- Theorems: `LEFT_IMP_EXISTS_THM`
- Functions: `CONV_OF_THM`

### Porting notes
When porting this definition to another proof assistant like Lean, Coq, or Isabelle, one should first ensure that an equivalent of `CONV_OF_THM` exists or can be defined, which might involve understanding how each system handles theorem applications and conversions. Additionally, the `LEFT_IMP_EXISTS_THM` theorem must be ported or proven within the target system before this conversion can be defined. The process may involve differences in how binders are handled or how tactical proofs are structured, requiring careful consideration of the source and target systems' strategic and tactical frameworks.

---

## LEFT_AND_EXISTS_CONV

### Name of formal statement
LEFT_AND_EXISTS_CONV

### Type of the formal statement
Theorem/Conversion Rule

### Formal Content
```ocaml
let LEFT_AND_EXISTS_CONV tm =
  let v = bndvar(rand(rand(rator tm))) in
  (REWR_CONV LEFT_AND_EXISTS_THM THENC TRY_CONV (GEN_ALPHA_CONV v)) tm;;
```

### Informal statement
This conversion rule takes a term `tm` and applies a series of transformations to it. First, it identifies a bound variable `v` within `tm` by navigating through the term's structure. It then applies `REWR_CONV` with the theorem `LEFT_AND_EXISTS_THM`, followed by `TRY_CONV` with `GEN_ALPHA_CONV` applied to the variable `v`, all composed together (`THENC`) and finally applied to the original term `tm`.

### Informal sketch
* Identify a term `tm` to which the conversion will be applied.
* Extract a bound variable `v` from `tm` by taking the argument of the argument of the operator of `tm` and then finding the bound variable within that.
* Apply the `REWR_CONV` conversion using the `LEFT_AND_EXISTS_THM` theorem to `tm`.
* Then, attempt (`TRY_CONV`) to apply `GEN_ALPHA_CONV` specifically to the variable `v` within the result.
* The result of these conversions is the output of `LEFT_AND_EXISTS_CONV` applied to `tm`.

### Mathematical insight
This conversion rule appears to be part of a system for manipulating logical expressions, specifically those involving existential quantification and conjunction. The `LEFT_AND_EXISTS_THM` theorem likely states a property or equivalence related to these concepts, and `GEN_ALPHA_CONV` seems to be involved in renaming or managing bound variables. The purpose of `LEFT_AND_EXISTS_CONV` is to systematically apply these transformations to terms, potentially simplifying or normalizing them according to the rules provided.

### Dependencies
* Theorems:
  - `LEFT_AND_EXISTS_THM`
* Conversions:
  - `REWR_CONV`
  - `TRY_CONV`
  - `GEN_ALPHA_CONV`
* Functions:
  - `bndvar`
  - `rand`
  - `rator`

### Porting notes
When translating `LEFT_AND_EXISTS_CONV` into another proof assistant, pay close attention to how that system handles bound variables and the application of theorems as rewriting rules. The equivalent of `GEN_ALPHA_CONV` and its application to specific variables will need to be identified or implemented. Additionally, the `THENC` composition and `TRY_CONV` may have direct analogs or require creative use of the target system's tacticals to achieve similar effects. Differences in how terms are represented and manipulated (e.g., de Bruijn indices vs. named variables) may also affect the translation of `bndvar`, `rand`, and `rator`.

---

## RIGHT_AND_EXISTS_CONV

### Name of formal statement
RIGHT_AND_EXISTS_CONV

### Type of the formal statement
Theorem/conversion rule

### Formal Content
```ocaml
let RIGHT_AND_EXISTS_CONV =
  CONV_OF_THM RIGHT_AND_EXISTS_THM;;
```

### Informal statement
This conversion rule is based on the theorem `RIGHT_AND_EXISTS_THM`, which likely states a property related to the existential quantifier and conjunction, specifically that an existential statement implies a conjunction of existentials under certain conditions.

### Informal sketch
* The proof or construction underlying `RIGHT_AND_EXISTS_CONV` involves applying the theorem `RIGHT_AND_EXISTS_THM` to convert or simplify expressions involving existential quantification and conjunction.
* The key logical stage is recognizing when an expression can be transformed using the `RIGHT_AND_EXISTS_THM` theorem, which may involve identifying patterns of existential quantification followed by conjunction.
* The `CONV_OF_THM` function is used to turn the theorem into a conversion rule, which can then be applied to terms in a goal to simplify or transform them according to the theorem's statement.

### Mathematical insight
The `RIGHT_AND_EXISTS_CONV` conversion rule is important because it provides a systematic way to apply the insight or result captured by `RIGHT_AND_EXISTS_THM` to simplify or prove statements involving existential quantification and conjunction. This is part of the foundational machinery for handling quantifiers and propositional logic within the proof assistant.

### Dependencies
- Theorems:
  - `RIGHT_AND_EXISTS_THM`
- Definitions:
  - None
- Inductive rules:
  - None
- Other dependencies:
  - `CONV_OF_THM`

### Porting notes
When translating `RIGHT_AND_EXISTS_CONV` into another proof assistant, pay close attention to how that system handles the conversion of theorems into tactics or conversion rules. The equivalent of `CONV_OF_THM` may differ, and the treatment of quantifiers and conjunction may have distinct syntactic or tactical representations. Ensure that the ported version correctly applies the underlying theorem to transform expressions as intended.

---

## AND_FORALL_CONV

### Name of formal statement
AND_FORALL_CONV

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let AND_FORALL_CONV = CONV_OF_THM AND_FORALL_THM;;
```

### Informal statement
The `AND_FORALL_CONV` is defined as the conversion of the theorem `AND_FORALL_THM` to a conversion rule.

### Informal sketch
* The definition involves applying the `CONV_OF_THM` function to the `AND_FORALL_THM` theorem, which suggests that `AND_FORALL_THM` is being used to derive a conversion rule.
* The `AND_FORALL_THM` theorem is not explicitly stated here, but it is likely related to the interaction between universal quantification and conjunction.
* The conversion rule derived from `AND_FORALL_THM` is assigned to `AND_FORALL_CONV`, implying its use in rewriting or simplifying expressions involving these logical operators.

### Mathematical insight
The definition of `AND_FORALL_CONV` is important because it provides a way to automate the manipulation of expressions involving universal quantification and conjunction. This is a fundamental aspect of formal proof systems, as it allows for the simplification and transformation of complex logical statements.

### Dependencies
* **Theorems**: `AND_FORALL_THM`
* **Definitions**: `CONV_OF_THM`

### Porting notes
When porting this definition to another proof assistant, ensure that the equivalent of `CONV_OF_THM` is used to convert the theorem `AND_FORALL_THM` (or its equivalent) into a conversion rule. Note that different systems may handle the interaction between theorems and conversion rules differently, so careful attention to the specifics of the target system is necessary.

---

## AND1_THM

### Name of formal statement
AND1_THM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let AND1_THM = TAUT `!t1 t2. t1 /\ t2 ==> t1`;;
```

### Informal statement
For all `t1` and `t2`, if `t1` and `t2` are true, then `t1` is true.

### Informal sketch
* The proof involves a straightforward application of the `TAUT` function, which proves a statement by verifying it as a tautology.
* The statement `!t1 t2. t1 /\ t2 ==> t1` is a universal quantification over two propositions `t1` and `t2`, stating that if the conjunction of `t1` and `t2` is true, then `t1` is true.
* The key logical stage is recognizing that the implication `t1 /\ t2 ==> t1` is a tautology because the conjunction `t1 /\ t2` being true implies that both `t1` and `t2` are true, and thus `t1` is true.

### Mathematical insight
This theorem represents a basic property of conjunction in propositional logic, highlighting that if a conjunction is true, then at least one of its conjuncts must be true. This property is fundamental in logical deductions and is used extensively in various proofs.

### Dependencies
* `TAUT`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, ensure that the equivalent of the `TAUT` function is used, which typically involves using a tactic or command that proves a statement by verifying it as a tautology or using a decision procedure for propositional logic. Note that the handling of universal quantification and implications may vary slightly between systems, so attention should be paid to how these are represented and proved in the target system.

---

## AND2_THM

### Name of formal statement
AND2_THM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let AND2_THM = TAUT `!t1 t2. t1 /\ t2 ==> t2`;;
```

### Informal statement
For all propositions `t1` and `t2`, if `t1` and `t2` are both true, then `t2` is true.

### Informal sketch
* The theorem `AND2_THM` is proven using the `TAUT` tactic, which likely involves simplifying the statement using logical rules and axioms.
* The key step is recognizing that the implication `t1 /\ t2 ==> t2` is a tautology, as the conjunction `t1 /\ t2` implies `t2` by the definition of conjunction.
* The `!t1 t2` quantifier indicates that this implication holds for all possible propositions `t1` and `t2`.

### Mathematical insight
This theorem is a basic property of propositional logic, stating that if two propositions are both true, then the second proposition is true. This is a fundamental principle in logic and is used extensively in mathematical proofs.

### Dependencies
* `TAUT` tactic
* Definition of conjunction (`/\`)
* Definition of implication (`==>`)

### Porting notes
When porting this theorem to another proof assistant, note that the `TAUT` tactic may not be directly available. Instead, the proof may need to be constructed using other tactics or rules, such as `conjunct1` or `conjunct2` rules for conjunction elimination. Additionally, the quantifier `!t1 t2` may need to be handled explicitly using universal introduction or elimination rules.

---

## AND_IMP_INTRO

### Name of formal statement
AND_IMP_INTRO

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let AND_IMP_INTRO = TAUT `!t1 t2 t3. t1 ==> t2 ==> t3 = t1 /\ t2 ==> t3`;;
```

### Informal statement
For all propositions `t1`, `t2`, and `t3`, the following equivalence holds: `t1` implies `t2` implies `t3` is equivalent to `t1` and `t2` imply `t3`.

### Informal sketch
* The proof involves recognizing the tautological equivalence between two forms of implication.
* It starts with the assumption of `t1`, `t2`, and `t3` being arbitrary propositions.
* The `TAUT` `!t1 t2 t3. t1 ==> t2 ==> t3 = t1 /\ t2 ==> t3` suggests using a tautology checker or logical simplification to establish the equivalence.

### Mathematical insight
This statement is important because it provides a fundamental equivalence in propositional logic, allowing for the transformation of nested implications into a simpler form involving conjunction, which can be crucial for simplifying and proving logical statements.

### Dependencies
* `TAUT`

### Porting notes
When translating this into other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system handles propositional logic and tautologies. The concept of `TAUT` might be represented differently, and the system's approach to handling implications and conjunctions could vary. In some systems, this equivalence might be a built-in axiom or derived theorem, so checking the standard library or documentation for such a proposition is advisable.

---

## AND_INTRO_THM

### Name of formal statement
AND_INTRO_THM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let AND_INTRO_THM = TAUT `!t1 t2. t1 ==> t2 ==> t1 /\ t2`;;
```

### Informal statement
For all propositions `t1` and `t2`, if `t1` implies `t2` and `t1` is true, then the conjunction of `t1` and `t2` is true.

### Informal sketch
* The proof involves assuming two propositions `t1` and `t2`.
* It then applies the `TAUT` tactic, which likely involves a straightforward application of the rules of propositional logic to derive the conclusion `t1 /\ t2` from the premises `t1` and `t2`.
* The key logical stage is recognizing that if `t1` is true and `t1` implies `t2`, then `t2` must also be true, thus validating the conjunction `t1 /\ t2`.

### Mathematical insight
This theorem captures a fundamental property of conjunction in propositional logic, specifically how it relates to implication. It's essential for building more complex logical arguments and is a basic construct in many formal systems.

### Dependencies
* `TAUT`

### Porting notes
When translating this into another proof assistant like Lean, Coq, or Isabelle, pay attention to how each system handles implication and conjunction. Specifically, ensure that the implications `t1 ==> t2` and the conjunction `t1 /\ t2` are correctly represented according to the target system's syntax and semantics. Additionally, the `TAUT` tactic in HOL Light might correspond to different tactics or automation mechanisms in other proof assistants, such as `tauto` in Isabelle or `taut` in Coq.

---

## BOOL_EQ_DISTINCT

### Name of formal statement
BOOL_EQ_DISTINCT

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let BOOL_EQ_DISTINCT = TAUT `~(T <=> F) /\ ~(F <=> T)`;;
```

### Informal statement
The statement `BOOL_EQ_DISTINCT` is a tautology that asserts the conjunction of two negated biconditionals: it is not the case that true (`T`) is equivalent to false (`F`), and it is not the case that false (`F`) is equivalent to true (`T`).

### Informal sketch
* The proof of `BOOL_EQ_DISTINCT` involves recognizing that the biconditional `T <=> F` is always false, because `T` and `F` have different truth values.
* Similarly, `F <=> T` is also always false for the same reason.
* The `TAUT` function then asserts that the conjunction of the negations of these biconditionals is a tautology, meaning it is always true.

### Mathematical insight
This definition is important because it formally captures the distinctness of the boolean values true and false, which is a fundamental property in logic and computer science. It ensures that these two values are not considered equivalent, which is crucial for maintaining the consistency and correctness of logical and computational systems.

### Dependencies
* `TAUT`
* `~` (negation)
* `<=>` (biconditional)
* `/\` (conjunction)
* `T` (true)
* `F` (false)

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system represents boolean values and logical operators. Specifically, ensure that the representations of `T`, `F`, `~`, `<=>`, and `/\` are correctly mapped to their counterparts in the target system. Additionally, verify that the `TAUT` function or its equivalent is properly applied to assert the tautological status of the given statement.

---

## EQ_EXPAND

### Name of formal statement
EQ_EXPAND

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let EQ_EXPAND = TAUT `!t1 t2. (t1 <=> t2) <=> t1 /\ t2 \/ ~t1 /\ ~t2`;;
```

### Informal statement
For all propositions `t1` and `t2`, the statement "`t1` if and only if `t2`" is logically equivalent to "`t1` and `t2`" or "not `t1` and not `t2`".

### Informal sketch
* The definition `EQ_EXPAND` involves a universal quantification over two propositions `t1` and `t2`.
* It states an equivalence between a biconditional statement `t1 <=> t2` and a disjunction of two conjunctions: `t1 /\ t2` or `~t1 /\ ~t2`.
* The `TAUT` keyword indicates that this is a tautology, implying it is always true.
* To prove or construct something similar in another system, one would need to establish this equivalence, potentially using properties of logical operators and quantifiers.

### Mathematical insight
This definition captures the idea that two propositions are equivalent if they have the same truth value. It provides a way to expand or transform biconditional statements into disjunctions of conjunctions, which can be useful in various logical manipulations and proofs. The equivalence is fundamental in propositional logic, allowing for the transformation of statements in a way that preserves their truth value.

### Dependencies
* `TAUT`

### Porting notes
When translating `EQ_EXPAND` into another proof assistant, pay attention to how that system handles logical equivalences, especially in the context of quantifiers. Ensure that the target system's `TAUT` or equivalent mechanism for asserting tautologies is used correctly. Additionally, consider how the system handles the expansion of biconditionals into disjunctions of conjunctions, as this may involve specific tactics or rewrite rules.

---

## EQ_IMP_THM

### Name of formal statement
EQ_IMP_THM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let EQ_IMP_THM = TAUT `!t1 t2. (t1 <=> t2) <=> (t1 ==> t2) /\ (t2 ==> t1)`;;
```

### Informal statement
For all statements `t1` and `t2`, the biconditional `t1` if and only if `t2` is logically equivalent to the conjunction of `t1` implies `t2` and `t2` implies `t1`.

### Informal sketch
* The theorem `EQ_IMP_THM` is established using the `TAUT` tactic, which likely involves a straightforward application of logical rules to prove the equivalence.
* The key steps involve recognizing that the biconditional `t1 <=> t2` can be expanded into `(t1 ==> t2) /\ (t2 ==> t1)` and then using the `TAUT` tactic to automatically prove this equivalence.
* The main logical stage is recognizing the definition of the biconditional in terms of implication and conjunction.

### Mathematical insight
This theorem is important because it provides a fundamental equivalence between the biconditional operator and a combination of implications. This equivalence is crucial in many logical and mathematical proofs, allowing for the conversion between these two forms of statements. It is a basic property of classical logic and is used extensively in various mathematical and logical derivations.

### Dependencies
* `TAUT`

### Porting notes
When porting this theorem to another proof assistant like Lean, Coq, or Isabelle, ensure that the equivalent of the `TAUT` tactic is used, which often involves using automated reasoning tools or tactics that can handle propositional logic. Note that the handling of binders and the specific syntax for biconditional and implication may differ between systems.

---

## FALSITY

### Name of formal statement
FALSITY

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let FALSITY = TAUT `!t. F ==> t`;;
```

### Informal statement
For all propositions `t`, if the false proposition `F` implies `t`, then `t` is true. In other words, the falsity `F` implies any proposition `t`.

### Informal sketch
* The definition of `FALSITY` involves a universal quantification over all propositions `t`.
* The `TAUT` function is used to assert that the implication `F ==> t` is a tautology for any `t`.
* The key logical stage is recognizing that `F` (falsity) implies any proposition `t` due to the principle of explosion, which states that anything can be deduced from a contradiction or a false premise.

### Mathematical insight
The definition of `FALSITY` captures the principle of explosion in classical logic, where a false statement implies any statement. This principle is fundamental in constructing proofs by contradiction and is a cornerstone of classical logic.

### Dependencies
* `TAUT`
* `F` (falsity proposition)

### Porting notes
When porting this definition to other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles the principle of explosion and the representation of falsity. Some systems may have built-in support for classical logic principles, while others might require explicit axiomatization or proof. Additionally, the representation of the `TAUT` function might differ, potentially involving different tactics or constructs for asserting tautologies.

---

## F_IMP

### Name of formal statement
F_IMP

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let F_IMP = TAUT `!t. ~t ==> t ==> F`;;
```

### Informal statement
For all propositions `t`, if not `t` implies `t` and `t` implies `F`, then the statement holds.

### Informal sketch
* The statement `F_IMP` is defined using the `TAUT` function, which likely checks for tautologies.
* The implication `~t ==> t` suggests a contradiction, unless `t` is a tautology itself.
* The further implication `t ==> F` then connects this to the proposition `F`.
* The use of `!t` indicates that this holds for all propositions `t`.

### Mathematical insight
This definition seems to capture a specific logical relationship, potentially related to the principles of non-contradiction or the nature of implication in classical logic. The involvement of `TAUT` suggests it's about logical truths.

### Dependencies
* `TAUT`

### Porting notes
When translating this into other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system handles implications, negations, and universal quantifications. Specifically, the `TAUT` function might need to be replaced with an equivalent mechanism for checking tautologies, and the implication syntax might differ (e.g., `->` in Lean or Coq instead of `==>`).

---

## IMP_DISJ_THM

### Name of formal statement
IMP_DISJ_THM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let IMP_DISJ_THM = TAUT `!t1 t2. t1 ==> t2 <=> ~t1 \/ t2`;;
```

### Informal statement
For all propositions `t1` and `t2`, the implication `t1` implies `t2` is logically equivalent to the disjunction of the negation of `t1` and `t2`.

### Informal sketch
* The theorem `IMP_DISJ_THM` establishes a logical equivalence between an implication and a disjunction.
* The proof involves recognizing that `t1 ==> t2` is equivalent to `~t1 \/ t2` through the use of `TAUT`, which likely applies a set of predefined logical rules or axioms to derive the equivalence.
* Key steps may involve:
  + Understanding the definition of implication in terms of negation and disjunction.
  + Applying logical equivalences or rules to transform the implication into a disjunction.

### Mathematical insight
This theorem is fundamental in classical logic, as it shows how an implication can be expressed using only negation, disjunction, and the propositions themselves. This equivalence is crucial for transforming and simplifying logical expressions, especially in contexts where only certain logical operators are primitive.

### Dependencies
* `TAUT`: A mechanism or tactic in HOL Light for deriving logical tautologies.
 
### Porting notes
When porting this theorem to another proof assistant, ensure that the target system has a similar mechanism for deriving or proving logical equivalences. Pay special attention to how implications and disjunctions are handled, as well as the treatment of quantifiers. In systems like Lean, Coq, or Isabelle, this might involve using specific tactics or libraries for logical manipulations.

---

## IMP_F

### Name of formal statement
IMP_F

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let IMP_F = TAUT `!t. (t ==> F) ==> ~t`;;
```

### Informal statement
For all propositions `t`, if `t` implies `F` (false), then not `t`. This statement captures the idea that if a proposition implies a false statement, then the original proposition must be false.

### Informal sketch
* The statement `IMP_F` is defined using the `TAUT` function, which likely denotes a tautology or a universally true statement.
* The definition involves a universal quantification over all propositions `t`.
* The implication `t ==> F` suggests that if `t` is true, then `F` (false) must also be true, which is a contradiction.
* Therefore, the conclusion `~t` (not `t`) logically follows from the premise `t ==> F`.
* The `TAUT` function may be used to assert the validity of this implication for all possible values of `t`.

### Mathematical insight
This definition is important because it formalizes a fundamental principle of classical logic, where a proposition that implies a false statement must itself be false. This is a key property of implication in classical logic and has far-reaching implications in various areas of mathematics and computer science.

### Dependencies
* `TAUT`
* `==>` (implication operator)
* `~` (negation operator)
* `!` (universal quantification)

### Porting notes
When translating this definition into other proof assistants, care should be taken to preserve the universal quantification and the implication structure. The `TAUT` function may need to be replaced with an equivalent construct, such as a `Theorem` or `Axiom` statement, depending on the target system. Additionally, the handling of implication and negation operators may differ between systems, requiring careful attention to the specific syntax and semantics of the target proof assistant.

---

## IMP_F_EQ_F

### Name of formal statement
IMP_F_EQ_F

### Type of the formal statement
new_definition or theorem, likely a theorem given the structure

### Formal Content
```ocaml
let IMP_F_EQ_F = TAUT `!t. t ==> F <=> (t <=> F)`;;
```

### Informal statement
For all propositions `t`, the implication that `t` implies False (`F`) is equivalent to the statement that `t` is equivalent to False (`F`).

### Informal sketch
* The statement involves a universal quantification over all propositions `t`.
* It asserts an equivalence between two statements: 
  + `t` implies `F` 
  + `t` is equivalent to `F`.
* The proof likely involves unfolding the definitions of implication and equivalence, and then using basic properties of propositional logic to establish the equivalence.
* Key steps may involve using the `TAUT` tactic to prove the statement is a tautology, possibly leveraging properties of implication (`-->`), equivalence (`<=>`), and the constant `F` (False).

### Mathematical insight
This statement highlights a fundamental property of propositional logic, showing how an implication to a false statement relates to the equivalence of a statement with falsehood. It's a basic result that can be used in various proofs involving implications and equivalences, especially when dealing with negations or falsehoods.

### Dependencies
* `TAUT`
* Basic properties of implication (`-->`)
* Basic properties of equivalence (`<=>`)
* Definition or axiom of `F` (False)

### Porting notes
When translating this into another proof assistant like Lean, Coq, or Isabelle, pay attention to how each system handles propositional logic, especially the representation of `F` (False) and the tactics available for proving tautologies. The `TAUT` tactic in HOL Light might have a direct counterpart or require a combination of tactics in the target system to achieve the same effect. Additionally, consider the specific syntax and built-in support for propositional reasoning in the target system.

---

## LEFT_AND_OVER_OR

### Name of formal statement
LEFT_AND_OVER_OR

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LEFT_AND_OVER_OR = TAUT `!t1 t2 t3. t1 /\ (t2 \/ t3) <=> t1 /\ t2 \/ t1 /\ t3`;;
```

### Informal statement
For all propositions `t1`, `t2`, and `t3`, the statement "`t1` and (`t2` or `t3`)" is logically equivalent to "(`t1` and `t2`) or (`t1` and `t3`)".

### Informal sketch
* The theorem `LEFT_AND_OVER_OR` is established by proving a logical equivalence between two expressions involving conjunction and disjunction.
* The proof likely involves using the `TAUT` tactic in HOL Light, which automatically proves tautologies.
* Key steps might include:
  + Applying the definition of logical equivalence (`<=>`)
  + Using the distributive property of conjunction over disjunction
  + Employing `TAUT` to discharge the resulting tautological statement

### Mathematical insight
This theorem represents the distributive law of conjunction over disjunction in propositional logic, which is a fundamental property that allows for the manipulation of logical expressions. It is crucial for simplifying and reasoning about complex logical statements.

### Dependencies
* `TAUT`

### Porting notes
When translating this theorem into other proof assistants, ensure that the target system supports automatic proof of tautologies or provides an equivalent mechanism for establishing logical equivalences. In systems like Lean, Coq, or Isabelle, this might involve using tactics or commands specifically designed for proving tautologies or logical equivalences.

---

## LEFT_OR_OVER_AND

### Name of formal statement
LEFT_OR_OVER_AND

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LEFT_OR_OVER_AND = TAUT `!t1 t2 t3. t1 \/ t2 /\ t3 <=> (t1 \/ t2) /\ (t1 \/ t3)`
```

### Informal statement
For all propositions `t1`, `t2`, and `t3`, the statement (`t1` or `t2`) and `t3` is logically equivalent to (`t1` or `t2`) and (`t1` or `t3`).

### Informal sketch
* The proof involves showing the equivalence of two logical expressions through a series of logical transformations.
* It starts with the original expression `t1 \/ t2 /\ t3` and aims to transform it into `(t1 \/ t2) /\ (t1 \/ t3)`.
* The key steps involve applying the distributive property of logical operators and potentially using the `TAUT` function from HOL Light, which likely applies a set of predefined logical transformations to validate the equivalence.
* The process ensures that the logical structure and quantifiers are preserved, demonstrating the equivalence for all possible `t1`, `t2`, and `t3`.

### Mathematical insight
This statement is a demonstration of the distributive property of logical disjunction over conjunction, showcasing how logical expressions can be manipulated and simplified while preserving their truth values. It's a fundamental property in propositional logic, crucial for simplifying complex logical statements and is often used in various proofs and logical derivations.

### Dependencies
* `TAUT`

### Porting notes
When porting this theorem to another proof assistant like Lean, Coq, or Isabelle, ensure that the target system supports a similar `TAUT` functionality or mechanism for proving logical equivalences. Additionally, pay attention to how each system handles quantifiers and logical operators, as the syntax and built-in support can vary.

---

## NOT_AND

### Name of formal statement
NOT_AND

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let NOT_AND = TAUT `~(t /\ ~t)`;;
```

### Informal statement
The definition NOT_AND is equivalent to the tautology that not (t and not t).

### Informal sketch
* The definition uses the `TAUT` function to assert a tautology.
* The tautology in question is the negation of the conjunction of `t` and the negation of `t`, which is always false, thus its negation is always true.
* This is a basic example of a tautology in propositional logic, where the statement is always true regardless of the truth value of `t`.

### Mathematical insight
This definition captures a fundamental property of propositional logic, where a statement and its negation cannot both be true at the same time. This is an instance of the law of non-contradiction.

### Dependencies
#### Definitions
* `TAUT`
#### Theorems
None

### Porting notes
When porting this definition to another proof assistant, ensure that the equivalent of `TAUT` is used to define a tautology. Note that different systems may handle tautologies and propositional logic differently, so the exact formulation may vary. For example, in a system that does not have a direct equivalent of `TAUT`, one might need to prove the tautology using basic axioms and rules of inference.

---

## NOT_F

### Name of formal statement
NOT_F

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let NOT_F = TAUT `!t. ~t ==> (t <=> F)`;;
```

### Informal statement
For all propositions t, if not t, then t is equivalent to False.

### Informal sketch
* The statement `NOT_F` is defined using the `TAUT` function, which likely asserts a tautology.
* The `!t` symbol denotes universal quantification over all propositions t.
* The antecedent `~t` represents the negation of proposition t.
* The consequent `t <=> F` states that t is equivalent to False, where `F` denotes the False proposition.
* The definition essentially captures the idea that if a proposition is false, it is equivalent to the constant False proposition.

### Mathematical insight
This definition is important because it establishes a fundamental property relating negation and equivalence in propositional logic. It provides a basis for further reasoning about propositions and their negations, facilitating the development of more complex logical arguments.

### Dependencies
* `TAUT`
* `!` (universal quantification)
* `~` (negation)
* `==>` (implication)
* `<=>` (equivalence)
* `F` (False proposition)

### Porting notes
When porting this definition to other proof assistants, note that the `TAUT` function may need to be replaced with an equivalent construct, such as a tautology checker or a propositional logic axiom. Additionally, the representation of propositions, quantification, and logical operators may differ between systems, requiring careful translation to ensure equivalence.

---

## OR_ELIM_THM

### Name of formal statement
OR_ELIM_THM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let OR_ELIM_THM = TAUT `!t t1 t2. t1 \/ t2 ==> (t1 ==> t) ==> (t2 ==> t) ==> t`
```

### Informal statement
For all statements `t`, `t1`, and `t2`, if `t1` or `t2` is true, and if `t1` implies `t`, and if `t2` implies `t`, then `t` is true.

### Informal sketch
* The theorem `OR_ELIM_THM` is proven using the `TAUT` tactic, which likely involves applying basic properties of propositional logic.
* The proof structure involves recognizing the disjunction `t1 \/ t2` and using this to derive `t` by considering two cases: one where `t1` holds and one where `t2` holds.
* In each case, the respective implication (`t1 ==> t` or `t2 ==> t`) is used to derive `t`.
* The `TAUT` tactic likely automates the recognition of tautologies and applies standard logical rules to derive the conclusion.

### Mathematical insight
This theorem formalizes the principle of proof by cases for disjunction in propositional logic. It's essential for constructing proofs that depend on the truth of at least one of two statements. The theorem is fundamental in logical deductions, allowing one to conclude a statement `t` if it can be shown that `t` follows from either `t1` or `t2`, given that `t1` or `t2` is true.

### Dependencies
* Propositional logic axioms and rules
* Definition of disjunction (`\/`)
* Definition of implication (`==>`)

### Porting notes
When porting this theorem to another proof assistant like Lean, Coq, or Isabelle, ensure that the target system's logic and proof mechanisms support similar constructs for disjunction and implication. Pay special attention to how each system handles propositional logic and case analysis, as the direct equivalent of HOL Light's `TAUT` tactic might not be available. Instead, use the proof assistants' built-in tactics for propositional logic, such as `tauto` in Isabelle or `tautology` tactics in Coq, to automate the proof.

---

## OR_IMP_THM

### Name of formal statement
OR_IMP_THM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let OR_IMP_THM = TAUT `!t1 t2. (t1 <=> t2 \/ t1) <=> t2 ==> t1;;
```

### Informal statement
For all propositions `t1` and `t2`, the statement "(`t1` is equivalent to `t2` or `t1`) is equivalent to (`t2` implies `t1`)" is a tautology.

### Informal sketch
* The theorem `OR_IMP_THM` involves proving a logical equivalence between two statements involving implications and disjunctions.
* The proof likely involves using properties of logical equivalence (`<=>`), disjunction (`\/`), and implication (`==>`), possibly leveraging known laws such as the distributive law or the definition of implication itself.
* Key steps may include using `TAUT` to establish the statement as a tautology, potentially simplifying or manipulating the expressions inside the quantifiers to show their equivalence.

### Mathematical insight
This theorem captures a fundamental property of classical logic, relating the equivalence of two propositions with the implication between them under certain conditions. It highlights how logical operators interact, particularly how disjunction and implication can be related through equivalence. Understanding and proving such statements is crucial for establishing the foundations of logic within a proof assistant.

### Dependencies
* `TAUT`

### Porting notes
When translating this theorem into another proof assistant like Lean, Coq, or Isabelle, pay close attention to how each system handles quantifiers, logical equivalences, and implications. Some systems may require explicit introduction of these rules or different tactics for proving tautologies. Additionally, consider the specific laws or properties of logical operators that are already defined in the target system, as these may simplify the porting process.

---

## OR_INTRO_THM1

### Name of formal statement
OR_INTRO_THM1

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let OR_INTRO_THM1 = TAUT `!t1 t2. t1 ==> t1 \/ t2`;;
```

### Informal statement
For all propositions `t1` and `t2`, if `t1` is true, then the disjunction of `t1` and `t2` is true.

### Informal sketch
* The proof involves a straightforward application of the `TAUT` function, which reduces the given statement to a tautology.
* The statement `!t1 t2. t1 ==> t1 \/ t2` is proven by recognizing that if `t1` is true, then the disjunction `t1 \/ t2` is also true, regardless of the truth value of `t2`.
* The key logical stage here is the introduction of the disjunction, which is justified by the truth of `t1`.

### Mathematical insight
This theorem represents a fundamental property of disjunction in classical logic, where if one of the disjuncts is known to be true, the entire disjunction is true. It is a basic building block for more complex logical arguments and is essential for constructing proofs that involve disjunctions.

### Dependencies
* `TAUT`

### Porting notes
When porting this theorem to another proof assistant like Lean, Coq, or Isabelle, pay attention to how each system handles the introduction of disjunctions and the representation of tautologies. Specifically, the `TAUT` function in HOL Light may not have a direct equivalent, so the proof may need to be reconstructed using the target system's methods for proving tautologies or basic logical properties.

---

## OR_INTRO_THM2

### Name of formal statement
OR_INTRO_THM2

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let OR_INTRO_THM2 = TAUT `!t1 t2. t2 ==> t1 \/ t2`;;
```

### Informal statement
For all propositions `t1` and `t2`, if `t2` is true, then `t1` or `t2` is true.

### Informal sketch
* The theorem `OR_INTRO_THM2` is proven using the `TAUT` tactic, which likely involves a straightforward application of logical rules to derive the conclusion.
* The proof starts with the assumption `t2`, which is then used to derive `t1 \/ t2` using the definition of disjunction.
* The `!t1 t2` quantification indicates that the statement holds for all possible propositions `t1` and `t2`.

### Mathematical insight
This theorem is a fundamental property of classical logic, stating that if a proposition `t2` is true, then the disjunction of any proposition `t1` with `t2` is also true. This theorem is important because it provides a basic rule for manipulating disjunctions in logical proofs.

### Dependencies
* `TAUT`

### Porting notes
When porting this theorem to another proof assistant, note that the `TAUT` tactic may not be directly available. Instead, the proof may need to be reconstructed using the specific tactics and rules provided by the target system. Additionally, the handling of quantifiers and propositional logic may differ between systems, requiring careful attention to the translation.

---

## RIGHT_AND_OVER_OR

### Name of formal statement
RIGHT_AND_OVER_OR

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let RIGHT_AND_OVER_OR = TAUT `!t1 t2 t3. (t2 \/ t3) /\ t1 <=> t2 /\ t1 \/ t3 /\ t1`;;
```

### Informal statement
For all propositions `t1`, `t2`, and `t3`, the following equivalence holds: `(t2 or t3) and t1` is equivalent to `(t2 and t1) or (t3 and t1)`.

### Informal sketch
* The proof involves establishing an equivalence between two logical expressions.
* It starts by assuming `(t2 or t3) and t1` and derives `(t2 and t1) or (t3 and t1)` through logical manipulation.
* Conversely, it assumes `(t2 and t1) or (t3 and t1)` and derives `(t2 or t3) and t1`.
* The `TAUT` `!t1 t2 t3. (t2 \/ t3) /\ t1 <=> t2 /\ t1 \/ t3 /\ t1` suggests the use of `TAUT` tactic to prove the statement.

### Mathematical insight
This statement is a variation of the distributive property of conjunction over disjunction in propositional logic. It highlights how the conjunction of a proposition with a disjunction can be distributed over the disjunction, which is a fundamental property in logical reasoning and is used extensively in various mathematical proofs and logical deductions.

### Dependencies
* `TAUT`

### Porting notes
When porting this theorem to another proof assistant, ensure that the target system supports a similar `TAUT` mechanism for proving tautologies or has an equivalent tactic for establishing logical equivalences. Additionally, pay attention to how the target system handles binder syntax and quantifier scope to accurately translate the `!t1 t2 t3` quantification.

---

## RIGHT_OR_OVER_AND

### Name of formal statement
RIGHT_OR_OVER_AND

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let RIGHT_OR_OVER_AND = TAUT `!t1 t2 t3. t2 /\ t3 \/ t1 <=> (t2 \/ t1) /\ (t3 \/ t1)`;;
```

### Informal statement
For all propositions `t1`, `t2`, and `t3`, the following equivalence holds: (`t2` and `t3`) or `t1` if and only if (`t2` or `t1`) and (`t3` or `t1`).

### Informal sketch
* The proof involves establishing an equivalence between two logical expressions, which can be approached by showing that each side implies the other.
* Start with the left-hand side (`t2 /\ t3 \/ t1`) and apply distributive laws or `TAUT` to transform it into the right-hand side (`(t2 \/ t1) /\ (t3 \/ t1)`).
* Conversely, begin with the right-hand side and use similar logical principles to derive the left-hand side, potentially leveraging `TAUT` for simplification.
* Key steps may involve using the `CONJUNCT1` and `CONJUNCT2` theorems to manipulate conjunctions, and possibly `DISJUNCT1` and `DISJUNCT2` for disjunctions.

### Mathematical insight
This theorem is a distributive property that relates conjunction and disjunction in propositional logic. It is essential for simplifying and manipulating logical expressions, allowing for the transformation of complex propositions into more manageable forms. Understanding and applying such properties is crucial in formal proof development, as it enables the derivation of conclusions from given premises in a logically sound manner.

### Dependencies
* **Theorems**: 
  - `TAUT`
  - Possibly `CONJUNCT1`, `CONJUNCT2`, `DISJUNCT1`, `DISJUNCT2`
* **Definitions**: 
  - None explicitly mentioned, but relies on standard definitions of `/\\` (conjunction), `\/` (disjunction), and logical equivalence `<=>`.

### Porting notes
When translating this theorem into another proof assistant like Lean, Coq, or Isabelle, pay close attention to how each system handles binders, propositional logic, and the specific tactics or automation available for manipulating logical expressions. The `TAUT` tactic in HOL Light is particularly powerful for simplifying logical expressions and may have analogs in other systems (e.g., `tauto` in Isabelle). Additionally, consider the differences in how each system represents and proves logical equivalences, as the specific proof steps and theorems used may vary.

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
The `is_type` definition asserts that it is possible to obtain the arity of a type.

### Informal sketch
* The definition relies on the `can` operator and the `get_type_arity` function.
* The `get_type_arity` function is expected to return the arity of a type if it exists.
* The `can` operator checks if the `get_type_arity` function can successfully return a value.

### Mathematical insight
This definition is important because it provides a way to determine if a type has a well-defined arity. In type theory, the arity of a type refers to the number of type parameters it takes. The ability to obtain the arity of a type is crucial in various type-related operations and constructions.

### Dependencies
* `get_type_arity`
* `can`

### Porting notes
When translating this definition into other proof assistants, ensure that the equivalent of the `can` operator and the `get_type_arity` function are properly defined and used. In some systems, the `can` operator might be represented as a separate tactic or a combinator, while in others, it might be implicit in the type system. Additionally, the `get_type_arity` function might need to be adapted to fit the specific type theory and representation of types in the target system.

---

## is_constant

### Name of formal statement
is_constant

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let is_constant = can get_const_type;;
```

### Informal statement
The function `is_constant` is defined as the ability to get the constant type.

### Informal sketch
* The definition relies on the `can` function and `get_const_type` to determine if a constant type can be obtained.
* The `is_constant` function essentially checks if it is possible to retrieve the type of a constant using `get_const_type`.
* This involves understanding the `can` function's behavior in the context of type retrieval.

### Mathematical insight
The `is_constant` definition is important because it provides a way to identify or check if an object or expression is a constant by determining if its type can be retrieved. This is a fundamental concept in formal systems, as constants often have specific properties or behaviors that need to be recognized and handled appropriately.

### Dependencies
* `can`
* `get_const_type`

### Porting notes
When translating `is_constant` into other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system handles type checking and the retrieval of constant types. The `can` function and `get_const_type` may have direct analogs or require a different approach to achieve the same functionality. Consider the specific type theories and mechanisms for handling constants in the target system.

---

## null

### Name of formal statement
null

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let null l = l = []
```

### Informal statement
The function `null` takes a list `l` and returns `True` if and only if the list `l` is equal to the empty list `[]`.

### Informal sketch
* The definition of `null` is straightforward and checks for list emptiness by comparing the input list `l` with the empty list `[]`.
* This comparison is the core of the `null` function, allowing it to determine whether a given list contains any elements.

### Mathematical insight
The `null` function is a fundamental predicate in list theory, used to determine if a list is empty. It is crucial in various list processing functions and theorems, serving as a basic condition for handling lists.

### Dependencies
#### Definitions
* `[]` (the empty list)

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, ensure that the equivalent of the `null` function is defined in terms of the empty list constant of the target system. Note that some systems may have predefined predicates or functions for checking list emptiness, which could be used instead of defining a new function.

---

## type_tyvars

### Name of formal statement
type_tyvars

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let type_tyvars = type_vars_in_term o curry mk_var "x";;
```

### Informal statement
The function `type_tyvars` is defined as the composition of `type_vars_in_term` and the curried version of `mk_var` applied to the string "x". In other words, `type_tyvars` applies `mk_var` to "x" to create a variable, then applies `type_vars_in_term` to find the type variables in that term.

### Informal sketch
* The definition starts by creating a variable `x` using `mk_var`.
* This variable is then passed to `type_vars_in_term` to extract type variables from the term.
* The `curry` function is used to partially apply `mk_var` to the string "x", effectively creating a function that takes no arguments and returns a term representing the variable `x`.
* The composition `type_vars_in_term o curry mk_var "x"` ensures that the type variables are extracted from the term created by applying `mk_var` to "x".

### Mathematical insight
The `type_tyvars` function is designed to identify the type variables present in a term that represents a variable `x`. This is a fundamental operation in type theory, as it allows for the analysis of the types of variables in a given term. The use of `curry` to partially apply `mk_var` to "x" highlights the functional programming style often employed in HOL Light.

### Dependencies
* `type_vars_in_term`
* `curry`
* `mk_var`

### Porting notes
When translating `type_tyvars` into other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system handles variable creation and type variable extraction. The `curry` function might need to be replaced or reinterpreted, depending on the target system's support for functional programming concepts. Additionally, the string "x" might need to be replaced with a more system-specific representation of a variable name.

---

## find_match

### Name of formal statement
find_match

### Type of the formal statement
new_definition

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
           tmin,tyin
```

### Informal statement
The `find_match` function takes a term `u` and returns a function that, given a term `t`, attempts to match `u` with `t` using `term_match`. If the match fails, it recursively attempts to match `u` with the rator, rand, or the second component of the abstracted term of `t`, until a match is found or all possibilities are exhausted, at which point it fails with the message "find_match".

### Informal sketch
* The definition of `find_match` involves a recursive helper function `find_mt` that attempts to match the input term `u` with a given term `t` using `term_match`.
* If `term_match` fails, `find_mt` recursively tries to match `u` with the rator of `t`, then the rand of `t`, and finally the second component of the abstracted term of `t`.
* The main function returned by `find_match` applies `find_mt` to a term `t` and returns the result of the match, which includes the matched term `tmin` and its type `tyin`.
* The use of `try` and `with Failure _` indicates that the function will catch and handle any failures that occur during the matching process.

### Mathematical insight
The `find_match` function is designed to search for a match between a given term `u` and a term `t` by recursively exploring the structure of `t`. This is a common technique in term rewriting and proof search, where the goal is to find a suitable substitution or transformation that applies to a given term. The function's recursive nature and use of `term_match` suggest that it is intended for use in a proof assistant or automated reasoning system.

### Dependencies
* `term_match`
* `rator`
* `rand`
* `dest_abs`

### Porting notes
When porting `find_match` to another proof assistant, care should be taken to ensure that the recursive structure and failure handling are properly translated. In particular, the use of `try` and `with Failure _` may need to be replaced with equivalent constructs in the target system. Additionally, the `term_match` function and other dependencies will need to be ported or reimplemented in the target system.

---

## rec

### Name of formal statement
rec

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let rec mk_primed_var(name,ty) =
  if can get_const_type name then mk_primed_var(name^"'",ty)
  else mk_var(name,ty);;
```

### Informal statement
The function `mk_primed_var` is defined recursively, taking two parameters: `name` and `ty`. If the `can get_const_type` condition is true for `name`, then `mk_primed_var` calls itself with the argument `name` appended with a prime symbol and the same type `ty`. Otherwise, it constructs a new variable using `mk_var` with the provided `name` and `ty`.

### Informal sketch
* The definition of `mk_primed_var` involves a recursive call based on the condition `can get_const_type name`.
* The base case for the recursion is when `can get_const_type name` is false, at which point `mk_var(name, ty)` is used to create a new variable.
* The recursive case involves appending a prime symbol to `name` and making a recursive call to `mk_primed_var` with this new name and the same type `ty`.
* This process suggests a strategy of iteratively checking and modifying the `name` until it meets the condition for creating a new variable.

### Mathematical insight
The definition of `mk_primed_var` appears to be part of a system for managing or generating unique variable names, possibly in the context of a proof assistant or a system for automated reasoning. The use of recursion and the condition `can get_const_type name` suggests that the system is designed to handle cases where a proposed variable name might already be in use or is otherwise invalid, by iteratively modifying the name until a valid one is found.

### Dependencies
* `can`
* `get_const_type`
* `mk_var`

### Porting notes
When translating `mk_primed_var` into another proof assistant, special attention should be given to how variable names are managed and how recursive functions are defined. The `can get_const_type` condition and the `mk_var` function may need to be adapted or replaced with equivalent constructs in the target system. Additionally, the handling of recursive functions and the specifics of string manipulation (e.g., appending a prime symbol to a name) may vary between systems.

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
  fun ilist slist tm -> fst(subst_occs (zip ilist slist) tm)
```

### Informal statement
The function `subst_occs` takes a list of indices `ilist`, a list of terms `slist`, and a term `tm` as input, and returns the result of substituting the terms in `slist` into `tm` at the corresponding indices in `ilist`. The substitution is performed recursively, handling combinations, abstractions, and variables. The function `aconv` is used to check if a term is convertible to another, and `vsubst` is used to substitute a variable in a term. The `genvar` function generates a fresh variable, and `alpha` is used to rename bound variables.

### Informal sketch
* The function `subst_occs` first partitions the input list `slist` into two lists: `applic` and `noway`, based on whether the terms in `slist` are convertible to the input term `tm`.
* It then processes the `applic` list by partitioning it into two lists: `racts` and `rrest`, based on whether the indices are equal to 1.
* The function then filters out empty lists from `racts` and `rrest`, and applies the `subst` function to the first element of `racts` if it is not empty.
* If `acts` is empty, the function recursively calls itself on the subterms of `tm` if it is a combination or abstraction, or returns `tm` unchanged if it is a variable.
* The function uses `unzip` to separate the indices and terms in `sposs`, and `map` to apply the `subst` function to each term in `trest`.
* The `C (-) 1` function is used to decrement the indices in `trest`.

### Mathematical insight
The `subst_occs` function is a recursive substitution function that handles the substitution of terms into other terms at specific indices. It is designed to work with a variety of term structures, including combinations, abstractions, and variables. The function uses a number of auxiliary functions, such as `aconv`, `vsubst`, `genvar`, and `alpha`, to perform the substitution correctly.

### Dependencies
* `aconv`
* `vsubst`
* `genvar`
* `alpha`
* `subst`
* `is_comb`
* `is_abs`
* `dest_comb`
* `dest_abs`
* `mk_comb`
* `mk_abs`

### Porting notes
When porting this definition to another proof assistant, care should be taken to ensure that the recursive structure of the function is preserved, and that the auxiliary functions are defined correctly. In particular, the `aconv` function, which checks if two terms are convertible, may need to be defined separately. Additionally, the `genvar` function, which generates a fresh variable, may need to be implemented differently depending on the specific proof assistant being used.

---

## INST_TY_TERM(substl,insttyl)

### Name of formal statement
INST_TY_TERM(substl,insttyl)

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let INST_TY_TERM(substl,insttyl) th =
  let th' = INST substl (INST_TYPE insttyl th) in
  if hyp th' = hyp th then th'
  else failwith "INST_TY_TERM: Free term and/or type variables in hypotheses"
```

### Informal statement
Given a theorem `th`, `INST_TY_TERM` applies a substitution `substl` to the terms in `th` after first applying a type instantiation `insttyl` to `th`, provided that the hypotheses of the resulting theorem `th'` are the same as those of the original theorem `th`. If the hypotheses change, it reports an error indicating the presence of free term and/or type variables in the hypotheses.

### Informal sketch
* Apply `INST_TYPE` with `insttyl` to `th` to perform type instantiation.
* Apply `INST` with `substl` to the result of the type instantiation to substitute terms.
* Check if the hypotheses of the resulting theorem `th'` are identical to those of the original theorem `th`.
* If the hypotheses match, return the resulting theorem `th'`; otherwise, report an error due to the presence of free variables in the hypotheses.

### Mathematical insight
This definition is crucial for managing and manipulating theorems in a formal system, particularly when dealing with type and term variables. It ensures that substitutions and instantiations are applied consistently and that any changes to the hypotheses are detected, which is vital for maintaining the soundness of the formal development.

### Dependencies
#### Definitions
* `INST`
* `INST_TYPE`
#### Theorems
* None explicitly mentioned, but the definition relies on the `hyp` function to access the hypotheses of a theorem.

### Porting notes
When translating this definition into another proof assistant, pay attention to how term and type substitutions are handled, as well as how hypotheses are represented and compared. In systems like Lean, Coq, or Isabelle, similar functions for substitution and instantiation exist, but their exact syntax and behavior may differ. Ensure that the ported version correctly checks for and handles changes in hypotheses to maintain the integrity of the formal development.

---

## RIGHT_CONV_RULE

### Name of formal statement
RIGHT_CONV_RULE

### Type of the formal statement
Theorem or definition introducing a conversion rule

### Formal Content
```ocaml
let RIGHT_CONV_RULE (conv:conv) th =
  TRANS th (conv(rhs(concl th)))
```

### Informal statement
The `RIGHT_CONV_RULE` states that for a given conversion `conv` and a theorem `th`, it applies the conversion to the right-hand side of the conclusion of `th` and then transforms `th` using this converted right-hand side.

### Informal sketch
* The `RIGHT_CONV_RULE` applies a given conversion `conv` to the right-hand side (`rhs`) of the conclusion (`concl`) of a theorem `th`.
* It utilizes the `TRANS` function to transform the original theorem `th` based on the conversion applied to its conclusion's right-hand side.
* Key steps involve:
  + Extracting the conclusion of `th` using `concl th`.
  + Isolating the right-hand side of this conclusion with `rhs`.
  + Applying the conversion `conv` to this right-hand side.
  + Using `TRANS` to apply this conversion to `th`, effectively transforming it.

### Mathematical insight
The `RIGHT_CONV_RULE` provides a way to apply conversions to theorems in a targeted manner, specifically altering the right-hand side of a theorem's conclusion. This is useful in proof development for manipulating and simplifying expressions within theorems, facilitating further deductions or proofs.

### Dependencies
- `TRANS`
- `conv`
- `rhs`
- `concl`

### Porting notes
When porting `RIGHT_CONV_RULE` to another proof assistant like Lean, Coq, or Isabelle, pay close attention to how each system handles theorem transformations and conversions. Specifically, understand how to apply a conversion to a part of a theorem (in this case, the right-hand side of the conclusion) and how to transform theorems based on such conversions. The exact implementation may vary significantly between systems, especially in how they represent theorems, conversions, and the application of these conversions to theorem parts.

---

## NOT_EQ_SYM

### Name of formal statement
NOT_EQ_SYM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let NOT_EQ_SYM =
  let pth = GENL [`a:A`; `b:A`]
    (GEN_REWRITE_RULE I [GSYM CONTRAPOS_THM] (DISCH_ALL(SYM(ASSUME`a:A = b`))))
  and aty = `:A` in
  fun th -> try let l,r = dest_eq(dest_neg(concl th)) in
                MP (SPECL [r; l] (INST_TYPE [type_of l,aty] pth)) th
            with Failure _ -> failwith "NOT_EQ_SYM"
```

### Informal statement
For all types `A` and for all `a` and `b` of type `A`, if `a` is not equal to `b`, then `b` is not equal to `a`. This is derived from assuming `a = b`, using the contrapositive, and then applying a general rewrite rule to discharge the assumption and conclude the symmetric property of not equal.

### Informal sketch
* The proof starts by assuming `a = b` and then applies `CONTRAPOS_THM` to derive a contrapositive form.
* It uses `GEN_REWRITE_RULE` with `GSYM` to apply the symmetric property to the equality, effectively turning `a = b` into `b = a`.
* The `DISCH_ALL` and `SYM` tactics are used within `GEN_REWRITE_RULE` to discharge the assumption and apply symmetry.
* The derived theorem `pth` is then instantiated with types and terms to apply to a given `th` (theorem) that concludes a not equal statement.
* The `MP` tactic is used to combine the instantiated `pth` with `th` to derive the conclusion that if `a` is not equal to `b`, then `b` is not equal to `a`.
* The function `NOT_EQ_SYM` attempts to apply this logic to any given theorem `th`, trying to match and apply the symmetric not equal rule.

### Mathematical insight
The `NOT_EQ_SYM` theorem captures the symmetric property of the "not equal" relation. It's essential in formal proofs involving equality and inequality, as it allows for the symmetric application of not equal statements, which is a fundamental property in mathematics.

### Dependencies
* Theorems:
  + `CONTRAPOS_THM`
* Definitions:
  + `GENL`
  + `GEN_REWRITE_RULE`
  + `GSYM`
  + `DISCH_ALL`
  + `SYM`
  + `MP`
  + `SPECL`
  + `INST_TYPE`
* Tactics and functions:
  + `dest_eq`
  + `dest_neg`
  + `concl`
  + `type_of`
  + `failwith`

### Porting notes
When translating `NOT_EQ_SYM` into another proof assistant, pay special attention to how each system handles symmetric properties, contrapositives, and the application of rewrite rules. The use of `GEN_REWRITE_RULE` and `GSYM` might need to be adapted based on the target system's capabilities for handling general rewrite rules and symmetry. Additionally, the error handling mechanism (`failwith`) should be translated appropriately to handle cases where the `NOT_EQ_SYM` application fails.

---

## NOT_MP

### Name of formal statement
NOT_MP

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let NOT_MP thi th =
  try MP thi th with Failure _ ->
  try let t = dest_neg (concl thi) in
      MP(MP (SPEC t F_IMP) thi) th
  with Failure _ -> failwith "NOT_MP"
```

### Informal statement
The `NOT_MP` theorem states that if there exists a hypothesis `thi` and a conclusion `th` such that the modus ponens (`MP`) rule cannot be applied directly to `thi` and `th`, then an attempt is made to apply `MP` by first deriving the negation of the conclusion of `thi` (denoted as `t`) and using the implication introduction rule (`F_IMP`) to introduce the implication. If this attempt also fails, the function raises a failure exception with the message "NOT_MP".

### Informal sketch
* The `NOT_MP` theorem starts by attempting to apply the modus ponens (`MP`) rule to the hypothesis `thi` and conclusion `th`.
* If the initial `MP` application fails, it attempts to derive the negation of the conclusion of `thi` (denoted as `t`) using `dest_neg`.
* It then applies `MP` twice: first to `SPEC t F_IMP` (which is an instantiation of the implication introduction rule `F_IMP` with `t` as the subject) and `thi`, and then to the result of this application and `th`.
* The `SPEC` tactic is used to specialize the `F_IMP` theorem with `t`.
* If any of these steps fail, the function raises a failure exception with the message "NOT_MP".

### Mathematical insight
The `NOT_MP` theorem provides an alternative way to apply modus ponens when the direct application fails, by using implication introduction and specialization. This is useful in situations where the conclusion of the hypothesis is not directly applicable to the desired conclusion, but can be related through an implication.

### Dependencies
* `MP` (modus ponens rule)
* `F_IMP` (implication introduction rule)
* `SPEC` (specialization tactic)
* `dest_neg` (negation derivation function)

### Porting notes
When porting `NOT_MP` to other proof assistants, special attention should be paid to the handling of failures and exceptions, as well as the implementation of the `SPEC` tactic and `dest_neg` function. The `MP` and `F_IMP` rules are likely to have direct counterparts in other systems, but their application and interaction with other tactics may differ. Additionally, the use of `try`-`with` blocks to handle failures may need to be adapted to the target system's error handling mechanisms.

---

## FORALL_EQ

### Name of formal statement
FORALL_EQ

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let FORALL_EQ x =
  let mkall = AP_TERM (mk_const("!",[type_of x,mk_vartype "A"])) in
  fun th -> try mkall (ABS x th)
            with Failure _ -> failwith "FORALL_EQ"
```

### Informal statement
The `FORALL_EQ` function takes a variable `x` and returns a function that attempts to construct a universal quantification of a given theorem `th` over `x`. If successful, it applies the `AP_TERM` function with `mk_const` to create a new term representing the universal quantification, and then applies `ABS` to `x` and `th`. If this construction fails, it raises an exception with the message "FORALL_EQ".

### Informal sketch
* The construction starts by defining an internal function `mkall` that applies `AP_TERM` to create a new term representing universal quantification.
* It then attempts to apply `mkall` to the result of `ABS x th`, which abstracts `x` in the theorem `th`.
* The `try`-`with` block is used to catch any failures during this construction, raising a specific exception if the construction of the universal quantification fails.
* Key HOL Light terms involved include `AP_TERM`, `mk_const`, `ABS`, and the `!` constant for universal quantification.

### Mathematical insight
The `FORALL_EQ` function is designed to automate the construction of universal quantifications in a formal proof development, providing a convenient way to express statements that hold for all values of a given variable. This is a fundamental concept in formal logic and proof assistants, as it allows for the expression of general properties and theorems.

### Dependencies
* `AP_TERM`
* `mk_const`
* `ABS`
* `type_of`
* `mk_vartype`

### Porting notes
When translating `FORALL_EQ` into other proof assistants like Lean, Coq, or Isabelle, special attention should be paid to how each system handles binders and universal quantification. For example, in Lean, the `∀` symbol is used for universal quantification, and binders are handled using the `λ` abstraction. In Coq, universal quantification is also represented using `∀`, and the `fun` keyword is used for abstraction. Understanding these differences is crucial for a correct translation.

---

## EXISTS_EQ

### Name of formal statement
EXISTS_EQ

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let EXISTS_EQ x =
  let mkex = AP_TERM (mk_const("?",[type_of x,mk_vartype "A"])) in
  fun th -> try mkex (ABS x th)
            with Failure _ -> failwith "EXISTS_EQ"
```

### Informal statement
The `EXISTS_EQ` function takes a term `x` and attempts to construct an existential statement using `x` as the witness. It first creates a term `mkex` by applying `AP_TERM` to a constant `?` with type `[type_of x, mk_vartype "A"]`. Then, it tries to apply `mkex` to the abstraction of `x` over the term `th`. If successful, it returns the resulting term; otherwise, it raises a failure exception with the message "EXISTS_EQ".

### Informal sketch
* The construction starts by creating a term `mkex` that represents an existential quantifier `?` with the appropriate type.
* It then attempts to apply `mkex` to the abstraction of `x` over the term `th`, effectively creating an existential statement.
* The use of `AP_TERM` and `ABS` suggests a careful manipulation of terms and binders to achieve the desired existential statement.
* The `try`-`with` block indicates that the construction may fail, in which case it raises an exception.

### Mathematical insight
The `EXISTS_EQ` function is likely used to automate the construction of existential statements in a formal proof development. The use of a constant `?` and the careful manipulation of terms and binders suggests a deliberate attempt to create a canonical representation of existential quantification. This construction is important because it provides a way to uniformly represent and manipulate existential statements, which is a fundamental concept in formal logic.

### Dependencies
* `AP_TERM`
* `mk_const`
* `type_of`
* `mk_vartype`
* `ABS`

### Porting notes
When porting this definition to another proof assistant, care should be taken to replicate the precise manipulation of terms and binders. The use of `AP_TERM` and `ABS` may need to be replaced with equivalent constructs in the target system. Additionally, the exception handling mechanism may need to be adapted to the target system's error handling mechanisms.

---

## SELECT_EQ

### Name of formal statement
SELECT_EQ

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let SELECT_EQ x =
  let mksel = AP_TERM (mk_const("@",[type_of x,mk_vartype "A"])) in
  fun th -> try mksel (ABS x th)
            with Failure _ -> failwith "SELECT_EQ";;
```

### Informal statement
The `SELECT_EQ` function takes an argument `x` and defines an internal function `mksel` that applies the `AP_TERM` constructor to a constant `@` with type `[type_of x, mk_vartype "A"]`. It then attempts to apply `mksel` to the abstraction of `x` over `th`, where `th` is presumably a theorem or a term. If this application fails, it raises a failure exception with the message "SELECT_EQ".

### Informal sketch
* The definition begins by determining the type of `x` and creating a variable type `A`.
* It constructs a constant `@` with a type that depends on `x` and `A`.
* The function `mksel` is defined to apply `AP_TERM` to this constant and the type of `x` and `A`.
* The main function attempts to apply `mksel` to an abstraction involving `x` and `th`, handling potential failures.
* Key HOL Light terms involved include `AP_TERM`, `mk_const`, `type_of`, `mk_vartype`, and `ABS`.

### Mathematical insight
The `SELECT_EQ` function appears to be involved in constructing or manipulating terms within a specific context, possibly related to selecting or applying a term to an abstraction. The use of `AP_TERM` and abstraction suggests a connection to lambda calculus or higher-order logic. Understanding the purpose of `SELECT_EQ` requires insight into the broader context of the formal development, including the roles of `@`, `x`, and `th`.

### Dependencies
* **Definitions:**
  - `AP_TERM`
  - `mk_const`
  - `type_of`
  - `mk_vartype`
  - `ABS`
* **Theorems/Axioms:**
  None explicitly mentioned, but the construction implies dependencies on underlying type theory and lambda calculus principles.

### Porting notes
When translating `SELECT_EQ` into another proof assistant, special attention should be paid to how that system handles abstraction, application, and type manipulation. The `AP_TERM` and `ABS` constructs may have direct analogs, but their behavior and any associated tactics or theorems will need to be carefully matched. Additionally, error handling mechanisms similar to `try`-`with` in OCaml may differ, requiring adjustments to manage potential failures during term construction.

---

## RIGHT_BETA

### Name of formal statement
RIGHT_BETA

### Type of the formal statement
Theorem/tactic definition

### Formal Content
```ocaml
let RIGHT_BETA th =
  try TRANS th (BETA_CONV(rhs(concl th)))
  with Failure _ -> failwith "RIGHT_BETA"
```

### Informal statement
The `RIGHT_BETA` theorem or tactic applies a transformation to a given theorem `th` by first attempting to apply the `TRANS` tactic to `th` combined with the result of applying `BETA_CONV` to the right-hand side (or conclusion) of `th`. If this application fails, it raises an exception with the message "RIGHT_BETA".

### Informal sketch
* The tactic starts with a given theorem `th`.
* It attempts to apply the `BETA_CONV` conversion to the right-hand side (or conclusion) of `th`, denoted as `rhs(concl th)`.
* The result of this conversion is then combined with `th` using the `TRANS` tactic.
* If the application of `TRANS` with the converted right-hand side fails, the tactic raises a failure exception.

### Mathematical insight
The `RIGHT_BETA` tactic seems to be designed to apply beta conversion to the conclusion of a theorem and then combine this with a transitivity step, possibly to simplify or transform the theorem into a more useful form. Beta conversion is a fundamental concept in lambda calculus and type theory, representing the reduction of a beta redex (a function applied to an argument). This tactic's purpose might be to automate certain simplification steps in proofs involving lambda terms or functional expressions.

### Dependencies
* `TRANS`
* `BETA_CONV`
* `rhs`
* `concl`

### Porting notes
When porting `RIGHT_BETA` to another proof assistant like Lean, Coq, or Isabelle, special attention should be given to how each system handles beta conversion and tactical applications. For example, in Lean, one might use the `beta` tactic for beta reduction, while in Coq, the `cbv` tactic could be used for call-by-value beta reduction. Understanding the equivalent tactics and conversions in the target system is crucial for a successful port. Additionally, the exception handling mechanism might differ, requiring adjustments to how failures are managed during tactic application.

---

## rec

### Name of formal statement
rec

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let rec LIST_BETA_CONV tm =
  try let rat,rnd = dest_comb tm in
      RIGHT_BETA(AP_THM(LIST_BETA_CONV rat)rnd)
  with Failure _ -> REFL tm;;
```

### Informal statement
The function `LIST_BETA_CONV` is defined recursively as follows: for any term `tm`, it attempts to decompose `tm` into `rat` and `rnd` using `dest_comb`. If successful, it applies `RIGHT_BETA` to the result of applying `AP_THM` to `LIST_BETA_CONV rat` and `rnd`. If the decomposition fails, it returns `REFL tm`.

### Informal sketch
* The definition of `LIST_BETA_CONV` is recursive, implying that it can be applied to terms of arbitrary complexity.
* The `try`-`with` block indicates that the function first attempts to apply `dest_comb` to the input term `tm`, which suggests that `tm` is expected to be a composite term.
* The use of `AP_THM` and `RIGHT_BETA` indicates that the function is working with beta-reduction, a fundamental concept in lambda calculus.
* The `Failure` handler suggests that not all terms can be decomposed by `dest_comb`, and in such cases, the function defaults to applying `REFL`, which likely represents a reflexive operation.

### Mathematical insight
The `LIST_BETA_CONV` function appears to be designed to perform beta-reduction on terms in a specific context, possibly related to lists or recursive data structures. The recursive nature and the use of `dest_comb` and `AP_THM` suggest that it's tailored for terms that can be broken down into simpler components, facilitating the application of beta-reduction rules. This function is likely crucial in proofs involving the manipulation of such terms, providing a systematic way to simplify expressions.

### Dependencies
* `dest_comb`
* `RIGHT_BETA`
* `AP_THM`
* `REFL`

### Porting notes
When translating `LIST_BETA_CONV` into another proof assistant, special attention should be given to the handling of recursive functions and the representation of terms. The `try`-`with` block may need to be translated into an equivalent error-handling mechanism in the target system. Additionally, the porting process should ensure that the `AP_THM` and `RIGHT_BETA` operations are correctly implemented, as these are crucial for the beta-reduction process. Differences in how binders are handled between HOL Light and the target system may also require careful consideration.

---

## RIGHT_LIST_BETA

### Name of formal statement
RIGHT_LIST_BETA

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let RIGHT_LIST_BETA th = TRANS th (LIST_BETA_CONV(snd(dest_eq(concl th))));
```

### Informal statement
For a given theorem `th`, `RIGHT_LIST_BETA` applies a transformation `TRANS` to `th` with the `LIST_BETA_CONV` conversion applied to the second component of the equation conclusion of `th`, effectively transforming the right-hand side of the list beta equality.

### Informal sketch
* The proof involves applying the `TRANS` tactic to a given theorem `th`.
* It utilizes the `LIST_BETA_CONV` conversion, which is applied to the second component (`snd`) of the equation conclusion (`concl th`) of the theorem, obtained by `dest_eq`.
* This process transforms the right-hand side of the list beta equality, leveraging the `LIST_BETA_CONV` to potentially simplify or normalize the list expressions involved.
* The `TRANS` tactic is then applied to the original theorem `th` with this modified conclusion, effectively creating a new theorem with the transformed right-hand side.

### Mathematical insight
The `RIGHT_LIST_BETA` theorem appears to be part of a development involving list theory and beta reductions. It provides a way to transform theorems by applying list beta conversions to their conclusions, specifically targeting the right-hand side of equations. This is likely important for simplifying expressions or proving properties about lists in a formal setting.

### Dependencies
- `TRANS`
- `LIST_BETA_CONV`
- `dest_eq`
- `concl`
- `snd`

### Porting notes
When translating `RIGHT_LIST_BETA` into another proof assistant, pay attention to how list beta conversions and theorem transformations are handled. The equivalent of `TRANS` and `LIST_BETA_CONV` needs to be identified in the target system. Additionally, the way equations are represented and manipulated (e.g., `dest_eq`, `concl`, `snd`) might differ and require careful handling to ensure the ported version accurately reflects the original theorem's behavior.

---

## LIST_CONJ

### Name of formal statement
LIST_CONJ

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let LIST_CONJ = end_itlist CONJ ;;
```

### Informal statement
The function `LIST_CONJ` is defined as the result of applying `end_itlist` to `CONJ`, where `end_itlist` is a higher-order function that applies a given binary operation to a list of elements in a cumulative way from left to right, and `CONJ` denotes conjunction.

### Informal sketch
* The definition involves applying `end_itlist` to `CONJ`, which suggests a cumulative conjunction operation over a list of propositions.
* The `end_itlist` function is typically used to apply a binary operation to all items in a list, going from left to right, and `CONJ` represents logical conjunction.
* This implies that `LIST_CONJ` takes a list of propositions as input and returns a single proposition that is the conjunction of all the propositions in the list.

### Mathematical insight
The `LIST_CONJ` definition provides a way to express the conjunction of a list of propositions in a compact form, which is useful in formal proofs involving multiple conditions or assumptions that all need to be true.

### Dependencies
* `end_itlist`
* `CONJ`

### Porting notes
When porting `LIST_CONJ` to another proof assistant, ensure that an equivalent of `end_itlist` is available or can be defined. Also, note that the handling of lists and higher-order functions may differ between systems, requiring adjustments to the definition or its application.

---

## rec

### Name of formal statement
rec

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let rec CONJ_LIST n th =
  try if n=1 then [th] else (CONJUNCT1 th)::(CONJ_LIST (n-1) (CONJUNCT2 th))
  with Failure _ -> failwith "CONJ_LIST";;
```

### Informal statement
The function `CONJ_LIST` takes two arguments, `n` and `th`, and recursively constructs a list of conjuncts. If `n` equals 1, it returns a list containing `th`. Otherwise, it prepends the first conjunct of `th` to the list of conjuncts of the second conjunct of `th`, obtained by recursively calling `CONJ_LIST` with `n-1` and the second conjunct of `th`. If any failure occurs during this process, it raises an exception with the message "CONJ_LIST".

### Informal sketch
* The definition of `CONJ_LIST` is recursive, with a base case when `n` equals 1.
* In the recursive case, `CONJ_LIST` applies `CONJUNCT1` and `CONJUNCT2` to `th` to extract the first and second conjuncts, respectively.
* The function then recursively calls itself with `n-1` and the second conjunct of `th`, effectively unwrapping the conjunctions.
* The use of `try` and `with Failure _` indicates that the function may fail and provides a custom error message.

### Mathematical insight
The `CONJ_LIST` function appears to be designed to flatten a nested conjunction into a list of individual conjuncts. This is a useful operation in formal proof systems, where conjunctions are often used to represent multiple assumptions or conclusions. By providing a way to extract and manipulate individual conjuncts, `CONJ_LIST` enables more flexible reasoning and proof construction.

### Dependencies
* `CONJUNCT1`
* `CONJUNCT2`

### Porting notes
When porting `CONJ_LIST` to another proof assistant, attention should be paid to the handling of recursive functions, exception mechanisms, and the specific representations of conjunctions and lists. For example, in a system like Coq, one might use a `Fixpoint` definition for the recursion, while in Lean, a `def` with a recursive equation could be used. Additionally, the error handling mechanism may differ, requiring adjustments to the `try`-`with` block.

---

## rec

### Name of formal statement
rec

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let rec BODY_CONJUNCTS th =
  if is_forall(concl th) then
    BODY_CONJUNCTS (SPEC_ALL th) else
  if is_conj (concl th) then
      BODY_CONJUNCTS (CONJUNCT1 th) @ BODY_CONJUNCTS (CONJUNCT2 th)
  else [th]
```

### Informal statement
The function `BODY_CONJUNCTS` takes a theorem `th` and recursively returns a list of theorems. If the conclusion of `th` is a universal quantification, it applies `SPEC_ALL` to `th` and recursively calls `BODY_CONJUNCTS` on the result. If the conclusion of `th` is a conjunction, it recursively calls `BODY_CONJUNCTS` on the first and second conjuncts of `th` and concatenates the results. Otherwise, it returns a list containing `th`.

### Informal sketch
* If the theorem `th` has a conclusion that is a `forall` statement, `BODY_CONJUNCTS` recursively processes the theorem after applying `SPEC_ALL` to remove the quantifier.
* If the conclusion of `th` is a conjunction, `BODY_CONJUNCTS` breaks it down into its `CONJUNCT1` and `CONJUNCT2` parts and recursively processes each, combining the results.
* For any other form of theorem, `BODY_CONJUNCTS` simply returns the theorem as is, wrapped in a list.

### Mathematical insight
The `BODY_CONJUNCTS` function appears to be designed to flatten or normalize theorems by handling quantifiers and conjunctions in a structured way, ensuring that theorems are broken down into their most basic, usable forms. This process is crucial in automated reasoning and proof construction, where theorems need to be manipulated and applied in a systematic manner.

### Dependencies
* `is_forall`
* `is_conj`
* `concl`
* `SPEC_ALL`
* `CONJUNCT1`
* `CONJUNCT2`

### Porting notes
When translating `BODY_CONJUNCTS` into another proof assistant, special attention should be given to how quantifiers and conjunctions are handled, as these may differ between systems. For example, in systems like Lean or Coq, the equivalent of `SPEC_ALL` and the treatment of `forall` and conjunction may involve different tactics or built-in functions. Additionally, the recursive nature of `BODY_CONJUNCTS` should be preserved, but the exact implementation may vary based on the target system's support for recursive functions and list manipulation.

---

## rec

### Name of formal statement
rec

### Type of the formal statement
new_definition

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
    else [th]
```

### Informal statement
The function `IMP_CANON` takes a theorem `th` and recursively applies transformations based on the conclusion `w` of `th`. If `w` is a conjunction, `IMP_CANON` is applied to the first and second conjuncts of `th`. If `w` is an implication, it is further analyzed: if the antecedent is a conjunction, `IMP_CANON` is applied after discharging the conjuncts and applying `NOT_MP` with the conjunction of the assumptions. If the antecedent is a disjunction, `IMP_CANON` is applied to each disjunct after discharging and applying `NOT_MP` with the disjunction of assumptions. For existential antecedents, `IMP_CANON` is applied after discharging the body of the existential statement and applying `NOT_MP` with the existential assumption. If the antecedent does not fit these cases, `IMP_CANON` is applied after discharging the antecedent. If `w` is a universal statement, `IMP_CANON` is applied to the theorem with all variables specialized. Otherwise, the theorem is returned as is.

### Informal sketch
* If the conclusion of the theorem is a conjunction, apply `IMP_CANON` to each conjunct.
* For implications:
  + If the antecedent is a conjunction, apply `DISCH` to each conjunct, then `NOT_MP` with the conjunction of the assumptions.
  + If the antecedent is a disjunction, apply `DISCH` to each disjunct and `NOT_MP` with the disjunction of assumptions.
  + If the antecedent is an existential statement, apply `DISCH` to the body of the existential statement and `NOT_MP` with the existential assumption.
  + Otherwise, apply `DISCH` to the antecedent and proceed.
* If the conclusion is a universal statement, apply `SPEC_ALL` to the theorem before proceeding.
* The process involves recursive application of `IMP_CANON`, using tactics like `CONJUNCT1`, `CONJUNCT2`, `DISCH`, `NOT_MP`, `CONJ`, `DISJ1`, `DISJ2`, `EXISTS`, and `SPEC_ALL` to transform the theorem.

### Mathematical insight
The `IMP_CANON` function appears to be designed to transform theorems into a canonical form, particularly focusing on implications and handling of quantifiers and logical connectives. It seems to apply various logical rules to simplify or normalize the theorem, potentially for use in further proofs or to make the theorem more amenable to automated reasoning systems. The function's recursive nature and use of specific tactics like `NOT_MP` and `DISCH` suggest it is tailored to work within the constraints of a formal proof system.

### Dependencies
#### Theorems and definitions
* `CONJUNCT1`
* `CONJUNCT2`
* `DISCH`
* `NOT_MP`
* `CONJ`
* `DISJ1`
* `DISJ2`
* `EXISTS`
* `SPEC_ALL`
* `UNDISCH`
* `ASSUME`
* `is_conj`
* `is_imp`
* `is_disj`
* `is_exists`
* `is_forall`
* `dest_neg_imp`
* `dest_conj`
* `dest_disj`
* `dest_exists`
* `variant`
* `thm_frees`
* `subst`

---

## LIST_MP

### Name of formal statement
LIST_MP

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let LIST_MP  = rev_itlist (fun x y -> MP y x);;
```

### Informal statement
LIST_MP is defined as the reverse iteration of the list, applying the function that takes two arguments x and y and returns the result of MP (Modus Ponens) applied to y and x.

### Informal sketch
* The definition of LIST_MP involves reversing the order of a list using `rev_itlist`.
* The `rev_itlist` function applies a given function to each element of the list in reverse order, accumulating the results.
* In this case, the given function is `fun x y -> MP y x`, which applies Modus Ponens to `y` and `x`.
* The `MP` function likely represents a basic inference rule in propositional logic, where `MP P Q` means "from `P` implies `Q` and `P`, infer `Q`".
* The overall effect of LIST_MP is to apply this Modus Ponens rule in a cumulative manner over the reversed list, effectively chaining the implications.

### Mathematical insight
The LIST_MP definition provides a way to iteratively apply Modus Ponens to a list of propositions in reverse order, which can be useful in constructing proofs that involve a series of implications. This definition likely plays a role in formalizing logical arguments or proofs within the HOL Light system.

### Dependencies
* `rev_itlist`
* `MP`

### Porting notes
When translating LIST_MP into another proof assistant, ensure that the equivalent of `rev_itlist` and `MP` are defined and properly understood. Note that the handling of lists and iteration may differ between systems, and the Modus Ponens rule may be implemented under a different name or with slightly different syntax. Additionally, the use of higher-order functions (like `fun x y -> MP y x`) may require special handling in some proof assistants.

---

## DISJ_IMP

### Name of formal statement
DISJ_IMP

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DISJ_IMP =
  let pth = TAUT`!t1 t2. t1 \/ t2 ==> ~t1 ==> t2` in
  fun th ->
    try let a,b = dest_disj(concl th) in MP (SPECL [a;b] pth) th
    with Failure _ -> failwith "DISJ_IMP"
```

### Informal statement
For all propositions `t1` and `t2`, if `t1` or `t2` is true and `t1` is false, then `t2` is true. Specifically, given a theorem `th` whose conclusion is a disjunction, if the first disjunct is false, then the second disjunct must be true.

### Informal sketch
* The theorem `DISJ_IMP` is proved by applying the `TAUT` theorem, which states a basic property of disjunction and implication.
* The `SPECL` tactic is used to specialize this `TAUT` theorem with the specific disjuncts `a` and `b` from the conclusion of the input theorem `th`.
* The `MP` tactic (modus ponens) is then applied to derive the conclusion that if the first disjunct `a` is false, then the second disjunct `b` must be true.
* If the conclusion of `th` is not a disjunction, the `dest_disj` function will fail, and the tactic will raise an exception.

### Mathematical insight
The `DISJ_IMP` theorem captures a fundamental property of classical logic, allowing us to infer the truth of one disjunct given the falsity of the other. This is crucial in many proofs where cases need to be analyzed based on the truth of certain conditions.

### Dependencies
* `TAUT`: a theorem capturing basic tautologies
* `MP`: modus ponens, a fundamental inference rule
* `SPECL`: a tactic for specializing theorems with specific terms
* `dest_disj`: a function for decomposing disjunctions

### Porting notes
When translating `DISJ_IMP` into another proof assistant, pay close attention to how disjunctions and implications are handled, as well as the specifics of modus ponens and term specialization. In systems like Lean or Coq, the equivalent of `TAUT` and `MP` may be built-in or derived early in the development, while `SPECL` and `dest_disj` might be tactics or functions that need to be defined or imported from a library.

---

## IMP_ELIM

### Name of formal statement
IMP_ELIM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let IMP_ELIM =
  let pth = TAUT`!t1 t2. (t1 ==> t2) ==> ~t1 \/ t2` in
  fun th ->
    try let a,b = dest_imp(concl th) in MP (SPECL [a;b] pth) th
    with Failure _ -> failwith "IMP_ELIM"
```

### Informal statement
For all propositions `t1` and `t2`, if `t1` implies `t2`, then either not `t1` or `t2`. This is used to define a function `IMP_ELIM` that takes a theorem `th` and attempts to apply modus ponens (`MP`) with a specialized instance of the tautology `!t1 t2. (t1 ==> t2) ==> ~t1 \/ t2`, where `t1` and `t2` are derived from the conclusion of `th` by decomposing an implication (`dest_imp`), or fails with an exception if this decomposition fails.

### Informal sketch
* The proof starts with a tautology `!t1 t2. (t1 ==> t2) ==> ~t1 \/ t2`, which is a fundamental property of implication in classical logic.
* Given a theorem `th`, it attempts to decompose the conclusion of `th` into two parts `a` and `b` such that `a` implies `b` (`dest_imp(concl th)`).
* If successful, it applies modus ponens (`MP`) with a specialized instance of the tautology, where `a` and `b` are used to instantiate `t1` and `t2`.
* The use of `SPECL [a;b] pth` indicates the specialization of the tautology with `a` and `b`.
* If the decomposition of the conclusion into an implication fails, the function raises an exception.

### Mathematical insight
This theorem and its proof embody a fundamental principle of classical logic, relating implication to disjunction and negation. The `IMP_ELIM` function provides a mechanized way to apply this principle in proofs, leveraging the `MP` (modus ponens) rule and a tautology that captures the essence of implication elimination. This is crucial for constructing and automating proofs in a formal system.

### Dependencies
* `TAUT`
* `MP`
* `SPECL`
* `dest_imp`

### Porting notes
When translating `IMP_ELIM` into another proof assistant, pay close attention to how implications are handled and how modus ponens is applied. The `dest_imp` function, which decomposes a proposition into its antecedent and consequent, might need to be replaced with an equivalent function in the target system. Additionally, the exception handling mechanism may differ, requiring adjustments to how failures are managed during proof construction.

---

## DISJ_CASES_UNION

### Name of formal statement
DISJ_CASES_UNION

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let DISJ_CASES_UNION dth ath bth =
    DISJ_CASES dth (DISJ1 ath (concl bth)) (DISJ2 (concl ath) bth)
```

### Informal statement
The `DISJ_CASES_UNION` definition takes three arguments: `dth`, `ath`, and `bth`, and applies the `DISJ_CASES` function to `dth`, `DISJ1` of `ath` and the conclusion of `bth`, and `DISJ2` of the conclusion of `ath` and `bth`.

### Informal sketch
* The definition begins with `dth` as the primary argument to `DISJ_CASES`.
* It constructs two disjuncts: 
  + The first disjunct is `DISJ1` applied to `ath` and the conclusion of `bth`.
  + The second disjunct is `DISJ2` applied to the conclusion of `ath` and `bth`.
* These disjuncts are then passed to `DISJ_CASES` along with `dth`.

### Mathematical insight
The `DISJ_CASES_UNION` definition appears to be a specialized application of case analysis for disjunctions, combining two separate disjunctive statements (`ath` and `bth`) under a common `DISJ_CASES` framework. This is likely used to handle proofs involving compound disjunctions in a structured manner.

### Dependencies
* `DISJ_CASES`
* `DISJ1`
* `DISJ2`
* `concl`

### Porting notes
When translating `DISJ_CASES_UNION` into another proof assistant, ensure that the target system supports similar higher-order functions and case analysis mechanisms. Pay particular attention to how disjunctions are represented and manipulated, as well as how conclusions are extracted from theorems (`concl` function). Additionally, verify that the target system's `DISJ_CASES`, `DISJ1`, and `DISJ2` equivalents behave similarly to their HOL Light counterparts.

---

## MK_ABS

### Name of formal statement
MK_ABS

### Type of the formal statement
new_definition

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
The `MK_ABS` function takes a theorem `qth` and attempts to construct a new theorem by applying a series of transformations. It first extracts the bound variable `ov` from the conclusion of `qth`, then decomposes `qth` into a variable `bv` and a theorem `rth` using `SPEC_VAR`. It constructs a new theorem `sth` by applying the `ABS` operator to `bv` and `rth`. The function then applies an alpha-conversion `cnv` to `ov` and uses `CONV_RULE` with `BINOP_CONV` to transform `sth`. If any part of this process fails, it raises a failure exception with the message "MK_ABS".

### Informal sketch
* Extract the bound variable `ov` from the conclusion of the input theorem `qth` using `bndvar` and `rand` functions.
* Decompose `qth` into a variable `bv` and a theorem `rth` using the `SPEC_VAR` function.
* Construct a new theorem `sth` by applying the `ABS` operator to `bv` and `rth`.
* Apply an alpha-conversion `cnv` to `ov` using `ALPHA_CONV`.
* Use `CONV_RULE` with `BINOP_CONV` to transform `sth`.
* Handle potential failures by catching exceptions and raising a failure with the message "MK_ABS".

### Mathematical insight
The `MK_ABS` function appears to be constructing an abstracted version of a given theorem, handling the binding of variables and applying appropriate conversions to ensure the result is well-formed. This is a common operation in formal systems, where theorems need to be manipulated and transformed to fit into different contexts or to apply specific rules.

### Dependencies
* `bndvar`
* `rand`
* `concl`
* `SPEC_VAR`
* `ABS`
* `ALPHA_CONV`
* `CONV_RULE`
* `BINOP_CONV`

### Porting notes
When translating `MK_ABS` into other proof assistants, special attention should be paid to how binders and variables are handled, as well as the specifics of conversion rules and tactics. The `ALPHA_CONV` and `BINOP_CONV` may have direct analogs in other systems, but their application and the overall strategy of `MK_ABS` will need to be adapted to the target system's primitives and tactics.

---

## HALF_MK_ABS

### Name of formal statement
HALF_MK_ABS

### Type of the formal statement
Theorem/Definition

### Formal Content
```ocaml
let HALF_MK_ABS th =
  try let th1 = MK_ABS th in
      CONV_RULE(LAND_CONV ETA_CONV) th1
  with Failure _ -> failwith "HALF_MK_ABS";;
```

### Informal statement
The function `HALF_MK_ABS` takes a theorem `th` and attempts to apply `MK_ABS` to it, then applies a conversion rule using `LAND_CONV` and `ETA_CONV` to the result. If any part of this process fails, it raises an exception with the message "HALF_MK_ABS".

### Informal sketch
* The process begins with the input theorem `th`.
* It attempts to apply `MK_ABS` to `th`, which presumably involves some form of abstraction.
* The result of this abstraction, `th1`, is then subject to a conversion rule that applies `LAND_CONV` and `ETA_CONV`. This step likely aims to normalize or simplify the expression in a way that is useful for further reasoning.
* The specific use of `LAND_CONV` and `ETA_CONV` suggests that the conversion involves logical and possibly eta-expansion/contraction rules, which are common in proof assistants for manipulating terms involving logical connectives and functions.
* If any step of this process fails, an exception is raised, indicating that the `HALF_MK_ABS` operation could not be successfully applied to the input theorem.

### Mathematical insight
The `HALF_MK_ABS` function appears to be part of a larger system for manipulating theorems, possibly in the context of predicate logic or a similar formal system. The application of `MK_ABS` followed by specific conversion rules suggests a strategy for preparing theorems for further use, such as proving other theorems or applying them in a proof. The exception handling indicates that not all theorems may be amenable to this treatment, possibly due to their form or content.

### Dependencies
* `MK_ABS`
* `LAND_CONV`
* `ETA_CONV`
* `CONV_RULE`

### Porting notes
When translating `HALF_MK_ABS` into another proof assistant, careful attention should be paid to how that system handles theorem manipulation, abstraction, and conversion rules. The exact equivalents of `MK_ABS`, `LAND_CONV`, and `ETA_CONV` will need to be identified or implemented. Additionally, the exception handling mechanism may need to be adapted to the target system's error handling conventions. Differences in how binders are handled and how automation is applied may also require special consideration to ensure that the ported version of `HALF_MK_ABS` behaves as expected.

---

## MK_EXISTS

### Name of formal statement
MK_EXISTS

### Type of the formal statement
Theorem/Definition

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
The `MK_EXISTS` function takes a theorem `qth` and attempts to construct a new theorem. It first identifies the bound variable `ov` in the conclusion of `qth`. Then, it extracts a bound variable `bv` and a theorem `rth` from `qth` using `SPEC_VAR`. It constructs a new theorem `sth` by applying the `EXISTS_EQ` rule to `bv` and `rth`. The function then applies a conversion `cnv` generated by `GEN_ALPHA_CONV` to `ov`, and uses `BINOP_CONV` to convert `sth`. If any part of this process fails, it raises a failure exception with the message "MK_EXISTS".

### Informal sketch
* Identify the bound variable in the conclusion of the input theorem `qth`.
* Extract a specific variable and theorem from `qth` using `SPEC_VAR`.
* Apply the `EXISTS_EQ` rule to the extracted variable and theorem.
* Generate a conversion using `GEN_ALPHA_CONV` based on the bound variable.
* Apply this conversion to the new theorem using `BINOP_CONV`.
* Handle any failures by raising an exception.

### Mathematical insight
The `MK_EXISTS` function appears to be designed to manipulate theorems involving existential quantification, specifically to transform them into a form where the existential quantifier is applied to an equality. This is a common step in formal proofs, especially when working with quantifiers and equalities. The function's use of `GEN_ALPHA_CONV` suggests it is also concerned with alpha-conversion, which is a process of renaming bound variables to avoid clashes, indicating its role in maintaining the hygiene of variable names in proofs.

### Dependencies
* `bndvar`
* `rand`
* `concl`
* `SPEC_VAR`
* `EXISTS_EQ`
* `GEN_ALPHA_CONV`
* `BINOP_CONV`
* `CONV_RULE`

### Porting notes
When porting `MK_EXISTS` to another proof assistant, special attention should be given to how that system handles existential quantification, alpha-conversion, and theorem manipulation. The equivalent of `GEN_ALPHA_CONV` and `BINOP_CONV` may need to be identified or implemented. Additionally, error handling mechanisms similar to the `try`/`with` block may need to be used to manage failures during the theorem construction process. Differences in how binders are handled and the specific tactics or rules available for manipulating quantifiers and equalities will also need to be considered.

---

## LIST_MK_EXISTS

### Name of formal statement
LIST_MK_EXISTS

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let LIST_MK_EXISTS l th = itlist (fun x th -> MK_EXISTS(GEN x th)) l th;;
```

### Informal statement
For a list `l` and a theorem `th`, `LIST_MK_EXISTS` applies `MK_EXISTS` to each element `x` in `l` and `th`, effectively creating a new theorem that asserts the existence of `x` such that `th` holds, for all elements in `l`.

### Informal sketch
* The definition starts with a list `l` and a theorem `th`.
* It uses `itlist` to apply a function to each element of `l` and accumulate the results.
* For each element `x` in `l`, the function `fun x th -> MK_EXISTS(GEN x th)` is applied, which:
  + Uses `GEN` to generalize `x` in `th`.
  + Applies `MK_EXISTS` to assert the existence of `x` such that the generalized `th` holds.
* The results of these applications are accumulated to form the final theorem.

### Mathematical insight
`LIST_MK_EXISTS` provides a way to construct a theorem that asserts the existence of elements in a list satisfying a given property, by applying existential quantification to each element. This is useful in formalizing proofs that involve the existence of objects with certain properties.

### Dependencies
* `itlist`
* `MK_EXISTS`
* `GEN`

### Porting notes
When porting `LIST_MK_EXISTS` to another proof assistant, note that the `itlist` function may need to be replaced with an equivalent fold or map operation. Additionally, the `MK_EXISTS` and `GEN` functions may have different names or require different syntax in the target system. Care should be taken to preserve the logical structure and quantifier scope.

---

## IMP_CONJ

### Name of formal statement
IMP_CONJ

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let IMP_CONJ th1 th2 =
  let A1,C1 = dest_imp (concl th1) and A2,C2 = dest_imp (concl th2) in
  let a1,a2 = CONJ_PAIR (ASSUME (mk_conj(A1,A2))) in
      DISCH (mk_conj(A1,A2)) (CONJ (MP th1 a1) (MP th2 a2))
```

### Informal statement
Given two theorems `th1` and `th2` of the form `A1 → C1` and `A2 → C2`, respectively, `IMP_CONJ th1 th2` is a theorem of the form `(A1 ∧ A2) → (C1 ∧ C2)`, derived by applying modus ponens (`MP`) to each theorem with assumptions `A1` and `A2` conjoined, and then conjoining the results.

### Informal sketch
* First, extract the antecedents `A1` and `A2` and the consequents `C1` and `C2` from the conclusions of `th1` and `th2`, respectively, using `dest_imp`.
* Assume the conjunction `A1 ∧ A2` and derive two assumptions `a1` and `a2` from this conjunction using `CONJ_PAIR` and `ASSUME`.
* Apply modus ponens (`MP`) to `th1` with `a1` and to `th2` with `a2`, yielding `C1` and `C2`, respectively.
* Conjoin the results `C1` and `C2` using `CONJ` to form the conclusion `(C1 ∧ C2)`.
* Discharge the assumption `A1 ∧ A2` using `DISCH` to obtain the final theorem `(A1 ∧ A2) → (C1 ∧ C2)`.

### Mathematical insight
`IMP_CONJ` is a theorem that allows combining two implications into a single implication where the antecedents and consequents are conjoined. This is useful for combining separate conditions and conclusions into a single statement, which can be particularly helpful in proofs involving multiple premises or when constructing complex logical arguments.

### Dependencies
* `dest_imp`
* `CONJ_PAIR`
* `ASSUME`
* `MP`
* `CONJ`
* `DISCH`
* `mk_conj`

### Porting notes
When translating `IMP_CONJ` into another proof assistant, pay close attention to how implications and conjunctions are handled, as well as the specifics of assumption and discharge mechanisms. The `CONJ_PAIR` and `dest_imp` functions may have direct analogs, but the way assumptions are managed and theorems are constructed could vary significantly between systems.

---

## EXISTS_IMP

### Name of formal statement
EXISTS_IMP

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let EXISTS_IMP x =
  if not (is_var x) then failwith "EXISTS_IMP: first argument not a variable"
  else fun th ->
         try let ante,cncl = dest_imp(concl th) in
             let th1 = EXISTS (mk_exists(x,cncl),x) (UNDISCH th) in
             let asm = mk_exists(x,ante) in
             DISCH asm (CHOOSE (x,ASSUME asm) th1)
         with Failure _ -> failwith "EXISTS_IMP: variable free in assumptions"
```

### Informal statement
Given a variable `x`, if the conclusion of a theorem `th` is an implication, then there exists an `x` such that the antecedent of the implication implies the consequent of the implication, under the assumption that `x` exists. Formally, if `th` is a theorem of the form `P -> Q`, then `EXISTS x. P -> EXISTS x. Q`, where `x` is not free in the assumptions of `th`.

### Informal sketch
* Start with a theorem `th` and check if its conclusion is an implication using `dest_imp`.
* Extract the antecedent and consequent of the implication.
* Apply the `EXISTS` rule to introduce an existential quantifier for `x` in the consequent.
* Use `UNDISCH` to remove any discharged assumptions from `th`.
* Create a new assumption `asm` that `x` exists such that the antecedent holds.
* Apply the `CHOOSE` tactic to select a witness for `x` that satisfies the assumption `asm`.
* Discharge the assumption `asm` using `DISCH` to obtain the final theorem.

### Mathematical insight
This theorem provides a way to transform a theorem about an implication into a theorem about the existence of a witness that satisfies the implication. It is a key step in formalizing proofs that involve existential quantification and implications.

### Dependencies
* `EXISTS`
* `UNDISCH`
* `CHOOSE`
* `DISCH`
* `dest_imp`
* `mk_exists`
* `is_var`

### Porting notes
When porting this theorem to another proof assistant, pay attention to the handling of existential quantification and implications. The `EXISTS` rule and `CHOOSE` tactic may need to be replaced with equivalent constructs in the target system. Additionally, the `UNDISCH` and `DISCH` tactics may need to be adapted to the target system's assumption management.

---

## CONJUNCTS_CONV

### Name of formal statement
CONJUNCTS_CONV

### Type of the formal statement
Theorem

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
  with Failure _ -> failwith "CONJUNCTS_CONV"
```

### Informal statement
The `CONJUNCTS_CONV` theorem takes two terms `t1` and `t2` and applies a conversion to prove a statement about the conjunction of these terms. Specifically, it attempts to apply the `IMP_ANTISYM_RULE` to prove that `t1` implies `t2` and `t2` implies `t1`, by constructing a conjunction of the consequences of assuming `t1` and `t2` separately, using the `build_conj` function to recursively break down the conjunctions.

### Informal sketch
* The `build_conj` function is defined recursively to break down a term `t` into its conjuncts `l` and `r`, and apply itself to these conjuncts.
* If `t` is not a conjunction, `build_conj` attempts to find a theorem `th` in the list `thl` whose conclusion is `t`.
* The main proof applies `IMP_ANTISYM_RULE` to prove the equivalence of `t1` and `t2` by constructing the conjunction of the consequences of assuming `t1` and `t2` separately.
* The `CONJUNCTS` function is used to get the list of conjuncts of a theorem, and `ASSUME` is used to create a theorem from a term.
* The `DISCH` tactic is used to discharge assumptions.

### Mathematical insight
The `CONJUNCTS_CONV` theorem provides a way to prove the equivalence of two terms by constructing a conjunction of their consequences. This is useful in situations where the equivalence of two terms needs to be established, and the terms can be broken down into their conjuncts. The theorem relies on the `IMP_ANTISYM_RULE`, which proves that two terms are equivalent if they imply each other.

### Dependencies
* `CONJUNCTS`
* `ASSUME`
* `IMP_ANTISYM_RULE`
* `DISCH`
* `dest_conj`
* `CONJ`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to replicate the recursive `build_conj` function and the application of `IMP_ANTISYM_RULE`. The `CONJUNCTS` function and `ASSUME` tactic may need to be replaced with equivalent constructs in the target system. Additionally, the `DISCH` tactic and `dest_conj` function may need to be reimplemented or replaced with similar tactics in the target system.

---

## CONJ_SET_CONV

### Name of formal statement
CONJ_SET_CONV

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let CONJ_SET_CONV l1 l2 =
  try CONJUNCTS_CONV (list_mk_conj l1, list_mk_conj l2)
  with Failure _ -> failwith "CONJ_SET_CONV";;
```

### Informal statement
The function `CONJ_SET_CONV` takes two lists of formulas `l1` and `l2` and attempts to apply the `CONJUNCTS_CONV` conversion to the conjunction of the formulas in `l1` and `l2`. If this application fails, it raises an exception with the message "CONJ_SET_CONV".

### Informal sketch
* The function `CONJ_SET_CONV` is defined to take two lists of formulas `l1` and `l2`.
* It first constructs the conjunction of the formulas in `l1` and `l2` using `list_mk_conj`.
* Then, it attempts to apply the `CONJUNCTS_CONV` conversion to the resulting conjunctions.
* If the application of `CONJUNCTS_CONV` fails, the function raises an exception with the message "CONJ_SET_CONV", indicating that the conversion was unsuccessful.

### Mathematical insight
The `CONJ_SET_CONV` function appears to be a utility for working with sets of formulas in conjunction, providing a way to convert or manipulate these sets using the `CONJUNCTS_CONV` conversion. This is likely used in a broader context of automated reasoning or proof search, where manipulating sets of formulas is a common task.

### Dependencies
* `CONJUNCTS_CONV`
* `list_mk_conj`
* `failwith`

### Porting notes
When porting this definition to another proof assistant, special attention should be given to how exceptions are handled, as the `try`-`with` block may not have a direct equivalent. Additionally, the `CONJUNCTS_CONV` and `list_mk_conj` functions will need to be defined or imported in the target system. The `failwith` function may also need to be replaced with an equivalent exception-raising mechanism in the target proof assistant.

---

## FRONT_CONJ_CONV

### Name of formal statement
FRONT_CONJ_CONV

### Type of the formal statement
Theorem/Conversion Rule

### Formal Content
```ocaml
let FRONT_CONJ_CONV tml t =
  let rec remove x l =
    if hd l = x then tl l else (hd l)::(remove x (tl l)) in
  try CONJ_SET_CONV tml (t::(remove t tml))
  with Failure _ -> failwith "FRONT_CONJ_CONV"
```

### Informal statement
This conversion rule takes a term `t` and a list of terms `tml` as input. It attempts to apply the `CONJ_SET_CONV` conversion to the list `tml` with `t` prepended, after removing the first occurrence of `t` from `tml`. If successful, it returns the result; otherwise, it raises a failure exception.

### Informal sketch
* The rule defines a recursive function `remove` to delete the first occurrence of a term `x` from a list `l`.
* It then attempts to apply `CONJ_SET_CONV` to the modified list with `t` prepended, after removing the first occurrence of `t` from `tml`.
* The `try`-`with` block is used to catch and handle any failure that might occur during the application of `CONJ_SET_CONV`.
* Key HOL Light terms involved include `CONJ_SET_CONV` and the `remove` function.

### Mathematical insight
This conversion rule appears to be designed to simplify or normalize conjunctions in a term by moving a specified term to the front of the conjunction and removing any duplicate occurrence of that term. It is likely used in a larger proof strategy to rearrange terms for easier manipulation or to prepare them for application of other rules or theorems.

### Dependencies
* `CONJ_SET_CONV`
* Basic list operations (`hd`, `tl`, `::`)

### Porting notes
When translating this rule into another proof assistant, special attention should be given to how that system handles recursive functions (like `remove`), term manipulation, and exception handling. The equivalent of `CONJ_SET_CONV` must also be identified or implemented in the target system. Additionally, the porting process may require adjustments due to differences in how terms and conversions are represented and applied between HOL Light and the target proof assistant.

---

## CONJ_DISCH

### Name of formal statement
CONJ_DISCH

### Type of the formal statement
Theorem

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
For all propositions `t`, `t1`, and `t2`, if `t` implies that `t1` is equivalent to `t2`, then `t` and `t1` being true is equivalent to `t` and `t2` being true. This is used to discharge a conjunction in a proof, given a theorem `th` concluding `t1 = t2`, to derive a new theorem where `t1` and `t2` are replaced by each other in the context of `t`.

### Informal sketch
* The `CONJ_DISCH` function takes a proposition `t` and a theorem `th` as input.
* It attempts to decompose the conclusion of `th` into an equality `t1 = t2` using `dest_eq`.
* If successful, it applies the `MP` (modus ponens) tactic to a specialized version of the `TAUT` (tautology) `pth`, which states the equivalence of `t /\ t1` and `t /\ t2` given `t` implies `t1 <=> t2`.
* The `SPECL` tactic is used to specialize `pth` with `t`, `t1`, and `t2`.
* The `DISCH` tactic is applied to `t` and `th` to discharge the assumption `t` in the context of the theorem.
* If any step fails, it raises a failure exception with the message "CONJ_DISCH".

### Mathematical insight
This theorem is crucial for managing conjunctions in proofs, allowing for the substitution of equivalent propositions within a conjunctive context. It reflects a fundamental property of logical equivalence and conjunction, enabling the manipulation of complex statements in a proof.

### Dependencies
* `TAUT`
* `MP`
* `SPECL`
* `DISCH`
* `dest_eq`

### Porting notes
When translating `CONJ_DISCH` into another proof assistant, pay special attention to how conjunction and equivalence are handled, as well as the specifics of the proof tactics (`MP`, `SPECL`, `DISCH`) and their equivalents in the target system. The `TAUT` definition and the `dest_eq` function may also require careful translation to ensure they match the target system's logic and tactic language.

---

## rec

### Name of formal statement
rec

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let rec CONJ_DISCHL l th =
  if l = [] then th else CONJ_DISCH (hd l) (CONJ_DISCHL (tl l) th)
```

### Informal statement
The function `CONJ_DISCHL` is defined recursively as follows: it takes a list `l` and a theorem `th` as input, and if the list `l` is empty, it returns the theorem `th`. Otherwise, it applies the `CONJ_DISCH` function to the head of the list `l` and the result of recursively calling `CONJ_DISCHL` on the tail of the list `l` and the theorem `th`.

### Informal sketch
* The definition of `CONJ_DISCHL` is recursive, with a base case where the input list `l` is empty.
* In the recursive case, `CONJ_DISCHL` applies `CONJ_DISCH` to the head of `l` and the result of the recursive call on the tail of `l`.
* The `CONJ_DISCH` function is used to discharge a conjunction, and its application is nested recursively based on the structure of the input list `l`.
* The recursion unfolds until the base case is reached, at which point the theorem `th` is returned.

### Mathematical insight
The `CONJ_DISCHL` function appears to be designed to discharge a list of conjunctions from a theorem, effectively "peeling off" the conjuncts one by one. This is a common operation in formal proof development, where conjunctions are used to combine multiple statements into a single statement. The recursive definition allows `CONJ_DISCHL` to handle lists of arbitrary length.

### Dependencies
* `CONJ_DISCH`
* `hd`
* `tl`

### Porting notes
When porting this definition to another proof assistant, care should be taken to preserve the recursive structure and the application of `CONJ_DISCH`. The `hd` and `tl` functions, which are used to access the head and tail of the list, respectively, may need to be replaced with equivalent functions in the target system. Additionally, the `CONJ_DISCH` function, which is not defined in this excerpt, will need to be ported or defined in the target system as well.

---

## rec

### Name of formal statement
rec

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let rec GSPEC th =
  let wl,w = dest_thm th in
  if is_forall w then
      GSPEC (SPEC (genvar (type_of (fst (dest_forall w)))) th)
  else th
```

### Informal statement
The function `GSPEC` takes a theorem `th` and recursively applies a transformation based on the structure of `th`. If `th` is a universally quantified statement (i.e., of the form `∀x. P(x)`), `GSPEC` applies itself to the result of specializing `th` by generalizing the variable of the correct type from the quantifier, effectively removing the outermost universal quantifier. If `th` is not universally quantified, `GSPEC` returns `th` unchanged.

### Informal sketch
* The function `GSPEC` is defined recursively to handle theorems that may contain nested universal quantifications.
* It first decomposes the input theorem `th` into its components using `dest_thm`.
* If the theorem is universally quantified (as determined by `is_forall`), it extracts the quantified variable's type and uses `genvar` to create a new variable of that type.
* It then applies `SPEC` to specialize the theorem with this new variable, effectively removing the outermost universal quantifier, and recursively calls `GSPEC` on the result.
* If the theorem is not universally quantified, the function simply returns the original theorem.

### Mathematical insight
The `GSPEC` function appears to be designed to strip away outer universal quantifiers from a given theorem, potentially to prepare it for further processing or application in a context where such quantifiers are not desired or are handled differently. This kind of transformation can be crucial in formal proof development, especially when working with higher-order logic or when interfacing with other systems that handle quantification differently.

### Dependencies
* `dest_thm`
* `is_forall`
* `SPEC`
* `genvar`
* `type_of`
* `dest_forall`
* `fst`

### Porting notes
When translating `GSPEC` into another proof assistant, special attention should be paid to how that system handles universal quantification and theorem specialization. The exact implementation of `GSPEC` may vary significantly depending on the target system's support for recursive functions, theorem manipulation primitives, and its type system. For example, in a system like Coq, one might need to define a recursive function using `Fixpoint` or `Function`, while in Lean, a similar function could be defined using recursion or pattern matching. Additionally, the equivalents of `dest_thm`, `is_forall`, `SPEC`, `genvar`, `type_of`, and `dest_forall` must be identified or defined in the target system.

---

## ANTE_CONJ_CONV

### Name of formal statement
ANTE_CONJ_CONV

### Type of the formal statement
Theorem/Conversion Rule

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
Given a term `tm` representing an implication, `ANTE_CONJ_CONV` is a conversion that applies to terms of the form `A1 --> A2 --> C` (where `A1`, `A2`, and `C` are formulas) and transforms them into a form that explicitly shows the conjunction of `A1` and `A2` implying `C`. Specifically, it transforms `A1 --> A2 --> C` into `(A1 ∧ A2) --> C`, leveraging the principle of `IMP_ANTISYM_RULE` for equivalence transformation.

### Informal sketch
* The conversion starts by decomposing the input term `tm` using `dest_imp` to extract the antecedent and consequent parts.
* It then further decomposes the antecedent part (expected to be an implication itself) to obtain two formulas `A1` and `A2`, and a consequent `C`.
* Two implications are constructed:
  + `imp1` is derived from `tm` by assuming `tm` itself and then applying `CONJ` to assume `A1` and `A2` separately, leading to an implication that `A1 ∧ A2` implies `C`.
  + `imp2` involves assuming the conjunction of `A1` and `A2`, then using `CONJUNCT1` and `CONJUNCT2` to separately derive `A1` and `A2`, and finally assuming the implication from `A1` to (`A2` implies `C`).
* `IMP_ANTISYM_RULE` is applied to establish the equivalence between these two constructed implications, effectively transforming the original implication into a form that explicitly conjoins the antecedents.
* The conversion fails with an error message if the input term does not match the expected form.

### Mathematical insight
This conversion is crucial for manipulating and simplifying implications in formal proofs, especially when dealing with nested implications. It leverages basic logical principles such as modus ponens (`MP`), conjunction introduction (`CONJ`), and the antisymmetric property of implication (`IMP_ANTISYM_RULE`) to transform implications into a more manageable form. This is particularly useful in proof assistants for automating or simplifying proof steps involving complex implications.

### Dependencies
* `dest_conj`
* `dest_imp`
* `MP`
* `CONJ`
* `CONJUNCT1`
* `CONJUNCT2`
* `IMP_ANTISYM_RULE`
* `ASSUME`
* `DISCH`
* `LIST_MP`
* `mk_conj`
* `mk_imp`

### Porting notes
When porting this conversion to another proof assistant, pay special attention to how implications and conjunctions are handled, as well as the specific tactics or rules available for manipulating these constructs. The `IMP_ANTISYM_RULE`, in particular, might be represented differently or might require additional lemmas to establish in other systems. Additionally, the error handling mechanism (`with Failure _ -> failwith "ANTE_CONJ_CONV"`) should be adapted to the target system's exception handling mechanisms.

---

## bool_EQ_CONV

### Name of formal statement
bool_EQ_CONV

### Type of the formal statement
Theorem/Conversion rule

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
    with Failure _ -> failwith "bool_EQ_CONV"
```

### Informal statement
This conversion rule `bool_EQ_CONV` is defined for proving equality between boolean terms. It checks if the terms are of type `bool`, then attempts to apply `EQ_CLAUSES` to simplify the equality. If both sides of the equality are the same, it applies `EQT_INTRO` with `REFL`. If one side is `T` (true), it applies the first conjunct of `EQ_CLAUSES` specialized to the other side. If one side is `F` (false), it applies the second conjunct of `EQ_CLAUSES` specialized to the other side. If none of these cases apply, it fails.

### Informal sketch
* The rule starts by checking if both terms of the equality are of type `bool`.
* It then tries to apply `EQ_CLAUSES` to the terms, which are presumably the standard equality axioms for boolean values.
* If the terms are equal, it applies `EQT_INTRO` with `REFL` to prove the equality.
* If one term is `T` and the other is not, it applies the appropriate conjunct of `EQ_CLAUSES` to prove the equality.
* If the terms cannot be proven equal by these methods, the rule fails.
* Key tactics used include `check`, `GEN`, `CONJUNCTS`, `SPEC`, `EQT_INTRO`, and `REFL`.

### Mathematical insight
This conversion rule is designed to simplify equalities between boolean terms by applying standard equality axioms and rules. It provides a basic mechanism for proving equalities in a boolean context, which is fundamental in many logical and mathematical developments. The rule is likely used throughout various proofs involving boolean expressions to reduce them to simpler forms.

### Dependencies
* `EQ_CLAUSES`
* `EQT_INTRO`
* `REFL`
* `GEN`
* `CONJUNCTS`
* `SPEC`
* `check`
* `F_F`
* `dest_eq`

### Porting notes
When translating this rule into another proof assistant, special attention should be given to how boolean types and equality axioms are handled. The `EQ_CLAUSES` and how they are applied may vary between systems. Additionally, the use of `GEN`, `CONJUNCTS`, and `SPEC` might need to be adapted based on the target system's handling of binders and term manipulation. The overall structure of the rule, however, should remain similar, as it follows a straightforward approach to simplifying boolean equalities.

---

## COND_CONV

### Name of formal statement
COND_CONV

### Type of the formal statement
Theorem/Conversion rule

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
  failwith "COND_CONV: can't simplify conditional"
```

### Informal statement
The `COND_CONV` conversion rule takes a term `tm` and attempts to simplify it if it is a conditional statement. If `tm` is not a conditional, it raises an error. Otherwise, it extracts the condition `P` and the terms `u` and `v` from `tm`. If `P` is true (`T`), it applies the `CT` theorem with `u` and `v`. If `P` is false (`F`), it applies the `CF` theorem with `u` and `v`. If `u` and `v` are equal, it applies the `COND_ID` theorem with `P`, `u`, and the type `ty` of `u`. If `u` and `v` are alpha-equivalent, it applies the `COND_ID` theorem with `P`, `u`, and `ty`, and then applies the `TRANS` tactic to the resulting theorem.

### Informal sketch
* The conversion rule `COND_CONV` first checks if the input term `tm` is a conditional statement using `dest_cond`.
* If `tm` is a conditional, it extracts the condition `P` and the terms `u` and `v`.
* It then applies different theorems based on the value of `P` and the relationship between `u` and `v`.
* The `GENL` and `SPECL` functions are used to generate and specialize theorems, respectively.
* The `INST_TYPE` function is used to instantiate theorems with specific types.
* The `aconv` function is used to check if two terms are alpha-equivalent.
* The `AP_TERM` and `ALPHA` functions are used to apply theorems to terms and perform alpha-conversion, respectively.
* The `TRANS` tactic is used to combine theorems.

### Mathematical insight
The `COND_CONV` conversion rule is a powerful tool for simplifying conditional statements in HOL Light. It provides a way to apply different theorems based on the condition and terms involved in the conditional, and can help to reduce the complexity of proofs. The rule is particularly useful when working with conditional statements that involve alpha-equivalent terms.

### Dependencies
* `GENL`
* `SPECL`
* `INST_TYPE`
* `COND_CLAUSES`
* `F_F`
* `COND_ID`
* `AP_TERM`
* `ALPHA`
* `TRANS`
* `aconv`
* `dest_cond` 
* `type_of`
* `rator`

---

## SUBST_MATCH

### Name of formal statement
SUBST_MATCH

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let SUBST_MATCH eqth th =
  let tm_inst,ty_inst = find_match (lhs(concl eqth)) (concl th) in
  SUBS [INST tm_inst (INST_TYPE ty_inst eqth)] th
```

### Informal statement
The `SUBST_MATCH` function takes two arguments, `eqth` and `th`, and returns a new theorem. It first finds a match between the left-hand side of the conclusion of `eqth` and the conclusion of `th` using the `find_match` function, resulting in term and type instantiations `tm_inst` and `ty_inst`. Then, it applies a substitution `SUBS` to `th` with the instantiations `tm_inst` and `ty_inst` applied to `eqth` using `INST` and `INST_TYPE`.

### Informal sketch
* The function `SUBST_MATCH` is defined to take two theorems `eqth` and `th` as input.
* It uses `find_match` to determine how the left-hand side of `eqth`'s conclusion can be matched with `th`'s conclusion, obtaining term and type instantiations.
* These instantiations are then applied to `eqth` using `INST` for terms and `INST_TYPE` for types, effectively creating a specialized version of `eqth`.
* This specialized `eqth` is used in a substitution `SUBS` applied to `th`, resulting in a new theorem.
* The process involves using `INST` and `INST_TYPE` to instantiate `eqth` with the matched terms and types, and then applying this to `th` via `SUBS`.

### Mathematical insight
The `SUBST_MATCH` function is designed to match the left-hand side of an equation theorem `eqth` with the conclusion of another theorem `th`, and then apply the corresponding substitution to `th`. This is useful in automated reasoning for substituting equal terms in theorems, enabling the derivation of new theorems based on established equalities. It reflects a fundamental principle in logic where if `A = B`, then `A` can be substituted for `B` in any statement.

### Dependencies
* `find_match`
* `SUBS`
* `INST`
* `INST_TYPE`
* `lhs`
* `concl`

### Porting notes
When translating `SUBST_MATCH` into another proof assistant, pay special attention to how term and type instantiations are handled, as well as how substitutions are applied to theorems. The `find_match` function, which is crucial for determining the instantiations, may need to be reimplemented or its equivalent found in the target system. Additionally, consider how the target system manages equality theorems and substitutions, as this may affect the direct translation of `SUBS`, `INST`, and `INST_TYPE`.

---

## SUBST

### Name of formal statement
SUBST

### Type of the formal statement
Theorem

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
  MP (rev_itlist (C MP) eqs th4) th
```

### Informal statement
The `SUBST` theorem states that given a list of equations `thl`, a pattern `pat`, and a theorem `th`, it is possible to derive a new theorem by substituting the variables in `pat` with general variables, assuming the equations in `thl` hold, and then discharging the assumptions to obtain a new theorem.

### Informal sketch
* The proof starts by unpacking the input list `thl` into equations `eqs` and variables `vs`.
* It then generates new general variables `gvs` of the same type as `vs` and substitutes these into the pattern `pat` to obtain `gpat`.
* The equations in `eqs` are then processed to extract left-hand sides `ls` and right-hand sides `rs`.
* A list of theorems `ths` is created by assuming the equality of each general variable in `gvs` with its corresponding right-hand side in `rs`.
* The pattern `gpat` is assumed as a theorem `th1`.
* The `SUBS` tactic is applied to `ths` and `th1` to obtain `th2`.
* The assumptions in `ths` are discharged from `th2` to obtain `th3`, and then `th3` is instantiated with `ls` and `gvs` to obtain `th4`.
* Finally, the `MP` tactic is applied to `eqs` and `th4` to obtain the final theorem.

### Mathematical insight
The `SUBST` theorem provides a way to perform substitution in a theorem, which is a fundamental operation in formal reasoning. It allows for the replacement of variables in a theorem with other expressions, which can be useful in a variety of contexts, such as proving equalities or simplifying expressions.

### Dependencies
* `genvar`
* `type_of`
* `subst`
* `dest_eq`
* `concl`
* `ASSUME`
* `mk_eq`
* `SUBS`
* `DISCH`
* `INST`
* `MP`
* `C`
* `rev_itlist`
* `itlist`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the substitution operation is handled correctly, as the specifics of substitution can vary between systems. Additionally, the `MP` tactic and `C` combinator may need to be translated to their equivalents in the target system.

---

## SUBST_CONV

### Name of formal statement
SUBST_CONV

### Type of the formal statement
Theorem/Definition

### Formal Content
```ocaml
let SUBST_CONV thvars template tm =
  let thms,vars = unzip thvars in
  let gvs = map (genvar o type_of) vars in
  let gtemplate = subst (zip gvs vars) template in
  SUBST (zip thms gvs) (mk_eq(template,gtemplate)) (REFL tm)
```

### Informal statement
The `SUBST_CONV` function takes three parameters: `thvars`, `template`, and `tm`. It first unzips `thvars` into two separate lists: `thms` and `vars`. Then, it generates a list of new variables `gvs` by mapping `genvar` composed with `type_of` over `vars`. Next, it substitutes `gvs` for `vars` in `template` to obtain `gtemplate`. Finally, it applies the `SUBST` function to `thms`, `gvs`, and the equation `template = gtemplate`, and applies `REFL` to `tm`.

### Informal sketch
* The function starts by separating the input `thvars` into `thms` and `vars` using `unzip`.
* It then generates new variables `gvs` based on the types of `vars` using `genvar` and `type_of`.
* The `subst` function is used to replace `vars` with `gvs` in `template`, resulting in `gtemplate`.
* The `SUBST` function is applied to `thms`, `gvs`, and the equality `template = gtemplate`.
* Finally, `REFL` is applied to `tm` to obtain the final result.
The key HOL Light terms involved are `unzip`, `genvar`, `type_of`, `subst`, `SUBST`, and `REFL`.

### Mathematical insight
The `SUBST_CONV` function appears to be a tool for substitution in a formal system, allowing the replacement of variables with terms while maintaining the correctness of the statement. This is crucial in formal proof development, where substitutions are a fundamental operation for manipulating and simplifying expressions. The use of `genvar` to generate new variables ensures that the substitution does not inadvertently capture free variables, which is essential for maintaining the soundness of the formal system.

### Dependencies
* `unzip`
* `genvar`
* `type_of`
* `subst`
* `SUBST`
* `REFL`
* `mk_eq`

### Porting notes
When porting `SUBST_CONV` to another proof assistant, special attention should be paid to how variables are managed, especially regarding the generation of new variables and substitution. The exact implementation may vary depending on the target system's handling of binders, variable scopes, and substitution mechanisms. For example, in systems like Lean or Coq, the equivalent of `genvar` and `subst` might be achieved through different tactics or functions, and the `REFL` application might be implicit or require a different formulation.

---

## FILTER_PURE_ASM_REWRITE_RULE

### Name of formal statement
FILTER_PURE_ASM_REWRITE_RULE

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let FILTER_PURE_ASM_REWRITE_RULE f thl th =
    PURE_REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th

and FILTER_ASM_REWRITE_RULE f thl th =
    REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th

and FILTER_PURE_ONCE_ASM_REWRITE_RULE f thl th =
    PURE_ONCE_REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th

and FILTER_ONCE_ASM_REWRITE_RULE f thl th =
    ONCE_REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th
```

### Informal statement
These definitions introduce four new rules for rewriting theorems based on filtered assumptions. Given a function `f`, a list of theorems `thl`, and a theorem `th`, the rules apply rewriting using filtered assumptions from `th`. Specifically, `FILTER_PURE_ASM_REWRITE_RULE`, `FILTER_ASM_REWRITE_RULE`, `FILTER_PURE_ONCE_ASM_REWRITE_RULE`, and `FILTER_ONCE_ASM_REWRITE_RULE` apply `PURE_REWRITE_RULE`, `REWRITE_RULE`, `PURE_ONCE_REWRITE_RULE`, and `ONCE_REWRITE_RULE` respectively, using assumptions from `th` that pass the filter `f`, combined with the theorems in `thl`.

### Informal sketch
* The process starts with a theorem `th` and a function `f` that filters assumptions.
* The `hyp th` function is used to get the hypotheses (assumptions) of `th`.
* The `filter f` function is applied to these hypotheses to select a subset that satisfy the condition `f`.
* The selected hypotheses are then wrapped in `ASSUME` and combined with a list of theorems `thl` using the `@` operator.
* This combined list of theorems and assumptions is then used in one of four rewriting rules:
  + `PURE_REWRITE_RULE` for `FILTER_PURE_ASM_REWRITE_RULE`
  + `REWRITE_RULE` for `FILTER_ASM_REWRITE_RULE`
  + `PURE_ONCE_REWRITE_RULE` for `FILTER_PURE_ONCE_ASM_REWRITE_RULE`
  + `ONCE_REWRITE_RULE` for `FILTER_ONCE_ASM_REWRITE_RULE`
* Each rewriting rule applies its specific rewriting strategy to the theorem `th` using the prepared list of theorems and assumptions.

### Mathematical insight
These definitions provide a way to selectively apply rewriting rules to theorems based on specific assumptions. This can be useful in controlling the application of rewriting rules in complex proofs, where not all assumptions are relevant or where the order of application matters. The use of a filter function `f` allows for flexible and dynamic selection of assumptions, making these rules powerful tools in theorem proving.

### Dependencies
* `PURE_REWRITE_RULE`
* `REWRITE_RULE`
* `PURE_ONCE_REWRITE_RULE`
* `ONCE_REWRITE_RULE`
* `ASSUME`
* `filter`
* `hyp`
* `map`
* `@` 

### Porting notes
When translating these definitions into other proof assistants, consider the following:
* The equivalent of `filter` and `map` functions may need to be used to apply the filter `f` to the hypotheses of a theorem.
* The `ASSUME` function may have a different counterpart in other systems, which wraps a proposition as an assumption.
* Rewriting rules (`PURE_REWRITE_RULE`, `REWRITE_RULE`, etc.) and their application may vary between systems, requiring careful translation.
* The `@` operator for list concatenation is likely to have a direct equivalent in other functional programming languages used in proof assistants.

---

## (FILTER_PURE_ASM_REWRITE_TAC:

### Name of formal statement
FILTER_PURE_ASM_REWRITE_TAC, FILTER_ASM_REWRITE_TAC, FILTER_PURE_ONCE_ASM_REWRITE_TAC, FILTER_ONCE_ASM_REWRITE_TAC

### Type of the formal statement
new_definition

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
    ONCE_REWRITE_TAC (filter (f o concl) (map snd asl) @ thl) (asl,w)
```

### Informal statement
These definitions describe four tactics for rewriting terms in a proof assistant, specifically `FILTER_PURE_ASM_REWRITE_TAC`, `FILTER_ASM_REWRITE_TAC`, `FILTER_PURE_ONCE_ASM_REWRITE_TAC`, and `FILTER_ONCE_ASM_REWRITE_TAC`. Each tactic takes a function `f` of type `term -> bool` and a list of theorems `thl`, and applies a rewriting strategy to a given assertion `asl` and a goal `w`. The `filter` function is used to select terms from the assertion `asl` based on the function `f` composed with `concl`, which presumably extracts the conclusion of a term, and then combines these selected terms with the provided list of theorems `thl` to guide the rewriting process.

### Informal sketch
* The process starts by defining four tactics, each corresponding to a different rewriting strategy: `PURE_REWRITE_TAC`, `REWRITE_TAC`, `PURE_ONCE_REWRITE_TAC`, and `ONCE_REWRITE_TAC`.
* For each tactic, a function `f` is applied to filter terms from the assertion list `asl` based on whether the conclusion of each term satisfies `f`.
* The filtered terms are then combined with a list of theorems `thl` to form a set of rewriting rules.
* The tactic then applies the corresponding rewriting strategy (`PURE_REWRITE_TAC`, `REWRITE_TAC`, `PURE_ONCE_REWRITE_TAC`, or `ONCE_REWRITE_TAC`) using the combined set of rewriting rules to the goal `w`.
* The key difference between these tactics lies in their rewriting strategies, with `PURE_REWRITE_TAC` and `PURE_ONCE_REWRITE_TAC` applying `pure` rewriting, and `REWRITE_TAC` and `ONCE_REWRITE_TAC` applying a more general form of rewriting, and between applying the rewriting strategy once or repeatedly.

### Mathematical insight
These tactics are designed to facilitate automated reasoning by strategically applying rewriting rules to prove or simplify goals in a proof assistant. The use of a filtering function `f` allows for selective application of rewriting rules based on the structure or properties of the terms involved, which can significantly impact the efficiency and effectiveness of the proof search. The distinction between `pure` and general rewriting, as well as the option to apply the rewriting once or repeatedly, provides flexibility in handling different types of proofs and theories.

### Dependencies
* `PURE_REWRITE_TAC`
* `REWRITE_TAC`
* `PURE_ONCE_REWRITE_TAC`
* `ONCE_REWRITE_TAC`
* `filter`
* `concl`
* `map`
* `@` (list concatenation operator)

### Porting notes
When translating these tactics into another proof assistant, special attention should be paid to how rewriting strategies are implemented and how terms are filtered and selected for rewriting. The exact implementation of `PURE_REWRITE_TAC`, `REWRITE_TAC`, `PURE_ONCE_REWRITE_TAC`, and `ONCE_REWRITE_TAC` may differ between systems, requiring adjustments to the tactic definitions. Additionally, the `filter` function and list operations (`map`, `@`) should be translated according to the target system's standard library or programming language.

---

## (X_CASES_THENL:

### Name of formal statement
X_CASES_THENL

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let (X_CASES_THENL: term list list -> thm_tactic list -> thm_tactic) =
  fun varsl ttacl ->
    end_itlist DISJ_CASES_THEN2
       (map (fun (vars,ttac) -> EVERY_TCL (map X_CHOOSE_THEN vars) ttac)
        (zip varsl ttacl))
```

### Informal statement
The `X_CASES_THENL` definition takes two arguments: a list of lists of terms (`varsl`) and a list of theorem tactics (`ttacl`). It applies `DISJ_CASES_THEN2` to the result of mapping a function over the zipped `varsl` and `ttacl`. This function applies `EVERY_TCL` to the result of mapping `X_CHOOSE_THEN` over the terms (`vars`) paired with a theorem tactic (`ttac`).

### Informal sketch
* The definition starts by zipping the list of term lists (`varsl`) with the list of theorem tactics (`ttacl`), creating pairs of terms and tactics.
* For each pair, it maps `X_CHOOSE_THEN` over the terms, effectively applying this tactic to each term.
* The results of this mapping are then wrapped in `EVERY_TCL`, which applies the tactics to every subgoal.
* The `DISJ_CASES_THEN2` tactic is applied to the list of these wrapped tactics, effectively handling disjunctive cases.

### Mathematical insight
The `X_CASES_THENL` definition appears to be a tactical for handling cases in a proof, specifically designed to work with disjunctions and to apply a tactic to every subgoal that arises from considering different cases. This is useful in proofs that involve breaking down a statement into multiple cases and applying a uniform approach to each.

### Dependencies
* `DISJ_CASES_THEN2`
* `EVERY_TCL`
* `X_CHOOSE_THEN`
* `end_itlist`
* `map`
* `zip`

### Porting notes
When translating `X_CASES_THENL` into another proof assistant, pay close attention to how that system handles tacticals, especially those involving disjunctions and application to every subgoal. The exact implementation of `DISJ_CASES_THEN2`, `EVERY_TCL`, and `X_CHOOSE_THEN` will need to be understood and potentially reimplemented in the target system. Additionally, consider how the target system handles the mapping and zipping operations, as these are crucial for the correct application of tactics to terms in the definition.

---

## (X_CASES_THEN:

### Name of formal statement
X_CASES_THEN

### Type of the formal statement
Theorem/tactical definition

### Formal Content
```ocaml
let (X_CASES_THEN: term list list -> thm_tactical) =
  fun varsl ttac ->
    end_itlist DISJ_CASES_THEN2
       (map (fun vars -> EVERY_TCL (map X_CHOOSE_THEN vars) ttac) varsl)
```

### Informal statement
The `X_CASES_THEN` tactical is a function that takes a list of lists of terms and a tactic, and applies a specific transformation to produce a theorem. It maps over each list of terms, applying `X_CHOOSE_THEN` to each term and then `EVERY_TCL` to the results, before combining these with `DISJ_CASES_THEN2` and finally applying `end_itlist`.

### Informal sketch
* The process starts with a list of lists of terms (`varsl`) and a tactic (`ttac`).
* For each list of terms, `X_CHOOSE_THEN` is applied to each term, and then `EVERY_TCL` is applied to the resulting theorems, effectively applying the tactic `ttac` to each of them.
* The results from each list are then combined using `DISJ_CASES_THEN2`, which suggests a disjunctive case analysis.
* The `end_itlist` function is used to consume the list of results, implying a fold or accumulation of the theorems produced by the tactical application.
* Key HOL Light terms involved include `X_CHOOSE_THEN`, `EVERY_TCL`, `DISJ_CASES_THEN2`, and `end_itlist`, indicating a structured approach to case analysis and theorem construction.

### Mathematical insight
The `X_CASES_THEN` tactical appears to be designed for structured case analysis in proofs, particularly where cases are defined by terms and require the application of a specific tactic to each case. This is useful in proofs that involve considering multiple, distinct scenarios defined by the terms in `varsl`. The tactical enables a systematic approach to handling such cases, ensuring that each is addressed appropriately and that the resulting theorems are properly combined.

### Dependencies
* `X_CHOOSE_THEN`
* `EVERY_TCL`
* `DISJ_CASES_THEN2`
* `end_itlist`

### Porting notes
When translating `X_CASES_THEN` into another proof assistant, special attention should be given to how case analysis and tactical application are handled. The equivalent of `end_itlist` and the mapping/combinator functions may differ, and the treatment of disjunctive cases (`DISJ_CASES_THEN2`) could vary between systems. Additionally, the porting process should ensure that the logic and structure of the original tactical are preserved, potentially requiring adjustments to accommodate differences in how terms, tactics, and theorems are represented and manipulated in the target system.

---

## (CASES_THENL:

### Name of formal statement
CASES_THENL

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let (CASES_THENL: thm_tactic list -> thm_tactic) =
  fun ttacl -> end_itlist DISJ_CASES_THEN2 (map (REPEAT_TCL CHOOSE_THEN) ttacl);;
```

### Informal statement
The `CASES_THENL` function takes a list of theorem tactics and returns a new theorem tactic. It applies the `CHOOSE_THEN` tactic repeatedly to each tactic in the input list, then combines the results using `DISJ_CASES_THEN2`.

### Informal sketch
* The function `CASES_THENL` starts with a list of theorem tactics `ttacl`.
* It applies the `REPEAT_TCL` tactic to `CHOOSE_THEN` for each tactic in `ttacl`, effectively repeating the `CHOOSE_THEN` tactic.
* The results of these repeated applications are then combined using `end_itlist` with `DISJ_CASES_THEN2`, which applies `DISJ_CASES_THEN2` to the list of results, effectively combining them into a single tactic.
* This process allows for a flexible and dynamic application of `CHOOSE_THEN` followed by `DISJ_CASES_THEN2`, enabling the handling of multiple cases in a theorem proof.

### Mathematical insight
The `CASES_THENL` definition provides a way to automate the process of handling multiple cases in a proof by repeatedly applying the `CHOOSE_THEN` tactic and then combining the results. This is particularly useful in proofs that involve disjunctions or case analyses, where the ability to systematically apply tactics to each case can simplify the proof process.

### Dependencies
* `thm_tactic`
* `DISJ_CASES_THEN2`
* `REPEAT_TCL`
* `CHOOSE_THEN`

### Porting notes
When translating `CASES_THENL` into another proof assistant, note that the `end_itlist` and `map` functions may need to be replaced with equivalent constructs. Additionally, the `REPEAT_TCL` and `CHOOSE_THEN` tactics may have different names or behaviors in other systems, requiring careful attention to ensure correct translation.

---

## (DISCARD_TAC:

### Name of formal statement
DISCARD_TAC

### Type of the formal statement
Theorem/tactic definition

### Formal Content
```ocaml
let (DISCARD_TAC: thm_tactic) =
  let truth = `T` in
  fun th (asl,w) ->
    if exists (aconv (concl th)) (truth::(map (concl o snd) asl))
    then ALL_TAC (asl,w)
    else failwith "DISCARD_TAC"
```

### Informal statement
The `DISCARD_TAC` tactic is defined as a function that takes a theorem `th` and a pair `(asl, w)` as input, where `asl` is a list of assumptions and `w` is the goal to be proven. It checks if the conclusion of `th` is syntactically equivalent to the constant true proposition `T` or if it appears as the conclusion of any of the assumptions in `asl`. If such a condition is met, it applies the `ALL_TAC` tactic to `(asl, w)`, effectively doing nothing and returning the original goal. Otherwise, it fails with an error message "DISCARD_TAC".

### Informal sketch
* The tactic `DISCARD_TAC` is designed to handle theorems or goals that are already true or can be directly inferred from the assumptions.
* It first defines a constant `truth` as the true proposition `T`.
* The tactic then checks for the existence of the conclusion of the input theorem `th` among the conclusions of the assumptions in `asl` (after converting them to a list of conclusions) or if it is directly `T`.
* If the condition is satisfied, it applies `ALL_TAC`, which does not modify the goal, effectively treating the theorem as already proven or discardable without affecting the proof search.
* The use of `aconv` suggests a check for alpha-convertibility, ensuring that the comparison between the conclusion of `th` and the truths in `asl` is done modulo variable renaming.
* If the condition is not met, the tactic fails, indicating that it cannot apply its simplification.

### Mathematical insight
The `DISCARD_TAC` tactic is a simple yet useful tool in proof development, allowing for the simplification of proofs by recognizing and eliminating trivial or already established truths. It relies on the basic principle of not altering the proof state when the goal is already known to be true or directly inferable from given assumptions. This tactic can be part of a larger strategy to streamline proofs, making them more efficient and easier to manage.

### Dependencies
* `ALL_TAC`
* `aconv`
* `concl`
* `map`
* `snd`
* `exists`

### Porting notes
When translating `DISCARD_TAC` into other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system handles tactics, particularly those that manipulate or inspect the proof state directly. The concept of `aconv` for alpha-convertibility and the application of tactics like `ALL_TAC` may need to be adapted to the target system's equivalents. Additionally, consider the differences in how assumptions and goals are represented and manipulated in the target proof assistant.

---

## (CHECK_ASSUME_TAC:

### Name of formal statement
CHECK_ASSUME_TAC

### Type of the formal statement
Theorem/tactic definition

### Formal Content
```ocaml
let (CHECK_ASSUME_TAC: thm_tactic) =
  fun gth ->
    FIRST [CONTR_TAC gth;  ACCEPT_TAC gth;
           DISCARD_TAC gth; ASSUME_TAC gth]
```

### Informal statement
This defines a tactic `CHECK_ASSUME_TAC` that takes a goal theorem `gth` and attempts to apply a series of tactics to it. The tactic tries to apply `CONTR_TAC`, `ACCEPT_TAC`, `DISCARD_TAC`, and `ASSUME_TAC` in sequence until one succeeds.

### Informal sketch
* The tactic `CHECK_ASSUME_TAC` is defined to handle a goal theorem `gth`.
* It uses the `FIRST` combinator to attempt a sequence of tactics:
  + `CONTR_TAC gth` attempts to prove the goal by contradiction.
  + `ACCEPT_TAC gth` attempts to accept the current goal as a fact.
  + `DISCARD_TAC gth` attempts to discard the current goal.
  + `ASSUME_TAC gth` attempts to assume the current goal as a premise.
* The tactic stops and succeeds as soon as one of these tactics applies.

### Mathematical insight
This tactic seems to be designed for situations where a goal can be resolved by either proving it directly, assuming it as a premise, or discarding it, possibly in the context of proof search or automated reasoning. The `CHECK_ASSUME_TAC` tactic provides a simple, sequential approach to handling such goals, reflecting a basic strategy in automated theorem proving.

### Dependencies
* `CONTR_TAC`
* `ACCEPT_TAC`
* `DISCARD_TAC`
* `ASSUME_TAC`
* `FIRST`

### Porting notes
When translating `CHECK_ASSUME_TAC` into another proof assistant, consider the following:
* Identify equivalent tactics for `CONTR_TAC`, `ACCEPT_TAC`, `DISCARD_TAC`, and `ASSUME_TAC`.
* Understand how the target system handles tactic composition and sequencing, as the `FIRST` combinator may have a direct equivalent or need to be emulated.
* Pay attention to how goals and theorems are represented and manipulated, as this may affect how `gth` is passed to and processed by each tactic.

---

## (FILTER_GEN_TAC:

### Name of formal statement
FILTER_GEN_TAC

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let (FILTER_GEN_TAC: term -> tactic) =
  fun tm (asl,w) ->
    if is_forall w && not (tm = fst(dest_forall w)) then
        GEN_TAC (asl,w)
    else failwith "FILTER_GEN_TAC"
```

### Informal statement
The `FILTER_GEN_TAC` function takes a term `tm` and returns a tactic that applies to an assumption list `asl` and a goal `w`. If the goal `w` is a universal statement (i.e., `is_forall w` is true) and the term `tm` is not equal to the body of the universal statement (i.e., `tm` is not equal to `fst(dest_forall w)`), then the tactic applies the `GEN_TAC` tactic to `asl` and `w`. Otherwise, it fails with the message "FILTER_GEN_TAC".

### Informal sketch
* The `FILTER_GEN_TAC` tactic checks if the goal is a universal statement and if the given term is not the body of that statement.
* If both conditions are met, it applies the `GEN_TAC` tactic, which is typically used for generalizing a variable in the context.
* The use of `is_forall` and `dest_forall` indicates that this tactic is specifically designed to handle universal quantification.
* The comparison `tm = fst(dest_forall w)` ensures that the term `tm` is not the same as the quantified variable, suggesting a mechanism to prevent inappropriate generalization.

### Mathematical insight
The `FILTER_GEN_TAC` tactic seems to be designed to control the application of generalization in a proof, ensuring that it only generalizes over terms that are not the body of a universal statement. This could be important in maintaining the soundness of proofs by preventing over-generalization, which might lead to incorrect conclusions.

### Dependencies
* `GEN_TAC`
* `is_forall`
* `dest_forall`

### Porting notes
When translating `FILTER_GEN_TAC` into another proof assistant, one should pay close attention to how that system handles universal quantification and generalization. The equivalent of `GEN_TAC` and the predicates `is_forall` and `dest_forall` will need to be identified or implemented. Additionally, the handling of terms and tactics may differ, requiring careful consideration of how to replicate the logic of `FILTER_GEN_TAC` in the target system.

---

## (FILTER_DISCH_THEN:

### Name of formal statement
FILTER_DISCH_THEN

### Type of the formal statement
Theorem/tactic definition

### Formal Content
```ocaml
let (FILTER_DISCH_THEN: thm_tactic -> term -> tactic) =
  fun ttac tm (asl,w) ->
    if is_neg_imp w && not (free_in tm (fst(dest_neg_imp w))) then
      DISCH_THEN ttac (asl,w)
    else failwith "FILTER_DISCH_THEN"
```

### Informal statement
FILTER_DISCH_THEN is a tactic that takes a theorem tactic `ttac` and a term `tm`, and applies `DISCH_THEN` to the assumption list `asl` and the goal `w` if `w` is a negated implication and `tm` is not free in the antecedent of `w`.

### Informal sketch
* The tactic `FILTER_DISCH_THEN` checks if the current goal `w` is a negated implication using `is_neg_imp`.
* If `w` is a negated implication, it extracts the antecedent of `w` using `fst(dest_neg_imp w)`.
* It then checks if the term `tm` is not free in the extracted antecedent using `not (free_in tm ...)`.
* If both conditions are met, it applies the `DISCH_THEN` tactic to the assumption list `asl` and the goal `w` with the provided theorem tactic `ttac`.
* If the conditions are not met, it fails with an error message "FILTER_DISCH_THEN".

### Mathematical insight
The `FILTER_DISCH_THEN` tactic is designed to strategically apply the `DISCH_THEN` tactic in a way that respects the logical structure of the goal, specifically targeting negated implications where the term `tm` does not occur in the antecedent. This selective application can be crucial in managing the proof search space and avoiding unnecessary or unproductive branches in the proof tree.

### Dependencies
* `DISCH_THEN`
* `is_neg_imp`
* `dest_neg_imp`
* `free_in`

### Porting notes
When translating `FILTER_DISCH_THEN` into other proof assistants, pay close attention to how each system handles negated implications and the application of tactics. The equivalent of `DISCH_THEN` and the conditional checks may vary, requiring adjustments to match the target system's tactic language and logical framework. Additionally, the error handling mechanism (`failwith`) should be translated into the target system's equivalent error reporting mechanism.

---

## FILTER_STRIP_THEN

### Name of formal statement
FILTER_STRIP_THEN

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let FILTER_STRIP_THEN ttac tm =
  FIRST [FILTER_GEN_TAC tm; FILTER_DISCH_THEN ttac tm; CONJ_TAC]
```

### Informal statement
The `FILTER_STRIP_THEN` function takes two arguments, `ttac` and `tm`, and applies a sequence of tactics to transform a goal. Specifically, it first applies `FILTER_GEN_TAC` to `tm`, then applies `FILTER_DISCH_THEN` to `ttac` and `tm`, and finally applies `CONJ_TAC`.

### Informal sketch
* The function `FILTER_STRIP_THEN` is defined as a composition of three tactics: 
  * `FILTER_GEN_TAC tm` is applied to generate a new subgoal
  * `FILTER_DISCH_THEN ttac tm` is applied to discharge assumptions in the subgoal
  * `CONJ_TAC` is applied to split the subgoal into two separate subgoals
* The `FIRST` combinator is used to apply the first successful tactic in the list

### Mathematical insight
The `FILTER_STRIP_THEN` function appears to be a strategy for simplifying or transforming proof goals, likely in the context of a specific proof or derivation. The use of `FILTER_GEN_TAC` and `FILTER_DISCH_THEN` suggests that it is designed to handle assumptions or hypotheses in a goal, while `CONJ_TAC` is used to split the goal into separate subgoals.

### Dependencies
* `FILTER_GEN_TAC`
* `FILTER_DISCH_THEN`
* `CONJ_TAC`

### Porting notes
When porting this definition to another proof assistant, note that the `FIRST` combinator and the specific tactics used (`FILTER_GEN_TAC`, `FILTER_DISCH_THEN`, `CONJ_TAC`) may need to be translated or reimplemented. Additionally, the handling of assumptions and subgoals may differ between systems, requiring careful attention to the underlying logic and proof structure.

---

## FILTER_DISCH_TAC

### Name of formal statement
FILTER_DISCH_TAC

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let FILTER_DISCH_TAC = FILTER_DISCH_THEN STRIP_ASSUME_TAC;;
```

### Informal statement
The `FILTER_DISCH_TAC` tactic is defined as the composition of `FILTER_DISCH_THEN` and `STRIP_ASSUME_TAC`, implying a strategy for discharging assumptions in a proof while filtering and stripping unnecessary parts.

### Informal sketch
* The definition involves combining two tactics: 
  * `FILTER_DISCH_THEN` which likely filters the discharge of assumptions based on certain conditions
  * `STRIP_ASSUME_TAC` which probably strips or simplifies assumptions in the proof context
* The purpose is to create a new tactic `FILTER_DISCH_TAC` that automates the process of assumption management in proofs, potentially simplifying the proof search or reducing the complexity of the proof state

### Mathematical insight
This definition is important for automating proof search in HOL Light by providing a tactic that can efficiently manage assumptions, potentially improving the system's ability to find proofs. It reflects a strategic approach to proof construction, emphasizing the importance of assumption management in formal proof systems.

### Dependencies
* `FILTER_DISCH_THEN`
* `STRIP_ASSUME_TAC`

### Porting notes
When translating this definition into another proof assistant like Lean, Coq, or Isabelle, one should look for analogous tactics or combinators that serve similar purposes. The main challenge will be identifying the equivalent of `FILTER_DISCH_THEN` and `STRIP_ASSUME_TAC` in the target system and ensuring that their composition behaves similarly to the HOL Light version. Pay particular attention to how each system handles assumption management and tactic composition.

---

## FILTER_STRIP_TAC

### Name of formal statement
FILTER_STRIP_TAC

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let FILTER_STRIP_TAC = FILTER_STRIP_THEN STRIP_ASSUME_TAC;;
```

### Informal statement
The `FILTER_STRIP_TAC` tactic is defined as the composition of `FILTER_STRIP_THEN` and `STRIP_ASSUME_TAC`.

### Informal sketch
* The `FILTER_STRIP_TAC` tactic is constructed by applying `FILTER_STRIP_THEN` followed by `STRIP_ASSUME_TAC`.
* This suggests a two-stage process where `FILTER_STRIP_THEN` is used to filter and then `STRIP_ASSUME_TAC` is applied to strip assumptions.
* The `FILTER_STRIP_THEN` tactic is likely used to filter theorems or goals based on certain conditions, and `STRIP_ASSUME_TAC` is used to remove assumptions from the context.

### Mathematical insight
The `FILTER_STRIP_TAC` definition provides a way to combine filtering and assumption stripping in a single tactic, which can be useful for simplifying proof scripts and making them more efficient.

### Dependencies
* `FILTER_STRIP_THEN`
* `STRIP_ASSUME_TAC`

### Porting notes
When porting this definition to another proof assistant, it is essential to understand the equivalent tactics or functions for filtering and assumption stripping. The porting process may require identifying similar tactics or functions and composing them in a way that mirrors the `FILTER_STRIP_TAC` definition. Additionally, the porter should be aware of any differences in how the target proof assistant handles tactic composition and assumption management.

---

## RES_CANON

### Name of formal statement
RES_CANON

### Type of the formal statement
Theorem

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
                failwith "RES_CANON: no implication is derivable from input thm."
```

### Informal statement
The `RES_CANON` theorem is defined as a recursive function `canon` that takes a flag `fl` and a theorem `th` as input. It applies various transformations to the conclusion of `th` based on its logical structure. If the conclusion is a conjunction, it recursively applies `canon` to the two conjuncts. If the conclusion is an implication, it handles various cases depending on the form of the antecedent, including conjunctions, disjunctions, and existential quantification. It also handles equalities and universal quantification. The function returns a list of theorems resulting from these transformations.

### Informal sketch
* The `RES_CANON` function starts by checking if the conclusion of the input theorem `th` is a negation, and if so, applies `NOT_ELIM` to it.
* It then enters a recursive case analysis based on the form of the conclusion:
  + Conjunction: recursively apply `canon` to the two conjuncts.
  + Implication: analyze the antecedent and apply different transformations based on its form, including:
    - Conjunction: apply `NOT_MP` and recursively apply `canon` to the resulting theorems.
    - Disjunction: apply `NOT_MP` and recursively apply `canon` to the resulting theorems.
    - Existential quantification: apply `NOT_MP` and recursively apply `canon` to the resulting theorem.
  + Equality: apply `EQ_IMP_RULE` and recursively apply `canon` to the resulting theorems.
  + Universal quantification: apply `SPECL` and recursively apply `canon` to the resulting theorem.
* The function returns a list of theorems resulting from these transformations, which are then checked to ensure they are not empty.

### Mathematical insight
The `RES_CANON` theorem appears to be a key component in a resolution-based theorem prover, responsible for applying various logical transformations to theorems to put them into a canonical form. This canonical form is likely used to facilitate the application of resolution rules and to improve the efficiency of the proof search. The theorem's recursive nature and case analysis suggest that it is designed to handle a wide range of logical constructs, including quantifiers and propositional connectives.

### Dependencies
* `NOT_ELIM`
* `CONJ_PAIR`
* `NOT_MP`
* `DISCH`
* `CONJ`
* `ASSUME`
* `DEST_NEG_IMP`
* `DEST_CONJ`
* `DEST_DISJ`
* `DEST_EXISTS`
* `VARIANT`
* `SUBST`
* `EXISTS`
* `EQ_IMP_RULE`
* `SPECL`
* `GEN_ALL`
* `SPEC_ALL`
* `CONJUNCTS`
* `FLAT`
* `UNCURRY`
* `CHECK`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the recursive function `canon` is properly translated, including its case analysis and application of various logical transformations. Additionally, the dependencies listed above should be ported or reimplemented as necessary to ensure that the `RES_CANON` theorem functions correctly in the new system. Particular attention should be paid to the handling of quantifiers and propositional connectives, as these are central to the theorem's operation.

---

## IMP_RES_THEN,RES_THEN

### Name of formal statement
IMP_RES_THEN,RES_THEN

### Type of the formal statement
Theorem/Definition

### Formal Content
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

### Informal statement
The `IMP_RES_THEN` and `RES_THEN` functions define a method for resolving implications in a sequent calculus. Given a tactic `ttac` and an implication `impth`, `IMP_RES_THEN` applies the tactic to the resolvents obtained by matching the implication with assumptions. `RES_THEN` applies a similar process but starts from a list of assumptions and a goal, resolving implications among them. Both functions use `MATCH_MP` to match the implications, `RES_CANON` to canonicalize resolvents, and `NOT_MP` to apply modus ponens. The `check` function ensures that the lists of resolvents and tactics are not empty.

### Informal sketch
* The process begins with `IMP_RES_THEN` or `RES_THEN` being applied to a tactic `ttac` and either an implication `impth` or a list of assumptions and a goal `(asl, g)`.
* For `IMP_RES_THEN`, it attempts to resolve the implication `impth` using `RES_CANON`, which may raise a failure if `impth` is not an implication.
* It then applies `MATCH_MP` to match the implication with the assumptions, generating a list of resolvents.
* The function `check` is used to ensure that there are resolvents and that applying the tactic `ttac` to these resolvents yields a non-empty list of tactics.
* For `RES_THEN`, it first extracts the assumptions `asm` from `(asl, g)`, then finds all implications among these assumptions using `RES_CANON`.
* It matches these implications with the assumptions using `MATCH_MP`, generates resolvents, and applies the tactic `ttac` to them.
* The `check` function is again used to handle potential failures in finding implications, resolvents, or tactics.
* The final step involves applying the resulting tactics to the original assumptions and goal.

### Mathematical insight
The `IMP_RES_THEN` and `RES_THEN` functions are crucial for automated reasoning in sequent calculus, as they provide a systematic way to resolve implications and apply tactics to prove goals. They are based on the principle of modus ponens and the concept of resolving assumptions to derive new conclusions. These functions are important for building automated theorem provers that can handle implications and resolvents efficiently.

### Dependencies
- `MATCH_MP`
- `RES_CANON`
- `NOT_MP`
- `SPEC_ALL`
- `INST_TY_TERM`
- `term_match`
- `dest_neg_imp`
- `concl`
- `ASSUM_LIST`
- `itlist`
- `mapfilter`
- `EVERY` 

### Porting notes
When translating `IMP_RES_THEN` and `RES_THEN` into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how these systems handle implications, resolvents, and tactic applications. Differences in the underlying logic (e.g., classical vs. intuitionistic) and the treatment of binders may require adjustments to the ported code. Additionally, the efficiency of the `check` function in handling failures and the application of tactics to resolvents might need optimization depending on the target system's capabilities.

---

## IMP_RES_TAC

### Name of formal statement
IMP_RES_TAC

### Type of the formal statement
Tactic definition

### Formal Content
```ocaml
let IMP_RES_TAC th g =
  try IMP_RES_THEN (REPEAT_GTCL IMP_RES_THEN STRIP_ASSUME_TAC) th g
  with Failure _ -> ALL_TAC g;;
```

### Informal statement
The `IMP_RES_TAC` tactic applies to a theorem `th` and a goal `g`, attempting to resolve the implications in `th` and then apply the result to `g`. If this process fails, it falls back to applying `ALL_TAC` to `g`.

### Informal sketch
* The tactic first attempts to apply `IMP_RES_THEN` with `REPEAT_GTCL` (a tactic for repeating a given tactic until no further changes are made) applied to `IMP_RES_THEN` and `STRIP_ASSUME_TAC` (a tactic for removing assumptions) to the theorem `th` and goal `g`.
* If the application of `IMP_RES_THEN` with the specified repetition and tactics succeeds, it applies the resulting theorem to `g`.
* If the application fails (indicated by a `Failure` exception), the tactic falls back to applying `ALL_TAC` to `g`, effectively doing nothing and leaving `g` unchanged.

### Mathematical insight
The `IMP_RES_TAC` tactic is designed to handle implications in theorems and apply them to goals in a proof, utilizing repetition and assumption stripping to simplify the process. It provides a fallback mechanism to ensure that the proof process can continue even if the implication resolution and application are not successful.

### Dependencies
* `IMP_RES_THEN`
* `REPEAT_GTCL`
* `STRIP_ASSUME_TAC`
* `ALL_TAC`

### Porting notes
When translating `IMP_RES_TAC` into another proof assistant, note that the equivalent of `REPEAT_GTCL` might need to be implemented using recursion or loops, depending on the target system's support for tactic repetition. Additionally, the `IMP_RES_THEN` and `STRIP_ASSUME_TAC` tactics, as well as the `ALL_TAC` fallback, will need to be translated or reimplemented according to the target system's tactic language and capabilities.

---

## RES_TAC

### Name of formal statement
RES_TAC

### Type of the formal statement
Tactic definition

### Formal Content
```ocaml
let RES_TAC g =
  try RES_THEN (REPEAT_GTCL IMP_RES_THEN STRIP_ASSUME_TAC) g
  with Failure _ -> ALL_TAC g;;
```

### Informal statement
The `RES_TAC` tactic applies a sequence of tactics to a goal `g`. It attempts to apply `RES_THEN` with the composition of `REPEAT_GTCL`, `IMP_RES_THEN`, and `STRIP_ASSUME_TAC` to `g`. If this attempt fails, it falls back to applying `ALL_TAC` to `g`.

### Informal sketch
* The tactic starts by attempting to apply a combination of tactics to the goal `g` using `RES_THEN`.
* The combined tactic involves:
  + `REPEAT_GTCL`: repeating a generalization and instantiation process.
  + `IMP_RES_THEN`: resolving implications and then applying another tactic.
  + `STRIP_ASSUME_TAC`: stripping assumptions and applying `ASSUME_TAC`.
* If the application of `RES_THEN` with these tactics fails, the tactic falls back to `ALL_TAC`, which applies all possible tactics to `g`.

### Mathematical insight
The `RES_TAC` tactic is designed to handle a specific class of goals by applying a structured sequence of reasoning steps. It leverages the `RES_THEN` combinator to chain tactics together, starting with generalization and implication resolution, followed by assumption stripping. The fallback to `ALL_TAC` ensures that if the specific sequence fails, a more general approach is taken.

### Dependencies
* Tactic combinators:
  + `RES_THEN`
  + `REPEAT_GTCL`
  + `IMP_RES_THEN`
  + `STRIP_ASSUME_TAC`
  + `ALL_TAC`
* Basic tactics:
  + `ASSUME_TAC`

### Porting notes
When porting `RES_TAC` to another proof assistant, pay close attention to how tactic combinators are handled, especially `RES_THEN` and how it composes tactics. The equivalent of `REPEAT_GTCL`, `IMP_RES_THEN`, and `STRIP_ASSUME_TAC` must be identified in the target system. Additionally, ensure that the fallback mechanism (in this case, `ALL_TAC`) is appropriately translated, considering how the target system handles tactic failure and backtracking.

---

## prove_rep_fn_one_one

### Name of formal statement
prove_rep_fn_one_one

### Type of the formal statement
Theorem

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
For a given theorem `th`, let `thm` be the first conjunct of `th`. Let `A` and `R` be the function and relation, respectively, obtained by decomposing the left-hand side of the conclusion of `thm`. Let `a` and `a'` be two distinct variables of the same type as the domain of `R`. Then, assuming `R(a) = R(a')`, it can be derived that `A(R(a)) = A(R(a'))`. Furthermore, for generic variables `ga1` and `ga2` of the same type as `a`, substituting `a` and `a'` into `thm` yields `ga1 = ga2`. Discharging the assumption `R(a) = R(a')` and applying the `IMP_ANTISYM_RULE` tactic, it can be concluded that `a = a'` implies `R(a) = R(a')`, and conversely.

### Informal sketch
* Start with a given theorem `th` and extract its first conjunct `thm`.
* Decompose the left-hand side of the conclusion of `thm` to obtain function `A` and relation `R`.
* Introduce two distinct variables `a` and `a'` of the same type as the domain of `R`.
* Assume `R(a) = R(a')` and derive `A(R(a)) = A(R(a'))` using `AP_TERM`.
* Substitute `a` and `a'` into `thm` to obtain `ga1 = ga2` for generic variables `ga1` and `ga2`.
* Discharge the assumption `R(a) = R(a')` and apply `IMP_ANTISYM_RULE` to conclude the equivalence between `a = a'` and `R(a) = R(a')`.
* Use `GEN` to generalize the result for all `a` and `a'`.

### Mathematical insight
This theorem appears to be related to the concept of representation of functions, specifically proving that a function `R` is one-to-one. The key idea is to show that if `R(a) = R(a')`, then `a = a'`, which is a fundamental property of injective functions. The theorem uses a combination of logical manipulations and substitutions to establish this result.

### Dependencies
* `CONJUNCT1`
* `I`
* `F_F`
* `rator`
* `dest_comb`
* `lhs`
* `snd`
* `dest_forall`
* `concl`
* `AP_TERM`
* `ASSUME`
* `SUBST`
* `SPEC`
* `genvar`
* `mk_eq`
* `mk_comb`
* `DISCH`
* `IMP_ANTISYM_RULE`
* `GEN`

---

## prove_rep_fn_onto

### Name of formal statement
prove_rep_fn_onto

### Type of the formal statement
Theorem

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
For a given theorem `th`, if `th` can be split into two conjuncts `th1` and `th2`, and if the conclusion of `th2` is a universal statement that can be transformed into an equation `r = eq` after removing the universal quantifier, then there exists a representation function `RE` and an argument `ar` such that `RE` applied to some argument `a` equals `r`. Furthermore, for any `v` of the same type as `r`, if `v` equals `RE` applied to some `a`, then `RE` applied to `v` equals `v`. This statement essentially proves that a representation function `RE` onto its domain exists.

### Informal sketch
* Start with a theorem `th` and split it into two conjuncts `th1` and `th2`.
* From `th2`, derive an equation `r = eq` by removing the universal quantifier and applying `F_F rhs`.
* Identify a representation function `RE` and its argument `ar` from the left-hand side of the equation `eq`.
* Introduce a new variable `a` of the same type as `ar` and form the equation `r = RE(a)`.
* Existentially quantify `a` to form `ex`.
* Derive two implications: `imp1` from assuming `eq` and `imp2` from choosing `a` such that `ex` holds and then substituting and transforming using `th1`.
* Apply `IMP_ANTISYM_RULE` to `imp1` and `imp2` to form `swap`.
* Finally, generalize over `r` and apply `TRANS` to `th2` and `swap` to conclude the proof.

### Mathematical insight
This theorem proves the existence of a representation function `RE` that is onto its domain, given certain conditions on a theorem `th`. The key idea is to manipulate the given theorem to derive the existence of such a representation function, which is crucial in various mathematical constructions, especially in areas like category theory and universal algebra. The proof involves careful manipulation of quantifiers, equations, and substitutions to establish the onto property of `RE`.

### Dependencies
#### Theorems
* `CONJUNCTS`
* `dest_forall`
* `I`
* `F_F`
* `rhs`
* `dest_comb`
* `mk_eq`
* `dest_eq`
* `mk_primed_var`
* `mk_exists`
* `EXISTS`
* `SYM`
* `ASSUME`
* `genvar`
* `rator`
* `AP_TERM`
* `SPEC`
* `SUBST`
* `CHOOSE`
* `IMP_ANTISYM_RULE`
* `DISCH`
* `TRANS`
* `GEN`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles binders, existential quantification, and equation manipulation. Specifically, the use of `CONJUNCTS`, `dest_forall`, and `F_F` might require equivalent tactics or functions in the target system. Additionally, the representation of `RE` and its argument `ar` might need to be adjusted according to the target system's type theory and handling of functions.

---

## prove_abs_fn_onto

### Name of formal statement
prove_abs_fn_onto

### Type of the formal statement
Theorem

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
Given a theorem `th`, if `th` can be split into two conjuncts `th1` and `th2`, then there exists a term `a` and functions `A` and `R` such that `A` and `R` satisfy certain properties derived from `th1` and `th2`. Specifically, `th1` implies the existence of `a` such that `A(a)` equals `a` and `R(a)` holds, and `th2` implies the existence of a term `r` such that `A(r)` equals `a` and `P(r)` holds, where `P` is a predicate derived from `th2`. The conclusion is that for all `a`, there exists an `r` such that `A(r)` equals `a` and `P(r)` holds.

### Informal sketch
* Start with a given theorem `th` and attempt to split it into two conjuncts `th1` and `th2` using `CONJUNCTS`.
* From `th1`, extract a term `a` and functions `A` and `R` using `dest_forall` and `dest_comb`.
* Derive a theorem `thm1` by applying `EQT_ELIM`, `TRANS`, and `EQT_INTRO` to `th2` and the extracted term `a`.
* Derive another theorem `thm2` by applying `SYM` to `th1` with `SPEC`ified term `a`.
* Extract a term `r` and predicate `P` from `th2` using `dest_forall` and `rator`.
* Construct an existential statement `ex` that combines the equalities and predicates derived from the previous steps.
* Conclude by applying `GEN` to `a` and combining `thm2` and `thm1` using `CONJ` to prove the existence of `r` satisfying the desired properties.

### Mathematical insight
This theorem appears to be related to the concept of proving the existence of a right inverse for a function, given certain properties about the function and its domain. The key idea is to manipulate the given theorems `th1` and `th2` to derive the existence of a term `r` that satisfies specific equalities and predicates, ultimately proving that the function is onto.

### Dependencies
* `CONJUNCTS`
* `dest_forall`
* `dest_comb`
* `EQT_ELIM`
* `TRANS`
* `EQT_INTRO`
* `SYM`
* `SPEC`
* `GEN`
* `CONJ`
* `EXISTS`
* `AP_TERM`
* `mk_comb`
* `mk_conj`
* `mk_eq`

### Porting notes
When translating this theorem into other proof assistants, pay close attention to the handling of binders, especially when applying `dest_forall` and `GEN`. Additionally, the use of `EQT_ELIM` and `EQT_INTRO` may require careful consideration of the equality rules in the target system. The construction of the existential statement `ex` and the application of `EXISTS` may also require adjustments depending on the specific proof assistant's handling of existential quantification.

---

## prove_abs_fn_one_one

### Name of formal statement
prove_abs_fn_one_one

### Type of the formal statement
Theorem

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
  with Failure _ -> failwith "prove_abs_fn_one_one"
```

### Informal statement
For all `r` and `r'` such that `P(r)` and `P(r')`, if `A(r) = A(r')`, then `r = r'`. This statement is derived from two theorems `th1` and `th2`, where `th2` implies `P(r)` and `th1` implies the existence of a function `A` such that `A(r)` is defined. The statement is proved by assuming `A(r) = A(r')` and deriving `r = r'` using the `IMP_ANTISYM_RULE` and `AP_TERM` rules.

### Informal sketch
* Start with two theorems `th1` and `th2`, where `th2` implies `P(r)` and `th1` implies the existence of a function `A` such that `A(r)` is defined.
* Assume `P(r)` and `P(r')` for some `r` and `r'`.
* Use `EQ_MP` to derive `t1` and `t2` from `th2` and the assumptions `P(r)` and `P(r')`.
* Assume `A(r) = A(r')` and derive `r = r'` using `SUBST`, `AP_TERM`, and `IMP_ANTISYM_RULE`.
* Discharge the assumptions `P(r)` and `P(r')` to obtain the final theorem.

### Mathematical insight
This theorem establishes the injectivity of the function `A` with respect to the predicate `P`. It ensures that if two inputs `r` and `r'` satisfy `P`, and their images under `A` are equal, then `r` and `r'` must be equal. This property is crucial in various mathematical contexts, such as functional equations and algebraic structures.

### Dependencies
* `CONJUNCTS`
* `I`
* `F_F`
* `rator`
* `lhs`
* `dest_forall`
* `dest_comb`
* `ASSUME`
* `EQ_MP`
* `SPEC`
* `SUBST`
* `AP_TERM`
* `IMP_ANTISYM_RULE`
* `GEN`
* `DISCH`
* `mk_comb`
* `mk_eq`
* `genvar`
* `type_of`

### Porting notes
When translating this theorem to other proof assistants, pay attention to the handling of binders, assumptions, and the `SUBST` rule. In particular, ensure that the `SUBST` rule is applied correctly to replace the variables `v1` and `v2` with the terms `t1` and `t2`. Additionally, the `AP_TERM` rule may need to be adapted to the specific proof assistant's syntax and semantics.

---

## AC_CONV(assoc,sym)

### Name of formal statement
AC_CONV(assoc,sym)

### Type of the formal statement
Theorem/conversion definition

### Formal Content
```ocaml
let AC_CONV(assoc,sym) =
  let th1 = SPEC_ALL assoc
  and th2 = SPEC_ALL sym in
  let th3 = GEN_REWRITE_RULE (RAND_CONV o LAND_CONV) [th2] th1 in
  let th4 = SYM th1 in
  let th5 = GEN_REWRITE_RULE RAND_CONV [th4] th3 in
  EQT_INTRO o AC(end_itlist CONJ [th2; th4; th5])
```

### Informal statement
The `AC_CONV(assoc,sym)` conversion is defined as a composition of several steps starting with the specialization of the `assoc` and `sym` theorems. It then applies `GEN_REWRITE_RULE` with specific conversions to these theorems, followed by symmetrization and further rewriting. The result is wrapped up as a special conversion using `EQT_INTRO` and `AC`, combining the theorems `th2`, `th4`, and `th5` conjunctively.

### Informal sketch
* The construction begins with the specialization of `assoc` and `sym` theorems using `SPEC_ALL`.
* It then applies a `GEN_REWRITE_RULE` with a specific conversion to `th1` (the specialized `assoc` theorem), using `th2` (the specialized `sym` theorem) as a rewrite rule.
* The process involves symmetrizing `th1` to obtain `th4`.
* Further rewriting is applied to `th3` using `th4` to obtain `th5`.
* The final step involves combining `th2`, `th4`, and `th5` conjunctively using `end_itlist CONJ`, and then applying `AC` and `EQT_INTRO` to form the `AC_CONV(assoc,sym)` conversion.

### Mathematical insight
This definition provides a conversion for associativity and symmetry properties, crucial in various algebraic structures. It demonstrates how to systematically derive and compose rewrite rules and conversions in a formal system, leveraging the `GEN_REWRITE_RULE`, `SYM`, `EQT_INTRO`, and `AC` tactics to create a powerful tool for manipulating equations involving associative and symmetric operations.

### Dependencies
* Theorems:
  - `assoc`
  - `sym`
* Tactics and functions:
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
When translating this into another proof assistant, pay close attention to how each system handles rewrite rules, symmetry, and associativity. Note that `GEN_REWRITE_RULE` and tactic compositions might have direct analogs, but the exact syntax and application could differ. For example, in systems like Lean or Coq, you might need to explicitly state the type of the terms being manipulated or use different tactics for symmetrization and rewriting. Additionally, the `AC` tactic, which is used for associative-commutative rewriting, might require a different approach in other systems, potentially involving more explicit use of equations or lemmas about associativity and commutativity.

---

## AC_RULE

### Name of formal statement
AC_RULE

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let AC_RULE ths = EQT_ELIM o AC_CONV ths;;
```

### Informal statement
The `AC_RULE` is defined as the composition of `EQT_ELIM` and `AC_CONV` applied to a list of theorems `ths`. This means that for a given set of theorems, `AC_RULE` first applies `AC_CONV` and then applies `EQT_ELIM` to the result.

### Informal sketch
* The definition involves a two-stage process:
  * First, `AC_CONV` is applied to the list of theorems `ths`. This suggests a conversion or transformation step, likely related to associativity and commutativity properties (`AC`).
  * Then, the result of this conversion is passed through `EQT_ELIM`, which likely eliminates equalities or performs some form of equational reasoning.
* The use of `EQT_ELIM` after `AC_CONV` implies that the definition is geared towards leveraging associativity and commutativity properties to simplify or solve equations.

### Mathematical insight
The `AC_RULE` definition appears to capture a common pattern in equational reasoning, particularly in the context of associative and commutative operations. By composing `AC_CONV` with `EQT_ELIM`, it provides a structured way to apply these properties in proofs, likely simplifying the process of deriving conclusions from given premises in a theory that involves such operations.

### Dependencies
- Key definitions and theorems:
  - `EQT_ELIM`
  - `AC_CONV`

### Porting notes
When translating `AC_RULE` into another proof assistant, pay close attention to how associativity and commutativity are handled, as well as how equality elimination is performed. The exact implementation of `AC_CONV` and `EQT_ELIM` may vary between systems, requiring careful consideration of how these concepts are represented and used in the target system.

---

## (COND_CASES_TAC

### Name of formal statement
COND_CASES_TAC

### Type of the formal statement
tactic

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
         (asl,w) 
```

### Informal statement
This tactic `COND_CASES_TAC` is defined to take an assumption list `asl` and a goal `w`, and applies a series of transformations to handle conditional statements within `w`. It first identifies a suitable conditional term `cond` in `w` that meets the `is_good_cond` criterion, which checks if the condition is not a constant and is free in `w`. It then decomposes `cond` into a predicate `p` and terms `t` and `u`. The tactic instantiates `COND_CLAUSES` with the type of `t` and applies `DISJ_CASES_THEN2` to handle the cases arising from the conditional, using `EXCLUDED_MIDDLE` for the predicate `p`. It applies substitutions and assumptions based on the cases, ultimately transforming the goal.

### Informal sketch
* Identify a conditional term `cond` in the goal `w` that meets the `is_good_cond` criterion.
* Decompose `cond` into a predicate `p` and terms `t` and `u`.
* Instantiate `COND_CLAUSES` with the type of `t` to obtain a specialized version.
* Apply `DISJ_CASES_THEN2` to handle the two cases arising from the conditional:
  + For the first case, apply `EQT_INTRO`, then `SUBST1_TAC` with `ct`, and assume the case's theorem.
  + For the second case, apply `EQF_INTRO`, then `SUBST1_TAC` with `cf`, and assume the case's theorem.
* Utilize `EXCLUDED_MIDDLE` for the predicate `p` in handling these cases.

### Mathematical insight
This tactic is designed to handle conditional statements in a goal by systematically breaking down the condition into cases and applying relevant transformations to simplify or solve the goal. The use of `COND_CLAUSES` and `EXCLUDED_MIDDLE` reflects the underlying logical principles of handling conditionals and the law of excluded middle, respectively. The tactic's structure ensures a systematic approach to dealing with conditionals, making it a useful tool in formal proofs involving such statements.

### Dependencies
* `COND_CLAUSES`
* `EXCLUDED_MIDDLE`
* `is_const`
* `dest_cond`
* `free_in`
* `find_term`
* `INST_TYPE`
* `CONJ_PAIR`
* `DISJ_CASES_THEN2`
* `SUBST1_TAC`
* `EQT_INTRO`
* `EQF_INTRO`
* `ASSUME_TAC`

---

## MATCH_MP_TAC

### Name of formal statement
MATCH_MP_TAC

### Type of the formal statement
Theorem/tactic definition

### Formal Content
```ocaml
let MATCH_MP_TAC th =
  MATCH_MP_TAC th ORELSE
  MATCH_MP_TAC(PURE_REWRITE_RULE[RIGHT_IMP_FORALL_THM] th);;
```

### Informal statement
The `MATCH_MP_TAC` tactic applies to a theorem `th`. If `th` does not directly match the goal, it attempts to apply `PURE_REWRITE_RULE` with `RIGHT_IMP_FORALL_THM` to transform `th` before applying it again.

### Informal sketch
* The tactic first attempts to apply `MATCH_MP_TAC` directly to the theorem `th`.
* If this fails, it rewrites `th` using `PURE_REWRITE_RULE` with `RIGHT_IMP_FORALL_THM`, aiming to transform the implication in `th` to better match the goal.
* The `RIGHT_IMP_FORALL_THM` theorem is specifically used to handle universals on the right side of implications, making the tactic more versatile.
* The `ORELSE` operator indicates that the second attempt is made only if the first application of `MATCH_MP_TAC` fails.

### Mathematical insight
The `MATCH_MP_TAC` tactic is designed to facilitate the application of theorems in a more flexible manner, especially when dealing with implications that involve universal quantifiers on the right side. This is crucial in formal proof development, as it allows for more natural and less constrained theorem application, enhancing the automation and expressiveness of the proof assistant.

### Dependencies
* Theorems:
  + `RIGHT_IMP_FORALL_THM`
* Tactics:
  + `MATCH_MP_TAC`
  + `PURE_REWRITE_RULE`

### Porting notes
When translating `MATCH_MP_TAC` into another proof assistant, pay special attention to how implications and universal quantifiers are handled. The equivalent of `PURE_REWRITE_RULE` and the theorem `RIGHT_IMP_FORALL_THM` must be identified in the target system. Additionally, consider how the target system manages tactic failure and recovery, as the `ORELSE` behavior might need to be replicated or emulated.

---

## ZERO_LESS_EQ

### Name of formal statement
ZERO_LESS_EQ

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let ZERO_LESS_EQ = LE_0;;
```

### Informal statement
The definition `ZERO_LESS_EQ` is equivalent to `LE_0`, which denotes the less-than-or-equal-to relation with zero.

### Informal sketch
* The definition directly assigns `ZERO_LESS_EQ` to be `LE_0`, indicating that `ZERO_LESS_EQ` is an alias or another name for the relation `LE_0`.
* This step involves simple substitution or renaming, with no additional proof or construction required beyond the definition itself.
* The `LE_0` relation is presumed to be already defined elsewhere in the HOL Light development.

### Mathematical insight
This definition provides a convenient shorthand or alternative name for the `LE_0` relation, potentially simplifying expressions or theorems involving this relation. It implies that `ZERO_LESS_EQ` can be used interchangeably with `LE_0` in proofs and definitions.

### Dependencies
#### Definitions
* `LE_0`

### Porting notes
When porting this definition to another proof assistant, ensure that `LE_0` (or its equivalent) is defined and accessible. The porting process should involve a straightforward renaming or aliasing, similar to how `ZERO_LESS_EQ` is defined in terms of `LE_0` here. Pay attention to the specific syntax and mechanisms for defining aliases or shorthand names in the target proof assistant.

---

## LESS_EQ_MONO

### Name of formal statement
LESS_EQ_MONO

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let LESS_EQ_MONO = LE_SUC;;
```

### Informal statement
The LESS_EQ_MONO definition is equivalent to LE_SUC.

### Informal sketch
* The definition `LESS_EQ_MONO` is a straightforward assignment, equating it with the existing definition `LE_SUC`.
* This step involves recognizing that `LESS_EQ_MONO` and `LE_SUC` represent the same concept or relationship, thus allowing for their direct equivalence.
* The key logical stage here is the acknowledgment of this equivalence without requiring additional proof or derivation, as it is presented as a basic definition.

### Mathematical insight
The definition of `LESS_EQ_MONO` as `LE_SUC` indicates that the concept of "less than or equal to" monotonicity is directly related to or even synonymous with the successor function's behavior in the context of ordering. This equivalence suggests a foundational aspect of how ordering relations are defined or utilized within the system.

### Dependencies
#### Definitions
* `LE_SUC`

### Porting notes
When translating `LESS_EQ_MONO` into other proof assistants like Lean, Coq, or Isabelle, ensure that the equivalent of `LE_SUC` is properly defined and recognized. The main challenge might lie in how each system handles definitions and their equivalences, particularly if there are differences in how terms are expanded or simplified.

---

## NOT_LESS

### Name of formal statement
NOT_LESS

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let NOT_LESS = NOT_LT;;
```

### Informal statement
NOT_LESS is defined as the negation of LESS, which is represented by the `NOT_LT` operator.

### Informal sketch
* The definition of `NOT_LESS` directly corresponds to the logical negation of the less-than relation, utilizing the `NOT_LT` operator.
* This implies that `NOT_LESS` holds true whenever `LESS` does not, following standard logical principles.

### Mathematical insight
The definition of `NOT_LESS` in terms of `NOT_LT` reflects a fundamental property of binary relations, where the negation of a relation holds if and only if the original relation does not. This construction is essential in building a comprehensive theory of order relations.

### Dependencies
#### Definitions
* `NOT_LT`

### Porting notes
When translating `NOT_LESS` into other proof assistants like Lean, Coq, or Isabelle, ensure that the target system's definition of negation and the less-than relation aligns with the HOL Light `NOT_LT` operator. Pay particular attention to how each system handles negation and relational operators, as the syntax and underlying logic may differ.

---

## LESS_0

### Name of formal statement
LESS_0

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let LESS_0 = LT_0;;
```

### Informal statement
LESS_0 is defined to be equal to LT_0.

### Informal sketch
* The definition of LESS_0 directly references `LT_0`, implying that `LESS_0` inherits its properties and behavior from `LT_0`.
* This step involves recognizing the equivalence between `LESS_0` and `LT_0`, suggesting that any properties or theorems applicable to `LT_0` are also applicable to `LESS_0`.

### Mathematical insight
The definition of LESS_0 as equal to LT_0 suggests a foundational or primitive concept in the theory, where `LESS_0` is introduced as a basic relation or operator, possibly in the context of ordering or comparison. This definition provides a starting point for more complex constructions or theorems involving `LESS_0`.

### Dependencies
* `LT_0`

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, ensure that the equivalent of `LT_0` is properly defined and accessible. The direct assignment or equivalence should be preserved, as it forms the basis of `LESS_0`'s properties and usage in subsequent proofs or definitions. Pay attention to how each system handles definitions and ensure that the translation maintains the intended semantic equivalence.

---

## LESS_EQ_REFL

### Name of formal statement
LESS_EQ_REFL

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let LESS_EQ_REFL = LE_REFL;;
```

### Informal statement
For all elements, it is true that each element is less than or equal to itself.

### Informal sketch
* The statement `LESS_EQ_REFL` is defined as `LE_REFL`, which implies reflexivity of the less-than-or-equal-to relation.
* This definition leverages the existing `LE_REFL` concept, which typically denotes that every element is less than or equal to itself.
* The key logical stage here involves recognizing that `LE_REFL` already encapsulates the notion of reflexivity for the less-than-or-equal-to relation.

### Mathematical insight
The `LESS_EQ_REFL` statement formalizes the reflexive property of the less-than-or-equal-to relation, which is a fundamental property in order theory. This property is crucial because it ensures that every element in a set is related to itself under this relation, providing a baseline for comparisons.

### Dependencies
* `LE_REFL`

### Porting notes
When translating `LESS_EQ_REFL` into other proof assistants like Lean, Coq, or Isabelle, ensure that the target system has an equivalent concept for `LE_REFL` and that it correctly implements the reflexive property of the less-than-or-equal-to relation. Pay attention to how each system handles equality and order relations, as the specifics can vary.

---

## LESS_EQUAL_ANTISYM

### Name of formal statement
LESS_EQUAL_ANTISYM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LESS_EQUAL_ANTISYM = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL LE_ANTISYM)))
```

### Informal statement
For all `x` and `y`, if `x` is less than or equal to `y` and `y` is less than or equal to `x`, then `x` is equal to `y`.

### Informal sketch
* The proof involves applying the `EQ_IMP_RULE` to `LE_ANTISYM`, which is a theorem stating that if `x` is less than or equal to `y` and `y` is less than or equal to `x`, then `x` is equal to `y`.
* The `SPEC_ALL` tactic is used to specialize the theorem `LE_ANTISYM` for all possible `x` and `y`.
* The `EQ_IMP_RULE` is then applied to this specialized theorem to obtain the desired conclusion.
* The `GEN_ALL` tactic is used to generalize the result for all `x` and `y`.
* The `fst` function is used to extract the first component of the resulting theorem.

### Mathematical insight
This theorem is a fundamental property of the less-than-or-equal-to relation, stating that it is antisymmetric. This means that if two elements are less than or equal to each other, then they must be equal. This property is crucial in many mathematical structures, such as partial orders and total orders.

### Dependencies
* `LE_ANTISYM`
* `EQ_IMP_RULE`
* `SPEC_ALL`
* `GEN_ALL`

### Porting notes
When porting this theorem to other proof assistants, note that the `EQ_IMP_RULE` and `SPEC_ALL` tactics may need to be replaced with equivalent constructs. Additionally, the `GEN_ALL` tactic may need to be replaced with a tactic that achieves the same effect, such as a `forall` introduction rule. The `fst` function may also need to be replaced with an equivalent construct, depending on the specific proof assistant being used.

---

## NOT_LESS_0

### Name of formal statement
NOT_LESS_0

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let NOT_LESS_0 = GEN_ALL(EQF_ELIM(SPEC_ALL(CONJUNCT1 LT)))
```

### Informal statement
For all x, it is not the case that x is less than 0.

### Informal sketch
* The proof involves using the `GEN_ALL` tactic to generalize the statement for all x.
* It utilizes `EQF_ELIM` to eliminate an equality, which is likely derived from the `SPEC_ALL` application on `CONJUNCT1 LT`, where `LT` refers to a less-than relation and `CONJUNCT1` extracts the first conjunct of a conjunction.
* The key step is applying `CONJUNCT1` to `LT`, which suggests that the less-than relation is defined as a conjunction, and the first part of this conjunction is relevant to proving that x is not less than 0.

### Mathematical insight
The NOT_LESS_0 theorem establishes a fundamental property related to the less-than relation, specifically stating that no number is less than 0. This is crucial in various mathematical proofs, especially those involving inequalities and ordering relations.

### Dependencies
* `LT` (less-than relation)
* `GEN_ALL` (tactic for generalization)
* `EQF_ELIM` (tactic for equality elimination)
* `SPEC_ALL` (tactic for specification)
* `CONJUNCT1` (tactic for extracting the first conjunct of a conjunction)

### Porting notes
When translating this theorem into another proof assistant, special attention should be paid to how the less-than relation (`LT`) and the tactics `GEN_ALL`, `EQF_ELIM`, `SPEC_ALL`, and `CONJUNCT1` are handled. The direct equivalents of these tactics and the less-than relation may differ between systems, requiring careful mapping to ensure the proof structure and mathematical content are preserved.

---

## LESS_TRANS

### Name of formal statement
LESS_TRANS

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let LESS_TRANS = LT_TRANS;;
```

### Informal statement
The LESS_TRANS relation is defined to be equivalent to the LT_TRANS relation.

### Informal sketch
* The definition directly assigns the value of `LT_TRANS` to `LESS_TRANS`, implying that `LESS_TRANS` inherits the properties and behavior of `LT_TRANS`.
* This step involves recognizing the equivalence between the two relations, which might be based on the transitivity property of a less-than relation in a specific context or structure.
* The key insight here is understanding that `LESS_TRANS` is not introducing a new relation but rather providing an alias or an alternative name for `LT_TRANS`, potentially for convenience, clarity, or compatibility in different parts of the formal development.

### Mathematical insight
The definition of `LESS_TRANS` as `LT_TRANS` suggests a context where a less-than relation is being defined or utilized, possibly within an order theory or in the context of a specific algebraic structure. This equivalence implies that any properties or theorems proven about `LT_TRANS` directly apply to `LESS_TRANS`, and vice versa, which can be useful for simplifying proofs or making the formal development more intuitive.

### Dependencies
- Definitions: `LT_TRANS`
- Theorems: None explicitly mentioned, but the definition implies a dependency on any theorem or property that `LT_TRANS` relies on or satisfies.

### Porting notes
When porting this definition to another proof assistant, ensure that the equivalent of `LT_TRANS` is correctly identified and that the new definition `LESS_TRANS` is introduced in a way that maintains the equivalence. Pay special attention to how the target system handles definitions and aliases, as the direct assignment might be represented differently (e.g., using a `let` statement in Coq or a `definition` command in Isabelle).

---

## LESS_LEMMA1

### Name of formal statement
LESS_LEMMA1

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LESS_LEMMA1 = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL(CONJUNCT2 LT))));
```

### Informal statement
For all `x` and `y`, if `x` is less than `y`, then it is not the case that `y` is less than `x`.

### Informal sketch
* The proof starts with the `CONJUNCT2` of the `LT` definition, which gives us `x < y` implies `~(y < x)`.
* The `SPEC_ALL` tactic is applied to generalize this implication for all `x` and `y`.
* The `EQ_IMP_RULE` tactic is then used to convert the implication into an equivalence, but since we only need the forward direction, we take the first component of the resulting equivalence using `fst`.
* Finally, `GEN_ALL` is applied to generalize the result for all possible `x` and `y`, yielding the final theorem `LESS_LEMMA1`.

### Mathematical insight
This theorem provides a fundamental property of the less-than relation, stating that it is asymmetric. This means if `x` is less than `y`, then `y` cannot be less than `x`, which is a basic characteristic of order relations.

### Dependencies
#### Theorems and Definitions
* `LT`
* `CONJUNCT2`
* `EQ_IMP_RULE`
* `GEN_ALL`
* `SPEC_ALL`

### Porting notes
When translating this into another proof assistant like Lean, Coq, or Isabelle, pay special attention to how each system handles generalization and the application of rules like `EQ_IMP_RULE`. The `GEN_ALL` and `SPEC_ALL` tactics have direct counterparts in many systems, but the exact syntax and application may vary. Additionally, the `CONJUNCT2` and `fst` operations may need to be adjusted based on how the target system represents and manipulates propositions and types.

---

## LESS_SUC_REFL

### Name of formal statement
LESS_SUC_REFL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LESS_SUC_REFL = prove(`!n. n < SUC n`,REWRITE_TAC[LT])
```

### Informal statement
For all natural numbers `n`, `n` is less than the successor of `n`.

### Informal sketch
* The proof involves a universal quantification over all natural numbers `n`.
* The key step is to apply the definition of the less-than relation (`LT`) and the successor function (`SUC`) to establish the inequality `n < SUC n`.
* The `REWRITE_TAC[LT]` tactic in HOL Light suggests that the proof may involve rewriting the less-than relation using its definition.

### Mathematical insight
This theorem captures a fundamental property of the natural numbers, namely that every number is less than its successor. This property is essential in various mathematical constructions, such as induction and recursion.

### Dependencies
* `LT` (less-than relation)
* `SUC` (successor function)

### Porting notes
When porting this theorem to other proof assistants, ensure that the less-than relation and successor function are defined and behave similarly. Note that some systems may require explicit type annotations or different tactic scripts to establish this property. Additionally, the use of `REWRITE_TAC` in HOL Light may correspond to a `rewrite` or `simpl` tactic in other systems.

---

## FACT_LESS

### Name of formal statement
FACT_LESS

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let FACT_LESS = FACT_LT;;
```

### Informal statement
The `FACT_LESS` definition is equivalent to the `FACT_LT` definition.

### Informal sketch
* The definition simply assigns the `FACT_LT` definition to `FACT_LESS`, implying that `FACT_LESS` is an alias or an equivalent representation of `FACT_LT`.
* This step involves no complex proof or construction, merely a renaming or reassignment of an existing definition.
* The key logical stage here is the recognition of equivalence between `FACT_LESS` and `FACT_LT`, which allows for their interchangeability in certain contexts.

### Mathematical insight
The definition of `FACT_LESS` as `FACT_LT` suggests that these two concepts are mathematically equivalent or serve the same purpose within the formal system. This equivalence might be used to simplify expressions, leverage existing proofs, or maintain consistency across different parts of the theory.

### Dependencies
#### Definitions
* `FACT_LT`

### Porting notes
When porting this definition to another proof assistant, ensure that the equivalent of `FACT_LT` is defined and accessible. The process involves a straightforward assignment or equivalence declaration, depending on the target system's syntax for defining or stating equivalences between concepts.

---

## LESS_EQ_SUC_REFL

### Name of formal statement
LESS_EQ_SUC_REFL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LESS_EQ_SUC_REFL = prove(`!n. n <= SUC n`,REWRITE_TAC[LE; LE_REFL]);;
```

### Informal statement
For all natural numbers `n`, `n` is less than or equal to the successor of `n`.

### Informal sketch
* The proof involves a universal quantification over all natural numbers `n`.
* The `REWRITE_TAC` tactic is used with the `LE` and `LE_REFL` theorems to establish the inequality `n <= SUC n`.
* The key insight is that the successor function `SUC` increments a number, and the less-than-or-equal relation `<=` is reflexive, as stated by `LE_REFL`.

### Mathematical insight
This theorem formalizes a fundamental property of the natural numbers, where every number is less than or equal to its successor. This property is essential in various mathematical proofs and constructions, particularly in Peano arithmetic and order theory.

### Dependencies
* Theorems:
	+ `LE`
	+ `LE_REFL`
* Definitions:
	+ `SUC` (successor function)

### Porting notes
When translating this theorem into other proof assistants, ensure that the successor function and the less-than-or-equal relation are defined and handled correctly. Additionally, the `REWRITE_TAC` tactic may need to be replaced with equivalent tactics or rewriting mechanisms available in the target proof assistant.

---

## LESS_EQ_ADD

### Name of formal statement
LESS_EQ_ADD

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let LESS_EQ_ADD = LE_ADD;;
```

### Informal statement
The LESS_EQ_ADD definition is equivalent to the LE_ADD definition.

### Informal sketch
* The definition of LESS_EQ_ADD is a straightforward assignment, where it is set to be equal to LE_ADD.
* This implies that any properties or theorems proven about LE_ADD can be directly applied to LESS_EQ_ADD, given the equivalence of the two.

### Mathematical insight
This definition provides an alias or an alternative name for the existing LE_ADD concept, potentially for convenience, readability, or to fit into a specific theoretical framework. It emphasizes the equality of two concepts, allowing for their interchangeable use in proofs and definitions.

### Dependencies
#### Definitions
* `LE_ADD`

### Porting notes
When translating this definition into another proof assistant, ensure that the target system supports equivalent definitions or aliases. In systems like Lean, Coq, or Isabelle, this might involve using specific keywords or syntax for defining or declaring such equivalences. For example, in Lean, one might use the `def` keyword for a similar purpose, while in Coq, the `Definition` keyword could be used. In Isabelle, the `definition` command serves a similar role.

---

## GREATER_EQ

### Name of formal statement
GREATER_EQ

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let GREATER_EQ = GE;;
```

### Informal statement
The `GREATER_EQ` definition is equivalent to the greater-than-or-equal-to relation `GE`.

### Informal sketch
* The definition directly assigns the `GE` relation to `GREATER_EQ`, indicating that `GREATER_EQ` is an alias or synonym for `GE`.
* This step involves recognizing that `GE` already represents the greater-than-or-equal-to relation, and thus `GREATER_EQ` inherits this meaning.

### Mathematical insight
This definition provides an alternative name for the greater-than-or-equal-to relation, which can enhance readability or compatibility in certain contexts by offering a more explicit or conventional naming for this relation.

### Dependencies
* `GE`

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, ensure that the equivalent of `GE` is correctly identified and assigned to `GREATER_EQ`. Note that different systems may have varying conventions for naming relations, so the exact implementation may differ. For example, in Lean, this might involve using the `≼` symbol or a similar definition, while in Coq, it could involve using `>=` within a specific context or library.

---

## LESS_EQUAL_ADD

### Name of formal statement
LESS_EQUAL_ADD

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LESS_EQUAL_ADD = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL LE_EXISTS)))
```

### Informal statement
For all x, y, and z, if x is less than or equal to y, then there exists a z such that x + z = y.

### Informal sketch
* The `GEN_ALL` indicates that the statement is universally quantified over all variables.
* The `EQ_IMP_RULE` is applied to the `LE_EXISTS` theorem, which states that for all x and y, if x is less than or equal to y, then there exists a z such that x + z = y.
* The `SPEC_ALL` suggests that the `LE_EXISTS` theorem is first specialized to all x, y, and then the implication rule is applied.
* The `fst` function is used to extract the first component of the resulting pair, which corresponds to the universally quantified statement.

### Mathematical insight
The LESS_EQUAL_ADD theorem provides a way to express the existence of a witness (z) that satisfies the equation x + z = y, given that x is less than or equal to y. This is a fundamental property of the less-than-or-equal-to relation and is used in various mathematical proofs.

### Dependencies
* `LE_EXISTS`
* `EQ_IMP_RULE`
* `GEN_ALL`
* `SPEC_ALL`

### Porting notes
When porting this theorem to other proof assistants, note that the `GEN_ALL` and `SPEC_ALL` may be replaced with explicit universal quantification and instantiation, respectively. Additionally, the `EQ_IMP_RULE` may be replaced with a similar implication rule or a modus ponens tactic. The `LE_EXISTS` theorem may need to be defined or imported separately, depending on the target proof assistant.

---

## LESS_EQ_IMP_LESS_SUC

### Name of formal statement
LESS_EQ_IMP_LESS_SUC

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LESS_EQ_IMP_LESS_SUC = GEN_ALL(snd(EQ_IMP_RULE(SPEC_ALL LT_SUC_LE)))
```

### Informal statement
For all `x` and `y`, if `x` is less than or equal to `y`, then the successor of `x` is less than or equal to the successor of `y`.

### Informal sketch
* The proof starts with the assumption that `x` is less than or equal to `y`.
* It then applies the `EQ_IMP_RULE` to the `LT_SUC_LE` theorem, which states that if `x` is less than `y`, then the successor of `x` is less than or equal to the successor of `y`.
* The `SPEC_ALL` tactic is used to instantiate the `LT_SUC_LE` theorem for all `x` and `y`.
* The `snd` function is used to extract the second component of the implication rule, which gives the desired conclusion.
* The `GEN_ALL` tactic is used to generalize the result for all `x` and `y`.

### Mathematical insight
This theorem provides a way to relate the ordering of numbers to the ordering of their successors. It is a fundamental property of the less-than-or-equal-to relation and is used in various proofs involving arithmetic and ordering.

### Dependencies
* `LT_SUC_LE`
* `EQ_IMP_RULE`
* `GEN_ALL`
* `SPEC_ALL`
* `snd`

### Porting notes
When porting this theorem to another proof assistant, note that the `EQ_IMP_RULE` and `GEN_ALL` tactics may need to be replaced with equivalent constructs. Additionally, the `SPEC_ALL` and `snd` functions may need to be adjusted depending on the specific proof assistant's handling of binders and implications.

---

## LESS_IMP_LESS_OR_EQ

### Name of formal statement
LESS_IMP_LESS_OR_EQ

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let LESS_IMP_LESS_OR_EQ = LT_IMP_LE;;
```

### Informal statement
If `a` is less than `b`, then `a` is less than or equal to `b`.

### Informal sketch
* The definition `LESS_IMP_LESS_OR_EQ` is based on the implication `LT_IMP_LE`, which establishes a relationship between the less-than (`<`) and less-than-or-equal-to (`≤`) relations.
* This implication is fundamental in establishing a connection between strict inequality and non-strict inequality.
* The key logical stage involves recognizing that if `a` is strictly less than `b`, it naturally follows that `a` is less than or equal to `b`, as the less-than-or-equal-to relation includes equality.

### Mathematical insight
The `LESS_IMP_LESS_OR_EQ` definition captures a basic property of order relations, specifically how strict order (less than) implies non-strict order (less than or equal to). This is crucial in mathematical reasoning about inequalities and is used extensively in various mathematical proofs and derivations.

### Dependencies
* `LT_IMP_LE`

### Porting notes
When translating `LESS_IMP_LESS_OR_EQ` into other proof assistants like Lean, Coq, or Isabelle, ensure that the equivalent of `LT_IMP_LE` is defined or available. The translation should preserve the implication from strict to non-strict inequality, which might be expressed using different notations or constructs in the target system. Pay attention to how each system handles implications and order relations, as the direct translation of `let` bindings and implications might vary.

---

## LESS_MONO_ADD

### Name of formal statement
LESS_MONO_ADD

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LESS_MONO_ADD = GEN_ALL(snd(EQ_IMP_RULE(SPEC_ALL LT_ADD_RCANCEL)));;
```

### Informal statement
For all numbers $a$, $b$, and $c$, if $a$ is less than $b$, then $a + c$ is less than $b + c$.

### Informal sketch
* Start with the `LT_ADD_RCANCEL` theorem, which states that for all numbers $a$, $b$, and $c$, if $a$ is less than $b$, then $a + c$ is less than $b + c$.
* Apply `SPEC_ALL` to `LT_ADD_RCANCEL` to obtain a version of the theorem with explicit universal quantification over $a$, $b$, and $c$.
* Use `EQ_IMP_RULE` to convert the implication in the theorem into an equivalent form.
* Apply `snd` to extract the conclusion of the implication.
* Finally, apply `GEN_ALL` to generalize the result for all possible values of $a$, $b$, and $c$.

### Mathematical insight
The `LESS_MONO_ADD` theorem is a fundamental property of the less-than relation in arithmetic, stating that adding the same value to both sides of an inequality preserves the inequality. This theorem is crucial in many mathematical proofs, particularly in algebra and analysis, where inequalities are used extensively.

### Dependencies
* `LT_ADD_RCANCEL`
* `GEN_ALL`
* `EQ_IMP_RULE`
* `SPEC_ALL`

### Porting notes
When translating this theorem into other proof assistants, note that the `GEN_ALL` and `SPEC_ALL` functions may be represented differently. For example, in Lean, the `GEN_ALL` function is not needed explicitly, as universal quantification is implicit in the `∀` symbol. Additionally, the `EQ_IMP_RULE` and `snd` functions may be replaced with equivalent constructs, such as `implies` and `conclusion`, respectively.

---

## LESS_SUC

### Name of formal statement
LESS_SUC

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LESS_SUC = prove(`!m n. m < n ==> m < (SUC n)`,MESON_TAC[LT])
```

### Informal statement
For all natural numbers `m` and `n`, if `m` is less than `n`, then `m` is less than the successor of `n`.

### Informal sketch
* The proof starts with the assumption that `m` is less than `n`, which is denoted by `m < n`.
* The `MESON_TAC` tactic is applied with the `LT` theorem to derive the conclusion that `m` is less than the successor of `n`, denoted as `m < (SUC n)`.
* The key logical stage involves using the properties of the less-than relation and the definition of the successor function to establish the desired inequality.

### Mathematical insight
This theorem is a fundamental property of the natural numbers, establishing a relationship between the less-than relation and the successor function. It is essential in many mathematical proofs, particularly those involving induction and inequalities.

### Dependencies
* Theorems:
	+ `LT` (less-than relation)
* Definitions:
	+ `SUC` (successor function)

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of the less-than relation and the successor function. In some systems, these may be defined differently or have different properties. Additionally, the `MESON_TAC` tactic may not have a direct equivalent, so the proof strategy may need to be adapted to the target system's proof automation mechanisms.

---

## LESS_CASES

### Name of formal statement
LESS_CASES

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let LESS_CASES = LTE_CASES;;
```

### Informal statement
LESS_CASES is defined to be equal to LTE_CASES.

### Informal sketch
* The definition directly assigns the value of `LTE_CASES` to `LESS_CASES`, implying an equivalence or a simple renaming.
* This step does not involve complex logical deductions but rather a straightforward assignment.

### Mathematical insight
This definition suggests that `LESS_CASES` and `LTE_CASES` are interchangeable or represent the same concept within the formal development, possibly for the sake of notation convenience or to align with different notational conventions in various parts of the theory.

### Dependencies
#### Definitions
- `LTE_CASES`

### Porting notes
When porting this definition to another proof assistant, ensure that the equivalent of `LTE_CASES` is defined and accessible. The translation should be straightforward, as it involves a simple assignment or equivalence statement. Note that the specifics of how definitions are declared and used may vary between proof assistants (e.g., `let` in HOL Light vs. `definition` in Isabelle).

---

## LESS_EQ

### Name of formal statement
LESS_EQ

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let LESS_EQ = GSYM LE_SUC_LT;;
```

### Informal statement
The LESS_EQ relation is defined as the symmetric closure of the LE_SUC_LT relation, denoted by GSYM.

### Informal sketch
* The definition utilizes the `GSYM` operator to derive the symmetric property of the `LESS_EQ` relation from the `LE_SUC_LT` relation.
* This step involves recognizing the `LE_SUC_LT` relation as a foundational ordering relation and applying the `GSYM` operator to establish the corresponding equality relation.

### Mathematical insight
The LESS_EQ relation is a fundamental concept in formalizing ordering relations, allowing for the expression of "less than or equal to" comparisons. This definition fits into the broader theory of order relations, enabling the development of more complex mathematical structures and theorems.

### Dependencies
#### Definitions
* `GSYM`
* `LE_SUC_LT`

### Porting notes
When translating this definition into other proof assistants, consider the following:
* The `GSYM` operator may need to be replaced with an equivalent construct, such as a symmetric closure operator or a relational converse operator, depending on the target system's library and syntax.
* Ensure that the `LE_SUC_LT` relation is properly defined and available in the target system, as it serves as the foundation for the `LESS_EQ` relation.

---

## LESS_OR_EQ

### Name of formal statement
LESS_OR_EQ

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let LESS_OR_EQ = LE_LT;;
```

### Informal statement
LESS_OR_EQ is defined to be equal to LE_LT.

### Informal sketch
* The definition simply assigns the existing `LE_LT` relation to the new name `LESS_OR_EQ`, implying that `LESS_OR_EQ` is an alias for `LE_LT`.
* This step does not involve complex proof tactics but is a straightforward renaming for potentially notational convenience or clarity in later proofs.

### Mathematical insight
The definition of `LESS_OR_EQ` as `LE_LT` suggests that in this context, "less or equal to" is being represented by the same relation as "less than or equal to", highlighting a potential notational convenience or equivalence in the formal development.

### Dependencies
* `LE_LT`

### Porting notes
When translating this definition into another proof assistant, ensure that the equivalent of `LE_LT` is correctly identified and assigned to `LESS_OR_EQ`. This may involve understanding the specific notational conventions and definitions of relations in the target system.

---

## LESS_ADD_1

### Name of formal statement
LESS_ADD_1

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LESS_ADD_1 = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL (REWRITE_RULE[ADD1] LT_EXISTS))))
```

### Informal statement
For all x and y, if x + 1 is less than y, then there exists a z such that x is less than z and z is less than y.

### Informal sketch
* The theorem `LESS_ADD_1` is derived using the `GEN_ALL` tactic, which generalizes the result for all possible values.
* The `EQ_IMP_RULE` tactic is applied to establish an equivalence implication.
* The `SPEC_ALL` tactic is used to instantiate a universal quantification.
* The `REWRITE_RULE` tactic with `[ADD1]` is applied to rewrite the expression using the definition of addition.
* The `LT_EXISTS` theorem is used to establish the existence of a intermediate value `z` such that `x` is less than `z` and `z` is less than `y`.

### Mathematical insight
The theorem `LESS_ADD_1` provides a key property of the less-than relation with respect to addition, allowing for the establishment of a relationship between `x`, `y`, and an intermediate value `z`. This property is essential in various mathematical proofs involving inequalities and ordering.

### Dependencies
* Theorems:
	+ `LT_EXISTS`
	+ `EQ_IMP_RULE`
* Definitions:
	+ `ADD1`
* Inductive rules: None

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of binders and quantifiers. The `GEN_ALL` tactic may need to be replaced with a corresponding universal quantification mechanism. Additionally, the `REWRITE_RULE` tactic may require a different formulation depending on the target proof assistant's rewriting mechanisms.

---

## SUC_SUB1

### Name of formal statement
SUC_SUB1

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SUC_SUB1 = prove(`!m. SUC m - 1 = m`, REWRITE_TAC[num_CONV `1`; SUB_SUC; SUB_0])
```

### Informal statement
For all natural numbers `m`, the successor of `m` minus 1 is equal to `m`.

### Informal sketch
* The proof involves rewriting the expression `SUC m - 1` to show its equivalence to `m`.
* It utilizes the `REWRITE_TAC` tactic to apply the following theorems in sequence:
  + `num_CONV `1``: likely a conversion for the numeral 1
  + `SUB_SUC`: a theorem about subtraction and successor
  + `SUB_0`: a theorem about subtraction and zero
* These rewrites aim to simplify the expression to directly show `SUC m - 1 = m`, leveraging properties of arithmetic operations and possibly the definition of the successor function.

### Mathematical insight
This theorem provides a basic property of arithmetic in the context of natural numbers, specifically how the successor function interacts with subtraction. It's foundational in establishing the consistency and expected behavior of arithmetic operations within the formal system.

### Dependencies
#### Theorems
* `SUB_SUC`
* `SUB_0`
* `num_CONV `1``

### Porting notes
When translating this theorem into another proof assistant, ensure that the successor function (`SUC`), subtraction, and any relevant arithmetic properties are defined and behave similarly. Note that different systems may handle numerals, successor functions, and arithmetic operations differently, potentially requiring adjustments to the proof strategy or the application of specific tactics or theorems.

---

## LESS_MONO_EQ

### Name of formal statement
LESS_MONO_EQ

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let LESS_MONO_EQ = LT_SUC;;
```

### Informal statement
LESS_MONO_EQ is defined as LT_SUC.

### Informal sketch
* The definition of LESS_MONO_EQ directly assigns it the value of LT_SUC, indicating a relationship between a less-than comparison and successor function in a specific context.

### Mathematical insight
This definition likely plays a role in establishing properties of order relations or arithmetic operations, potentially serving as a foundation for more complex proofs involving comparisons or successor functions.

### Dependencies
* `LT_SUC`

### Porting notes
When translating this definition into another proof assistant, ensure that the equivalent of `LT_SUC` is correctly defined and accessible. The translation should preserve the direct assignment of LESS_MONO_EQ to this value, as it forms the basis of subsequent proofs or definitions that rely on this relationship.

---

## LESS_ADD_SUC

### Name of formal statement
LESS_ADD_SUC

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LESS_ADD_SUC = prove (`!m n. m < m + SUC n`, REWRITE_TAC[ADD_CLAUSES; LT_SUC_LE; LE_ADD])
```

### Informal statement
For all natural numbers `m` and `n`, `m` is less than `m` plus the successor of `n`.

### Informal sketch
* The proof starts by considering the universal quantification over `m` and `n`, aiming to establish the inequality `m < m + SUC n`.
* It then applies `REWRITE_TAC` with the `ADD_CLAUSES`, `LT_SUC_LE`, and `LE_ADD` theorems to simplify and derive the desired inequality.
* The use of `ADD_CLAUSES` suggests a case analysis based on the definition of addition, potentially breaking down the addition into its recursive definition.
* `LT_SUC_LE` and `LE_ADD` likely play a role in establishing the relationship between less-than and addition, possibly leveraging properties of successor and the less-than relation.

### Mathematical insight
This theorem captures a fundamental property of arithmetic, specifically how the less-than relation behaves with respect to addition and the successor function. It's essential for establishing further properties of arithmetic and inequalities in the context of natural numbers.

### Dependencies
* Theorems:
  + `ADD_CLAUSES`
  + `LT_SUC_LE`
  + `LE_ADD`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to how each system handles arithmetic operations, successor functions, and less-than relations. Specifically, ensure that the ported version correctly applies equivalent theorems or axioms for `ADD_CLAUSES`, `LT_SUC_LE`, and `LE_ADD`, as these are crucial for the proof. Additionally, consider the differences in how universal quantification and rewriting tactics are implemented in the target system.

---

## LESS_REFL

### Name of formal statement
LESS_REFL

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let LESS_REFL = LT_REFL;;
```

### Informal statement
The LESS_REFL definition is equivalent to the LT_REFL definition, establishing a relationship between less-than and its reflexive property.

### Informal sketch
* The definition `LESS_REFL` is directly assigned the value of `LT_REFL`, implying that the less-than relation's reflexive property is being defined in terms of an existing less-than reflexive (`LT_REFL`) property.
* This step suggests a straightforward equivalence or identity between two concepts, likely leveraging existing properties or theorems related to `LT_REFL`.

### Mathematical insight
This definition provides a foundation for establishing properties of the less-than relation, specifically its reflexive aspect. It implies that the concept of "less than" includes the notion that something is not less than itself, which is a fundamental property in order relations.

### Dependencies
#### Definitions
* `LT_REFL`

### Porting notes
When translating this definition into another proof assistant, ensure that the equivalent of `LT_REFL` is defined and accessible. The translation should maintain the direct assignment or equivalence, as the purpose is to establish a foundational property of the less-than relation. Pay attention to how the target system handles definitions and ensure that the `LESS_REFL` definition is properly linked to its `LT_REFL` counterpart.

---

## INV_SUC_EQ

### Name of formal statement
INV_SUC_EQ

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let INV_SUC_EQ = SUC_INJ;;
```

### Informal statement
The definition `INV_SUC_EQ` is equivalent to `SUC_INJ`, which implies that the successor function is injective.

### Informal sketch
* The definition relies on the `SUC_INJ` property, which states that the successor function is injective, meaning that if the successors of two numbers are equal, then the numbers themselves are equal.
* This definition does not involve a complex proof, as it is a direct assignment of `SUC_INJ` to `INV_SUC_EQ`.
* The key concept here is the injectivity of the successor function, which is a fundamental property in Peano arithmetic.

### Mathematical insight
The definition `INV_SUC_EQ` is important because it highlights the injective nature of the successor function, which is crucial in various proofs involving natural numbers, such as those related to induction and the uniqueness of the natural numbers.

### Dependencies
#### Definitions
* `SUC_INJ`

### Porting notes
When translating this definition into other proof assistants, ensure that the equivalent of `SUC_INJ` is defined and accessible. In systems like Lean, Coq, or Isabelle, this might involve using existing libraries or proving the injectivity of the successor function as a lemma before defining `INV_SUC_EQ`. Note that the exact names and structures may vary, but the underlying mathematical concept remains the same.

---

## LESS_EQ_CASES

### Name of formal statement
LESS_EQ_CASES

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let LESS_EQ_CASES = LE_CASES;;
```

### Informal statement
The LESS_EQ_CASES definition is equivalent to the LE_CASES definition.

### Informal sketch
* The definition directly assigns the value of `LE_CASES` to `LESS_EQ_CASES`, implying that the cases for less-than-or-equal-to (`LESS_EQ`) are the same as those for less-than-or-equal-to (`LE`).
* This suggests a relationship or equivalence between the two, possibly due to the nature of the relations or the specific logic system being used.

### Mathematical insight
This definition implies that the distinction between `LESS_EQ` and `LE` cases is either not present or not significant in this context, allowing for their direct equivalence. This could be due to the properties of the relations themselves or the specific requirements of the theory being developed.

### Dependencies
#### Definitions
* `LE_CASES`

### Porting notes
When translating this definition into another proof assistant, ensure that the equivalent of `LE_CASES` is properly defined and accessible. Note that the direct assignment implies a straightforward equivalence, but the actual implementation may vary depending on how relations and cases are handled in the target system.

---

## LESS_EQ_TRANS

### Name of formal statement
LESS_EQ_TRANS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LESS_EQ_TRANS = LE_TRANS;;
```

### Informal statement
For all elements a, b, and c, if a is less than or equal to b and b is less than or equal to c, then a is less than or equal to c.

### Informal sketch
* The theorem `LESS_EQ_TRANS` is based on the transitivity property of the less-than-or-equal-to relation, denoted by `LE_TRANS`.
* The proof likely involves assuming `a <= b` and `b <= c`, then using the definition of `LE` to derive `a <= c`.
* The `LE_TRANS` tactic or definition is key to establishing this transitivity property.

### Mathematical insight
The `LESS_EQ_TRANS` theorem captures the transitive nature of the less-than-or-equal-to relation, which is fundamental in order theory and essential for many mathematical proofs involving inequalities.

### Dependencies
* `LE_TRANS`

### Porting notes
When porting `LESS_EQ_TRANS` to another proof assistant, ensure that the target system has a similar transitivity property for its less-than-or-equal-to relation. Pay attention to how the system handles relational properties and transitivity, as this may involve different tactics or axioms.

---

## LESS_THM

### Name of formal statement
LESS_THM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LESS_THM = CONJUNCT2 LT;;
```

### Informal statement
The theorem LESS_THM is defined as the second conjunct of the theorem LT.

### Informal sketch
* The proof of LESS_THM involves extracting a specific part of the theorem `LT` using the `CONJUNCT2` function, which suggests that `LT` is a conjunction and `LESS_THM` represents one of its components.
* The key logical stage here is the application of `CONJUNCT2` to `LT`, implying that `LT` has at least two conjuncts and `LESS_THM` is the second one.

### Mathematical insight
This theorem is important for modularizing proofs and theorems, allowing for the reuse of specific parts of previously established results. The `CONJUNCT2` function is a way to access and isolate components of conjunctive statements, which is crucial in formal proofs where theorems often have multiple parts.

### Dependencies
#### Theorems
* `LT`

### Porting notes
When translating this into another proof assistant, ensure that there is an equivalent mechanism for extracting conjuncts from a theorem. In some systems, this might involve pattern matching or using a tactic specifically designed for manipulating conjunctions. Note that the exact implementation of `CONJUNCT2` might differ, so understanding its role in HOL Light and finding its counterpart in the target system is essential.

---

## GREATER

### Name of formal statement
GREATER

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let GREATER = GT;;
```

### Informal statement
The constant `GREATER` is defined to be the greater-than relation `GT`.

### Informal sketch
* The definition directly assigns the meaning of `GT` to `GREATER`, implying a simple aliasing or renaming of the `GT` relation.
* This step involves recognizing `GT` as a predefined greater-than relation in the HOL Light system.

### Mathematical insight
This definition provides a convenient shorthand or alternative name for the greater-than relation, which can enhance readability or conform to specific notational conventions in mathematical expressions or proofs.

### Dependencies
#### Definitions
* `GT`

### Porting notes
When translating this definition into another proof assistant, ensure that an equivalent greater-than relation is defined or available. The translation should preserve the exact semantic meaning of `GREATER` as an alias for this relation.

---

## LESS_EQ_0

### Name of formal statement
LESS_EQ_0

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let LESS_EQ_0 = CONJUNCT1 LE;;
```

### Informal statement
LESS_EQ_0 is defined as the first conjunct of the less-than-or-equal-to relation, denoted by LE.

### Informal sketch
* The definition of LESS_EQ_0 relies on the `CONJUNCT1` function, which extracts the first part of a conjunction.
* The `LE` relation is used as the input to `CONJUNCT1`, implying that LESS_EQ_0 is derived from the definition or properties of `LE`.
* The key logical stage involves understanding how `CONJUNCT1` operates on `LE` to yield LESS_EQ_0.

### Mathematical insight
The definition of LESS_EQ_0 is important because it provides a foundational element for constructing or proving statements involving the less-than-or-equal-to relation. It suggests that the less-than-or-equal-to relation can be decomposed or analyzed in terms of its conjuncts, and LESS_EQ_0 represents a crucial part of this decomposition.

### Dependencies
* `CONJUNCT1`
* `LE`

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system handles conjunctions and the extraction of conjuncts. The equivalent of `CONJUNCT1` might be a built-in function, a tactic, or require a specific library or module. Additionally, ensure that the less-than-or-equal-to relation (`LE`) is defined or imported correctly, as its properties and behavior may vary between systems.

---

## OR_LESS

### Name of formal statement
OR_LESS

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let OR_LESS = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL LE_SUC_LT)));;
```

### Informal statement
For all propositions `p` and `q`, `OR_LESS` is defined as the universal generalization of the first projection of the implication rule applied to the specialization of all instances of `LE_SUC_LT`, which itself denotes the less-than relation between a number and its successor.

### Informal sketch
* The definition begins with `LE_SUC_LT`, which represents a fundamental property that a number is less than its successor.
* `SPEC_ALL LE_SUC_LT` specializes this property for all instances, making it applicable to any number.
* `EQ_IMP_RULE` applies the implication rule to this specialized property, effectively stating that if two numbers are equal, then the first is less than the successor of the second if and only if the first is less than the successor of the second.
* `fst` takes the first projection of the result, focusing on the forward direction of the implication.
* Finally, `GEN_ALL` universally generalizes this result, making it applicable to all propositions.

### Mathematical insight
`OR_LESS` seems to encapsulate a basic property related to the ordering of numbers, specifically leveraging the less-than relation and the concept of successors. This definition is foundational in constructing more complex mathematical structures and theorems involving order relations and potentially equality.

### Dependencies
- **Theorems and Definitions:**
  - `LE_SUC_LT`
  - `EQ_IMP_RULE`
- **Tactics and Functions:**
  - `GEN_ALL`
  - `fst`
  - `SPEC_ALL`

### Porting notes
When porting `OR_LESS` to another proof assistant like Lean, Coq, or Isabelle, pay special attention to how each system handles universal generalization, implication rules, and projections. The direct equivalent of `GEN_ALL`, `EQ_IMP_RULE`, `SPEC_ALL`, and `fst` may vary, requiring careful translation to preserve the logical structure. Additionally, the representation of `LE_SUC_LT` and how it's specialized and generalized might differ, necessitating an understanding of how each proof assistant manages such properties and their instantiations.

---

## SUB_EQUAL_0

### Name of formal statement
SUB_EQUAL_0

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let SUB_EQUAL_0 = SUB_REFL;;
```

### Informal statement
SUB_EQUAL_0 is defined as the reflexive property of equality, denoted by SUB_REFL.

### Informal sketch
* The definition of SUB_EQUAL_0 directly references the `SUB_REFL` concept, implying that it is based on the reflexive property of a relation, where every element is related to itself.
* This step does not involve complex proof tactics but rather a straightforward definition that sets the foundation for further equalities or substitutions.

### Mathematical insight
The definition of SUB_EQUAL_0, equating it to `SUB_REFL`, highlights the fundamental principle that any entity is equal to itself, which is a cornerstone of equality in mathematics. This principle is crucial for establishing more complex equalities and substitutions in formal systems.

### Dependencies
#### Definitions
* `SUB_REFL`

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, ensure that the equivalent of `SUB_REFL` is properly defined or imported. In many systems, this reflexive property of equality is a basic axiom or theorem, so identifying and using the correct counterpart is essential for a successful port.

---

## SUB_MONO_EQ

### Name of formal statement
SUB_MONO_EQ

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let SUB_MONO_EQ = SUB_SUC;;
```

### Informal statement
The definition `SUB_MONO_EQ` is equivalent to `SUB_SUC`.

### Informal sketch
* The definition directly assigns `SUB_SUC` to `SUB_MONO_EQ`, indicating that `SUB_MONO_EQ` is another name for the `SUB_SUC` concept.
* No complex proof steps are involved; it's a straightforward definition.

### Mathematical insight
This definition suggests that the concept of `SUB_SUC` is being aliased or identified with `SUB_MONO_EQ`, possibly for notational convenience, to emphasize a particular property, or to fit into a specific theoretical framework. Understanding the context in which `SUB_SUC` is used and why it's being equated with `SUB_MONO_EQ` is crucial for grasping the significance of this definition.

### Dependencies
#### Definitions
* `SUB_SUC`

### Porting notes
When porting this definition to another proof assistant, ensure that the equivalent of `SUB_SUC` is properly defined and accessible. The porting process should be straightforward since it involves a simple definition. However, the context and usage of `SUB_SUC` and its relationship to `SUB_MONO_EQ` in the target system should be carefully considered to ensure semantic equivalence.

---

## NOT_SUC_LESS_EQ

### Name of formal statement
NOT_SUC_LESS_EQ

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let NOT_SUC_LESS_EQ = prove (`!n m. ~(SUC n <= m) <=> m <= n`,
                             REWRITE_TAC[NOT_LE; LT] THEN
                             MESON_TAC[LE_LT]);;
```

### Informal statement
For all natural numbers n and m, it is not the case that the successor of n is less than or equal to m if and only if m is less than or equal to n.

### Informal sketch
* The proof involves rewriting the inequality using `NOT_LE` and `LT` to simplify the expression.
* The `MESON_TAC` tactic is then applied with `LE_LT` to derive the conclusion.
* The key logical stage is transforming the negation of the successor's inequality into an equivalent statement about the relationship between m and n.
* This transformation relies on the properties of less than or equal to (`<=`) and the successor function (`SUC`).

### Mathematical insight
This theorem provides an important equivalence that helps in manipulating inequalities involving the successor function, which is crucial in Peano arithmetic and other formalizations of natural numbers. It shows that the negation of a successor being less than or equal to another number is logically equivalent to the other number being less than or equal to the original number, which can be a useful tool in proofs involving natural numbers.

### Dependencies
#### Theorems
* `NOT_LE`
* `LT`
* `LE_LT`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system handles the successor function and inequalities. Specifically, ensure that the properties of `NOT_LE` and `LT` are appropriately translated, and that the `MESON_TAC` tactic's role is replicated, potentially using equivalent tactics or built-in automation in the target system.

---

## SUC_NOT

### Name of formal statement
SUC_NOT

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let SUC_NOT = GSYM NOT_SUC;;
```

### Informal statement
The definition `SUC_NOT` is given by applying the `GSYM` operator to `NOT_SUC`.

### Informal sketch
* The definition involves using the `GSYM` operator, which likely refers to a symmetric or inverse operation, applied to `NOT_SUC`.
* Understanding `NOT_SUC` is crucial, as it seems to be a negation or complement of a successor function `SUC`.
* The `GSYM` operator may imply a form of duality or reversal in the context of the successor function.

### Mathematical insight
This definition appears to establish a relationship between a successor function and its negation or complement, potentially in the context of Peano arithmetic or a similar formal system. The use of `GSYM` suggests a symmetric property or a way to derive a complementary concept from `NOT_SUC`.

### Dependencies
#### Definitions
* `NOT_SUC`
* `GSYM`
#### Theorems or Axioms
None explicitly mentioned, but the definition implies a dependency on the underlying formal system's treatment of successor functions and negation.

### Porting notes
When translating this definition into another proof assistant, ensure that the equivalent of `GSYM` is correctly interpreted. This might involve understanding how the target system handles symmetric operations or inverses, especially in the context of arithmetic or algebraic structures. Additionally, the definition of `NOT_SUC` and how it interacts with `GSYM` should be carefully examined to ensure consistency with the original formal system's intent.

---

## LESS_LESS_CASES

### Name of formal statement
LESS_LESS_CASES

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LESS_LESS_CASES = prove(`!m n:num. (m = n) \/ m < n \/ n < m`, MESON_TAC[LT_CASES])
```

### Informal statement
For all natural numbers m and n, either m is equal to n, or m is less than n, or n is less than m.

### Informal sketch
* The theorem `LESS_LESS_CASES` is proven using the `MESON_TAC` tactic, which applies a set of meson rules to solve the goal.
* The proof relies on the `LT_CASES` theorem, which provides cases for the less-than relation on natural numbers.
* The overall strategy is to consider all possible cases for the relationship between two natural numbers m and n, and show that one of the three conditions (equality, m less than n, or n less than m) must hold.

### Mathematical insight
This theorem captures the trichotomy property of the less-than relation on natural numbers, which states that for any two natural numbers, they are either equal or one is less than the other. This property is fundamental to the ordering of natural numbers and is used extensively in mathematical proofs.

### Dependencies
* `LT_CASES`
* `MESON_TAC`

### Porting notes
When porting this theorem to another proof assistant, note that the `MESON_TAC` tactic may not have a direct equivalent. Instead, the proof may need to be reconstructed using the proof assistant's native tactics and rules. Additionally, the `LT_CASES` theorem may need to be ported or proven separately in the target system.

---

## NOT_LESS_EQUAL

### Name of formal statement
NOT_LESS_EQUAL

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let NOT_LESS_EQUAL = NOT_LE;;
```

### Informal statement
NOT_LESS_EQUAL is defined as the negation of less than or equal to, denoted by NOT_LE.

### Informal sketch
* The definition of NOT_LESS_EQUAL is straightforward, relying on the existing definition of `NOT_LE`.
* The key logical stage involves understanding that NOT_LESS_EQUAL is the negation of the less than or equal to relation.
* This definition does not require a complex proof or construction, as it directly builds upon existing definitions.

### Mathematical insight
The NOT_LESS_EQUAL definition is important because it provides a concise way to express the negation of the less than or equal to relation, which is a fundamental concept in mathematics. This definition fits into the broader theory of inequalities and is a canonical construction in many mathematical and logical frameworks.

### Dependencies
#### Definitions
* `NOT_LE`

### Porting notes
When translating this definition into other proof assistants, ensure that the equivalent of `NOT_LE` is defined and accessible. The translation should be straightforward, as it involves a simple definition. However, pay attention to how the target system handles negation and relational operators to ensure a correct and equivalent definition.

---

## LESS_EQ_EXISTS

### Name of formal statement
LESS_EQ_EXISTS

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let LESS_EQ_EXISTS = LE_EXISTS;;
```

### Informal statement
The LESS_EQ_EXISTS definition is equivalent to the LE_EXISTS definition, where LE_EXISTS is likely a previously defined concept related to the existence of a less-than-or-equal-to relation.

### Informal sketch
* The definition directly maps `LESS_EQ_EXISTS` to `LE_EXISTS`, suggesting that the existence of a less-than-or-equal-to relation is being defined in terms of a previously established concept.
* This step likely involves recognizing that the less-than-or-equal-to relation can be expressed in terms of an existing less-than relation, possibly leveraging properties of order relations.
* Key HOL Light terms involved include `LE_EXISTS`, which is directly assigned to `LESS_EQ_EXISTS`.

### Mathematical insight
The definition of `LESS_EQ_EXISTS` in terms of `LE_EXISTS` highlights the interplay between different relational properties, specifically how existence under one relation can imply existence under another related relation. This construction is important for building a coherent theory of order relations, where various relations (less-than, less-than-or-equal-to, etc.) need to be consistently defined and related to one another.

### Dependencies
#### Definitions
* `LE_EXISTS`

### Porting notes
When translating this definition into another proof assistant, ensure that the equivalent of `LE_EXISTS` is properly defined and accessible. The direct assignment suggests a straightforward translation, but pay attention to how the target system handles relational properties and their interdependencies. In systems like Lean, Coq, or Isabelle, this might involve ensuring that the `LE_EXISTS` concept is defined and then simply mapping `LESS_EQ_EXISTS` to it, potentially using the respective system's syntax for definitions or equivalences.

---

## LESS_MONO_ADD_EQ

### Name of formal statement
LESS_MONO_ADD_EQ

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LESS_MONO_ADD_EQ = LT_ADD_RCANCEL;;
```

### Informal statement
For all numbers `a`, `b`, and `c`, if `a` is less than `b`, then `a + c` is less than `b + c`.

### Informal sketch
* The proof involves using the `LT_ADD_RCANCEL` theorem, which likely states that adding the same number to both sides of a less-than inequality preserves the inequality.
* The key step is applying `LT_ADD_RCANCEL` to the given less-than relation `a < b` to derive the less-than relation between `a + c` and `b + c`.

### Mathematical insight
This theorem is important because it establishes a basic property of inequalities under addition, which is crucial in various mathematical proofs involving comparisons and arithmetic operations. It ensures that adding the same value to both sides of an inequality does not change the direction of the inequality.

### Dependencies
* `LT_ADD_RCANCEL`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system handles arithmetic operations and inequalities. Specifically, look for theorems or lemmas similar to `LT_ADD_RCANCEL` and ensure that the addition operation is properly defined and supported.

---

## LESS_LESS_EQ_TRANS

### Name of formal statement
LESS_LESS_EQ_TRANS

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let LESS_LESS_EQ_TRANS = LTE_TRANS;;
```

### Informal statement
The `LESS_LESS_EQ_TRANS` definition states that the less-than-or-equal-to relation is transitive.

### Informal sketch
* The proof of transitivity involves assuming `a` is less than or equal to `b` and `b` is less than or equal to `c`, and then showing that `a` is less than or equal to `c`.
* This is typically done using the `LTE_TRANS` theorem, which is referenced directly in the definition.
* The key logical stage is applying transitivity to combine the two given inequalities.

### Mathematical insight
The `LESS_LESS_EQ_TRANS` definition is important because it establishes a fundamental property of the less-than-or-equal-to relation, allowing for the combination of inequalities in a chain.

### Dependencies
#### Theorems
* `LTE_TRANS`

### Porting notes
When porting this definition to another proof assistant, ensure that the target system has an equivalent `LTE_TRANS` theorem or axiom. If the system uses a different naming convention, adjust the reference accordingly. Note that some systems may automatically derive transitivity from other properties, in which case an explicit definition like `LESS_LESS_EQ_TRANS` might not be necessary.

---

## SUB_SUB

### Name of formal statement
SUB_SUB

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let SUB_SUB = ARITH_RULE
  `!b c. c <= b ==> (!a:num. a - (b - c) = (a + c) - b)`;;
```

### Informal statement
For all natural numbers `b` and `c` such that `c` is less than or equal to `b`, it holds that for all natural numbers `a`, the equation `a - (b - c) = (a + c) - b` is true.

### Informal sketch
* The statement `SUB_SUB` is a universally quantified implication, relying on the `ARITH_RULE` to establish an equality involving subtraction and addition within the natural numbers.
* The proof likely involves basic properties of arithmetic, such as the commutativity and associativity of addition, and the definition of subtraction in terms of addition and the additive inverse.
* Key steps might involve:
  + Using the definition of subtraction to expand `a - (b - c)` into `a + (- (b - c))`.
  + Applying properties of the additive inverse to simplify the expression.
  + Utilizing the `ARITH_RULE` to justify the arithmetic manipulations, possibly invoking `COMMUTATIVITY` and `ASSOCIATIVITY` of addition.

### Mathematical insight
The `SUB_SUB` definition captures a fundamental property of arithmetic that relates subtraction and addition. It is essential for establishing the consistency and coherence of arithmetic operations within the natural numbers, particularly in how subtraction interacts with addition. This property is crucial for more complex arithmetic derivations and is a foundational element in the construction of arithmetic theories.

### Dependencies
* `ARITH_RULE`
* Basic properties of natural number arithmetic, including:
  + `COMMUTATIVITY` of addition
  + `ASSOCIATIVITY` of addition
  + Definition of subtraction in terms of addition and additive inverse

### Porting notes
When translating `SUB_SUB` into another proof assistant like Lean, Coq, or Isabelle, pay attention to how each system handles arithmetic and the properties of natural numbers. Specifically, consider how subtraction is defined and how arithmetic rules are applied. The use of `ARITH_RULE` in HOL Light may correspond to specific tactics or automation in other systems, such as `ring` or `field` tactics in Coq, or the `arith` tactic in Isabelle. Ensure that the target system's arithmetic foundations are aligned with the intended meaning of `SUB_SUB`.

---

## LESS_CASES_IMP

### Name of formal statement
LESS_CASES_IMP

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LESS_CASES_IMP = ARITH_RULE
  `!m n:num. ~(m < n) /\ ~(m = n) ==> n < m`;;
```

### Informal statement
For all natural numbers `m` and `n`, if it is not the case that `m` is less than `n` and it is not the case that `m` is equal to `n`, then `n` is less than `m`.

### Informal sketch
* The proof starts with a universal quantification over two natural numbers `m` and `n`.
* It assumes two negated conditions: `m` is not less than `n` and `m` is not equal to `n`.
* From these assumptions, it deduces that `n` must be less than `m`, utilizing the `ARITH_RULE` to handle the arithmetic properties of natural numbers.
* The key logical stage involves using the properties of order relations (less than and equal to) on natural numbers to derive the conclusion.

### Mathematical insight
This statement captures a fundamental property of the ordering of natural numbers, specifically that if `m` is neither less than nor equal to `n`, then `n` must be less than `m`. This is a direct consequence of the trichotomy law for natural numbers, which states that for any two natural numbers `m` and `n`, exactly one of the following holds: `m < n`, `m = n`, or `m > n` (or equivalently, `n < m`).

### Dependencies
* `ARITH_RULE`
* Basic properties of natural numbers, including the trichotomy law

### Porting notes
When translating this theorem into another proof assistant, ensure that the target system has a similar `ARITH_RULE` or mechanism for handling arithmetic properties of natural numbers. Additionally, verify that the system's treatment of order relations (less than, equal to) on natural numbers aligns with the assumptions and conclusion of this theorem. Pay particular attention to how the system handles negated conditions and universal quantification, as these are crucial to the theorem's statement and proof.

---

## SUB_LESS_EQ

### Name of formal statement
SUB_LESS_EQ

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SUB_LESS_EQ = ARITH_RULE
  `!n m:num. (n - m) <= n`;;
```

### Informal statement
For all natural numbers `n` and `m`, the difference `n - m` is less than or equal to `n`.

### Informal sketch
* The proof involves recognizing that subtracting `m` from `n` either results in a smaller number or, if `m` is zero, leaves `n` unchanged.
* The `ARITH_RULE` suggests that this is derived directly from basic properties of arithmetic operations, possibly leveraging properties of inequalities and the behavior of subtraction in the context of natural numbers.

### Mathematical insight
This statement is important because it establishes a fundamental property of subtraction in relation to inequality, which is crucial for various arithmetic and algebraic manipulations. It provides a basis for further reasoning about the relationships between numbers under subtraction and comparison operations.

### Dependencies
* `ARITH_RULE` 

### Porting notes
When translating this into another proof assistant, pay attention to how that system handles arithmetic and inequalities. Specifically, ensure that the target system's `ARITH_RULE` or equivalent mechanism can derive or directly support this property of subtraction. Note that some systems may require explicit proof steps or different formulations of arithmetic properties.

---

## SUB_EQ_EQ_0

### Name of formal statement
SUB_EQ_EQ_0

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SUB_EQ_EQ_0 = ARITH_RULE
 `!m n:num. (m - n = m) <=> (m = 0) \/ (n = 0)`;;
```

### Informal statement
For all natural numbers `m` and `n`, the equation `m - n = m` holds if and only if either `m` is equal to 0 or `n` is equal to 0.

### Informal sketch
* The theorem `SUB_EQ_EQ_0` is proven using the `ARITH_RULE` mechanism, which suggests a straightforward application of arithmetic properties.
* The proof likely involves recognizing that `m - n = m` implies `n = 0` due to the properties of subtraction in the context of natural numbers.
* Conversely, if `n = 0`, then `m - n = m - 0 = m`, establishing the reverse implication.
* The use of `ARITH_RULE` implies that the proof may leverage basic properties of arithmetic operations, potentially including the definition of subtraction and the role of the additive identity (0).

### Mathematical insight
This theorem captures a fundamental property of subtraction in the context of natural numbers, highlighting the conditions under which subtracting one number from another results in the original number. It is essential for establishing various arithmetic properties and can be seen as a foundational step in building more complex arithmetic theories.

### Dependencies
* `ARITH_RULE`
* Basic properties of natural numbers, including the definition of subtraction and the role of 0 as the additive identity.

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system handles arithmetic operations and the representation of natural numbers. The proof may require adjustments based on the specific arithmetic libraries and tactics available in the target system. Additionally, consider how the target system treats the equivalence (`<=>`) and how it is used in the context of arithmetic equalities.

---

## SUB_LEFT_LESS_EQ

### Name of formal statement
SUB_LEFT_LESS_EQ

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SUB_LEFT_LESS_EQ = ARITH_RULE
  `!m n p:num. m <= (n - p) <=> (m + p) <= n \/ m <= 0`
```

### Informal statement
For all natural numbers m, n, and p, m is less than or equal to (n minus p) if and only if (m plus p) is less than or equal to n or m is less than or equal to 0.

### Informal sketch
* The theorem `SUB_LEFT_LESS_EQ` involves proving an equivalence between two conditions involving natural numbers m, n, and p.
* The proof likely involves using the `ARITH_RULE` to derive the equivalence `m <= (n - p) <=> (m + p) <= n \/ m <= 0`.
* Key steps may include:
  + Using properties of addition and subtraction on natural numbers
  + Applying rules for inequalities and equivalences
  + Possibly using case analysis or split rules to handle the disjunction `\/`

### Mathematical insight
This theorem provides a useful equivalence for manipulating inequalities involving subtraction, which can be particularly helpful in arithmetic and algebraic manipulations. It highlights the relationship between subtracting a number and adding its negation, and how this relates to the ordering of numbers.

### Dependencies
* `ARITH_RULE`
* Basic properties of natural numbers, such as addition and subtraction rules, and inequality properties.

### Porting notes
When porting this theorem to other proof assistants, pay attention to how each system handles arithmetic operations and inequalities on natural numbers. Some systems may have built-in support for arithmetic reasoning, while others may require manual application of rules. Additionally, the handling of disjunctions and case splits may vary between systems, requiring adjustments to the proof strategy.

---

## SUB_LEFT_GREATER_EQ

### Name of formal statement
SUB_LEFT_GREATER_EQ

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SUB_LEFT_GREATER_EQ =
  ARITH_RULE `!m n p:num. m >= (n - p) <=> (m + p) >= n`;;
```

### Informal statement
For all natural numbers $m$, $n$, and $p$, $m$ is greater than or equal to $n - p$ if and only if $m + p$ is greater than or equal to $n$.

### Informal sketch
* The proof involves using the `ARITH_RULE` to establish the equivalence between two inequalities.
* The key step is recognizing that the inequality $m >= (n - p)$ can be rewritten as $(m + p) >= n$ by adding $p$ to both sides.
* This step relies on basic properties of arithmetic operations, including the commutativity and associativity of addition, as well as the definition of the greater-than-or-equal-to relation.

### Mathematical insight
This theorem provides a useful equivalence between two inequalities, allowing for the simplification or transformation of expressions involving subtraction and addition. It is a fundamental property of arithmetic and is likely used in a wide range of mathematical proofs.

### Dependencies
* `ARITH_RULE`

### Porting notes
When porting this theorem to another proof assistant, note that the `ARITH_RULE` tactic may not have a direct equivalent. Instead, the porter may need to use a combination of arithmetic properties and logical equivalences to establish the result. Additionally, the representation of natural numbers and the definition of the greater-than-or-equal-to relation may vary between systems, requiring careful attention to the specifics of the target proof assistant.

---

## LESS_EQ_LESS_TRANS

### Name of formal statement
LESS_EQ_LESS_TRANS

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let LESS_EQ_LESS_TRANS = LET_TRANS;;
```

### Informal statement
The LESS_EQ_LESS_TRANS definition is equivalent to the LET_TRANS definition, where LET_TRANS is a predefined transitivity property.

### Informal sketch
* The definition relies on the existing `LET_TRANS` property, which likely establishes a transitivity relation.
* The main logical stage involves assigning the `LET_TRANS` property to `LESS_EQ_LESS_TRANS`, implying that `LESS_EQ_LESS_TRANS` inherits the transitivity characteristics of `LET_TRANS`.
* This step does not involve complex proofs but rather a straightforward assignment or equivalence statement.

### Mathematical insight
This definition is important because it extends or specifies a transitivity property related to less-than or equal-to relations, which is fundamental in constructing and proving properties about order relations in mathematics. The intuition behind this is to ensure that if `a` is less than or equal to `b`, and `b` is less than or equal to `c`, then `a` is less than or equal to `c`, following the principle of transitivity.

### Dependencies
#### Definitions
* `LET_TRANS`

### Porting notes
When translating `LESS_EQ_LESS_TRANS` into another proof assistant, ensure that an equivalent of `LET_TRANS` is defined or available. The translation should preserve the assignment or equivalence between `LESS_EQ_LESS_TRANS` and `LET_TRANS`. Pay attention to how the target system handles definitions and transitivity properties, as the syntax and built-in support can vary significantly between systems like Lean, Coq, or Isabelle.

---

## LESS_0_CASES

### Name of formal statement
LESS_0_CASES

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let LESS_0_CASES = ARITH_RULE `!m. (0 = m) \/ 0 < m`;;
```

### Informal statement
For all natural numbers m, either 0 is equal to m or 0 is less than m.

### Informal sketch
* The statement `LESS_0_CASES` is defined using the `ARITH_RULE` to express a basic property of natural numbers.
* The `ARITH_RULE` is likely applying a decision procedure for arithmetic to establish the validity of the statement.
* The statement itself is a disjunction that covers all possible cases for a natural number m in relation to 0, implying that every natural number is either 0 or greater than 0.

### Mathematical insight
This definition captures a fundamental property of natural numbers, where every number is either zero or positive. It's essential in arithmetic and serves as a foundation for more complex proofs involving natural numbers.

### Dependencies
* `ARITH_RULE`

### Porting notes
When translating this into another proof assistant, ensure that the target system has a similar mechanism for applying arithmetic decision procedures or rules, such as `ARITH_RULE` in HOL Light. In systems like Lean, Coq, or Isabelle, this might involve using tactics or commands that apply arithmetic reasoning or decision procedures. Note that the exact formulation and the way arithmetic is handled might differ between systems.

---

## LESS_OR

### Name of formal statement
LESS_OR

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let LESS_OR = ARITH_RULE `!m n. m < n ==> (SUC m) <= n`;;
```

### Informal statement
For all natural numbers `m` and `n`, if `m` is less than `n`, then the successor of `m` is less than or equal to `n`.

### Informal sketch
* The statement `LESS_OR` is proved using the `ARITH_RULE` mechanism in HOL Light, which typically involves basic properties of arithmetic and possibly induction.
* The key step involves recognizing that if `m` is less than `n`, then `SUC m` (the successor of `m`, which is `m + 1`) must be less than or equal to `n` due to the basic ordering properties of natural numbers.
* This involves understanding the relationship between the less-than (`<`) and less-than-or-equal-to (`<=`) relations and how they interact with the successor function (`SUC`).

### Mathematical insight
The `LESS_OR` definition captures a fundamental property relating the successor function to the ordering of natural numbers. It's essential for establishing basic arithmetic properties and inequalities in a formal system, reflecting the intuitive notion that adding one to a number that is already less than another will result in a value that is still less than or equal to the second number.

### Dependencies
* `ARITH_RULE`
* Basic properties of natural numbers, including the definition of `SUC` (successor function) and the `<` and `<=` relations.

### Porting notes
When translating `LESS_OR` into another proof assistant like Lean, Coq, or Isabelle, pay close attention to how each system handles arithmetic and the successor function. Specifically, note the differences in how these systems define and prove basic properties of natural numbers, as the `ARITH_RULE` mechanism may not have a direct counterpart. Additionally, consider the treatment of binders and quantifiers (`!m n`) and how they are expressed in the target system.

---

## SUB

### Name of formal statement
SUB

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let SUB = ARITH_RULE
  `(!m. 0 - m = 0) /\
   (!m n. (SUC m) - n = (if m < n then 0 else SUC(m - n)))`
```

### Informal statement
For all natural numbers `m`, the difference between 0 and `m` is 0. For all natural numbers `m` and `n`, the difference between the successor of `m` and `n` is equal to 0 if `m` is less than `n`, otherwise it is equal to the successor of the difference between `m` and `n`.

### Informal sketch
* The definition of subtraction `SUB` involves two main cases:
  + The first case states that subtracting any number `m` from 0 results in 0.
  + The second case defines the subtraction of `n` from the successor of `m` as follows:
    - If `m` is less than `n`, the result is 0.
    - Otherwise, the result is the successor of the difference between `m` and `n`, which is computed recursively.
* This recursive definition of subtraction mirrors the standard definition of subtraction in Peano arithmetic.

### Mathematical insight
The definition of `SUB` is a fundamental component of Peano arithmetic, which provides a foundation for formalizing basic arithmetic operations. This definition is important because it allows for the formalization of subtraction in a way that is consistent with the standard definition of subtraction in mathematics.

### Dependencies
* `ARITH_RULE`
* `SUC` (successor function)

### Porting notes
When porting this definition to other proof assistants, note that the handling of recursive definitions and the `if-then-else` construct may differ. In particular, some systems may require explicit pattern matching or the use of a `case` statement to define the subtraction function. Additionally, the `ARITH_RULE` may need to be replaced with an equivalent rule or axiom in the target system.

---

## LESS_MULT_MONO

### Name of formal statement
LESS_MULT_MONO

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LESS_MULT_MONO = prove
 (`!m i n. ((SUC n) * m) < ((SUC n) * i) <=> m < i`,
  REWRITE_TAC[LT_MULT_LCANCEL; NOT_SUC])
```

### Informal statement
For all natural numbers $m$, $i$, and $n$, the statement $((n+1) \cdot m) < ((n+1) \cdot i)$ holds if and only if $m < i$.

### Informal sketch
* The proof involves rewriting the inequality using the `LT_MULT_LCANCEL` and `NOT_SUC` theorems.
* The `REWRITE_TAC` tactic is applied to transform the original statement into a more manageable form.
* The key insight is that the factor $(n+1)$ can be canceled out from both sides of the inequality, reducing it to a comparison between $m$ and $i$.
* The `LT_MULT_LCANCEL` theorem likely provides the basis for this cancellation step, while `NOT_SUC` may be used to handle the successor function `SUC`.

### Mathematical insight
This theorem establishes a monotonicity property of multiplication with respect to inequality, specifically when one of the factors is a successor number. It shows that the ordering of the products depends solely on the ordering of the other factors, $m$ and $i$, when the common factor $(n+1)$ is positive.

### Dependencies
* Theorems:
  + `LT_MULT_LCANCEL`
  + `NOT_SUC`
* Definitions:
  + `SUC` (successor function)

### Porting notes
When translating this theorem into another proof assistant, pay attention to how the system handles the successor function and inequality properties. Ensure that the equivalent of `LT_MULT_LCANCEL` and `NOT_SUC` are available or can be derived. Additionally, consider how the target system's automation and rewriting mechanisms compare to HOL Light's `REWRITE_TAC`, as this may affect the proof strategy.

---

## LESS_MONO_MULT

### Name of formal statement
LESS_MONO_MULT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LESS_MONO_MULT = prove
 (`!m n p. m <= n ==> (m * p) <= (n * p)`,
  SIMP_TAC[LE_MULT_RCANCEL])
```

### Informal statement
For all numbers `m`, `n`, and `p`, if `m` is less than or equal to `n`, then the product of `m` and `p` is less than or equal to the product of `n` and `p`.

### Informal sketch
* The theorem `LESS_MONO_MULT` is proved using a simple implication from the assumption `m <= n` to the conclusion `(m * p) <= (n * p)`.
* The proof involves using the `SIMP_TAC` tactic with a theorem `LE_MULT_RCANCEL`, which likely establishes a property related to the monotonicity of multiplication with respect to the less-than-or-equal-to relation.
* The key logical stage is applying the `LE_MULT_RCANCEL` theorem to simplify or directly prove the implication.

### Mathematical insight
This theorem captures the monotonicity property of multiplication over the less-than-or-equal-to relation, which is a fundamental property in arithmetic. It states that if one factor in a product is increased (or not decreased) while the other factor remains constant, the product either increases or remains the same. This property is crucial in various mathematical proofs and is a building block for more complex arithmetic reasoning.

### Dependencies
* `LE_MULT_RCANCEL`

### Porting notes
When translating `LESS_MONO_MULT` into another proof assistant, ensure that the target system has a similar `LE_MULT_RCANCEL` theorem or property, or can derive it. The `SIMP_TAC` tactic in HOL Light is used for simplification based on a set of theorems; the equivalent tactic or mechanism in the target system should be used to apply `LE_MULT_RCANCEL` or its equivalent. Pay attention to how the target system handles arithmetic properties and implications, as the direct translation of `SIMP_TAC` and the specific theorem application might require adjustments.

---

## LESS_MULT2

### Name of formal statement
LESS_MULT2

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LESS_MULT2 = prove
 (`!m n. 0 < m /\ 0 < n ==> 0 < (m * n)`,
  REWRITE_TAC[LT_MULT])
```

### Informal statement
For all positive integers `m` and `n`, if `0` is less than `m` and `0` is less than `n`, then `0` is less than the product of `m` and `n`.

### Informal sketch
* The theorem `LESS_MULT2` is proven by applying the `REWRITE_TAC` tactic with the `LT_MULT` rule.
* The proof starts with the assumption that `0` is less than `m` and `0` is less than `n`.
* The `LT_MULT` rule is then applied to derive that `0` is less than the product of `m` and `n`.
* The `REWRITE_TAC` tactic is used to rewrite the goal using the `LT_MULT` rule, effectively completing the proof.

### Mathematical insight
The theorem `LESS_MULT2` captures a fundamental property of multiplication in the context of positive integers, stating that the product of two positive integers is also positive. This property is crucial in various mathematical contexts, such as algebra, analysis, and number theory. The proof of `LESS_MULT2` relies on the `LT_MULT` rule, which likely formalizes the concept that the product of two positive numbers is positive.

### Dependencies
* `LT_MULT`

### Porting notes
When porting this theorem to another proof assistant, ensure that the equivalent of the `LT_MULT` rule is available and that the proof tactic analogous to `REWRITE_TAC` can be applied. Note that the handling of binders and quantifiers may differ between systems, requiring adjustments to the proof script. Additionally, the `LESS_MULT2` theorem may be a consequence of more general properties of multiplication and ordering in the target system, potentially simplifying its proof or making it a trivial consequence of other established results.

---

## SUBSET_FINITE

### Name of formal statement
SUBSET_FINITE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SUBSET_FINITE = prove
 (`!s. FINITE s ==> (!t. t SUBSET s ==> FINITE t)`,
  MESON_TAC[FINITE_SUBSET])
```

### Informal statement
For all sets `s`, if `s` is finite, then for all sets `t`, if `t` is a subset of `s`, then `t` is finite.

### Informal sketch
* The theorem `SUBSET_FINITE` is proved by assuming `s` is finite and then showing that any subset `t` of `s` is also finite.
* The proof strategy involves using the `FINITE_SUBSET` theorem, which likely states that a subset of a finite set is finite.
* The `MESON_TAC` tactic is used to apply this theorem and derive the finiteness of `t`.

### Mathematical insight
This theorem is important because it establishes a fundamental property of finite sets: any subset of a finite set is also finite. This is a basic result in set theory and has numerous applications in mathematics and computer science.

### Dependencies
* `FINITE`
* `SUBSET`
* `FINITE_SUBSET`

### Porting notes
When porting this theorem to another proof assistant, ensure that the `FINITE` and `SUBSET` definitions are properly translated, and that an equivalent to the `FINITE_SUBSET` theorem is available or can be derived. The `MESON_TAC` tactic may need to be replaced with a similar tactic or a manual proof step in the target system.

---

## LESS_EQ_SUC

### Name of formal statement
LESS_EQ_SUC

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LESS_EQ_SUC = prove
 (`!n. m <= SUC n <=> (m = SUC n) \/ m <= n`,
  REWRITE_TAC[LE])
```

### Informal statement
For all natural numbers `n` and `m`, `m` is less than or equal to the successor of `n` if and only if `m` is equal to the successor of `n` or `m` is less than or equal to `n`.

### Informal sketch
* The proof involves rewriting the less-than-or-equal-to relation `LE` to establish the equivalence between two conditions: `m <= SUC n` and `(m = SUC n) \/ m <= n`.
* The `REWRITE_TAC[LE]` tactic is used to apply the definition of `LE` to the goal, allowing the theorem to be proven by simplifying the resulting expression.
* The key logical stage is the application of the definition of `LE` to `m <= SUC n`, which leads to the disjunction `(m = SUC n) \/ m <= n`.

### Mathematical insight
This theorem provides a key property of the less-than-or-equal-to relation in the context of natural numbers, specifically relating it to the successor function `SUC`. It is essential for establishing various properties and theorems involving inequalities and natural numbers, showcasing how the successor function interacts with the ordering of natural numbers.

### Dependencies
* `LE` 
* `SUC`

### Porting notes
When translating this theorem into other proof assistants, pay attention to how each system handles the successor function and the less-than-or-equal-to relation, as these may have different definitions or properties. Additionally, the tactic `REWRITE_TAC[LE]` may need to be replaced with an equivalent tactic or a series of tactics that achieve the same goal in the target proof assistant.

---

## ANTE_RES_THEN

### Name of formal statement
ANTE_RES_THEN

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ANTE_RES_THEN ttac th = FIRST_ASSUM(fun t -> ttac (MATCH_MP t th));;
```

### Informal statement
For a given tactic `ttac` and a theorem `th`, `ANTE_RES_THEN` applies `ttac` to the result of applying the `MATCH_MP` tactic to each assumption `t` with `th`, effectively using the first assumption that matches to derive a new conclusion.

### Informal sketch
* The `ANTE_RES_THEN` function takes a tactic `ttac` and a theorem `th` as inputs.
* It uses `FIRST_ASSUM` to consider each assumption `t` in the context.
* For each assumption `t`, it applies `MATCH_MP` with `t` and `th` to potentially derive a new conclusion.
* The `ttac` tactic is then applied to this new conclusion.
* The process stops at the first successful application of `ttac` to a derived conclusion.

### Mathematical insight
`ANTE_RES_THEN` seems to encapsulate a strategy for proving a theorem by applying a given tactic to the result of combining an assumption with a known theorem (`th`), using `MATCH_MP` for modus ponens. This is useful for automated reasoning systems where a conclusion is to be drawn from a set of premises and a rule of inference.

### Dependencies
- `FIRST_ASSUM`
- `MATCH_MP`

### Porting notes
When translating `ANTE_RES_THEN` into another proof assistant, consider how assumptions are handled and how tactics are applied to them. The equivalent of `FIRST_ASSUM` and `MATCH_MP` must be identified in the target system. Pay special attention to how tactics are composed and applied to conclusions derived from assumptions and theorems.

---

## IMP_RES_THEN

### Name of formal statement
IMP_RES_THEN

### Type of the formal statement
Theorem/tactic definition

### Formal Content
```ocaml
let IMP_RES_THEN ttac th = FIRST_ASSUM(fun t -> ttac (MATCH_MP th t))
```

### Informal statement
The `IMP_RES_THEN` tactic applies a given tactic `ttac` to the result of applying modus ponens (`MATCH_MP`) to a theorem `th` and a term `t` that is assumed as the first assumption, effectively using the assumption to instantiate the antecedent of `th` to derive a new conclusion.

### Informal sketch
* The tactic starts by selecting the first assumption `t` using `FIRST_ASSUM`.
* It then applies modus ponens (`MATCH_MP`) to the theorem `th` and the selected assumption `t`, which effectively substitutes `t` for the antecedent of `th` to obtain a new conclusion.
* The result of this modus ponens application is then passed to the tactic `ttac` for further processing.
* The use of `MATCH_MP` indicates that `th` is a theorem of the form `p --> q`, and `t` is used to discharge the assumption `p` to derive `q`.

### Mathematical insight
This tactic is useful for applying theorems that have an implicational form (`p --> q`) to assumptions in a proof, allowing for the derivation of new conclusions based on the assumptions present in the context. It encapsulates a common pattern of proof where an assumption is used to satisfy the premise of a conditional statement, enabling the conclusion of that statement to be derived.

### Dependencies
* `FIRST_ASSUM`
* `MATCH_MP`

### Porting notes
When translating `IMP_RES_THEN` into another proof assistant, pay attention to how assumptions are managed and how modus ponens is applied. The equivalent of `FIRST_ASSUM` and `MATCH_MP` must be identified in the target system. Additionally, consider how tactics are composed and applied in the target system, as the direct application of a tactic to the result of another tactic may differ.

---

## INFINITE_MEMBER

### Name of formal statement
INFINITE_MEMBER

### Type of the formal statement
Theorem

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
    REWRITE_TAC[]])
```

### Informal statement
For all sets `s` of type `A->bool`, if `s` is infinite, then there exists an element `x` such that `x` is in `s`.

### Informal sketch
* The proof starts by assuming `INFINITE(s:A->bool)`, which means `s` is an infinite set.
* It then proceeds to show that if `s` were empty, it would be finite, contradicting the assumption of infiniteness.
* The `CONTRAPOS_CONV` tactic is used to derive a contradiction, implying that `s` cannot be empty.
* The existence of an element `x` in `s` is then inferred from the fact that `s` is not empty.
* Key steps involve using `INFINITE` and `FINITE_EMPTY` definitions, as well as logical manipulations involving `NOT_FORALL_THM` and `EXTENSION`.

### Mathematical insight
This theorem is important because it establishes a fundamental property of infinite sets in the context of set theory: an infinite set must have at least one element. This might seem trivial, but in the formal development of set theory, such basic properties need to be rigorously proven from the axioms.

### Dependencies
#### Theorems and Definitions
* `INFINITE`
* `FINITE_EMPTY`
* `EXTENSION`
* `NOT_IN_EMPTY`
* `NOT_FORALL_THM`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles set theory, infiniteness, and the existential quantifier. The `CONTRAPOS_CONV` tactic, which is used for contradiction, might be directly available or achievable through other means, such as using a negation introduction rule followed by a contradiction lemma. Additionally, the representation of sets as `A->bool` (characteristic functions) might differ, requiring adjustments in how set membership and emptiness are defined and used.

---

## INFINITE_CHOOSE

### Name of formal statement
INFINITE_CHOOSE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let INFINITE_CHOOSE = prove(
  `!s:A->bool. INFINITE(s) ==> ((@) s) IN s`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP INFINITE_MEMBER) THEN
  DISCH_THEN(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[IN] THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN REWRITE_TAC[]);;
```

### Informal statement
For all sets `s` of type `A->bool`, if `s` is infinite, then there exists an element `x` in `s` such that `x` is a member of `s`.

### Informal sketch
* The proof starts by assuming an arbitrary set `s` of type `A->bool` and that `s` is infinite, as expressed by the `INFINITE(s)` predicate.
* It then applies the `INFINITE_MEMBER` theorem, which likely states that an infinite set has at least one member, to deduce the existence of an element `x` in `s`.
* The `SELECT_RULE` is applied to select a specific member from `s`, leveraging the `INFINITE_MEMBER` theorem's conclusion.
* The proof then uses rewriting and conversion tactics (`REWRITE_TAC` and `CONV_TAC`) to manipulate the expression and conclude that `x` is indeed a member of `s`, as denoted by the `IN` relation.

### Mathematical insight
The `INFINITE_CHOOSE` theorem provides a way to select an element from an infinite set, which is crucial in various mathematical constructions and proofs, especially those involving infinite sets or sequences. This theorem relies on the concept of infinity and the `INFINITE` predicate, which captures the property of a set being infinite.

### Dependencies
* Theorems:
  + `INFINITE_MEMBER`
* Definitions:
  + `INFINITE`
  + `IN`

### Porting notes
When translating this theorem into other proof assistants, pay attention to how infinity is represented and how selection from infinite sets is handled. Some systems may have built-in support for infinite sets and selection, while others may require manual construction or the use of specific libraries. Additionally, the automation and rewriting tactics used in the HOL Light proof may need to be adjusted or reimplemented in the target system.

---

## INFINITE_DELETE

### Name of formal statement
INFINITE_DELETE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let INFINITE_DELETE = prove(
  `!(t:A->bool) x. INFINITE (t DELETE x) = INFINITE(t)`,
  REWRITE_TAC[INFINITE; FINITE_DELETE])
```

### Informal statement
For all predicates `t` of type `A -> bool` and all elements `x`, the set `t DELETE x` is infinite if and only if the set `t` is infinite.

### Informal sketch
* The theorem `INFINITE_DELETE` establishes an equivalence between the infiniteness of a set `t` and the infiniteness of the set `t` with an element `x` removed.
* The proof involves rewriting the `INFINITE` and `FINITE_DELETE` definitions using `REWRITE_TAC`.
* Key steps include:
  + Understanding the definition of `INFINITE` and how it applies to `t` and `t DELETE x`.
  + Applying the `FINITE_DELETE` property to relate the finiteness of `t` and `t DELETE x`.
  + Using the `REWRITE_TAC` tactic to simplify the expressions involving `INFINITE` and `FINITE_DELETE`.

### Mathematical insight
The theorem `INFINITE_DELETE` provides insight into the properties of infinite sets and how they behave under removal of elements. It shows that removing a single element from an infinite set does not affect its infiniteness, which is a fundamental property in set theory.

### Dependencies
* `INFINITE`
* `FINITE_DELETE`

### Porting notes
When porting this theorem to other proof assistants, note that the handling of infiniteness and set operations may differ. In particular, the `REWRITE_TAC` tactic may need to be replaced with equivalent rewriting mechanisms in the target system. Additionally, the definitions of `INFINITE` and `FINITE_DELETE` should be carefully examined to ensure consistency with the target system's libraries and conventions.

---

## INFINITE_INSERT

### Name of formal statement
INFINITE_INSERT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let INFINITE_INSERT = prove(
  `!(x:A) t. INFINITE(x INSERT t) = INFINITE(t)`,
  REWRITE_TAC[INFINITE; FINITE_INSERT])
```

### Informal statement
For all elements `x` of type `A` and for all sets `t`, the set `x` inserted into `t` is infinite if and only if `t` is infinite.

### Informal sketch
* The proof involves showing the equivalence between the infinity of `x INSERT t` and the infinity of `t`.
* The `REWRITE_TAC` tactic is used with the `INFINITE` and `FINITE_INSERT` theorems to establish this equivalence.
* The key insight is recognizing that inserting an element into an infinite set does not change its infinity property.

### Mathematical insight
This theorem is important because it provides a fundamental property of infinite sets under the operation of inserting an element. It implies that the infinity of a set is preserved under such operations, which is crucial in various mathematical constructions and proofs involving infinite sets.

### Dependencies
* `INFINITE`
* `FINITE_INSERT`

### Porting notes
When translating this theorem into other proof assistants, ensure that the notion of infinity and set insertion is defined similarly. Note that the `REWRITE_TAC` tactic in HOL Light corresponds to rewriting or substitution tactics in other systems, which may require manual application of the `INFINITE` and `FINITE_INSERT` properties. Additionally, the handling of binders and quantifiers may differ between systems, requiring adjustments to the proof script.

---

## SIZE_INSERT

### Name of formal statement
SIZE_INSERT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SIZE_INSERT = prove(
  `!(x:A) t. ~(x IN t) /\ t HAS_SIZE n ==> (x INSERT t) HAS_SIZE (SUC n)`,
  SIMP_TAC[HAS_SIZE; CARD_CLAUSES; FINITE_RULES])
```

### Informal statement
For all elements `x` of type `A` and all sets `t`, if `x` is not in `t` and `t` has a size `n`, then the set resulting from inserting `x` into `t` has a size equal to the successor of `n`.

### Informal sketch
* The proof starts by assuming that `x` is not an element of `t` and `t` has a size `n`.
* It then applies `SIMP_TAC` with `HAS_SIZE`, `CARD_CLAUSES`, and `FINITE_RULES` to simplify the expression and derive the conclusion that `(x INSERT t)` has a size of `SUC n`.
* The use of `SIMP_TAC` indicates a simplification step, likely unfolding definitions and applying basic properties of set size and insertion.
* Key HOL Light terms involved include `HAS_SIZE`, `CARD_CLAUSES`, and `FINITE_RULES`, which suggest the proof relies on basic properties of finite sets and their sizes.

### Mathematical insight
This theorem provides a fundamental property of set operations, specifically how the size of a set changes when an element is added to it, under the condition that the element is not already in the set. It's crucial for reasoning about the cardinality of sets after insertions, which is a common operation in many mathematical and computational contexts.

### Dependencies
* **Definitions:**
  - `HAS_SIZE`
  - `CARD_CLAUSES`
* **Theorems and Rules:**
  - `FINITE_RULES`
* **Tactics:**
  - `SIMP_TAC`

### Porting notes
When translating this theorem into another proof assistant, special attention should be given to how set sizes and insertions are handled. The equivalent of `SIMP_TAC` might need to be applied in a context where the properties of `HAS_SIZE` and `CARD_CLAUSES` are appropriately defined and accessible. Additionally, the treatment of finite sets and their sizes (`FINITE_RULES`) should be correctly ported to ensure the theorem's applicability in the target system.

---

## SIZE_DELETE

### Name of formal statement
SIZE_DELETE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SIZE_DELETE = prove(
  `!(x:A) t. x IN t /\ t HAS_SIZE (SUC n) ==> (t DELETE x) HAS_SIZE n`,
  SIMP_TAC[HAS_SIZE_SUC])
```

### Informal statement
For all `x` of type `A` and all sets `t`, if `x` is an element of `t` and `t` has size `SUC n`, then the set resulting from deleting `x` from `t` has size `n`.

### Informal sketch
* The proof starts by assuming `x IN t` and `t HAS_SIZE (SUC n)`.
* It then applies the `SIMP_TAC` tactic with `HAS_SIZE_SUC` to simplify the expression for the size of `t`.
* The main logical stage involves recognizing that deleting an element from a set reduces its size by one, which is reflected in the `SUC n` to `n` relationship.
* The `SIMP_TAC` tactic is used to simplify the expression, leveraging the `HAS_SIZE_SUC` theorem to establish the size of `t DELETE x` as `n`.

### Mathematical insight
This theorem formalizes the intuitive notion that removing an element from a set decreases its size by one, provided the original set has a successor size (`SUC n`). It's a fundamental property relating set operations (deletion) with cardinality (size), underpinning various arguments in combinatorics and set theory.

### Dependencies
* Theorems:
  * `HAS_SIZE_SUC`
* Definitions:
  * `HAS_SIZE`
  * `SUC`

### Porting notes
When translating this theorem into another proof assistant, ensure that the notion of set size and the `SUC` function (successor) are defined and behave similarly. Pay particular attention to how the target system handles set operations like deletion and how it represents and proves properties about finite sets. The equivalent of `SIMP_TAC` may vary, but the goal is to apply simplification rules to leverage the `HAS_SIZE_SUC` theorem or its equivalent in simplifying the size expression after deletion.

---

## SIZE_EXISTS

### Name of formal statement
SIZE_EXISTS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SIZE_EXISTS = prove(
  `!s N. s HAS_SIZE (SUC N) ==> ?x:A. x IN s`,
  SIMP_TAC[HAS_SIZE_SUC; GSYM MEMBER_NOT_EMPTY])
```

### Informal statement
For all sets `s` and natural numbers `N`, if `s` has size `SUC N`, then there exists an element `x` of type `A` such that `x` is in `s`.

### Informal sketch
* The proof starts with the assumption that a set `s` has size `SUC N`, which implies that `s` is non-empty.
* Using the `HAS_SIZE_SUC` definition, we can infer that `s` has at least one element.
* The `GSYM MEMBER_NOT_EMPTY` tactic is applied to derive the existence of an element `x` in `s`.
* The `SIMP_TAC` tactic is used to simplify the goal and derive the final conclusion.

### Mathematical insight
This theorem provides a fundamental property of sets with finite size, namely that a non-empty set must contain at least one element. This result is crucial in various areas of mathematics, such as set theory, combinatorics, and logic.

### Dependencies
#### Theorems
* `HAS_SIZE_SUC`
#### Definitions
* `HAS_SIZE`
* `SUC`
* `MEMBER_NOT_EMPTY`

### Porting notes
When porting this theorem to other proof assistants, attention should be paid to the handling of size and membership predicates. The `SIMP_TAC` tactic may need to be replaced with equivalent simplification mechanisms, and the `GSYM` tactic may require manual application of symmetric properties. Additionally, the representation of natural numbers and sets may differ between systems, requiring adjustments to the theorem statement and proof.

---

## SUBSET_DELETE

### Name of formal statement
SUBSET_DELETE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SUBSET_DELETE = prove(
  `!s t (x:A). s SUBSET t ==> (s DELETE x) SUBSET t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `s:A->bool` THEN ASM_REWRITE_TAC[DELETE_SUBSET])
```

### Informal statement
For all sets `s` and `t` and for all elements `x` of type `A`, if `s` is a subset of `t`, then the set resulting from deleting `x` from `s` is also a subset of `t`.

### Informal sketch
* The proof starts by assuming `s SUBSET t` and an arbitrary element `x` of type `A`.
* It then applies `SUBSET_TRANS` to establish a relationship between `s DELETE x` and `t`, leveraging the transitivity of the subset relation.
* The `EXISTS_TAC` tactic introduces a witness, in this case, `s:A->bool`, which is used to instantiate the `SUBSET_TRANS` theorem.
* Finally, `ASM_REWRITE_TAC[DELETE_SUBSET]` is applied to simplify the expression `s DELETE x` using the definition of `DELETE_SUBSET`, showing that `s DELETE x` is indeed a subset of `t`.

### Mathematical insight
This theorem is important because it establishes a fundamental property of set operations, specifically that removing an element from a set preserves the subset relationship with respect to another set. This property is crucial in various mathematical constructions and proofs involving sets.

### Dependencies
* Theorems:
  - `SUBSET_TRANS`
* Definitions:
  - `SUBSET`
  - `DELETE_SUBSET`

### Porting notes
When porting this theorem to another proof assistant, ensure that the subset relation and the delete operation are defined similarly. Note that the `REPEAT STRIP_TAC` and `MATCH_MP_TAC` tactics may have direct analogs in other systems, but the specific automation and tactic scripting might differ. The key insight is to apply subset transitivity and then use the definition of set deletion to establish the subset relationship.

---

## INFINITE_FINITE_CHOICE

### Name of formal statement
INFINITE_FINITE_CHOICE

### Type of the formal statement
Theorem

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
        DISCH_THEN(IMP_RES_THEN MP_TAC) THEN REWRITE_TAC[]]])
```

### Informal statement
For all natural numbers `n` and for all subsets `s` of a non-empty set `A`, if `s` is infinite, then there exists a subset `t` of `s` such that `t` has exactly `n` elements.

### Informal sketch
* The proof proceeds by induction on `n`.
* For the base case `n = 0`, it is shown that the empty set `{}:A->bool` is a subset of `s` and has size `0`.
* For the inductive step, assuming `s` is infinite, it is shown that there exists an element `x` in `s` such that `s` without `x` is also infinite.
* Then, using the inductive hypothesis on `s` without `x`, there exists a subset `t` of `s` without `x` with `n-1` elements.
* The subset `t` union `{x}` is then shown to be a subset of `s` with `n` elements, using `INSERT_SUBSET` and `SIZE_INSERT`.
* Key steps involve using `INFINITE_CHOOSE` to select an element from `s`, and `INFINITE_DELETE` to show that removing an element from `s` preserves infinity.

### Mathematical insight
This theorem is important because it establishes a fundamental property of infinite sets: for any infinite set `s`, it is possible to find a subset with exactly `n` elements for any given natural number `n`. This property is crucial in various areas of mathematics, including set theory, combinatorics, and real analysis.

### Dependencies
* Theorems:
  * `INFINITE_CHOOSE`
  * `INFINITE_DELETE`
  * `SIZE_INSERT`
* Definitions:
  * `INFINITE`
  * `SUBSET`
  * `HAS_SIZE`
  * `INSERT`
  * `DELETE`
* Inductive rules:
  * `INDUCT_TAC`

### Porting notes
When porting this theorem to another proof assistant, pay attention to the handling of infinite sets and the `INFINITE` predicate. The `INFINITE_CHOOSE` and `INFINITE_DELETE` theorems may need to be adapted or re-proven in the target system. Additionally, the use of `INDUCT_TAC` and `GEN_TAC` may require adjustments depending on the specific proof assistant's support for induction and generic tactics.

---

## IMAGE_WOP_LEMMA

### Name of formal statement
IMAGE_WOP_LEMMA

### Type of the formal statement
Theorem

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
      UNDISCH_TAC `~(z:A = x)` THEN ASM_REWRITE_TAC[]]])
```

### Informal statement
For all natural numbers `N`, for all predicates `t` on natural numbers and `u` on a non-empty set `A`, if `u` is a subset of the image of `f` under `t` and `u` has size `N+1`, then there exist `n` and a subset `v` of `A` such that `u` equals the union of the set containing `f(n)` and `v`, and for every `y` in `v`, there exists `m` such that `y` equals `f(m)` and `n` is less than `m`.

### Informal sketch
* Start by assuming `u` is a subset of the image of `f` under `t` and `u` has size `N+1`.
* Apply the `num_WOP` theorem to show the existence of `y` in `u` such that `y` equals `f(n)` for some `n`.
* Use the `SIZE_EXISTS` theorem to choose an element `y` from `u`.
* Derive that `y` is in the image of `f` under `t`, and thus `y` equals `f(n)` for some `n`.
* Choose `n` such that `y` equals `f(n)`.
* Construct `v` as `u` with `y` removed.
* Show that `u` equals the union of the set containing `f(n)` and `v`.
* For every `z` in `v`, show that `z` equals `f(m)` for some `m` greater than `n`.
* Apply various logical and set-theoretic rules (`SUBSET`, `IN_IMAGE`, `INSERT_DELETE`) to establish the required properties of `u`, `v`, and the relationship between elements of `v` and `f`.

### Mathematical insight
This theorem provides a way to decompose a subset `u` of the image of a function `f` under a predicate `t` into a singleton set containing `f(n)` and a remainder set `v`, where every element of `v` is the image of some `m` greater than `n` under `f`. This decomposition is useful for inductive proofs involving the image of `f` under `t`.

### Dependencies
* Theorems:
  + `num_WOP`
  + `SIZE_EXISTS`
  + `SUBSET`
  + `IN_IMAGE`
  + `INSERT_DELETE`
* Definitions:
  + `IMAGE`
  + `HAS_SIZE`
  + `SUBSET`
  + `IN_IMAGE` 

### Porting notes
When translating this theorem into another proof assistant, pay close attention to the handling of binders, especially in the `?n` and `?m` quantifiers. Additionally, the `X_CHOOSE_TAC` and `EXISTS_TAC` tactics may need to be replaced with equivalent constructs in the target system. The use of `REWRITE_TAC` and `ASM_REWRITE_TAC` may also require careful handling, as the rewriting rules and strategies may differ between systems.

---

## COLOURING_LEMMA

### Name of formal statement
COLOURING_LEMMA

### Type of the formal statement
Theorem

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
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]]);;
```

### Informal statement
For all natural numbers `M` and for all colouring functions `col` and sets `s`, if `s` is infinite and for all `n` in `s`, `col(n)` is less than or equal to `M`, then there exists a colour `c` and an infinite subset `t` of `s` such that for all `n` in `t`, `col(n)` equals `c`.

### Informal sketch
* The proof begins by considering the case when `M` equals `0`, in which it constructs a trivial subset that satisfies the condition.
* For `M` greater than `0`, it proceeds by cases based on whether the set of elements in `s` with colour `SUC M` is infinite or the set of elements with colour less than or equal to `M` is infinite.
* If the former, it directly constructs an infinite subset with constant colour `SUC M`.
* If the latter, it applies the same principle recursively, finding an infinite subset where all elements have the same colour, which must be less than or equal to `M`.
* The proof leverages `INDUCT_TAC`, `SUBGOAL_THEN`, and `DISJ_CASES_TAC` to manage these cases and apply the necessary logical rules, including `SUBSET_FINITE` and `SUBSET_TRANS`.

### Mathematical insight
This theorem is about the finite colouring of infinite sets of natural numbers. It states that if we have an infinite set `s` and a colouring function `col` that maps each element of `s` to a colour (a natural number) in such a way that no colour exceeds a certain maximum `M`, then there must exist an infinite subset `t` of `s` where all elements have the same colour `c`. This result has implications in combinatorics and graph theory, particularly in problems involving colourings and partitions of infinite sets.

### Dependencies
- `INFINITE`
- `SUBSET`
- `SUBSET_FINITE`
- `SUBSET_TRANS`
- `IN_ELIM_THM`
- `DE_MORGAN_THM`
- `FINITE_UNION`

### Porting notes
When translating this into another proof assistant like Lean, Coq, or Isabelle, pay close attention to how each system handles infinite sets, subset relations, and colouring functions. The use of `INDUCT_TAC` and recursive constructions may need to be adapted based on the target system's support for induction and recursion. Additionally, the `DISJ_CASES_TAC` and `SUBGOAL_THEN` tactics might be replaced with equivalent constructs in the target system, such as pattern matching or conditional statements. Ensure that the translation preserves the original's logical structure and quantifier scope.

---

## COLOURING_THM

### Name of formal statement
COLOURING_THM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let COLOURING_THM = prove(
  `!M col. (!n. col n <= M) ==>
           ?c s. INFINITE(s) /\ !n:num. n IN s ==> (col(n) = c)`,
  REPEAT STRIP_TAC THEN MP_TAC
   (ISPECL [`M:num`; `col:num->num`; `UNIV:num->bool`] COLOURING_LEMMA) THEN
  ASM_REWRITE_TAC[num_INFINITE] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num` (X_CHOOSE_TAC `t:num->bool`)) THEN
  MAP_EVERY EXISTS_TAC [`c:num`; `t:num->bool`] THEN ASM_REWRITE_TAC[])
```

### Informal statement
For all natural numbers M and all functions col from natural numbers to natural numbers, if for all natural numbers n, col(n) is less than or equal to M, then there exists a natural number c and an infinite set s of natural numbers such that for all natural numbers n in s, col(n) equals c.

### Informal sketch
* The proof starts by assuming the existence of a bound M for the function col.
* It then applies the `COLOURING_LEMMA` with specific instantiations for M, col, and the universe of natural numbers.
* The `ASM_REWRITE_TAC` tactic is used to rewrite the infinite set condition using `num_INFINITE`.
* The proof then proceeds by choosing a constant c and an infinite set t such that for all elements n in t, col(n) equals c.
* Finally, the existence of c and t is asserted using `EXISTS_TAC`, completing the proof.

### Mathematical insight
This theorem appears to be related to the pigeonhole principle, which states that if n items are put into m containers, with n > m, then at least one container must contain more than one item. In this case, the theorem states that if a function col assigns natural numbers to natural numbers in a bounded way, then there must exist an infinite set of natural numbers that are all assigned the same value by col.

### Dependencies
* `COLOURING_LEMMA`
* `num_INFINITE`
* `UNIV`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to preserve the precise quantifier structure and the use of infinite sets. The `COLOURING_LEMMA` and `num_INFINITE` definitions should be ported first, as they are crucial to the proof. Additionally, the use of `EXISTS_TAC` and `ASM_REWRITE_TAC` tactics may need to be adapted to the target proof assistant's syntax and semantics.

---

## RAMSEY_LEMMA1

### Name of formal statement
RAMSEY_LEMMA1

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let RAMSEY_LEMMA1 = prove(
 `(!C s. INFINITE(s:A->bool) /\
         (!t. t SUBSET s /\ t HAS_SIZE N ==> C(t) <= M)
         ==> ?t c. INFINITE(t) /\ t SUBSET s /\
                   (!u. u SUBSET t /\ u HAS_SIZE N ==> (C(u) = c)))
  ==> !C s. INFINITE(s:A->bool) /\
            (!t. t SUBSET s /\ t HAS_SIZE (SUC N) ==> C(t) <= M)
            ==> ?t c. INFINITE(t) /\ t SUBSET s /\ ~((@) s) IN t /\
                      (!u. u SUBSET t /\ u HAS_SIZE N
                           ==> (C((@) s) INSERT u) = c))
```

### Informal statement
For all colorings `C` of infinite sets `s` of type `A->bool`, if for every subset `t` of `s` with size `N`, the color `C(t)` is less than or equal to `M`, then there exists an infinite subset `t` of `s` and a color `c` such that for every subset `u` of `t` with size `N`, `C(u)` equals `c`. This implies that for all colorings `C` of infinite sets `s` of type `A->bool`, if for every subset `t` of `s` with size `SUC N` (successor of `N`), the color `C(t)` is less than or equal to `M`, then there exists an infinite subset `t` of `s`, not containing a specific element `(@) s`, and a color `c` such that for every subset `u` of `t` with size `N`, the color of `(@) s` inserted into `u` equals `c`.

### Informal sketch
* The proof involves assuming the existence of a coloring `C` and an infinite set `s` such that every subset `t` of `s` with size `N` has a color `C(t)` less than or equal to `M`.
* It then proceeds to show that under these conditions, there exists an infinite subset `t` of `s` where all subsets `u` of `t` with size `N` have the same color `c`.
* The proof strategy involves using the `INFINITE` and `SUBSET` properties, as well as the `HAS_SIZE` relation to constrain the sizes of subsets.
* Key steps include using `DISCH_THEN` and `MP_TAC` to manage assumptions, and `ASM_REWRITE_TAC` to simplify expressions based on the assumptions.
* The `INFINITE_CHOOSE` lemma is also crucial for selecting elements from infinite sets.
* The proof concludes by showing that a similar property holds for subsets of size `SUC N`, with additional constraints on the existence of a specific element `(@) s` in the subset `t`.

### Mathematical insight
This theorem is related to Ramsey theory, which studies the conditions under which order must appear in a large enough system, no matter how the system is colored or partitioned. The specific lemma here deals with the existence of monochromatic subsets of a certain size within an infinitely colored set, under certain constraints on the coloring. It provides a foundation for more complex results in combinatorial mathematics and has implications for understanding the structure of infinite sets under different coloring schemes.

### Dependencies
* `INFINITE`
* `SUBSET`
* `HAS_SIZE`
* `INFINITE_CHOOSE`
* `SIZE_INSERT`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles infinite sets, subset relations, and size constraints. The use of `DISCH_THEN` and `MP_TAC` may need to be adapted based on the specific tactic languages of the target system. Additionally, the representation of `INFINITE` sets and the `INFINITE_CHOOSE` lemma may vary, requiring careful consideration to ensure the ported theorem maintains the same logical structure and constraints as the original HOL Light version.

---

## RAMSEY_LEMMA2

### Name of formal statement
RAMSEY_LEMMA2

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let RAMSEY_LEMMA2 = prove(
 `(!C s. INFINITE(s:A->bool) /\
         (!t. t SUBSET s /\ t HAS_SIZE (SUC N) ==> C(t) <= M)
        ==> ?t c. INFINITE(t) /\ t SUBSET s /\ ~((@) s IN t) /\
                  (!u. u SUBSET t /\ u HAS_SIZE N
                       ==> (C((@) s INSERT u) = c)))
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
      ~((@) s IN t) /\
      !u. u SUBSET t /\ u HAS_SIZE N ==> (C((@) s INSERT u) = c)`]
    num_Axiom) THEN DISCH_THEN(MP_TAC o BETA_RULE o EXISTENCE) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->(A->bool)` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!n:num. (f n) SUBSET (s:A->bool) /\
    ?c. INFINITE(f(SUC n)) /\ f(SUC n) SUBSET (f n) /\
        ~((@)(f n)) IN (f(SUC n))) /\
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
        UNDISCH_TAC `!n:num. ~((@)(f n):A) IN (f(SUC n))` THEN
        DISCH_THEN(MP_TAC o SPEC `n:num`) THEN CONV_TAC CONTRAPOS_CONV THEN
        REWRITE_TAC[] THEN
        FIRST_ASSUM(MATCH_ACCEPT_TAC o REWRITE_RULE[SUBSET])];
      REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM MATCH_ACCEPT_TAC) THENL
       [GEN_TAC; INDUCT_TAC THENL
         [ASM_REWRITE_TAC[];
          FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
          EXISTS_TAC `SUC n`]] THEN
      MATCH_MP_TAC INFINITE_CHOOSE THEN ASM_REWRITE_TAC[]]])
```

### Informal statement
For all functions `C` and sets `s` of infinite sequences of booleans, if for every subset `t` of `s` with size `SUC N`, `C(t)` is less than or equal to `M`, then there exists a subset `t` of `s`, an element `c`, and a sequence `x` such that `t` is infinite, `x` is not in `t`, and for all subsets `u` of `t` with size `N`, `C(x` inserted into `u)` equals `c`. Furthermore, there exists a sequence of sets `t` and a sequence of colors `col` such that for all natural numbers `n`, `col(n)` is less than or equal to `M`, `t(n)` is a subset of `s`, `t(SUC n)` is a subset of `t(n)`, `x(n)` is not in `t(n)`, `x(SUC n)` is in `t(n)`, `x(n)` is in `s`, and for all subsets `u` of `t(n)` with size `N`, `C(x(n)` inserted into `u)` equals `col(n)`.

### Informal sketch
* The proof starts by assuming the existence of a function `C` and a set `s` of infinite sequences of booleans, and then applies `num_Axiom` to obtain a sequence of sets `f`.
* It then uses induction on the natural numbers to show that for each `n`, there exists a set `f(SUC n)` that is a subset of `f(n)` and satisfies certain properties.
* The proof then uses `INFINITE_CHOOSE` and `SUBSET_TRANS` to construct a sequence of sets `t` and a sequence of elements `x` that satisfy the desired properties.
* Finally, it uses `SKOLEM_CONV` to obtain a sequence of colors `col` that satisfies the desired properties.

### Mathematical insight
The `RAMSEY_LEMMA2` theorem is a variation of Ramsey's theorem, which states that for any infinite set of sequences, there exists a subset of that set such that all sequences in the subset have the same color. This theorem is important in combinatorial mathematics and has applications in various fields, including computer science and philosophy.

### Dependencies
* `INFINITE`
* `SUBSET`
* `HAS_SIZE`
* `INSERT`
* `INFINITE_FINITE_CHOICE`
* `SUBSET_TRANS`
* `SKOLEM_CONV`
* `num_Axiom`
* `INFINITE_CHOOSE`
* `SIZE_INSERT`

### Porting notes
When porting this theorem to other proof assistants, such as Lean or Coq, care should be taken to ensure that the `INFINITE` and `SUBSET` predicates are defined correctly, and that the `SKOLEM_CONV` tactic is replaced with an equivalent tactic in the target system. Additionally, the use of `num_Axiom` and `INFINITE_CHOOSE` may require special handling, as these axioms and theorems may not have direct equivalents in other systems.

---

## RAMSEY_LEMMA3

### Name of formal statement
RAMSEY_LEMMA3

### Type of the formal statement
Theorem

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
For all colorings `C` of subsets of `s` (where `s` is an infinite set of type `A->bool`), if for all subsets `t` of `s` with size `SUC N`, `C(t)` is less than or equal to `M`, then there exist `t`, `x`, and `col` such that:
- For all `n`, `col n` is less than or equal to `M`.
- For all `n`, `t n` is a subset of `s`.
- For all `n`, `t(SUC n)` is a subset of `t n`.
- For all `n`, `x n` is not in `t n`.
- For all `n`, `x(SUC n)` is in `t n`.
- For all `n`, `x n` is in `s`.
- For all `n` and `u`, if `u` is a subset of `t n` and `u` has size `N`, then `C((x n) INSERT u)` equals `col n`.
This implies that for all `C` and `s` as above, there exists `t` and `c` such that:
- `t` is infinite.
- `t` is a subset of `s`.
- For all `u`, if `u` is a subset of `t` and `u` has size `SUC N`, then `C(u)` equals `c`.

### Informal sketch
* The proof starts by assuming the existence of a coloring `C` and an infinite set `s` of type `A->bool`, such that for all subsets `t` of `s` with size `SUC N`, `C(t)` is less than or equal to `M`.
* It then applies the `COLOURING_LEMMA` to find `t`, `x`, and `col` satisfying certain properties.
* The proof proceeds by a series of assumptions and applications of various lemmas and theorems, including `INFINITE_IMAGE_INJ`, `IMAGE_WOP_LEMMA`, and `SIZE_DELETE`.
* Key steps involve:
  + Finding `c` such that for all `n`, `c` equals `(col n)`.
  + Showing that `t` is infinite and a subset of `s`.
  + Proving that for all `u` subsets of `t` with size `SUC N`, `C(u)` equals `c`.
* The proof uses various tactics, including `DISCH_THEN`, `MP_TAC`, `SUBGOAL_THEN`, and `MATCH_MP_TAC`, to derive the desired conclusions.

### Mathematical insight
The `RAMSEY_LEMMA3` theorem is a variation of Ramsey's theorem, which states that for any coloring of the subsets of a set, there exists a monochromatic subset of a certain size. In this case, the theorem provides a condition under which a coloring `C` of subsets of an infinite set `s` can be shown to have a monochromatic subset of size `SUC N`. The theorem has implications for combinatorial and model-theoretic applications, particularly in the study of infinite sets and colorings.

### Dependencies
* `COLOURING_LEMMA`
* `INFINITE_IMAGE_INJ`
* `IMAGE_WOP_LEMMA`
* `SIZE_DELETE`
* `SUBSET_TRANS`
* `IN_INSERT`
* `DELETE_INSERT`
* `EXTENSION`
* `IN_DELETE`

### Porting notes
When porting this theorem to another proof assistant, such as Lean or Coq, special attention should be paid to the handling of infinite sets, colorings, and the various lemmas and theorems used in the proof. The `COLOURING_LEMMA` and other dependencies may need to be ported or re-proven in the target system. Additionally, the use of tactics like `DISCH_THEN` and `MATCH_MP_TAC` may need to be adapted to the target system's proof scripting language.

---

## RAMSEY

### Name of formal statement
RAMSEY

### Type of the formal statement
Theorem

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
    POP_ASSUM MATCH_ACCEPT_TAC])
```

### Informal statement
For all natural numbers `M` and `N`, and for all functions `C` from subsets of a set `s` to natural numbers, if `s` is infinite and for all subsets `t` of `s` with size `N`, `C(t)` is less than or equal to `M`, then there exists an infinite subset `t` of `s` and a natural number `c` such that for all subsets `u` of `t` with size `N`, `C(u)` equals `c`.

### Informal sketch
* The proof starts by assuming the premises: `s` is infinite and `C(t)` is bounded by `M` for all subsets `t` of `s` with size `N`.
* It then proceeds to find an infinite subset `t` of `s` such that `C(u)` is constant for all subsets `u` of `t` with size `N`.
* The proof uses `GEN_TAC` to generalize the statement, followed by `INDUCT_TAC` to proceed by induction.
* The base case involves `REPEAT STRIP_TAC` to simplify the assumptions, `MAP_EVERY EXISTS_TAC` to introduce the subset `s` and the function `C`, and `ASM_REWRITE_TAC` to apply `HAS_SIZE_0` and `SUBSET_REFL`.
* The inductive step uses `MAP_EVERY MATCH_MP_TAC` to apply the `RAMSEY_LEMMA3`, `RAMSEY_LEMMA2`, and `RAMSEY_LEMMA1` to derive the existence of `t` and `c`.

### Mathematical insight
The RAMSEY theorem is a fundamental result in combinatorial mathematics, stating that under certain conditions, there exists an infinite subset of a set with a specific property. This theorem has far-reaching implications in many areas of mathematics, including graph theory, number theory, and combinatorics. The key idea is to find a subset with a uniform property, which is achieved through a combination of induction and clever use of the `RAMSEY_LEMMA` statements.

### Dependencies
* Theorems:
  * `RAMSEY_LEMMA1`
  * `RAMSEY_LEMMA2`
  * `RAMSEY_LEMMA3`
* Definitions:
  * `INFINITE`
  * `SUBSET`
  * `HAS_SIZE`
* Inductive rules:
  * `INDUCT_TAC`

### Porting notes
When translating this theorem to other proof assistants, pay close attention to the handling of infinite sets and the `INFINITE` predicate. Additionally, the use of `GEN_TAC` and `INDUCT_TAC` may need to be adapted to the specific proof assistant's syntax and tactics. The `RAMSEY_LEMMA` statements will also need to be ported or re-proven in the target system.

---

