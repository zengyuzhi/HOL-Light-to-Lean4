# polyhedron.ml

## Overview

Number of statements: 58

This file formalizes Jim Lawrence's proof of Euler's relation for polyhedra, which states that for a convex polyhedron, the number of vertices minus the number of edges plus the number of faces equals 2. It builds upon the polytope theory and uses combinatorial tools from binomial theory, inclusion-exclusion principle, and combination theorems. The file likely contains definitions of polyhedra, their combinatorial structure, and the formal mathematical machinery needed to prove this fundamental result in polyhedral geometry.

## hyperplane_side

### hyperplane_side
- `hyperplane_side`

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let hyperplane_side = new_definition
 `hyperplane_side (a,b) (x:real^N) = real_sgn (a dot x - b)`;;
```

### Informal statement
Given a hyperplane in $\mathbb{R}^N$ represented by a pair $(a, b)$ where $a$ is a vector in $\mathbb{R}^N$ and $b$ is a real number, and a point $x$ in $\mathbb{R}^N$, the function `hyperplane_side` determines which side of the hyperplane the point lies on:

$$\text{hyperplane\_side}(a, b)(x) = \text{sgn}(a \cdot x - b)$$

where:
- $a \cdot x$ represents the dot product of vectors $a$ and $x$
- $\text{sgn}$ is the sign function that returns:
  - $+1$ if the argument is positive
  - $0$ if the argument is zero
  - $-1$ if the argument is negative

### Informal proof
This is a definition, not a theorem, so no proof is provided.

### Mathematical insight
This definition provides a way to determine the relative position of a point with respect to a hyperplane in $\mathbb{R}^N$. A hyperplane can be represented by the equation $a \cdot x = b$, which divides the space into two half-spaces.

The value returned by `hyperplane_side` indicates:
- $+1$ if the point is in the positive half-space ($a \cdot x > b$)
- $0$ if the point lies exactly on the hyperplane ($a \cdot x = b$)
- $-1$ if the point is in the negative half-space ($a \cdot x < b$)

This function is useful in computational geometry, particularly when dealing with polytopes, convex hulls, and related geometric structures where we need to determine whether points lie on one side or the other of a hyperplane.

### Dependencies
- Definitions:
  - `real_sgn` - The sign function on real numbers

### Porting notes
When porting to other systems:
- Ensure the target system has a properly defined sign function (`sgn` or equivalent)
- Dot product notation may vary between systems
- The definition is straightforward and should translate easily to other proof assistants

---

## hyperplane_equiv

### hyperplane_equiv
- `hyperplane_equiv`

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let hyperplane_equiv = new_definition
 `hyperplane_equiv A x y <=>
        !h. h IN A ==> hyperplane_side h x = hyperplane_side h y`;;
```

### Informal statement
The definition `hyperplane_equiv A x y` establishes an equivalence relation between points $x$ and $y$ in $\mathbb{R}^N$ with respect to a set $A$ of hyperplanes. Two points $x$ and $y$ are equivalent under this relation if and only if they lie on the same side of every hyperplane in the set $A$.

Formally, $\text{hyperplane\_equiv } A\, x\, y \iff \forall h \in A, \text{hyperplane\_side } h\, x = \text{hyperplane\_side } h\, y$

Where `hyperplane_side (a,b) x` represents the side of the hyperplane $\{z \in \mathbb{R}^N : a \cdot z = b\}$ on which point $x$ lies, encoded as $\text{sgn}(a \cdot x - b)$ with values in $\{-1, 0, 1\}$.

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
This definition captures the key concept of a hyperplane arrangement partitioning space into regions. Two points are equivalent under `hyperplane_equiv` if they belong to the same region (or cell) of the partition induced by the hyperplanes in set $A$. 

The definition uses the `hyperplane_side` function which assigns a sign (-1, 0, or 1) to indicate whether a point is on the negative side, directly on the hyperplane, or on the positive side. Two points are equivalent precisely when they have the same relationship to all hyperplanes in the set.

This equivalence relation is fundamental in studying the combinatorial and geometric properties of hyperplane arrangements, which are important in computational geometry, optimization theory, and the study of convex polyhedra.

### Dependencies
- Definitions:
  - `hyperplane_side`: Determines which side of a hyperplane a point lies on

### Porting notes
When porting to other systems:
- Ensure the `hyperplane_side` function is properly implemented first
- Note that the definition establishes an equivalence relation which may need to be explicitly proven in some systems
- The `real_sgn` function used in `hyperplane_side` needs to be available or defined in the target system

---

## HYPERPLANE_EQUIV_REFL

### Name of formal statement
HYPERPLANE_EQUIV_REFL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_EQUIV_REFL = prove
 (`!A x. hyperplane_equiv A x x`,
  REWRITE_TAC[hyperplane_equiv]);;
```

### Informal statement
For any set of hyperplanes $A$ and any point $x$, the hyperplane equivalence relation is reflexive, i.e., 
$\forall A, x. \text{hyperplane\_equiv}(A, x, x)$

Where `hyperplane_equiv A x y` means that points $x$ and $y$ are on the same side of all hyperplanes in set $A$.

### Informal proof
The theorem is proved directly by using the definition of `hyperplane_equiv`. 

By definition, `hyperplane_equiv A x y` means that for all hyperplanes $h$ in $A$, the hyperplane side of $x$ equals the hyperplane side of $y$ with respect to $h$. 

Since equality is reflexive, for any hyperplane $h$, we have `hyperplane_side h x = hyperplane_side h x`. Therefore, the statement `hyperplane_equiv A x x` holds trivially for any set $A$ and point $x$.

### Mathematical insight
This theorem establishes the reflexivity property of the hyperplane equivalence relation, which is a fundamental property for any equivalence relation. The hyperplane equivalence relation classifies points based on which side of each hyperplane in a given set they lie on. Points that are on the same side of all hyperplanes in the set are considered equivalent.

This is a foundational result in the theory of polyhedra and convex sets, where hyperplane arrangements are used to define regions in space. The reflexivity property ensures that any point is equivalent to itself with respect to any set of hyperplanes.

### Dependencies
- **Definitions**:
  - `hyperplane_equiv`: Defines when two points are on the same side of all hyperplanes in a given set.

### Porting notes
This theorem should be straightforward to port to other systems. It only requires the definition of `hyperplane_equiv` and relies on basic rewriting tactics. The reflexivity property follows directly from the definition and the reflexivity of equality.

---

## HYPERPLANE_EQUIV_SYM

### Name of formal statement
HYPERPLANE_EQUIV_SYM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_EQUIV_SYM = prove
 (`!A x y. hyperplane_equiv A x y <=> hyperplane_equiv A y x`,
  REWRITE_TAC[hyperplane_equiv; EQ_SYM_EQ]);;
```

### Informal statement
For any set of hyperplanes $A$ and any points $x$ and $y$, the relation $\text{hyperplane\_equiv}$ is symmetric. That is:
$$\text{hyperplane\_equiv}(A, x, y) \Leftrightarrow \text{hyperplane\_equiv}(A, y, x)$$

Where $\text{hyperplane\_equiv}(A, x, y)$ means that for all hyperplanes $h \in A$, the points $x$ and $y$ lie on the same side of the hyperplane $h$.

### Informal proof
The proof follows directly from the definition of `hyperplane_equiv` and the symmetry of equality.

From the definition of `hyperplane_equiv`, we have:
$$\text{hyperplane\_equiv}(A, x, y) \Leftrightarrow \forall h \in A, \text{hyperplane\_side}(h, x) = \text{hyperplane\_side}(h, y)$$

Since equality is symmetric (i.e., $a = b \Leftrightarrow b = a$), we can rewrite:
$$\forall h \in A, \text{hyperplane\_side}(h, x) = \text{hyperplane\_side}(h, y) \Leftrightarrow \forall h \in A, \text{hyperplane\_side}(h, y) = \text{hyperplane\_side}(h, x)$$

This last statement is exactly the definition of $\text{hyperplane\_equiv}(A, y, x)$, which completes the proof.

### Mathematical insight
This theorem establishes the symmetry property of the `hyperplane_equiv` relation. It formalizes the intuitive notion that if point $x$ is on the same side as point $y$ with respect to all hyperplanes in a set $A$, then necessarily point $y$ is on the same side as point $x$ with respect to all those hyperplanes.

The `hyperplane_equiv` relation is important in computational geometry and convex analysis as it helps characterize when two points belong to the same equivalence class determined by a set of hyperplanes. These equivalence classes correspond to the cells of a hyperplane arrangement, which are convex polyhedra. This theorem ensures that this relation behaves as expected by confirming one of the key properties of an equivalence relation (symmetry).

### Dependencies
- **Definitions**
  - `hyperplane_equiv`: Defines when two points lie on the same side of all hyperplanes in a set
- **Theorems**
  - `EQ_SYM_EQ`: A HOL Light theorem expressing that equality is symmetric

### Porting notes
This proof is straightforward to port to other systems, as it relies only on the basic properties of equality and the definition of `hyperplane_equiv`. Ensure that the definition of `hyperplane_equiv` is properly ported first, and that the targeted system has some analogue of the `EQ_SYM_EQ` theorem or can handle symmetry of equality automatically.

---

## HYPERPLANE_EQUIV_TRANS

### HYPERPLANE_EQUIV_TRANS

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let HYPERPLANE_EQUIV_TRANS = prove
 (`!A x y z.
        hyperplane_equiv A x y /\ hyperplane_equiv A y z
        ==> hyperplane_equiv A x z`,
  REWRITE_TAC[hyperplane_equiv] THEN MESON_TAC[]);;
```

### Informal statement
For any set $A$ and points $x$, $y$, and $z$, if $x$ is hyperplane-equivalent to $y$ with respect to $A$ and $y$ is hyperplane-equivalent to $z$ with respect to $A$, then $x$ is hyperplane-equivalent to $z$ with respect to $A$.

Formally:
$$\forall A,x,y,z. \text{hyperplane\_equiv}(A,x,y) \land \text{hyperplane\_equiv}(A,y,z) \Rightarrow \text{hyperplane\_equiv}(A,x,z)$$

Where $\text{hyperplane\_equiv}(A,x,y)$ means that for all hyperplanes $h \in A$, points $x$ and $y$ are on the same side of $h$, i.e., $\text{hyperplane\_side}(h,x) = \text{hyperplane\_side}(h,y)$.

### Informal proof
This theorem proves the transitivity of the hyperplane equivalence relation.

The proof proceeds as follows:
- First, we expand the definition of `hyperplane_equiv` which states that two points are hyperplane equivalent with respect to set $A$ if they lie on the same side of every hyperplane in $A$.
- After expanding the definition, the goal becomes:
  $$\forall A,x,y,z. (\forall h \in A. \text{hyperplane\_side}(h,x) = \text{hyperplane\_side}(h,y)) \land (\forall h \in A. \text{hyperplane\_side}(h,y) = \text{hyperplane\_side}(h,z)) \Rightarrow (\forall h \in A. \text{hyperplane\_side}(h,x) = \text{hyperplane\_side}(h,z))$$
- This is a straightforward application of the transitivity of equality: if $a = b$ and $b = c$, then $a = c$.
- The MESON automated theorem prover is able to complete this proof automatically after the definition is expanded.

### Mathematical insight
This theorem establishes that hyperplane equivalence is a transitive relation. Together with reflexivity and symmetry properties (which would be established separately), this shows that hyperplane equivalence is an equivalence relation.

In geometric terms, this theorem states that if points $x$ and $y$ lie on the same side of every hyperplane in set $A$, and points $y$ and $z$ also lie on the same side of every hyperplane in $A$, then points $x$ and $z$ must lie on the same side of every hyperplane in $A$.

This relation is important in computational geometry, particularly in the study of convex polyhedra and in algorithms for linear programming, as it helps partition space into equivalence classes defined by their relationship to a set of hyperplanes.

### Dependencies
- **Definitions**: 
  - `hyperplane_equiv`: Defines when two points are on the same side of all hyperplanes in a set

### Porting notes
This theorem should be straightforward to port to other proof assistants. The proof relies on basic logical principles (transitivity of equality) and doesn't use any complex HOL Light-specific tactics. After defining the concept of hyperplane equivalence, the proof should be automatable in most systems with a reasonably powerful automated theorem prover.

---

## HYPERPLANE_EQUIV_UNION

### HYPERPLANE_EQUIV_UNION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_EQUIV_UNION = prove
 (`!A B x y. hyperplane_equiv (A UNION B) x y <=>
                hyperplane_equiv A x y /\ hyperplane_equiv B x y`,
  REWRITE_TAC[hyperplane_equiv; IN_UNION] THEN MESON_TAC[]);;
```

### Informal statement
For any sets $A$ and $B$ and points $x$ and $y$, the hyperplane equivalence of $x$ and $y$ with respect to the union $A \cup B$ holds if and only if the hyperplane equivalence holds with respect to both $A$ and $B$ individually. Formally:

$$\text{hyperplane\_equiv}(A \cup B, x, y) \iff \text{hyperplane\_equiv}(A, x, y) \land \text{hyperplane\_equiv}(B, x, y)$$

Where $\text{hyperplane\_equiv}(A, x, y)$ means that for all hyperplanes $h \in A$, the points $x$ and $y$ lie on the same side of the hyperplane $h$.

### Informal proof
The proof follows directly from the definition of `hyperplane_equiv` and the properties of set unions.

By definition, $\text{hyperplane\_equiv}(A \cup B, x, y)$ means that for all hyperplanes $h \in A \cup B$, we have $\text{hyperplane\_side}(h, x) = \text{hyperplane\_side}(h, y)$.

A hyperplane $h$ is in $A \cup B$ if and only if $h \in A$ or $h \in B$. Therefore:
- $\text{hyperplane\_equiv}(A \cup B, x, y)$ is equivalent to:
  - For all $h$, if $h \in A$ or $h \in B$, then $\text{hyperplane\_side}(h, x) = \text{hyperplane\_side}(h, y)$

This is logically equivalent to:
- For all $h$, if $h \in A$, then $\text{hyperplane\_side}(h, x) = \text{hyperplane\_side}(h, y)$, and
- For all $h$, if $h \in B$, then $\text{hyperplane\_side}(h, x) = \text{hyperplane\_side}(h, y)$

Which is exactly the definition of $\text{hyperplane\_equiv}(A, x, y) \land \text{hyperplane\_equiv}(B, x, y)$.

The proof in HOL Light uses `REWRITE_TAC` to expand the definition of `hyperplane_equiv` and `IN_UNION`, then `MESON_TAC` automatically completes the proof using first-order reasoning.

### Mathematical insight
This theorem establishes that hyperplane equivalence distributes over set unions, which is a natural property to expect. Intuitively, two points are on the same side of all hyperplanes in a union if and only if they are on the same side of all hyperplanes in each constituent set.

This result is important for reasoning about convex polyhedra, which can be defined as intersections of half-spaces determined by hyperplanes. The theorem allows us to decompose hyperplane equivalence relations over composite sets into simpler components, facilitating modular analysis and proof construction in computational geometry and convex analysis.

### Dependencies
- Definitions:
  - `hyperplane_equiv`: Defines when two points are on the same side of all hyperplanes in a set
  - `IN_UNION`: The membership relation for union of sets

### Porting notes
When porting to other proof assistants:
1. Ensure that the definition of `hyperplane_equiv` matches exactly, particularly regarding how "being on the same side of a hyperplane" is defined
2. The proof is straightforward first-order reasoning, so most proof assistants should handle it easily with similar automation tactics
3. In systems with strong typeclass support (like Lean or Coq), this could be generalized to work with any appropriate notion of "sides" beyond just hyperplanes

---

## hyperplane_cell

### Name of formal statement
hyperplane_cell

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let hyperplane_cell = new_definition
 `hyperplane_cell A c <=> ?x. c = hyperplane_equiv A x`;;
```

### Informal statement
For a set $A$ of hyperplanes and an equivalence relation $c$, we define $\text{hyperplane\_cell}(A, c)$ to be true if and only if there exists a point $x$ such that $c$ is the equivalence relation induced by $A$ at $x$. That is, $c = \text{hyperplane\_equiv}(A, x)$.

More specifically, $c$ is a cell of the hyperplane arrangement $A$ if it represents the set of all points that lie on the same side of every hyperplane in $A$ as some reference point $x$.

### Informal proof
This is a definition, so there is no proof to translate.

### Mathematical insight
This definition formalizes the concept of a "cell" in a hyperplane arrangement, which is fundamental in computational geometry and the theory of polytopes. 

A hyperplane arrangement $A$ divides the space into regions called cells, where each cell contains points that are on the same side of every hyperplane in the arrangement. Two points are in the same cell if and only if, for each hyperplane in $A$, both points lie on the same side of that hyperplane.

This definition captures the cells as equivalence classes under the relation `hyperplane_equiv`. Each cell is characterized by a particular pattern of "sidedness" with respect to all hyperplanes in the arrangement.

In the context of polytopes and polyhedra, these cells are crucial for understanding the combinatorial structure of the space division induced by a set of hyperplanes.

### Dependencies
#### Definitions:
- `hyperplane_equiv`: Defines an equivalence relation such that two points are equivalent if they lie on the same side of every hyperplane in a given set
- `hyperplane_side`: (Implied dependency) Determines which side of a hyperplane a point lies on

### Porting notes
When porting this definition, ensure that the underlying concept of `hyperplane_side` is properly implemented in the target system. The definition relies on the notion that points can be classified according to which side of a hyperplane they lie on.

In some systems, you may need to explicitly define the equivalence relation properties (reflexivity, symmetry, transitivity) for `hyperplane_equiv` if they aren't automatically derived from the definition.

---

## HYPERPLANE_CELL

### HYPERPLANE_CELL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELL = prove
 (`hyperplane_cell A c <=> ?x. c = {y | hyperplane_equiv A x y}`,
  REWRITE_TAC[EXTENSION; hyperplane_cell; IN_ELIM_THM; IN] THEN
  MESON_TAC[]);;
```

### Informal statement
The theorem `HYPERPLANE_CELL` states that for a set of hyperplanes $A$ and a set $c$, $c$ is a hyperplane cell with respect to $A$ if and only if there exists a point $x$ such that $c$ equals the set of all points $y$ that are hyperplane-equivalent to $x$ with respect to $A$. In other words:

$$\text{hyperplane\_cell}(A, c) \iff \exists x. \, c = \{y \mid \text{hyperplane\_equiv}(A, x, y)\}$$

where two points are hyperplane-equivalent with respect to $A$ if they lie on the same side of every hyperplane in $A$.

### Informal proof
This theorem is proved by:

* Expanding the definitions and applying set-theoretic principles.
* Using `REWRITE_TAC` with `EXTENSION`, `hyperplane_cell`, `IN_ELIM_THM`, and `IN` to express the goal in terms of set membership.
* The `MESON_TAC[]` tactic then completes the proof automatically by reasoning about the resulting first-order logic formulas.

The proof essentially shows that the original definition `hyperplane_cell A c <=> ?x. c = hyperplane_equiv A x` is equivalent to the statement where `hyperplane_equiv A x` is explicitly represented as a set comprehension `{y | hyperplane_equiv A x y}`.

### Mathematical insight
This theorem provides a more explicit characterization of hyperplane cells. A hyperplane cell represents a region of space where all points have the same relationship to every hyperplane in a given collection. These cells form the building blocks for understanding the geometry of arrangements of hyperplanes.

The theorem bridges two ways of thinking about these cells:
1. The abstract definition using the equivalence relation `hyperplane_equiv`
2. The concrete representation as a set comprehension

This clarification is crucial for working with hyperplane cells in geometric algorithms and proofs about polyhedra and convex sets.

### Dependencies
- **Definitions**:
  - `hyperplane_equiv`: An equivalence relation where two points are equivalent if they lie on the same side of every hyperplane in a given set.
  - `hyperplane_cell`: A cell defined by the equivalence relation `hyperplane_equiv`.

- **Tactics and utilities**:
  - `REWRITE_TAC`
  - `EXTENSION`
  - `IN_ELIM_THM`
  - `IN`
  - `MESON_TAC`

### Porting notes
When porting this theorem, ensure that:
- The equivalence relation `hyperplane_equiv` is properly defined
- Set comprehension notation is available in the target system
- The target system has utilities for set-theoretic reasoning equivalent to `EXTENSION`
- First-order logic reasoning capabilities similar to `MESON_TAC` are available

---

## NOT_HYPERPLANE_CELL_EMPTY

### NOT_HYPERPLANE_CELL_EMPTY
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let NOT_HYPERPLANE_CELL_EMPTY = prove
 (`!A. ~(hyperplane_cell A {})`,
  REWRITE_TAC[hyperplane_cell; EXTENSION; NOT_IN_EMPTY] THEN
  MESON_TAC[HYPERPLANE_EQUIV_REFL; IN]);;
```

### Informal statement
For all sets $A$, the empty set is not a hyperplane cell of $A$.

Formally, $\forall A. \neg(\text{hyperplane_cell}(A, \emptyset))$

### Informal proof
The proof shows that no hyperplane cell can be empty by:

1. Expanding the definition of `hyperplane_cell` and using the principles of set extension and empty set membership.
2. Using the reflexivity of hyperplane equivalence: for any $A$ and $x$, we know that $x$ is hyperplane equivalent to itself (by `HYPERPLANE_EQUIV_REFL`).
3. Therefore, any hyperplane equivalence class must contain at least one element (the representative itself), so it cannot be empty.

The proof concludes by applying the MESON theorem prover with these facts, deriving a contradiction from the assumption that a hyperplane cell could be empty.

### Mathematical insight
This theorem establishes a basic property of hyperplane cells: they cannot be empty sets. A hyperplane cell is an equivalence class under the hyperplane equivalence relation, and such equivalence classes always contain at least their representative element.

This property is important for understanding the structure of the partition induced by hyperplanes - each hyperplane cell must contain at least one point. This insight is fundamental when working with arrangements of hyperplanes in affine or projective spaces and is useful for computational geometry and polyhedral theory.

### Dependencies
- **Theorems**:
  - `HYPERPLANE_EQUIV_REFL`: Reflexivity of hyperplane equivalence, stating that any point is hyperplane equivalent to itself

- **Definitions**: 
  - `hyperplane_cell`: Defines a hyperplane cell of $A$ as an equivalence class under the hyperplane equivalence relation

### Porting notes
When porting this theorem:
- Ensure that the empty set and set membership operations are properly defined
- Make sure the hyperplane equivalence relation is properly defined and its reflexivity is established
- The proof uses extension principles for sets, which should be available in most proof assistants but may have different names

---

## NONEMPTY_HYPERPLANE_CELL

### NONEMPTY_HYPERPLANE_CELL
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let NONEMPTY_HYPERPLANE_CELL = prove
 (`!A c. hyperplane_cell A c ==> ~(c = {})`,
  MESON_TAC[NOT_HYPERPLANE_CELL_EMPTY]);;
```

### Informal statement
For any set $A$ and set $c$, if $c$ is a hyperplane cell in $A$ (i.e., $c$ is an equivalence class under the hyperplane equivalence relation defined by $A$), then $c$ is non-empty.

Formally: $\forall A, c. \text{hyperplane\_cell}(A, c) \Rightarrow c \neq \emptyset$.

### Informal proof
The theorem is proven directly by applying the previously established theorem `NOT_HYPERPLANE_CELL_EMPTY`, which states that the empty set is never a hyperplane cell for any set $A$. The proof uses MESON, an automated theorem prover, to establish the connection.

### Mathematical insight
This theorem establishes a fundamental property of hyperplane cells: they are always non-empty. Hyperplane cells partition a space according to the equivalence relation defined by a set of hyperplanes. The theorem confirms that each equivalence class in this partition contains at least one point, which is expected since each equivalence class should represent a region of space determined by its position relative to each hyperplane in the set $A$.

This result is important for various applications in computational geometry, optimization theory, and in the study of polyhedra, as it ensures that the decomposition of space by hyperplanes always results in non-empty regions.

### Dependencies
- Theorems:
  - `NOT_HYPERPLANE_CELL_EMPTY`: States that the empty set is not a hyperplane cell for any set $A$.
- Definitions:
  - `hyperplane_cell`: Defines a hyperplane cell as an equivalence class under the hyperplane equivalence relation.

### Porting notes
When porting this theorem, ensure that the underlying definitions of hyperplane cells and hyperplane equivalence are correctly implemented. The proof is straightforward if the dependency theorem is already available, making it easy to port to other systems with similar automated reasoning capabilities.

---

## UNIONS_HYPERPLANE_CELLS

### Name of formal statement
UNIONS_HYPERPLANE_CELLS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let UNIONS_HYPERPLANE_CELLS = prove
 (`!A. UNIONS {c | hyperplane_cell A c} = (:real^N)`,
  REWRITE_TAC[EXTENSION; IN_UNIONS; IN_UNIV; IN_ELIM_THM] THEN
  REWRITE_TAC[hyperplane_cell] THEN MESON_TAC[HYPERPLANE_EQUIV_REFL; IN]);;
```

### Informal statement
For any set of hyperplanes $A$ in $\mathbb{R}^N$, the union of all hyperplane cells determined by $A$ is equal to the entire space $\mathbb{R}^N$.

Formally:
$$\forall A. \bigcup\{c \mid c \text{ is a hyperplane cell determined by } A\} = \mathbb{R}^N$$

### Informal proof
The proof proceeds by showing set equality via the extension principle, which means showing that each element belongs to the left-hand side if and only if it belongs to the right-hand side.

The proof uses:
- The definition of set extension (two sets are equal if they contain exactly the same elements)
- The definition of being an element of a union of sets 
- The fact that every element is in the universal set $\mathbb{R}^N$
- The definition of hyperplane cell
- The reflexivity of hyperplane equivalence

Since every point $x$ is hyperplane-equivalent to itself (by `HYPERPLANE_EQUIV_REFL`), each point belongs to some hyperplane cell. Therefore, the union of all hyperplane cells is the entire space $\mathbb{R}^N$.

### Mathematical insight
This theorem establishes that hyperplane cells form a partition of the entire space $\mathbb{R}^N$. Each point in the space belongs to exactly one hyperplane cell.

A hyperplane cell represents an equivalence class under the relation `hyperplane_equiv`, where two points are equivalent if they lie on the same side of every hyperplane in set $A$. The theorem confirms that these equivalence classes collectively cover the entire space.

This result is important in computational geometry and the theory of convex polyhedra, as it shows that a set of hyperplanes divides the space into regions (cells) without leaving any "gaps" - the cells fully partition the space.

### Dependencies
- Definitions:
  - `hyperplane_cell` - defines a cell as an equivalence class under hyperplane equivalence
  
- Theorems:
  - `HYPERPLANE_EQUIV_REFL` - establishes that hyperplane equivalence is reflexive
  - Standard set theory theorems: `EXTENSION`, `IN_UNIONS`, `IN_UNIV`, `IN_ELIM_THM`

### Porting notes
When porting this theorem:
1. Ensure that the hyperplane equivalence relation is properly defined as an equivalence relation
2. The proof relies on basic set theory, which should be available in most proof assistants
3. The MESON tactic in HOL Light is doing some automation - in other systems, you might need to make the steps more explicit, particularly showing how reflexivity of the equivalence relation implies that every point belongs to some cell

---

## DISJOINT_HYPERPLANE_CELLS

### Name of formal statement
DISJOINT_HYPERPLANE_CELLS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DISJOINT_HYPERPLANE_CELLS = prove
 (`!A c1 c2. hyperplane_cell A c1 /\ hyperplane_cell A c2 /\ ~(c1 = c2)
             ==> DISJOINT c1 c2`,
  REWRITE_TAC[hyperplane_cell] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  ASM_REWRITE_TAC[IN_DISJOINT; IN; EXTENSION] THEN
  ASM_MESON_TAC[HYPERPLANE_EQUIV_TRANS; HYPERPLANE_EQUIV_SYM]);;
```

### Informal statement
For any set of hyperplanes $A$ and any two distinct hyperplane cells $c_1$ and $c_2$ induced by $A$, the cells $c_1$ and $c_2$ are disjoint.

Formally, for all $A$, $c_1$, and $c_2$:
$$\text{hyperplane\_cell}(A, c_1) \land \text{hyperplane\_cell}(A, c_2) \land c_1 \neq c_2 \Rightarrow \text{DISJOINT}(c_1, c_2)$$

### Informal proof
We prove that if we have two distinct hyperplane cells $c_1$ and $c_2$ induced by a set of hyperplanes $A$, then these cells must be disjoint.

By definition of `hyperplane_cell`, there exist points $x$ and $y$ such that:
- $c_1 = \text{hyperplane\_equiv}(A, x)$
- $c_2 = \text{hyperplane\_equiv}(A, y)$

We need to show that $c_1$ and $c_2$ are disjoint, i.e., $c_1 \cap c_2 = \emptyset$.

Suppose, for contradiction, that there exists a point $z \in c_1 \cap c_2$. Then:
- $z \in c_1 = \text{hyperplane\_equiv}(A, x)$ implies $\text{hyperplane\_equiv}(A, z, x)$
- $z \in c_2 = \text{hyperplane\_equiv}(A, y)$ implies $\text{hyperplane\_equiv}(A, z, y)$

By the symmetry property of hyperplane equivalence (`HYPERPLANE_EQUIV_SYM`), we have $\text{hyperplane\_equiv}(A, z, y)$ implies $\text{hyperplane\_equiv}(A, y, z)$.

Now, using the transitivity of hyperplane equivalence (`HYPERPLANE_EQUIV_TRANS`), we can deduce:
- From $\text{hyperplane\_equiv}(A, x, z)$ and $\text{hyperplane\_equiv}(A, z, y)$, we get $\text{hyperplane\_equiv}(A, x, y)$

This means that $x$ and $y$ are in the same hyperplane equivalence class with respect to $A$, which implies $c_1 = c_2$ (since $c_1 = \text{hyperplane\_equiv}(A, x)$ and $c_2 = \text{hyperplane\_equiv}(A, y)$).

But this contradicts our assumption that $c_1 \neq c_2$. Therefore, there cannot be a point $z \in c_1 \cap c_2$, which proves that $c_1$ and $c_2$ are disjoint.

### Mathematical insight
This theorem establishes a fundamental property of hyperplane arrangements: the cells created by the arrangement form a partition of the space. Each point belongs to exactly one cell, as the cells are disjoint and cover the entire space.

In geometric terms, hyperplanes divide the space into regions, and points in the same region have the same "side relationship" with each hyperplane in the arrangement. This theorem confirms that these regions (cells) are indeed distinct in the sense that they don't overlap.

This result is important for computational geometry, arrangement theory, and the study of convex polyhedra, as it ensures that the subdivision of space by hyperplanes is well-defined.

### Dependencies
- **Theorems**:
  - `HYPERPLANE_EQUIV_SYM`: The symmetry property of hyperplane equivalence.
  - `HYPERPLANE_EQUIV_TRANS`: The transitivity property of hyperplane equivalence.
- **Definitions**:
  - `hyperplane_cell`: Defines a hyperplane cell as an equivalence class under the hyperplane equivalence relation.

### Porting notes
When porting this theorem, ensure that:
1. The definitions of hyperplane cells and hyperplane equivalence are properly established
2. The properties of an equivalence relation (reflexivity, symmetry, transitivity) for the hyperplane equivalence relation are proven beforehand
3. The set-theoretic operations (especially DISJOINT and set membership) are appropriately handled in the target system

---

## DISJOINT_HYPERPLANE_CELLS_EQ

### DISJOINT_HYPERPLANE_CELLS_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DISJOINT_HYPERPLANE_CELLS_EQ = prove
 (`!A c1 c2. hyperplane_cell A c1 /\ hyperplane_cell A c2
             ==> (DISJOINT c1 c2 <=> ~(c1 = c2))`,
  MESON_TAC[NONEMPTY_HYPERPLANE_CELL; DISJOINT_HYPERPLANE_CELLS;
            SET_RULE `DISJOINT s s <=> s = {}`]);;
```

### Informal statement
For any set of hyperplanes $A$ and hyperplane cells $c_1$ and $c_2$, if $c_1$ and $c_2$ are both hyperplane cells with respect to $A$, then $c_1$ and $c_2$ are disjoint if and only if they are not equal:

$$\forall A, c_1, c_2. \text{hyperplane\_cell}(A, c_1) \wedge \text{hyperplane\_cell}(A, c_2) \Rightarrow (\text{DISJOINT}(c_1, c_2) \Leftrightarrow c_1 \neq c_2)$$

### Informal proof
The proof uses the MESON tactic with several lemmas:

1. From `NONEMPTY_HYPERPLANE_CELL`, we know that any hyperplane cell is non-empty.

2. From `DISJOINT_HYPERPLANE_CELLS`, we know that distinct hyperplane cells are disjoint.

3. The `SET_RULE` is used to establish that a set is disjoint with itself if and only if it is empty: $\text{DISJOINT}(s, s) \Leftrightarrow s = \emptyset$

Combining these facts:
- If $c_1 = c_2$, then $\text{DISJOINT}(c_1, c_2)$ would mean $\text{DISJOINT}(c_1, c_1)$, which implies $c_1 = \emptyset$ by the SET_RULE. But this contradicts `NONEMPTY_HYPERPLANE_CELL`.
- If $c_1 \neq c_2$, then $\text{DISJOINT}(c_1, c_2)$ follows directly from `DISJOINT_HYPERPLANE_CELLS`.

### Mathematical insight
This theorem establishes an important characterization of hyperplane cells: any two hyperplane cells are either identical or completely disjoint. This is a fundamental property of the partition induced by hyperplanes in a space.

The result is particularly useful because it means that the hyperplane cells form a partition of the space - there's no partial overlap between cells. This clean separation makes hyperplane arrangements important in computational geometry and for defining convex polyhedra.

### Dependencies
- Theorems:
  - `NONEMPTY_HYPERPLANE_CELL`: Any hyperplane cell is non-empty.
  - `DISJOINT_HYPERPLANE_CELLS`: Different hyperplane cells are disjoint.
  - `SET_RULE`: A set rule stating that a set is disjoint with itself if and only if it is empty.

- Definitions:
  - `hyperplane_cell`: A hyperplane cell is defined as an equivalence class under the hyperplane equivalence relation.

### Porting notes
When porting this theorem:
1. Ensure that your system has equivalent definitions for hyperplane cells and the disjointness of sets.
2. The proof relies on automated reasoning (MESON_TAC), so you might need to provide more explicit steps in systems with weaker automation.
3. The handling of equivalence classes might differ between systems, so pay attention to how `hyperplane_equiv` is defined in the target system.

---

## HYPERPLANE_CELL_EMPTY

### Name of formal statement
HYPERPLANE_CELL_EMPTY

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELL_EMPTY = prove
 (`hyperplane_cell {} c <=> c = (:real^N)`,
  REWRITE_TAC[HYPERPLANE_CELL; NOT_IN_EMPTY; hyperplane_equiv] THEN
  SET_TAC[]);;
```

### Informal statement
For any set $c$, the statement $\text{hyperplane\_cell } \emptyset \, c$ is true if and only if $c$ equals the entire space $\mathbb{R}^N$.

In other words, when we consider the family of hyperplanes to be empty, the resulting cell of the hyperplane arrangement is the entire space.

### Informal proof
We need to prove that $\text{hyperplane\_cell } \emptyset \, c$ if and only if $c = \mathbb{R}^N$.

First, we use the theorem `HYPERPLANE_CELL`, which states that $\text{hyperplane\_cell } A \, c$ if and only if there exists some $x$ such that $c = \{y \mid \text{hyperplane\_equiv } A \, x \, y\}$.

Then we use the definition of `hyperplane_equiv`, which says that $\text{hyperplane\_equiv } A \, x \, y$ if and only if for all hyperplanes $h \in A$, $\text{hyperplane\_side } h \, x = \text{hyperplane\_side } h \, y$.

When $A = \emptyset$, the condition $h \in \emptyset$ is never satisfied, so the implication is vacuously true for all pairs of points $x$ and $y$. Therefore, $\text{hyperplane\_equiv } \emptyset \, x \, y$ holds for all $x$ and $y$.

Consequently, for any point $x$, the set $\{y \mid \text{hyperplane\_equiv } \emptyset \, x \, y\}$ contains all points in $\mathbb{R}^N$, making it equal to the entire space $\mathbb{R}^N$.

The proof is completed using set-theoretic reasoning tactics in HOL Light.

### Mathematical insight
This theorem establishes the boundary case for hyperplane arrangements. When no hyperplanes are given, there are no constraints on the space, so the only "cell" is the entire space itself.

In the theory of hyperplane arrangements, cells are formed by the intersection of half-spaces defined by hyperplanes. Each hyperplane divides the space into two half-spaces, and a cell represents a region where points are on the same "side" of each hyperplane in the arrangement. When there are no hyperplanes, there are no divisions of space, resulting in a single cell that encompasses the entire space.

This result serves as a natural base case for inductive arguments involving hyperplane arrangements, allowing for systematic analysis of how cells are formed as hyperplanes are incrementally added to an arrangement.

### Dependencies

#### Theorems
- `HYPERPLANE_CELL`: Establishes that a hyperplane cell is defined as the set of points equivalent to some reference point with respect to the given hyperplane arrangement.

#### Definitions
- `hyperplane_equiv`: Defines when two points are equivalent with respect to a hyperplane arrangement (they lie on the same side of each hyperplane).
- `hyperplane_cell`: Defines a cell in a hyperplane arrangement as the equivalence class of some point.

---

## HYPERPLANE_CELL_SING_CASES

### Name of formal statement
HYPERPLANE_CELL_SING_CASES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELL_SING_CASES = prove
 (`!a b c:real^N->bool.
        hyperplane_cell {(a,b)} c
        ==>  c = {x | a dot x = b} \/
             c = {x | a dot x < b} \/
             c = {x | a dot x > b}`,
  REWRITE_TAC[HYPERPLANE_CELL; hyperplane_equiv] THEN
  REWRITE_TAC[FORALL_UNWIND_THM2; IN_SING; hyperplane_side] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_THEN `y:real^N` MP_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
  REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC
   (SPEC `(a:real^N) dot y - b` REAL_SGN_CASES) THEN
  ASM_REWRITE_TAC[REAL_SGN_EQ] THEN
  SIMP_TAC[REAL_SUB_0; REAL_SUB_LT; real_gt;
           REAL_ARITH `x - y < &0 <=> x < y`]);;
```

### Informal statement
For any vectors $a \in \mathbb{R}^N$, scalars $b \in \mathbb{R}$, and sets $c \subseteq \mathbb{R}^N$, if $c$ is a hyperplane cell defined by a singleton set of hyperplanes $\{(a,b)\}$, then $c$ must be one of the following:
- The hyperplane itself: $c = \{x \in \mathbb{R}^N \mid a \cdot x = b\}$
- The negative half-space: $c = \{x \in \mathbb{R}^N \mid a \cdot x < b\}$
- The positive half-space: $c = \{x \in \mathbb{R}^N \mid a \cdot x > b\}$

### Informal proof
The proof analyzes what a hyperplane cell looks like when defined by a single hyperplane:

1. We start by expanding the definition of `hyperplane_cell` and `hyperplane_equiv`.

2. Since we're dealing with a singleton set $\{(a,b)\}$, we can simplify the universal quantification over hyperplanes.

3. By definition, for any $y \in \mathbb{R}^N$, the set $c$ consists of all points $x$ such that $\text{hyperplane_side}(a,b)(x) = \text{hyperplane_side}(a,b)(y)$.

4. The value of $\text{hyperplane_side}(a,b)(y)$ depends on the sign of $a \cdot y - b$, which has three possibilities:
   - If $a \cdot y - b = 0$, then $c = \{x \mid a \cdot x - b = 0\} = \{x \mid a \cdot x = b\}$ (the hyperplane itself).
   - If $a \cdot y - b < 0$, then $c = \{x \mid a \cdot x - b < 0\} = \{x \mid a \cdot x < b\}$ (the negative half-space).
   - If $a \cdot y - b > 0$, then $c = \{x \mid a \cdot x - b > 0\} = \{x \mid a \cdot x > b\}$ (the positive half-space).

5. These three cases exhaust all possibilities for the hyperplane cell defined by a single hyperplane.

### Mathematical insight
This theorem characterizes the possible configurations of hyperplane cells when only a single hyperplane is considered. Intuitively, a single hyperplane divides the space into three distinct regions: the hyperplane itself (where the defining equation is satisfied exactly), and the two half-spaces on either side of the hyperplane.

In the context of computational geometry and convex analysis, this is a fundamental result that helps understand how hyperplanes partition space. This partitioning is essential in algorithms for linear programming, convex hull computation, and in various geometric algorithms where space decomposition is needed.

The result also forms the basis for understanding more complex arrangements where multiple hyperplanes intersect and divide space into numerous cells.

### Dependencies
- Definitions:
  - `hyperplane_side`: Defines the sign of the expression $a \cdot x - b$ for a hyperplane $(a,b)$ and a point $x$
  - `hyperplane_equiv`: Defines when two points are on the same side of all hyperplanes in a set
  - `hyperplane_cell`: Defines a cell as the set of all points equivalent to some point with respect to a set of hyperplanes

- Theorems:
  - `HYPERPLANE_CELL`: Characterizes a hyperplane cell as the set of points that are hyperplane-equivalent to some point

### Porting notes
When porting to other systems, pay attention to:
1. The definition of `real_sgn` which returns -1, 0, or 1 depending on whether its argument is negative, zero, or positive
2. The representation of hyperplanes as pairs $(a,b)$ where $a$ is a vector and $b$ is a scalar
3. The definition of dot product and how vector operations are handled in the target system

---

## HYPERPLANE_CELL_SING

### HYPERPLANE_CELL_SING
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let HYPERPLANE_CELL_SING = prove
 (`!a b c.
        hyperplane_cell {(a,b)} c <=>
        if a = vec 0 then c = (:real^N)
        else c = {x | a dot x = b} \/
             c = {x | a dot x < b} \/
             c = {x | a dot x > b}`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [REWRITE_TAC[hyperplane_cell; hyperplane_equiv; EXTENSION; IN_UNIV] THEN
    REWRITE_TAC[IN] THEN REWRITE_TAC[hyperplane_equiv] THEN
    ASM_SIMP_TAC[IN_SING; FORALL_UNWIND_THM2] THEN
    REWRITE_TAC[hyperplane_side; DOT_LZERO];
    EQ_TAC THEN REWRITE_TAC[HYPERPLANE_CELL_SING_CASES] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[hyperplane_cell; EXTENSION; IN_ELIM_THM] THEN
    REWRITE_TAC[IN] THEN REWRITE_TAC[hyperplane_equiv] THEN
    ASM_SIMP_TAC[IN_SING; FORALL_UNWIND_THM2] THEN
    REWRITE_TAC[hyperplane_side] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `a dot x = b <=> a dot x - b = &0`;
                     REAL_ARITH `a > b <=> a - b > &0`;
                     REAL_ARITH `a < b <=> a - b < &0`] THEN
    ONCE_REWRITE_TAC[GSYM REAL_SGN_EQ] THEN REWRITE_TAC[REAL_SUB_0] THEN
    MATCH_MP_TAC(MESON[]
     `(?x. f x = a) ==> (?x. !y. f y = a <=> f x = f y)`) THEN
    REWRITE_TAC[REAL_SGN_EQ] THENL
     [EXISTS_TAC `b / (a dot a) % a:real^N`;
      EXISTS_TAC `(b - &1) / (a dot a) % a:real^N`;
      EXISTS_TAC `(b + &1) / (a dot a) % a:real^N`] THEN
    ASM_SIMP_TAC[DOT_RMUL; REAL_DIV_RMUL; DOT_EQ_0] THEN REAL_ARITH_TAC]);;
```

### Informal statement
For any vectors $a \in \mathbb{R}^N$, real values $b \in \mathbb{R}$, and sets $c \subseteq \mathbb{R}^N$:

$$\text{hyperplane\_cell } \{(a,b)\} \, c \iff 
\begin{cases}
c = \mathbb{R}^N & \text{if } a = \vec{0} \\
c = \{x \mid a \cdot x = b\} \text{ or } \\
c = \{x \mid a \cdot x < b\} \text{ or } \\
c = \{x \mid a \cdot x > b\} & \text{otherwise}
\end{cases}$$

This theorem characterizes cells created by a single hyperplane in $\mathbb{R}^N$. When the normal vector $a$ is zero, the cell is the entire space. Otherwise, the cell must be one of three possibilities: the hyperplane itself, the open half-space below, or the open half-space above.

### Informal proof
The proof is divided into two cases based on whether $a = \vec{0}$ or not.

**Case 1**: When $a = \vec{0}$
- We expand the definitions of `hyperplane_cell` and `hyperplane_equiv`
- Since $a = \vec{0}$, we have $a \cdot x = 0$ for all $x$, so `hyperplane_side` is constant
- Therefore all points are equivalent under `hyperplane_equiv`, giving us $c = \mathbb{R}^N$

**Case 2**: When $a \neq \vec{0}$
- For the forward direction, we use `HYPERPLANE_CELL_SING_CASES`
- For the reverse direction, we show that each of the three cases satisfies `hyperplane_cell`
- We rewrite using the definition of `hyperplane_cell` and `hyperplane_equiv`
- The key insight is that for each of the three sets, all points within that set have the same sign for $a \cdot x - b$
  - For $\{x \mid a \cdot x = b\}$, we exhibit a point $\frac{b}{a \cdot a} \cdot a$ which lies in the hyperplane
  - For $\{x \mid a \cdot x < b\}$, we exhibit a point $\frac{b-1}{a \cdot a} \cdot a$ which lies in the lower half-space
  - For $\{x \mid a \cdot x > b\}$, we exhibit a point $\frac{b+1}{a \cdot a} \cdot a$ which lies in the upper half-space
- For each case, we show that the `hyperplane_side` for this point matches all points in the corresponding set

### Mathematical insight
This theorem provides a complete classification of cells formed by a single hyperplane in Euclidean space. Specifically:

1. When the normal vector $a$ is zero, the hyperplane is degenerate and the cell is the entire space.
2. Otherwise, there are exactly three possible cells:
   - The hyperplane itself $\{x \mid a \cdot x = b\}$
   - The open half-space below the hyperplane $\{x \mid a \cdot x < b\}$
   - The open half-space above the hyperplane $\{x \mid a \cdot x > b\}$

This classification is fundamental for understanding the geometry of hyperplane arrangements and is a building block for more complex results about convex polyhedra, which are defined as intersections of half-spaces.

### Dependencies
- `HYPERPLANE_CELL_SING_CASES`: A theorem stating that a cell defined by a single hyperplane must be one of three possibilities
- `hyperplane_side`: Defines the side of a hyperplane that a point lies on using the sign of $a \cdot x - b$
- `hyperplane_equiv`: Defines when two points are equivalent with respect to a set of hyperplanes
- `hyperplane_cell`: Defines a cell as a set of points equivalent under `hyperplane_equiv`

### Porting notes
When porting this theorem:
- Ensure that the vector operations (dot product) and sign functions are correctly defined
- The proof uses several specific lemmas about real arithmetic which may need to be recreated in the target system
- The construction of specific points in the second part of the proof may need careful attention to ensure they are well-defined when $a \neq 0$

---

## HYPERPLANE_CELL_UNION

### HYPERPLANE_CELL_UNION
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let HYPERPLANE_CELL_UNION = prove
 (`!A B c:real^N->bool.
        hyperplane_cell (A UNION B) c <=>
        ~(c = {}) /\
        ?c1 c2. hyperplane_cell A c1 /\
                hyperplane_cell B c2 /\
                c = c1 INTER c2`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `c:real^N->bool = {}` THENL
   [ASM_MESON_TAC[NONEMPTY_HYPERPLANE_CELL]; ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[HYPERPLANE_CELL; HYPERPLANE_EQUIV_UNION] THEN
  REWRITE_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
  REWRITE_TAC[MESON[]
   `(?c1 c2. (?x. c1 = f x) /\ (?y. c2 = g y) /\ P c1 c2) <=>
    (?x y. P (f x) (g y))`] THEN
  EQ_TAC THENL [MESON_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN
  MESON_TAC[HYPERPLANE_EQUIV_TRANS; HYPERPLANE_EQUIV_SYM]);;
```

### Informal statement
For any sets of hyperplanes $A$ and $B$ in $\mathbb{R}^N$, and a set $c \subseteq \mathbb{R}^N$, the following are equivalent:

1. $c$ is a cell in the hyperplane arrangement $A \cup B$
2. $c$ is non-empty, and there exist cells $c_1$ in arrangement $A$ and $c_2$ in arrangement $B$ such that $c = c_1 \cap c_2$

Where a hyperplane cell in an arrangement is defined as an equivalence class of points under the relation of being on the same side of every hyperplane in the arrangement.

### Informal proof

The proof has two main parts:

- First, we handle the case where $c = \emptyset$. By the theorem `NONEMPTY_HYPERPLANE_CELL`, all hyperplane cells are non-empty, so this case is immediate.

- For the non-empty case, we use the definition of hyperplane cells and the properties of hyperplane equivalence:

  * By `HYPERPLANE_CELL`, a set $c$ is a cell in arrangement $A \cup B$ if and only if there exists a point $x$ such that $c = \{y \mid \text{hyperplane\_equiv } (A \cup B) \, x \, y\}$.
  
  * By `HYPERPLANE_EQUIV_UNION`, points are equivalent in the union arrangement $A \cup B$ if and only if they are equivalent in both $A$ and $B$ separately.
  
  * This means $c = \{y \mid \text{hyperplane\_equiv } A \, x \, y \text{ and } \text{hyperplane\_equiv } B \, x \, y\}$
  
  * This can be rewritten as $c = \{y \mid \text{hyperplane\_equiv } A \, x \, y\} \cap \{y \mid \text{hyperplane\_equiv } B \, x \, y\}$
  
  * These two sets are precisely cells in arrangements $A$ and $B$ respectively.

  * For the converse direction, we need to show that if $c$ is the intersection of cells from $A$ and $B$, then it's a cell in $A \cup B$. This follows from the transitivity and symmetry of the hyperplane equivalence relation (using `HYPERPLANE_EQUIV_TRANS` and `HYPERPLANE_EQUIV_SYM`).

### Mathematical insight
This theorem characterizes cells in a union of hyperplane arrangements as intersections of cells from the individual arrangements. This is a fundamental result in the theory of hyperplane arrangements, showing how the cell structure of complex arrangements can be understood by breaking them down into simpler components.

The result provides a recursive way to analyze the cell structure of hyperplane arrangements and is essential for understanding the combinatorial structure of arrangements. It's particularly relevant in computational geometry, polyhedral theory, and the study of convex polytopes.

### Dependencies
- **Theorems**:
  - `HYPERPLANE_EQUIV_SYM`: The relation of being equivalent with respect to a hyperplane arrangement is symmetric
  - `HYPERPLANE_EQUIV_TRANS`: The relation of being equivalent with respect to a hyperplane arrangement is transitive
  - `HYPERPLANE_EQUIV_UNION`: Two points are equivalent with respect to a union of hyperplane arrangements if and only if they are equivalent with respect to each arrangement
  - `HYPERPLANE_CELL`: Characterizes hyperplane cells as equivalence classes under the hyperplane equivalence relation
  - `NONEMPTY_HYPERPLANE_CELL`: All hyperplane cells are non-empty

- **Definitions**:
  - `hyperplane_cell`: Defines a hyperplane cell in an arrangement as an equivalence class of points

### Porting notes
When porting this theorem:
1. Ensure that the hyperplane equivalence relation is defined first
2. The proof relies heavily on the properties of the hyperplane equivalence relation (symmetry, transitivity)
3. Be careful with the representation of cells as sets and the treatment of empty sets
4. The predicate calculus manipulation in the middle of the proof (restructuring existential quantifiers) may require different techniques in other proof assistants

---

## FINITE_HYPERPLANE_CELLS

### Name of formal statement
FINITE_HYPERPLANE_CELLS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FINITE_HYPERPLANE_CELLS = prove
 (`!A. FINITE A ==> FINITE {c:real^N->bool | hyperplane_cell A c}`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[HYPERPLANE_CELL_EMPTY; SING_GSPEC; FINITE_SING] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real`; `A:(real^N#real)->bool`] THEN
  STRIP_TAC THEN ONCE_REWRITE_TAC[SET_RULE `a INSERT s = {a} UNION s`] THEN
  REWRITE_TAC[HYPERPLANE_CELL_UNION] THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{ c1 INTER c2:real^N->bool |
                c1 IN {c | hyperplane_cell A c} /\
                c2 IN {c | hyperplane_cell {(a,b)} c}}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
     `{{x:real^N | a dot x = b},{x | a dot x < b},{x | a dot x > b}}` THEN
    REWRITE_TAC[SUBSET; IN_SING; HYPERPLANE_CELL_SING_CASES; IN_ELIM_THM;
                IN_INSERT; NOT_IN_EMPTY; FINITE_INSERT; FINITE_EMPTY];
    REWRITE_TAC[IN_ELIM_THM; SUBSET] THEN MESON_TAC[INTER_COMM]]);;
```

### Informal statement
For any finite set $A$ of hyperplane descriptions (where each description is a pair $(a, b)$ representing $a \cdot x = b$), the collection of all hyperplane cells defined by $A$ is finite.

Formally: For all $A$, if $A$ is finite, then the set $\{c \subseteq \mathbb{R}^N \mid \text{hyperplane\_cell}(A, c)\}$ is also finite.

### Informal proof
The proof proceeds by strong induction on the finite set $A$.

* **Base case**: When $A = \emptyset$
  - By `HYPERPLANE_CELL_EMPTY`, we know that `hyperplane_cell {} c` holds if and only if $c = \mathbb{R}^N$.
  - So there is only one hyperplane cell in this case, making the set a singleton and therefore finite.

* **Inductive case**: Assume $A$ is finite and the result holds for $A$.
  - Consider $A' = A \cup \{(a,b)\}$ for some vector $a$ and scalar $b$.
  - By `HYPERPLANE_CELL_UNION`, a set $c$ is a hyperplane cell for $A'$ if and only if:
    1. $c$ is non-empty, and
    2. There exist cells $c_1$ and $c_2$ where $c_1$ is a hyperplane cell for $A$, $c_2$ is a hyperplane cell for $\{(a,b)\}$, and $c = c_1 \cap c_2$.

  - By `HYPERPLANE_CELL_SING_CASES`, each hyperplane cell for $\{(a,b)\}$ must be one of exactly three possibilities:
    1. $\{x \mid a \cdot x = b\}$ (the hyperplane itself)
    2. $\{x \mid a \cdot x < b\}$ (one side of the hyperplane)
    3. $\{x \mid a \cdot x > b\}$ (the other side of the hyperplane)

  - Therefore, the hyperplane cells for $A'$ are contained in the set of all possible intersections of cells from $A$ with these three sets.
  - By the induction hypothesis, there are finitely many hyperplane cells for $A$.
  - Since we're taking intersections with a finite number of sets (just three possibilities for $c_2$), the resulting collection is also finite.

### Mathematical insight
This theorem establishes that a finite collection of hyperplanes divides space into a finite number of regions (cells). This is a fundamental result in computational geometry, particularly for algorithms involving arrangements of hyperplanes.

The result is intuitive geometrically: each hyperplane cuts space into two half-spaces and the hyperplane itself. As we add hyperplanes, we keep subdividing existing cells, but with a finite number of hyperplanes, we can only have a finite number of resulting cells.

This theorem provides the theoretical foundation for algorithms that compute cell decompositions induced by hyperplanes, which are used in many applications, including linear programming, motion planning, and machine learning.

### Dependencies
- **Theorems:**
  - `HYPERPLANE_CELL_EMPTY`: Characterizes the hyperplane cell for an empty set of constraints
  - `HYPERPLANE_CELL_SING_CASES`: Identifies the possible hyperplane cells from a single hyperplane
  - `HYPERPLANE_CELL_UNION`: Describes how hyperplane cells behave under union of constraint sets
- **Definitions:**
  - `hyperplane_cell`: Defines a cell in the partition induced by a set of hyperplanes

### Porting notes
When porting to other systems:
1. Ensure the target system has a well-developed theory of finite sets and their properties
2. Verify that the system has appropriate support for vector spaces and hyperplanes
3. Note that the proof relies heavily on set operations and their properties, so the target system should have good automation for set reasoning
4. The dependency on `FINITE_INDUCT_STRONG` requires a form of strong induction on finite sets, which might need to be formulated in some systems

---

## FINITE_RESTRICT_HYPERPLANE_CELLS

### Name of formal statement
FINITE_RESTRICT_HYPERPLANE_CELLS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FINITE_RESTRICT_HYPERPLANE_CELLS = prove
 (`!P A. FINITE A ==> FINITE {c:real^N->bool | hyperplane_cell A c /\ P c}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{c:real^N->bool | hyperplane_cell A c}` THEN
  ASM_SIMP_TAC[FINITE_HYPERPLANE_CELLS] THEN SET_TAC[]);;
```

### Informal statement
For any predicate $P$ and any finite collection of hyperplanes $A$ in $\mathbb{R}^N$, the set of hyperplane cells formed by $A$ that satisfy property $P$ is finite.

Formally, for all predicates $P$ and sets $A$, if $A$ is finite, then the set $\{c \subseteq \mathbb{R}^N \mid c \text{ is a hyperplane cell determined by } A \text{ and } P(c) \text{ holds}\}$ is also finite.

### Informal proof
The proof follows a straightforward set-theoretic approach:

1. We know that $\{c \subseteq \mathbb{R}^N \mid c \text{ is a hyperplane cell determined by } A \text{ and } P(c) \text{ holds}\} \subseteq \{c \subseteq \mathbb{R}^N \mid c \text{ is a hyperplane cell determined by } A\}$

2. By the theorem `FINITE_HYPERPLANE_CELLS`, since $A$ is finite, the set of all hyperplane cells determined by $A$ is finite.

3. A subset of a finite set is finite. Thus, the restricted set of hyperplane cells satisfying property $P$ is finite.

### Mathematical insight
This theorem extends `FINITE_HYPERPLANE_CELLS` by showing that any subset of hyperplane cells with an additional property $P$ remains finite. In the context of computational geometry and polyhedral theory, this result is important because:

1. It guarantees that when we filter hyperplane cells by certain properties, we still have a finite collection to work with.

2. This allows for practical algorithms that enumerate or process hyperplane cells with specific properties.

3. It provides a foundation for further complexity results about hyperplane arrangements with constraints.

The theorem is essentially an application of the basic principle that a subset of a finite set is finite, applied in the context of hyperplane cells.

### Dependencies
- Theorems:
  - `FINITE_HYPERPLANE_CELLS`: Proves that the set of hyperplane cells determined by a finite set of hyperplanes is finite.
- Definitions:
  - `hyperplane_cell`: Defines a hyperplane cell as an equivalence class of points that are on the same side of each hyperplane in a given set of hyperplanes.

### Porting notes
When porting this theorem:
1. Ensure that the underlying theory of hyperplane cells and hyperplane equivalence is properly defined in your target system.
2. The proof is a straightforward application of set theory and the finiteness of hyperplane cells, so it should translate easily to other proof assistants.
3. The proof relies on set-theoretic tactics in HOL Light; these may need to be replaced with equivalent reasoning in your target system.

---

## FINITE_SET_OF_HYPERPLANE_CELLS

### Name of formal statement
FINITE_SET_OF_HYPERPLANE_CELLS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FINITE_SET_OF_HYPERPLANE_CELLS = prove
 (`!A C. FINITE A /\ (!c:real^N->bool. c IN C ==> hyperplane_cell A c)
         ==> FINITE C`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{c:real^N->bool | hyperplane_cell A c}` THEN
  ASM_SIMP_TAC[FINITE_HYPERPLANE_CELLS] THEN ASM SET_TAC[]);;
```

### Informal statement
For any set $A$ of hyperplanes (represented as pairs of normal vector and offset) and any set $C$ of subsets of $\mathbb{R}^N$, if $A$ is finite and every element $c \in C$ is a hyperplane cell with respect to $A$, then $C$ is finite.

More precisely, if $A \subseteq \mathbb{R}^N \times \mathbb{R}$ is finite and for all $c \subseteq \mathbb{R}^N$ with $c \in C$, we have that $c$ is a hyperplane cell determined by $A$, then the set $C$ is finite.

### Informal proof
The proof follows directly from the fact that the set of all hyperplane cells determined by a finite set of hyperplanes is itself finite.

- We start with the assumptions that $A$ is finite and every element of $C$ is a hyperplane cell with respect to $A$.
- By the theorem `FINITE_HYPERPLANE_CELLS`, we know that the set $\{c \subseteq \mathbb{R}^N \mid c \text{ is a hyperplane cell determined by } A\}$ is finite.
- Since $C$ is a subset of this set (by our assumption that every element of $C$ is a hyperplane cell determined by $A$), and a subset of a finite set is finite, we conclude that $C$ is finite.

### Mathematical insight
This theorem establishes that any collection of hyperplane cells determined by a finite set of hyperplanes must be finite. 

A hyperplane cell is a region of $\mathbb{R}^N$ defined by a set of constraints of the form $a \cdot x = b$, $a \cdot x < b$, or $a \cdot x > b$ for each hyperplane $(a,b)$ in the collection. The theorem formalizes the intuitive fact that a finite number of hyperplanes can only partition the space into a finite number of regions.

This result is important for computational geometry, polyhedra theory, and algorithms that need to enumerate or iterate through the cells defined by a set of hyperplanes.

### Dependencies
- Theorems:
  - `FINITE_HYPERPLANE_CELLS`: If $A$ is finite, then the set of all hyperplane cells determined by $A$ is finite.
- Definitions:
  - `hyperplane_cell`: A set $c$ is a hyperplane cell determined by $A$ if there exists some point $x$ such that $c$ is the equivalence class of $x$ under the hyperplane equivalence relation defined by $A$.

### Porting notes
When porting this theorem:
1. Ensure that the underlying theory of hyperplanes and hyperplane cells is properly defined.
2. The proof is straightforward using set theory and finiteness properties, so it should translate well to other systems.
3. The key dependency is `FINITE_HYPERPLANE_CELLS`, which would need to be ported first.

---

## PAIRWISE_DISJOINT_HYPERPLANE_CELLS

### Name of formal statement
PAIRWISE_DISJOINT_HYPERPLANE_CELLS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PAIRWISE_DISJOINT_HYPERPLANE_CELLS = prove
 (`!A C. (!c. c IN C ==> hyperplane_cell A c)
         ==> pairwise DISJOINT C`,
  REWRITE_TAC[pairwise] THEN MESON_TAC[DISJOINT_HYPERPLANE_CELLS]);;
```

### Informal statement
For any set of hyperplanes $A$ and any collection $C$ of sets, if every set $c \in C$ is a hyperplane cell with respect to $A$, then the collection $C$ is pairwise disjoint.

Formally: $\forall A, C. (\forall c. c \in C \Rightarrow \text{hyperplane\_cell}(A, c)) \Rightarrow \text{pairwise DISJOINT}(C)$

### Informal proof
This theorem follows directly from a previously proven result about the disjointness of distinct hyperplane cells. The proof uses the definition of "pairwise" disjointness and applies the DISJOINT_HYPERPLANE_CELLS theorem.

The proof proceeds as follows:
- First, we rewrite using the definition of `pairwise`, which states that a collection is pairwise disjoint if any two distinct elements in it are disjoint.
- Then, we apply the theorem DISJOINT_HYPERPLANE_CELLS, which states that any two distinct hyperplane cells of the same arrangement $A$ are disjoint.
- Since all sets in $C$ are hyperplane cells with respect to $A$ (by our assumption), any two distinct elements of $C$ must be disjoint.

### Mathematical insight
This theorem establishes an important property of hyperplane cells: when we consider a collection of cells all defined with respect to the same hyperplane arrangement $A$, these cells form a partition of the space (except for the disjointness part of the definition of a partition).

In geometric terms, hyperplane cells represent the regions into which a space is divided by a collection of hyperplanes. This theorem confirms that these regions do not overlap, which is a fundamental property for applications in computational geometry, arrangement theory, and the study of polyhedra.

The result is important for understanding the structure of hyperplane arrangements and is used in various algorithms that process geometric subdivisions.

### Dependencies
- **Theorems**:
  - `DISJOINT_HYPERPLANE_CELLS`: States that any two distinct hyperplane cells of the same arrangement are disjoint.
  
- **Definitions**:
  - `hyperplane_cell`: Defines what it means for a set to be a hyperplane cell with respect to a collection of hyperplanes.
  - `pairwise`: Not explicitly listed in dependencies but used in the proof.

### Porting notes
When porting this theorem:
- Ensure that you have the correct definition of "pairwise disjointness" in your target system.
- The proof is straightforward and relies mainly on the DISJOINT_HYPERPLANE_CELLS theorem, so focus on porting that dependency correctly first.
- Note that this theorem uses MESON_TAC, an automated reasoning tactic, which might need to be replaced with appropriate automation in the target system.

---

## HYPERPLANE_CELL_INTER_OPEN_AFFINE

### Name of formal statement
HYPERPLANE_CELL_INTER_OPEN_AFFINE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELL_INTER_OPEN_AFFINE = prove
 (`!A c:real^N->bool.
        FINITE A /\ hyperplane_cell A c
        ==> ?s t. open s /\ affine t /\ c = s INTER t`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[HYPERPLANE_CELL_EMPTY] THEN REPEAT STRIP_TAC THEN
    REPEAT(EXISTS_TAC `(:real^N)`) THEN
    ASM_REWRITE_TAC[AFFINE_UNIV; OPEN_UNIV; INTER_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real`; `A:real^N#real->bool`] THEN
  STRIP_TAC THEN ONCE_REWRITE_TAC[SET_RULE `a INSERT s = {a} UNION s`] THEN
  REWRITE_TAC[HYPERPLANE_CELL_UNION] THEN X_GEN_TAC `c':real^N->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real^N->bool`; `c:real^N->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:real^N->bool`) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `t:real^N->bool`] THEN
  STRIP_TAC THEN REWRITE_TAC[HYPERPLANE_CELL_SING] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THENL
   [MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `t:real^N->bool`] THEN
    ASM_REWRITE_TAC[INTER_UNIV];
    MAP_EVERY EXISTS_TAC
     [`s:real^N->bool`; `{x:real^N | a dot x = b} INTER t`] THEN
    ASM_REWRITE_TAC[INTER_ACI] THEN MATCH_MP_TAC AFFINE_INTER THEN
    ASM_REWRITE_TAC[AFFINE_HYPERPLANE];
    MAP_EVERY EXISTS_TAC
     [`{x:real^N | a dot x < b} INTER s`; `t:real^N->bool`] THEN
    ASM_REWRITE_TAC[INTER_ACI] THEN MATCH_MP_TAC OPEN_INTER THEN
    ASM_REWRITE_TAC[OPEN_HALFSPACE_LT];
    MAP_EVERY EXISTS_TAC
     [`{x:real^N | a dot x > b} INTER s`; `t:real^N->bool`] THEN
    ASM_REWRITE_TAC[INTER_ACI] THEN MATCH_MP_TAC OPEN_INTER THEN
    ASM_REWRITE_TAC[OPEN_HALFSPACE_GT]]);;
```

### Informal statement
For any finite set $A$ of hyperplane constraints and a set $c$ in $\mathbb{R}^N$, if $c$ is a hyperplane cell defined by $A$ (i.e., $\text{hyperplane\_cell}\ A\ c$ holds), then there exist sets $s$ and $t$ such that:
- $s$ is open
- $t$ is affine
- $c = s \cap t$

In other words, any hyperplane cell defined by a finite set of constraints can be represented as the intersection of an open set and an affine set.

### Informal proof
We prove this by strong induction on the finite set $A$ of hyperplane constraints.

* **Base case**: When $A = \emptyset$
  By `HYPERPLANE_CELL_EMPTY`, we know that $\text{hyperplane\_cell}\ \emptyset\ c$ implies $c = \mathbb{R}^N$. 
  We can choose $s = t = \mathbb{R}^N$, which is both open and affine, and $c = s \cap t = \mathbb{R}^N$.

* **Induction step**: Assume the theorem holds for set $A$.
  Consider $A \cup \{(a,b)\}$ where $(a,b)$ is a hyperplane constraint with normal vector $a$ and offset $b$.
  
  By `HYPERPLANE_CELL_UNION`, if $c'$ is a hyperplane cell for $A \cup \{(a,b)\}$, then:
  1. $c'$ is non-empty
  2. There exist $c_1$ and $c$ such that:
     - $\text{hyperplane\_cell}\ \{(a,b)\}\ c_1$
     - $\text{hyperplane\_cell}\ A\ c$
     - $c' = c_1 \cap c$
  
  By the induction hypothesis, for $c$ there exist sets $s$ and $t$ such that $s$ is open, $t$ is affine, and $c = s \cap t$.
  
  Now we need to analyze what $c_1$ is using `HYPERPLANE_CELL_SING`. There are several cases:
  
  - If $a = \vec{0}$, then $c_1 = \mathbb{R}^N$, so $c' = c = s \cap t$, which already has the desired form.
  
  - If $a \neq \vec{0}$ and $c_1 = \{x \mid a \cdot x = b\}$ (the hyperplane itself):
    We set $s' = s$ and $t' = \{x \mid a \cdot x = b\} \cap t$.
    Then $c' = c_1 \cap c = \{x \mid a \cdot x = b\} \cap s \cap t = s' \cap t'$.
    $s'$ is open (same as $s$) and $t'$ is affine (intersection of two affine sets).
  
  - If $a \neq \vec{0}$ and $c_1 = \{x \mid a \cdot x < b\}$ (the lower half-space):
    We set $s' = \{x \mid a \cdot x < b\} \cap s$ and $t' = t$.
    Then $c' = c_1 \cap c = \{x \mid a \cdot x < b\} \cap s \cap t = s' \cap t'$.
    $s'$ is open (intersection of two open sets) and $t'$ is affine (same as $t$).
  
  - If $a \neq \vec{0}$ and $c_1 = \{x \mid a \cdot x > b\}$ (the upper half-space):
    Similarly, we set $s' = \{x \mid a \cdot x > b\} \cap s$ and $t' = t$.
    Then $c' = s' \cap t'$ where $s'$ is open and $t'$ is affine.

In all cases, we have shown that $c'$ can be expressed as the intersection of an open set and an affine set, completing the proof.

### Mathematical insight
This theorem provides a structural characterization of hyperplane cells in $\mathbb{R}^N$. Hyperplane cells are fundamental in computational geometry and linear programming, as they correspond to the regions defined by linear constraints.

The result shows that any hyperplane cell has a clean mathematical decomposition: it can be viewed as an open set restricted to some affine subspace. This characterization is particularly useful because:

1. It separates the "interior" part (the open set) from the "boundary" part (the affine constraints)
2. It helps understand the geometric structure of polyhedra and their faces
3. It provides a foundation for analyzing properties like convexity and connectedness of these regions

This decomposition is canonical in the sense that it separates the "equality constraints" (which define the affine subspace) from the "strict inequality constraints" (which define the open portions).

### Dependencies
- **Theorems**:
  - `HYPERPLANE_CELL_EMPTY`: States that the hyperplane cell of an empty set of constraints is the entire space
  - `HYPERPLANE_CELL_SING`: Characterizes hyperplane cells defined by a single constraint
  - `HYPERPLANE_CELL_UNION`: Shows how to construct hyperplane cells from the union of constraint sets

- **Definitions**:
  - `hyperplane_cell`: Defines a hyperplane cell as the set of points that are equivalent with respect to the given hyperplane constraints

### Porting notes
When porting this theorem:
1. Ensure that your system has appropriate definitions for hyperplane cells, affine sets, and open sets
2. The proof relies heavily on set theory operations and properties of affine geometry
3. Breaking down hyperplane constraints one by one is a key strategy in the proof, so ensure your system has good support for induction over finite sets

---

## HYPERPLANE_CELL_RELATIVELY_OPEN

### HYPERPLANE_CELL_RELATIVELY_OPEN
- `HYPERPLANE_CELL_RELATIVELY_OPEN`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let HYPERPLANE_CELL_RELATIVELY_OPEN = prove
 (`!A c:real^N->bool.
        FINITE A /\ hyperplane_cell A c
        ==> open_in (subtopology euclidean (affine hull c)) c`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HYPERPLANE_CELL_INTER_OPEN_AFFINE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `t:real^N->bool`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_CASES_TAC `s INTER t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[OPEN_IN_EMPTY] THEN
  SUBGOAL_THEN `affine hull (s INTER t:real^N->bool) = t`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `affine hull t:real^N->bool` THEN
    ASM_REWRITE_TAC[AFFINE_HULL_EQ] THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE[INTER_COMM]
      AFFINE_HULL_CONVEX_INTER_OPEN) THEN
    ASM_SIMP_TAC[AFFINE_IMP_CONVEX];
    ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_SIMP_TAC[OPEN_IN_OPEN_INTER]]);;
```

### Informal statement
For any set $A$ of hyperplanes in $\mathbb{R}^n$ and any set $c \subseteq \mathbb{R}^n$, if $A$ is finite and $c$ is a hyperplane cell defined by $A$, then $c$ is relatively open in the affine hull of $c$. 

In other words, $c$ is open in the subspace topology induced by the affine hull of $c$.

### Informal proof
We need to prove that if $A$ is finite and $c$ is a hyperplane cell defined by $A$, then $c$ is open in the subtopology of the affine hull of $c$.

- By the theorem `HYPERPLANE_CELL_INTER_OPEN_AFFINE`, we know that if $A$ is finite and $c$ is a hyperplane cell defined by $A$, then there exist sets $s$ and $t$ such that $s$ is open, $t$ is affine, and $c = s \cap t$.

- Suppose for contradiction that $s \cap t = \emptyset$. Then our claim is trivial since the empty set is open in any topology.

- Next, we want to show that the affine hull of $c = s \cap t$ equals $t$.
  * Since $t$ is affine, we have $\text{affine hull}(t) = t$.
  * By the theorem `AFFINE_HULL_CONVEX_INTER_OPEN`, which states that the affine hull of the intersection of a convex set and an open set equals the affine hull of the convex set, and noting that affine sets are convex (by `AFFINE_IMP_CONVEX`), we have:
    $\text{affine hull}(s \cap t) = \text{affine hull}(t) = t$

- Finally, we can rewrite $c = s \cap t = t \cap s$, and by the theorem `OPEN_IN_OPEN_INTER`, the intersection of an open set with an affine set is relatively open in the affine set. Therefore, $c$ is open in the subtopology of its affine hull.

### Mathematical insight
This theorem establishes an important property of hyperplane cells: they are relatively open sets within their affine hulls. This is significant for understanding the geometric structure of these cells.

In convex geometric terms, this means that a hyperplane cell can be viewed as an open set when considered within the appropriate affine subspace. This characterization helps in analyzing the boundary structure of convex polyhedra formed by hyperplane arrangements.

The result fits into the broader theory of convex geometry and polyhedral combinatorics, providing a topological perspective on hyperplane cells that complements their combinatorial description.

### Dependencies
- **Theorems**:
  - `HYPERPLANE_CELL_INTER_OPEN_AFFINE`: Shows that a hyperplane cell can be represented as the intersection of an open set and an affine set
  - `AFFINE_HULL_CONVEX_INTER_OPEN`: (implicitly used) Relates the affine hull of an intersection of a convex set and an open set
  - `AFFINE_IMP_CONVEX`: States that affine sets are convex
  - `OPEN_IN_OPEN_INTER`: Related to openness of intersections in subtopologies
  - `AFFINE_HULL_EQ`: For affine equality reasoning
  - `OPEN_IN_EMPTY`: The empty set is open in any topology

- **Definitions**:
  - `hyperplane_cell`: Defines a hyperplane cell via hyperplane equivalence relations

### Porting notes
When porting this theorem, care should be taken with:
1. The definition of subtopology/subspace topology, which may be handled differently across systems
2. The treatment of affine hulls and how they interact with topological notions
3. The precise definition of hyperplane cells, which could vary across libraries

The proof makes heavy use of facts about the interplay between affine sets, convexity, and topology, which may need to be established separately in the target system.

---

## HYPERPLANE_CELL_RELATIVE_INTERIOR

### Name of formal statement
HYPERPLANE_CELL_RELATIVE_INTERIOR

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELL_RELATIVE_INTERIOR = prove
 (`!A c:real^N->bool.
        FINITE A /\ hyperplane_cell A c
        ==> relative_interior c = c`,
  MESON_TAC[RELATIVE_INTERIOR_OPEN_IN; HYPERPLANE_CELL_RELATIVELY_OPEN]);;
```

### Informal statement
For any finite set $A$ and any set $c$ in $\mathbb{R}^N$, if $c$ is a hyperplane cell determined by $A$, then the relative interior of $c$ equals $c$ itself.

Formally: 
$$\forall A, c \subseteq \mathbb{R}^N. \text{FINITE}(A) \land \text{hyperplane\_cell}(A, c) \Rightarrow \text{relative\_interior}(c) = c$$

### Informal proof
The proof follows by applying two key theorems:

1. By `HYPERPLANE_CELL_RELATIVELY_OPEN`, if $A$ is finite and $c$ is a hyperplane cell determined by $A$, then $c$ is relatively open in the affine hull of $c$. That is, $c$ is open in the subtopology induced by the affine hull of $c$.

2. By `RELATIVE_INTERIOR_OPEN_IN`, if a set is relatively open (open in the subtopology induced by its affine hull), then its relative interior equals the set itself.

Combining these two results yields the conclusion that the relative interior of $c$ equals $c$ itself.

### Mathematical insight
This theorem establishes an important property of hyperplane cells: they are equal to their relative interiors. This means hyperplane cells are relatively open sets within their affine hulls.

The result is significant because:
1. It characterizes hyperplane cells as "full-dimensional" within their affine spans
2. It simplifies analysis of hyperplane cells, as we don't need to distinguish between a cell and its relative interior
3. It's important for the theory of polyhedra, as hyperplane cells are building blocks for describing more complex geometric objects

In the context of convex geometry, relatively open sets play a role similar to open sets in standard topology, but restricted to their affine hulls.

### Dependencies
- **Theorems**:
  - `RELATIVE_INTERIOR_OPEN_IN`: Establishes that if a set is open in the subtopology induced by its affine hull, then its relative interior equals the set itself.
  - `HYPERPLANE_CELL_RELATIVELY_OPEN`: Proves that hyperplane cells are open in the subtopology induced by their affine hulls.

- **Definitions**:
  - `hyperplane_cell`: Defined as `hyperplane_cell A c <=> ?x. c = hyperplane_equiv A x`, meaning $c$ is a hyperplane cell determined by set $A$ if there exists a point $x$ such that $c$ is the hyperplane equivalence class containing $x$.

### Porting notes
When porting this theorem:
1. The notion of relative interior and subtopology should be defined consistently with the standard definitions in convex geometry
2. Ensure the definition of hyperplane cells and hyperplane equivalence classes is properly translated
3. The proof is quite short and relies on applying two key theorems, so focus on ensuring those dependencies are properly ported first

---

## HYPERPLANE_CELL_CONVEX

### Name of formal statement
HYPERPLANE_CELL_CONVEX

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELL_CONVEX = prove
 (`!A c:real^N->bool. hyperplane_cell A c ==> convex c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HYPERPLANE_CELL] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N` SUBST1_TAC) THEN
  REWRITE_TAC[hyperplane_equiv] THEN
  ONCE_REWRITE_TAC[SET_RULE `f x = f y <=> y IN {y | f x = f y}`] THEN
  REWRITE_TAC[GSYM INTERS_IMAGE] THEN MATCH_MP_TAC CONVEX_INTERS THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real`] THEN DISCH_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN REWRITE_TAC[hyperplane_side] THEN
  REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC
   (SPEC `(a:real^N) dot c - b` REAL_SGN_CASES) THEN
  ASM_REWRITE_TAC[REAL_SGN_EQ] THEN
  SIMP_TAC[REAL_SUB_0; REAL_ARITH `a - b > &0 <=> a > b`;
           REAL_ARITH `a - b < &0 <=> a < b`] THEN
  REWRITE_TAC[CONVEX_HALFSPACE_LT; CONVEX_HALFSPACE_GT;
              CONVEX_HYPERPLANE]);;
```

### Informal statement
For any set of hyperplanes $A$ and any set $c$ of points in $\mathbb{R}^N$, if $c$ is a hyperplane cell with respect to $A$, then $c$ is convex.

More precisely, if $c$ is a set of points in $\mathbb{R}^N$ such that there exists a point $x \in \mathbb{R}^N$ where $c = \{y \in \mathbb{R}^N \mid \text{hyperplane\_equiv}(A, x, y)\}$, then $c$ is convex.

Here, $\text{hyperplane\_equiv}(A, x, y)$ means that for all hyperplanes $h \in A$, points $x$ and $y$ are on the same side of hyperplane $h$, i.e., $\text{hyperplane\_side}(h, x) = \text{hyperplane\_side}(h, y)$.

### Informal proof
The proof proceeds as follows:

- We first rewrite the statement using the definition of `hyperplane_cell`: there exists a point $c$ such that the set in question is $\{y \mid \text{hyperplane\_equiv}(A, c, y)\}$.

- We expand `hyperplane_equiv` to get $\{y \mid \forall h \in A, \text{hyperplane\_side}(h, c) = \text{hyperplane\_side}(h, y)\}$.

- This can be rewritten as an intersection of sets: $\bigcap_{h \in A} \{y \mid \text{hyperplane\_side}(h, c) = \text{hyperplane\_side}(h, y)\}$.

- The convexity of an intersection of convex sets is used (`CONVEX_INTERS`), so we need to show that each set in this intersection is convex.

- For each hyperplane $h = (a, b)$ in $A$, we analyze the set $\{y \mid \text{hyperplane\_side}((a, b), c) = \text{hyperplane\_side}((a, b), y)\}$.

- By definition, `hyperplane_side(h, x)` is the sign of $a \cdot x - b$.

- We consider three cases for the value of $a \cdot c - b$:
  * If $a \cdot c - b > 0$, then the set becomes $\{y \mid a \cdot y - b > 0\}$, which is a half-space (convex by `CONVEX_HALFSPACE_GT`).
  * If $a \cdot c - b < 0$, then the set becomes $\{y \mid a \cdot y - b < 0\}$, which is a half-space (convex by `CONVEX_HALFSPACE_LT`).
  * If $a \cdot c - b = 0$, then the set becomes $\{y \mid a \cdot y - b = 0\}$, which is a hyperplane (convex by `CONVEX_HYPERPLANE`).

- Since each set in the intersection is convex, the hyperplane cell itself is convex.

### Mathematical insight
Hyperplane cells are regions of space defined by the relative position with respect to a set of hyperplanes. This theorem establishes that these cells are convex, which is a fundamental property for computational geometry, linear programming, and the theory of polyhedra.

The key insight is that each hyperplane divides the space into three convex regions: the hyperplane itself and the two half-spaces on either side. A hyperplane cell is formed by the intersection of these regions (one for each hyperplane in A), and since the intersection of convex sets is convex, the cell is also convex.

This result is essential for algorithms that work with arrangements of hyperplanes, such as those used in convex optimization and computational geometry.

### Dependencies
- **Theorems**:
  - `HYPERPLANE_CELL`: Definition equivalence for hyperplane cells
  - `CONVEX_INTERS`: The intersection of convex sets is convex
  - `CONVEX_HALFSPACE_LT`: Half-spaces defined by linear inequalities are convex
  - `CONVEX_HALFSPACE_GT`: Half-spaces defined by linear inequalities are convex
  - `CONVEX_HYPERPLANE`: Hyperplanes are convex
  - `REAL_SGN_CASES`: Case analysis for the sign of a real number
  - `REAL_SGN_EQ`: Characterization of when the sign of a real number equals a specific value

- **Definitions**:
  - `hyperplane_side`: Defines which side of a hyperplane a point lies on
  - `hyperplane_equiv`: Defines when two points are on the same side of all hyperplanes in a set
  - `hyperplane_cell`: Defines a cell in the arrangement of hyperplanes

### Porting notes
When porting this theorem:
1. Ensure that your system has robust definitions for hyperplanes, half-spaces, and convexity.
2. The proof relies on case analysis for the sign function (`real_sgn`), so you'll need an equivalent mechanism.
3. The `SET_RULE` tactic is used for set-theoretic reasoning; you may need to replace this with appropriate set manipulation tactics in your system.
4. The proof uses the fact that the intersection of convex sets is convex, which should be a standard result in most libraries.

---

## HYPERPLANE_CELL_INTERS

### Name of formal statement
HYPERPLANE_CELL_INTERS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELL_INTERS = prove
 (`!A C. (!c:real^N->bool. c IN C ==> hyperplane_cell A c) /\
         ~(C = {}) /\ ~(INTERS C = {})
         ==> hyperplane_cell A (INTERS C)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HYPERPLANE_CELL; GSYM MEMBER_NOT_EMPTY] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:real^N` THEN
  REWRITE_TAC[IN_INTERS] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_INTERS; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `c:real^N->bool`);
    X_GEN_TAC `c:real^N->bool` THEN DISCH_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `c:real^N->bool`)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN SIMP_TAC[IN_ELIM_THM] THEN
  ASM_MESON_TAC[HYPERPLANE_EQUIV_SYM; HYPERPLANE_EQUIV_TRANS]);;
```

### Informal statement
For any set of hyperplanes $A$ and any collection $C$ of subsets of $\mathbb{R}^N$, if every set $c \in C$ is a hyperplane cell with respect to $A$, the collection $C$ is non-empty, and the intersection of all sets in $C$ is non-empty, then the intersection of all sets in $C$ is also a hyperplane cell with respect to $A$.

Formally:
$$\forall A, C. (\forall c \in C. \text{hyperplane\_cell}(A, c)) \land C \neq \emptyset \land \bigcap C \neq \emptyset \Rightarrow \text{hyperplane\_cell}(A, \bigcap C)$$

### Informal proof
We need to prove that $\bigcap C$ is a hyperplane cell with respect to $A$. By the definition of a hyperplane cell (`HYPERPLANE_CELL`), we need to show that there exists a point $x$ such that $\bigcap C = \{y \mid \text{hyperplane\_equiv}(A, x, y)\}$.

The proof proceeds as follows:

- Since $\bigcap C$ is non-empty, we can choose a point $z \in \bigcap C$.
- We claim that $\bigcap C = \{y \mid \text{hyperplane\_equiv}(A, z, y)\}$.
- To prove this set equality, we need to show both inclusions:
  
  1. First, let's prove $\bigcap C \subseteq \{y \mid \text{hyperplane\_equiv}(A, z, y)\}$:
     - Let $x \in \bigcap C$.
     - For any set $c \in C$, we know $c$ is a hyperplane cell, so there exists some point $p_c$ such that $c = \{y \mid \text{hyperplane\_equiv}(A, p_c, y)\}$.
     - Since $z \in c$ and $x \in c$, we have $\text{hyperplane\_equiv}(A, p_c, z)$ and $\text{hyperplane\_equiv}(A, p_c, x)$.
     - By symmetry of hyperplane equivalence (`HYPERPLANE_EQUIV_SYM`), we have $\text{hyperplane\_equiv}(A, z, p_c)$.
     - By transitivity of hyperplane equivalence (`HYPERPLANE_EQUIV_TRANS`), we have $\text{hyperplane\_equiv}(A, z, x)$.
     
  2. Now, let's prove $\{y \mid \text{hyperplane\_equiv}(A, z, y)\} \subseteq \bigcap C$:
     - Let $x$ be such that $\text{hyperplane\_equiv}(A, z, x)$.
     - For any set $c \in C$, we need to show that $x \in c$.
     - As above, there exists $p_c$ such that $c = \{y \mid \text{hyperplane\_equiv}(A, p_c, y)\}$.
     - Since $z \in c$, we have $\text{hyperplane\_equiv}(A, p_c, z)$.
     - By symmetry and transitivity of hyperplane equivalence, we can derive that $\text{hyperplane\_equiv}(A, p_c, x)$.
     - Therefore, $x \in c$ for all $c \in C$, which means $x \in \bigcap C$.

Thus, we have shown that $\bigcap C = \{y \mid \text{hyperplane\_equiv}(A, z, y)\}$, which means $\bigcap C$ is a hyperplane cell with respect to $A$.

### Mathematical insight
This theorem establishes an important closure property of hyperplane cells: the intersection of non-empty hyperplane cells, provided it is non-empty, is still a hyperplane cell. 

In geometric terms, a hyperplane cell represents a region in space where points have the same relative position with respect to each hyperplane in set $A$. This theorem shows that if multiple such regions overlap, the overlapping area still maintains this property - it represents points with a consistent relationship to all hyperplanes in $A$.

This result is crucial for understanding the structure of arrangements of hyperplanes, which divide space into convex regions (cells). It allows us to reason about how these cells interact and combine, which is fundamental in computational geometry, convex analysis, and the study of polyhedra.

### Dependencies
- **Theorems**:
  - `HYPERPLANE_EQUIV_SYM`: The hyperplane equivalence relation is symmetric
  - `HYPERPLANE_EQUIV_TRANS`: The hyperplane equivalence relation is transitive
  - `HYPERPLANE_CELL`: Characterizes a hyperplane cell as the set of points equivalent to some point
- **Definitions**:
  - `hyperplane_cell`: Defines what it means for a set to be a hyperplane cell

### Porting notes
When porting this theorem, care should be taken with:
1. The definition of hyperplane equivalence, which typically means two points are on the same side of every hyperplane in the set
2. The representation of the intersection of a collection of sets, which is denoted by INTERS in HOL Light
3. The handling of set extensionality, which is used in the proof to show the equality of two sets

---

## HYPERPLANE_CELL_INTER

### Name of formal statement
HYPERPLANE_CELL_INTER

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELL_INTER = prove
 (`!A s t:real^N->bool.
        hyperplane_cell A s /\ hyperplane_cell A t /\ ~(s INTER t = {})
        ==> hyperplane_cell A (s INTER t)`,
  REWRITE_TAC[GSYM INTERS_2] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HYPERPLANE_CELL_INTERS THEN
  ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; NOT_INSERT_EMPTY]);;
```

### Informal statement
For any set of hyperplanes $A$ and any sets $s, t \subseteq \mathbb{R}^N$, if both $s$ and $t$ are hyperplane cells with respect to $A$, and their intersection is non-empty ($s \cap t \neq \emptyset$), then their intersection $s \cap t$ is also a hyperplane cell with respect to $A$.

### Informal proof
The proof shows that the intersection of two hyperplane cells with a non-empty intersection is itself a hyperplane cell.

- First, rewrite $s \cap t$ as $\bigcap \{s, t\}$ using `INTERS_2`.
- Apply the theorem `HYPERPLANE_CELL_INTERS`, which states that the intersection of a non-empty collection of hyperplane cells is a hyperplane cell, provided the intersection is non-empty.
- To apply this theorem, we need to verify that:
  - Every element in $\{s, t\}$ is a hyperplane cell (which is true by assumption).
  - The set $\{s, t\}$ is non-empty (true since it contains at least $s$ and $t$).
  - The intersection $s \cap t$ is non-empty (given in the assumption).
- These conditions are satisfied based on the assumptions and properties of set insertion.

### Mathematical insight
This theorem establishes a closure property for hyperplane cells: the intersection of two hyperplane cells remains a hyperplane cell, provided the intersection is non-empty. This is a fundamental property for working with hyperplane arrangements and their induced cell decompositions.

A hyperplane cell represents an equivalence class of points with respect to a set of hyperplanes, where two points are equivalent if they lie on the same side of each hyperplane in the set. This theorem shows that when two such equivalence classes have points in common, their intersection forms another valid equivalence class.

The non-emptiness condition is essential, as an empty intersection would not correspond to any valid equivalence class of points.

### Dependencies
- `HYPERPLANE_CELL_INTERS`: The intersection of a non-empty collection of hyperplane cells with non-empty intersection is itself a hyperplane cell.
- `hyperplane_cell`: Definition of a hyperplane cell as an equivalence class under the hyperplane equivalence relation.
- `INTERS_2`: Representation of the binary intersection of two sets as the intersection of a set of two elements.
- Various set-theoretic lemmas about emptiness and insertion.

### Porting notes
When porting this theorem, ensure that the underlying concept of hyperplane cells and their equivalence relation is properly set up. The proof relies on more general results about intersections of arbitrary collections of hyperplane cells, which should be ported first.

---

## hyperplane_cellcomplex

### hyperplane_cellcomplex
- `hyperplane_cellcomplex`

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let hyperplane_cellcomplex = new_definition
 `hyperplane_cellcomplex A s <=>
        ?t. (!c. c IN t ==> hyperplane_cell A c) /\
            s = UNIONS t`;;
```

### Informal statement
A hyperplane cell complex is defined as a set $s$ that can be expressed as the union of hyperplane cells. Formally, we say that $s$ is a hyperplane cell complex with respect to a family of hyperplanes $A$ (denoted as $\text{hyperplane\_cellcomplex}(A, s)$) if and only if:

$$\exists t. (\forall c \in t. \text{hyperplane\_cell}(A, c)) \land (s = \bigcup t)$$

where $t$ is a collection of hyperplane cells determined by the family of hyperplanes $A$.

### Informal proof
This is a definition, so there is no proof to translate.

### Mathematical insight
The concept of a hyperplane cell complex is fundamental in polyhedral geometry and the theory of arrangements. It represents a way to decompose space into cells based on a collection of hyperplanes.

In the context of hyperplane arrangements, the space is partitioned into regions (cells) by the hyperplanes. Each cell corresponds to a specific pattern of signs with respect to the linear functions defining the hyperplanes. The hyperplane cell complex is then the entire collection of these cells, viewed as a single topological space.

This definition allows for studying the topological and combinatorial properties of arrangements of hyperplanes, which has applications in computational geometry, optimization theory, and the study of convex polytopes.

### Dependencies
- Definitions:
  - `hyperplane_cell`: A predicate defining when a set is a cell with respect to a family of hyperplanes
  - `hyperplane_equiv`: Defines an equivalence relation based on hyperplane arrangements (implied from the definition of `hyperplane_cell`)

### Porting notes
When porting this definition to other proof assistants, it's important to ensure that the underlying concepts of hyperplane cells and set unions are appropriately defined. The definition itself is straightforward, but the surrounding theory of hyperplane arrangements may require significant development depending on the target system's mathematical libraries.

---

## HYPERPLANE_CELLCOMPLEX_EMPTY

### HYPERPLANE_CELLCOMPLEX_EMPTY
- hyperplane_cellcomplex_empty

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let HYPERPLANE_CELLCOMPLEX_EMPTY = prove
 (`!A:real^N#real->bool. hyperplane_cellcomplex A {}`,
  GEN_TAC THEN REWRITE_TAC[hyperplane_cellcomplex] THEN
  EXISTS_TAC `{}:(real^N->bool)->bool` THEN
  REWRITE_TAC[NOT_IN_EMPTY; UNIONS_0]);;
```

### Informal statement
For any set $A$ of hyperplanes in $\mathbb{R}^N$, the empty set $\emptyset$ is a hyperplane cell complex determined by $A$.

More formally, for any set $A \subseteq \mathbb{R}^N \times \mathbb{R}$ (representing a set of hyperplanes in $\mathbb{R}^N$), the theorem states that $\text{hyperplane\_cellcomplex}(A, \emptyset)$ holds.

### Informal proof
To prove that the empty set is a hyperplane cell complex determined by $A$, we need to show there exists a collection of hyperplane cells whose union is the empty set.

- By the definition of `hyperplane_cellcomplex`, we need to find a set $t$ of subsets of $\mathbb{R}^N$ such that:
  1. Every element of $t$ is a hyperplane cell determined by $A$
  2. The union of all elements in $t$ equals the empty set

- We choose $t = \emptyset$ (the empty set of cells)
- Since $t$ is empty, the condition that every element of $t$ is a hyperplane cell is vacuously true (there are no elements to check)
- The union of an empty collection of sets is the empty set: $\bigcup \emptyset = \emptyset$

Therefore, the empty set is indeed a hyperplane cell complex determined by any set of hyperplanes $A$.

### Mathematical insight
This theorem establishes that the empty set is always a valid hyperplane cell complex, regardless of the set of hyperplanes used. This is a base case result that allows for recursive constructions and inductive arguments about hyperplane cell complexes.

In the theory of cell decompositions and arrangements of hyperplanes, it's important to have well-defined edge cases like this one. The empty set represents the trivial cell complex with no cells, which serves as a natural starting point when building more complex structures.

The result is analogous to other mathematical conventions where empty structures are considered valid instances of their kind (e.g., the empty set is a valid topology, the empty sum equals zero, etc.).

### Dependencies
- **Definitions**:
  - `hyperplane_cellcomplex`: Defines when a set is a hyperplane cell complex determined by a set of hyperplanes
  - `hyperplane_cell` (implicit): Defines when a set is a cell determined by a set of hyperplanes

- **Tactics and theorems**:
  - `NOT_IN_EMPTY`: States that no element belongs to the empty set
  - `UNIONS_0`: States that the union of an empty collection of sets is the empty set

### Porting notes
When porting this theorem to other proof assistants, the main challenge is to ensure that the definitions of hyperplane cells and cell complexes are properly set up. The proof itself is straightforward and relies on basic set theory facts about the empty set that should be available in any proof assistant. Make sure the theorem stating that the union of an empty collection of sets is the empty set (UNIONS_0) is available or proved first.

---

## HYPERPLANE_CELL_CELLCOMPLEX

### HYPERPLANE_CELL_CELLCOMPLEX

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELL_CELLCOMPLEX = prove
 (`!A c:real^N->bool. hyperplane_cell A c ==> hyperplane_cellcomplex A c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hyperplane_cellcomplex] THEN
  EXISTS_TAC `{c:real^N->bool}` THEN
  ASM_SIMP_TAC[IN_SING; UNIONS_1]);;
```

### Informal statement
For any set of hyperplanes $A$ and any set $c \subseteq \mathbb{R}^N$, if $c$ is a hyperplane cell with respect to $A$, then $c$ is a hyperplane cell complex with respect to $A$.

Formally,
$$\forall A, c \subseteq \mathbb{R}^N. \text{hyperplane\_cell}(A, c) \Rightarrow \text{hyperplane\_cellcomplex}(A, c)$$

### Informal proof
Let $A$ be a set of hyperplanes and $c \subseteq \mathbb{R}^N$ be a hyperplane cell with respect to $A$.

We need to show that $c$ is a hyperplane cell complex with respect to $A$, which means we need to find a set $t$ of hyperplane cells such that $c$ equals the union of all sets in $t$.

The proof is straightforward:
- We choose $t = \{c\}$, the singleton set containing only $c$.
- Since we already know $c$ is a hyperplane cell with respect to $A$, every element in $t$ (which is just $c$ itself) is a hyperplane cell with respect to $A$.
- The union of all sets in $t$ is just $c$ itself, as $t$ contains only $c$: $\bigcup t = \bigcup \{c\} = c$

Therefore, $c$ satisfies the definition of a hyperplane cell complex with respect to $A$.

### Mathematical insight
This theorem establishes that every hyperplane cell is trivially a hyperplane cell complex. It's a basic but important connection between these two concepts.

The key insight is that a hyperplane cell complex is defined as a union of hyperplane cells. Since every set equals the union of the singleton containing itself, any hyperplane cell trivially forms a hyperplane cell complex on its own.

This theorem provides a foundational relationship in the hierarchy of geometric structures formed by hyperplanes, confirming that hyperplane cells are the basic building blocks of hyperplane cell complexes.

### Dependencies
- `hyperplane_cell`: Definition that a set is a hyperplane cell with respect to a set of hyperplanes if it equals the hyperplane equivalence class of some point.
- `hyperplane_cellcomplex`: Definition that a set is a hyperplane cell complex with respect to a set of hyperplanes if it equals the union of some collection of hyperplane cells.

### Porting notes
When porting this theorem:
- The proof is quite straightforward and should be easy to implement in other systems.
- The main challenge might be ensuring that the definitions of hyperplane cell and hyperplane cell complex are correctly ported first.
- Note the use of the singleton set and its union properties, which may require different syntax in other proof assistants.

---

## HYPERPLANE_CELLCOMPLEX_UNIONS

### Name of formal statement
HYPERPLANE_CELLCOMPLEX_UNIONS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELLCOMPLEX_UNIONS = prove
 (`!A C. (!s:real^N->bool. s IN C ==> hyperplane_cellcomplex A s)
         ==> hyperplane_cellcomplex A (UNIONS C)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hyperplane_cellcomplex] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `f:(real^N->bool)->(real^N->bool)->bool` THEN DISCH_TAC THEN
  EXISTS_TAC `UNIONS (IMAGE (f:(real^N->bool)->(real^N->bool)->bool) C)` THEN
  REWRITE_TAC[FORALL_IN_UNIONS; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[UNIONS_IMAGE]] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  ASM SET_TAC[]);;
```

### Informal statement
For any set of hyperplanes $A$ and any collection of sets $C$, if every set $s \in C$ is a hyperplane cell complex with respect to $A$, then the union $\bigcup C$ is also a hyperplane cell complex with respect to $A$.

Formally:
$$\forall A, C. \left(\forall s. s \in C \Rightarrow \text{hyperplane\_cellcomplex}(A, s)\right) \Rightarrow \text{hyperplane\_cellcomplex}(A, \bigcup C)$$

### Informal proof
The proof shows that the union of hyperplane cell complexes is again a hyperplane cell complex.

Recall that a set $s$ is a hyperplane cell complex with respect to $A$ if there exists a collection $t$ of hyperplane cells with respect to $A$ such that $s$ is the union of $t$.

* We begin by rewriting the definition of `hyperplane_cellcomplex`.
* By the assumption, for each $s \in C$, there exists a collection of hyperplane cells $f(s)$ such that $s = \bigcup f(s)$.
* We claim that $\bigcup_{s \in C} f(s)$ is the collection of hyperplane cells that we need.
* First, we verify that every element in this collection is a hyperplane cell with respect to $A$, which follows from our assumption.
* Then we verify that $\bigcup C = \bigcup \bigcup_{s \in C} f(s)$.
* This equality holds because:
  $$\bigcup C = \bigcup_{s \in C} s = \bigcup_{s \in C} \bigcup f(s) = \bigcup \bigcup_{s \in C} f(s)$$

### Mathematical insight
This theorem establishes that the class of hyperplane cell complexes is closed under arbitrary unions. This is an important structural property for topological and geometric reasoning. 

Hyperplane cell complexes are collections of regions formed by hyperplane arrangements, and this theorem shows that we can take unions of such collections while preserving the fundamental structure. This closure property is useful in computational geometry, polyhedral theory, and when analyzing the topology of spaces partitioned by hyperplanes.

### Dependencies
#### Definitions
- `hyperplane_cellcomplex` - Defines a set as a union of hyperplane cells with respect to a set of hyperplanes.

### Porting notes
When porting this theorem:
- Ensure that the target system has a corresponding definition of hyperplane cell complexes.
- The proof relies on set-theoretic reasoning about unions and images, which should be available in most proof assistants.
- Take care with the Skolemization step, as different systems may handle the extraction of choice functions differently.

---

## HYPERPLANE_CELLCOMPLEX_UNION

### Name of formal statement
HYPERPLANE_CELLCOMPLEX_UNION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELLCOMPLEX_UNION = prove
 (`!A s t.
        hyperplane_cellcomplex A s /\ hyperplane_cellcomplex A t
        ==> hyperplane_cellcomplex A (s UNION t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM UNIONS_2] THEN
  MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_UNIONS THEN
  ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY]);;
```

### Informal statement
For any set $A$ of hyperplanes in $\mathbb{R}^N$ and any sets $s$ and $t$, if both $s$ and $t$ are hyperplane cell complexes with respect to $A$, then their union $s \cup t$ is also a hyperplane cell complex with respect to $A$.

Formally: $\forall A, s, t. \text{hyperplane\_cellcomplex}(A, s) \land \text{hyperplane\_cellcomplex}(A, t) \implies \text{hyperplane\_cellcomplex}(A, s \cup t)$

### Informal proof
We need to show that if $s$ and $t$ are both hyperplane cell complexes with respect to $A$, then $s \cup t$ is also a hyperplane cell complex with respect to $A$.

First, we observe that $s \cup t = \bigcup\{s, t\}$, which is the union of a collection containing exactly the sets $s$ and $t$. This is done by applying the theorem `UNIONS_2` (in its symmetric form).

Next, we apply the theorem `HYPERPLANE_CELLCOMPLEX_UNIONS`, which states that the union of any collection of hyperplane cell complexes with respect to $A$ is also a hyperplane cell complex with respect to $A$.

Finally, we complete the proof by showing that every set in our collection $\{s, t\}$ is a hyperplane cell complex with respect to $A$, which is true by our assumptions. This is done by simplifying the relevant set membership conditions with `FORALL_IN_INSERT` and `NOT_IN_EMPTY`.

### Mathematical insight
This theorem establishes that the collection of hyperplane cell complexes with respect to a fixed set of hyperplanes $A$ is closed under binary unions. This is a fundamental property that allows us to build larger hyperplane cell complexes from smaller ones.

A hyperplane cell complex is a union of hyperplane cells, where each cell is a maximal connected region of the space that doesn't intersect any hyperplane in $A$. This theorem is particularly useful in computational geometry, polytope theory, and the study of convex sets, as it allows for modular construction of complex regions from simpler ones.

### Dependencies
#### Theorems:
- `HYPERPLANE_CELLCOMPLEX_UNIONS`: States that if every set in a collection $C$ is a hyperplane cell complex with respect to $A$, then the union of $C$ is also a hyperplane cell complex with respect to $A$.
- `UNIONS_2` (used in symmetric form via `GSYM`): Represents that the union of two sets can be viewed as the union of a collection containing exactly those two sets.
- `FORALL_IN_INSERT`: A set-theoretic rule for quantification over elements of a set formed by insertion.
- `NOT_IN_EMPTY`: A set-theoretic fact stating that no element belongs to the empty set.

#### Definitions:
- `hyperplane_cellcomplex`: A set $s$ is a hyperplane cell complex with respect to $A$ if there exists a collection $t$ of hyperplane cells with respect to $A$ such that $s$ is the union of $t$.

### Porting notes
When porting this theorem:
1. Ensure your system has proper definitions for hyperplane cells and hyperplane cell complexes.
2. The theorem relies on set-theoretic operations and quantification over sets, so ensure your target system has adequate support for these.
3. The proof is relatively straightforward if the dependencies are already ported, particularly `HYPERPLANE_CELLCOMPLEX_UNIONS`.

---

## HYPERPLANE_CELLCOMPLEX_UNIV

### HYPERPLANE_CELLCOMPLEX_UNIV
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let HYPERPLANE_CELLCOMPLEX_UNIV = prove
 (`!A. hyperplane_cellcomplex A (:real^N)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM UNIONS_HYPERPLANE_CELLS] THEN
  MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_UNIONS THEN
  REWRITE_TAC[IN_ELIM_THM; HYPERPLANE_CELL_CELLCOMPLEX]);;
```

### Informal statement
For any set $A$ of hyperplanes in $\mathbb{R}^N$, the entire space $\mathbb{R}^N$ forms a hyperplane cell complex with respect to $A$.

### Informal proof
The proof proceeds as follows:

- We use the fact that $\mathbb{R}^N$ is equal to the union of all hyperplane cells with respect to $A$, which is given by the theorem `UNIONS_HYPERPLANE_CELLS`: 
  $\bigcup\{c \mid c \text{ is a hyperplane cell of } A\} = \mathbb{R}^N$

- We apply `HYPERPLANE_CELLCOMPLEX_UNIONS`, which states that the union of a collection of hyperplane cell complexes is itself a hyperplane cell complex.

- Each individual hyperplane cell $c$ of $A$ is a hyperplane cell complex by `HYPERPLANE_CELL_CELLCOMPLEX`.

- Therefore, the union of all hyperplane cells, which is $\mathbb{R}^N$, forms a hyperplane cell complex with respect to $A$.

### Mathematical insight
This theorem establishes that the entire space $\mathbb{R}^N$ can be viewed as a hyperplane cell complex with respect to any set of hyperplanes $A$. This is an important foundational result in the theory of cell decomposition induced by hyperplanes.

The result shows that hyperplane arrangements naturally partition the entire space into cells, and this partition forms a well-structured decomposition (a cell complex). This decomposition is fundamental in computational geometry, arrangement theory, and the study of convex polyhedra, as it provides a way to systematically analyze the regions formed by intersecting hyperplanes.

The theorem serves as a foundation for further results about hyperplane arrangements and their topological and combinatorial properties.

### Dependencies
- `UNIONS_HYPERPLANE_CELLS`: The union of all hyperplane cells with respect to $A$ equals $\mathbb{R}^N$
- `HYPERPLANE_CELL_CELLCOMPLEX`: Every hyperplane cell is a hyperplane cell complex
- `HYPERPLANE_CELLCOMPLEX_UNIONS`: The union of hyperplane cell complexes is a hyperplane cell complex
- `hyperplane_cellcomplex`: Definition of a hyperplane cell complex with respect to a set of hyperplanes

### Porting notes
When porting this theorem to another proof assistant, ensure that the underlying definitions of hyperplane cells and hyperplane cell complexes are properly formalized. The theorem relies on set-theoretic operations and properties of hyperplane arrangements, which should be available in most proof assistants with good mathematical libraries.

---

## HYPERPLANE_CELLCOMPLEX_INTERS

### Name of formal statement
HYPERPLANE_CELLCOMPLEX_INTERS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELLCOMPLEX_INTERS = prove
 (`!A C. (!s:real^N->bool. s IN C ==> hyperplane_cellcomplex A s)
         ==> hyperplane_cellcomplex A (INTERS C)`,
  let lemma = prove
   (`UNIONS s = UNIONS {t | t IN s /\ ~(t = {})}`,
    REWRITE_TAC[UNIONS_GSPEC] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[NOT_IN_EMPTY]) in
  REPEAT GEN_TAC THEN ASM_CASES_TAC `C:(real^N->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[INTERS_0; HYPERPLANE_CELLCOMPLEX_UNIV] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [hyperplane_cellcomplex] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `f:(real^N->bool)->(real^N->bool)->bool` THEN
  DISCH_TAC THEN SUBGOAL_THEN
   `C = {UNIONS((f:(real^N->bool)->(real^N->bool)->bool) s) | s IN C}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[INTERS_OVER_UNIONS] THEN ONCE_REWRITE_TAC[lemma] THEN
  MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_UNIONS THEN
  REWRITE_TAC[FORALL_IN_GSPEC; IMP_CONJ] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HYPERPLANE_CELL_CELLCOMPLEX THEN
  MATCH_MP_TAC HYPERPLANE_CELL_INTERS THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ASM SET_TAC[]]);;
```

### Informal statement
For any set $A$ of hyperplanes in $\mathbb{R}^N$ and any collection $C$ of sets, if every set $s \in C$ is a hyperplane cell complex with respect to $A$, then the intersection of all sets in $C$ (denoted by $\bigcap_{s \in C} s$) is also a hyperplane cell complex with respect to $A$.

In symbols: $\forall A, C. (\forall s \in C. \text{hyperplane\_cellcomplex}(A, s)) \Rightarrow \text{hyperplane\_cellcomplex}(A, \bigcap_{s \in C} s)$

### Informal proof
The proof proceeds as follows:

* First, we prove a lemma that states $\bigcup s = \bigcup \{t \in s \mid t \neq \emptyset\}$, which allows us to eliminate empty sets from a union without changing the result.

* We handle the trivial case: if $C = \emptyset$, then $\bigcap_{s \in C} s = \mathbb{R}^N$, and we know $\mathbb{R}^N$ is a hyperplane cell complex with respect to any set of hyperplanes (by `HYPERPLANE_CELLCOMPLEX_UNIV`).

* For the non-trivial case where $C \neq \emptyset$:
  1. By the definition of hyperplane cell complex, for each $s \in C$, there exists a set $f(s)$ of hyperplane cells such that $s = \bigcup f(s)$.
  2. We can rewrite $C$ as $\{\bigcup f(s) \mid s \in C\}$.
  3. The intersection $\bigcap_{s \in C} s$ can be rewritten as $\bigcap_{s \in C} \bigcup f(s)$.
  4. Using the distributivity of intersection over union (`INTERS_OVER_UNIONS`), this equals $\bigcup \{\bigcap_{s \in C} t_s \mid t_s \in f(s) \text{ for each } s \in C\}$.
  5. We apply our lemma to eliminate any empty intersections.
  6. By `HYPERPLANE_CELLCOMPLEX_UNIONS`, it suffices to show that each non-empty intersection $\bigcap_{s \in C} t_s$ is a hyperplane cell complex.
  7. Each $t_s$ is a hyperplane cell, so by `HYPERPLANE_CELL_INTERS`, their non-empty intersection is a hyperplane cell.
  8. By `HYPERPLANE_CELL_CELLCOMPLEX`, any hyperplane cell is also a hyperplane cell complex.

Therefore, the intersection $\bigcap_{s \in C} s$ is a hyperplane cell complex with respect to $A$.

### Mathematical insight
This theorem establishes that the intersection of hyperplane cell complexes remains a hyperplane cell complex. This is a fundamental property for describing the structure of polyhedra and cell decompositions in computational geometry.

The proof makes essential use of the distributivity of intersection over union and the fact that the intersection of hyperplane cells is still a hyperplane cell (when non-empty). This closure property is important for operations on polyhedra and for applications in convex geometry.

The result complements `HYPERPLANE_CELLCOMPLEX_UNIONS`, showing that both union and intersection preserve the hyperplane cell complex structure, making these objects well-behaved under standard set operations.

### Dependencies
- Theorems:
  - `HYPERPLANE_CELL_INTERS`: The intersection of a non-empty collection of non-empty hyperplane cells is a hyperplane cell.
  - `HYPERPLANE_CELL_CELLCOMPLEX`: Any hyperplane cell is a hyperplane cell complex.
  - `HYPERPLANE_CELLCOMPLEX_UNIONS`: The union of hyperplane cell complexes is a hyperplane cell complex.
  - `HYPERPLANE_CELLCOMPLEX_UNIV`: The entire space $\mathbb{R}^N$ is a hyperplane cell complex.
  - `INTERS_OVER_UNIONS`: Distributivity of intersection over union.

- Definitions:
  - `hyperplane_cellcomplex`: A set is a hyperplane cell complex if it can be expressed as the union of hyperplane cells.

### Porting notes
When porting this theorem:
- Pay attention to how set operations (unions, intersections) and quantifiers over sets are handled in the target system.
- The proof relies on a lemma about eliminating empty sets from unions. This lemma might need to be proved separately in the target system if not available.
- The distributivity of intersection over union (`INTERS_OVER_UNIONS`) is crucial and may require specific attention in systems with different set theory foundations.
- Ensure the definitions of hyperplane cells and cell complexes are aligned with the HOL Light versions before porting this theorem.

---

## HYPERPLANE_CELLCOMPLEX_INTER

### Name of formal statement
HYPERPLANE_CELLCOMPLEX_INTER

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELLCOMPLEX_INTER = prove
 (`!A s t.
        hyperplane_cellcomplex A s /\ hyperplane_cellcomplex A t
        ==> hyperplane_cellcomplex A (s INTER t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INTERS_2] THEN
  MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_INTERS THEN
  ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY]);;
```

### Informal statement
For any set $A$ of hyperplanes and any sets $s$ and $t$ in $\mathbb{R}^N$, if both $s$ and $t$ are hyperplane cell complexes with respect to $A$, then their intersection $s \cap t$ is also a hyperplane cell complex with respect to $A$.

Formally:
$$\forall A, s, t. \text{hyperplane\_cellcomplex}(A, s) \land \text{hyperplane\_cellcomplex}(A, t) \implies \text{hyperplane\_cellcomplex}(A, s \cap t)$$

### Informal proof
We need to prove that the intersection of two hyperplane cell complexes is also a hyperplane cell complex. The proof proceeds as follows:

- First, we observe that the binary intersection $s \cap t$ can be rewritten as the intersection of a set containing just $s$ and $t$: $s \cap t = \bigcap \{s, t\}$
- This is done using `GSYM INTERS_2`, which provides the equality $s \cap t = \bigcap \{s, t\}$
- Then we apply the theorem `HYPERPLANE_CELLCOMPLEX_INTERS`, which states that the intersection of a collection of hyperplane cell complexes is also a hyperplane cell complex
- The premises of `HYPERPLANE_CELLCOMPLEX_INTERS` require that all elements in the collection are hyperplane cell complexes
- We verify this using `ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY]`, which handles the fact that every element in $\{s, t\}$ (i.e., $s$ and $t$) is a hyperplane cell complex as per our assumptions

### Mathematical insight
This theorem establishes that hyperplane cell complexes are closed under binary intersection. In geometric terms, this means that when we intersect two regions that are each composed of unions of convex cells defined by hyperplanes, the resulting region is also composed of such cells.

This property is important for computational geometry and convex optimization, as it allows us to construct more complex regions by intersecting simpler ones, while maintaining the hyperplane cell complex structure. This ensures that various algorithms which rely on this structure remain applicable to the intersection.

### Dependencies
- Theorems:
  - `HYPERPLANE_CELLCOMPLEX_INTERS`: The intersection of a collection of hyperplane cell complexes is a hyperplane cell complex
  - `INTERS_2`: Represents a binary intersection as the intersection of a two-element set
  
- Definitions:
  - `hyperplane_cellcomplex`: Defines when a set is a hyperplane cell complex with respect to a set of hyperplanes

### Porting notes
When porting this theorem to other systems:
- Ensure the definition of `hyperplane_cellcomplex` is properly translated, maintaining the exact meaning
- The proof relies on expressing binary intersection as the intersection of a set, which might be handled differently in other systems
- Much of the HOL Light proof relies on rewriting tactics, which may need to be adapted to the equivalent tactics in the target system

---

## HYPERPLANE_CELLCOMPLEX_COMPL

### Name of formal statement
HYPERPLANE_CELLCOMPLEX_COMPL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HYPERPLANE_CELLCOMPLEX_COMPL = prove
 (`!A s. hyperplane_cellcomplex A s
         ==> hyperplane_cellcomplex A ((:real^N) DIFF s)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [hyperplane_cellcomplex] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `C:(real^N->bool)->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[UNIONS_INTERS; COMPL_COMPL] THEN
  MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_INTERS THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  X_GEN_TAC `c:real^N->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(:real^N) DIFF c = UNIONS {c' | hyperplane_cell A c' /\ ~(c' = c)}`
  SUBST1_TAC THENL
   [SUBST1_TAC(SYM(ISPEC `A:real^N#real->bool` UNIONS_HYPERPLANE_CELLS)) THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    X_GEN_TAC `c':real^N->bool` THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`A:real^N#real->bool`; `c:real^N->bool`; `c':real^N->bool`]
        DISJOINT_HYPERPLANE_CELLS_EQ) THEN
    ASM_SIMP_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_UNIONS THEN
    ASM_SIMP_TAC[HYPERPLANE_CELL_CELLCOMPLEX; IN_ELIM_THM]]);;
```

### Informal statement
For any set of hyperplanes $A$ and any set $s$ in $\mathbb{R}^N$, if $s$ is a hyperplane cell complex with respect to $A$, then the complement of $s$ in $\mathbb{R}^N$ (i.e., $\mathbb{R}^N \setminus s$) is also a hyperplane cell complex with respect to $A$.

Formally: $\forall A, s. \text{hyperplane\_cellcomplex}(A, s) \Rightarrow \text{hyperplane\_cellcomplex}(A, \mathbb{R}^N \setminus s)$

### Informal proof
We begin with a set $s$ that is a hyperplane cell complex with respect to $A$, meaning there exists a collection $C$ of hyperplane cells such that $s = \bigcup C$.

First, we observe that:
- The complement of $s$ can be written as $\mathbb{R}^N \setminus s = \mathbb{R}^N \setminus \bigcup C = \bigcap_{c \in C} (\mathbb{R}^N \setminus c)$

For each hyperplane cell $c \in C$, we need to prove that $\mathbb{R}^N \setminus c$ is a hyperplane cell complex. We show that:
- $\mathbb{R}^N \setminus c = \bigcup \{c' \mid \text{hyperplane\_cell}(A, c') \text{ and } c' \neq c\}$

This equality follows from:
1. The universe $\mathbb{R}^N$ is the union of all hyperplane cells with respect to $A$ (by `UNIONS_HYPERPLANE_CELLS`)
2. For distinct hyperplane cells $c$ and $c'$, they are disjoint if and only if $c \neq c'$ (by `DISJOINT_HYPERPLANE_CELLS_EQ`)
3. Standard set theory: an element is in $\mathbb{R}^N \setminus c$ if and only if it's in some hyperplane cell $c'$ different from $c$

Since each $c'$ in this union is a hyperplane cell, it's also a hyperplane cell complex by `HYPERPLANE_CELL_CELLCOMPLEX`. Therefore $\mathbb{R}^N \setminus c$ is a union of hyperplane cell complexes, which is itself a hyperplane cell complex by `HYPERPLANE_CELLCOMPLEX_UNIONS`.

Finally, $\mathbb{R}^N \setminus s$ is an intersection of hyperplane cell complexes, and by `HYPERPLANE_CELLCOMPLEX_INTERS`, this intersection is also a hyperplane cell complex.

### Mathematical insight
This theorem establishes closure properties of hyperplane cell complexes under set complement operations. This is important because it shows that the collection of hyperplane cell complexes forms a Boolean algebra of sets. In geometric terms, this means that if a region can be described as a union of hyperplane cells, then its complement can also be described this way.

In computational geometry and algorithmic applications, this property is valuable because it allows operations like "outside of region X" to stay within the same representational framework as "region X" itself, enabling efficient handling of regions in arrangements of hyperplanes.

The proof technique is elegant, using the duality between unions and intersections via De Morgan's laws (complement of a union is the intersection of complements), and showing that the complement of a single hyperplane cell is expressible as a union of other hyperplane cells.

### Dependencies
- Theorems:
  - `UNIONS_HYPERPLANE_CELLS`: The union of all hyperplane cells covers the entire space $\mathbb{R}^N$
  - `DISJOINT_HYPERPLANE_CELLS_EQ`: Two hyperplane cells are disjoint if and only if they are not equal
  - `HYPERPLANE_CELL_CELLCOMPLEX`: Any hyperplane cell is also a hyperplane cell complex
  - `HYPERPLANE_CELLCOMPLEX_UNIONS`: The union of hyperplane cell complexes is a hyperplane cell complex
  - `HYPERPLANE_CELLCOMPLEX_INTERS`: The intersection of hyperplane cell complexes is a hyperplane cell complex

- Definitions:
  - `hyperplane_cell`: A set defined as the equivalence class of a point under hyperplane equivalence
  - `hyperplane_cellcomplex`: A set that can be expressed as a union of hyperplane cells

### Porting notes
When porting this theorem to other proof assistants:

1. Ensure that the hyperplane equivalence relation and hyperplane cells are properly defined first
2. The proof relies heavily on set operations and quantifier manipulations - systems with good set theory libraries will make this easier
3. The hyperplane cell complex representation may need adaptation depending on how geometric objects are represented in the target system
4. The proof uses several specialized theorems about hyperplane cells - these would need to be ported first or their proofs integrated into this one

---

## HYPERPLANE_CELLCOMPLEX_DIFF

### HYPERPLANE_CELLCOMPLEX_DIFF
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let HYPERPLANE_CELLCOMPLEX_DIFF = prove
 (`!A s t.
        hyperplane_cellcomplex A s /\ hyperplane_cellcomplex A t
        ==> hyperplane_cellcomplex A (s DIFF t)`,
  ONCE_REWRITE_TAC[SET_RULE `s DIFF t = s INTER (UNIV DIFF t)`] THEN
  SIMP_TAC[HYPERPLANE_CELLCOMPLEX_COMPL; HYPERPLANE_CELLCOMPLEX_INTER]);;
```

### Informal statement
For any set of hyperplanes $A$ and sets $s$ and $t$ in $\mathbb{R}^N$, if $s$ and $t$ are hyperplane cell complexes with respect to $A$, then the set difference $s \setminus t$ is also a hyperplane cell complex with respect to $A$.

Formally, for all $A$, $s$, and $t$:
$$\text{hyperplane\_cellcomplex}(A,s) \land \text{hyperplane\_cellcomplex}(A,t) \Rightarrow \text{hyperplane\_cellcomplex}(A, s \setminus t)$$

### Informal proof
The proof proceeds by first rewriting the set difference using the identity $s \setminus t = s \cap (\text{UNIV} \setminus t)$, where UNIV represents the universal set (in this case, $\mathbb{R}^N$).

Then we apply two theorems:
1. `HYPERPLANE_CELLCOMPLEX_COMPL`: If $t$ is a hyperplane cell complex with respect to $A$, then its complement $\mathbb{R}^N \setminus t$ is also a hyperplane cell complex with respect to $A$.
2. `HYPERPLANE_CELLCOMPLEX_INTER`: If $s$ and $\mathbb{R}^N \setminus t$ are hyperplane cell complexes with respect to $A$, then their intersection $s \cap (\mathbb{R}^N \setminus t)$ is also a hyperplane cell complex with respect to $A$.

Combining these results, we conclude that $s \setminus t$ is a hyperplane cell complex with respect to $A$.

### Mathematical insight
This theorem establishes closure properties of hyperplane cell complexes under set difference operations. A hyperplane cell complex is a union of cells formed by hyperplanes dividing the space, and this theorem shows that when we take the difference of two such complexes, we still get a valid hyperplane cell complex.

This result is important for manipulating these geometric structures in computational geometry and polyhedral theory. Together with the theorems about unions, intersections, and complements, this provides a complete set of Boolean operations on hyperplane cell complexes, ensuring that these structures form a Boolean algebra.

### Dependencies
- Definitions:
  - `hyperplane_cellcomplex`: Defines a hyperplane cell complex as a union of hyperplane cells.

- Theorems:
  - `HYPERPLANE_CELLCOMPLEX_INTER`: The intersection of two hyperplane cell complexes is a hyperplane cell complex.
  - `HYPERPLANE_CELLCOMPLEX_COMPL`: The complement of a hyperplane cell complex is a hyperplane cell complex.

### Porting notes
When porting this theorem, ensure that the related concepts of hyperplane cells and cell complexes are properly defined first. The proof relies heavily on set-theoretic manipulations, so make sure that the target system has adequate support for set operations and rewriting with set identities.

---

## HYPERPLANE_CELLCOMPLEX_MONO

### HYPERPLANE_CELLCOMPLEX_MONO
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let HYPERPLANE_CELLCOMPLEX_MONO = prove
 (`!A B s:real^N->bool.
        hyperplane_cellcomplex A s /\ A SUBSET B
        ==> hyperplane_cellcomplex B s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [hyperplane_cellcomplex]) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_UNIONS THEN
  X_GEN_TAC `c:real^N->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:real^N->bool`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `B:(real^N#real)->bool = A UNION (B DIFF A)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[hyperplane_cellcomplex; HYPERPLANE_CELL_UNION] THEN
  EXISTS_TAC `{c' INTER c:real^N->bool |c'| hyperplane_cell (B DIFF A) c' /\
                                            ~(c' INTER c = {})}` THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN CONJ_TAC THENL
   [X_GEN_TAC `c':real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`c:real^N->bool`; `c':real^N->bool`] THEN
    ASM_REWRITE_TAC[INTER_COMM];
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN
    X_GEN_TAC `x:real^N` THEN EQ_TAC THENL [DISCH_TAC; MESON_TAC[]] THEN
    MP_TAC(ISPEC `B DIFF A:(real^N#real)->bool` UNIONS_HYPERPLANE_CELLS) THEN
    GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN ASM SET_TAC[]]);;
```

### Informal statement
For all sets of hyperplanes $A$ and $B$ in $\mathbb{R}^N$, and for any set $s \subseteq \mathbb{R}^N$:

If $s$ is a hyperplane cellcomplex with respect to $A$, and $A \subseteq B$, then $s$ is also a hyperplane cellcomplex with respect to $B$.

In other words, if $s$ can be expressed as a union of cells defined by the hyperplanes in $A$, and $A$ is a subset of $B$, then $s$ can also be expressed as a union of cells defined by the hyperplanes in $B$.

### Informal proof
We need to prove that if $s$ is a hyperplane cellcomplex with respect to $A$, and $A \subseteq B$, then $s$ is also a hyperplane cellcomplex with respect to $B$.

* By the definition of `hyperplane_cellcomplex`, since $s$ is a hyperplane cellcomplex with respect to $A$, there exists a set of cells $C$ such that:
  - Each $c \in C$ is a hyperplane cell with respect to $A$
  - $s = \bigcup C$

* First, we observe that $B = A \cup (B \setminus A)$

* To prove that $s$ is a hyperplane cellcomplex with respect to $B$, we'll show that each cell $c \in C$ is a hyperplane cellcomplex with respect to $B$, and then apply the theorem `HYPERPLANE_CELLCOMPLEX_UNIONS`.

* For each cell $c \in C$, which is a hyperplane cell with respect to $A$, we need to express it as a hyperplane cellcomplex with respect to $B$.

* Using the fact that $B = A \cup (B \setminus A)$ and applying `HYPERPLANE_CELL_UNION`, we can show that a hyperplane cell in $B$ can be expressed as an intersection of a hyperplane cell in $A$ and a hyperplane cell in $B \setminus A$.

* We construct the set of all non-empty intersections between $c$ and hyperplane cells with respect to $B \setminus A$:
  $\{c' \cap c \mid c' \text{ is a hyperplane cell with respect to } B \setminus A \text{ and } c' \cap c \neq \emptyset\}$

* Each element in this set is a hyperplane cell with respect to $B$ (by the characterization of hyperplane cells with respect to $A \cup (B \setminus A)$).

* We then verify that the union of these intersections equals $c$, using the fact that the union of all hyperplane cells with respect to $B \setminus A$ covers the entire space $\mathbb{R}^N$ (from `UNIONS_HYPERPLANE_CELLS`).

* Therefore, each cell $c \in C$ is a hyperplane cellcomplex with respect to $B$.

* Applying `HYPERPLANE_CELLCOMPLEX_UNIONS`, since each $c \in C$ is a hyperplane cellcomplex with respect to $B$, their union $s = \bigcup C$ is also a hyperplane cellcomplex with respect to $B$.

### Mathematical insight
This theorem establishes a monotonicity property of hyperplane cellcomplexes: adding more hyperplanes to a set preserves the cellcomplex property. This is intuitively clear because additional hyperplanes can only further partition existing cells, but the overall union remains unchanged.

This result is important in computational geometry and arrangement theory, where it allows incremental construction of cell decompositions. When analyzing the structure of a space divided by hyperplanes, this theorem confirms that you can analyze the decomposition with respect to a larger set of hyperplanes while preserving previously established properties.

The proof highlights the relationship between cells defined by a set of hyperplanes and those defined by a superset, showing how the latter can be constructed as refinements of the former.

### Dependencies
- **Theorems**:
  - `UNIONS_HYPERPLANE_CELLS`: The union of all hyperplane cells with respect to a set A equals the entire space $\mathbb{R}^N$.
  - `HYPERPLANE_CELL_UNION`: Characterizes hyperplane cells with respect to $A \cup B$ as non-empty intersections of hyperplane cells from $A$ and $B$.
  - `HYPERPLANE_CELLCOMPLEX_UNIONS`: If each set in a collection is a hyperplane cellcomplex with respect to $A$, then their union is also a hyperplane cellcomplex with respect to $A$.

- **Definitions**:
  - `hyperplane_cell`: Defines a cell formed by a set of hyperplanes.
  - `hyperplane_cellcomplex`: Defines a set that can be expressed as a union of hyperplane cells.

### Porting notes
When porting this theorem:
1. Ensure the definition of hyperplane cells and cellcomplexes are properly established first.
2. The proof relies heavily on set-theoretic manipulations, which might require different tactics in other systems.
3. The reasoning about partitioning space with hyperplanes might require specific libraries for computational geometry in other proof assistants.
4. The construction of the set of intersections might require careful handling of set comprehensions, which have different syntax across systems.

---

## FINITE_HYPERPLANE_CELLCOMPLEXES

### Name of formal statement
FINITE_HYPERPLANE_CELLCOMPLEXES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FINITE_HYPERPLANE_CELLCOMPLEXES = prove
 (`!A. FINITE A ==> FINITE {c:real^N->bool | hyperplane_cellcomplex A c}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
   `IMAGE UNIONS {t | t SUBSET {c:real^N->bool | hyperplane_cell A c}}` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FINITE_POWERSET; FINITE_HYPERPLANE_CELLS] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM; hyperplane_cellcomplex] THEN
  MESON_TAC[]);;
```

### Informal statement
For any finite set $A$ of hyperplanes (each represented as a pair $(a, b)$ with normal vector $a$ and offset $b$), the set of all hyperplane cell complexes with respect to $A$ is finite. Formally:

$$\forall A. \text{ FINITE } A \Rightarrow \text{ FINITE } \{c \subseteq \mathbb{R}^N \mid \text{hyperplane\_cellcomplex } A \, c\}$$

Where a hyperplane cell complex is a set that can be expressed as the union of hyperplane cells with respect to $A$.

### Informal proof
We prove that for any finite set $A$ of hyperplanes, the set of all hyperplane cell complexes with respect to $A$ is finite.

* First, we apply `MATCH_MP_TAC FINITE_SUBSET` to show that our target set is finite if it's a subset of another finite set.

* We choose as our finite set: `IMAGE UNIONS {t | t SUBSET {c:real^N->bool | hyperplane_cell A c}}`. This represents the set of all possible unions of subsets of hyperplane cells with respect to $A$.

* This set is finite because:
  - By `FINITE_HYPERPLANE_CELLS`, the set of all hyperplane cells with respect to $A$ is finite.
  - By `FINITE_POWERSET`, the powerset (set of all subsets) of a finite set is finite.
  - By `FINITE_IMAGE`, the image of a finite set under a function is finite.

* Finally, we show that every hyperplane cell complex is in this set:
  - By definition, a hyperplane cell complex is the union of a set of hyperplane cells.
  - Every such union corresponds to an element in our constructed set.

Therefore, the set of all hyperplane cell complexes with respect to $A$ is finite.

### Mathematical insight
This theorem establishes that when working with a finite set of hyperplanes, we only have finitely many distinct cell complexes that can be formed. This is important because:

1. It guarantees that algorithms working with these structures will terminate.
2. It shows that the combinatorial complexity of arrangements of hyperplanes is bounded.
3. It provides a foundation for computational geometry algorithms that enumerate or process all possible regions formed by hyperplane arrangements.

The result follows naturally from the fact that hyperplane cell complexes are defined as unions of hyperplane cells, and there are only finitely many hyperplane cells given a finite set of hyperplanes.

### Dependencies
- **Theorems**:
  - `FINITE_HYPERPLANE_CELLS`: Proves that for a finite set of hyperplanes, the set of all hyperplane cells is finite.
  - `FINITE_IMAGE`: The image of a finite set under a function is finite.
  - `FINITE_POWERSET`: The powerset of a finite set is finite.
  - `FINITE_SUBSET`: If a set is a subset of a finite set, then it is finite.

- **Definitions**:
  - `hyperplane_cell`: A hyperplane cell is defined as a set of points that are equivalent under the hyperplane equivalence relation.
  - `hyperplane_cellcomplex`: A set is a hyperplane cell complex if it can be expressed as the union of hyperplane cells.

### Porting notes
When porting this theorem:
1. Ensure that your system has appropriate definitions for hyperplane cells and cell complexes.
2. The proof relies heavily on set theory and finiteness properties, so make sure your target system has good support for these concepts.
3. The use of the powerset operation might require careful handling in systems with different set-theoretic foundations.

---

## FINITE_RESTRICT_HYPERPLANE_CELLCOMPLEXES

### Name of formal statement
FINITE_RESTRICT_HYPERPLANE_CELLCOMPLEXES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FINITE_RESTRICT_HYPERPLANE_CELLCOMPLEXES = prove
 (`!P A. FINITE A
         ==> FINITE {c:real^N->bool | hyperplane_cellcomplex A c /\ P c}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{c:real^N->bool | hyperplane_cellcomplex A c}` THEN
  ASM_SIMP_TAC[FINITE_HYPERPLANE_CELLCOMPLEXES] THEN SET_TAC[]);;
```

### Informal statement
For any predicate $P$ and any finite set $A$ of hyperplanes in $\mathbb{R}^N$, the set of all hyperplane cell complexes formed by $A$ that satisfy the predicate $P$ is finite. In symbols:
$$\forall P, A. \text{FINITE}(A) \Rightarrow \text{FINITE}(\{c \subset \mathbb{R}^N \mid \text{hyperplane\_cellcomplex}(A, c) \land P(c)\})$$

### Informal proof
The proof is straightforward:

1. We start with a finite set of hyperplanes $A$ and need to show that the set $\{c \subset \mathbb{R}^N \mid \text{hyperplane\_cellcomplex}(A, c) \land P(c)\}$ is finite.

2. We apply the theorem `FINITE_SUBSET`, which states that any subset of a finite set is also finite.

3. We show that $\{c \subset \mathbb{R}^N \mid \text{hyperplane\_cellcomplex}(A, c) \land P(c)\}$ is a subset of $\{c \subset \mathbb{R}^N \mid \text{hyperplane\_cellcomplex}(A, c)\}$.

4. Using the theorem `FINITE_HYPERPLANE_CELLCOMPLEXES`, we know that $\{c \subset \mathbb{R}^N \mid \text{hyperplane\_cellcomplex}(A, c)\}$ is finite when $A$ is finite.

5. By set theory, the restricted set (where we add the condition $P(c)$) is clearly a subset of the original set.

6. Therefore, the restricted set is finite.

### Mathematical insight
This theorem extends the result from `FINITE_HYPERPLANE_CELLCOMPLEXES` by showing that any subset of hyperplane cell complexes defined by an additional predicate $P$ also remains finite. This is important for applications where we need to work with specific families of cell complexes that satisfy certain properties.

Hyperplane cell complexes are fundamental structures in computational geometry and polyhedral theory. They decompose space into regions defined by hyperplane arrangements. The result ensures that when working with a finite set of hyperplanes, we can always have only finitely many cell complexes meeting any additional criteria we might impose.

### Dependencies
- **Theorems:**
  - `FINITE_HYPERPLANE_CELLCOMPLEXES`: States that for a finite set of hyperplanes, the set of all possible hyperplane cell complexes is finite.
  - `FINITE_SUBSET`: A set is finite if it is a subset of a finite set.
  
- **Definitions:**
  - `hyperplane_cellcomplex`: Defines a hyperplane cell complex as a union of hyperplane cells.

### Porting notes
When porting this theorem to other systems, ensure that the underlying concepts of hyperplane cells and cell complexes are properly defined. The proof should be easy to replicate in any system with good support for set theory reasoning, as it primarily uses subset relations and finiteness preservation.

---

## FINITE_SET_OF_HYPERPLANE_CELLS

### FINITE_SET_OF_HYPERPLANE_CELLS
- FINITE_SET_OF_HYPERPLANE_CELLS

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FINITE_SET_OF_HYPERPLANE_CELLS = prove
 (`!A C. FINITE A /\ (!c:real^N->bool. c IN C ==> hyperplane_cellcomplex A c)
         ==> FINITE C`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{c:real^N->bool | hyperplane_cellcomplex A c}` THEN
  ASM_SIMP_TAC[FINITE_HYPERPLANE_CELLCOMPLEXES] THEN ASM SET_TAC[]);;
```

### Informal statement
For any set $A$ of hyperplanes in $\mathbb{R}^N$ and any collection $C$ of subsets of $\mathbb{R}^N$, if $A$ is finite and every element $c \in C$ is a hyperplane cell complex with respect to $A$, then $C$ is a finite set.

Formally, $\forall A, C. \text{FINITE}(A) \land (\forall c \in C. \text{hyperplane\_cellcomplex}(A, c)) \Rightarrow \text{FINITE}(C)$.

### Informal proof
This theorem follows directly from the fact that there are only finitely many hyperplane cell complexes that can be formed from a finite set of hyperplanes.

The proof proceeds as follows:
- Assume $A$ is finite and every element $c \in C$ is a hyperplane cell complex with respect to $A$.
- We show that $C$ is finite by proving it is a subset of a finite set.
- Specifically, $C \subseteq \{c \mid \text{hyperplane\_cellcomplex}(A, c)\}$.
- By the theorem `FINITE_HYPERPLANE_CELLCOMPLEXES`, the set of all hyperplane cell complexes formed by $A$ is finite when $A$ is finite.
- Since $C$ is a subset of this finite set, $C$ must also be finite.

### Mathematical insight
This theorem establishes that given a finite set of hyperplanes, we can only form a finite number of distinct hyperplane cell complexes. This is important in computational geometry and polyhedral theory because it shows that the combinatorial complexity of arrangements of hyperplanes is bounded when the number of hyperplanes is finite.

The result is useful for algorithms that enumerate cells or regions formed by hyperplane arrangements, as it guarantees termination for finite inputs. It's also relevant in the theory of polyhedra, where hyperplane arrangements define the faces of polyhedra.

### Dependencies
- Theorems:
  - `FINITE_HYPERPLANE_CELLCOMPLEXES`: If $A$ is finite, then the set of all hyperplane cell complexes formed by $A$ is finite.
  - Various set theory tactics (`SET_TAC`)
  - Various finiteness theorems (`FINITE_SUBSET`)

- Definitions:
  - `hyperplane_cellcomplex`: A set is a hyperplane cell complex with respect to $A$ if it's a union of hyperplane cells with respect to $A$.

### Porting notes
When porting this theorem:
1. Ensure that the concept of hyperplane cells and cell complexes is properly defined in the target system.
2. The theorem relies on set theory operations, so make sure the target system has good support for set operations.
3. The proof uses matching on the `FINITE_SUBSET` theorem and set tactics - these might need to be replaced with appropriate tactics in the target system.

---

## CELL_SUBSET_CELLCOMPLEX

### CELL_SUBSET_CELLCOMPLEX
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let CELL_SUBSET_CELLCOMPLEX = prove
 (`!A s c:real^N->bool.
        hyperplane_cell A c /\ hyperplane_cellcomplex A s
        ==> (c SUBSET s <=> ~(DISJOINT c s))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [hyperplane_cellcomplex]) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN EQ_TAC THENL
   [ASM_CASES_TAC `c:real^N->bool = {}` THENL
     [ASM_MESON_TAC[NONEMPTY_HYPERPLANE_CELL]; ASM SET_TAC[]];
    REWRITE_TAC[DISJOINT; INTER_UNIONS; GSYM MEMBER_NOT_EMPTY] THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `c':real^N->bool`] THEN
    REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`A:(real^N#real)->bool`; `c:real^N->bool`;
      `c':real^N->bool`] DISJOINT_HYPERPLANE_CELLS_EQ) THEN
    ASM_SIMP_TAC[] THEN
    ASM_CASES_TAC `c':real^N->bool = c` THENL
     [DISCH_THEN(K ALL_TAC); ASM SET_TAC[]] THEN
    MATCH_MP_TAC(SET_RULE `c IN C ==> c SUBSET UNIONS C`) THEN
    ASM_MESON_TAC[]]);;
```

### Informal statement
For any set of hyperplanes $A$ in $\mathbb{R}^n$, a hyperplane cell $c$, and a hyperplane cell complex $s$, the following equivalence holds:
$$c \subseteq s \iff c \cap s \neq \emptyset$$

In other words, a hyperplane cell is either entirely contained in a hyperplane cell complex or completely disjoint from it.

### Informal proof
The proof shows that for a hyperplane cell $c$ and a hyperplane cell complex $s$, the cell $c$ is a subset of $s$ if and only if $c$ and $s$ are not disjoint.

* By the definition of a hyperplane cell complex, there exists a set of hyperplane cells $C$ such that $s = \bigcup C$.
* For the forward direction ($c \subseteq s \implies c \cap s \neq \emptyset$):
  * If $c = \emptyset$, we have a contradiction since hyperplane cells are non-empty by `NONEMPTY_HYPERPLANE_CELL`.
  * Otherwise, since $c \subseteq s$, $c \cap s = c \neq \emptyset$.

* For the reverse direction ($c \cap s \neq \emptyset \implies c \subseteq s$):
  * If $c \cap s \neq \emptyset$, then there exists an $x \in c \cap s$.
  * Since $s = \bigcup C$, there is some cell $c' \in C$ such that $x \in c'$.
  * Thus, $x \in c \cap c'$.
  * By `DISJOINT_HYPERPLANE_CELLS_EQ`, two hyperplane cells are either equal or disjoint.
  * Since $c \cap c' \neq \emptyset$, we must have $c = c'$.
  * Therefore, $c \in C$, which implies $c \subseteq \bigcup C = s$.

### Mathematical insight
This theorem establishes an important topological property of hyperplane cell complexes: cells in the complex behave in an "all-or-nothing" manner with respect to containment. A hyperplane cell cannot partially overlap with a cell complex - it is either completely contained within it or completely disjoint from it.

This property stems from the fact that hyperplane cells form a partition of the space, and each cell is defined by a specific sign pattern with respect to the hyperplanes in $A$. The result is fundamental for understanding the structure of arrangements of hyperplanes and is particularly useful in computational geometry and polyhedral theory.

### Dependencies
- Theorems:
  - `NONEMPTY_HYPERPLANE_CELL`: Hyperplane cells are non-empty
  - `DISJOINT_HYPERPLANE_CELLS_EQ`: Two hyperplane cells are disjoint if and only if they are not equal
- Definitions:
  - `hyperplane_cell`: A cell defined by a hyperplane equivalence relation
  - `hyperplane_cellcomplex`: A union of hyperplane cells

### Porting notes
When porting this theorem:
- Ensure that hyperplane cells are properly defined as equivalence classes under the hyperplane equivalence relation.
- The proof relies on the partitioning property of hyperplane cells, which should be established early.
- The set-theoretic reasoning is fairly standard across proof assistants, but specific tactics for handling set operations may differ.

---

## euler_characteristic

### euler_characteristic
- euler_characteristic

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let euler_characteristic = new_definition
 `euler_characteristic A (s:real^N->bool) =
        sum {c | hyperplane_cell A c /\ c SUBSET s}
            (\c. (-- &1) pow (num_of_int(aff_dim c)))`;;
```

### Informal statement
The Euler characteristic of a set $s$ in $\mathbb{R}^N$ with respect to a collection of hyperplanes $A$ is defined as:

$$\text{euler\_characteristic}(A, s) = \sum_{c \in \{c \mid \text{hyperplane\_cell}(A, c) \land c \subseteq s\}} (-1)^{\dim_{\text{aff}}(c)}$$

where:
- $\text{hyperplane\_cell}(A, c)$ means that $c$ is a cell in the hyperplane arrangement $A$
- $c \subseteq s$ indicates that the cell is contained in the set $s$
- $\dim_{\text{aff}}(c)$ is the affine dimension of the cell $c$
- $\text{num\_of\_int}$ converts the dimension to a natural number for the exponentiation

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
The Euler characteristic is a topological invariant that describes the structure of a topological space regardless of how it is bent or stretched. In this context, it is defined using a hyperplane arrangement.

For a polyhedron or cell complex, the Euler characteristic is traditionally calculated as $V - E + F - \ldots$, alternating the sum of the number of faces of each dimension. This definition generalizes that concept to hyperplane arrangements.

The definition computes the Euler characteristic by summing over all cells in the hyperplane arrangement that are contained within the set $s$, with each cell contributing $(-1)$ raised to the power of its affine dimension.

This invariant plays a crucial role in combinatorial topology and the study of polyhedra. It connects to the Euler-Poincaré formula and has applications in the analysis of convex polytopes, simplicial complexes, and more generally in algebraic topology.

### Dependencies
- **Definitions**:
  - `hyperplane_cell`: Defines what constitutes a cell in a hyperplane arrangement, where a cell is an equivalence class under the relation defined by hyperplanes
  - `aff_dim`: (Implicit) The affine dimension of a set
  - `num_of_int`: (Implicit) Conversion from integers to natural numbers

### Porting notes
When porting this definition:
1. Ensure the target system has suitable definitions for hyperplane arrangements and cells
2. Check that the affine dimension concept is defined appropriately
3. Consider how the sum over a set of cells is implemented in the target system
4. Verify that the power operation with negative base is well-defined for the number types used

---

## EULER_CHARACTERISTIC_EMPTY

### EULER_CHARACTERISTIC_EMPTY

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_CHARACTERISTIC_EMPTY = prove
 (`euler_characteristic A {} = &0`,
  REWRITE_TAC[euler_characteristic; SUBSET_EMPTY] THEN
  MATCH_MP_TAC SUM_EQ_0 THEN
  MATCH_MP_TAC(MESON[] `~(?x. x IN s) ==> (!x. x IN s ==> P x)`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[NONEMPTY_HYPERPLANE_CELL]);;
```

### Informal statement
The Euler characteristic of the empty set with respect to any hyperplane arrangement $A$ is zero:

$$\text{euler\_characteristic}(A, \emptyset) = 0$$

### Informal proof
We show that the Euler characteristic of the empty set is zero by proving that the sum defining it contains no terms.

The Euler characteristic is defined as:
$$\text{euler\_characteristic}(A, s) = \sum_{c \in \{c \mid \text{hyperplane\_cell}(A, c) \land c \subseteq s\}} (-1)^{\dim(c)}$$

For the empty set case, we have:
- When $s = \emptyset$, any cell $c$ must satisfy $c \subseteq \emptyset$
- But $c \subseteq \emptyset$ implies $c = \emptyset$
- From `NONEMPTY_HYPERPLANE_CELL`, we know that hyperplane cells cannot be empty
- Therefore, the set $\{c \mid \text{hyperplane\_cell}(A, c) \land c \subseteq \emptyset\}$ must be empty
- Since the sum is taken over an empty set, the result is $0$

### Mathematical insight
This theorem establishes the base case for the Euler characteristic calculation. The Euler characteristic is an important topological invariant that generalizes to various settings. In the context of hyperplane arrangements, it captures combinatorial information about how the hyperplanes divide space.

The empty set has an Euler characteristic of zero because it contains no cells. This aligns with the intuition that the Euler characteristic counts alternating sums of cells of different dimensions, and the empty set has no cells to count.

### Dependencies
#### Theorems
- `NONEMPTY_HYPERPLANE_CELL`: Any hyperplane cell is non-empty

#### Definitions
- `euler_characteristic`: The Euler characteristic of a set with respect to a hyperplane arrangement

### Porting notes
- This proof should be straightforward to port to other systems
- The key insight is to recognize that the empty set cannot contain any hyperplane cells
- Implementation would rely on the system's handling of sums over empty collections

---

## EULER_CHARACTERISTIC_CELL_UNIONS

### EULER_CHARACTERISTIC_CELL_UNIONS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let EULER_CHARACTERISTIC_CELL_UNIONS = prove
 (`!A C. (!c:real^N->bool. c IN C ==> hyperplane_cell A c)
         ==> euler_characteristic A (UNIONS C) =
             sum C (\c. (-- &1) pow (num_of_int(aff_dim c)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[euler_characteristic] THEN
  MATCH_MP_TAC(MESON[] `s = t ==> sum s f = sum t f`) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `c:real^N->bool` THEN
  EQ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN `~(c:real^N->bool = {})` MP_TAC THENL
   [ASM_MESON_TAC[NONEMPTY_HYPERPLANE_CELL]; ALL_TAC] THEN
  REWRITE_TAC[MEMBER_NOT_EMPTY; SUBSET; IN_UNIONS] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c':real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(DISJOINT (c:real^N->bool) c')` MP_TAC THENL
   [ASM SET_TAC[]; ASM_MESON_TAC[DISJOINT_HYPERPLANE_CELLS_EQ]]);;
```

### Informal statement
For any set of hyperplanes $A$ and any collection of hyperplane cells $C$ in $\mathbb{R}^N$ such that every $c \in C$ is a hyperplane cell with respect to $A$, the Euler characteristic of the union of cells in $C$ equals the sum over all cells in $C$ of $(-1)^{\dim(c)}$:

$$\forall A, C. (\forall c \in C. \text{hyperplane\_cell}(A, c)) \Rightarrow \text{euler\_characteristic}(A, \bigcup C) = \sum_{c \in C} (-1)^{\dim(c)}$$

where $\dim(c)$ represents the affine dimension of cell $c$.

### Informal proof
The proof establishes that the Euler characteristic of a union of hyperplane cells equals the sum of the alternating powers of their dimensions.

1. We start by expanding the definition of `euler_characteristic`, which is:
   $$\text{euler\_characteristic}(A, s) = \sum_{c \in \{c \mid \text{hyperplane\_cell}(A, c) \land c \subseteq s\}} (-1)^{\dim(c)}$$

2. We need to show that the set of cells $\{c \mid \text{hyperplane\_cell}(A, c) \land c \subseteq \bigcup C\}$ is equal to $C$ itself.

3. For the direction $\supseteq$:
   - This direction is straightforward set theory: if $c \in C$, then $c \subseteq \bigcup C$ and by assumption $c$ is a hyperplane cell with respect to $A$.

4. For the direction $\subseteq$:
   - Let $c$ be a hyperplane cell with respect to $A$ such that $c \subseteq \bigcup C$.
   - Since $c$ is a hyperplane cell, it is non-empty (by theorem `NONEMPTY_HYPERPLANE_CELL`).
   - Since $c$ is non-empty, there exists a point $x \in c$.
   - Since $c \subseteq \bigcup C$, this point $x$ must be in some cell $c' \in C$.
   - Now we have two hyperplane cells $c$ and $c'$ that share a point, so they are not disjoint.
   - By the theorem `DISJOINT_HYPERPLANE_CELLS_EQ`, two hyperplane cells are disjoint if and only if they are not equal.
   - Therefore, $c = c'$, which means $c \in C$.

5. Since the two sets are equal, their summations over the same function are equal, which proves the theorem.

### Mathematical insight
This theorem is fundamental in combinatorial topology and the study of cell complexes. It shows that the Euler characteristic has an additive property for unions of hyperplane cells, which is a key result in the computation of topological invariants.

The theorem reveals that the Euler characteristic of a union of hyperplane cells can be computed directly from the individual cells, without needing to analyze their intersections. This simplifies many topological computations.

This result is particularly useful in the study of polyhedra, arrangements of hyperplanes, and cell decompositions of spaces, as it provides a way to compute the Euler characteristic from a cell decomposition.

### Dependencies
- **Theorems**:
  - `NONEMPTY_HYPERPLANE_CELL`: Proves that hyperplane cells are non-empty
  - `DISJOINT_HYPERPLANE_CELLS_EQ`: Shows that two hyperplane cells are disjoint if and only if they are not equal

- **Definitions**:
  - `hyperplane_cell`: Defines a hyperplane cell as an equivalence class under hyperplane equivalence
  - `euler_characteristic`: Defines the Euler characteristic as a sum over hyperplane cells with alternating signs based on dimension

### Porting notes
When porting this theorem:
- Ensure the definition of hyperplane cells and Euler characteristic are equivalently defined in the target system
- The proof relies on set-theoretic reasoning about hyperplane cells, so make sure the target system has adequate set theory support
- The dimension calculation and alternating powers may require specific handling in other systems
- The use of the `MESON_TAC` and `SET_TAC` tactics indicates significant automated reasoning; you may need to expand these steps explicitly in systems with weaker automation

---

## EULER_CHARACTERISTIC_CELL

### Name of formal statement
EULER_CHARACTERISTIC_CELL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_CHARACTERISTIC_CELL = prove
 (`!A c. hyperplane_cell A c
         ==> euler_characteristic A c =  (-- &1) pow (num_of_int(aff_dim c))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM UNIONS_1] THEN
  ASM_SIMP_TAC[EULER_CHARACTERISTIC_CELL_UNIONS; IN_SING; SUM_SING]);;
```

### Informal statement
For any set $A$ and any set $c$ in $\mathbb{R}^N$, if $c$ is a hyperplane cell with respect to $A$, then the Euler characteristic of $c$ with respect to $A$ is equal to $(-1)^{\dim(c)}$, where $\dim(c)$ is the affine dimension of $c$.

### Informal proof
We need to prove that if $c$ is a hyperplane cell with respect to $A$, then $\chi_A(c) = (-1)^{\dim(c)}$, where $\chi_A$ is the Euler characteristic function.

The proof proceeds as follows:

- First, we rewrite $c$ as $\bigcup\{c\}$, which is a singleton union containing just $c$ itself.
- Then we apply the theorem `EULER_CHARACTERISTIC_CELL_UNIONS`, which states that for a collection $C$ of hyperplane cells, the Euler characteristic of their union equals the sum of $(-1)^{\dim(c)}$ over all cells $c \in C$.
- Since we're dealing with a singleton set $\{c\}$, where $c$ is a hyperplane cell (by assumption), the conditions for applying `EULER_CHARACTERISTIC_CELL_UNIONS` are satisfied.
- Finally, since we're summing over a singleton set $\{c\}$, the sum simplifies to just $(-1)^{\dim(c)}$.

### Mathematical insight
This theorem provides a formula for the Euler characteristic of a single hyperplane cell. The Euler characteristic is a topological invariant that can be defined for various mathematical objects. In this context, it's defined for hyperplane cells in $\mathbb{R}^N$ with respect to a set $A$ of hyperplanes.

The formula $\chi_A(c) = (-1)^{\dim(c)}$ reveals a fundamental relationship between the Euler characteristic and the dimension of a cell. This is a special case of a more general result `EULER_CHARACTERISTIC_CELL_UNIONS`, which handles unions of cells.

The Euler characteristic plays an important role in combinatorial topology and the study of polyhedra, as it connects geometric properties (like dimension) with topological invariants.

### Dependencies
- **Theorems**:
  - `EULER_CHARACTERISTIC_CELL_UNIONS`: Formula for the Euler characteristic of a union of hyperplane cells

- **Definitions**:
  - `hyperplane_cell`: Defines what it means for a set to be a hyperplane cell with respect to a set of hyperplanes
  - `euler_characteristic`: Definition of the Euler characteristic function

### Porting notes
When porting this theorem:
- Ensure that the affine dimension function (`aff_dim`) is correctly implemented
- The `num_of_int` function converts between numeric types - make sure your target system handles this conversion properly
- The proof relies on rewriting a singleton set as a union, which should be straightforward in most systems

---

## EULER_CHARACTERISTIC_CELLCOMPLEX_UNION

### Name of formal statement
EULER_CHARACTERISTIC_CELLCOMPLEX_UNION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_CHARACTERISTIC_CELLCOMPLEX_UNION = prove
 (`!A s t:real^N->bool.
        FINITE A /\
        hyperplane_cellcomplex A s /\
        hyperplane_cellcomplex A t /\
        DISJOINT s t
        ==> euler_characteristic A (s UNION t) =
            euler_characteristic A s + euler_characteristic A t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[euler_characteristic] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_UNION_EQ THEN
  ASM_SIMP_TAC[FINITE_RESTRICT_HYPERPLANE_CELLS] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY; IN_UNION] THEN
  CONJ_TAC THEN X_GEN_TAC `c:real^N->bool` THENL
   [ASM_CASES_TAC `c:real^N->bool = {}` THENL
     [ASM_MESON_TAC[NONEMPTY_HYPERPLANE_CELL]; ASM SET_TAC[]];
    ASM_CASES_TAC `hyperplane_cell A (c:real^N->bool)` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `A:(real^N#real)->bool` CELL_SUBSET_CELLCOMPLEX) THEN
    ASM_SIMP_TAC[HYPERPLANE_CELLCOMPLEX_UNION] THEN SET_TAC[]]);;
```

### Informal statement
For any set $A$ of hyperplanes and sets $s, t \subseteq \mathbb{R}^N$, if:
- $A$ is finite
- $s$ and $t$ are hyperplane cell complexes with respect to $A$
- $s$ and $t$ are disjoint

Then the Euler characteristic of their union equals the sum of their individual Euler characteristics:
$$\chi_A(s \cup t) = \chi_A(s) + \chi_A(t)$$

where $\chi_A(s)$ is defined as:
$$\chi_A(s) = \sum_{c \subseteq s, \text{ hyperplane cell of } A} (-1)^{\dim(c)}$$

### Informal proof
We need to prove that the Euler characteristic of the union of two disjoint cell complexes equals the sum of their individual Euler characteristics.

First, we expand the definition of Euler characteristic:
$$\chi_A(s \cup t) = \sum_{c \in \{c \mid \text{hyperplane\_cell}(A,c) \land c \subseteq s \cup t\}} (-1)^{\dim(c)}$$

The proof proceeds by showing this sum equals the sum of the Euler characteristics of $s$ and $t$:
$$\sum_{c \in \{c \mid \text{hyperplane\_cell}(A,c) \land c \subseteq s\}} (-1)^{\dim(c)} + \sum_{c \in \{c \mid \text{hyperplane\_cell}(A,c) \land c \subseteq t\}} (-1)^{\dim(c)}$$

We apply the `SUM_UNION_EQ` theorem, which states that for finite sets $P$ and $Q$, if $P \cap Q = \emptyset$, then:
$$\sum_{x \in P \cup Q} f(x) = \sum_{x \in P} f(x) + \sum_{x \in Q} f(x)$$

To apply this theorem, we need to show:
1. The sets $\{c \mid \text{hyperplane\_cell}(A,c) \land c \subseteq s\}$ and $\{c \mid \text{hyperplane\_cell}(A,c) \land c \subseteq t\}$ are finite, which follows from `FINITE_RESTRICT_HYPERPLANE_CELLS` and the assumption that $A$ is finite.
2. These sets are disjoint.

For the disjointness condition, we prove that no hyperplane cell can be a subset of both $s$ and $t$. This follows because:
- If $c$ is a hyperplane cell, then $c$ is nonempty (by `NONEMPTY_HYPERPLANE_CELL`).
- If $c$ is a subset of both $s$ and $t$, then $c$ would have a non-empty intersection with both $s$ and $t$ (using `CELL_SUBSET_CELLCOMPLEX`).
- Since $s$ and $t$ are disjoint, this is impossible.

Therefore, the Euler characteristic of the union equals the sum of the individual Euler characteristics.

### Mathematical insight
This theorem establishes an important property of Euler characteristics: additivity over disjoint unions. This is a fundamental property expected of any topological invariant like the Euler characteristic.

The Euler characteristic is a topological invariant that alternately sums the number of cells of different dimensions in a cell complex. It has numerous applications in algebraic topology, differential geometry, and combinatorics.

This theorem specifically shows that when working with hyperplane cell complexes, the Euler characteristic behaves in the expected manner with respect to disjoint unions. This property is essential for inductive arguments and for computing the Euler characteristic of complex spaces by decomposing them into simpler components.

### Dependencies
#### Theorems
- `NONEMPTY_HYPERPLANE_CELL`: Any hyperplane cell is non-empty.
- `FINITE_RESTRICT_HYPERPLANE_CELLS`: If A is finite, then the set of hyperplane cells of A satisfying a property P is also finite.
- `HYPERPLANE_CELLCOMPLEX_UNION`: The union of two hyperplane cell complexes is also a hyperplane cell complex.
- `CELL_SUBSET_CELLCOMPLEX`: For a hyperplane cell c and a hyperplane cell complex s, c is a subset of s if and only if c has a non-empty intersection with s.
- `SUM_UNION_EQ`: For disjoint finite sets, the sum over their union equals the sum of the individual sums.

#### Definitions
- `hyperplane_cell`: A set c is a hyperplane cell of A if it's the equivalence class of some point under the hyperplane equivalence relation.
- `hyperplane_cellcomplex`: A set s is a hyperplane cell complex of A if it's the union of a collection of hyperplane cells of A.
- `euler_characteristic`: The Euler characteristic of a set s with respect to hyperplanes A is the alternating sum of (-1)^d where d is the dimension of each hyperplane cell contained in s.

### Porting notes
When porting this theorem:
1. Ensure that the definition of hyperplane cells, cell complexes, and Euler characteristic are consistently ported.
2. The proof relies on set-theoretic reasoning about disjoint unions and the properties of hyperplane cells, which should translate well to other proof assistants.
3. The main challenges might be in handling the specific representation of affine dimension and ensuring that the sum over sets of cells is well-defined in the target system.
4. Some systems might need explicit type annotations for the dimension N of the Euclidean space.

---

## EULER_CHARACTERISTIC_CELLCOMPLEX_UNIONS

### EULER_CHARACTERISTIC_CELLCOMPLEX_UNIONS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem 

### Formal Content
```ocaml
let EULER_CHARACTERISTIC_CELLCOMPLEX_UNIONS = prove
 (`!A C. FINITE A /\
         (!c:real^N->bool. c IN C ==> hyperplane_cellcomplex A c) /\
         pairwise DISJOINT C
         ==> euler_characteristic A (UNIONS C) =
             sum C (\c. euler_characteristic A c)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_CASES_TAC `FINITE(C:(real^N->bool)->bool)` THENL
   [UNDISCH_TAC `FINITE(C:(real^N->bool)->bool)`;
    ASM_MESON_TAC[FINITE_SET_OF_HYPERPLANE_CELLS]] THEN
  SPEC_TAC(`C:(real^N->bool)->bool`,`C:(real^N->bool)->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[EULER_CHARACTERISTIC_EMPTY; SUM_CLAUSES; UNIONS_0] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[UNIONS_INSERT] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) EULER_CHARACTERISTIC_CELLCOMPLEX_UNION o
        lhs o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_UNIONS THEN ASM SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pairwise]) THEN
      REWRITE_TAC[DISJOINT; INTER_UNIONS; IMP_CONJ; RIGHT_FORALL_IMP_THM;
                  FORALL_IN_INSERT; EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
      ASM_MESON_TAC[INTER_COMM]];
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pairwise]) THEN
    ASM_REWRITE_TAC[pairwise] THEN ASM SET_TAC[]]);;
```

### Informal statement
For any set of hyperplanes $A$ in $\mathbb{R}^N$ and a collection $C$ of subsets of $\mathbb{R}^N$, if:
1. $A$ is finite
2. Every element $c \in C$ is a hyperplane cellcomplex with respect to $A$
3. The elements of $C$ are pairwise disjoint

Then the Euler characteristic of the union of all sets in $C$ equals the sum of Euler characteristics of individual sets:

$$\chi_A(\bigcup_{c \in C} c) = \sum_{c \in C} \chi_A(c)$$

where $\chi_A$ denotes the Euler characteristic with respect to the hyperplane arrangement $A$.

### Informal proof

We proceed by strong induction on the finite set $C$.

First, we verify that $C$ is finite: this follows from `FINITE_SET_OF_HYPERPLANE_CELLS` since $A$ is finite and each element of $C$ is a hyperplane cellcomplex with respect to $A$.

The base case is when $C = \emptyset$:
- By `EULER_CHARACTERISTIC_EMPTY`, we have $\chi_A(\emptyset) = 0$
- Also, $\sum_{c \in \emptyset} \chi_A(c) = 0$
- And $\bigcup_{c \in \emptyset} c = \emptyset$
- Therefore, $\chi_A(\bigcup_{c \in \emptyset} c) = \chi_A(\emptyset) = 0 = \sum_{c \in \emptyset} \chi_A(c)$

For the inductive step, suppose the statement holds for some finite set $C_0$. We need to show it holds for $C = C_0 \cup \{x\}$ where $x \not\in C_0$.

We have:
- $\bigcup_{c \in C} c = x \cup (\bigcup_{c \in C_0} c)$

Now we apply `EULER_CHARACTERISTIC_CELLCOMPLEX_UNION` to compute $\chi_A(x \cup (\bigcup_{c \in C_0} c))$. This requires verifying several conditions:
1. $A$ is finite (given)
2. $x$ is a hyperplane cellcomplex with respect to $A$ (given)
3. $\bigcup_{c \in C_0} c$ is a hyperplane cellcomplex with respect to $A$ (follows from `HYPERPLANE_CELLCOMPLEX_UNIONS`)
4. $x$ and $\bigcup_{c \in C_0} c$ are disjoint (follows from the pairwise disjointness of $C$)

Therefore:
$$\chi_A(x \cup (\bigcup_{c \in C_0} c)) = \chi_A(x) + \chi_A(\bigcup_{c \in C_0} c)$$

By the induction hypothesis:
$$\chi_A(\bigcup_{c \in C_0} c) = \sum_{c \in C_0} \chi_A(c)$$

Therefore:
$$\chi_A(\bigcup_{c \in C} c) = \chi_A(x) + \sum_{c \in C_0} \chi_A(c) = \sum_{c \in C} \chi_A(c)$$

This completes the proof.

### Mathematical insight
This theorem extends the additive property of the Euler characteristic to countable unions of pairwise disjoint cellcomplexes. The Euler characteristic is an important topological invariant that generalizes the familiar formula $V - E + F$ for polyhedra to higher dimensions.

The additivity property of the Euler characteristic is fundamental in combinatorial topology and geometry. This result shows that when decomposing a space into disjoint cellcomplexes, we can compute the overall Euler characteristic by simply adding the Euler characteristics of the individual components. This provides a powerful computational tool for analyzing complex geometric structures by breaking them down into simpler parts.

### Dependencies
- Definitions:
  - `hyperplane_cellcomplex` - Defines a set as a union of hyperplane cells
  - `euler_characteristic` - The Euler characteristic of a set with respect to a hyperplane arrangement
  
- Theorems:
  - `FINITE_SET_OF_HYPERPLANE_CELLS` - Shows that a collection of hyperplane cellcomplexes is finite
  - `HYPERPLANE_CELLCOMPLEX_UNIONS` - Shows that the union of hyperplane cellcomplexes is a hyperplane cellcomplex
  - `EULER_CHARACTERISTIC_EMPTY` - The Euler characteristic of the empty set is zero
  - `EULER_CHARACTERISTIC_CELLCOMPLEX_UNION` - Additivity of Euler characteristic for the union of two disjoint cellcomplexes

### Porting notes
When porting this theorem:
1. Ensure that the concept of hyperplane cells and cellcomplexes is properly defined in the target system
2. Pay attention to how finite sums and unions over collections are handled
3. Be aware that the strong induction principle used in the proof might require explicit formulation in some systems
4. The definition of the Euler characteristic using alternating sums over cells of different dimensions might need careful formulation in other systems

---

## EULER_CHARACTERISTIC

### Name of formal statement
EULER_CHARACTERISTIC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_CHARACTERISTIC = prove
 (`!A s:real^N->bool.
        FINITE A
        ==> euler_characteristic A s =
            sum (0..dimindex(:N))
                (\d. (-- &1) pow d *
                     &(CARD {c | hyperplane_cell A c /\ c SUBSET s /\
                                 aff_dim c = &d}))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[euler_characteristic] THEN
  MP_TAC(ISPECL [`\c:real^N->bool. aff_dim c`;
                 `\c:real^N->bool. (-- &1) pow (num_of_int(aff_dim c))`;
                 `{c:real^N->bool | hyperplane_cell A c /\ c SUBSET s}`;
                 `IMAGE int_of_num (0..dimindex(:N))`]
                SUM_GROUP) THEN
  SIMP_TAC[SUM_IMAGE; INT_OF_NUM_EQ; o_DEF; NUM_OF_INT_OF_NUM] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_RESTRICT_HYPERPLANE_CELLS] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `c:real^N->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[IN_IMAGE; IN_NUMSEG; LE_0] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE; INT_EXISTS_POS] THEN
    EXISTS_TAC `aff_dim(c:real^N->bool)` THEN
    REWRITE_TAC[AFF_DIM_LE_UNIV; AFF_DIM_POS_LE] THEN
    ASM_MESON_TAC[NONEMPTY_HYPERPLANE_CELL];
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC] THEN
    ASM_SIMP_TAC[SUM_CONST; FINITE_RESTRICT_HYPERPLANE_CELLS] THEN
    REWRITE_TAC[REAL_MUL_AC]]);;
```

### Informal statement
For any finite set $A$ of hyperplanes in $\mathbb{R}^N$ and any subset $s \subseteq \mathbb{R}^N$, the Euler characteristic of $s$ with respect to $A$ can be expressed as:

$$\text{euler\_characteristic}(A, s) = \sum_{d=0}^N (-1)^d \cdot |\{c \mid c \text{ is a hyperplane cell of } A \text{ and } c \subseteq s \text{ and } \text{aff\_dim}(c) = d\}|$$

where $\text{aff\_dim}(c)$ denotes the affine dimension of the cell $c$.

### Informal proof
The theorem provides an alternative formulation of the Euler characteristic in terms of a sum over dimensions rather than a direct sum over cells.

The proof proceeds as follows:

- Start with the definition of `euler_characteristic A s` as the sum over all hyperplane cells $c$ of $A$ that are subsets of $s$, where each cell contributes $(-1)^{\text{num\_of\_int}(\text{aff\_dim}(c))}$.

- Apply the `SUM_GROUP` theorem to group the cells by their affine dimension. This theorem allows us to rewrite a sum over a set as grouped by some function (in this case, the affine dimension).

- For the application of `SUM_GROUP`, we use:
  * The grouping function: $c \mapsto \text{aff\_dim}(c)$
  * The summand function: $c \mapsto (-1)^{\text{num\_of\_int}(\text{aff\_dim}(c))}$
  * The domain set: $\{c \mid \text{hyperplane\_cell}(A, c) \wedge c \subseteq s\}$
  * The range set for grouping: $\{\text{int\_of\_num}(d) \mid d \in \{0,\ldots,N\}\}$

- Verify the assumptions required by `SUM_GROUP`:
  * The domain set is finite (by `FINITE_RESTRICT_HYPERPLANE_CELLS`)
  * Each element in the domain maps to an element in the range set. This is shown by proving:
    1. The affine dimension of any cell is at most the dimension of the space (using `AFF_DIM_LE_UNIV`)
    2. The affine dimension is non-negative for non-empty cells (using `AFF_DIM_POS_LE`)
    3. All hyperplane cells are non-empty (using `NONEMPTY_HYPERPLANE_CELL`)

- After applying `SUM_GROUP`, we get a sum over the range set (dimensions), where each dimension $d$ contributes $(-1)^d$ multiplied by the number of cells of that dimension.

- Simplify using `SUM_CONST` and arrive at the desired formula.

### Mathematical insight
This theorem provides a more structured way to compute the Euler characteristic by grouping cells by their dimension. The Euler characteristic is a topological invariant that generalizes the notion of the alternating sum of the number of simplices of each dimension in a simplicial complex.

The formula expresses the Euler characteristic as an alternating sum of cell counts by dimension, which is a common formulation in topology. This perspective makes it easier to analyze and compute the Euler characteristic in practice, especially for complex arrangements of hyperplanes.

The result connects the combinatorial structure of hyperplane arrangements (cell counts by dimension) with the topological property (Euler characteristic), making it valuable for both computational and theoretical purposes.

### Dependencies
- **Theorems**:
  - `NONEMPTY_HYPERPLANE_CELL`: Every hyperplane cell is non-empty.
  - `FINITE_RESTRICT_HYPERPLANE_CELLS`: For a finite set of hyperplanes, the collection of hyperplane cells satisfying a given property is finite.
  - `SUM_GROUP` (used but not in dependency list): A theorem for grouping elements in a sum.
  - `AFF_DIM_LE_UNIV` (used but not in dependency list): The affine dimension of any set is at most the dimension of the space.
  - `AFF_DIM_POS_LE` (used but not in dependency list): The affine dimension is non-negative for non-empty sets.

- **Definitions**:
  - `hyperplane_cell`: A cell defined by a hyperplane equivalence relation.
  - `euler_characteristic`: The sum over cells, where each cell contributes $(-1)^{\text{dim}}$ to the sum.

### Porting notes
When porting this theorem:
1. Ensure that the affine dimension function in your target system matches HOL Light's definition.
2. Be aware of how hyperplane cells are represented in your target system.
3. The proof relies on `SUM_GROUP` which groups summands by a function - make sure a similar theorem or approach exists in your target system.
4. The proof uses several theorems about properties of affine dimensions and hyperplane cells which would need to be ported first.

---

## HYPERPLANE_CELLS_DISTINCT_LEMMA

### HYPERPLANE_CELLS_DISTINCT_LEMMA
- HYPERPLANE_CELLS_DISTINCT_LEMMA

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let HYPERPLANE_CELLS_DISTINCT_LEMMA = prove
 (`!a b. {x | a dot x = b} INTER {x | a dot x < b} = {} /\
         {x | a dot x = b} INTER {x | a dot x > b} = {} /\
         {x | a dot x < b} INTER {x | a dot x = b} = {} /\
         {x | a dot x < b} INTER {x | a dot x > b} = {} /\
         {x | a dot x > b} INTER {x | a dot x = b} = {} /\
         {x | a dot x > b} INTER {x | a dot x < b} = {}`,
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  REAL_ARITH_TAC);;
```

### Informal statement
For any vectors $a$ and scalar $b$, the following set intersections are all empty:
- $\{x \mid a \cdot x = b\} \cap \{x \mid a \cdot x < b\} = \emptyset$
- $\{x \mid a \cdot x = b\} \cap \{x \mid a \cdot x > b\} = \emptyset$
- $\{x \mid a \cdot x < b\} \cap \{x \mid a \cdot x = b\} = \emptyset$
- $\{x \mid a \cdot x < b\} \cap \{x \mid a \cdot x > b\} = \emptyset$
- $\{x \mid a \cdot x > b\} \cap \{x \mid a \cdot x = b\} = \emptyset$
- $\{x \mid a \cdot x > b\} \cap \{x \mid a \cdot x < b\} = \emptyset$

Where $a \cdot x$ represents the dot product of vectors $a$ and $x$.

### Informal proof
This theorem shows that the sets determined by the regions defined by a hyperplane $a \cdot x = b$ are disjoint. The proof is straightforward:

- We first use `EXTENSION` to prove set equality by showing that the elements of both sets are the same.
- We then use `IN_INTER` and `IN_ELIM_THM` to unfold the definitions of set intersection and set membership.
- Finally, we use `NOT_IN_EMPTY` to show that no element can be in the empty set.
- `REAL_ARITH_TAC` automatically handles the arithmetic reasoning, as the statements involve mutually exclusive conditions. For example, it's impossible for a value to simultaneously satisfy $a \cdot x = b$ and $a \cdot x < b$.

### Mathematical insight
This lemma establishes the fundamental property that a hyperplane $a \cdot x = b$ divides the space into three disjoint regions: points on the hyperplane ($a \cdot x = b$), points on one side of the hyperplane ($a \cdot x < b$), and points on the other side ($a \cdot x > b$).

This is important in the context of hyperplane arrangements, as it confirms that the cells defined by these hyperplanes have well-defined boundaries and are properly separated. The theorem forms the foundation for analyzing the topology and combinatorial properties of arrangements of hyperplanes in Euclidean space.

As noted in the comment, this result is used to show that the characteristic of a space is invariant with respect to hyperplane arrangements, which is crucial in various geometric and topological applications.

### Dependencies
- `EXTENSION`: Theorem establishing that two sets are equal if they have the same elements
- `IN_INTER`: Theorem describing membership in the intersection of sets
- `IN_ELIM_THM`: Theorem for simplifying set comprehension membership
- `NOT_IN_EMPTY`: Theorem stating that no element belongs to the empty set
- `REAL_ARITH_TAC`: Tactic for solving real arithmetic problems

### Porting notes
When porting this theorem:
- The proof is quite straightforward and should work similarly in other systems with good arithmetic automation.
- Ensure the target system has good support for set comprehension notation and real arithmetic reasoning.
- In systems with less powerful arithmetic automation than HOL Light's `REAL_ARITH_TAC`, you might need to manually prove the mutually exclusive nature of the conditions.

---

## EULER_CHARACTERSTIC_LEMMA

### Name of formal statement
EULER_CHARACTERSTIC_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_CHARACTERSTIC_LEMMA = prove
 (`!A h s:real^N->bool.
        FINITE A /\ hyperplane_cellcomplex A s
        ==> euler_characteristic (h INSERT A) s = euler_characteristic A s`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN MAP_EVERY X_GEN_TAC
   [`A:(real^N#real)->bool`; `a:real^N`; `b:real`; `s:real^N->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[hyperplane_cellcomplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN
   `!c:real^N->bool. c IN C ==> hyperplane_cellcomplex A c /\
                                hyperplane_cellcomplex ((a,b) INSERT A) c`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[HYPERPLANE_CELL_CELLCOMPLEX] THEN
    MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_MONO THEN
    EXISTS_TAC `A:(real^N#real)->bool` THEN
    ASM_SIMP_TAC[HYPERPLANE_CELL_CELLCOMPLEX] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pairwise DISJOINT (C:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PAIRWISE_DISJOINT_HYPERPLANE_CELLS]; ALL_TAC] THEN
  ASM_SIMP_TAC[EULER_CHARACTERISTIC_CELLCOMPLEX_UNIONS; FINITE_INSERT] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `c:real^N->bool` THEN DISCH_TAC THEN
  ASM_CASES_TAC `hyperplane_cell ((a,b) INSERT A) (c:real^N->bool)` THEN
  ASM_SIMP_TAC[EULER_CHARACTERISTIC_CELL] THEN
  SUBGOAL_THEN `~(a:real^N = vec 0)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    SIMP_TAC[CONTRAPOS_THM] THEN DISCH_THEN(K ALL_TAC) THEN
    ONCE_REWRITE_TAC[SET_RULE `x INSERT s = {x} UNION s`] THEN
    REWRITE_TAC[HYPERPLANE_CELL_UNION] THEN
    REWRITE_TAC[HYPERPLANE_CELL_SING; RIGHT_EXISTS_AND_THM; UNWIND_THM2] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[NONEMPTY_HYPERPLANE_CELL]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[INTER_UNIV; UNWIND_THM1] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[euler_characteristic] THEN
  ONCE_REWRITE_TAC[SET_RULE `x INSERT s = {x} UNION s`] THEN
  REWRITE_TAC[HYPERPLANE_CELL_UNION] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum {c' INTER c |c'| hyperplane_cell {(a,b)} c' /\ ~(c' INTER c = {})}
        (\c:real^N->bool. (-- &1) pow (num_of_int(aff_dim c)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(MESON[] `s = t ==> sum s f = sum t f`) THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `c':real^N->bool` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c1:real^N->bool` THEN
      DISCH_THEN(X_CHOOSE_THEN `c2:real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `~(DISJOINT c2 (c:real^N->bool))` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_MESON_TAC[DISJOINT_HYPERPLANE_CELLS_EQ]];
      DISCH_THEN(X_CHOOSE_THEN `c1:real^N->bool` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[INTER_SUBSET] THEN
      MAP_EVERY EXISTS_TAC [`c1:real^N->bool`; `c:real^N->bool`] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[HYPERPLANE_CELL_SING] THEN
  SUBGOAL_THEN `~(c:real^N->bool = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[NONEMPTY_HYPERPLANE_CELL]; ALL_TAC] THEN
  MAP_EVERY (fun t ->
   ASM_CASES_TAC t THENL
    [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
      `sum {c} (\c:real^N->bool. (-- &1) pow num_of_int (aff_dim c))` THEN
     CONJ_TAC THENL [ALL_TAC; SIMP_TAC[SUM_SING]] THEN
     MATCH_MP_TAC(MESON[] `s = t ==> sum s f = sum t f`) THEN
     GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `c':real^N->bool` THEN
     REWRITE_TAC[IN_SING; IN_ELIM_THM] THEN
     REWRITE_TAC[TAUT `(a \/ b) /\ c <=> a /\ c \/ b /\ c`] THEN
     REWRITE_TAC[EXISTS_OR_THM; UNWIND_THM2; GSYM CONJ_ASSOC] THEN
     EQ_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
     MP_TAC(ISPECL [`a:real^N`; `b:real`] HYPERPLANE_CELLS_DISTINCT_LEMMA) THEN
     ASM SET_TAC[];
     ALL_TAC])
   [`c SUBSET {x:real^N | a dot x < b}`;
    `c SUBSET {x:real^N | a dot x > b}`;
    `c SUBSET {x:real^N | a dot x = b}`] THEN
  SUBGOAL_THEN `~(c INTER {x:real^N | a dot x = b} = {})` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `?u v:real^N. u IN c /\ ~(a dot u < b) /\ v IN c /\ ~(a dot v > b)`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[real_gt; REAL_NOT_LT; GSYM MEMBER_NOT_EMPTY] THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN SIMP_TAC[REAL_LE_LT] THEN
    ASM_CASES_TAC `(a:real^N) dot u = b` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `(a:real^N) dot v = b` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `v + (b - a dot v) / (a dot u - a dot v) % (u - v):real^N` THEN
    SUBGOAL_THEN `(a:real^N) dot v < a dot u` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[DOT_RADD; DOT_RMUL; DOT_RSUB; REAL_DIV_RMUL; REAL_SUB_LT;
                 REAL_LT_IMP_NZ; REAL_SUB_ADD2] THEN
    REWRITE_TAC[VECTOR_ARITH
     `v + a % (u - v):real^N = (&1 - a) % v + a % u`] THEN
    MATCH_MP_TAC IN_CONVEX_SET THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_SUB_LT] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    ASM_MESON_TAC[HYPERPLANE_CELL_CONVEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(c INTER {x:real^N | a dot x < b} = {}) /\
                ~(c INTER {x:real^N | a dot x > b} = {})`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `?u v:real^N.
         u IN c /\ a dot u = b /\ v IN c /\ ~(a dot v = b) /\ ~(u = v)`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `open_in (subtopology euclidean (affine hull c)) (c:real^N->bool)`
    MP_TAC THENL [ASM_MESON_TAC[HYPERPLANE_CELL_RELATIVELY_OPEN]; ALL_TAC] THEN
    REWRITE_TAC[open_in] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `u:real^N`)) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `e:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (MP_TAC o SPEC `u - e / &2 / norm(v - u) % (v - u):real^N`)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[NORM_ARITH `dist(u - a:real^N,u) = norm a`] THEN
      REWRITE_TAC[VECTOR_ARITH `x - a % (y - z):real^N = x + a % (z - y)`] THEN
      REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NUM; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_EQ_0; VECTOR_SUB_EQ] THEN
      ASM_REWRITE_TAC[REAL_ARITH `abs e / &2 < e <=> &0 < e`] THEN
      MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN
      ASM_SIMP_TAC[AFFINE_AFFINE_HULL; HULL_INC];
      DISCH_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
    SUBGOAL_THEN `(a:real^N) dot v < b \/ a dot v > b` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC;
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `u - e / &2 / norm(v - u) % (v - u):real^N` THEN
      ASM_REWRITE_TAC[DOT_RSUB; DOT_RMUL] THEN
      REWRITE_TAC[REAL_ARITH `b - x * y > b <=> &0 < x * --y`] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF; NORM_POS_LT; VECTOR_SUB_EQ] THEN
      ASM_REAL_ARITH_TAC;
      CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]]] THEN
    EXISTS_TAC `u - e / &2 / norm(v - u) % (v - u):real^N` THEN
    ASM_REWRITE_TAC[DOT_RSUB; DOT_RMUL] THEN
    REWRITE_TAC[REAL_ARITH `b - x * y > b <=> &0 < x * --y`;
                REAL_ARITH `b - x < b <=> &0 < x`] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF; NORM_POS_LT; VECTOR_SUB_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `sum {{x | a dot x = b} INTER c,
         {x | a dot x > b} INTER c,
         {x | a dot x < b} INTER c}
        (\c:real^N->bool. (-- &1) pow (num_of_int(aff_dim c)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(MESON[] `s = t ==> sum s f = sum t f`) THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `c':real^N->bool` THEN
    REWRITE_TAC[TAUT `(a \/ b) /\ c <=> a /\ c \/ b /\ c`] THEN
    REWRITE_TAC[EXISTS_OR_THM; UNWIND_THM2; GSYM CONJ_ASSOC] THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  SIMP_TAC[SUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY;
           IN_INSERT; NOT_IN_EMPTY] THEN
  ONCE_REWRITE_TAC[INTER_COMM] THEN
  ASM_SIMP_TAC[HYPERPLANE_CELLS_DISTINCT_LEMMA; REAL_ADD_RID; SET_RULE
   `s INTER t = {} /\ ~(c INTER s = {}) ==> ~(c INTER s = c INTER t)`] THEN
  SUBGOAL_THEN
   `aff_dim (c INTER {x:real^N | a dot x < b}) = aff_dim c /\
    aff_dim (c INTER {x:real^N | a dot x > b}) = aff_dim c`
   (CONJUNCTS_THEN SUBST1_TAC)
  THENL
   [ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN CONJ_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC AFFINE_HULL_CONVEX_INTER_OPEN THEN
    ASM_REWRITE_TAC[OPEN_HALFSPACE_LT; OPEN_HALFSPACE_GT] THEN
    ASM_MESON_TAC[HYPERPLANE_CELL_CONVEX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `aff_dim c = aff_dim(c INTER {x:real^N | a dot x = b}) + &1`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`A:real^N#real->bool`; `c:real^N->bool`]
        HYPERPLANE_CELL_INTER_OPEN_AFFINE) THEN
    ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `t:real^N->bool`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
    SUBGOAL_THEN
     `affine hull (s INTER t) = affine hull t /\
      affine hull ((s INTER t) INTER {x:real^N | a dot x = b}) =
      affine hull (t INTER {x:real^N | a dot x = b})`
     (CONJUNCTS_THEN SUBST1_TAC)
    THENL
     [REWRITE_TAC[INTER_ASSOC] THEN CONJ_TAC THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [INTER_COMM] THEN
      MATCH_MP_TAC AFFINE_HULL_CONVEX_INTER_OPEN THEN
      ASM_SIMP_TAC[CONVEX_INTER; CONVEX_HYPERPLANE; AFFINE_IMP_CONVEX] THEN
      ASM SET_TAC[];
      REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN
      ASM_SIMP_TAC[AFF_DIM_AFFINE_INTER_HYPERPLANE] THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[INT_SUB_ADD]) THEN
      ASM SET_TAC[]];
    SUBGOAL_THEN `&0 <= aff_dim (c INTER {x:real^N | a dot x = b})` MP_TAC
    THENL [REWRITE_TAC[AFF_DIM_POS_LE] THEN ASM SET_TAC[]; ALL_TAC] THEN
    SPEC_TAC(`aff_dim (c INTER {x:real^N | a dot x = b})`,`i:int`) THEN
    REWRITE_TAC[GSYM INT_FORALL_POS] THEN
    REWRITE_TAC[NUM_OF_INT_OF_NUM; INT_OF_NUM_ADD] THEN
    REWRITE_TAC[REAL_POW_ADD] THEN REAL_ARITH_TAC]);;
```

### Informal statement
For any finite set of hyperplanes $A$, vector $a \in \mathbb{R}^N$, scalar $b \in \mathbb{R}$, and set $s \subseteq \mathbb{R}^N$, if $s$ is a hyperplane cell complex with respect to $A$, then the Euler characteristic of $s$ with respect to $A \cup \{(a,b)\}$ equals the Euler characteristic of $s$ with respect to $A$:

$$\forall A, (a,b), s \subseteq \mathbb{R}^N. \text{Finite}(A) \land \text{hyperplane\_cellcomplex}(A, s) \Rightarrow \text{euler\_characteristic}((a,b) \cup A, s) = \text{euler\_characteristic}(A, s)$$

### Informal proof
We need to show that adding a hyperplane to a hyperplane arrangement does not change the Euler characteristic of a cell complex in that arrangement.

* First, we rewrite the problem by representing the hyperplane cell complex $s$ as a union of hyperplane cells: $s = \bigcup C$, where each $c \in C$ is a hyperplane cell with respect to $A$.

* We establish two important facts:
  1. For each cell $c \in C$, $c$ is a hyperplane cell complex with respect to both $A$ and $A \cup \{(a,b)\}$
  2. The cells in $C$ are pairwise disjoint

* By the formula for Euler characteristic of a union of cell complexes, we have:
  $$\text{euler\_characteristic}(A, \bigcup C) = \sum_{c \in C} \text{euler\_characteristic}(A, c)$$
  and
  $$\text{euler\_characteristic}(A \cup \{(a,b)\}, \bigcup C) = \sum_{c \in C} \text{euler\_characteristic}(A \cup \{(a,b)\}, c)$$

* We need to show that for each cell $c \in C$, $\text{euler\_characteristic}(A \cup \{(a,b)\}, c) = \text{euler\_characteristic}(A, c)$

* We handle a special case: if $a = \vec{0}$, then the hyperplane $(a,b)$ doesn't divide any cell, so the result is trivial.

* Assuming $a \neq \vec{0}$, we analyze how the hyperplane $(a,b)$ intersects each cell $c$.

* We show that each hyperplane cell $c$ is intersected by the hyperplane $\{x : a \cdot x = b\}$, dividing it into three parts:
  - $c \cap \{x : a \cdot x = b\}$ (intersection with the hyperplane)
  - $c \cap \{x : a \cdot x < b\}$ (points below the hyperplane)
  - $c \cap \{x : a \cdot x > b\}$ (points above the hyperplane)

* For the two open half-spaces, we prove that:
  $$\text{aff\_dim}(c \cap \{x : a \cdot x < b\}) = \text{aff\_dim}(c \cap \{x : a \cdot x > b\}) = \text{aff\_dim}(c)$$
  
* For the hyperplane intersection, we establish:
  $$\text{aff\_dim}(c) = \text{aff\_dim}(c \cap \{x : a \cdot x = b\}) + 1$$

* Using the formula that each cell contributes $(-1)^{\text{aff\_dim}(c)}$ to the Euler characteristic, we get:
  $$\text{euler\_characteristic}(A \cup \{(a,b)\}, c) = (-1)^{\text{aff\_dim}(c \cap \{x : a \cdot x = b\})} + (-1)^{\text{aff\_dim}(c)} + (-1)^{\text{aff\_dim}(c)}$$

* Since $\text{aff\_dim}(c) = \text{aff\_dim}(c \cap \{x : a \cdot x = b\}) + 1$, we have $(-1)^{\text{aff\_dim}(c)} = -(-1)^{\text{aff\_dim}(c \cap \{x : a \cdot x = b\})}$

* Therefore:
  $$\text{euler\_characteristic}(A \cup \{(a,b)\}, c) = (-1)^{\text{aff\_dim}(c \cap \{x : a \cdot x = b\})} - (-1)^{\text{aff\_dim}(c \cap \{x : a \cdot x = b\})} + (-1)^{\text{aff\_dim}(c)} = (-1)^{\text{aff\_dim}(c)}$$

* This equals $\text{euler\_characteristic}(A, c)$, completing the proof.

### Mathematical insight
This lemma demonstrates a fundamental invariance property of the Euler characteristic in hyperplane arrangements. It shows that the Euler characteristic is independent of the specific hyperplanes used to define the cell complex, as long as the cell complex itself remains fixed. 

This result is crucial for establishing the topological properties of arrangements of hyperplanes and is related to the classical Euler characteristic in algebraic topology. It allows us to compute the Euler characteristic incrementally by adding hyperplanes one at a time without changing the final result.

The key insight is that when a new hyperplane intersects an existing cell, it divides it into pieces whose contributions to the Euler characteristic exactly balance out, preserving the original value. This reflects the deeper topological invariance of the Euler characteristic.

### Dependencies
- **Definitions**:
  - `hyperplane_cell`: Defines a cell in a hyperplane arrangement
  - `hyperplane_cellcomplex`: Defines a cell complex formed by hyperplane cells
  - `euler_characteristic`: Defines the Euler characteristic of a set with respect to a hyperplane arrangement

- **Theorems**:
  - `NONEMPTY_HYPERPLANE_CELL`: Hyperplane cells are non-empty
  - `DISJOINT_HYPERPLANE_CELLS_EQ`: Two hyperplane cells are disjoint iff they are not equal
  - `HYPERPLANE_CELL_SING`: Characterizes cells formed by a single hyperplane
  - `HYPERPLANE_CELL_UNION`: Characterizes cells formed by a union of hyperplane arrangements
  - `PAIRWISE_DISJOINT_HYPERPLANE_CELLS`: Hyperplane cells are pairwise disjoint
  - `HYPERPLANE_CELL_INTER_OPEN_AFFINE`: A hyperplane cell is the intersection of an open set and an affine set
  - `HYPERPLANE_CELL_RELATIVELY_OPEN`: A hyperplane cell is relatively open in its affine hull
  - `HYPERPLANE_CELL_CONVEX`: Hyperplane cells are convex
  - `HYPERPLANE_CELL_CELLCOMPLEX`: A hyperplane cell is also a cell complex
  - `HYPERPLANE_CELLCOMPLEX_MONO`: Cell complex property is monotone with respect to hyperplane sets
  - `EULER_CHARACTERISTIC_CELL`: Formula for the Euler characteristic of a cell
  - `EULER_CHARACTERISTIC_CELLCOMPLEX_UNIONS`: Euler characteristic of a union of cell complexes
  - `HYPERPLANE_CELLS_DISTINCT_LEMMA`: Cells formed by different sides of a hyperplane are disjoint

### Porting notes
When porting this theorem:
1. First ensure the underlying definitions of hyperplane cells, cell complexes, and Euler characteristic are correctly implemented
2. Be careful with the handling of affine dimension, as this varies across proof assistants
3. The proof relies on convexity properties and the relationship between affine dimension when intersecting with hyperplanes - these properties may need separate verification in other systems
4. The combinatorial aspect of the proof may benefit from specialized libraries for combinatorics or algebraic topology in the target system

---

## EULER_CHARACTERSTIC_INVARIANT

### Name of formal statement
EULER_CHARACTERSTIC_INVARIANT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_CHARACTERSTIC_INVARIANT = prove
 (`!A B h s:real^N->bool.
        FINITE A /\ FINITE B /\
        hyperplane_cellcomplex A s /\ hyperplane_cellcomplex B s
        ==> euler_characteristic A s = euler_characteristic B s`,
  SUBGOAL_THEN
   `!A s:real^N->bool.
        FINITE A /\ hyperplane_cellcomplex A s
        ==> !B. FINITE B
                ==> euler_characteristic (A UNION B) s =
                    euler_characteristic A s`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN ASM_REWRITE_TAC[UNION_EMPTY] THEN
    MAP_EVERY X_GEN_TAC [`h:real^N#real`; `B:real^N#real->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[SET_RULE `s UNION (x INSERT t) = x INSERT (s UNION t)`] THEN
    MATCH_MP_TAC EULER_CHARACTERSTIC_LEMMA THEN
    ASM_REWRITE_TAC[FINITE_UNION] THEN
    MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_MONO THEN
    EXISTS_TAC `A:real^N#real->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]) THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `euler_characteristic (A UNION B) (s:real^N->bool)` THEN
    ASM_MESON_TAC[UNION_COMM]]);;
```

### Informal statement
For any finite sets $A$ and $B$ of hyperplanes in $\mathbb{R}^N$ and any set $s \subseteq \mathbb{R}^N$, if both $A$ and $B$ form hyperplane cellcomplexes of $s$, then the Euler characteristic of $s$ with respect to $A$ equals the Euler characteristic of $s$ with respect to $B$.

In mathematical notation:
$$\forall A, B, s \subset \mathbb{R}^N. \text{FINITE}(A) \wedge \text{FINITE}(B) \wedge \text{hyperplane_cellcomplex}(A, s) \wedge \text{hyperplane_cellcomplex}(B, s) \Rightarrow \text{euler_characteristic}(A, s) = \text{euler_characteristic}(B, s)$$

### Informal proof
The proof proceeds by establishing a more general lemma first, and then applying it to prove the main theorem.

The key lemma (proved within the main proof) states:
$$\forall A, s \subset \mathbb{R}^N. \text{FINITE}(A) \wedge \text{hyperplane_cellcomplex}(A, s) \Rightarrow \forall B. \text{FINITE}(B) \Rightarrow \text{euler_characteristic}(A \cup B, s) = \text{euler_characteristic}(A, s)$$

To prove this lemma:
* We use induction on set $B$.
* Base case: When $B$ is empty, $A \cup B = A$, so $\text{euler_characteristic}(A \cup \emptyset, s) = \text{euler_characteristic}(A, s)$.
* Inductive step: For any hyperplane $h$ and set $B$ such that $h \notin B$, we assume 
  $\text{euler_characteristic}(A \cup B, s) = \text{euler_characteristic}(A, s)$.
  * We need to show $\text{euler_characteristic}(A \cup (h \cup B), s) = \text{euler_characteristic}(A, s)$.
  * This can be rewritten as $\text{euler_characteristic}(h \cup (A \cup B), s) = \text{euler_characteristic}(A, s)$.
  * By the previous theorem `EULER_CHARACTERSTIC_LEMMA`, we know that inserting a single hyperplane doesn't change the Euler characteristic: 
    $\text{euler_characteristic}(h \cup C, s) = \text{euler_characteristic}(C, s)$ for any finite set $C$ where $\text{hyperplane_cellcomplex}(C, s)$.
  * We apply this with $C = A \cup B$, noting that $A \cup B$ is finite and forms a hyperplane cellcomplex of $s$ 
    (by `HYPERPLANE_CELLCOMPLEX_MONO` since $A \subseteq A \cup B$ and $A$ forms a hyperplane cellcomplex of $s$).

Once the lemma is established, the main theorem is proved:
* For any finite sets $A$ and $B$ forming hyperplane cellcomplexes of $s$:
  * By our lemma, $\text{euler_characteristic}(A \cup B, s) = \text{euler_characteristic}(A, s)$
  * By the same lemma with $A$ and $B$ swapped, $\text{euler_characteristic}(B \cup A, s) = \text{euler_characteristic}(B, s)$
  * Since $A \cup B = B \cup A$, we have $\text{euler_characteristic}(A, s) = \text{euler_characteristic}(B, s)$

### Mathematical insight
This theorem establishes the invariance of the Euler characteristic with respect to different hyperplane decompositions of the same set. This is a fundamental result because:

1. It shows that the Euler characteristic is well-defined and doesn't depend on the particular choice of hyperplanes used to decompose a set.

2. This invariance property is essential for using the Euler characteristic as a topological invariant, allowing it to characterize properties of spaces regardless of how they are partitioned.

3. The result connects to the classical Euler formula for polyhedra (V-E+F=2 for convex polyhedra), showing that this relationship holds regardless of how the polyhedron is subdivided.

4. In algebraic topology, this invariance property allows the Euler characteristic to serve as a bridge between combinatorial and topological properties of spaces.

### Dependencies
- Theorems:
  - `HYPERPLANE_CELLCOMPLEX_MONO`: Shows that if a set of hyperplanes forms a cellcomplex for a set, then any superset of those hyperplanes also forms a cellcomplex for the set.
  - `EULER_CHARACTERSTIC_LEMMA`: Shows that adding a single hyperplane to a set of hyperplanes doesn't change the Euler characteristic.
  
- Definitions:
  - `hyperplane_cellcomplex`: Defines when a set of hyperplanes forms a cellcomplex of a space.
  - `euler_characteristic`: Defines the Euler characteristic of a set with respect to a collection of hyperplanes.

### Porting notes
When porting this theorem:
1. Make sure the underlying definitions of hyperplane cellcomplexes and Euler characteristic are compatible with the target system.
2. The proof relies on strong induction over finite sets, which might be implemented differently in various systems.
3. The proof requires careful handling of set operations and equalities, particularly around union and insertion operations.
4. Some proof assistants may have better automation for set theory reasoning, which could simplify parts of this proof.

---

## EULER_CHARACTERISTIC_INCLUSION_EXCLUSION

### Name of formal statement
EULER_CHARACTERISTIC_INCLUSION_EXCLUSION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_CHARACTERISTIC_INCLUSION_EXCLUSION = prove
 (`!A s:(real^N->bool)->bool.
        FINITE A /\ FINITE s /\ (!k. k IN s ==> hyperplane_cellcomplex A k)
        ==> euler_characteristic A (UNIONS s) =
            sum {t | t SUBSET s /\ ~(t = {})}
                (\t. (-- &1) pow (CARD t + 1) *
                     euler_characteristic A (INTERS t))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`hyperplane_cellcomplex A :(real^N->bool)->bool`;
    `euler_characteristic A :(real^N->bool)->real`;
    `s:(real^N->bool)->bool`]
        INCLUSION_EXCLUSION_REAL_RESTRICTED) THEN
  ASM_SIMP_TAC[EULER_CHARACTERISTIC_CELLCOMPLEX_UNION] THEN
  SIMP_TAC[HYPERPLANE_CELLCOMPLEX_EMPTY; HYPERPLANE_CELLCOMPLEX_INTER;
           HYPERPLANE_CELLCOMPLEX_UNION; HYPERPLANE_CELLCOMPLEX_DIFF]);;
```

### Informal statement
For any set of hyperplanes $A$ in $\mathbb{R}^N$ and any finite collection $s$ of sets where each set in $s$ is a hyperplane cell complex with respect to $A$, the Euler characteristic of the union of all sets in $s$ can be expressed as:

$$\chi_A\left(\bigcup_{k \in s} k\right) = \sum_{\substack{t \subseteq s \\ t \neq \emptyset}} (-1)^{|t|+1} \cdot \chi_A\left(\bigcap_{k \in t} k\right)$$

where $\chi_A$ represents the Euler characteristic with respect to hyperplane arrangement $A$, $|t|$ denotes the cardinality of set $t$, and the sum is taken over all non-empty subsets $t$ of $s$.

### Informal proof
This theorem follows from the general inclusion-exclusion principle for real-valued functions. The proof proceeds as follows:

* We apply the theorem `INCLUSION_EXCLUSION_REAL_RESTRICTED` to the function $\chi_A$ (Euler characteristic) and the predicate "is a hyperplane cell complex with respect to $A$".

* To apply this theorem, we need to verify several conditions:
  1. The Euler characteristic is additive for disjoint hyperplane cell complexes, which is provided by `EULER_CHARACTERISTIC_CELLCOMPLEX_UNION`.
  2. The empty set is a hyperplane cell complex, which is given by `HYPERPLANE_CELLCOMPLEX_EMPTY`.
  3. Hyperplane cell complexes are closed under intersection, union, and set difference operations, which are provided by `HYPERPLANE_CELLCOMPLEX_INTER`, `HYPERPLANE_CELLCOMPLEX_UNION`, and `HYPERPLANE_CELLCOMPLEX_DIFF`.

* Once these conditions are verified, the inclusion-exclusion formula follows directly from the general principle.

### Mathematical insight
The Euler characteristic is a topological invariant that generalizes the concept of alternating sums of the number of vertices, edges, faces, etc. in a polyhedron. This theorem provides a powerful combinatorial formula for computing the Euler characteristic of a union of cell complexes.

This result is particularly important in polyhedral geometry and topology. It allows us to compute the Euler characteristic of a complicated space by breaking it down into simpler pieces whose Euler characteristics are easier to calculate. The formula relates to the Möbius inversion formula in combinatorial theory.

The alternating signs in the formula reflect the principle of inclusion-exclusion, where overcounting is systematically corrected by subtracting and adding terms in an alternating pattern based on the number of sets being intersected.

### Dependencies
- **Theorems**:
  - `INCLUSION_EXCLUSION_REAL_RESTRICTED`: General inclusion-exclusion principle for real-valued functions
  - `HYPERPLANE_CELLCOMPLEX_EMPTY`: Empty set is a hyperplane cell complex
  - `HYPERPLANE_CELLCOMPLEX_UNION`: Union of hyperplane cell complexes is a hyperplane cell complex
  - `HYPERPLANE_CELLCOMPLEX_INTER`: Intersection of hyperplane cell complexes is a hyperplane cell complex
  - `HYPERPLANE_CELLCOMPLEX_DIFF`: Set difference of hyperplane cell complexes is a hyperplane cell complex
  - `EULER_CHARACTERISTIC_CELLCOMPLEX_UNION`: Additivity of Euler characteristic for disjoint cell complexes

- **Definitions**:
  - `hyperplane_cellcomplex`: Definition of hyperplane cell complexes
  - `euler_characteristic`: Definition of Euler characteristic for hyperplane arrangements

### Porting notes
When porting this theorem to another proof assistant:
1. Ensure that the underlying theory of hyperplane arrangements and cell complexes is already established
2. The definition of Euler characteristic might need special attention, as it involves affine dimensions and alternating sums
3. The inclusion-exclusion principle will need to be available in the target system
4. Set operations (union, intersection, difference) and their properties should be well-developed in the target system

---

## EULER_POLYHEDRAL_CONE

### EULER_POLYHEDRAL_CONE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let EULER_POLYHEDRAL_CONE = prove
 (`!s. polyhedron s /\ conic s /\ ~(interior s = {}) /\ ~(s = (:real^N))
       ==> sum (0..dimindex(:N))
               (\d. (-- &1) pow d *
                    &(CARD {f | f face_of s /\ aff_dim f = &d })) = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `affine hull s = (:real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s. s = UNIV /\ s SUBSET t ==> t = UNIV`) THEN
    EXISTS_TAC `affine hull (interior s:real^N->bool)` THEN
    SIMP_TAC[INTERIOR_SUBSET; HULL_MONO] THEN
    MATCH_MP_TAC AFFINE_HULL_OPEN THEN ASM_REWRITE_TAC[OPEN_INTERIOR];
    ALL_TAC] THEN
  FIRST_ASSUM
   (MP_TAC o GEN_REWRITE_RULE I [POLYHEDRON_INTER_AFFINE_MINIMAL]) THEN
  ASM_REWRITE_TAC[INTER_UNIV; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `H:(real^N->bool)->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(vec 0:real^N) IN s` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CONIC_CONTAINS_0] THEN
    ASM_MESON_TAC[SUBSET_EMPTY; INTERIOR_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h:real^N->bool. h IN H ==> ?a. ~(a = vec 0) /\ h = {x | a dot x <= &0}`
  MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `h:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; MATCH_MP_TAC MONO_EXISTS]  THEN
    X_GEN_TAC `a:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `b = &0` SUBST_ALL_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= b /\ ~(&0 < b) ==> b = &0`) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `(vec 0:real^N) IN INTERS H` MP_TAC THENL
       [ASM SET_TAC[]; REWRITE_TAC[IN_INTERS]] THEN
      DISCH_THEN(MP_TAC o SPEC `h:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_ELIM_THM; DOT_RZERO];
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `H DELETE (h:real^N->bool)`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[PSUBSET_ALT]] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC o CONJUNCT2) THEN
      SUBGOAL_THEN `?e. &0 < e /\ e < &1 /\
                        (e % x:real^N) IN h` STRIP_ASSUME_TAC THENL
       [EXISTS_TAC `min (&1 / &2) (b / ((a:real^N) dot x))` THEN
        ASM_REWRITE_TAC[IN_ELIM_THM; DOT_RMUL] THEN
        SUBGOAL_THEN `&0 < (a:real^N) dot x` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `b:real` THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `~((x:real^N) IN s)` THEN EXPAND_TAC "s" THEN
          ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
          REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
          SUBGOAL_THEN `H:(real^N->bool)->bool = h INSERT (H DELETE h)`
          SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
          REWRITE_TAC[INTERS_INSERT; IN_INTER] THEN
          ASM_REWRITE_TAC[IN_ELIM_THM];
          ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_DIV; REAL_MIN_LT] THEN
          CONV_TAC REAL_RAT_REDUCE_CONV THEN
          ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC];
        UNDISCH_TAC `~((x:real^N) IN s)` THEN REWRITE_TAC[] THEN
        SUBGOAL_THEN `x:real^N = inv e % e % x` SUBST1_TAC THENL
         [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ;
                       VECTOR_MUL_LID];
          ALL_TAC] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[conic]) THEN
        FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ] THEN
        EXPAND_TAC "s" THEN
        SUBGOAL_THEN `H:(real^N->bool)->bool = h INSERT (H DELETE h)`
        SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[INTERS_INSERT; IN_INTER] THEN
        CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `(x:real^N) IN INTERS (H DELETE h)` THEN
        REWRITE_TAC[IN_INTERS] THEN MATCH_MP_TAC MONO_FORALL THEN
        X_GEN_TAC `k:real^N->bool` THEN REWRITE_TAC[IN_DELETE] THEN
        DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `k:real^N->bool`) THEN
        ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
        MAP_EVERY X_GEN_TAC [`a':real^N`; `b':real`] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
        MATCH_MP_TAC(REAL_ARITH
         `(&0 <= x ==> y <= x) /\ (&0 <= --x ==> &0 <= --y) /\ &0 <= b
          ==> x <= b ==> y <= b`) THEN
        REWRITE_TAC[DOT_RMUL; GSYM REAL_MUL_RNEG] THEN
        REWRITE_TAC[REAL_ARITH `e * x <= x <=> &0 <= x * (&1 - e)`] THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_SUB_LE] THEN
        SUBGOAL_THEN `(vec 0:real^N) IN INTERS H` MP_TAC THENL
         [ASM SET_TAC[]; REWRITE_TAC[IN_INTERS]] THEN
        DISCH_THEN(MP_TAC o SPEC `k:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[IN_ELIM_THM; DOT_RZERO]]];
    FIRST_X_ASSUM(K ALL_TAC o SPEC `h:real^N->bool`)] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `fa:(real^N->bool)->real^N` THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o funpow 2 RAND_CONV)
   [EQ_SYM_EQ] THEN
  DISCH_TAC THEN ABBREV_TAC
   `A = IMAGE (\h. (fa:(real^N->bool)->real^N) h,&0) H` THEN
  SUBGOAL_THEN `FINITE(A:real^N#real->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN MATCH_MP_TAC FINITE_IMAGE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `euler_characteristic A (s:real^N->bool)` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[EULER_CHARACTERISTIC] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `d:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC BIJECTIONS_CARD_EQ THEN
    ASM_SIMP_TAC[FINITE_RESTRICT_HYPERPLANE_CELLS] THEN
    EXISTS_TAC `relative_interior:(real^N->bool)->(real^N->bool)` THEN
    EXISTS_TAC `closure:(real^N->bool)->(real^N->bool)` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [X_GEN_TAC `f:real^N->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN `closure(relative_interior f):real^N->bool = f`
      ASSUME_TAC THENL
       [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `closure f:real^N->bool` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CONVEX_CLOSURE_RELATIVE_INTERIOR THEN
          ASM_MESON_TAC[FACE_OF_IMP_CONVEX];
          REWRITE_TAC[CLOSURE_EQ] THEN MATCH_MP_TAC FACE_OF_IMP_CLOSED THEN
          ASM_MESON_TAC[POLYHEDRON_IMP_CLOSED; POLYHEDRON_IMP_CONVEX]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ALL_TAC;
        ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
        ONCE_REWRITE_TAC[GSYM AFFINE_HULL_CLOSURE] THEN
        ASM_REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN
        ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET_TRANS;
                      FACE_OF_IMP_SUBSET]] THEN
      SUBGOAL_THEN `~(f:real^N->bool = {})` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[GSYM AFF_DIM_POS_LE; INT_POS]; ALL_TAC] THEN
      SUBGOAL_THEN
       `?J. J SUBSET H /\
            f = INTERS {{x:real^N | fa h dot x <= &0} | h IN H} INTER
                INTERS {{x | fa(h:real^N->bool) dot x = &0} | h IN J}`
      ASSUME_TAC THENL
       [ASM_CASES_TAC `f:real^N->bool = s` THENL
         [EXISTS_TAC `{}:(real^N->bool)->bool` THEN
          REWRITE_TAC[EMPTY_SUBSET; NOT_IN_EMPTY; INTERS_0; INTER_UNIV;
                      SET_RULE `{f x | x | F} = {}`] THEN
          ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[SYM(ASSUME `INTERS H = (s:real^N->bool)`)] THEN
          AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
           `(!x. x IN s ==> f x = x) ==> s = {f x | x IN s}`) THEN
          ASM_SIMP_TAC[];
          ALL_TAC] THEN
        EXISTS_TAC
        `{h:real^N->bool | h IN H /\
                     f SUBSET s INTER {x:real^N | fa h dot x = &0}}` THEN
        CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPECL [`s:real^N->bool`; `H:(real^N->bool)->bool`;
                       `fa:(real^N->bool)->real^N`;
                       `\h:real^N->bool. &0`]
          FACE_OF_POLYHEDRON_EXPLICIT) THEN
        ASM_SIMP_TAC[INTER_UNIV] THEN
        DISCH_THEN(MP_TAC o SPEC `f:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN
         `INTERS {{x:real^N | fa(h:real^N->bool) dot x <= &0} | h IN H} = s`
        ASSUME_TAC THENL
         [EXPAND_TAC "s" THEN AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
           `(!x. x IN s ==> f x = x) ==> {f x | x IN s} = s`) THEN
          ASM_SIMP_TAC[];
         ALL_TAC] THEN
        ASM_CASES_TAC `{h:real^N->bool | h IN H /\
                           f SUBSET s INTER {x:real^N | fa h dot x = &0}} =
                       {}`
        THENL
         [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
          ASM_REWRITE_TAC[IMAGE_CLAUSES; INTERS_0] THEN
          FIRST_ASSUM(MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
          ASM SET_TAC[];
          ALL_TAC] THEN
        DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
        ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
        X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_INTER; IN_INTERS] THEN
        REWRITE_TAC[FORALL_IN_GSPEC; IN_INTER] THEN
        ASM_CASES_TAC `(y:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      ABBREV_TAC
       `H' = IMAGE (\h:real^N->bool. {x:real^N | --(fa h) dot x <= &0}) H` THEN
      SUBGOAL_THEN
       `?J. FINITE J /\
            J SUBSET (H UNION H') /\
            f:real^N->bool = affine hull f INTER INTERS J`
      MP_TAC THENL
       [FIRST_X_ASSUM(X_CHOOSE_THEN `J:(real^N->bool)->bool`
          STRIP_ASSUME_TAC) THEN
        EXISTS_TAC
         `H UNION IMAGE (\h:real^N->bool.
             {x:real^N | --(fa h) dot x <= &0}) J` THEN
        REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[FINITE_UNION] THEN MATCH_MP_TAC FINITE_IMAGE THEN
          ASM_MESON_TAC[FINITE_SUBSET];
          EXPAND_TAC "H'" THEN ASM SET_TAC[];
          MATCH_MP_TAC(SET_RULE `s SUBSET f /\ s = t ==> s = f INTER t`) THEN
          REWRITE_TAC[HULL_SUBSET] THEN
          FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
          REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
          REWRITE_TAC[INTERS_UNION] THEN MATCH_MP_TAC(SET_RULE
           `s = s' /\ (!x. x IN s ==> (x IN t <=> x IN t'))
            ==> s INTER t = s' INTER t'`) THEN
          CONJ_TAC THENL
           [AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
             `(!x. x IN s ==> f x = x) ==> {f x | x IN s} = s`) THEN
            ASM_SIMP_TAC[];
            ALL_TAC] THEN
          X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_INTERS] THEN
          REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
          REWRITE_TAC[IN_ELIM_THM; DOT_LNEG] THEN
          REWRITE_TAC[REAL_ARITH `--x <= &0 <=> &0 <= x`] THEN
          ASM SET_TAC[]];
        ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV
         [MESON[HAS_SIZE]
           `(?f. FINITE f /\ P f) <=> (?n f. f HAS_SIZE n /\ P f)`] THEN
      GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
      DISCH_THEN(X_CHOOSE_THEN `nn:num`
        (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
      DISCH_THEN(X_CHOOSE_THEN `J:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       `!J'. J' PSUBSET J
             ==> (f:real^N->bool) PSUBSET (affine hull f INTER INTERS J')`
      ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `CARD(J':(real^N->bool)->bool)`) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[CARD_PSUBSET; HAS_SIZE]; ALL_TAC] THEN
        REWRITE_TAC[NOT_EXISTS_THM; HAS_SIZE] THEN
        DISCH_THEN(MP_TAC o SPEC `J':(real^N->bool)->bool`) THEN
        MATCH_MP_TAC(TAUT `a /\ b /\ (~c ==> d) ==> ~(a /\ b /\ c) ==> d`) THEN
        CONJ_TAC THENL
         [ASM_MESON_TAC[PSUBSET; FINITE_SUBSET; HAS_SIZE]; ALL_TAC] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC(SET_RULE
         `s SUBSET t ==> ~(s = t) ==> s PSUBSET t`) THEN
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `!h:real^N->bool. h IN J
          ==> ?a. {x | a dot x <= &0} = h /\
                  (h IN H /\ a = fa h \/ ?h'. h' IN H /\ a = --(fa h'))`
      MP_TAC THENL
       [X_GEN_TAC `h:real^N->bool` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(h:real^N->bool) IN (H UNION H')` MP_TAC THENL
         [ASM SET_TAC[]; EXPAND_TAC "H'"] THEN
        UNDISCH_THEN `(h:real^N->bool) IN J` (K ALL_TAC) THEN
        SPEC_TAC(`h:real^N->bool`,`h:real^N->bool`) THEN
        REWRITE_TAC[IN_UNION; TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`;
                    FORALL_AND_THM; FORALL_IN_IMAGE] THEN
        CONJ_TAC THEN X_GEN_TAC `h:real^N->bool` THEN DISCH_TAC THENL
         [EXISTS_TAC `(fa:(real^N->bool)->real^N) h` THEN
          ASM_SIMP_TAC[];
          EXISTS_TAC `--((fa:(real^N->bool)->real^N) h)` THEN
          REWRITE_TAC[] THEN DISJ2_TAC THEN ASM_MESON_TAC[]];
        ALL_TAC] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
      REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `ga:(real^N->bool)->real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPECL
       [`f:real^N->bool`; `J:(real^N->bool)->bool`;
        `ga:(real^N->bool)->real^N`; `\h:real^N->bool. &0`]
       RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_MESON_TAC[HAS_SIZE];
          ASM_MESON_TAC[];
          ASM_SIMP_TAC[] THEN ASM_MESON_TAC[VECTOR_NEG_EQ_0; SUBSET]];
        DISCH_TAC THEN ASM_REWRITE_TAC[]] THEN
      SUBGOAL_THEN
       `!h:real^N->bool. h IN J ==> h IN H /\ ga h:real^N = fa h`
      ASSUME_TAC THENL
       [SUBGOAL_THEN `~(relative_interior f:real^N->bool = {})` MP_TAC THENL
         [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; FACE_OF_IMP_CONVEX];
          REWRITE_TAC[GSYM MEMBER_NOT_EMPTY]] THEN
        DISCH_THEN(X_CHOOSE_TAC `z:real^N`) THEN
        SUBGOAL_THEN `(z:real^N) IN f /\ z IN s` STRIP_ASSUME_TAC THENL
         [ASM_MESON_TAC[SUBSET; FACE_OF_IMP_SUBSET; RELATIVE_INTERIOR_SUBSET];
          ALL_TAC] THEN
        X_GEN_TAC `h:real^N->bool` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `h:real^N->bool`) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `h':real^N->bool` STRIP_ASSUME_TAC) THEN
        UNDISCH_TAC `(z:real^N) IN relative_interior f` THEN
        ASM_REWRITE_TAC[IN_ELIM_THM] THEN
        DISCH_THEN(MP_TAC o SPEC `h:real^N->bool`) THEN
        ASM_REWRITE_TAC[DOT_LNEG] THEN
        UNDISCH_TAC `(z:real^N) IN s` THEN EXPAND_TAC "s" THEN
        REWRITE_TAC[IN_INTERS] THEN
        DISCH_THEN(MP_TAC o SPEC `h':real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `h':real^N->bool`) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
          GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM(CONJUNCT2 th)]) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th] THEN
        MP_TAC(SYM th)) THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `K:(real^N->bool)->bool` MP_TAC) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN(fun th -> ASSUME_TAC(SYM th) THEN
        GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
      REWRITE_TAC[IN_INTER; IN_INTERS; FORALL_IN_GSPEC; GSYM CONJ_ASSOC] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(relative_interior f:real^N->bool = {})` ASSUME_TAC THENL
       [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; FACE_OF_IMP_CONVEX];
        ALL_TAC] THEN
      SUBGOAL_THEN `DISJOINT (J:(real^N->bool)->bool) K` ASSUME_TAC THENL
       [UNDISCH_TAC `~(relative_interior f:real^N->bool = {})` THEN
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC
         (LAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
        REWRITE_TAC[IN_DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
        ASM_MESON_TAC[REAL_LT_REFL];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `relative_interior f =
          INTERS {(if (h:real^N->bool) IN J then {x | fa h dot x < &0}
                   else if h IN K then {x:real^N | fa h dot x = &0}
                   else if relative_interior f SUBSET {x | fa h dot x = &0}
                   then {x | fa h dot x = &0}
                   else {x | fa h dot x < &0}) | h IN H}`
      ASSUME_TAC THENL
       [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
         [ALL_TAC;
          FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
          GEN_REWRITE_TAC I [SUBSET] THEN
          REWRITE_TAC[IN_INTERS; FORALL_IN_GSPEC; AND_FORALL_THM] THEN
          X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN
          MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `h:real^N->bool` THEN
          ASM_CASES_TAC `(h:real^N->bool) IN H` THENL
           [ALL_TAC; DISCH_THEN(K ALL_TAC) THEN ASM SET_TAC[]] THEN
          ASM_REWRITE_TAC[] THEN
          ASM_CASES_TAC `(h:real^N->bool) IN J` THEN
          ASM_SIMP_TAC[IN_ELIM_THM; REAL_LT_IMP_LE] THENL
           [ASM SET_TAC[]; ALL_TAC] THEN
          ASM_CASES_TAC `(h:real^N->bool) IN K` THEN
          ASM_SIMP_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN
          COND_CASES_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
          REAL_ARITH_TAC] THEN
        GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN
        DISCH_TAC THEN REWRITE_TAC[IN_INTERS; FORALL_IN_GSPEC] THEN
        X_GEN_TAC `h:real^N->bool` THEN DISCH_TAC THEN
        REPEAT(COND_CASES_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
        REWRITE_TAC[IN_ELIM_THM; REAL_LT_LE] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; DISCH_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
         [SET_RULE `~(s SUBSET t) <=> ?y. y IN s /\ ~(y IN t)`]) THEN
        REWRITE_TAC[IN_ELIM_THM; NOT_EXISTS_THM] THEN
        X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
         `~(x:real = &0) ==> ~(x <= &0) \/ x < &0`))
        THENL [ASM SET_TAC[]; ALL_TAC] THEN
        MP_TAC(ASSUME `(x:real^N) IN relative_interior f`) THEN
        REWRITE_TAC[IN_RELATIVE_INTERIOR_CBALL] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `e:real` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        REWRITE_TAC[SUBSET; IN_INTER; IN_CBALL] THEN
        SUBGOAL_THEN `~(y:real^N = x)` ASSUME_TAC THENL
         [ASM_MESON_TAC[REAL_LT_REFL]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPEC `x + e / norm(y - x) % (x - y):real^N`) THEN
        SUBGOAL_THEN
         `(x:real^N) IN affine hull f /\ y IN affine hull f`
        STRIP_ASSUME_TAC THENL
         [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET; HULL_SUBSET];
          ASM_SIMP_TAC[IN_AFFINE_ADD_MUL_DIFF; AFFINE_AFFINE_HULL]] THEN
        REWRITE_TAC[NORM_ARITH `dist(x:real^N,x + r) = norm r`] THEN
        REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM; NORM_SUB;
                       REAL_DIV_RMUL; NORM_EQ_0; VECTOR_SUB_EQ] THEN
          ASM_REAL_ARITH_TAC;
          DISCH_TAC] THEN
        SUBGOAL_THEN `(x + e / norm(y - x) % (x - y):real^N) IN s` MP_TAC THENL
         [ASM_MESON_TAC[SUBSET; FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
        EXPAND_TAC "s" THEN REWRITE_TAC[IN_INTERS] THEN
        DISCH_THEN(MP_TAC o SPEC `h:real^N->bool`) THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
         [SYM(CONJUNCT2(MATCH_MP th (ASSUME `(h:real^N->bool) IN H`)))]) THEN
        ASM_REWRITE_TAC[IN_ELIM_THM; DOT_RADD; REAL_ADD_LID; DOT_RMUL] THEN
        ASM_REWRITE_TAC[DOT_RSUB; REAL_SUB_LZERO; REAL_NOT_LE] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN
        ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT; VECTOR_SUB_EQ] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `~(relative_interior f:real^N->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; hyperplane_cell] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:real^N` THEN
      GEN_REWRITE_TAC RAND_CONV [EXTENSION] THEN
      ONCE_ASM_REWRITE_TAC[] THEN EXPAND_TAC "A" THEN
      REWRITE_TAC[IN_INTERS; FORALL_IN_GSPEC] THEN
      DISCH_THEN(fun th -> X_GEN_TAC `x:real^N` THEN MP_TAC th) THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [IN] THEN
      REWRITE_TAC[hyperplane_equiv; FORALL_IN_IMAGE] THEN
      MATCH_MP_TAC(MESON[]
       `(!h. P h ==> (Q h <=> R h))
        ==> (!h. P h) ==> ((!h. Q h) <=> (!h. R h))`) THEN
      X_GEN_TAC `h:real^N->bool` THEN
      ASM_CASES_TAC `(h:real^N->bool) IN H` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[hyperplane_side; REAL_SUB_RZERO] THEN
      REPEAT(COND_CASES_TAC THEN
        SIMP_TAC[IN_ELIM_THM] THENL [MESON_TAC[REAL_SGN_EQ]; ALL_TAC]) THEN
      MESON_TAC[REAL_SGN_EQ];
      X_GEN_TAC `c:real^N->bool` THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
      REWRITE_TAC[AFFINE_HULL_CLOSURE] THEN
      ASM_REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC `relative_interior c:real^N->bool` THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONVEX_RELATIVE_INTERIOR_CLOSURE THEN
          ASM_MESON_TAC[HYPERPLANE_CELL_CONVEX];
          ASM_MESON_TAC[HYPERPLANE_CELL_RELATIVE_INTERIOR]]] THEN
      SUBGOAL_THEN
       `?J. J SUBSET H /\
            c = INTERS {{x | (fa(h:real^N->bool)) dot x < &0} | h IN J} INTER
                INTERS {{x:real^N | (fa h) dot x = &0} | h IN (H DIFF J)}`
      MP_TAC THENL
       [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HYPERPLANE_CELL]) THEN
        EXPAND_TAC "A" THEN REWRITE_TAC[hyperplane_equiv; FORALL_IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `z:real^N` MP_TAC) THEN
        REWRITE_TAC[hyperplane_side; REAL_SUB_RZERO] THEN
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)
         [EQ_SYM_EQ] THEN
        DISCH_THEN(ASSUME_TAC o SYM) THEN EXISTS_TAC
         `{h:real^N->bool | h IN H /\
                            real_sgn(fa h dot (z:real^N)) = -- &1}` THEN
        REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} SUBSET s`] THEN
        REWRITE_TAC[GSYM INTERS_UNION] THEN EXPAND_TAC "c" THEN
        GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^N` THEN
        REWRITE_TAC[IN_ELIM_THM; IN_INTERS] THEN REWRITE_TAC[IN_UNION] THEN
        REWRITE_TAC[TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`;
                    FORALL_AND_THM] THEN
        REWRITE_TAC[FORALL_IN_GSPEC] THEN
        REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
        REWRITE_TAC[TAUT `a /\ ~(a /\ b) <=> a /\ ~b`] THEN
        REWRITE_TAC[AND_FORALL_THM] THEN AP_TERM_TAC THEN
        REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h:real^N->bool` THEN
        ASM_CASES_TAC `(h:real^N->bool) IN H` THEN ASM_REWRITE_TAC[] THEN
        REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
         (SPEC `(fa:(real^N->bool)->real^N) h dot z` REAL_SGN_CASES) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        REWRITE_TAC[REAL_SGN_EQ] THEN
        SUBGOAL_THEN `?x:real^N. x IN c /\ x IN s` MP_TAC THENL
         [ASM_MESON_TAC[MEMBER_NOT_EMPTY; SUBSET; NONEMPTY_HYPERPLANE_CELL];
          MATCH_MP_TAC(TAUT `~p ==> p ==> q`)] THEN
        MAP_EVERY EXPAND_TAC ["s"; "c"] THEN
        REWRITE_TAC[IN_INTERS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
        X_GEN_TAC `x:real^N` THEN REWRITE_TAC[AND_FORALL_THM] THEN
        DISCH_THEN(MP_TAC o SPEC `h:real^N->bool`) THEN
        ASM_REWRITE_TAC[REAL_SGN_EQ] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `h:real^N->bool`) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN(STRIP_ASSUME_TAC o GSYM)] THEN
      EXPAND_TAC "c" THEN
      W(MP_TAC o PART_MATCH (lhand o rand) CLOSURE_INTER_CONVEX o
        lhand o snd) THEN
      ANTS_TAC THENL
       [SIMP_TAC[CONVEX_INTERS; FORALL_IN_GSPEC; CONVEX_HALFSPACE_LT;
                 CONVEX_HYPERPLANE] THEN
        W(MP_TAC o PART_MATCH (lhand o rand) RELATIVE_INTERIOR_OPEN o
          lhand o lhand o rand o snd) THEN
        ANTS_TAC THENL
         [MATCH_MP_TAC OPEN_INTERS THEN
          ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
          REWRITE_TAC[FORALL_IN_IMAGE; OPEN_HALFSPACE_LT] THEN
          MATCH_MP_TAC FINITE_IMAGE THEN ASM_MESON_TAC[FINITE_SUBSET];
          DISCH_THEN SUBST1_TAC] THEN
        W(MP_TAC o PART_MATCH (lhand o rand) RELATIVE_INTERIOR_OPEN_IN o
          rand o lhand o rand o snd) THEN
        ANTS_TAC THENL
         [MATCH_MP_TAC(MESON[OPEN_IN_SUBTOPOLOGY_REFL]
           `s SUBSET topspace tp /\ t = s
            ==> open_in (subtopology tp t) s`) THEN
          REWRITE_TAC[SUBSET_UNIV; TOPSPACE_EUCLIDEAN] THEN
          REWRITE_TAC[AFFINE_HULL_EQ] THEN
          SIMP_TAC[AFFINE_INTERS; AFFINE_HYPERPLANE; FORALL_IN_GSPEC];
          DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
          ASM_MESON_TAC[NONEMPTY_HYPERPLANE_CELL]];
        ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      SIMP_TAC[CLOSURE_INTERS_CONVEX_OPEN; FORALL_IN_GSPEC;
               CONVEX_HALFSPACE_LT; OPEN_HALFSPACE_LT] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[EMPTY_FACE_OF; INTER_EMPTY] THEN
      SUBGOAL_THEN
       `IMAGE closure {{x | fa h dot x < &0} | h IN J} =
        {{x | (fa:(real^N->bool)->real^N) h dot x <= &0} | h IN J}`
      SUBST1_TAC THENL
       [ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
        REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN MATCH_MP_TAC IMAGE_EQ THEN
        GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC CLOSURE_HALFSPACE_LT THEN ASM SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
      `closure (INTERS {{x | fa h dot x = &0} | h IN H DIFF J}) =
       INTERS {{x | (fa:(real^N->bool)->real^N) h dot x = &0} | h IN H DIFF J}`
      SUBST1_TAC THENL
       [REWRITE_TAC[CLOSURE_EQ] THEN
        SIMP_TAC[CLOSED_INTERS; FORALL_IN_GSPEC; CLOSED_HYPERPLANE];
        ALL_TAC] THEN
      ASM_CASES_TAC `J:(real^N->bool)->bool = H` THENL
       [ASM_REWRITE_TAC[DIFF_EQ_EMPTY; INTER_UNIV; NOT_IN_EMPTY;
                        SET_RULE `{f x | x | F} = {}`; INTERS_0] THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP FACE_OF_REFL o
         MATCH_MP POLYHEDRON_IMP_CONVEX) THEN
        MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        EXPAND_TAC "s" THEN AP_TERM_TAC THEN
        MATCH_MP_TAC(SET_RULE
         `(!x. x IN s ==> f x = x) ==> s = {f x | x IN s}`) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `INTERS {{x | fa(h:real^N->bool) dot x <= &0} | h IN J} INTER
        INTERS {{x:real^N | fa h dot x = &0} | h IN H DIFF J} =
        INTERS {s INTER {x | fa h dot x = &0} | h IN H DIFF J}`
      SUBST1_TAC THENL
       [ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN REWRITE_TAC[INTERS_IMAGE] THEN
        GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^N` THEN
        REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
        ASM_CASES_TAC `(y:real^N) IN s` THEN ASM_REWRITE_TAC[] THENL
         [MATCH_MP_TAC(TAUT `a ==> (a /\ b <=> b)`) THEN
          UNDISCH_TAC `(y:real^N) IN s` THEN EXPAND_TAC "s" THEN
          REWRITE_TAC[IN_INTERS] THEN MATCH_MP_TAC MONO_FORALL THEN
          X_GEN_TAC `h:real^N->bool` THEN
          DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
          ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `h:real^N->bool`) THEN
          ANTS_TAC THENL [ASM SET_TAC[]; SET_TAC[]];
          UNDISCH_TAC `~((y:real^N) IN s)` THEN MATCH_MP_TAC
           (TAUT `~q /\ (p ==> r) ==> ~r ==> (p <=> q)`) THEN
          CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
          EXPAND_TAC "s" THEN REWRITE_TAC[IN_INTERS; AND_FORALL_THM] THEN
          MATCH_MP_TAC MONO_FORALL THEN
          X_GEN_TAC `h:real^N->bool` THEN
          DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `h:real^N->bool`) THEN
          ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
          DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
           [GSYM(CONJUNCT2 th)]) THEN
          ASM_REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
          ASM_CASES_TAC `(h:real^N->bool) IN J` THEN
          ASM_SIMP_TAC[REAL_LE_REFL]];
        ALL_TAC] THEN
      MATCH_MP_TAC FACE_OF_INTERS THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      X_GEN_TAC `h:real^N->bool` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE THEN
      ASM_SIMP_TAC[POLYHEDRON_IMP_CONVEX] THEN X_GEN_TAC `y:real^N` THEN
      EXPAND_TAC "s" THEN REWRITE_TAC[IN_INTERS] THEN
      DISCH_THEN(MP_TAC o SPEC `h:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `h:real^N->bool`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
        [GSYM(CONJUNCT2 th)]) THEN
      REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h. h IN H ==> hyperplane_cellcomplex A ((:real^N) DIFF h)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_MONO THEN
    EXISTS_TAC `{((fa:(real^N->bool)->real^N) h,&0)}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HYPERPLANE_CELL_CELLCOMPLEX THEN
      ASM_SIMP_TAC[HYPERPLANE_CELL_SING] THEN REPEAT DISJ2_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `h:real^N->bool`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
        GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM(CONJUNCT2 th)]) THEN
      REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM; IN_UNIV] THEN
      REAL_ARITH_TAC;
      EXPAND_TAC "A" THEN
      REWRITE_TAC[IN_IMAGE; SUBSET; FORALL_UNWIND_THM2; IN_SING] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h:real^N->bool. h IN H ==> hyperplane_cellcomplex A h`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[HYPERPLANE_CELLCOMPLEX_COMPL;
                  COMPL_COMPL];
    ALL_TAC] THEN
  SUBGOAL_THEN `hyperplane_cellcomplex A (s:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_INTERS THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:real^N#real->bool`;
                 `INTERS H:real^N->bool`;
                 `(:real^N) DIFF INTERS H`]
        EULER_CHARACTERISTIC_CELLCOMPLEX_UNION) THEN
  REWRITE_TAC[SET_RULE `DISJOINT s (UNIV DIFF s)`] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[HYPERPLANE_CELLCOMPLEX_DIFF; HYPERPLANE_CELLCOMPLEX_UNIV];
    REWRITE_TAC[SET_RULE `s UNION (UNIV DIFF s) = UNIV`]] THEN
  REWRITE_TAC[DIFF_INTERS] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x = (--(&1)) pow (dimindex(:N)) /\
    y = (--(&1)) pow (dimindex(:N))
    ==> x = s + y ==> s = &0`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `euler_characteristic {} (:real^N)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC EULER_CHARACTERSTIC_INVARIANT THEN
      ASM_REWRITE_TAC[FINITE_EMPTY] THEN CONJ_TAC THENL
       [MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_MONO THEN
        EXISTS_TAC `{}:real^N#real->bool` THEN REWRITE_TAC[EMPTY_SUBSET];
        ALL_TAC] THEN
      MATCH_MP_TAC HYPERPLANE_CELL_CELLCOMPLEX THEN
      REWRITE_TAC[HYPERPLANE_CELL_EMPTY];
      SIMP_TAC[EULER_CHARACTERISTIC_CELL; HYPERPLANE_CELL_EMPTY] THEN
      REWRITE_TAC[AFF_DIM_UNIV; NUM_OF_INT_OF_NUM]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) EULER_CHARACTERISTIC_INCLUSION_EXCLUSION o
    lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FORALL_IN_GSPEC] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
    ASM_SIMP_TAC[FINITE_IMAGE];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {t | t SUBSET {(:real^N) DIFF t | t IN H} /\ ~(t = {})}
             (\t. -- &1 pow (CARD t + 1) * (--(&1)) pow (dimindex(:N)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
    REWRITE_TAC[SIMPLE_IMAGE; IMP_CONJ; FORALL_SUBSET_IMAGE] THEN
    X_GEN_TAC `J:(real^N->bool)->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN DISCH_TAC THEN AP_TERM_TAC THEN
    ABBREV_TAC `B = IMAGE (\h:real^N->bool. fa h:real^N,&0) J` THEN
    SUBGOAL_THEN `(B:real^N#real->bool) SUBSET A` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `INTERS (IMAGE (\t. (:real^N) DIFF t) H) =
      IMAGE (--) (interior s)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`s:real^N->bool`; `H:(real^N->bool)->bool`;
                     `fa:(real^N->bool)->real^N`;
                     `\h:real^N->bool. &0`]
                RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT) THEN
      ASM_SIMP_TAC[INTER_UNIV] THEN
      ASM_SIMP_TAC[RELATIVE_INTERIOR_INTERIOR] THEN
      DISCH_THEN(K ALL_TAC) THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
      REWRITE_TAC[VECTOR_ARITH `--x:real^N = y <=> x = --y`; EXISTS_REFL] THEN
      X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTERS; IN_ELIM_THM] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_DIFF; IN_UNIV] THEN
      MATCH_MP_TAC(TAUT `(c ==> b) /\ (a <=> c) ==> (a <=> b /\ c)`) THEN
      CONJ_TAC THENL
       [EXPAND_TAC "s" THEN REWRITE_TAC[IN_INTERS] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `h:real^N->bool` THEN
        ASM_CASES_TAC `(h:real^N->bool) IN H` THEN ASM_REWRITE_TAC[] THEN
        ASM SET_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC(MESON[]
         `(!h. P h ==> (Q h <=> R h))
          ==> ((!h. P h ==> Q h) <=> (!h. P h ==> R h))`) THEN
        X_GEN_TAC `h:real^N->bool` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
         [SYM(CONJUNCT2(MATCH_MP th (ASSUME `(h:real^N->bool) IN H`)))]) THEN
        REWRITE_TAC[IN_ELIM_THM; DOT_RNEG] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `hyperplane_cell B (INTERS (IMAGE (\t. (:real^N) DIFF t) J))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN
       `~(INTERS (IMAGE (\t. (:real^N) DIFF t) J) = {})`
      MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[hyperplane_cell; GSYM MEMBER_NOT_EMPTY; IN_INTERS] THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:real^N` THEN
      REWRITE_TAC[IN_UNIV; IN_DIFF] THEN
      GEN_REWRITE_TAC RAND_CONV [EXTENSION] THEN
      DISCH_THEN(fun th -> X_GEN_TAC `x:real^N` THEN MP_TAC th) THEN
      REWRITE_TAC[IN_INTERS; FORALL_IN_IMAGE; IN_DIFF; IN_UNIV] THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [IN] THEN
      REWRITE_TAC[hyperplane_equiv] THEN EXPAND_TAC "B" THEN
      REWRITE_TAC[FORALL_IN_IMAGE; hyperplane_side] THEN
      MATCH_MP_TAC(MESON[]
       `(!h. P h ==> (Q h <=> R h))
        ==> (!h. P h) ==> ((!h. Q h) <=> (!h. R h))`) THEN
      X_GEN_TAC `h:real^N->bool` THEN
      ASM_CASES_TAC `(h:real^N->bool) IN J` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(h:real^N->bool) IN H` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o C MATCH_MP (ASSUME
       `(h:real^N->bool) IN H`)) THEN
      DISCH_THEN(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [SYM th] THEN
        GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM th]) THEN
      REWRITE_TAC[IN_ELIM_THM; REAL_SUB_RZERO; REAL_NOT_LE] THEN
      MESON_TAC[REAL_SGN_EQ; real_gt];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     `euler_characteristic B (INTERS (IMAGE (\t. (:real^N) DIFF t) J))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EULER_CHARACTERSTIC_INVARIANT THEN
      ASM_SIMP_TAC[HYPERPLANE_CELL_CELLCOMPLEX] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
      MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_MONO THEN
      EXISTS_TAC `B:real^N#real->bool` THEN
      ASM_SIMP_TAC[HYPERPLANE_CELL_CELLCOMPLEX];
      ALL_TAC] THEN
    ASM_SIMP_TAC[EULER_CHARACTERISTIC_CELL] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(MESON[NUM_OF_INT_OF_NUM] `i = &n ==> num_of_int i = n`) THEN
    REWRITE_TAC[AFF_DIM_EQ_FULL] THEN
    MATCH_MP_TAC(SET_RULE `!t. t SUBSET s /\ t = UNIV ==> s = UNIV`) THEN
    EXISTS_TAC `affine hull (INTERS (IMAGE (\t. (:real^N) DIFF t) H))` THEN
    CONJ_TAC THENL [MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC AFFINE_HULL_OPEN THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[IMAGE_EQ_EMPTY; OPEN_NEGATIONS; OPEN_INTERIOR];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_RMUL] THEN
  MATCH_MP_TAC(REAL_RING `s = &1 ==> s * t = t`) THEN
  MP_TAC(ISPECL [`\t:(real^N->bool)->bool. CARD t`;
                 `\t:(real^N->bool)->bool. (-- &1) pow (CARD t + 1)`;
                 `{t |  t SUBSET
                     {(:real^N) DIFF t | t IN H} /\ ~(t = {})}`;
                 `1..CARD(H:(real^N->bool)->bool)`]
        SUM_GROUP) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{t |  t SUBSET {(:real^N) DIFF t | t IN H}}` THEN
      CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      MATCH_MP_TAC FINITE_POWERSET THEN REWRITE_TAC[SIMPLE_IMAGE] THEN
      ASM_SIMP_TAC[FINITE_IMAGE];
      GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
      REWRITE_TAC[FORALL_IN_GSPEC; IN_NUMSEG] THEN
      REWRITE_TAC[SIMPLE_IMAGE; FORALL_SUBSET_IMAGE; IMP_CONJ] THEN
      X_GEN_TAC `J:(real^N->bool)->bool` THEN DISCH_TAC THEN
      REWRITE_TAC[IMAGE_EQ_EMPTY] THEN DISCH_TAC THEN
      SUBGOAL_THEN `FINITE(J:(real^N->bool)->bool)` ASSUME_TAC THENL
       [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
      ASM_SIMP_TAC[CARD_EQ_0; FINITE_IMAGE; ARITH_RULE `1 <= n <=> ~(n = 0)`;
                   IMAGE_EQ_EMPTY] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(J:(real^N->bool)->bool)` THEN
      ASM_SIMP_TAC[CARD_SUBSET; CARD_IMAGE_LE]];
    REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum (1..CARD(H:(real^N->bool)->bool))
        (\n. -- &1 pow (n + 1) * &(binom(CARD H,n)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[IN_NUMSEG] THEN DISCH_TAC THEN
    SIMP_TAC[IN_ELIM_THM] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) SUM_CONST o lhand o snd) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{t |  t SUBSET {(:real^N) DIFF t | t IN H}}` THEN
      CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      MATCH_MP_TAC FINITE_POWERSET THEN REWRITE_TAC[SIMPLE_IMAGE] THEN
      ASM_SIMP_TAC[FINITE_IMAGE];
      DISCH_THEN SUBST1_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `CARD {t | t SUBSET {(:real^N) DIFF t | t IN H} /\
                          t HAS_SIZE n}` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
      X_GEN_TAC `t:(real^N->bool)->bool` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_CASES_TAC `t:(real^N->bool)->bool = {}` THEN
      ASM_REWRITE_TAC[HAS_SIZE; CARD_CLAUSES; FINITE_EMPTY] THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `(p ==> r) ==> (p /\ q <=> p /\ r /\ q)`) THEN
      SPEC_TAC(`t:(real^N->bool)->bool`,`u:(real^N->bool)->bool`) THEN
      REWRITE_TAC[SIMPLE_IMAGE; FORALL_SUBSET_IMAGE] THEN
      ASM_MESON_TAC[FINITE_IMAGE; FINITE_SUBSET];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`CARD(H:(real^N->bool)->bool)`;
                   `n:num`; `{(:real^N) DIFF t | t IN H}`]
        NUMBER_OF_COMBINATIONS) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[HAS_SIZE]] THEN
    REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    ASM_REWRITE_TAC[GSYM FINITE_HAS_SIZE] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`CARD(H:(real^N->bool)->bool)`; `--(&1)`; `&1`]
        REAL_BINOMIAL_THEOREM) THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_RID; REAL_ADD_LINV] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; REAL_POW_ADD; REAL_POW_ONE; LE_0] THEN
  REWRITE_TAC[REAL_ARITH `(x * --(&1) pow 1) * y = --(y * x)`] THEN
  REWRITE_TAC[real_pow; SUM_NEG; ADD_CLAUSES; REAL_MUL_RID] THEN
  REWRITE_TAC[binom] THEN MATCH_MP_TAC(REAL_ARITH
   `x = &0 ==> x = &1 + y ==> --y = &1`) THEN
  REWRITE_TAC[REAL_POW_ZERO] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `CARD(H:(real^N->bool)->bool) = 0` THEN
  ASM_SIMP_TAC[CARD_EQ_0] THEN DISCH_THEN SUBST_ALL_TAC THEN ASM SET_TAC[]);;
```

### Informal statement
The Euler-Poincaré formula for a proper polyhedral cone states that the alternating sum of face counts by dimension equals zero:

For any set $s \subseteq \mathbb{R}^N$ that is a polyhedron, conic, with non-empty interior, and not the entire space, the Euler characteristic vanishes:

$$\sum_{d=0}^{\dim(\mathbb{R}^N)} (-1)^d \cdot |\{f \mid f \text{ face\_of } s \text{ and } \text{aff\_dim}(f) = d\}| = 0$$

Where $|\cdot|$ denotes the cardinality of a set.

### Informal proof
The proof develops in several main steps:

1. **Setup and Properties of the Cone**:
   - Since $s$ has non-empty interior, its affine hull must be the entire space $\mathbb{R}^N$.
   - We establish that the cone can be represented as an intersection of halfspaces of the form $\{x \mid a_h \cdot x \leq 0\}$ for vectors $a_h \neq 0$.
   - The origin $0$ is in $s$ (by the conic property).

2. **Representation via Hyperplane Arrangement**:
   - We define a hyperplane arrangement $A$ consisting of pairs $(a_h, 0)$ corresponding to the bounding halfspaces of $s$.
   - This representation allows us to express the alternating sum in terms of an Euler characteristic:
     $$\sum_{d=0}^{\dim(\mathbb{R}^N)} (-1)^d \cdot |\{f \mid f \text{ face\_of } s \text{ and } \text{aff\_dim}(f) = d\}| = \text{euler\_characteristic}(A, s)$$

3. **Applying Euler Characteristic Properties**:
   - The Euler characteristic of the entire space equals $(-1)^{\dim(\mathbb{R}^N)}$.
   - Using the fact that $s$ and its complement partition the space, we apply an additive property:
     $$\text{euler\_characteristic}(A, \mathbb{R}^N) = \text{euler\_characteristic}(A, s) + \text{euler\_characteristic}(A, \mathbb{R}^N \setminus s)$$

4. **Inclusion-Exclusion Analysis**:
   - We analyze the Euler characteristic of the complement of $s$ using an inclusion-exclusion formula.
   - The key insight is that this equals $(-1)^{\dim(\mathbb{R}^N)}$, the same as the Euler characteristic of the entire space.

5. **Final Algebraic Step**:
   - From the equation $\text{euler\_characteristic}(A, \mathbb{R}^N) = \text{euler\_characteristic}(A, s) + \text{euler\_characteristic}(A, \mathbb{R}^N \setminus s)$
   - And the fact that both $\text{euler\_characteristic}(A, \mathbb{R}^N)$ and $\text{euler\_characteristic}(A, \mathbb{R}^N \setminus s)$ equal $(-1)^{\dim(\mathbb{R}^N)}$
   - We conclude $\text{euler\_characteristic}(A, s) = 0$, which is exactly our theorem statement.

The proof combines combinatorial properties of hyperplane arrangements, topological Euler characteristics, and properties of polyhedral cones.

### Mathematical insight
This theorem extends the classical Euler's formula for polyhedra to the setting of polyhedral cones. The classical Euler formula states that for a convex polyhedron in $\mathbb{R}^3$, the number of vertices minus the number of edges plus the number of faces equals 2. 

In this generalized form for proper polyhedral cones (which are unbounded), the alternating sum of face counts equals 0 instead of 2. This is a fundamental result in polyhedral combinatorics and relates to the topology of polyhedral objects.

The theorem reveals an invariant property of polyhedral cones: regardless of their specific geometry, as long as they're full-dimensional and proper, their face counts must satisfy this alternating sum condition. This invariant is useful in enumerative combinatorics, polytope theory, and has connections to the Euler characteristic in algebraic topology.

### Dependencies
- **Theorems**:
  - `REAL_BINOMIAL_THEOREM`: Applies the binomial theorem to real expressions.
  - `FACE_OF_REFL`: Establishes that a convex set is a face of itself.
  - `EMPTY_FACE_OF`: The empty set is a face of any set.
  - `FACE_OF_INTERS`: The intersection of a collection of faces is a face.
  - `FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE`: Characterizes faces as intersections with supporting hyperplanes.
  - `FACE_OF_IMP_SUBSET`: A face is a subset of the original set.
  - `FACE_OF_IMP_CONVEX`: A face of a set is convex.
  - `FACE_OF_IMP_CLOSED`: A face of a closed convex set is closed.
  - `POLYHEDRON_IMP_CLOSED`: A polyhedron is closed.
  - `POLYHEDRON_IMP_CONVEX`: A polyhedron is convex.
  - `POLYHEDRON_INTER_AFFINE_MINIMAL`: Representation of polyhedron as intersection of minimal collection of halfspaces.
  - `FACE_OF_POLYHEDRON_EXPLICIT`: Explicit characterization of the faces of a polyhedron.
  - `RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT`: Explicit description of the relative interior of a polyhedron.
  - `HYPERPLANE_CELL`, `NONEMPTY_HYPERPLANE_CELL`, `HYPERPLANE_CELL_EMPTY`, `HYPERPLANE_CELL_SING`: Properties of hyperplane cells.
  - `HYPERPLANE_CELL_RELATIVE_INTERIOR`: The relative interior of a hyperplane cell is the cell itself.
  - `HYPERPLANE_CELL_CONVEX`: Hyperplane cells are convex.
  - `HYPERPLANE_CELLCOMPLEX_UNIV`: The entire space has a hyperplane cellcomplex structure.
  - `EULER_CHARACTERISTIC_CELLCOMPLEX_UNION`: Additivity of Euler characteristic for disjoint union.
  - `EULER_CHARACTERISTIC`: Formula for the Euler characteristic.
  - `EULER_CHARACTERISTIC_INCLUSION_EXCLUSION`: Inclusion-exclusion principle for Euler characteristics.
  - `NUMBER_OF_COMBINATIONS`: Counts the number of k-combinations from an n-element set.

- **Definitions**:
  - `binom`: Binomial coefficient.
  - `face_of`: Definition of a face of a set.
  - `polyhedron`: Definition of a polyhedron as intersection of halfspaces.
  - `hyperplane_side`, `hyperplane_equiv`, `hyperplane_cell`: Definitions for hyperplane arrangements.
  - `hyperplane_cellcomplex`: Structure formed by hyperplane cells.
  - `euler_characteristic`: Topological invariant for cell complexes.

### Porting notes
When porting this theorem:
1. Ensure your target system has a compatible definition of polyhedral cones and faces.
2. The proof relies heavily on properties of hyperplane arrangements and Euler characteristics, which may need to be developed first.
3. The theorem assumes a full-dimensional cone, which should be preserved as a condition.
4. The combinatorial argument using inclusion-exclusion principles is central to the proof.
5. Take care with the definition of Euler characteristic, as different systems might define it with different conventions.

---

## EULER_POINCARE_LEMMA

### Name of formal statement
EULER_POINCARE_LEMMA

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let EULER_POINCARE_LEMMA = prove
 (`!p:real^N->bool.
        2 <= dimindex(:N) /\ polytope p /\ affine hull p = {x | x$1 = &1}
        ==> sum (0..dimindex(:N)-1)
               (\d. (-- &1) pow d *
                    &(CARD {f | f face_of p /\ aff_dim f = &d })) = &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`basis 1:real^N`; `&1`] AFF_DIM_HYPERPLANE) THEN
  SIMP_TAC[BASIS_NONZERO; DOT_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN
  ASM_CASES_TAC `p:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN
    REWRITE_TAC[INT_ARITH `--(&1):int = x - &1 <=> x = &0`] THEN
    SIMP_TAC[INT_OF_NUM_EQ; LE_1; DIMINDEX_GE_1];
    DISCH_TAC] THEN
  ABBREV_TAC `s:real^N->bool = conic hull p` THEN
  MP_TAC(ISPEC `s:real^N->bool` EULER_POLYHEDRAL_CONE) THEN
  SUBGOAL_THEN
   `!f. f SUBSET {x:real^N | x$1 = &1}
        ==> (conic hull f) INTER {x:real^N | x$1 = &1} = f`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    ASM_SIMP_TAC[HULL_SUBSET; SUBSET_INTER] THEN
    REWRITE_TAC[SUBSET; CONIC_HULL_EXPLICIT; IN_INTER; IMP_CONJ] THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`c:real`; `x:real^N`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; REAL_MUL_RID; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `polyhedron(s:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `k:real^N->bool` MP_TAC o
      GEN_REWRITE_RULE I [polytope]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(fun th -> SUBST1_TAC th THEN ASSUME_TAC th) THEN
    MP_TAC(ISPEC `k:real^N->bool` CONVEX_CONE_HULL_SEPARATE_NONEMPTY) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[CONVEX_HULL_EQ_EMPTY]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC POLYHEDRON_CONVEX_CONE_HULL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP POLYHEDRON_IMP_CONVEX) THEN
  SUBGOAL_THEN `conic(s:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONIC_CONIC_HULL]; ALL_TAC] THEN
  SUBGOAL_THEN `~(s = (:real^N))` ASSUME_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `p:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[HULL_SUBSET]; ALL_TAC] THEN
    ASM_REWRITE_TAC[INTER_UNIV] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
    UNDISCH_TAC `polytope(p:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP POLYTOPE_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; NOT_EXISTS_THM] THEN X_GEN_TAC `B:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC
     `(lambda i. if i = 1 then &1 else B + &1):real^N`) THEN
    SIMP_TAC[LAMBDA_BETA; DIMINDEX_GE_1; LE_REFL; IN_ELIM_THM] THEN
    REWRITE_TAC[REAL_NOT_LE] THEN
    MP_TAC(ISPECL
    [`(lambda i. if i = 1 then &1 else B + &1):real^N`; `2`]
      COMPONENT_LE_NORM) THEN
    ASM_SIMP_TAC[ARITH; LAMBDA_BETA; DIMINDEX_GE_1; LE_REFL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONIC_HULL_EQ_EMPTY]; ALL_TAC] THEN
  MP_TAC(ISPEC `s:real^N->bool` CONIC_CONTAINS_0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(interior(s:real^N->bool) = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN MP_TAC(ISPEC `s:real^N->bool`
     EMPTY_INTERIOR_SUBSET_HYPERPLANE) THEN
    ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `s SUBSET {x:real^N | x$1 = &1}` MP_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `s SUBSET h' ==> h SUBSET h' /\ ~(h PSUBSET h') ==> s SUBSET h`)) THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
        MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_HYPERPLANE] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[HULL_SUBSET];
        DISCH_TAC THEN
        MP_TAC(ISPECL [`a:real^N`; `b:real`] AFF_DIM_HYPERPLANE) THEN
        MP_TAC(ISPECL [`basis 1:real^N`; `&1`] AFF_DIM_HYPERPLANE) THEN
        ASM_SIMP_TAC[BASIS_NONZERO; DOT_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
        MATCH_MP_TAC(INT_ARITH `a:int < b ==> a = n ==> ~(b = n)`) THEN
        MATCH_MP_TAC AFF_DIM_PSUBSET THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
         (SET_RULE `s PSUBSET t ==> s' = s /\ t' = t ==> s' PSUBSET t'`)) THEN
        REWRITE_TAC[AFFINE_HULL_EQ; AFFINE_HYPERPLANE] THEN
        MP_TAC(ISPECL [`basis 1:real^N`; `&1`] AFFINE_HYPERPLANE) THEN
        SIMP_TAC[BASIS_NONZERO; DOT_BASIS; DIMINDEX_GE_1; LE_REFL]];
      REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN
      EXISTS_TAC `vec 0:real^N` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; VEC_COMPONENT] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x:real^N. x IN s /\ ~(x = vec 0) ==> &0 < x$1`
  ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[CONIC_HULL_EXPLICIT; IMP_CONJ] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; VECTOR_MUL_EQ_0; DE_MORGAN_THM] THEN
    MAP_EVERY X_GEN_TAC [`c:real`; `x:real^N`] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN affine hull p` MP_TAC THENL
     [ASM_MESON_TAC[HULL_SUBSET; SUBSET]; ASM_REWRITE_TAC[]] THEN
    SIMP_TAC[IN_ELIM_THM; REAL_LT_01];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN s ==> &0 <= x$1` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `x:real^N = vec 0` THEN
    ASM_SIMP_TAC[VEC_COMPONENT; REAL_POS; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) SUM_CLAUSES_LEFT o
    lhand o lhand o snd) THEN
  REWRITE_TAC[LE_0] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[AFF_DIM_EQ_0; real_pow; REAL_MUL_LID] THEN
  SUBGOAL_THEN `{f | f face_of s /\ (?a:real^N. f = {a})} = {{vec 0}}`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
    X_GEN_TAC `f:real^N->bool` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_TAC `a:real^N`)) THEN
      ASM_REWRITE_TAC[FACE_OF_SING] THEN
      ASM_MESON_TAC[EXTREME_POINT_OF_CONIC];
      DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
      ASM_REWRITE_TAC[FACE_OF_SING; extreme_point_of; IN_SEGMENT] THEN
      MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN STRIP_TAC THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `u:real` THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC[CART_EQ] THEN DISCH_THEN(MP_TAC o SPEC `1`) THEN
      REWRITE_TAC[LE_REFL; DIMINDEX_GE_1; VEC_COMPONENT] THEN
      REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      SUBGOAL_THEN `&0 < (a:real^N)$1 \/ &0 < (b:real^N)$1` DISJ_CASES_TAC THENL
       [ASM_MESON_TAC[];
        MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 <= b ==> ~(&0 = a + b)`);
        MATCH_MP_TAC(REAL_ARITH `&0 < b /\ &0 <= a ==> ~(&0 = a + b)`)] THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LT_MUL; REAL_SUB_LT]];
    ALL_TAC] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_EMPTY; NOT_IN_EMPTY; GSYM REAL_OF_NUM_SUC] THEN
  MATCH_MP_TAC(REAL_ARITH `s = --t ==> (&0 + &1) + s = &0 ==> t = &1`) THEN
  SUBGOAL_THEN `dimindex(:N) = (dimindex(:N)-1)+1`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
  THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUM_OFFSET; GSYM SUM_NEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; REAL_MUL_RNEG; REAL_MUL_LNEG] THEN
  AP_TERM_TAC THEN REWRITE_TAC[REAL_MUL_RID] THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC BIJECTIONS_CARD_EQ THEN
  EXISTS_TAC `\f:real^N->bool. f INTER {x | x$1 = &1}` THEN
  EXISTS_TAC `\f:real^N->bool. conic hull f` THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN CONJ_TAC THENL
   [DISJ1_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{f:real^N->bool | f face_of s}` THEN
    ASM_SIMP_TAC[FINITE_POLYHEDRON_FACES] THEN SET_TAC[];
    REWRITE_TAC[IN_ELIM_THM; GSYM INT_OF_NUM_ADD]] THEN
  SUBGOAL_THEN
   `!f:real^N->bool. f face_of p ==> conic hull f INTER {x | x$1 = &1} = f`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `affine hull p:real^N->bool` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; HULL_SUBSET; SUBSET_TRANS];
      ASM_REWRITE_TAC[SUBSET_REFL]];
    ASM_SIMP_TAC[]] THEN
  SUBGOAL_THEN
   `!f:real^N->bool. f face_of s ==> f INTER {x | x$1 = &1} face_of p`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `p = conic hull p INTER {x:real^N | x$1 = &1}` SUBST1_TAC
    THENL [ASM_MESON_TAC[FACE_OF_REFL; POLYTOPE_IMP_CONVEX]; ALL_TAC] THEN
    MATCH_MP_TAC FACE_OF_SLICE THEN
    ASM_REWRITE_TAC[CONVEX_STANDARD_HYPERPLANE];
    ASM_SIMP_TAC[]] THEN
  SUBGOAL_THEN
   `!f. f face_of s  /\ &0 < aff_dim f
        ==> conic hull (f INTER {x:real^N | x$1 = &1}) = f`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; CONIC_HULL_EXPLICIT; FORALL_IN_GSPEC] THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
      ASM_MESON_TAC[FACE_OF_CONIC; conic];
      REWRITE_TAC[SUBSET; CONIC_HULL_EXPLICIT] THEN X_GEN_TAC `x:real^N` THEN
      DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN
      ASM_CASES_TAC `x:real^N = vec 0` THENL
       [SUBGOAL_THEN `?y:real^N. y IN f /\ ~(y = vec 0)` STRIP_ASSUME_TAC THENL
         [MATCH_MP_TAC(SET_RULE
           `a IN s /\ ~(s = {a}) ==> ?y. y IN s /\ ~(y = a)`) THEN
          ASM_MESON_TAC[AFF_DIM_EQ_0; INT_LT_REFL];
          SUBGOAL_THEN `&0 < (y:real^N)$1` ASSUME_TAC THENL
           [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
          EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[REAL_POS; VECTOR_MUL_LZERO] THEN
          EXISTS_TAC `inv(y$1) % y:real^N` THEN
          ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; REAL_MUL_LINV;
                       REAL_LT_IMP_NZ] THEN
          ASM_MESON_TAC[FACE_OF_CONIC; conic; REAL_LE_INV_EQ; REAL_LT_IMP_LE]];
        SUBGOAL_THEN `&0 < (x:real^N)$1` ASSUME_TAC THENL
         [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
        EXISTS_TAC `(x:real^N)$1` THEN EXISTS_TAC `inv(x$1) % x:real^N` THEN
        ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; REAL_MUL_LINV; REAL_LT_IMP_LE;
          REAL_LT_IMP_NZ; VECTOR_MUL_ASSOC; REAL_MUL_RINV; VECTOR_MUL_LID] THEN
        ASM_MESON_TAC[FACE_OF_CONIC; conic; REAL_LE_INV_EQ; REAL_LT_IMP_LE]]];
    ASM_SIMP_TAC[INT_ARITH `&0:int < &d + &1`]] THEN
  SUBGOAL_THEN
   `!f:real^N->bool. f face_of p ==> (conic hull f) face_of s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `f:real^N->bool = {}` THEN
    ASM_REWRITE_TAC[CONIC_HULL_EMPTY; EMPTY_FACE_OF] THEN
    REWRITE_TAC[face_of] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "s" THEN MATCH_MP_TAC HULL_MONO THEN
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET];
      ASM_MESON_TAC[CONVEX_CONIC_HULL; FACE_OF_IMP_CONVEX];
      ALL_TAC] THEN
    EXPAND_TAC "s" THEN REWRITE_TAC[CONIC_HULL_EXPLICIT; IMP_CONJ] THEN
    REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`ca:real`; `a:real^N`] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`cb:real`; `b:real^N`] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`cx:real`; `x:real^N`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `cx % x:real^N = vec 0` THENL
     [ASM_REWRITE_TAC[IN_SEGMENT] THEN
      MATCH_MP_TAC(TAUT `(a ==> ~b) ==> a /\ b ==> c`) THEN
      DISCH_TAC THEN DISCH_THEN(X_CHOOSE_THEN `u:real` MP_TAC) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC[CART_EQ] THEN DISCH_THEN(MP_TAC o SPEC `1`) THEN
      REWRITE_TAC[LE_REFL; DIMINDEX_GE_1; VEC_COMPONENT] THEN
      REWRITE_TAC[VECTOR_ADD_COMPONENT] THEN
      ONCE_REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
      SUBGOAL_THEN `&0 < (ca % a:real^N)$1 \/ &0 < (cb % b:real^N)$1`
      DISJ_CASES_TAC THENL
       [SUBGOAL_THEN `(ca % a:real^N) IN s /\ (cb % b:real^N) IN s`
          (fun th -> ASM_MESON_TAC[th]) THEN
        ASM_MESON_TAC[conic; HULL_SUBSET; SUBSET];
        MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 <= b ==> ~(&0 = a + b)`);
        MATCH_MP_TAC(REAL_ARITH `&0 < b /\ &0 <= a ==> ~(&0 = a + b)`)] THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LT_MUL; REAL_SUB_LT] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_SUB_LT] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[conic; HULL_SUBSET; SUBSET];
      ALL_TAC] THEN
    UNDISCH_TAC `~(cx % x:real^N = vec 0)` THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0; DE_MORGAN_THM] THEN STRIP_TAC THEN
    ASM_CASES_TAC `x:real^N = a` THENL
     [REWRITE_TAC[IN_SEGMENT] THEN DISCH_THEN
       (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real` MP_TAC)) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      ASM_REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_ARITH
       `x % a:real^N = y % a + z % b <=> (x - y) % a = z % b`] THEN
      DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC th) THEN
      GEN_REWRITE_TAC LAND_CONV [CART_EQ] THEN
      DISCH_THEN(MP_TAC o SPEC `1`) THEN
      REWRITE_TAC[LE_REFL; DIMINDEX_GE_1; VECTOR_MUL_COMPONENT] THEN
      SUBGOAL_THEN `(a:real^N) IN affine hull p /\ b IN affine hull p`
      MP_TAC THENL
       [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; HULL_SUBSET; SUBSET]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
      REWRITE_TAC[REAL_MUL_RID] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_ENTIRE; REAL_LT_IMP_NZ] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [CONJ_TAC THENL
         [MAP_EVERY EXISTS_TAC [`ca:real`; `a:real^N`] THEN
          ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
          MAP_EVERY EXISTS_TAC [`&0`; `x:real^N`] THEN
          ASM_REWRITE_TAC[VECTOR_MUL_LZERO; REAL_LE_REFL]];
        CONJ_TAC THENL [EXISTS_TAC `ca:real`; EXISTS_TAC `cb:real`] THEN
        EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `x:real^N = b` THENL
     [REWRITE_TAC[IN_SEGMENT] THEN DISCH_THEN
       (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real` MP_TAC)) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      ASM_REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_ARITH
       `x % b:real^N = y % a + z % b <=> (x - z) % b = y % a`] THEN
      DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC th) THEN
      GEN_REWRITE_TAC LAND_CONV [CART_EQ] THEN
      DISCH_THEN(MP_TAC o SPEC `1`) THEN
      REWRITE_TAC[LE_REFL; DIMINDEX_GE_1; VECTOR_MUL_COMPONENT] THEN
      SUBGOAL_THEN `(a:real^N) IN affine hull p /\ b IN affine hull p`
      MP_TAC THENL
       [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; HULL_SUBSET; SUBSET]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
      REWRITE_TAC[REAL_MUL_RID] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_ENTIRE;
                   REAL_LT_IMP_NE; REAL_SUB_0] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [CONJ_TAC THENL
         [MAP_EVERY EXISTS_TAC [`&0`; `x:real^N`] THEN
          ASM_REWRITE_TAC[VECTOR_MUL_LZERO; REAL_LE_REFL];
          MAP_EVERY EXISTS_TAC [`cb:real`; `b:real^N`] THEN
          ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
        CONJ_TAC THENL [EXISTS_TAC `ca:real`; EXISTS_TAC `cb:real`] THEN
        EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN segment(a,b)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_OPEN_SEGMENT]) THEN
      ASM_REWRITE_TAC[IN_OPEN_SEGMENT] THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[IN_SEGMENT] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real` MP_TAC) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC th) THEN
      GEN_REWRITE_TAC LAND_CONV [CART_EQ] THEN
      DISCH_THEN(MP_TAC o SPEC `1`) THEN
      REWRITE_TAC[LE_REFL; DIMINDEX_GE_1; VECTOR_ADD_COMPONENT;
                  VECTOR_MUL_COMPONENT] THEN
      SUBGOAL_THEN `(x:real^N) IN affine hull p /\
                    a IN affine hull p /\ b IN affine hull p`
      MP_TAC THENL
       [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; HULL_SUBSET; SUBSET]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
      REWRITE_TAC[REAL_MUL_RID] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
      DISCH_THEN(MP_TAC o AP_TERM `(%) (inv cx) :real^N->real^N`) THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID] THEN
      DISCH_THEN(K ALL_TAC) THEN EXISTS_TAC `inv(cx) * u * cb` THEN
      REWRITE_TAC[REAL_ARITH `inv(cx) * x:real = x / cx`] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_LT_LE] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REAL_MUL_LZERO] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
         `a + b = cx ==> &0 <= a ==> b <= &1 * cx`)) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_ADD_LDISTRIB] THEN
        BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        MAP_EVERY UNDISCH_TAC
         [`(&1 - u) * ca + u * cb = cx`; `~(cx = &0)`] THEN
        CONV_TAC REAL_FIELD];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [face_of]) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN(MP_TAC o SPECL [`a:real^N`; `b:real^N`; `x:real^N`]) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ASM_SIMP_TAC[]] THEN
  SUBGOAL_THEN
   `!f:real^N->bool. f face_of p /\ ~(f = {})
                     ==> aff_dim(conic hull f) = aff_dim f + &1`
  (LABEL_TAC "*") THENL
   [ALL_TAC;
    CONJ_TAC THEN X_GEN_TAC `f:real^N->bool` THEN STRIP_TAC THENL
     [REMOVE_THEN "*" (MP_TAC o SPEC `f INTER {x:real^N | x$1 = &1}`) THEN
      ASM_SIMP_TAC[INT_ARITH `&0:int < &d + &1`; INT_EQ_ADD_RCANCEL] THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      SUBGOAL_THEN `?y:real^N. y IN f /\ ~(y = vec 0)` STRIP_ASSUME_TAC THENL
       [MATCH_MP_TAC(SET_RULE
         `a IN s /\ ~(s = {a}) ==> ?y. y IN s /\ ~(y = a)`) THEN
        CONJ_TAC THENL
         [MP_TAC(ISPECL [`s:real^N->bool`; `f:real^N->bool`]
            FACE_OF_CONIC) THEN
          ASM_SIMP_TAC[CONIC_CONTAINS_0] THEN REPEAT DISCH_TAC;
          DISCH_TAC] THEN
        UNDISCH_TAC `aff_dim(f:real^N->bool) = &d + &1` THEN
        ASM_REWRITE_TAC[AFF_DIM_SING; AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
        SUBGOAL_THEN `&0 < (y:real^N)$1` ASSUME_TAC THENL
         [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
        EXISTS_TAC `inv(y$1) % y:real^N` THEN
        ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; REAL_MUL_LINV;
                     REAL_LT_IMP_NZ] THEN
        MP_TAC(ISPECL [`s:real^N->bool`; `f:real^N->bool`]
          FACE_OF_CONIC) THEN
        ASM_SIMP_TAC[CONIC_CONTAINS_0] THEN
        REWRITE_TAC[conic] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]];
      REMOVE_THEN "*" (MP_TAC o SPEC `f:real^N->bool`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      DISCH_TAC THEN UNDISCH_TAC `aff_dim(f:real^N->bool) = &d` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC]] THEN
  X_GEN_TAC `f:real^N->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC(INT_ARITH `f < a /\ a <= f + &1 ==> a:int = f + &1`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC AFF_DIM_PSUBSET THEN
    SIMP_TAC[PSUBSET; HULL_MONO; HULL_SUBSET] THEN
    REWRITE_TAC[EXTENSION; NOT_FORALL_THM] THEN EXISTS_TAC `vec 0:real^N` THEN
    MATCH_MP_TAC(TAUT `~p /\ q ==> ~(p <=> q)`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!t. ~(x IN t) /\ s SUBSET t ==> ~(x IN s)`) THEN
      EXISTS_TAC `affine hull p:real^N->bool` THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[IN_ELIM_THM; VEC_COMPONENT] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC HULL_MONO THEN ASM_MESON_TAC[FACE_OF_IMP_SUBSET]];
      MATCH_MP_TAC(SET_RULE
       `x IN s /\ s SUBSET P hull s ==> x IN P hull s`) THEN
      ASM_SIMP_TAC[CONIC_CONTAINS_0; HULL_SUBSET; CONIC_CONIC_HULL] THEN
      ASM_REWRITE_TAC[CONIC_HULL_EQ_EMPTY]];
    MATCH_MP_TAC INT_LE_TRANS THEN
    EXISTS_TAC `aff_dim((vec 0:real^N) INSERT (affine hull f))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[AFF_DIM_INSERT; AFF_DIM_AFFINE_HULL] THEN INT_ARITH_TAC] THEN
    ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
    MATCH_MP_TAC AFF_DIM_SUBSET THEN MATCH_MP_TAC HULL_MINIMAL THEN
    REWRITE_TAC[AFFINE_AFFINE_HULL; SUBSET; CONIC_HULL_EXPLICIT] THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`c:real`; `x:real^N`] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH
     `c % x:real^N = vec 0 + c % (x - vec 0)`] THEN
    MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN
    ASM_SIMP_TAC[AFFINE_AFFINE_HULL; HULL_INC; IN_INSERT]]);;
```

### Informal statement
Let $p$ be a polytope in $\mathbb{R}^N$ where $N \geq 2$, such that the affine hull of $p$ is exactly the hyperplane $\{x \in \mathbb{R}^N : x_1 = 1\}$. Then the alternating sum of the face counts by dimension satisfies:

$$\sum_{d=0}^{N-1} (-1)^d \cdot |{\{f : f \text{ face_of } p \text{ and } \text{aff_dim}(f) = d\}}| = 1$$

In other words, for a polytope $p$ embedded in a hyperplane in $\mathbb{R}^N$, the Euler-Poincaré characteristic equals 1.

### Informal proof
The proof involves several main steps:

- First, we define $s$ as the conic hull of $p$, which creates a polyhedral cone.
- We verify that $s$ is a polyhedron, is conic, has non-empty interior, and is not the entire space.
- We establish that for any face $f$ of $p$, the set $\text{conic hull}(f)$ is a face of $s$.
- We show that faces of $s$ intersected with the hyperplane $\{x : x_1 = 1\}$ give faces of $p$.
- We prove a key bijection between faces of $p$ of dimension $d$ and faces of $s$ of dimension $d+1$.

The proof then handles several technical aspects:

1. For a non-empty set $f$, we show $\text{aff_dim}(\text{conic hull}(f)) = \text{aff_dim}(f) + 1$.

2. We establish that the only 0-dimensional face of $s$ is $\{\vec{0}\}$, which follows from the fact that the only extreme point of a cone is the origin.

3. By applying the Euler characteristic formula for polyhedral cones (which states that the alternating sum equals 0), we get:
   $$\sum_{d=0}^{N} (-1)^d \cdot |{\{f : f \text{ face_of } s \text{ and } \text{aff_dim}(f) = d\}}| = 0$$

4. Using the bijection between faces and the dimension relationship, we rewrite this as:
   $$(-1)^0 \cdot 1 + \sum_{d=0}^{N-1} (-1)^{d+1} \cdot |{\{f : f \text{ face_of } p \text{ and } \text{aff_dim}(f) = d\}}| = 0$$

5. Simplifying further:
   $$1 + \sum_{d=0}^{N-1} (-1)^{d+1} \cdot |{\{f : f \text{ face_of } p \text{ and } \text{aff_dim}(f) = d\}}| = 0$$

6. Manipulating this equation:
   $$\sum_{d=0}^{N-1} (-1)^{d} \cdot |{\{f : f \text{ face_of } p \text{ and } \text{aff_dim}(f) = d\}}| = 1$$

Which gives us the desired result.

### Mathematical insight
The Euler-Poincaré lemma is a fundamental result in polyhedral combinatorics and relates to the Euler characteristic of polytopes. This particular formulation deals with polytopes embedded in a hyperplane, which is a common setting for representing standard polytopes in one dimension less.

The theorem establishes that the alternating sum of face counts by dimension equals 1, which is consistent with the topological interpretation of the Euler characteristic for convex polytopes. 

The key insight in this proof is the relationship between a polytope in a hyperplane and its conic hull. By creating this correspondence, we can leverage properties of polyhedral cones (where the Euler characteristic is 0) to establish the result for polytopes (where the Euler characteristic is 1).

This result has connections to the classical Euler formula for polyhedra (vertices - edges + faces = 2), but generalizes it to arbitrary dimensions and to polytopes embedded in a specific hyperplane.

### Dependencies
- Theorems related to faces:
  - `FACE_OF_REFL`: For any convex set s, s is a face of itself
  - `EMPTY_FACE_OF`: The empty set is a face of any set
  - `FACE_OF_SLICE`: If f is a face of s and t is convex, then f ∩ t is a face of s ∩ t
  - `FACE_OF_IMP_SUBSET`: If t is a face of s, then t is a subset of s
  - `FACE_OF_IMP_CONVEX`: If t is a face of s, then t is convex
  - `FACE_OF_CONIC`: If s is conic and f is a face of s, then f is conic
  - `FACE_OF_SING`: A singleton is a face of s iff its element is an extreme point of s

- Theorems about extreme points:
  - `EXTREME_POINT_OF_CONIC`: In a conic set, the only possible extreme point is the origin

- Theorems about polytopes and polyhedra:
  - `POLYTOPE_IMP_CONVEX`: A polytope is convex
  - `POLYTOPE_IMP_BOUNDED`: A polytope is bounded
  - `POLYHEDRON_IMP_CONVEX`: A polyhedron is convex
  - `FINITE_POLYHEDRON_FACES`: A polyhedron has finitely many faces
  - `POLYHEDRON_CONVEX_CONE_HULL`: The convex cone hull of a finite set is a polyhedron

- Key theorem used in the proof:
  - `EULER_POLYHEDRAL_CONE`: For a polyhedral cone that satisfies certain conditions, the alternating sum of face counts by dimension equals 0

### Porting notes
When porting this theorem:
1. Ensure your system has a proper representation of affine dimension and faces of convex sets
2. The theorem relies on the concept of conic hull, which should be defined correctly
3. Pay attention to type casting between integers and natural numbers when dealing with dimensions
4. The dimensions in the sum range from 0 to N-1, where N is the dimension of the ambient space
5. The proof makes essential use of properties of polyhedral cones and their relationship to polytopes embedded in hyperplanes

---

## EULER_POINCARE_SPECIAL

### Name of formal statement
EULER_POINCARE_SPECIAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_POINCARE_SPECIAL = prove
 (`!p:real^N->bool.
        2 <= dimindex(:N) /\ polytope p /\ affine hull p = {x | x$1 = &0}
        ==> sum (0..dimindex(:N)-1)
               (\d. (-- &1) pow d *
                    &(CARD {f | f face_of p /\ aff_dim f = &d })) = &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (\x:real^N. basis 1 + x) p` EULER_POINCARE_LEMMA) THEN
  ASM_REWRITE_TAC[POLYTOPE_TRANSLATION_EQ; AFFINE_HULL_TRANSLATION] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
    REWRITE_TAC[EXISTS_REFL; VECTOR_ARITH
     `a + x:real^N = y <=> x = y - a`] THEN
    SIMP_TAC[IN_ELIM_THM; VECTOR_ADD_COMPONENT; BASIS_COMPONENT;
             DIMINDEX_GE_1; LE_REFL] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SET_RULE `{f | f face_of s /\ P f} =
                          {f | f IN {f | f face_of s} /\ P f}`] THEN
    REWRITE_TAC[FACES_OF_TRANSLATION] THEN
    REWRITE_TAC[SET_RULE `{y | y IN IMAGE f s /\ P y} =
                          {f x |x| x IN s /\ P(f x)}`] THEN
    REWRITE_TAC[AFF_DIM_TRANSLATION_EQ; IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SIMPLE_IMAGE_GEN] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
       `(!x y. Q x y ==> x = y)
        ==> (!x y. P x /\ P y /\ Q x y ==> x = y)`) THEN
      REWRITE_TAC[INJECTIVE_IMAGE] THEN VECTOR_ARITH_TAC;
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{f:real^N->bool | f face_of p}` THEN
      ASM_SIMP_TAC[FINITE_POLYTOPE_FACES] THEN SET_TAC[]]]);;
```

### Informal statement
For any polytope $p$ in $\mathbb{R}^N$ where $N \geq 2$, if the affine hull of $p$ is the hyperplane $\{x \in \mathbb{R}^N \mid x_1 = 0\}$, then the alternating sum of the face counts by dimension satisfies the Euler-Poincaré formula:
$$\sum_{d=0}^{N-1} (-1)^d \cdot |\{f \mid f \text{ face_of } p \text{ and } \text{aff_dim}(f) = d\}| = 1$$

Where:
- $\text{face_of}$ denotes that $f$ is a face of the polytope $p$
- $\text{aff_dim}(f)$ is the affine dimension of the face $f$
- $|\cdot|$ represents the cardinality of a set

### Informal proof
The proof uses a translation of the polytope to apply the existing Euler-Poincaré lemma.

- We apply the Euler-Poincaré lemma to the translated polytope $\{basis_1 + x \mid x \in p\}$, which shifts $p$ to lie in the hyperplane $\{x \mid x_1 = 1\}$.
- The translation preserves the polytope property (by `POLYTOPE_TRANSLATION_EQ`).
- The affine hull of the translated polytope is $\{x \mid x_1 = 1\}$, which follows from `AFFINE_HULL_TRANSLATION`.
- We verify that the translated polytope satisfies the conditions of the Euler-Poincaré lemma.
- For the main equality, we need to show that the face structure and dimensions are preserved under translation.
- Using `FACES_OF_TRANSLATION`, we establish that there is a bijection between faces of the original polytope and faces of the translated polytope.
- Since affine dimension is invariant under translation (`AFF_DIM_TRANSLATION_EQ`), each face maps to a face of the same dimension.
- Therefore, the alternating sum of face counts gives the same result for both polytopes, which is 1 according to the lemma.

### Mathematical insight
The Euler-Poincaré formula is a fundamental result in polyhedral combinatorics, generalizing Euler's formula for polyhedra ($V - E + F = 2$) to higher dimensions. This theorem provides a special case where the polytope lies in a specific affine hyperplane.

The formula connects the combinatorial structure of a polytope (count of faces by dimension) with a topological invariant (Euler characteristic). This relationship is important in discrete geometry and topology.

The special case proven here is useful because many polytope problems can be reduced to this standard form, where the polytope lies in the hyperplane $\{x \mid x_1 = 0\}$. The translation technique demonstrates how to move between different standard representations while preserving the essential combinatorial properties.

### Dependencies
- **Theorems**:
  - `EULER_POINCARE_LEMMA`: The main result for polytopes in the hyperplane $\{x \mid x_1 = 1\}$
  - `FACES_OF_TRANSLATION`: The faces of a translated set correspond to translations of faces of the original set
  - `POLYTOPE_TRANSLATION_EQ`: Translation preserves the polytope property
  - `FINITE_POLYTOPE_FACES`: A polytope has finitely many faces
  - `AFFINE_HULL_TRANSLATION`: Relationship between affine hull and translation
  - `AFF_DIM_TRANSLATION_EQ`: Affine dimension is preserved under translation

- **Definitions**:
  - `face_of`: A face of a convex set
  - `polytope`: A set that is the convex hull of a finite set of points

### Porting notes
When porting this theorem:
- Ensure that the translation operation and its properties are properly defined in the target system.
- Pay attention to the indexing conventions for vector components. HOL Light uses 1-based indexing with `x$1`.
- The sum range `0..dimindex(:N)-1` may need adjustment depending on how dimension indexing works in the target system.
- In HOL Light, `&n` denotes the conversion of a natural number to a real number, which might be handled differently in other systems.

---

## EULER_POINCARE_FULL

### Name of formal statement
EULER_POINCARE_FULL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_POINCARE_FULL = prove
 (`!p:real^N->bool.
        polytope p /\ aff_dim p = &(dimindex(:N))
        ==> sum (0..dimindex(:N))
                (\d. (-- &1) pow d *
                     &(CARD {f | f face_of p /\ aff_dim f = &d })) = &1`,
  REPEAT STRIP_TAC THEN ABBREV_TAC
   `f:real^N->real^(N,1)finite_sum =
          \x. lambda i. if i = 1 then &0 else x$(i-1)` THEN
  ABBREV_TAC `s = IMAGE (f:real^N->real^(N,1)finite_sum) p` THEN
  MP_TAC(ISPEC `s:real^(N,1)finite_sum->bool` EULER_POINCARE_SPECIAL) THEN
  REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; ADD_SUB] THEN
  REWRITE_TAC[DIMINDEX_GE_1; ARITH_RULE `2 <= n + 1 <=> 1 <= n`] THEN
  SUBGOAL_THEN `linear(f:real^N->real^(N,1)finite_sum)` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[linear] THEN
    SIMP_TAC[CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
             LAMBDA_BETA] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "s" THEN
  ASM_SIMP_TAC[POLYTOPE_LINEAR_IMAGE; AFFINE_HULL_LINEAR_IMAGE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_EQ_FULL]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `y:real^(N,1)finite_sum` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^N` SUBST1_TAC) THEN
      EXPAND_TAC "f" THEN SIMP_TAC[LAMBDA_BETA; LE_REFL; DIMINDEX_GE_1];
      DISCH_TAC THEN
      EXISTS_TAC `(lambda i. (y:real^(N,1)finite_sum)$(i+1)):real^N` THEN
      EXPAND_TAC "f" THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA; DIMINDEX_FINITE_SUM; DIMINDEX_1;
       DIMINDEX_GE_1; ARITH_RULE `1 <= i /\ ~(i = 1) ==> 1 <= i - 1`;
       ARITH_RULE `1 <= n /\ i <= n + 1 ==> i - 1 <= n`] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
      ASM_ARITH_TAC];
    DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `!x y. (f:real^N->real^(N,1)finite_sum) x = f y <=> x = y`
    ASSUME_TAC THENL
     [EXPAND_TAC "f" THEN
      ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA; DIMINDEX_FINITE_SUM; DIMINDEX_1;
        DIMINDEX_GE_1; ARITH_RULE `1 <= i /\ ~(i = 1) ==> 1 <= i - 1`;
        ARITH_RULE `1 <= n /\ i <= n + 1 ==> i - 1 <= n`] THEN
      REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `i:num` THENL
       [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i + 1`) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[ADD_SUB] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    EXPAND_TAC "s" THEN
    MP_TAC(ISPECL [`f:real^N->real^(N,1)finite_sum`; `p:real^N->bool`]
        FACES_OF_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[SET_RULE `{f | f face_of s /\ P f} =
                          {f | f IN {f | f face_of s} /\ P f}`] THEN
    ASM_REWRITE_TAC[SET_RULE `{y | y IN IMAGE f s /\ P y} =
                              {f x |x| x IN s /\ P(f x)}`] THEN
    ASM_SIMP_TAC[AFF_DIM_INJECTIVE_LINEAR_IMAGE] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SIMPLE_IMAGE_GEN] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
       `(!x y. Q x y ==> x = y)
        ==> (!x y. P x /\ P y /\ Q x y ==> x = y)`) THEN
      ASM_REWRITE_TAC[INJECTIVE_IMAGE];
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{f:real^N->bool | f face_of p}` THEN
      ASM_SIMP_TAC[FINITE_POLYTOPE_FACES] THEN SET_TAC[]]]);;
```

### Informal statement
For any polytope $p$ in $\mathbb{R}^N$ with affine dimension equal to $N$, the alternating sum of the number of faces of each dimension equals 1. Specifically:

$$\sum_{d=0}^{N} (-1)^d \cdot |F_d| = 1$$

where $F_d = \{f \mid f \text{ face_of } p \text{ and } \text{aff\_dim}(f) = d\}$ is the set of all faces of $p$ with affine dimension $d$.

### Informal proof
We prove this by reduction to the special case where the polytope lies in a hyperplane.

Let's define a linear map $f: \mathbb{R}^N \to \mathbb{R}^{N+1}$ given by:
$$f(x) = \lambda i. \begin{cases} 0 & \text{if } i = 1 \\ x_{i-1} & \text{otherwise} \end{cases}$$

This map essentially embeds $\mathbb{R}^N$ into $\mathbb{R}^{N+1}$ with the first coordinate set to 0. Let $s = f(p)$ be the image of our polytope under this mapping.

We now apply the special case theorem `EULER_POINCARE_SPECIAL` to $s$. We need to verify its preconditions:

1. $\text{dimindex}(\mathbb{R}^{N+1}) \geq 2$, which holds because $\text{dimindex}(\mathbb{R}^N) \geq 1$.
2. $s$ is a polytope, which follows from `POLYTOPE_LINEAR_IMAGE` since $f$ is linear and $p$ is a polytope.
3. $\text{affine hull}(s) = \{x \in \mathbb{R}^{N+1} \mid x_1 = 0\}$, which we can verify by showing both inclusions.

The function $f$ is injective, which we prove by showing that $f(x) = f(y)$ implies $x = y$.

From `FACES_OF_LINEAR_IMAGE`, we know that there is a bijection between the faces of $p$ and the faces of $s$ given by $f$. Furthermore, since $f$ is an injective linear map, it preserves affine dimension: $\text{aff\_dim}(f(t)) = \text{aff\_dim}(t)$ for any face $t$ of $p$.

Therefore, the alternating sum for $s$ equals the alternating sum for $p$, which by the special case equals 1.

### Mathematical insight
The Euler-Poincare formula is a fundamental result in polyhedral combinatorics, providing a topological invariant for convex polytopes. For 3-dimensional polytopes, this reduces to Euler's famous formula $V - E + F = 2$ (after adjusting for the empty face).

This theorem extends the formula to polytopes of arbitrary dimension. The result is remarkable because it shows that regardless of how complicated a polytope's structure might be, this alternating sum always equals 1.

The proof leverages a dimensional embedding technique, reducing the full-dimensional case to a special case where the polytope lies in a hyperplane. This is a common strategy in polytope theory - embedding a problem in a higher dimension to apply known results.

### Dependencies
- **Theorems**:
  - `FACES_OF_LINEAR_IMAGE`: Relates faces of a set to faces of its linear image under an injective linear map
  - `POLYTOPE_LINEAR_IMAGE`: The image of a polytope under a linear map is a polytope
  - `FINITE_POLYTOPE_FACES`: A polytope has finitely many faces
  - `EULER_POINCARE_SPECIAL`: The special case of the Euler-Poincare formula for polytopes in a hyperplane
  
- **Definitions**:
  - `face_of`: Defines when a set is a face of another set
  - `polytope`: A set is a polytope if it is the convex hull of a finite set of points

### Porting notes
When porting this theorem:
1. Ensure your system supports affine dimension calculations with the same semantics as HOL Light
2. The proof relies on manipulations of finite sums, so make sure your system has good support for finite sum operations
3. The lambda-abstraction for the linear map $f$ requires careful handling in systems with different function representation
4. The dimensional embedding technique used here is common, but may require different syntax in other systems

---

## EULER_RELATION

### Name of formal statement
EULER_RELATION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_RELATION = prove
 (`!p:real^3->bool.
        polytope p /\ aff_dim p = &3
        ==> (CARD {v | v face_of p /\ aff_dim(v) = &0} +
             CARD {f | f face_of p /\ aff_dim(f) = &2}) -
            CARD {e | e face_of p /\ aff_dim(e) = &1} = 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `p:real^3->bool` EULER_POINCARE_FULL) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN
  REWRITE_TAC[TOP_DEPTH_CONV num_CONV `3`; SUM_CLAUSES_NUMSEG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LNEG] THEN
  SUBGOAL_THEN `{f:real^3->bool | f face_of p /\ aff_dim f = &3} = {p}`
   (fun th -> SIMP_TAC[th; NOT_IN_EMPTY; FINITE_EMPTY; CARD_CLAUSES])
  THENL
   [MATCH_MP_TAC(SET_RULE
     `P a /\ (!x. P x ==> x = a) ==> {x | P x} = {a}`) THEN
    ASM_SIMP_TAC[FACE_OF_REFL; POLYTOPE_IMP_CONVEX] THEN
    X_GEN_TAC `f:real^3->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^3->bool`; `p:real^3->bool`]
        FACE_OF_AFF_DIM_LT) THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; INT_LT_REFL];
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_LID] THEN
    REWRITE_TAC[REAL_ARITH `((x + --y) + z) + -- &1:real = &1 <=>
                            x + z = y + &2`] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ADD_SUB2]]);;
```

### Informal statement
For any polytope $p$ in $\mathbb{R}^3$ with affine dimension $\text{aff\_dim}(p) = 3$, the following relation holds:
$$\text{CARD}\{v \mid v \text{ face\_of } p \text{ and } \text{aff\_dim}(v) = 0\} + \text{CARD}\{f \mid f \text{ face\_of } p \text{ and } \text{aff\_dim}(f) = 2\} - \text{CARD}\{e \mid e \text{ face\_of } p \text{ and } \text{aff\_dim}(e) = 1\} = 2$$

This is the classic Euler's formula for polyhedra, stating that the number of vertices ($0$-dimensional faces) plus the number of $2$-dimensional faces (actual "faces"), minus the number of edges ($1$-dimensional faces), equals $2$.

### Informal proof
The proof follows from the general Euler-Poincaré formula for polytopes. Here's the structure:

1. Apply the `EULER_POINCARE_FULL` theorem to the polytope $p$.
2. For a polytope in $\mathbb{R}^3$, this theorem states that:
   $$\sum_{d=0}^{3} (-1)^d \cdot |F_d| = 1$$
   where $|F_d|$ is the cardinality of the set of $d$-dimensional faces.

3. Expanding this sum:
   $$|F_0| - |F_1| + |F_2| - |F_3| = 1$$

4. Show that $F_3 = \{p\}$, i.e., the only $3$-dimensional face of $p$ is $p$ itself:
   - $p$ is a face of itself by `FACE_OF_REFL` since polytopes are convex.
   - Any face $f$ of $p$ with affine dimension $3$ must equal $p$. This is shown using `FACE_OF_AFF_DIM_LT`, which states that if $f$ is a proper face of $p$, then its affine dimension is strictly less than that of $p$.

5. Therefore, $|F_3| = 1$, and the equation becomes:
   $$|F_0| - |F_1| + |F_2| - 1 = 1$$

6. Rearranging:
   $$|F_0| + |F_2| = |F_1| + 2$$

Which is precisely the Euler relation for polyhedra in 3D space.

### Mathematical insight
Euler's relation is a fundamental result in combinatorial topology that connects the number of vertices, edges, and faces of a polyhedron (or more generally, a polytope). This relation is invariant under continuous deformations of the polytope, making it a topological invariant.

For convex polyhedra in 3D space, this formula states that $V - E + F = 2$, where $V$ is the number of vertices, $E$ is the number of edges, and $F$ is the number of faces. This result has far-reaching implications in graph theory, topological classification of surfaces, and various areas of mathematics.

The theorem proved here is a special case of the more general Euler-Poincaré formula for polytopes of arbitrary dimension, which is a discrete analog of the Euler characteristic in algebraic topology.

### Dependencies
- **Theorems**:
  - `FACE_OF_REFL`: If a set is convex, then it is a face of itself.
  - `FACE_OF_AFF_DIM_LT`: If $f$ is a proper face of a convex set $s$, then the affine dimension of $f$ is strictly less than that of $s$.
  - `POLYTOPE_IMP_CONVEX`: Every polytope is convex.
  - `EULER_POINCARE_FULL`: The general Euler-Poincaré formula for polytopes.

- **Definitions**:
  - `face_of`: Defines what it means for one set to be a face of another.
  - `polytope`: Defines a polytope as the convex hull of a finite set of points.

### Porting notes
When porting this theorem:
1. Ensure the definition of faces includes all dimensions from 0 to the full dimension of the polytope.
2. The proof relies on the general Euler-Poincaré formula, which should be ported first.
3. The dimensionality handling may differ between systems - pay attention to how the affine dimension is calculated and represented.
4. The identification of $p$ as the only face of itself with full dimension relies on proper handling of the face relation.

---

