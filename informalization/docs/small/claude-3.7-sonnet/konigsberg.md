# konigsberg.ml

## Overview

Number of statements: 18

This file formalizes the classic Eulerian path problem for the bridges of Königsberg, proving the impossibility of finding a path that crosses each bridge exactly once. It uses graph theory to formalize the problem, defines the necessary graph structures representing the Königsberg bridges configuration, and proves that no Eulerian path exists because the graph contains vertices with odd degree. The proof demonstrates a fundamental result in graph theory that was historically one of the first applications of mathematical reasoning to topology and networks.

## edges

### Name of formal statement
edges

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let edges = new_definition
  `edges(E:E->bool,V:V->bool,Ter:E->V->bool) = E`;;
```

### Informal statement
The function `edges` is defined for a graph represented by a triple $(E, V, Ter)$ where:
- $E$ is a set of edges (represented as a predicate on type $E$)
- $V$ is a set of vertices (represented as a predicate on type $V$)
- $Ter$ is a terminal relation mapping edges to vertices

The function is defined as:
$\text{edges}(E, V, Ter) = E$

In other words, `edges` simply extracts the edge set from a graph representation.

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
This is a simple selector function that extracts the set of edges from a graph representation. In HOL Light, graphs are represented as triples containing the set of edges, the set of vertices, and a terminal relation that specifies how edges connect to vertices.

This definition is part of a formalization of graph theory used to prove the impossibility of finding an Eulerian path for the bridges of Königsberg problem. The function provides a convenient way to access the edge set from a graph structure without having to use tuple projection operations directly.

In the Königsberg bridges problem, we need to analyze the edges (bridges) of the graph to determine if an Eulerian path exists.

### Dependencies
#### Definitions
- `edges` (self-referential)

### Porting notes
This is a trivial definition that should be straightforward to port to any system. In systems with native tuple support and projection functions, you might not need this definition at all and could use the built-in projection instead.

---

## vertices

### Name of formal statement
vertices

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let vertices = new_definition
  `vertices(E:E->bool,V:V->bool,Ter:E->V->bool) = V`;;
```

### Informal statement
The definition `vertices` states that for a graph represented by the triple $(E, V, Ter)$ where:
- $E$ is a predicate on edges (type $E \to \text{bool}$)
- $V$ is a predicate on vertices (type $V \to \text{bool}$)
- $Ter$ is a relation between edges and vertices (type $E \to V \to \text{bool}$)

The function `vertices` simply returns the set of vertices $V$.

Formally: $\text{vertices}(E, V, Ter) = V$

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
This definition is part of a graph representation framework where a graph is represented as a triple consisting of:
1. A set of edges $E$
2. A set of vertices $V$
3. A relation $Ter$ that connects edges to vertices (the incidence relation)

The `vertices` function is a simple accessor/projection function that extracts the vertex set from this triple. This representation allows for flexible modeling of graphs in formal systems, where the vertex set can be accessed directly when needed.

This definition is likely used in the formalization of graph theory problems such as the famous Seven Bridges of Königsberg problem (as suggested by the filename "konigsberg.ml").

### Dependencies
#### Definitions
- `vertices` - Self-reference to this definition

### Porting notes
This is a straightforward definition to port to other proof assistants. The main consideration would be ensuring that the type variables (`E` and `V`) are properly handled in the target system, as different proof assistants have different approaches to polymorphism and type inference.

If the target system uses a different approach to representing graphs (such as adjacency lists or matrices), this accessor function might need to be adapted accordingly.

---

## termini

### Name of formal statement
termini

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let termini = new_definition
  `termini(E:E->bool,V:V->bool,Ter:E->V->bool) = Ter`;;
```

### Informal statement
The function `termini` is defined as:

For sets of edges $E \subseteq \mathcal{E}$, vertices $V \subseteq \mathcal{V}$, and a terminal relation $\text{Ter} : \mathcal{E} \to \mathcal{V} \to \text{bool}$:

$$\text{termini}(E, V, \text{Ter}) = \text{Ter}$$

This definition simply returns the terminal relation from the inputs. The terminal relation $\text{Ter}$ indicates which vertices are endpoints (terminals) of which edges.

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
This definition is part of a graph theory formalization. It extracts the incidence relation between edges and vertices from a graph representation.

In graph theory, we often need to work with the relationship between edges and their endpoints. The `termini` function provides direct access to this relation, which is useful for many graph algorithms and proofs. It's a simple accessor function that makes it easier to refer to the terminal relation when working with graphs.

The definition is particularly useful in the context of the Königsberg bridge problem or when working with Eulerian paths, where understanding which vertices are connected by edges is crucial.

### Dependencies
#### Definitions
- `termini` (self-referential)

### Porting notes
This is a straightforward definition that should be easy to port to any proof assistant. It's essentially defining an accessor function to extract the terminal relation from a graph representation. In some systems, this might be implemented as a record projection or a simple function definition.

---

## graph

### Name of formal statement
graph

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let graph = new_definition
 `graph G <=>
        !e. e IN edges(G)
            ==> ?a b. a IN vertices(G) /\ b IN vertices(G) /\
                      termini G e = {a,b}`;;
```

### Informal statement
A structure $G$ is a graph if and only if for every edge $e$ in the set of edges of $G$ (denoted by $\text{edges}(G)$), there exist two vertices $a$ and $b$ in the set of vertices of $G$ (denoted by $\text{vertices}(G)$) such that the termini of edge $e$ in $G$ (given by $\text{termini } G \, e$) is exactly the set $\{a,b\}$.

Formally:
$$\text{graph } G \iff \forall e. e \in \text{edges}(G) \Rightarrow \exists a,b. a \in \text{vertices}(G) \land b \in \text{vertices}(G) \land \text{termini } G \, e = \{a,b\}$$

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
This definition formalizes the concept of an undirected graph in HOL Light. The definition captures several important aspects:

1. A graph $G$ is represented as a triple consisting of:
   - A set of edges $\text{edges}(G)$
   - A set of vertices $\text{vertices}(G)$
   - A termini function $\text{termini}(G)$ that maps each edge to its endpoint vertices

2. The definition enforces that every edge must connect exactly two vertices from the vertex set.

3. The representation uses sets to define the endpoints of edges (rather than ordered pairs), which makes the graph undirected by definition - there is no distinction between the "start" and "end" of an edge.

4. This definition allows for a general treatment of graphs where the types of edges and vertices can be arbitrary, providing flexibility in applications.

This definition is canonical in graph theory and serves as the foundation for developing theorems about undirected graphs in the HOL Light library.

### Dependencies
- **Definitions**:
  - `vertices`: Extracts the vertex set from a graph triple
  - `edges`: Extracts the edge set from a graph triple
  - `termini`: Extracts the terminus function from a graph triple

### Porting notes
When porting this definition to other proof assistants:

1. Ensure the representation of the graph as a triple (edge set, vertex set, termini function) is maintained or appropriately translated.

2. Pay attention to how set membership and equality are handled in the target system.

3. The termini function maps an edge to the set of its endpoints (exactly two vertices). In some systems, you might need to explicitly state that the set has exactly two elements or use a different representation for the endpoints.

4. Type parameters should be preserved: vertices and edges can have different types in this definition.

---

## TERMINI_IN_VERTICES

### Name of formal statement
TERMINI_IN_VERTICES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TERMINI_IN_VERTICES = prove
 (`!G e v. graph G /\ e IN edges(G) /\ v IN termini G e ==> v IN vertices G`,
  REWRITE_TAC[graph; EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;
```

### Informal statement
For any graph $G$, edge $e$, and vertex $v$, if $G$ is a graph, $e$ is an edge of $G$, and $v$ is a terminus of edge $e$ in $G$, then $v$ is a vertex of $G$.

More formally, $\forall G, e, v: \text{graph}(G) \land e \in \text{edges}(G) \land v \in \text{termini}(G, e) \Rightarrow v \in \text{vertices}(G)$.

### Informal proof
The proof directly follows from the definition of a graph. By definition, a graph $G$ satisfies the condition that for any edge $e \in \text{edges}(G)$, there exist vertices $a$ and $b$ in $\text{vertices}(G)$ such that $\text{termini}(G, e) = \{a, b\}$.

Therefore, if $v \in \text{termini}(G, e)$, then $v$ must be either $a$ or $b$, both of which are in $\text{vertices}(G)$.

The proof uses:
- `REWRITE_TAC` to expand the definition of `graph` and set operations
- `MESON_TAC` to complete the proof by first-order reasoning

### Mathematical insight
This theorem establishes a basic property of graphs: the endpoints (termini) of any edge in a graph must be vertices of that graph. This is a fundamental constraint in graph theory that ensures the coherence of the graph structure.

In the formalization, a graph is represented as a triple $(E, V, Ter)$ where $E$ is the set of edges, $V$ is the set of vertices, and $Ter$ maps each edge to its set of endpoints. The theorem confirms that this representation correctly maintains the basic property that edge endpoints are vertices.

### Dependencies
#### Definitions
- `vertices`: Extracts the vertex set from a graph representation
- `edges`: Extracts the edge set from a graph representation
- `termini`: Extracts the terminus mapping from a graph representation
- `graph`: Defines what it means for a triple to be a graph

### Porting notes
When porting this theorem to other systems, ensure that your graph representation maintains the property that edges can only connect vertices that are part of the graph. Different systems may represent graphs differently (e.g., as adjacency matrices, adjacency lists, or edge lists), but this fundamental property should be preserved.

---

## connects

### Name of formal statement
connects

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let connects = new_definition
 `connects G e (a,b) <=> termini G e = {a,b}`;;
```

### Informal statement
A graph edge $e$ connects vertices $a$ and $b$ in graph $G$ if and only if the terminals of edge $e$ are exactly the set $\{a, b\}$.

Formally, for a graph $G$, an edge $e$, and vertices $a$ and $b$:
$$\text{connects}(G, e, (a, b)) \iff \text{termini}(G, e) = \{a, b\}$$

### Informal proof
This is a definition, not a theorem requiring proof.

### Mathematical insight
This definition formalizes the standard notion of an edge connecting two vertices in a graph. It uses the `termini` function which gives the set of vertices that an edge connects to. The definition states that an edge connects exactly two vertices if and only if its termini set contains precisely those two vertices.

In graph theory, an edge typically connects exactly two vertices (in an undirected simple graph). This definition is used as a fundamental building block for graph theory formalization in HOL Light, particularly for problems like the Königsberg bridge problem where connectivity between vertices via edges is essential.

### Dependencies
- Definitions:
  - `termini` - Represents the terminals or endpoints of edges in a graph

### Porting notes
When porting this definition:
- Ensure that the `termini` function is properly defined first
- Note that this definition assumes the representation of an edge connecting vertices as an ordered pair $(a,b)$
- The definition uses equality with a two-element set, which may need appropriate set theory support in the target system

---

## delete_edge

### Name of formal statement
delete_edge

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let delete_edge = new_definition
 `delete_edge e (E,V,Ter) = (E DELETE e,V,Ter)`;;
```

### Informal statement
The function `delete_edge` takes an edge $e$ and a graph represented as a triple $(E, V, Ter)$ where:
- $E$ is the set of edges
- $V$ is the set of vertices
- $Ter$ is the terminal function

It returns a new graph $(E \setminus \{e\}, V, Ter)$ which is identical to the original graph except that the edge $e$ has been removed from the set of edges $E$.

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
This definition provides a basic graph operation for removing a single edge from a graph while preserving the vertex set and terminal function. This is a fundamental operation in graph theory that allows for the modification of a graph's structure without altering its vertices.

The operation is particularly useful in various graph algorithms and proofs, such as when analyzing connectivity properties or when working with spanning trees. In the context of the Königsberg bridge problem (suggested by the file name), removing edges can be used to analyze whether certain paths are possible after removing specific bridges.

### Dependencies
#### Definitions
- `delete_edge`: The definition itself

### Porting notes
When porting this definition:
1. Ensure the target system has set operations, particularly the set difference operation (`DELETE` in HOL Light corresponds to set difference in other systems)
2. The graph representation as a triple $(E, V, Ter)$ should be maintained with the appropriate types

---

## DELETE_EDGE_CLAUSES

I'll revise the documentation according to your feedback, changing "Informal proof" to "Informal sketch" while maintaining the same high-quality content.

### DELETE_EDGE_CLAUSES
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DELETE_EDGE_CLAUSES = prove
 (`(!G. edges(delete_edge e G) = (edges G) DELETE e) /\
   (!G. vertices(delete_edge e G) = vertices G) /\
   (!G. termini(delete_edge e G) = termini G)`,
  REWRITE_TAC[FORALL_PAIR_THM; delete_edge; edges; vertices; termini]);;
```

### Informal statement
This theorem states the following properties of the `delete_edge` operation on a graph:

1. For any graph $G$, the set of edges of the graph after deleting edge $e$ equals the original set of edges with $e$ removed:
   $\forall G. \text{edges}(\text{delete\_edge}(e, G)) = \text{edges}(G) \setminus \{e\}$

2. For any graph $G$, the set of vertices remains unchanged after deleting an edge:
   $\forall G. \text{vertices}(\text{delete\_edge}(e, G)) = \text{vertices}(G)$

3. For any graph $G$, the function mapping edges to their incident vertices remains unchanged after deleting an edge:
   $\forall G. \text{termini}(\text{delete\_edge}(e, G)) = \text{termini}(G)$

### Informal sketch
The proof is straightforward by rewriting using the definitions of `delete_edge`, `edges`, `vertices`, and `termini`, along with `FORALL_PAIR_THM` which allows decomposing the universally quantified graph $G$ into its components.

Specifically, a graph in this formalization is represented as a triple $(E, V, Ter)$ where:
- $E$ represents the set of edges
- $V$ represents the set of vertices
- $Ter$ is the function mapping edges to their incident vertices

The `delete_edge e (E, V, Ter)` operation is defined as $(E \setminus \{e\}, V, Ter)$, which only modifies the edge set while preserving the vertex set and the edge-vertex incidence mapping.

### Mathematical insight
This theorem establishes the fundamental properties of the edge deletion operation in a graph. It confirms that:

1. Edge deletion only affects the edge set in the expected way
2. Edge deletion preserves the vertex set 
3. Edge deletion preserves the incidence relation between edges and vertices

These properties ensure that edge deletion behaves as expected in graph theory and are essential for reasoning about graph modifications such as those used in algorithms like Euler path finding, network flow problems, or proving structural results in graph theory.

### Dependencies
- **Definitions:**
  - `vertices`: Extracts the vertex set from a graph represented as a triple
  - `edges`: Extracts the edge set from a graph represented as a triple
  - `termini`: Extracts the edge-vertex incidence mapping from a graph represented as a triple
  - `delete_edge`: Removes an edge from a graph while preserving its vertices and incidence relation
- **Theorems:**
  - `FORALL_PAIR_THM`: Allows reasoning about universally quantified tuples by breaking them into components

### Porting notes
When porting to other systems:
- Ensure the graph representation (as a triple) is properly set up
- The theorem is quite straightforward and should translate easily to any system with basic set operations
- The `DELETE` operation in HOL Light corresponds to set difference and would be represented by operations like `\` or `difference` in other systems

---

## GRAPH_DELETE_EDGE

### Name of formal statement
GRAPH_DELETE_EDGE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let GRAPH_DELETE_EDGE = prove
 (`!G e. graph G ==> graph(delete_edge e G)`,
  REWRITE_TAC[graph; DELETE_EDGE_CLAUSES; IN_DELETE] THEN MESON_TAC[]);;
```

### Informal statement
For any graph $G$ and any edge $e$, if $G$ is a graph, then the graph with edge $e$ deleted, denoted by $\text{delete\_edge}(e, G)$, is also a graph.

More formally: $\forall G, e. \, \text{graph}(G) \Rightarrow \text{graph}(\text{delete\_edge}(e, G))$

### Informal proof
The proof follows directly from the definitions of graph and delete_edge:

1. We first expand the definitions of `graph`, `DELETE_EDGE_CLAUSES`, and `IN_DELETE` using `REWRITE_TAC`.
   
2. After expanding these definitions, we have:
   - A graph $G$ is defined as a structure where for any edge $e$ in the edge set, there exist vertices $a$ and $b$ in the vertex set such that the termini of $e$ are $\{a,b\}$.
   - `DELETE_EDGE_CLAUSES` tells us that:
     - The edges of $\text{delete\_edge}(e, G)$ are exactly the edges of $G$ with $e$ removed.
     - The vertices and termini functions remain unchanged when we delete an edge.
   - `IN_DELETE` specifies the membership condition for a set with an element removed.

3. After these rewrites, the MESON (Model Elimination Search for Natural deduction) automated theorem prover completes the proof.

The key insight is that deleting an edge preserves the graph property because:
- Any remaining edge was already in the original graph
- The vertices and termini remain unchanged
- Therefore, any edge in the new graph still has proper termini in the vertex set

### Mathematical insight
This theorem establishes that the operation of deleting an edge from a graph preserves the "graph-ness" property. This is a fundamental result in graph theory, confirming that edge deletion is a well-defined operation that yields another valid graph.

The definition of `graph` used here emphasizes the relationship between edges and vertices via the termini function, which maps each edge to the set of its endpoints. The theorem shows that removing an edge doesn't break this relationship for the remaining edges.

This result is important for algorithms and proofs that involve incrementally removing edges from graphs, such as in spanning tree algorithms or in the study of graph minors.

### Dependencies
- **Theorems**:
  - `DELETE_EDGE_CLAUSES`: States how the edge deletion operation affects the components of a graph (edges, vertices, termini).
  
- **Definitions**:
  - `graph`: Defines what constitutes a valid graph structure.
  - `delete_edge`: Defines the operation of removing an edge from a graph.

### Porting notes
When porting to other proof assistants:
- Ensure that the graph representation is compatible. HOL Light represents a graph as a triple (E,V,Ter) where E is the edge set, V is the vertex set, and Ter maps edges to their termini.
- The proof relies heavily on the MESON tactic, which is a powerful automated theorem prover in HOL Light. Other systems might need a more explicit proof or different automated tactics.
- The theorem is straightforward but depends on the specific representation of graphs, so adapting the representation might require adjusting the proof accordingly.

---

## locally_finite

### Name of formal statement
locally_finite

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let locally_finite = new_definition
 `locally_finite G <=>
     !v. v IN vertices(G) ==> FINITE {e | e IN edges G /\ v IN termini G e}`;;
```

### Informal statement
A graph $G$ is locally finite if and only if for all vertices $v$ in $G$, the set of edges that have $v$ as an endpoint is finite.

Formally, $\text{locally\_finite}(G) \iff \forall v \in \text{vertices}(G).\ \text{FINITE}(\{e \mid e \in \text{edges}(G) \land v \in \text{termini}(G)(e)\})$

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
Local finiteness is a fundamental property of graphs that ensures every vertex is incident to only finitely many edges. This property is particularly important in infinite graph theory, as it allows for various induction techniques and algorithms to be applied locally even when the graph itself is infinite.

In many graph algorithms, local finiteness ensures that vertex-based operations terminate in finite time. For instance, in the Königsberg bridge problem context where this definition appears, local finiteness would ensure that each land mass connects to only finitely many bridges, making path-finding problems tractable.

Unlike global finiteness (finite number of vertices and edges), local finiteness permits infinite graphs while maintaining a "reasonable" structure around each vertex.

### Dependencies
#### Definitions
- `vertices`: Extracts the vertex set from a graph representation
- `edges`: Extracts the edge set from a graph representation  
- `termini`: Provides the relation between edges and their endpoint vertices

### Porting notes
When porting this definition:
1. Ensure your target system has a suitable representation of graphs that separates vertices, edges, and the incidence relation (termini)
2. Verify that your target system has a built-in notion of finiteness for sets
3. The set-builder notation `{e | e IN edges G /\ v IN termini G e}` represents the set of edges incident to vertex v, which may need explicit construction in some systems

---

## localdegree

### Name of formal statement
localdegree

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let localdegree = new_definition
 `localdegree G v e =
        if termini G e = {v} then 2
        else if v IN termini G e then 1
        else 0`;;
```

### Informal statement
The `localdegree` function specifies the contribution of a single edge $e$ to the degree of a vertex $v$ in a graph $G$. It is defined as:

$$\text{localdegree}(G, v, e) = 
\begin{cases}
2 & \text{if}~\text{termini}(G)_e = \{v\} \\
1 & \text{if}~v \in \text{termini}(G)_e \\
0 & \text{otherwise}
\end{cases}$$

Where $\text{termini}(G)_e$ represents the set of vertices that are endpoints of edge $e$.

### Informal proof
This is a definition, not a theorem, so no proof is provided.

### Mathematical insight
This definition captures the local contribution of an edge to a vertex's degree in graph theory. The key insight is the distinction between three cases:

1. When the edge $e$ is a loop (self-loop) at vertex $v$ (i.e., its only endpoint is $v$), it contributes 2 to the degree.
2. When the vertex $v$ is one of the endpoints of edge $e$ but not the only one, it contributes 1 to the degree.
3. When the vertex $v$ is not an endpoint of edge $e$, it contributes 0 to the degree.

This definition follows the standard convention in graph theory where loops contribute twice to a vertex's degree, reflecting that both "ends" of the edge are incident to the same vertex. The total degree of a vertex would be calculated by summing the `localdegree` over all edges in the graph.

### Dependencies
#### Definitions
- `termini`: Represents the function mapping edges to their endpoint vertices in a graph.

### Porting notes
When porting this definition:
- Ensure the system handles the case distinction properly (the nested if-then-else structure)
- Verify that the graph representation in the target system supports loops (self-loops)
- Ensure consistency with how the termini function is implemented in the target system

---

## degree

### degree
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let degree = new_definition
 `degree G v = nsum {e | e IN edges G /\ v IN termini G e} (localdegree G v)`;;
```

### Informal statement
The degree of a vertex $v$ in a graph $G$ is defined as the sum of the local degrees of $v$ over all edges $e$ in $G$ where $v$ is a terminus of $e$:

$$\text{degree}(G, v) = \sum_{e \in \{e \mid e \in \text{edges}(G) \wedge v \in \text{termini}(G, e)\}} \text{localdegree}(G, v, e)$$

where:
- $\text{edges}(G)$ denotes the set of all edges in graph $G$
- $\text{termini}(G, e)$ represents the set of vertices that are endpoints of edge $e$
- $\text{localdegree}(G, v, e)$ gives the contribution of edge $e$ to the degree of vertex $v$, which is:
  - 2 if $v$ is the only terminus of $e$ (a loop)
  - 1 if $v$ is one of multiple termini of $e$ (a regular edge connection)
  - 0 if $v$ is not a terminus of $e$

### Informal proof
This is a definition, not a theorem, so no proof is required.

### Mathematical insight
This definition captures the notion of vertex degree in a graph that can include both regular edges and loops. The key insight is handling special cases like self-loops differently from regular edges:

1. For a regular edge connecting two different vertices, each vertex gets a degree contribution of 1
2. For a self-loop (an edge that connects a vertex to itself), the vertex gets a degree contribution of 2

This definition is designed to maintain the handshaking lemma in graph theory, which states that the sum of all vertex degrees in a graph is equal to twice the number of edges.

The use of `nsum` (numeric sum) over the set of relevant edges allows for a concise formal definition that handles both regular edges and loops uniformly.

### Dependencies
- **Definitions:**
  - `edges` - extracts the edge set from a graph structure
  - `termini` - provides the set of endpoint vertices for a given edge
  - `localdegree` - determines the contribution of an edge to a vertex's degree based on the edge type
  - `nsum` (built-in) - sums numeric values over a set

### Porting notes
When porting this definition:
- Ensure your target system has support for summation over sets
- Pay attention to how graphs are represented in the target system, as this definition assumes a specific graph representation with edges, vertices, and a termini relation
- The handling of self-loops with a degree contribution of 2 is a common convention but might need explicit documentation in some systems

---

## DEGREE_DELETE_EDGE

### DEGREE_DELETE_EDGE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DEGREE_DELETE_EDGE = prove
 (`!G e:E v:V.
        graph G /\ locally_finite G /\ e IN edges(G)
        ==> degree G v =
                if termini G e = {v} then degree (delete_edge e G) v + 2
                else if v IN termini G e then degree (delete_edge e G) v + 1
                else degree (delete_edge e G) v`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[degree; DELETE_EDGE_CLAUSES; IN_DELETE] THEN
  SUBGOAL_THEN
   `{e:E | e IN edges G /\ (v:V) IN termini G e} =
        if v IN termini G e
        then e INSERT {e' | (e' IN edges G /\ ~(e' = e)) /\ v IN termini G e'}
        else {e' | (e' IN edges G /\ ~(e' = e)) /\ v IN termini G e'}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION] THEN GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_INSERT] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(v:V) IN termini G (e:E)` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    COND_CASES_TAC THENL [ASM_MESON_TAC[IN_SING; EXTENSION]; ALL_TAC] THEN
    MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM; localdegree] THEN
    REWRITE_TAC[DELETE_EDGE_CLAUSES]] THEN
  SUBGOAL_THEN
   `FINITE {e':E | (e' IN edges G /\ ~(e' = e)) /\ (v:V) IN termini G e'}`
   (fun th -> SIMP_TAC[NSUM_CLAUSES; th])
  THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{e:E | e IN edges G /\ (v:V) IN termini G e}` THEN
    SIMP_TAC[IN_ELIM_THM; SUBSET] THEN
    ASM_MESON_TAC[locally_finite; TERMINI_IN_VERTICES];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[localdegree] THEN
  SUBGOAL_THEN
   `nsum {e':E | (e' IN edges G /\ ~(e' = e)) /\ (v:V) IN termini G e'}
         (localdegree (delete_edge e G) v) =
    nsum {e' | (e' IN edges G /\ ~(e' = e)) /\ v IN termini G e'}
         (localdegree G v)`
  SUBST1_TAC THENL
   [ALL_TAC; COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC] THEN
  MATCH_MP_TAC NSUM_EQ THEN SIMP_TAC[localdegree; DELETE_EDGE_CLAUSES]);;
```

### Informal statement
For any graph $G$, edge $e$, and vertex $v$, if $G$ is a graph that is locally finite and $e$ is an edge in $G$, then the degree of vertex $v$ in $G$ is:
- $\text{degree}(G \setminus e, v) + 2$ if the termini of edge $e$ is exactly $\{v\}$ (i.e., $e$ is a self-loop at $v$)
- $\text{degree}(G \setminus e, v) + 1$ if $v$ is one of the termini of edge $e$ but not the only one (i.e., $e$ connects $v$ to another vertex)
- $\text{degree}(G \setminus e, v)$ if $v$ is not a terminus of edge $e$ (i.e., $e$ is not incident to $v$)

Here, $G \setminus e$ denotes the graph obtained by deleting edge $e$ from $G$.

### Informal proof
The proof shows how the degree of a vertex changes when an edge is removed from a graph:

1. First, we rewrite the degree definition and use properties of edge deletion.

2. We establish that the set of edges in $G$ incident to $v$ can be decomposed into:
   - If $v$ is a terminus of $e$, then this set equals $\{e\} \cup \{e' \in E(G) : e' \neq e \text{ and } v \in \text{termini}(G,e')\}$
   - Otherwise, it equals $\{e' \in E(G) : e' \neq e \text{ and } v \in \text{termini}(G,e')\}$

3. We then consider two cases:
   - Case 1: $v$ is a terminus of $e$
     - We prove the finiteness of the set $\{e' \in E(G) : e' \neq e \text{ and } v \in \text{termini}(G,e')\}$ using the locally finite property
     - Using properties of numeric summation, we split the degree calculation into the contribution from $e$ and the contribution from other edges
     - Then we establish that for all edges $e' \neq e$, the local degree contribution in $G \setminus e$ is the same as in $G$
     - Finally, we handle two subcases:
       - When $\text{termini}(G,e) = \{v\}$ (self-loop), we add 2 to the degree
       - When $v$ is just one of the termini of $e$, we add 1 to the degree

   - Case 2: $v$ is not a terminus of $e$
     - We show that deleting $e$ doesn't change the degree of $v$

4. The conclusion follows by arithmetic reasoning based on the different cases.

### Mathematical insight
This theorem establishes a precise relationship between the degree of a vertex in a graph and the degree of the same vertex after deleting an edge. The result provides three clear cases that completely characterize how deleting an edge affects vertex degrees:

1. Deleting a self-loop (an edge connecting a vertex to itself) reduces that vertex's degree by 2.
2. Deleting an edge connected to a vertex reduces that vertex's degree by 1.
3. Deleting an edge not connected to a vertex leaves that vertex's degree unchanged.

This result is fundamental in graph theory and is particularly useful in inductive arguments about graphs, where one might proceed by edge deletion. It's also essential for algorithm analysis when considering edge removal operations in graphs.

### Dependencies
- **Definitions**:
  - `degree`: The degree of a vertex in a graph, defined as the sum of local degrees over all edges incident to the vertex
  - `edges`: Accessor function to get the set of edges in a graph
  - `termini`: Accessor function to get the endpoints (termini) of an edge in a graph
  - `graph`: Predicate that characterizes a valid graph structure
  - `delete_edge`: Function that removes an edge from a graph
  - `locally_finite`: Property that each vertex has a finite number of incident edges
  - `localdegree`: Function that gives the contribution of an edge to a vertex's degree

- **Theorems**:
  - `DELETE_EDGE_CLAUSES`: Properties of the edge deletion operation
  - `TERMINI_IN_VERTICES`: States that the termini of an edge are vertices of the graph

### Porting notes
When porting this theorem:
1. Ensure your graph representation supports self-loops (edges where both endpoints are the same vertex)
2. Be careful with the definition of degree, especially how self-loops contribute to vertex degree (they add 2 to the degree)
3. The theorem depends on the graph being locally finite - this may be an implicit assumption in some graph libraries
4. The proof makes heavy use of set manipulation and sum operations over filtered sets

---

## eulerian_RULES,eulerian_INDUCT,eulerian_CASES

### Name of formal statement
eulerian_RULES, eulerian_INDUCT, eulerian_CASES

### Type of the formal statement
new_inductive_definition

### Formal Content
```ocaml
let eulerian_RULES,eulerian_INDUCT,eulerian_CASES = new_inductive_definition
 `(!G a. a IN vertices G /\ edges G = {} ==> eulerian G [] (a,a)) /\
  (!G a b c e es. e IN edges(G) /\ connects G e (a,b) /\
                  eulerian (delete_edge e G) es (b,c)
                  ==> eulerian G (CONS e es) (a,c))`;;
```

### Informal statement
The relation `eulerian G es (a,c)` is inductively defined to mean that `es` is an Eulerian path in graph `G` from vertex `a` to vertex `c`. The inductive definition consists of two rules:

1. Base case: For any graph `G` and vertex `a`, if `a` is in the vertices of `G` and the set of edges of `G` is empty, then there is an Eulerian path in `G` represented by the empty list `[]` from `a` to itself.

2. Inductive case: For any graph `G`, vertices `a`, `b`, `c`, edge `e`, and list of edges `es`, if:
   - `e` is in the edges of `G`
   - `e` connects vertices `a` and `b` in `G`
   - There is an Eulerian path `es` in the graph obtained by deleting edge `e` from `G`, from vertex `b` to vertex `c`
   
   Then there is an Eulerian path represented by `CONS e es` (i.e., `e` followed by `es`) in graph `G` from vertex `a` to vertex `c`.

### Informal proof
This is an inductive definition, not a theorem with a proof. The definition introduces the `eulerian` relation and specifies the rules for when this relation holds.

### Mathematical insight
An Eulerian path in a graph is a path that traverses every edge of the graph exactly once (but may visit vertices multiple times). This definition captures the concept inductively:

- The base case handles graphs with no edges, where the only possible Eulerian path is the empty path from a vertex to itself.
- The inductive case builds an Eulerian path by starting with an edge `e` from `a` to `b`, and then following an existing Eulerian path from `b` to some vertex `c` in the graph with `e` removed.

This definition is particularly elegant because it naturally ensures that:
1. Every edge is traversed exactly once (as each edge is deleted after being traversed)
2. The path is connected (the endpoint of each edge is the starting point of the next segment of the path)

The standard theorem associated with Eulerian paths, Euler's theorem, states that a connected graph has an Eulerian path if and only if it has at most two vertices of odd degree, and if there are exactly two such vertices, they must be the start and end vertices of the path.

### Dependencies
#### Definitions
- `vertices`: Returns the vertex set `V` of a graph represented as triple `(E,V,Ter)`
- `edges`: Returns the edge set `E` of a graph represented as triple `(E,V,Ter)`
- `connects`: Defines when an edge connects two vertices
- `delete_edge`: Removes an edge from a graph

### Porting notes
When porting this definition to other proof assistants:
1. Ensure the underlying graph representation is compatible
2. Note that HOL Light represents a graph as a triple `(E,V,Ter)` where:
   - `E` is the set of edges
   - `V` is the set of vertices
   - `Ter` is a relation that associates edges with their terminal vertices
3. The inductive definition generates three theorems:
   - `eulerian_RULES`: The basic rules for the relation
   - `eulerian_INDUCT`: The induction principle
   - `eulerian_CASES`: A case analysis theorem
4. In systems with dependent types, the graph structure might be represented differently

---

## EULERIAN_FINITE

### Name of formal statement
EULERIAN_FINITE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULERIAN_FINITE = prove
 (`!G es ab. eulerian G es ab ==> FINITE (edges G)`,
  MATCH_MP_TAC eulerian_INDUCT THEN
  SIMP_TAC[DELETE_EDGE_CLAUSES; FINITE_DELETE; FINITE_RULES]);;
```

### Informal statement
For any graph $G$, edge sequence $es$, and vertex pair $ab$, if $G$ is Eulerian with respect to $es$ and $ab$ (meaning $es$ forms an Eulerian path in $G$ from vertex $a$ to vertex $b$), then the set of edges in $G$ is finite.

Formally: $\forall G, es, ab. \text{eulerian}(G, es, ab) \Rightarrow \text{FINITE}(\text{edges}(G))$

### Informal proof
The proof uses induction on the Eulerian path structure:

- The proof applies `eulerian_INDUCT`, which allows for induction on the structure of Eulerian paths.

- After applying induction, the proof simplifies using:
  * `DELETE_EDGE_CLAUSES` which states that deleting an edge from a graph removes it from the edge set but preserves vertices and termini
  * `FINITE_DELETE` which states that removing an element from a finite set produces a finite set
  * `FINITE_RULES` which contains basic finiteness properties

- The induction shows that each smaller Eulerian path acts on a graph with one fewer edge, and since the base case has a finite number of edges, the original graph must also have a finite edge set.

### Mathematical insight
This theorem establishes that any graph containing an Eulerian path must be finite in terms of its edge set. This is important because:

1. It confirms that the Eulerian property is only meaningful for finite graphs
2. It's a necessary condition for algorithms that seek Eulerian paths
3. It connects the existence of an Eulerian path with the structural property of finiteness

The result might seem intuitively obvious since an Eulerian path must traverse each edge exactly once, but formally establishing this property is essential for the mathematical foundation of graph theory in a proof assistant.

### Dependencies
- **Theorems**:
  * `eulerian_INDUCT`: Induction principle for Eulerian paths
  * `DELETE_EDGE_CLAUSES`: Properties preserved when deleting an edge from a graph
  * `FINITE_DELETE`: Removing an element from a finite set yields a finite set
  * `FINITE_RULES`: Basic rules about finite sets
  
- **Definitions**:
  * `edges`: Extracts the edge set from a graph representation
  * `eulerian`: Defines when a graph has an Eulerian path

### Porting notes
When porting this theorem:
- Ensure the graph representation in your target system matches HOL Light's triplet structure (edges, vertices, termini)
- The induction principle for Eulerian paths will need to be established first
- The finiteness properties needed are standard in most proof assistants, but the exact theorems may have different names

---

## EULERIAN_ODD_LEMMA

### EULERIAN_ODD_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULERIAN_ODD_LEMMA = prove
 (`!G:(E->bool)#(V->bool)#(E->V->bool) es ab.
        eulerian G es ab
        ==> graph G
            ==> FINITE(edges G) /\
                !v. v IN vertices G
                    ==> (ODD(degree G v) <=>
                         ~(FST ab = SND ab) /\ (v = FST ab \/ v = SND ab))`,
  MATCH_MP_TAC eulerian_INDUCT THEN CONJ_TAC THENL
   [SIMP_TAC[degree; NOT_IN_EMPTY; SET_RULE `{x | F} = {}`] THEN
    SIMP_TAC[NSUM_CLAUSES; FINITE_RULES; ARITH];
    ALL_TAC] THEN
  SIMP_TAC[GRAPH_DELETE_EDGE; FINITE_DELETE; DELETE_EDGE_CLAUSES] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  ASM_SIMP_TAC[GRAPH_DELETE_EDGE] THEN STRIP_TAC THEN
  X_GEN_TAC `v:V` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:(E->bool)#(V->bool)#(E->V->bool)`; `e:E`; `v:V`]
                DEGREE_DELETE_EDGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[locally_finite] THEN GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `edges(G:(E->bool)#(V->bool)#(E->V->bool))` THEN
    ASM_SIMP_TAC[SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`G:(E->bool)#(V->bool)#(E->V->bool)`; `e:E`]
         TERMINI_IN_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [connects]) THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_CASES_TAC `b:V = a` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[SET_RULE `{a,a} = {v} <=> v = a`] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[ODD_ADD; ARITH];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[SET_RULE `{a,b} = {v} <=> a = b /\ a = v`] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[ODD_ADD; ARITH] THEN ASM_MESON_TAC[]);;
```

### Informal statement
For any graph $G$ with edge type $E$ and vertex type $V$, Euler path $es$, and pair of vertices $ab$, if $G$ has an Eulerian path $es$ starting at vertex $a$ and ending at vertex $b$ (represented by the pair $ab$), and $G$ is a valid graph, then:

1. The set of edges in $G$ is finite, and
2. For any vertex $v$ in $G$, the degree of $v$ is odd if and only if the starting and ending vertices are different (i.e., $a \neq b$) and $v$ is either the starting vertex $a$ or the ending vertex $b$.

### Informal proof
The proof proceeds by induction on the Eulerian path structure:

* **Base case**: For the empty graph with no edges, the result holds trivially:
  - The degree of any vertex is 0, which is even.
  - The only possible Eulerian path is from a vertex to itself, making the start and end vertices the same.

* **Inductive step**: Assume the result holds for a graph with an Eulerian path after removing an edge $e$.
  - We know that removing an edge preserves the graph property and finiteness.
  - For any vertex $v$ in the graph, we analyze how removing an edge affects its degree using `DEGREE_DELETE_EDGE`:
    
    If $e$ connects vertices $a$ and $b$ (i.e., $\text{termini}\ G\ e = \{a, b\}$):
    
    1. If $a = b$ (self-loop):
       - If $v = a$, then $\text{degree}\ G\ v = \text{degree}\ (G \setminus e)\ v + 2$
       - Since adding 2 preserves oddness/evenness, $v$ has odd degree iff its degree was odd after removing $e$
      
    2. If $a \neq b$:
       - If $v = a$ or $v = b$, then $\text{degree}\ G\ v = \text{degree}\ (G \setminus e)\ v + 1$
       - If $v \neq a$ and $v \neq b$, then $\text{degree}\ G\ v = \text{degree}\ (G \setminus e)\ v$
      
    The proof then uses properties of odd numbers and the induction hypothesis to show that a vertex has odd degree if and only if it is a distinct start or end vertex of the Eulerian path.

### Mathematical insight
This lemma captures a fundamental property of Eulerian paths: in a graph with an Eulerian path, exactly two vertices (the start and end) have odd degree, unless the path starts and ends at the same vertex (in which case all vertices have even degree).

This is a crucial component of the characterization of Eulerian graphs. It's sometimes referred to as the "odd vertex theorem" and forms part of the basis for solving problems like the Seven Bridges of Königsberg, which was historically one of the first graph theory problems.

The result provides a necessary condition for a graph to have an Eulerian path: it must have either zero or exactly two vertices of odd degree. When there are two odd-degree vertices, they must be the start and end of any Eulerian path.

### Dependencies
- **Definitions**:
  - `degree`: defines the degree of a vertex in a graph
  - `vertices`: extracts the vertex set from a graph
  - `edges`: extracts the edge set from a graph
  - `graph`: defines what constitutes a valid graph
  - `connects`: defines when an edge connects two vertices
  - `locally_finite`: ensures that each vertex is incident to finitely many edges

- **Theorems**:
  - `TERMINI_IN_VERTICES`: ensures termini of edges are vertices
  - `DELETE_EDGE_CLAUSES`: describes properties after edge deletion
  - `GRAPH_DELETE_EDGE`: graph property preserved after edge deletion
  - `DEGREE_DELETE_EDGE`: relationship between vertex degree before/after edge deletion

### Porting notes
When porting this theorem:
1. Ensure your system has an appropriate graph representation with vertices, edges, and a terminus function.
2. The degree definition (sum of local degrees) should be consistent.
3. Pay attention to the inductive structure of Eulerian paths.
4. The proof relies on parity properties of integer addition (odd+1=even, even+1=odd, etc.).
5. Set operations and finite set handling are needed for managing edges and vertices.

---

## EULERIAN_ODD

### EULERIAN_ODD

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let EULERIAN_ODD = prove
 (`!G es a b.
        graph G /\ eulerian G es (a,b)
        ==> !v. v IN vertices G
                ==> (ODD(degree G v) <=> ~(a = b) /\ (v = a \/ v = b))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP EULERIAN_ODD_LEMMA) THEN
  ASM_SIMP_TAC[FST; SND]);;
```

### Informal statement
For all graphs $G$, edge sequences $es$, and vertices $a$ and $b$:
If $G$ is a graph and there exists an Eulerian path $es$ from vertex $a$ to vertex $b$ in $G$, then for any vertex $v$ in $G$, the degree of $v$ is odd if and only if $a \neq b$ and $v$ is either $a$ or $b$.

### Informal proof
The proof is straightforward, relying on a previously established lemma:

* First, we take the given premises that $G$ is a graph and $es$ is an Eulerian path from $a$ to $b$.
* We then apply `EULERIAN_ODD_LEMMA`, which states essentially the same result but expresses $a$ and $b$ as components of a pair $(a,b)$.
* Finally, we simplify the result by replacing the `FST` and `SND` operations (which extract the first and second components of a pair) to match our desired conclusion.

The key insight is that we're reformulating a result about pairs into one about individual vertices $a$ and $b$.

### Mathematical insight
This theorem captures a fundamental property of Eulerian paths: in a graph with an Eulerian path, exactly two vertices (the start and end vertices) have odd degree, unless the path is a cycle (where start equals end), in which case all vertices have even degree.

This is a classic result in graph theory and is crucial for characterizing when a graph admits an Eulerian path. The "Seven Bridges of Königsberg" problem, famously solved by Euler, relates to this theorem by showing that if a graph has more than two vertices with odd degree, it cannot have an Eulerian path.

### Dependencies
#### Theorems
- `EULERIAN_ODD_LEMMA`: Establishes the same result but with the endpoints represented as a pair.

#### Definitions
- `graph`: Defines what constitutes a graph in this formalization.
- `vertices`: Returns the vertex set of a graph.
- `degree`: The number of edges incident to a vertex in a graph.

### Porting notes
When porting this theorem:
- Ensure your definition of "Eulerian path" correctly captures the requirement that it traverses every edge exactly once.
- The formalization of graph structure might differ between systems; adjust accordingly by ensuring all components (edges, vertices, termini function) have appropriate representations.
- Different systems may have different conventions for representing ordered pairs and accessing their components.

---

## KOENIGSBERG

### KOENIGSBERG
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let KOENIGSBERG = prove
 (`!G. vertices(G) = {0,1,2,3} /\
       edges(G) = {10,20,30,40,50,60,70} /\
       termini G (10) = {0,1} /\
       termini G (20) = {0,2} /\
       termini G (30) = {0,3} /\
       termini G (40) = {1,2} /\
       termini G (50) = {1,2} /\
       termini G (60) = {2,3} /\
       termini G (70) = {2,3}
       ==> ~(?es a b. eulerian G es (a,b))`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `G:(num->bool)#(num->bool)#(num->num->bool)` EULERIAN_ODD) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[graph] THEN GEN_TAC THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[SET_RULE
     `{a,b} = {x,y} <=> a = x /\ b = y \/ a = y /\ b = x`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  SIMP_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  ASM_REWRITE_TAC[degree; edges] THEN
  SIMP_TAC[TAUT `a IN s /\ k IN t <=> ~(a IN s ==> ~(k IN t))`] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  SIMP_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH] THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN
  REWRITE_TAC[SET_RULE `{x | x = a \/ P(x)} = a INSERT {x | P(x)}`] THEN
  REWRITE_TAC[SET_RULE `{x | x = a} = {a}`] THEN
  SIMP_TAC[NSUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH] THEN
  ASM_REWRITE_TAC[localdegree; IN_INSERT; NOT_IN_EMPTY; ARITH] THEN
  REWRITE_TAC[SET_RULE `{a,b} = {x} <=> x = a /\ a = b`] THEN
  DISCH_THEN(fun th ->
   MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th) THEN
   MP_TAC(SPEC `2` th) THEN MP_TAC(SPEC `3` th)) THEN
  REWRITE_TAC[ARITH] THEN ARITH_TAC);;
```

### Informal statement
This theorem formally proves the impossibility of the Königsberg bridge problem. It states:

For any graph $G$ with:
- Vertices $\{0, 1, 2, 3\}$ (representing the four land masses)
- Edges $\{10, 20, 30, 40, 50, 60, 70\}$ (representing the seven bridges)
- Edge connections as follows:
  - Edge 10 connects vertices 0 and 1
  - Edge 20 connects vertices 0 and 2
  - Edge 30 connects vertices 0 and 3
  - Edge 40 connects vertices 1 and 2
  - Edge 50 connects vertices 1 and 2
  - Edge 60 connects vertices 2 and 3
  - Edge 70 connects vertices 2 and 3

There does not exist any sequence of edges $es$ and vertices $a$ and $b$ such that $G$ has an Eulerian path from $a$ to $b$ (i.e., a path that traverses each edge exactly once).

### Informal proof
The proof uses Euler's criterion for Eulerian paths, which relates to the parity of vertex degrees:

1. We first apply the EULERIAN_ODD theorem, which states that in a graph with an Eulerian path, odd degree vertices can only be the start and end points, and if those are different, there must be exactly two odd degree vertices.

2. The proof then calculates the degree of each vertex in the Königsberg graph:
   - Vertex 0 has degree 3 (connects to edges 10, 20, 30)
   - Vertex 1 has degree 3 (connects to edges 10, 40, 50)
   - Vertex 2 has degree 5 (connects to edges 20, 40, 50, 60, 70)
   - Vertex 3 has degree 3 (connects to edges 30, 60, 70)

3. Since all four vertices have odd degree, an Eulerian path cannot exist because an Eulerian path requires either:
   - All vertices with even degree (for a closed Eulerian circuit), or
   - Exactly two vertices with odd degree (for an open Eulerian path)

4. The contradiction is established by arithmetic, showing that the degree pattern (3,3,5,3) violates the necessary condition for an Eulerian path.

### Mathematical insight
This theorem formalizes Euler's famous solution to the Königsberg bridge problem from 1736, which is often considered the birth of graph theory. The key insight is that the possibility of traversing all edges exactly once depends solely on the parity of vertex degrees - not on the specific layout of edges.

The Königsberg bridge problem was historically significant because Euler recognized that the geometric layout was irrelevant, and instead abstracted the problem into a graph where only the connections (not distances or angles) mattered. This demonstrated the power of mathematical abstraction.

The specific graph represents the actual arrangement of bridges and land masses in 18th-century Königsberg (modern Kaliningrad):
- Vertex 0 represents the island Kneiphof
- Vertices 1, 2, and 3 represent the three mainland areas
- The seven edges represent the seven bridges connecting these land masses

This result is canonical in graph theory as the first application of mathematical abstraction to solve a practical problem about physical paths.

### Dependencies
- Theorems:
  - `EULERIAN_ODD`: Relates the parity of vertex degrees to the existence of Eulerian paths
- Definitions:
  - `graph`: Defines what constitutes a graph
  - `vertices`: Extracts the vertex set from a graph
  - `edges`: Extracts the edge set from a graph
  - `termini`: Specifies which vertices an edge connects
  - `degree`: The number of edges incident to a vertex
  - `localdegree`: The contribution of a specific edge to a vertex's degree

### Porting notes
When porting this theorem:
- The graph representation in HOL Light uses a triple (E,V,Ter) where E is the edge set, V is the vertex set, and Ter maps edges to their endpoint sets. Other systems might use different graph representations.
- The proof relies heavily on set operations and arithmetic reasoning, which should be straightforward to port.
- The specific numeric values for vertices (0,1,2,3) and edges (10,20,...) are arbitrary; any distinct values would work.

---

