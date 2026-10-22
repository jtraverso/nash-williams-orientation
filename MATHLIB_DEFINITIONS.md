# Mathlib definitions used by Nash-Williams' orientation theorem

Verbatim excerpts of the Mathlib definitions used by the statements in `Challenge.lean`, at the
pinned Mathlib revision `c55e6e786f49471c72fbddbec5415808896aec1e` (tag `v4.35.0-rc3`, repository
https://github.com/leanprover-community/mathlib4). Mathlib is released under the Apache-2.0
licence. Each excerpt gives the file and line at that revision; the complete source is at
`https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/<file>`.

These excerpts are provided so that the meaning of every imported notion used by the
Challenge can be audited without fetching Mathlib.

## Finset.card

`Mathlib/Data/Finset/Card.lean`, line 47:

```lean
/-- `s.card` is the number of elements of `s`, aka its cardinality.

The notation `#s` can be accessed in the `Finset` locale. -/
def card (s : Finset α) : ℕ :=
  Multiset.card s.1
```

## Finset.filter

`Mathlib/Data/Finset/Filter.lean`, line 52:

```lean
/-- `Finset.filter p s` is the set of elements of `s` that satisfy `p`.

For example, one can use `s.filter (· ∈ t)` to get the intersection of `s` with `t : Set α`
as a `Finset α` (when a `DecidablePred (· ∈ t)` instance is available). -/
def filter (s : Finset α) : Finset α :=
  ⟨_, s.2.filter p⟩
```

## SimpleGraph

`Mathlib/Combinatorics/SimpleGraph/Basic.lean`, line 95:

```lean
/-- A simple graph is an irreflexive symmetric relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent vertices;
see `SimpleGraph.edgeSet` for the corresponding edge set.
-/
@[ext, aesop safe constructors (rule_sets := [SimpleGraph]), wikidata Q141488]
structure SimpleGraph (V : Type u) where
  /-- The adjacency relation of a simple graph. -/
  Adj : V → V → Prop
  symm : Std.Symm Adj := by aesop_graph
  loopless : Std.Irrefl Adj := by aesop_graph
```

## SimpleGraph.fromRel

`Mathlib/Combinatorics/SimpleGraph/Basic.lean`, line 137:

```lean
/-- Construct the simple graph induced by the given relation. It
symmetrizes the relation and makes it irreflexive. -/
def SimpleGraph.fromRel {V : Type u} (r : V → V → Prop) : SimpleGraph V where
  Adj a b := a ≠ b ∧ (r a b ∨ r b a)
```

## SimpleGraph.edgeSetEmbedding

`Mathlib/Combinatorics/SimpleGraph/Basic.lean`, line 477:

```lean
def edgeSetEmbedding (V : Type*) : SimpleGraph V ↪o Set (Sym2 V) :=
  OrderEmbedding.ofMapLEIff (fun G => Sym2.fromRel G.symm) fun _ _ =>
    ⟨fun h a b => @h s(a, b), fun h e => Sym2.ind @h e⟩
```

## SimpleGraph.edgeSet

`Mathlib/Combinatorics/SimpleGraph/Basic.lean`, line 483:

```lean
/-- `G.edgeSet` is the edge set for `G`.
This is an abbreviation for `edgeSetEmbedding G` that permits dot notation. -/
abbrev edgeSet (G : SimpleGraph V) : Set (Sym2 V) := edgeSetEmbedding V G
```

## Digraph

`Mathlib/Combinatorics/Digraph/Basic.lean`, line 48:

```lean
/--
A digraph is a relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.

In this treatment, a digraph may have self-loops.
-/
@[ext]
structure Digraph (V : Type*) where
  /-- The adjacency relation of a digraph. -/
  Adj : V → V → Prop
```

## Digraph.toSimpleGraphInclusive

`Mathlib/Combinatorics/Digraph/Orientation.lean`, line 51:

```lean
/--
Orientation-forgetting map from `Digraph` to `SimpleGraph` that gives an unoriented edge if
either orientation is present.
-/
def toSimpleGraphInclusive (G : Digraph V) : SimpleGraph V := SimpleGraph.fromRel G.Adj
```

## SimpleGraph.deleteEdges

`Mathlib/Combinatorics/SimpleGraph/DeleteEdges.lean`, line 46:

```lean
/-- Given a set of vertex pairs, remove all of the corresponding edges from the
graph's edge set, if present.

See also: `SimpleGraph.Subgraph.deleteEdges`. -/
def deleteEdges (s : Set (Sym2 V)) : SimpleGraph V := G \ fromEdgeSet s
```

## SimpleGraph.Walk

`Mathlib/Combinatorics/SimpleGraph/Walk/Basic.lean`, line 54:

```lean
/-- A walk is a sequence of adjacent vertices.  For vertices `u v : V`,
the type `walk u v` consists of all walks starting at `u` and ending at `v`.

We say that a walk *visits* the vertices it contains.  The set of vertices a
walk visits is `SimpleGraph.Walk.support`.

See `SimpleGraph.Walk.nil'` and `SimpleGraph.Walk.cons'` for patterns that
can be useful in definitions since they make the vertices explicit. -/
inductive Walk : V → V → Type u
  | nil {u : V} : Walk u u
  | cons {u v w : V} (h : G.Adj u v) (p : Walk v w) : Walk u w
  deriving DecidableEq
```

## SimpleGraph.Reachable

`Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean`, line 52:

```lean
/-- Two vertices are *reachable* if there is a walk between them.
This is equivalent to `Relation.ReflTransGen` of `G.Adj`.
See `SimpleGraph.reachable_iff_reflTransGen`. -/
def Reachable (u v : V) : Prop := Nonempty (G.Walk u v)
```

## SimpleGraph.Preconnected

`Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean`, line 228:

```lean
/-- A graph is preconnected if every pair of vertices is reachable from one another. -/
def Preconnected : Prop := ∀ u v : V, G.Reachable u v
```

## SimpleGraph.Connected

`Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean`, line 314:

```lean
/-- A graph is connected if it's preconnected and contains at least one vertex.
This follows the convention observed by mathlib that something is connected iff it has
exactly one connected component.

There is a `CoeFun` instance so that `h u v` can be used instead of `h.Preconnected u v`. -/
@[mk_iff]
structure Connected : Prop where
  protected preconnected : G.Preconnected
  protected [nonempty : Nonempty V]
```

## SimpleGraph.IsEdgeReachable

`Mathlib/Combinatorics/SimpleGraph/Connectivity/EdgeConnectivity.lean`, line 33:

```lean
/-- Two vertices are `k`-edge-reachable if they remain reachable after removing strictly fewer than
`k` edges. -/
def IsEdgeReachable : Prop :=
  ∀ ⦃s : Set (Sym2 V)⦄, s.encard < k → (G.deleteEdges s).Reachable u v
```

## SimpleGraph.IsEdgeConnected

`Mathlib/Combinatorics/SimpleGraph/Connectivity/EdgeConnectivity.lean`, line 38:

```lean
/-- A graph is `k`-edge-connected if any two vertices are `k`-edge-reachable. -/
def IsEdgeConnected : Prop := ∀ u v, G.IsEdgeReachable k u v
```

