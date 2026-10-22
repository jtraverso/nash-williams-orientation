/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Nash-Williams' weak orientation theorem

C. St. J. A. Nash-Williams, *On orientations, connectivity and odd-vertex-pairings in finite
graphs*, Canad. J. Math. 12 (1960) 555–567: every `2k`-edge-connected finite graph has a
`k`-arc-connected orientation. Statements in the namespace `NashWilliamsOrientation`:

* `nash_williams`: the theorem for finite loopless multigraphs, given by an edge family
  `ends : ι → V × V` (parallel edges allowed); an orientation is a function `o : ι → Bool`.
* `nash_williams_simple`: the case of simple graphs, with Mathlib's `SimpleGraph.IsEdgeConnected`
  and orientations as Mathlib `Digraph`s whose underlying graph
  (`Digraph.toSimpleGraphInclusive`) is `G` and which never contain both `u → v` and `v → u`.

The definitions `cut` and `outCut` below are part of the audited statements; the Mathlib
definitions used are reproduced in `MATHLIB_DEFINITIONS.md`.
-/

@[expose] public section

namespace NashWilliamsOrientation

section Multigraph

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]

/-- Number of edges with exactly one endpoint in `S` (the edge cut `d(S)`). -/
def cut (ends : ι → V × V) (S : Finset V) : ℕ :=
  (Finset.univ.filter fun i => ((ends i).1 ∈ S) ≠ ((ends i).2 ∈ S)).card

/-- Arcs leaving `S` when edge `i` is oriented `(ends i).1 → (ends i).2` if `o i` and the other
way otherwise. -/
def outCut (ends : ι → V × V) (o : ι → Bool) (S : Finset V) : ℕ :=
  (Finset.univ.filter fun i =>
    if o i then (ends i).1 ∈ S ∧ (ends i).2 ∉ S else (ends i).2 ∈ S ∧ (ends i).1 ∉ S).card

/-- **Nash-Williams' weak orientation theorem.** A finite loopless multigraph, given by an edge
family `ends : ι → V × V`, in which every nonempty proper vertex set is left by at least `2k`
edges has an orientation `o : ι → Bool` in which every such set is left by at least `k` arcs. -/
theorem nash_williams (k : ℕ) (ends : ι → V × V) (hloop : ∀ i, (ends i).1 ≠ (ends i).2)
    (hconn : ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → 2 * k ≤ cut ends S) :
    ∃ o : ι → Bool, ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → k ≤ outCut ends o S := by
  sorry

end Multigraph

open Classical in
/-- **Nash-Williams' theorem for simple graphs.** Every finite `2k`-edge-connected simple graph
has an orientation (a `Digraph` with underlying graph `G` and no pair of opposite arcs) in which
every nonempty proper vertex set has at least `k` leaving arcs. -/
theorem nash_williams_simple {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (k : ℕ)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsEdgeConnected (2 * k)) :
    ∃ D : Digraph V, D.toSimpleGraphInclusive = G ∧ (∀ u v, D.Adj u v → ¬ D.Adj v u) ∧
      ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
        k ≤ ((S ×ˢ Sᶜ).filter fun q => D.Adj q.1 q.2).card := by
  sorry

end NashWilliamsOrientation
