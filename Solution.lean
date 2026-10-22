/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import NashWilliamsLib.Defs

/-!
# Proofs of the statements in `Challenge.lean`

The definitions are copied verbatim from `Challenge.lean`; each theorem is closed by the
corresponding theorem of `NashWilliamsLib` (namespace `NashWilliams`), whose definitions are
literally the same.
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
    ∃ o : ι → Bool, ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → k ≤ outCut ends o S :=
  NashWilliams.nash_williams k ends hloop hconn

end Multigraph

open Classical in
/-- **Nash-Williams' theorem for simple graphs.** Every finite `2k`-edge-connected simple graph
has an orientation (a `Digraph` with underlying graph `G` and no pair of opposite arcs) in which
every nonempty proper vertex set has at least `k` leaving arcs. -/
theorem nash_williams_simple {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (k : ℕ)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsEdgeConnected (2 * k)) :
    ∃ D : Digraph V, D.toSimpleGraphInclusive = G ∧ (∀ u v, D.Adj u v → ¬ D.Adj v u) ∧
      ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
        k ≤ ((S ×ˢ Sᶜ).filter fun q => D.Adj q.1 q.2).card :=
  NashWilliams.nash_williams_simple k G hG

end NashWilliamsOrientation
