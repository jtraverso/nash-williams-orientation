/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import NashWilliamsLib.Orientation

/-!
# Nash-Williams' weak orientation theorem

C. St. J. A. Nash-Williams, *On orientations, connectivity and odd-vertex-pairings in finite
graphs*, Canad. J. Math. 12 (1960) 555–567: every `2k`-edge-connected finite (multi)graph has a
`k`-arc-connected orientation.

* `NashWilliams.nash_williams`: the statement for loopless multigraphs given by an edge family
  `ends : ι → V × V`; an orientation is a function `o : ι → Bool`.
* `NashWilliams.nash_williams_simple`: the corollary for simple graphs, in the conventions of
  `Challenge.lean` (orientations are `Digraph`s with `toSimpleGraphInclusive = G`, and
  `SimpleGraph.IsEdgeConnected`).

The proof (`NashWilliamsLib/Orientation.lean`) is by induction on the number of edges,
using Mader's lemma on minimally `2k`-edge-connected graphs (`Mader.lean`) and Lovász's splitting
lemma (`Splitting.lean`).
-/

@[expose] public section

open Finset

namespace NashWilliams

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

omit [Fintype V] in
lemma outCut_eq_outCutF (ends : ι → V × V) (o : ι → Bool) (S : Finset V) :
    outCut ends o S = outCutF ends o Finset.univ S := by
  unfold outCut outCutF
  congr 1
  ext i
  rw [mem_filter, mem_filter]
  rfl

/-- **Nash-Williams' weak orientation theorem (1960).** Every `2k`-edge-connected finite loopless
multigraph has a `k`-arc-connected orientation. (The looplessness hypothesis `_hloop` is part of
the requested statement; the proof does not need it, since loops never cross a cut, hence the
underscore in its name.) -/
theorem nash_williams (k : ℕ) (ends : ι → V × V) (_hloop : ∀ i, (ends i).1 ≠ (ends i).2)
    (hconn : ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → 2 * k ≤ cut ends S) :
    ∃ o : ι → Bool, ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → k ≤ outCut ends o S := by
  classical
  obtain ⟨o, ho⟩ := exists_orientation k _ Finset.univ ends Finset.univ rfl
    (fun _ _ => ⟨mem_univ _, mem_univ _⟩) (fun S _ hne hneT => by
      have := hconn S hne hneT
      unfold cut at this
      unfold cutF
      convert this using 2)
  exact ⟨o, fun S hne hneT => by
    rw [outCut_eq_outCutF]
    convert ho S (subset_univ S) hne hneT using 2⟩

end Multigraph

section Simple

variable {V : Type*} (G : SimpleGraph V)

/-- The edge family of a simple graph: each edge with a chosen ordering of its endpoints. -/
noncomputable def edgeEnds (e : G.edgeSet) : V × V := Quot.out (e : Sym2 V)

lemma mk_edgeEnds (e : G.edgeSet) : s((edgeEnds G e).1, (edgeEnds G e).2) = (e : Sym2 V) :=
  Quot.out_eq _

lemma adj_edgeEnds (e : G.edgeSet) : G.Adj (edgeEnds G e).1 (edgeEnds G e).2 := by
  have h := e.2
  rwa [← mk_edgeEnds G e, SimpleGraph.mem_edgeSet] at h

lemma edgeEnds_eq_or {e : G.edgeSet} {a b : V} (h : (e : Sym2 V) = s(a, b)) :
    edgeEnds G e = (a, b) ∨ edgeEnds G e = (b, a) := by
  have := mk_edgeEnds G e
  rw [h] at this
  rcases (Sym2.mk_eq_mk_iff (q := (a, b))).1 this with h | h
  · exact Or.inl h
  · exact Or.inr h

lemma edge_eq_of_edgeEnds {e e' : G.edgeSet} {a b : V}
    (h : edgeEnds G e = (a, b) ∨ edgeEnds G e = (b, a))
    (h' : edgeEnds G e' = (a, b) ∨ edgeEnds G e' = (b, a)) : e = e' := by
  apply Subtype.ext
  rw [← mk_edgeEnds G e, ← mk_edgeEnds G e']
  rcases h with h | h <;> rcases h' with h' | h' <;> rw [h, h'] <;> simp [Sym2.eq_swap]

/-- A `2k`-edge-connected simple graph has every edge cut of size at least `2k`. -/
lemma two_mul_le_cut_edgeEnds [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {k : ℕ}
    (hG : G.IsEdgeConnected (2 * k)) {S : Finset V}
    (hne : S.Nonempty) (hneT : S ≠ Finset.univ) : 2 * k ≤ cut (edgeEnds G) S := by
  by_contra hlt
  push Not at hlt
  set C : Finset (Sym2 V) := (Finset.univ.filter fun e : G.edgeSet =>
    ((edgeEnds G e).1 ∈ S) ≠ ((edgeEnds G e).2 ∈ S)).image Subtype.val with hC
  have hCcard : C.card < 2 * k := lt_of_le_of_lt card_image_le hlt
  obtain ⟨u, hu⟩ := hne
  obtain ⟨v, hv⟩ : ∃ v, v ∉ S := by
    by_contra! h
    exact hneT (eq_univ_of_forall h)
  have hr : (G.deleteEdges (C : Set (Sym2 V))).Reachable u v := hG u v (by
    rw [Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast hCcard)
  obtain ⟨p⟩ := hr
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart (S : Set V) (by simpa using hu)
    (by simpa using hv)
  have hadj := d.adj
  rw [SimpleGraph.deleteEdges_adj] at hadj
  obtain ⟨hadj, hnot⟩ := hadj
  apply hnot
  have hd1' : d.fst ∈ S := by simpa using hd1
  have hd2' : d.snd ∉ S := by simpa using hd2
  refine mem_image.2 ⟨⟨s(d.fst, d.snd), hadj⟩, mem_filter.2 ⟨mem_univ _, ?_⟩, rfl⟩
  rcases edgeEnds_eq_or G (e := ⟨s(d.fst, d.snd), hadj⟩) rfl with h | h <;> rw [h] <;>
    simp [hd1', hd2']

/-- The digraph obtained from an orientation `o` of the edge family `edgeEnds G`. -/
def toDigraph (o : G.edgeSet → Bool) : Digraph V where
  Adj a b := ∃ e : G.edgeSet, if o e then edgeEnds G e = (a, b) else edgeEnds G e = (b, a)

lemma toDigraph_adj_ends {o : G.edgeSet → Bool} {a b : V} (h : (toDigraph G o).Adj a b) :
    ∃ e : G.edgeSet, edgeEnds G e = (a, b) ∨ edgeEnds G e = (b, a) := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, ?_⟩
  split at he
  · exact Or.inl he
  · exact Or.inr he

lemma toDigraph_toSimpleGraphInclusive (o : G.edgeSet → Bool) :
    (toDigraph G o).toSimpleGraphInclusive = G := by
  ext a b
  simp only [Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · obtain ⟨e, he | he⟩ := toDigraph_adj_ends G h
      · simpa [he] using adj_edgeEnds G e
      · simpa [he] using (adj_edgeEnds G e).symm
    · obtain ⟨e, he | he⟩ := toDigraph_adj_ends G h
      · simpa [he] using (adj_edgeEnds G e).symm
      · simpa [he] using adj_edgeEnds G e
  · intro h
    refine ⟨G.ne_of_adj h, ?_⟩
    set e : G.edgeSet := ⟨s(a, b), h⟩
    rcases edgeEnds_eq_or G (e := e) rfl with he | he <;> cases ho : o e
    · exact Or.inr ⟨e, by simp [ho, he]⟩
    · exact Or.inl ⟨e, by simp [ho, he]⟩
    · exact Or.inl ⟨e, by simp [ho, he]⟩
    · exact Or.inr ⟨e, by simp [ho, he]⟩

lemma toDigraph_antisymm (o : G.edgeSet → Bool) (a b : V) (h : (toDigraph G o).Adj a b) :
    ¬ (toDigraph G o).Adj b a := by
  rintro ⟨e', he'⟩
  obtain ⟨e, he⟩ := h
  have hab : a ≠ b := by
    obtain ⟨e0, h0 | h0⟩ := toDigraph_adj_ends G ⟨e, he⟩
    · simpa [h0] using G.ne_of_adj (adj_edgeEnds G e0)
    · simpa [h0] using (G.ne_of_adj (adj_edgeEnds G e0)).symm
  have hee : e = e' := by
    refine edge_eq_of_edgeEnds G (a := a) (b := b) ?_ ?_
    · split at he
      · exact Or.inl he
      · exact Or.inr he
    · split at he'
      · exact Or.inr he'
      · exact Or.inl he'
  subst hee
  by_cases ho : o e
  · simp only [ho, ↓reduceIte] at he he'
    rw [he] at he'
    exact hab (Prod.ext_iff.1 he').1
  · simp only [ho, Bool.false_eq_true, ↓reduceIte] at he he'
    rw [he] at he'
    exact hab (Prod.ext_iff.1 he').2

open Classical in
lemma outCut_le_card [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (o : G.edgeSet → Bool)
    (S : Finset V) :
    outCut (edgeEnds G) o S ≤
      ((S ×ˢ Sᶜ).filter fun q : V × V => (toDigraph G o).Adj q.1 q.2).card := by
  classical
  unfold outCut
  let f : G.edgeSet → V × V := fun e => if o e then edgeEnds G e else (edgeEnds G e).swap
  have hf : ∀ e, s((f e).1, (f e).2) = e := by
    intro e
    by_cases ho : o e
    · simp only [f, ho, ↓reduceIte]
      exact mk_edgeEnds G e
    · simp only [f, ho, Bool.false_eq_true, ↓reduceIte, Prod.fst_swap, Prod.snd_swap]
      rw [Sym2.eq_swap, mk_edgeEnds]
  refine card_le_card_of_injOn f (fun e he => ?_) (fun e _ e' _ hee => ?_)
  · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at he
    simp only [coe_filter, mem_product, mem_compl, Set.mem_ofPred_eq]
    by_cases ho : o e
    · simp only [ho, ↓reduceIte] at he
      refine ⟨⟨by simp [f, ho, he.1], by simp [f, ho, he.2]⟩, e, by simp [f, ho]⟩
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at he
      refine ⟨⟨by simp [f, ho, he.1], by simp [f, ho, he.2]⟩, e, by simp [f, ho]⟩
  · apply Subtype.ext
    rw [← hf e, ← hf e', hee]

open Classical in
/-- **Nash-Williams' weak orientation theorem for simple graphs.** Every finite
`2k`-edge-connected simple graph has an orientation in which every nonempty proper vertex set has
at least `k` leaving arcs. (The hypothesis `[Nonempty V]` is part of the requested statement; the
proof does not need it.) The filter in the conclusion is over a predicate on an arbitrary digraph
`D`, so its decidability is provided classically (`open Classical in`). -/
theorem nash_williams_simple {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (k : ℕ)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsEdgeConnected (2 * k)) :
    ∃ D : Digraph V, D.toSimpleGraphInclusive = G ∧ (∀ u v, D.Adj u v → ¬ D.Adj v u) ∧
      ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
        k ≤ ((S ×ˢ Sᶜ).filter fun q => D.Adj q.1 q.2).card := by
  obtain ⟨o, ho⟩ := nash_williams k (edgeEnds G)
    (fun e => G.ne_of_adj (adj_edgeEnds G e))
    (fun S hne hneT => two_mul_le_cut_edgeEnds G hG hne hneT)
  exact ⟨toDigraph G o, toDigraph_toSimpleGraphInclusive G o, toDigraph_antisymm G o,
    fun S hne hneT => (ho S hne hneT).trans (outCut_le_card G o S)⟩

end Simple

end NashWilliams
