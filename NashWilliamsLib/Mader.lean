/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import NashWilliamsLib.Basic

/-!
# Minimally `K`-edge-connected multigraphs have a vertex of degree `K`

If no active edge can be deleted while keeping `Req K T`, then every active edge crosses a
*tight* set (a nonempty proper subset of `T` with cut exactly `K`). An inclusion-minimal tight set
is a single vertex: an active edge inside it would cross another tight set, and uncrossing
(submodularity or posimodularity) would produce a smaller tight set; and without inner edges its
cut would be at least `2K`.
-/

@[expose] public section

open Finset

namespace NashWilliams

variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

/-- A tight set: a nonempty proper subset of `T` whose cut is exactly `K`. -/
def Tight (K : ℕ) (T : Finset V) (ends : ι → V × V) (F : Finset ι) (S : Finset V) : Prop :=
  S ⊆ T ∧ S.Nonempty ∧ S ≠ T ∧ cutF ends F S = K

lemma exists_tight_of_not_req {K : ℕ} {T : Finset V} {ends : ι → V × V} {F : Finset ι}
    (hreq : Req K T ends F) {i : ι} (hi : ¬ Req K T ends (F.erase i)) :
    ∃ S, Tight K T ends F S ∧ (((ends i).1 ∈ S) ≠ ((ends i).2 ∈ S)) := by
  simp only [Req, not_forall, not_le] at hi
  obtain ⟨S, hST, hne, hneT, hlt⟩ := hi
  have h1 := cutF_le_erase_add_one ends F S i
  have h2 := hreq S hST hne hneT
  refine ⟨S, ⟨hST, hne, hneT, by omega⟩, ?_⟩
  intro hc
  rw [cutF_erase_eq ends F S i (not_not.2 hc)] at hlt
  omega

omit [DecidableEq ι] in
/-- Uncrossing step: a tight set `X` containing `a` and `b`, and a tight set `Y` containing `a`
but not `b`, yield a strictly smaller tight set. -/
lemma exists_smaller_tight {K : ℕ} {T : Finset V} {ends : ι → V × V} {F : Finset ι}
    (hreq : Req K T ends F) {X Y : Finset V} (hX : Tight K T ends F X) (hY : Tight K T ends F Y)
    {a b : V} (haX : a ∈ X) (hbX : b ∈ X) (haY : a ∈ Y) (hbY : b ∉ Y) :
    ∃ Z, Tight K T ends F Z ∧ Z.card < X.card := by
  obtain ⟨hXT, hXne, hXT', hXc⟩ := hX
  obtain ⟨hYT, hYne, hYT', hYc⟩ := hY
  by_cases hU : X ∪ Y = T
  · have hpos := cutF_sdiff_add_sdiff ends F X Y
    have hYX : K ≤ cutF ends F (Y \ X) := by
      refine hreq _ (sdiff_subset.trans hYT) ?_ ?_
      · obtain ⟨t, htT, htX⟩ : ∃ t ∈ T, t ∉ X := by
          by_contra! h
          exact hXT' (Subset.antisymm hXT h)
        refine ⟨t, mem_sdiff.2 ⟨?_, htX⟩⟩
        rw [← hU] at htT
        simpa [htX] using htT
      · intro h
        have : a ∈ Y \ X := h ▸ hXT haX
        simp [haX] at this
    have hXY : K ≤ cutF ends F (X \ Y) := by
      refine hreq _ (sdiff_subset.trans hXT) ⟨b, by simp [hbX, hbY]⟩ ?_
      intro h
      have : a ∈ X \ Y := h ▸ hXT haX
      simp [haY] at this
    refine ⟨X \ Y, ⟨sdiff_subset.trans hXT, ⟨b, by simp [hbX, hbY]⟩, ?_, by omega⟩, ?_⟩
    · intro h
      have : a ∈ X \ Y := h ▸ hXT haX
      simp [haY] at this
    · exact card_lt_card ⟨sdiff_subset, fun h => by simpa [haY] using h haX⟩
  · have hsub := cutF_inter_add_union ends F X Y
    have hU' : K ≤ cutF ends F (X ∪ Y) :=
      hreq _ (union_subset hXT hYT) ⟨a, by simp [haX]⟩ hU
    have hI : K ≤ cutF ends F (X ∩ Y) := by
      refine hreq _ (inter_subset_left.trans hXT) ⟨a, by simp [haX, haY]⟩ ?_
      intro h
      have : b ∈ X ∩ Y := h ▸ hXT hbX
      simp [hbY] at this
    refine ⟨X ∩ Y, ⟨inter_subset_left.trans hXT, ⟨a, by simp [haX, haY]⟩, ?_, by omega⟩, ?_⟩
    · intro h
      have : b ∈ X ∩ Y := h ▸ hXT hbX
      simp [hbY] at this
    · exact card_lt_card ⟨inter_subset_left, fun h => by simpa [hbY] using h hbX⟩

/-- **Mader-type lemma.** If `Req K T` holds (with `K ≥ 1` and `|T| ≥ 2`) but fails after deleting
any active edge, then some vertex of `T` has degree exactly `K`. -/
theorem exists_vertex_cutF_eq {K : ℕ} (hK : 1 ≤ K) {T : Finset V} (hT : 1 < T.card)
    {ends : ι → V × V} {F : Finset ι} (hin : Inside T ends F) (hreq : Req K T ends F)
    (hmin : ∀ i ∈ F, ¬ Req K T ends (F.erase i)) : ∃ s ∈ T, cutF ends F {s} = K := by
  have hsing : ∀ x ∈ T, K ≤ cutF ends F {x} := by
    intro x hx
    refine hreq _ (by simpa using hx) (singleton_nonempty x) ?_
    intro h
    rw [← h] at hT
    simp at hT
  -- there is a tight set
  have hex : ∃ S, Tight K T ends F S := by
    rcases F.eq_empty_or_nonempty with hF | ⟨i, hi⟩
    · exfalso
      obtain ⟨x, hx⟩ : T.Nonempty := card_pos.1 (by omega)
      have := hsing x hx
      simp [hF, cutF] at this
      omega
    · obtain ⟨S, hS, -⟩ := exists_tight_of_not_req hreq (hmin i hi)
      exact ⟨S, hS⟩
  classical
  obtain ⟨X, hXmem, hXmin⟩ := (T.powerset.filter fun S => Tight K T ends F S).exists_min_image
    card (by
      obtain ⟨S, hS⟩ := hex
      exact ⟨S, mem_filter.2 ⟨mem_powerset.2 hS.1, hS⟩⟩)
  have hX : Tight K T ends F X := (mem_filter.1 hXmem).2
  have hnosmaller : ∀ Z, Tight K T ends F Z → X.card ≤ Z.card := fun Z hZ =>
    hXmin Z (mem_filter.2 ⟨mem_powerset.2 hZ.1, hZ⟩)
  by_cases h1 : X.card = 1
  · obtain ⟨s, rfl⟩ := card_eq_one.1 h1
    exact ⟨s, hX.1 (mem_singleton_self s), hX.2.2.2⟩
  exfalso
  have h2 : 1 < X.card := by
    have := hX.2.1.card_pos
    omega
  by_cases hinner : ∃ i ∈ F, (ends i).1 ∈ X ∧ (ends i).2 ∈ X
  · obtain ⟨i, hi, ha, hb⟩ := hinner
    obtain ⟨Y, hY, hcr⟩ := exists_tight_of_not_req hreq (hmin i hi)
    by_cases haY : (ends i).1 ∈ Y
    · have hbY : (ends i).2 ∉ Y := fun h => hcr (by simp [haY, h])
      obtain ⟨Z, hZ, hlt⟩ := exists_smaller_tight hreq hX hY ha hb haY hbY
      exact absurd (hnosmaller Z hZ) (not_le.2 hlt)
    · have hbY : (ends i).2 ∈ Y := by
        by_contra h
        exact hcr (by simp [haY, h])
      -- use the complement `T \ Y`, which is also tight
      obtain ⟨hYT, hYne, hYT', hYc⟩ := hY
      have hY' : Tight K T ends F (T \ Y) := by
        refine ⟨sdiff_subset, ?_, ?_, by rw [cutF_sdiff_eq hin]; exact hYc⟩
        · obtain ⟨t, htT, htY⟩ : ∃ t ∈ T, t ∉ Y := by
            by_contra! h
            exact hYT' (Subset.antisymm hYT h)
          exact ⟨t, mem_sdiff.2 ⟨htT, htY⟩⟩
        · intro h
          obtain ⟨y, hy⟩ := hYne
          have : y ∈ T \ Y := by rw [h]; exact hYT hy
          simp [hy] at this
      have haY' : (ends i).1 ∈ T \ Y := mem_sdiff.2 ⟨hX.1 ha, haY⟩
      have hbY' : (ends i).2 ∉ T \ Y := by simp [hbY]
      obtain ⟨Z, hZ, hlt⟩ := exists_smaller_tight hreq hX hY' ha hb haY' hbY'
      exact absurd (hnosmaller Z hZ) (not_le.2 hlt)
  · push Not at hinner
    obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.1 h2
    have := cutF_pair_le hxy hx hy (fun i hi h => hinner i hi h.1 h.2)
    have hx' := hsing x (hX.1 hx)
    have hy' := hsing y (hX.1 hy)
    have := hX.2.2.2
    omega

end NashWilliams
