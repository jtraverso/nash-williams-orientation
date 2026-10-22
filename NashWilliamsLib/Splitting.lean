/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import NashWilliamsLib.Basic

/-!
# Lovász's splitting lemma

Let `s ∈ T` have even positive degree, all active edges lie in `T`, and suppose every nonempty
proper subset of `T \ {s}` has cut at least `K ≥ 2` (cuts are computed in the whole graph, so
this is the usual requirement on all sets separating two vertices of `T \ {s}`). Then there are two
active edges `su`, `sv` whose *splitting off* (replacing them by a single edge `uv`) preserves
the requirement (`exists_split`).

Proof: fix an edge `su`. If no edge `sv` works, every other neighbour `v` of `s` lies, together
with `u`, in a *dangerous* set (cut at most `K + 1`). Each dangerous set receives at most half
of the edges at `s` (here the parity of the degree is used). Take a minimum cover of the
neighbours of `s` by dangerous sets containing `u`: covers by one or two sets contradict the
half-degree bound, and three sets with private neighbours contradict the three-set uncrossing
inequality since `K ≥ 2`.
-/

@[expose] public section

open Finset

namespace NashWilliams

variable {V ι : Type*} [DecidableEq V]

/-- The edge `p` joins `s` to a vertex `u ≠ s`. -/
def Joins (s u : V) (p : V × V) : Prop := (p = (s, u) ∨ p = (u, s)) ∧ u ≠ s

/-- The endpoint of `p` other than `s` (if `p.1 = s`, the second one, otherwise the first one). -/
def oth (s : V) (p : V × V) : V := if p.1 = s then p.2 else p.1

lemma joins_oth {s : V} {p : V × V} (h : (p.1 = s) ≠ (p.2 = s)) : Joins s (oth s p) p := by
  unfold Joins oth
  by_cases h1 : p.1 = s
  · have h2 : p.2 ≠ s := fun h2 => h (by simp [h1, h2])
    simp only [h1, ↓reduceIte]
    exact ⟨Or.inl (Prod.ext h1 rfl), h2⟩
  · have h2 : p.2 = s := by
      by_contra h2
      exact h (by simp [h1, h2])
    simp only [h1, ↓reduceIte]
    exact ⟨Or.inr (Prod.ext rfl h2), h1⟩

/-- Number of active edges joining `s` to a vertex of `X`. -/
def dsF (s : V) (ends : ι → V × V) (F : Finset ι) (X : Finset V) : ℕ :=
  (F.filter fun l => ((ends l).1 = s ∧ (ends l).2 ∈ X) ∨ ((ends l).2 = s ∧ (ends l).1 ∈ X)).card

/-- Indicator of an edge joining `s` to `X`. -/
def jn (s : V) (p : V × V) (X : Finset V) : ℕ :=
  if (p.1 = s ∧ p.2 ∈ X) ∨ (p.2 = s ∧ p.1 ∈ X) then 1 else 0

lemma dsF_eq_sum (s : V) (ends : ι → V × V) (F : Finset ι) (X : Finset V) :
    dsF s ends F X = ∑ l ∈ F, jn s (ends l) X := by
  unfold dsF jn
  rw [Finset.card_filter]

/-- Bookkeeping for the replacement of the edges `i`, `j` by a single edge stored at `i`. -/
lemma sum_split [DecidableEq ι] {f f1 : ι → ℕ} {F : Finset ι} {i j : ι} (hi : i ∈ F)
    (hj : j ∈ F) (hij : i ≠ j) (hf : ∀ l ∈ F, l ≠ i → l ≠ j → f1 l = f l) :
    ∑ l ∈ F, f l + f1 i = ∑ l ∈ F.erase j, f1 l + f i + f j := by
  have hi' : i ∈ F.erase j := mem_erase.2 ⟨hij, hi⟩
  have e1 := Finset.add_sum_erase F f hj
  have e2 := Finset.add_sum_erase (F.erase j) f hi'
  have e3 := Finset.add_sum_erase (F.erase j) f1 hi'
  have e4 : ∑ l ∈ (F.erase j).erase i, f1 l = ∑ l ∈ (F.erase j).erase i, f l := by
    refine Finset.sum_congr rfl fun l hl => ?_
    simp only [mem_erase] at hl
    exact hf l hl.2.2 hl.1 hl.2.1
  omega

lemma cutF_split [DecidableEq ι] {ends : ι → V × V} {F : Finset ι} {i j : ι} (hi : i ∈ F)
    (hj : j ∈ F) (hij : i ≠ j) (u v : V) (S : Finset V) :
    cutF ends F S + cr (u, v) S =
      cutF (Function.update ends i (u, v)) (F.erase j) S + cr (ends i) S + cr (ends j) S := by
  rw [cutF_eq_sum, cutF_eq_sum]
  have := sum_split (f := fun l => cr (ends l) S)
    (f1 := fun l => cr (Function.update ends i (u, v) l) S) hi hj hij
    (fun l _ hli _ => by simp [Function.update_of_ne hli])
  simpa using this

lemma cr_of_joins {s u : V} {p : V × V} (hJ : Joins s u p) {S : Finset V} (hs : s ∉ S) :
    cr p S = if u ∈ S then 1 else 0 := by
  obtain ⟨h | h, -⟩ := hJ <;> subst h <;> by_cases hu : u ∈ S <;> simp [cr, hs, hu]

lemma cr_singleton_of_joins {s u : V} {p : V × V} (hJ : Joins s u p) : cr p {s} = 1 := by
  obtain ⟨h | h, hu⟩ := hJ <;> subst h <;> simp [cr, hu]

/-- If splitting off `su`, `sv` violates the requirement, then `u` and `v` lie in a dangerous
set. -/
lemma dangerous_of_not_req [DecidableEq ι] {K : ℕ} {T : Finset V} {s : V} {ends : ι → V × V}
    {F : Finset ι} (hreq : Req K (T.erase s) ends F) {i j : ι} (hi : i ∈ F) (hj : j ∈ F)
    (hij : i ≠ j) {u v : V} (hJi : Joins s u (ends i)) (hJj : Joins s v (ends j))
    (hfail : ¬ Req K (T.erase s) (Function.update ends i (u, v)) (F.erase j)) :
    ∃ X ⊆ T.erase s, X ≠ T.erase s ∧ u ∈ X ∧ v ∈ X ∧ cutF ends F X ≤ K + 1 := by
  simp only [Req, not_forall, not_le] at hfail
  obtain ⟨S, hST, hne, hneT, hlt⟩ := hfail
  have hs : s ∉ S := fun h => by simpa using hST h
  have e := cutF_split hi hj hij u v S (ends := ends)
  rw [cr_of_joins hJi hs, cr_of_joins hJj hs] at e
  have hK := hreq S hST hne hneT
  refine ⟨S, hST, hneT, ?_, ?_, ?_⟩
  · by_contra hu
    by_cases hv : v ∈ S <;> simp [cr, hu, hv] at e <;> omega
  · by_contra hv
    by_cases hu : u ∈ S <;> simp [cr, hu, hv] at e <;> omega
  · by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [cr, hu, hv] at e <;> omega

/-- A dangerous set receives at most half of the edges at `s` (the degree of `s` being even). -/
lemma two_mul_dsF_le {K : ℕ} {T : Finset V} {s : V} {ends : ι → V × V} {F : Finset ι}
    (hin : Inside T ends F) (hreq : Req K (T.erase s) ends F) (heven : Even (cutF ends F {s}))
    {X : Finset V} (hXT : X ⊆ T.erase s) (hXne : X.Nonempty) (hXT' : X ≠ T.erase s)
    (hXc : cutF ends F X ≤ K + 1) : 2 * dsF s ends F X ≤ cutF ends F {s} := by
  set Y := T.erase s \ X with hY
  have hYK : K ≤ cutF ends F Y := by
    refine hreq Y sdiff_subset ?_ ?_
    · obtain ⟨t, htT, htX⟩ : ∃ t ∈ T.erase s, t ∉ X := by
        by_contra! h
        exact hXT' (Subset.antisymm hXT h)
      exact ⟨t, mem_sdiff.2 ⟨htT, htX⟩⟩
    · intro h
      obtain ⟨x, hx⟩ := hXne
      have : x ∈ Y := by rw [h]; exact hXT hx
      simp [hY, hx] at this
  have key : cutF ends F Y + 2 * dsF s ends F X = cutF ends F X + cutF ends F {s} := by
    simp only [cutF_eq_sum, dsF_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l hl => ?_
    obtain ⟨h1, h2⟩ := hin l hl
    have hsX : s ∉ X := fun h => by simpa using hXT h
    have hX1 : (ends l).1 ∈ X → (ends l).1 ≠ s := fun h h' => hsX (h' ▸ h)
    have hX2 : (ends l).2 ∈ X → (ends l).2 ≠ s := fun h h' => hsX (h' ▸ h)
    unfold cr jn
    by_cases a1 : (ends l).1 = s <;> by_cases a2 : (ends l).2 = s <;>
      by_cases b1 : (ends l).1 ∈ X <;> by_cases b2 : (ends l).2 ∈ X <;> simp_all
  obtain ⟨r, hr⟩ := heven
  omega

lemma dsF_union_add_inter (s : V) (ends : ι → V × V) (F : Finset ι) (X Y : Finset V) :
    dsF s ends F X + dsF s ends F Y = dsF s ends F (X ∪ Y) + dsF s ends F (X ∩ Y) := by
  simp only [dsF_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  unfold jn
  by_cases a1 : (ends l).1 = s <;> by_cases a2 : (ends l).2 = s <;>
    by_cases b1 : (ends l).1 ∈ X <;> by_cases b2 : (ends l).2 ∈ X <;>
    by_cases c1 : (ends l).1 ∈ Y <;> by_cases c2 : (ends l).2 ∈ Y <;> simp_all

lemma cutF_singleton_le_dsF {s : V} {ends : ι → V × V} {F : Finset ι} {X : Finset V}
    (h : ∀ l ∈ F, ((ends l).1 = s) ≠ ((ends l).2 = s) → oth s (ends l) ∈ X) :
    cutF ends F {s} ≤ dsF s ends F X := by
  unfold cutF dsF
  refine Finset.card_le_card fun l hl => ?_
  simp only [mem_filter, mem_singleton] at hl ⊢
  refine ⟨hl.1, ?_⟩
  have := h l hl.1 hl.2
  unfold oth at this
  by_cases a1 : (ends l).1 = s
  · simp only [a1, ↓reduceIte] at this
    exact Or.inl ⟨a1, this⟩
  · simp only [a1, ↓reduceIte] at this
    have a2 : (ends l).2 = s := by
      by_contra a2
      exact hl.2 (by simp [a1, a2])
    exact Or.inr ⟨a2, this⟩

lemma one_le_dsF {s u : V} {ends : ι → V × V} {F : Finset ι} {i : ι} (hi : i ∈ F)
    (hJ : Joins s u (ends i)) {X : Finset V} (hu : u ∈ X) : 1 ≤ dsF s ends F X := by
  unfold dsF
  refine Finset.card_pos.2 ⟨i, mem_filter.2 ⟨hi, ?_⟩⟩
  obtain ⟨h | h, -⟩ := hJ <;> rw [h] <;> simp [hu]

/-- **Lovász's splitting lemma.** -/
theorem exists_split [DecidableEq ι] {K : ℕ} (hK : 2 ≤ K) {T : Finset V} {s : V}
    {ends : ι → V × V} {F : Finset ι} (hin : Inside T ends F) (hreq : Req K (T.erase s) ends F)
    (heven : Even (cutF ends F {s})) (hpos : 0 < cutF ends F {s}) :
    ∃ i ∈ F, ∃ j ∈ F, ∃ u v : V, i ≠ j ∧ Joins s u (ends i) ∧ Joins s v (ends j) ∧
      Req K (T.erase s) (Function.update ends i (u, v)) (F.erase j) := by
  classical
  obtain ⟨i, hiF, hiSE⟩ : ∃ i ∈ F, ((ends i).1 = s) ≠ ((ends i).2 = s) := by
    obtain ⟨i, hi⟩ := Finset.card_pos.1 hpos
    simp only [mem_filter, mem_singleton] at hi
    exact ⟨i, hi.1, hi.2⟩
  set u := oth s (ends i) with hu_def
  have hJi : Joins s u (ends i) := joins_oth hiSE
  have huT : u ∈ T.erase s := by
    obtain ⟨h1, h2⟩ := hin i hiF
    obtain ⟨h | h, hus⟩ := hJi
    · rw [h] at h2; exact mem_erase.2 ⟨hus, h2⟩
    · rw [h] at h1; exact mem_erase.2 ⟨hus, h1⟩
  by_contra hcon
  set D := (T.erase s).powerset.filter fun X => u ∈ X ∧ X ≠ T.erase s ∧ cutF ends F X ≤ K + 1
    with hD
  have hmemD : ∀ X ∈ D, X ⊆ T.erase s ∧ u ∈ X ∧ X ≠ T.erase s ∧ cutF ends F X ≤ K + 1 := by
    intro X hX
    simp only [hD, mem_filter, mem_powerset] at hX
    exact ⟨hX.1, hX.2⟩
  have hdang : ∀ j ∈ F, j ≠ i → ((ends j).1 = s) ≠ ((ends j).2 = s) →
      ∃ X ∈ D, oth s (ends j) ∈ X := by
    intro j hj hji hjSE
    have hfail : ¬ Req K (T.erase s) (Function.update ends i (u, oth s (ends j))) (F.erase j) :=
      fun h => hcon ⟨i, hiF, j, hj, u, oth s (ends j), Ne.symm hji, hJi, joins_oth hjSE, h⟩
    obtain ⟨X, hXT, hXne, huX, hvX, hXc⟩ :=
      dangerous_of_not_req hreq hiF hj (Ne.symm hji) hJi (joins_oth hjSE) hfail
    exact ⟨X, mem_filter.2 ⟨mem_powerset.2 hXT, huX, hXne, hXc⟩, hvX⟩
  set Nb := (F.filter fun j => j ≠ i ∧ ((ends j).1 = s) ≠ ((ends j).2 = s)).image
    fun j => oth s (ends j) with hNb
  have hNbD : ∀ v ∈ Nb, ∃ X ∈ D, v ∈ X := by
    intro v hv
    simp only [hNb, mem_image, mem_filter] at hv
    obtain ⟨j, ⟨hj, hji, hjSE⟩, rfl⟩ := hv
    exact hdang j hj hji hjSE
  obtain ⟨C, hCmem, hCmin⟩ :=
    (D.powerset.filter fun C => ∀ v ∈ Nb, ∃ X ∈ C, v ∈ X).exists_min_image card
      ⟨D, mem_filter.2 ⟨mem_powerset_self D, hNbD⟩⟩
  simp only [mem_filter, mem_powerset] at hCmem hCmin
  obtain ⟨hCD, hCcov⟩ := hCmem
  have hall : ∀ l ∈ F, ((ends l).1 = s) ≠ ((ends l).2 = s) → oth s (ends l) = u ∨
      oth s (ends l) ∈ Nb := by
    intro l hl hlSE
    by_cases hli : l = i
    · left; rw [hli]
    · right
      exact mem_image.2 ⟨l, mem_filter.2 ⟨hl, hli, hlSE⟩, rfl⟩
  have hhalf : ∀ X ∈ D, 2 * dsF s ends F X ≤ cutF ends F {s} := by
    intro X hX
    obtain ⟨hXT, huX, hXne, hXc⟩ := hmemD X hX
    exact two_mul_dsF_le hin hreq heven hXT ⟨u, huX⟩ hXne hXc
  have hpriv : ∀ X ∈ C, ∃ v ∈ Nb, v ∈ X ∧ ∀ Y ∈ C, Y ≠ X → v ∉ Y := by
    intro X hX
    by_contra! h
    have hcov' : ∀ v ∈ Nb, ∃ Y ∈ C.erase X, v ∈ Y := by
      intro v hv
      obtain ⟨Z, hZ, hvZ⟩ := hCcov v hv
      by_cases hZX : Z = X
      · obtain ⟨Y, hY, hYX, hvY⟩ := h v hv (hZX ▸ hvZ)
        exact ⟨Y, mem_erase.2 ⟨hYX, hY⟩, hvY⟩
      · exact ⟨Z, mem_erase.2 ⟨hZX, hZ⟩, hvZ⟩
    have := hCmin (C.erase X) ⟨(erase_subset X C).trans hCD, hcov'⟩
    have h2 := card_erase_lt_of_mem hX
    omega
  obtain h0 | h1 | h2 | h3 : C.card = 0 ∨ C.card = 1 ∨ C.card = 2 ∨ 2 < C.card := by omega
  · -- no cover set: `i` is the only edge at `s`
    rw [card_eq_zero] at h0
    subst h0
    have : cutF ends F {s} ≤ 1 := by
      unfold cutF
      calc _ ≤ ({i} : Finset ι).card := by
            refine card_le_card fun l hl => ?_
            simp only [mem_filter, mem_singleton] at hl
            by_contra hli
            rw [mem_singleton] at hli
            have hv : oth s (ends l) ∈ Nb := mem_image.2 ⟨l, mem_filter.2 ⟨hl.1, hli, hl.2⟩, rfl⟩
            obtain ⟨X, hX, -⟩ := hCcov _ hv
            simp at hX
        _ = 1 := card_singleton i
    obtain ⟨r, hr⟩ := heven
    omega
  · obtain ⟨X, rfl⟩ := card_eq_one.1 h1
    have hXD : X ∈ D := hCD (mem_singleton_self X)
    have hle : cutF ends F {s} ≤ dsF s ends F X := by
      refine cutF_singleton_le_dsF fun l hl hlSE => ?_
      rcases hall l hl hlSE with h | h
      · rw [h]; exact (hmemD X hXD).2.1
      · obtain ⟨Y, hY, hvY⟩ := hCcov _ h
        rw [mem_singleton] at hY
        exact hY ▸ hvY
    have := hhalf X hXD
    omega
  · obtain ⟨X, Y, hXY, rfl⟩ := card_eq_two.1 h2
    have hXD : X ∈ D := hCD (by simp)
    have hYD : Y ∈ D := hCD (by simp)
    have hle : cutF ends F {s} ≤ dsF s ends F (X ∪ Y) := by
      refine cutF_singleton_le_dsF fun l hl hlSE => ?_
      rcases hall l hl hlSE with h | h
      · rw [h]; exact mem_union_left _ (hmemD X hXD).2.1
      · obtain ⟨Z, hZ, hvZ⟩ := hCcov _ h
        simp only [mem_insert, mem_singleton] at hZ
        rcases hZ with rfl | rfl
        · exact mem_union_left _ hvZ
        · exact mem_union_right _ hvZ
    have hmod := dsF_union_add_inter s ends F X Y
    have hone := one_le_dsF hiF hJi (mem_inter.2 ⟨(hmemD X hXD).2.1, (hmemD Y hYD).2.1⟩)
    have := hhalf X hXD
    have := hhalf Y hYD
    omega
  · obtain ⟨X1, hX1, X2, hX2, X3, hX3, h12, h13, h23⟩ := two_lt_card.1 h3
    obtain ⟨hX1T, hu1, hX1ne, hX1c⟩ := hmemD X1 (hCD hX1)
    obtain ⟨hX2T, hu2, hX2ne, hX2c⟩ := hmemD X2 (hCD hX2)
    obtain ⟨hX3T, hu3, hX3ne, hX3c⟩ := hmemD X3 (hCD hX3)
    obtain ⟨v1, -, hv1, hv1o⟩ := hpriv X1 hX1
    obtain ⟨v2, -, hv2, hv2o⟩ := hpriv X2 hX2
    obtain ⟨v3, -, hv3, hv3o⟩ := hpriv X3 hX3
    have h12' := hv1o X2 hX2 (Ne.symm h12)
    have h13' := hv1o X3 hX3 (Ne.symm h13)
    have h21' := hv2o X1 hX1 h12
    have h23' := hv2o X3 hX3 (Ne.symm h23)
    have h31' := hv3o X1 hX1 h13
    have h32' := hv3o X2 hX2 h23
    have hR1 : K ≤ cutF ends F ((X1 \ X2) \ X3) := by
      refine hreq _ (sdiff_subset.trans (sdiff_subset.trans hX1T)) ⟨v1, by simp [hv1, h12', h13']⟩ ?_
      intro h
      have : u ∈ (X1 \ X2) \ X3 := by rw [h]; exact huT
      simp [hu2] at this
    have hR2 : K ≤ cutF ends F ((X2 \ X1) \ X3) := by
      refine hreq _ (sdiff_subset.trans (sdiff_subset.trans hX2T)) ⟨v2, by simp [hv2, h21', h23']⟩ ?_
      intro h
      have : u ∈ (X2 \ X1) \ X3 := by rw [h]; exact huT
      simp [hu1] at this
    have hR3 : K ≤ cutF ends F ((X3 \ X1) \ X2) := by
      refine hreq _ (sdiff_subset.trans (sdiff_subset.trans hX3T)) ⟨v3, by simp [hv3, h31', h32']⟩ ?_
      intro h
      have : u ∈ (X3 \ X1) \ X2 := by rw [h]; exact huT
      simp [hu1] at this
    have hZ : K ≤ cutF ends F (X1 ∩ X2 ∩ X3) := by
      refine hreq _ (inter_subset_left.trans (inter_subset_left.trans hX1T))
        ⟨u, by simp [hu1, hu2, hu3]⟩ ?_
      intro h
      have : v1 ∈ X1 ∩ X2 ∩ X3 := by rw [h]; exact hX1T hv1
      simp [h12'] at this
    have key := Finset.sum_le_sum fun l (_ : l ∈ F) => cr_three (ends l) X1 X2 X3
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← cutF_eq_sum] at key
    have hind : 1 ≤ ∑ l ∈ F, (if ((ends l).1 ∈ X1 ∩ X2 ∩ X3 ∧ (ends l).2 ∉ X1 ∪ X2 ∪ X3) ∨
        ((ends l).2 ∈ X1 ∩ X2 ∩ X3 ∧ (ends l).1 ∉ X1 ∪ X2 ∪ X3) then 1 else 0) := by
      refine le_trans ?_ (Finset.single_le_sum (fun l _ => Nat.zero_le _) hiF)
      have hs1 : s ∉ X1 := fun h => by simpa using hX1T h
      have hs2 : s ∉ X2 := fun h => by simpa using hX2T h
      have hs3 : s ∉ X3 := fun h => by simpa using hX3T h
      obtain ⟨h | h, -⟩ := hJi <;> rw [h] <;> simp [hu1, hu2, hu3, hs1, hs2, hs3]
    omega

end NashWilliams
