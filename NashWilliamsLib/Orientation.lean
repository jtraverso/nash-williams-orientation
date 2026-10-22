/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import NashWilliamsLib.Mader
public import NashWilliamsLib.Splitting

/-!
# Nash-Williams' weak orientation theorem for edge families

* `split_all`: repeating Lovász's splitting lemma, all `2m` edges at a vertex `s` can be split
  off in `m` pairs keeping the requirement on `T \ {s}`; conversely every orientation of the split
  graph lifts to an orientation of the original one (each new arc `u → v` becomes `u → s → v`)
  with at least as many arcs leaving every set, and with `m` arcs leaving and `m` arcs entering
  `s`.
* `exists_orientation`: induction on the number of active edges. If an edge can be deleted we
  delete it; otherwise Mader's lemma gives a vertex `s` of degree `2k`, which we split off
  completely and remove.
-/

@[expose] public section

open Finset

namespace NashWilliams

variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

/-- Indicator of the oriented edge `p` leaving `S`. -/
def lv (p : V × V) (b : Bool) (S : Finset V) : ℕ := if Leaves p b S then 1 else 0

omit [DecidableEq ι] in
lemma outCutF_eq_sum (ends : ι → V × V) (o : ι → Bool) (F : Finset ι) (S : Finset V) :
    outCutF ends o F S = ∑ i ∈ F, lv (ends i) (o i) S := by
  unfold outCutF lv
  rw [Finset.card_filter]

omit [DecidableEq ι] in
lemma outCutF_mono {ends : ι → V × V} {o : ι → Bool} {F G : Finset ι} (h : F ⊆ G)
    (S : Finset V) : outCutF ends o F S ≤ outCutF ends o G S := by
  unfold outCutF
  exact card_le_card (filter_subset_filter _ h)

omit [DecidableEq ι] in
lemma outCutF_erase_congr {ends : ι → V × V} {o : ι → Bool} {F : Finset ι} {s : V}
    (h : ∀ l ∈ F, (ends l).1 ≠ s ∧ (ends l).2 ≠ s) (S : Finset V) :
    outCutF ends o F (S.erase s) = outCutF ends o F S := by
  unfold outCutF
  congr 1
  refine filter_congr fun l hl => ?_
  obtain ⟨h1, h2⟩ := h l hl
  unfold Leaves
  split <;> simp [mem_erase, h1, h2]

/-- Orientation of the two split edges `i`, `j` induced by the orientation of the new edge `i`. -/
def liftO (s : V) (ends : ι → V × V) (o1 : ι → Bool) (i j : ι) (l : ι) : Bool :=
  if l = i then (if (ends i).2 = s then o1 i else !o1 i)
  else if l = j then (if (ends j).1 = s then o1 i else !o1 i)
  else o1 l

omit [DecidableEq ι] in
lemma lv_split {s u v : V} {p q : V × V} (hp : Joins s u p) (hq : Joins s v q) (b : Bool)
    (S : Finset V) :
    lv (u, v) b S ≤ lv p (if p.2 = s then b else !b) S + lv q (if q.1 = s then b else !b) S := by
  obtain ⟨hp | hp, hu⟩ := hp <;> obtain ⟨hq | hq, hv⟩ := hq <;> subst hp hq <;>
    cases b <;> by_cases hs : s ∈ S <;> by_cases hu' : u ∈ S <;> by_cases hv' : v ∈ S <;>
    simp [lv, Leaves, *]

omit [DecidableEq ι] in
lemma lv_split_eq {s u v : V} {p q : V × V} (hp : Joins s u p) (hq : Joins s v q) (b : Bool)
    {X : Finset V} (h : (s ∈ X ∧ u ∉ X ∧ v ∉ X) ∨ (s ∉ X ∧ u ∈ X ∧ v ∈ X)) :
    lv (u, v) b X + 1 =
      lv p (if p.2 = s then b else !b) X + lv q (if q.1 = s then b else !b) X := by
  obtain ⟨hp | hp, hu⟩ := hp <;> obtain ⟨hq | hq, hv⟩ := hq <;> subst hp hq <;>
    cases b <;> rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> simp [lv, Leaves, *]

lemma outCutF_split {ends : ι → V × V} {F : Finset ι} {i j : ι} (hi : i ∈ F) (hj : j ∈ F)
    (hij : i ≠ j) {s u v : V} (o1 : ι → Bool) (S : Finset V) :
    outCutF ends (liftO s ends o1 i j) F S + lv (u, v) (o1 i) S =
      outCutF (Function.update ends i (u, v)) o1 (F.erase j) S +
        lv (ends i) (liftO s ends o1 i j i) S + lv (ends j) (liftO s ends o1 i j j) S := by
  rw [outCutF_eq_sum, outCutF_eq_sum]
  have := sum_split (f := fun l => lv (ends l) (liftO s ends o1 i j l) S)
    (f1 := fun l => lv (Function.update ends i (u, v) l) (o1 l) S) hi hj hij
    (fun l _ hli hlj => by simp [liftO, hli, hlj])
  simpa using this

omit [DecidableEq ι] in
lemma mem_erase_of_joins {T : Finset V} {s u : V} {ends : ι → V × V} {F : Finset ι}
    (hin : Inside T ends F) {i : ι} (hi : i ∈ F) (hJ : Joins s u (ends i)) : u ∈ T.erase s := by
  obtain ⟨h1, h2⟩ := hin i hi
  obtain ⟨h | h, hus⟩ := hJ
  · rw [h] at h2; exact mem_erase.2 ⟨hus, h2⟩
  · rw [h] at h1; exact mem_erase.2 ⟨hus, h1⟩

omit [DecidableEq ι] in
/-- **Complete splitting at `s`.** -/
theorem split_all {K : ℕ} (hK : 2 ≤ K) {T : Finset V} {s : V} :
    ∀ (m : ℕ) (ends : ι → V × V) (F : Finset ι), Inside T ends F → Req K (T.erase s) ends F →
      cutF ends F {s} = 2 * m →
      ∃ (ends' : ι → V × V) (F' : Finset ι), F'.card + m = F.card ∧ Inside T ends' F' ∧
        Req K (T.erase s) ends' F' ∧ cutF ends' F' {s} = 0 ∧
        ∀ o' : ι → Bool, ∃ o : ι → Bool, (∀ S, outCutF ends' o' F' S ≤ outCutF ends o F S) ∧
          m ≤ outCutF ends o F {s} ∧ m ≤ outCutF ends o F (T.erase s) := by
  classical
  intro m
  induction m with
  | zero =>
    intro ends F hin hreq hcut
    exact ⟨ends, F, by simp, hin, hreq, by simpa using hcut,
      fun o' => ⟨o', fun S => le_rfl, Nat.zero_le _, Nat.zero_le _⟩⟩
  | succ m ih =>
    intro ends F hin hreq hcut
    obtain ⟨i, hi, j, hj, u, v, hij, hJi, hJj, hreq1⟩ :=
      exists_split hK hin hreq ⟨m + 1, by omega⟩ (by omega)
    have huT := mem_erase_of_joins hin hi hJi
    have hvT := mem_erase_of_joins hin hj hJj
    have hin1 : Inside T (Function.update ends i (u, v)) (F.erase j) := by
      intro l hl
      by_cases hli : l = i
      · subst hli
        simp only [Function.update_self]
        exact ⟨mem_of_mem_erase huT, mem_of_mem_erase hvT⟩
      · rw [Function.update_of_ne hli]
        exact hin l (mem_of_mem_erase hl)
    have hcut1 : cutF (Function.update ends i (u, v)) (F.erase j) {s} = 2 * m := by
      have e := cutF_split hi hj hij u v {s} (ends := ends)
      rw [cr_singleton_of_joins hJi, cr_singleton_of_joins hJj] at e
      have hu : u ≠ s := (mem_erase.1 huT).1
      have hv : v ≠ s := (mem_erase.1 hvT).1
      simp [cr, hu, hv] at e
      omega
    obtain ⟨ends', F', hcard, hin', hreq', hcut', htrans⟩ := ih _ _ hin1 hreq1 hcut1
    refine ⟨ends', F', ?_, hin', hreq', hcut', fun o' => ?_⟩
    · have := card_erase_of_mem hj
      have := card_pos.2 ⟨j, hj⟩
      omega
    obtain ⟨o1, ha, hb1, hb2⟩ := htrans o'
    have hli : liftO s ends o1 i j i = if (ends i).2 = s then o1 i else !o1 i := by
      simp [liftO]
    have hlj : liftO s ends o1 i j j = if (ends j).1 = s then o1 i else !o1 i := by
      simp [liftO, Ne.symm hij]
    refine ⟨liftO s ends o1 i j, fun S => ?_, ?_, ?_⟩
    · have e := outCutF_split (s := s) (u := u) (v := v) (ends := ends) hi hj hij o1 S
      have := lv_split hJi hJj (o1 i) S
      rw [hli, hlj] at e
      have := ha S
      omega
    · have e := outCutF_split (s := s) (u := u) (v := v) (ends := ends) hi hj hij o1 {s}
      have := lv_split_eq hJi hJj (o1 i) (X := {s})
        (Or.inl ⟨mem_singleton_self s, by simpa using (mem_erase.1 huT).1,
          by simpa using (mem_erase.1 hvT).1⟩)
      rw [hli, hlj] at e
      omega
    · have e := outCutF_split (s := s) (u := u) (v := v) (ends := ends) hi hj hij o1 (T.erase s)
      have := lv_split_eq hJi hJj (o1 i) (X := T.erase s)
        (Or.inr ⟨by simp, huT, hvT⟩)
      rw [hli, hlj] at e
      omega

omit [DecidableEq ι] in
lemma req_erase_of_req {K : ℕ} {T : Finset V} {ends : ι → V × V} {F : Finset ι}
    (hreq : Req K T ends F) (s : V) : Req K (T.erase s) ends F := by
  intro S hS hne hneT
  refine hreq S (hS.trans (erase_subset _ _)) hne ?_
  rintro rfl
  by_cases hs : s ∈ S
  · simpa using hS hs
  · exact hneT (erase_eq_of_notMem hs).symm

omit [DecidableEq ι] in
/-- **Nash-Williams' weak orientation theorem**, general form: if every nonempty proper subset of
`T` has cut at least `2k` (all active edges inside `T`), then the active edges have an orientation
in which every nonempty proper subset of `T` has at least `k` leaving arcs. -/
theorem exists_orientation (k : ℕ) : ∀ (n : ℕ) (T : Finset V) (ends : ι → V × V) (F : Finset ι),
    F.card = n → Inside T ends F → Req (2 * k) T ends F →
    ∃ o : ι → Bool, ∀ S ⊆ T, S.Nonempty → S ≠ T → k ≤ outCutF ends o F S := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T ends F hn hin hreq
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨fun _ => true, fun _ _ _ _ => Nat.zero_le _⟩
  by_cases hT : T.card ≤ 1
  · refine ⟨fun _ => true, fun S hS hne hneT => ?_⟩
    have h1 := card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hS, hneT⟩)
    have h2 := hne.card_pos
    omega
  push Not at hT
  by_cases hdel : ∃ i ∈ F, Req (2 * k) T ends (F.erase i)
  · obtain ⟨i, hi, hreq'⟩ := hdel
    obtain ⟨o, ho⟩ := ih _ (hn ▸ card_erase_lt_of_mem hi) T ends (F.erase i) rfl
      (fun l hl => hin l (mem_of_mem_erase hl)) hreq'
    exact ⟨o, fun S hS hne hneT => (ho S hS hne hneT).trans (outCutF_erase_le ends o F S i)⟩
  push Not at hdel
  obtain ⟨s, hsT, hcut⟩ := exists_vertex_cutF_eq (by omega) hT hin hreq hdel
  obtain ⟨ends', F', hcard, hin', hreq', hcut0, htrans⟩ :=
    split_all (by omega) k ends F hin (req_erase_of_req hreq s) hcut
  -- the only edges at `s` left are loops; drop them
  have hloopS : ∀ l ∈ F', ((ends' l).1 = s) ↔ ((ends' l).2 = s) := by
    intro l hl
    by_contra h
    have : 0 < cutF ends' F' {s} := card_pos.2 ⟨l, mem_filter.2 ⟨hl, by simpa using h⟩⟩
    omega
  set F'' := F'.filter fun l => (ends' l).1 ≠ s ∧ (ends' l).2 ≠ s with hF''
  have hF''s : ∀ l ∈ F'', (ends' l).1 ≠ s ∧ (ends' l).2 ≠ s := fun l hl => (mem_filter.1 hl).2
  have hcut'' : ∀ S, cutF ends' F'' S = cutF ends' F' S := by
    intro S
    unfold cutF
    rw [hF'', filter_filter]
    congr 1
    refine filter_congr fun l hl => ?_
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      by_contra h'
      have h1 : (ends' l).1 = s := by
        by_contra h1
        exact h' ⟨h1, fun h2 => h1 ((hloopS l hl).2 h2)⟩
      have h2 := (hloopS l hl).1 h1
      exact h (by rw [h1, h2])
  have hin'' : Inside (T.erase s) ends' F'' := by
    intro l hl
    obtain ⟨h1, h2⟩ := hin' l (mem_filter.1 hl).1
    obtain ⟨h3, h4⟩ := hF''s l hl
    exact ⟨mem_erase.2 ⟨h3, h1⟩, mem_erase.2 ⟨h4, h2⟩⟩
  have hreq'' : Req (2 * k) (T.erase s) ends' F'' := fun S hS hne hneT =>
    (hcut'' S).symm ▸ hreq' S hS hne hneT
  obtain ⟨o', ho'⟩ := ih F''.card (by
    have : F''.card ≤ F'.card := card_filter_le _ _
    omega) (T.erase s) ends' F'' rfl hin'' hreq''
  obtain ⟨o, ha, hb1, hb2⟩ := htrans o'
  refine ⟨o, fun S hS hne hneT => ?_⟩
  by_cases h1 : S = {s}
  · exact h1 ▸ hb1
  by_cases h2 : S = T.erase s
  · exact h2 ▸ hb2
  have hS' : S.erase s ⊆ T.erase s := erase_subset_erase s hS
  have hne' : (S.erase s).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    by_cases hxs : x = s
    · subst hxs
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      exact h1 (by
        ext y
        constructor
        · intro hy
          by_contra hys
          have : y ∈ S.erase x := mem_erase.2 ⟨by simpa using hys, hy⟩
          simp [h] at this
        · intro hy
          rw [mem_singleton] at hy
          exact hy ▸ hx)
    · exact ⟨x, mem_erase.2 ⟨hxs, hx⟩⟩
  have hneT' : S.erase s ≠ T.erase s := by
    intro h
    by_cases hsS : s ∈ S
    · exact hneT (by rw [← insert_erase hsS, h, insert_erase hsT])
    · exact h2 (by rw [← h, erase_eq_of_notMem hsS])
  calc k ≤ outCutF ends' o' F'' (S.erase s) := ho' _ hS' hne' hneT'
    _ = outCutF ends' o' F'' S := outCutF_erase_congr hF''s S
    _ ≤ outCutF ends' o' F' S := outCutF_mono (filter_subset _ _) S
    _ ≤ outCutF ends o F S := ha S

end NashWilliams
