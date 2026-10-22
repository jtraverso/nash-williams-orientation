/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Cuts in multigraphs given by an edge family

A (multi)graph is given by an edge family `ends : ι → V × V`, restricted to a finite set
`F : Finset ι` of *active* edges. Loops are allowed (they never cross a cut).

* `cutF ends F S`: number of active edges with exactly one endpoint in `S`.
* `outCutF ends o F S`: number of active edges leaving `S` under the orientation `o`
  (edge `i` is oriented `(ends i).1 → (ends i).2` if `o i` and the other way otherwise).
* `Req K T ends F`: every nonempty proper subset of the vertex set `T` has cut at least `K`.

We prove the basic uncrossing inequalities (submodularity, posimodularity and a three-set
inequality) by counting edge by edge.
-/

@[expose] public section

open Finset

namespace NashWilliams

variable {V ι : Type*} [DecidableEq V]

/-- Number of active edges with exactly one endpoint in `S`. -/
def cutF (ends : ι → V × V) (F : Finset ι) (S : Finset V) : ℕ :=
  (F.filter fun i => ((ends i).1 ∈ S) ≠ ((ends i).2 ∈ S)).card

/-- Whether edge `p`, oriented `p.1 → p.2` if `b` and `p.2 → p.1` otherwise, leaves `S`. -/
def Leaves (p : V × V) (b : Bool) (S : Finset V) : Prop :=
  if b then p.1 ∈ S ∧ p.2 ∉ S else p.2 ∈ S ∧ p.1 ∉ S

instance (p : V × V) (b : Bool) (S : Finset V) : Decidable (Leaves p b S) := by
  unfold Leaves; split <;> infer_instance

/-- Number of active edges leaving `S` under the orientation `o`. -/
def outCutF (ends : ι → V × V) (o : ι → Bool) (F : Finset ι) (S : Finset V) : ℕ :=
  (F.filter fun i => Leaves (ends i) (o i) S).card

/-- Every nonempty proper subset of `T` has cut at least `K`. -/
def Req (K : ℕ) (T : Finset V) (ends : ι → V × V) (F : Finset ι) : Prop :=
  ∀ S ⊆ T, S.Nonempty → S ≠ T → K ≤ cutF ends F S

/-- All active edges have both endpoints in `T`. -/
def Inside (T : Finset V) (ends : ι → V × V) (F : Finset ι) : Prop :=
  ∀ i ∈ F, (ends i).1 ∈ T ∧ (ends i).2 ∈ T

/-- Indicator of edge `p` crossing `S`. -/
def cr (p : V × V) (S : Finset V) : ℕ := if (p.1 ∈ S) ≠ (p.2 ∈ S) then 1 else 0

lemma cutF_eq_sum (ends : ι → V × V) (F : Finset ι) (S : Finset V) :
    cutF ends F S = ∑ i ∈ F, cr (ends i) S := by
  simp [cutF, cr, Finset.card_filter]

lemma cutF_le_of_forall {ends : ι → V × V} {F : Finset ι} {S S' : Finset V}
    (h : ∀ i ∈ F, ((ends i).1 ∈ S) ≠ ((ends i).2 ∈ S) → ((ends i).1 ∈ S') ≠ ((ends i).2 ∈ S')) :
    cutF ends F S ≤ cutF ends F S' := by
  unfold cutF
  exact Finset.card_le_card fun i hi => by
    simp only [Finset.mem_filter] at hi ⊢; exact ⟨hi.1, h i hi.1 hi.2⟩

lemma cutF_congr {ends : ι → V × V} {F : Finset ι} {S S' : Finset V}
    (h : ∀ i ∈ F, (((ends i).1 ∈ S) ≠ ((ends i).2 ∈ S) ↔
      ((ends i).1 ∈ S') ≠ ((ends i).2 ∈ S'))) :
    cutF ends F S = cutF ends F S' :=
  le_antisymm (cutF_le_of_forall fun i hi => (h i hi).1)
    (cutF_le_of_forall fun i hi => (h i hi).2)

/-- Submodularity of the cut function. -/
lemma cutF_inter_add_union (ends : ι → V × V) (F : Finset ι) (X Y : Finset V) :
    cutF ends F (X ∩ Y) + cutF ends F (X ∪ Y) ≤ cutF ends F X + cutF ends F Y := by
  simp only [cutF_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  unfold cr
  by_cases h1 : (ends i).1 ∈ X <;> by_cases h2 : (ends i).1 ∈ Y <;>
    by_cases h3 : (ends i).2 ∈ X <;> by_cases h4 : (ends i).2 ∈ Y <;> simp [*]

/-- Posimodularity of the cut function. -/
lemma cutF_sdiff_add_sdiff (ends : ι → V × V) (F : Finset ι) (X Y : Finset V) :
    cutF ends F (X \ Y) + cutF ends F (Y \ X) ≤ cutF ends F X + cutF ends F Y := by
  simp only [cutF_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  unfold cr
  by_cases h1 : (ends i).1 ∈ X <;> by_cases h2 : (ends i).1 ∈ Y <;>
    by_cases h3 : (ends i).2 ∈ X <;> by_cases h4 : (ends i).2 ∈ Y <;> simp [*]

/-- Complementation inside `T` does not change the cut. -/
lemma cutF_sdiff_eq {T : Finset V} {ends : ι → V × V} {F : Finset ι} (hin : Inside T ends F)
    (S : Finset V) : cutF ends F (T \ S) = cutF ends F S := by
  refine cutF_congr fun i hi => ?_
  obtain ⟨h1, h2⟩ := hin i hi
  by_cases h3 : (ends i).1 ∈ S <;> by_cases h4 : (ends i).2 ∈ S <;> simp [*]

lemma cutF_erase_le (ends : ι → V × V) (F : Finset ι) (S : Finset V) [DecidableEq ι] (i : ι) :
    cutF ends (F.erase i) S ≤ cutF ends F S := by
  unfold cutF
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _))

lemma cutF_le_erase_add_one (ends : ι → V × V) (F : Finset ι) (S : Finset V) [DecidableEq ι]
    (i : ι) : cutF ends F S ≤ cutF ends (F.erase i) S + 1 := by
  unfold cutF
  rw [Finset.filter_erase]
  have := Finset.pred_card_le_card_erase
    (s := F.filter fun i => ((ends i).1 ∈ S) ≠ ((ends i).2 ∈ S))
    (a := i)
  omega

lemma cutF_erase_eq (ends : ι → V × V) (F : Finset ι) (S : Finset V) [DecidableEq ι] (i : ι)
    (h : ¬ (((ends i).1 ∈ S) ≠ ((ends i).2 ∈ S))) :
    cutF ends (F.erase i) S = cutF ends F S := by
  unfold cutF
  rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
  simp only [Finset.mem_filter, not_and]
  exact fun _ => h

lemma outCutF_erase_le (ends : ι → V × V) (o : ι → Bool) (F : Finset ι) (S : Finset V)
    [DecidableEq ι] (i : ι) : outCutF ends o (F.erase i) S ≤ outCutF ends o F S := by
  unfold outCutF
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _))

/-- If no active edge lies inside `X`, then the cut of `X` is at least the sum of the cuts of two
distinct vertices of `X`. -/
lemma cutF_pair_le {ends : ι → V × V} {F : Finset ι} {X : Finset V} {x y : V} (hxy : x ≠ y)
    (hx : x ∈ X) (hy : y ∈ X) (hno : ∀ i ∈ F, ¬ ((ends i).1 ∈ X ∧ (ends i).2 ∈ X)) :
    cutF ends F {x} + cutF ends F {y} ≤ cutF ends F X := by
  simp only [cutF_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have := hno i hi
  unfold cr
  by_cases h1 : (ends i).1 ∈ X <;> by_cases h2 : (ends i).2 ∈ X <;>
    by_cases h3 : (ends i).1 = x <;> by_cases h4 : (ends i).2 = x <;>
    by_cases h5 : (ends i).1 = y <;> by_cases h6 : (ends i).2 = y <;> simp_all

/-- The three-set uncrossing inequality, edge by edge. -/
lemma cr_three (p : V × V) (A B C : Finset V) :
    cr p ((A \ B) \ C) + cr p ((B \ A) \ C) + cr p ((C \ A) \ B) + cr p (A ∩ B ∩ C) +
      2 * (if (p.1 ∈ A ∩ B ∩ C ∧ p.2 ∉ A ∪ B ∪ C) ∨ (p.2 ∈ A ∩ B ∩ C ∧ p.1 ∉ A ∪ B ∪ C)
        then 1 else 0) ≤ cr p A + cr p B + cr p C := by
  unfold cr
  by_cases h1 : p.1 ∈ A <;> by_cases h2 : p.1 ∈ B <;> by_cases h3 : p.1 ∈ C <;>
    by_cases h4 : p.2 ∈ A <;> by_cases h5 : p.2 ∈ B <;> by_cases h6 : p.2 ∈ C <;> simp [*]

end NashWilliams
