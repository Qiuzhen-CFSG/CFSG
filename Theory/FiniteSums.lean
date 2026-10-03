module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.SetTheory.Cardinal.NatCard

import Mathlib.Tactic.Group

/-!
# Finite-sum utilities

Small reusable identities for finite sums over groups and subgroups.
-/

@[expose] public section

open scoped BigOperators

universe u v

/-- Reindexing: `∑_{x,y} f (x⁻¹·y) = |L| • ∑_z f z`. -/
public lemma conj_reindex {L : Type u} {M : Type v} [Group L] [Fintype L]
    [AddCommMonoid M] (f : L → M)
    : (∑ x : L, ∑ y : L, f (x⁻¹ * y)) = Fintype.card L • ∑ z : L, f z := by
  classical
  calc
    (∑ x : L, ∑ y : L, f (x⁻¹ * y)) = ∑ x : L, ∑ z : L, f z := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      refine (Finset.sum_bij (fun z hz => x * z) ?_ ?_ ?_ ?_).symm
      · intro z hz
        simp
      · intro z₁ h₁ z₂ h₂ hEq
        exact mul_left_cancel hEq
      · intro y hy
        refine ⟨x⁻¹ * y, by simp, ?_⟩
        group
      · intro z hz
        congr 1
        group
    _ = Fintype.card L • ∑ z : L, f z := by
      rw [Finset.sum_const, Finset.card_univ]

/-- Semiring-valued form of `conj_reindex`, with the cardinal as a scalar product. -/
public lemma conj_reindex_mul {L : Type u} {R : Type v} [Group L] [Fintype L] [Semiring R]
    (f : L → R)
    : (∑ x : L, ∑ y : L, f (x⁻¹ * y)) = (Nat.card L : R) * ∑ z : L, f z := by
  calc
    (∑ x : L, ∑ y : L, f (x⁻¹ * y)) = Fintype.card L • ∑ z : L, f z :=
      conj_reindex f
    _ = (Nat.card L : R) * ∑ z : L, f z := by
      rw [Nat.card_eq_fintype_card]
      simp [nsmul_eq_mul]

/-- A function vanishing off `H` sums over `G` the same as over `H`. -/
public lemma sum_eq_sum_subgroup_of_vanishes
    {G : Type u} {M : Type v} [Group G] [Fintype G] [AddCommMonoid M]
    (H : Subgroup G) [Fintype H] (f : G → M)
    (hf : ∀ x : G, x ∉ H → f x = 0)
    : (∑ x : G, f x) = ∑ x : H, f (x : G) := by
  classical
  calc
    (∑ x : G, f x) = Finset.sum (Finset.univ.filter (fun x : G => x ∈ H)) f := by
      refine (Finset.sum_subset (by intro x hx; exact Finset.mem_univ x) ?_).symm
      intro x hx hxnot
      have hxH : x ∉ H := by
        intro hxH
        exact hxnot (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxH⟩)
      exact hf x hxH
    _ = ∑ x : H, f (x : G) := by
      refine Finset.sum_bij (fun x hx => (⟨(x : G), (Finset.mem_filter.mp hx).2⟩ : H)) ?_ ?_ ?_ ?_
      · intro x hx
        simp
      · intro x₁ h₁ x₂ h₂ hEq
        exact congrArg Subtype.val hEq
      · intro x hx
        refine ⟨(x : G), Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩, ?_⟩
        exact Subtype.ext rfl
      · intro x hx
        rfl
