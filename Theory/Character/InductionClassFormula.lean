module

public import Theory.Character.Induction
public import Theory.GroupTheory.ConjugacyClassSize
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp

/-!
# Induction evaluated by intersections with conjugacy classes

Frobenius reciprocity against the indicator of a conjugacy class gives
`Ind_H^G φ(g) = |C_G(g)| / |H| * ∑_{h ∈ H, h ~ g} φ(h)`.
The sum uses conjugacy in G, even when H is not normal, and needs no
invariance assumption on φ. This reduces character-table calculations to
weighted intersections with an actual subgroup.
-/

open scoped BigOperators
open Subgroup
noncomputable section
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

private theorem scalarProduct_indicator {G : Type*} [Group G] [Finite G]
    (φ : ClassFunction G) (hφ : IsClassFunction φ) (g : G) :
    scalarProduct G φ (fun y => if IsConj y g then 1 else 0) =
      φ g / (Nat.card (centralizer ({g} : Set G)) : ℂ) := by
  classical
  have hterm (y : G) :
      φ y * star (if IsConj y g then (1 : ℂ) else 0) =
        if IsConj y g then φ g else 0 := by
    by_cases hy : IsConj y g
    · obtain ⟨x, hx⟩ := isConj_iff.mp hy
      simp only [if_pos hy, star_one, mul_one]
      exact (hφ y x).symm.trans (congrArg φ hx)
    · simp only [if_neg hy, star_zero, mul_zero]
  have hcard : (Finset.univ.filter (fun y : G => IsConj y g)).card =
      Nat.card (ConjClasses.mk g).carrier := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun y =>
      ConjClasses.mk_eq_mk_iff_isConj.symm.trans ConjClasses.mem_carrier_iff_mk_eq.symm)
  have hs : (∑ y : G, φ y * star (if IsConj y g then (1 : ℂ) else 0)) =
      (Nat.card (ConjClasses.mk g).carrier : ℂ) * φ g := by
    simp_rw [hterm]
    rw [← Finset.sum_filter, Finset.sum_const, hcard, nsmul_eq_mul]
  have hc : Nat.card (ConjClasses.mk g).carrier * Nat.card (centralizer ({g} : Set G)) =
      Nat.card G := by
    rw [ConjClasses.nat_card_carrier_eq_index_centralizer, Subgroup.index_mul_card]
  have hc' : (Nat.card (ConjClasses.mk g).carrier : ℂ) *
      (Nat.card (centralizer ({g} : Set G)) : ℂ) = (Nat.card G : ℂ) := by exact_mod_cast hc
  have hG : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hC : (Nat.card (centralizer ({g} : Set G)) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := centralizer ({g} : Set G))).ne'
  rw [scalarProduct, hs]
  field_simp [hG, hC]
  linear_combination φ g * hc'

/-- Evaluate induction using each subgroup element in the ambient conjugacy class once. -/
public theorem inducedClassFunction_eq_centralizer_mul_sum {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (φ : ClassFunction H) (g : G) :
    inducedClassFunction H φ g =
      (Nat.card (centralizer ({g} : Set G)) : ℂ) / (Nat.card H : ℂ) *
        ∑ h : H, if IsConj (h : G) g then φ h else 0 := by
  classical
  let δ : ClassFunction G := fun y => if IsConj y g then 1 else 0
  have hδ : IsClassFunction δ := by
    intro y x
    have he : IsConj (x * y * x⁻¹) g ↔ IsConj y g :=
      ⟨fun h => (isConj_iff.mpr ⟨x, rfl⟩).trans h,
       fun h => (isConj_iff.mpr ⟨x, rfl⟩).symm.trans h⟩
    simp only [δ, he]
  have hh := scalarProduct_inducedClassFunction H φ hδ
  rw [scalarProduct_indicator _ (inducedClassFunction_isClassFunction H φ)] at hh
  have he : scalarProduct H φ (fun h : H => δ (h : G)) =
      (Nat.card H : ℂ)⁻¹ * ∑ h : H, if IsConj (h : G) g then φ h else 0 := by
    unfold scalarProduct
    congr 1
    apply Finset.sum_congr rfl
    intro h _
    by_cases hc : IsConj (h : G) g <;> simp only [δ, hc, ite_true, ite_false, star_one, star_zero, mul_one, mul_zero]
  rw [he] at hh
  have hC : (Nat.card (centralizer ({g} : Set G)) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := centralizer ({g} : Set G))).ne'
  have h := (div_eq_iff hC).mp hh
  rw [h]
  ring

/-- Reindex the class-intersection formula along specified subgroup coordinates. -/
public theorem inducedClassFunction_eq_centralizer_mul_sum_equiv
    {G K : Type*} [Group G] [Finite G] [Group K] [Fintype K]
    (H : Subgroup G) (e : K ≃* H) (φ : ClassFunction H) (g : G) :
    inducedClassFunction H φ g =
      (Nat.card (centralizer ({g} : Set G)) : ℂ) / (Nat.card H : ℂ) *
        ∑ t : K, if IsConj (e t : G) g then φ (e t) else 0 := by
  rw [inducedClassFunction_eq_centralizer_mul_sum]
  congr 1
  exact (e.toEquiv.sum_comp
    (fun h : H => if IsConj (h : G) g then φ h else 0)).symm
