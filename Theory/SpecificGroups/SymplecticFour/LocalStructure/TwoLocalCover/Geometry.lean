module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
The parameterized transvection calculation below adapts the private calculation
in Theory/SpecificGroups/SymplecticFour/EvenProjective.lean, itself adapted from
Atlas/LinearGroups/Symplectic/{Transvection,TransvectionImage,Center}.lean,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917. Covered by the ATLAS Research
and Attribution License 1.0; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Changes: retain a scalar parameter and use transvections to move vectors;
subspace transport uses the existing CFSG point Levi matrices.
-/

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.FixedRadical
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.Coordinates
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.Action
public import Mathlib.LinearAlgebra.Transvection.Basic
import Mathlib.Tactic.FinCases

/-!
# Conjugating isotropic subspaces to the standard point or plane

Parameterized symplectic transvections move any nonzero vector to the first
standard vector. An isotropic plane through that vector has a nonzero vector
in the second hyperbolic pair. The existing SL₂ Levi matrices move that
component to the second standard vector while fixing the first. Dimension
then identifies the image with the full standard plane.

All changes of coordinates are elements of the actual symplectic matrix
group. These geometric facts supply the conjugacy step of the symplectic
two-local coverage used in Aschbacher–Smith, Theorem 0.1.2(1), printed pp.3–4
(repeated as Theorem 0.1.1(1), printed pp.481–482).
-/

public noncomputable section
open Matrix
namespace Theory.SpecificGroups.SymplecticFour.TwoLocalCover
variable {F : Type*} [Field F]

private def transvectionMap (t : F) (v : Vector F) : Module.End F (Vector F) :=
  LinearMap.transvection (t • (form F).flip v) v

private theorem transvectionMap_apply (t : F) (v x : Vector F) :
    transvectionMap t v x = x + (t * form F x v) • v := rfl

private def transvection (t : F) (v : Vector F) : Sp F :=
  ⟨LinearMap.toMatrix' (transvectionMap t v), by
    apply SymplecticGroup.mem_iff'.mpr
    have he := Matrix.toBilin'_comp (-Matrix.J (Fin 2) F)
      (LinearMap.toMatrix' (transvectionMap t v)) (LinearMap.toMatrix' (transvectionMap t v))
    have hpres : (form F).comp (transvectionMap t v) (transvectionMap t v) = form F := by
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      change form F (transvectionMap t v x) (transvectionMap t v y) = form F x y
      simp only [transvectionMap_apply, map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul, form_alternating.self_eq_zero,
        mul_zero, add_zero]
      rw [← form_alternating.neg_eq y v]
      ring
    simp only [Matrix.toLin'_toMatrix'] at he
    have hm := Matrix.toBilin'.injective (he.symm.trans hpres)
    simpa [Matrix.mul_neg, Matrix.neg_mul, form] using hm⟩

private theorem transvection_apply (t : F) (v x : Vector F) :
    transvection t v • x = x + (t * form F x v) • v := by
  change (LinearMap.toMatrix' (transvectionMap t v)) *ᵥ x = _
  rw [LinearMap.toMatrix'_mulVec, transvectionMap_apply]

private theorem exists_partner {v : Vector F} (hv : v ≠ 0) :
    ∃ x, form F v x = 1 := by
  obtain ⟨w, hw⟩ : ∃ w, form F v w ≠ 0 := by
    by_contra! h
    exact hv (form_nondegenerate.1 v h)
  exact ⟨(form F v w)⁻¹ • w, by simp [map_smul, hw]⟩

private theorem exists_move_of_pairing_ne_zero (x y : Vector F)
    (hxy : form F x y ≠ 0) : ∃ g : Sp F, g • x = y := by
  refine ⟨transvection (form F x y)⁻¹ (y - x), ?_⟩
  rw [transvection_apply]
  simp only [map_sub, form_alternating.self_eq_zero, sub_zero, inv_mul_cancel₀ hxy,
    one_smul]
  abel

/-- The full symplectic matrix group is transitive on nonzero vectors. -/
theorem nonzero_vector_transitive {x y : Vector F} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g : Sp F, g • x = y := by
  obtain ⟨u, hu⟩ := exists_partner hx
  obtain ⟨v, hv⟩ := exists_partner hy
  have hz : ∃ z, form F x z ≠ 0 ∧ form F y z ≠ 0 := by
    by_cases h : form F y u = 0
    · by_cases h' : form F x v = 0
      · exact ⟨u + v, by simp [map_add, hu, h'], by simp [map_add, h, hv]⟩
      · exact ⟨v, h', by rw [hv]; exact one_ne_zero⟩
    · exact ⟨u, by rw [hu]; exact one_ne_zero, h⟩
  obtain ⟨z, hxz, hyz⟩ := hz
  obtain ⟨a, ha⟩ := exists_move_of_pairing_ne_zero x z hxz
  obtain ⟨b, hb⟩ := exists_move_of_pairing_ne_zero z y
    (fun h => hyz (form_alternating.eq_iff.mp h))
  exact ⟨b * a, by rw [mul_smul, ha, hb]⟩

private theorem e_zero_ne_zero : e (F := F) 0 ≠ 0 := by
  intro h
  have := congrFun h (.inl 0)
  simp [e] at this

private theorem map_isotropic (W : Submodule F (Vector F))
    (hW : ∀ x ∈ W, ∀ y ∈ W, form F x y = 0) (g : Sp F) :
    ∀ x ∈ W.map (toLinear g).toLinearMap,
      ∀ y ∈ W.map (toLinear g).toLinearMap, form F x y = 0 := by
  rintro x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩
  exact (preserves_form g u v).trans (hW u hu v hv)

private theorem levi_move (w : Vector F) (hw0 : w (.inr 0) = 0)
    (hw : w ∉ point F) : ∃ a : Sp F,
      a • e (F := F) 0 = e 0 ∧ a • w = w (.inl 0) • e 0 + e 1 := by
  let v : Fin 2 → F := ![w (.inl 1), w (.inr 1)]
  have hv : v ≠ 0 := by
    intro h
    apply hw
    rw [mem_point_iff]
    refine ⟨?_, ?_⟩
    · exact congrFun h 0
    · intro i
      fin_cases i
      · exact hw0
      · exact congrFun h 1
  have he : (Pi.single 0 (1 : F) : Fin 2 → F) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  obtain ⟨A, hA⟩ := natural_transitive hv he
  refine ⟨(pointLevi A).val, ?_, ?_⟩
  · exact (mem_pointLocal_iff_fixed _).mp (pointLevi A).property
  · have hA0 := congrFun hA 0
    have hA1 := congrFun hA 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, v,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0)] at hA0 hA1
    funext i
    cases i with
    | inl i =>
      fin_cases i <;>
        simp [pointLevi, pointLeviMatrix, Matrix.mulVec, dotProduct,
          Fintype.sum_sum_type, Fin.sum_univ_two, e, hA0]
    | inr i =>
      fin_cases i <;>
        simp [pointLevi, pointLeviMatrix, Matrix.mulVec, dotProduct,
          Fintype.sum_sum_type, Fin.sum_univ_two, e, hw0, hA1]

private theorem standard_of_contains_point (W : Submodule F (Vector F))
    (hW : ∀ x ∈ W, ∀ y ∈ W, form F x y = 0) (he : e 0 ∈ W) :
    ∃ g : Sp F, W.map (toLinear g).toLinearMap = point F ∨
      W.map (toLinear g).toLinearMap = plane F := by
  have hp : point F ≤ W := Submodule.span_le.mpr (by simpa using he)
  by_cases hle : W ≤ point F
  · refine ⟨1, Or.inl ?_⟩
    simpa using le_antisymm hle hp
  · obtain ⟨w, hwW, hw⟩ : ∃ w ∈ W, w ∉ point F := by
      simpa only [SetLike.le_def, not_forall, exists_prop] using hle
    have hw0 : w (.inr 0) = 0 := by
      have h := hW w hwW (e 0) he
      simpa using h
    obtain ⟨a, ha, haw⟩ := levi_move w hw0 hw
    let U := W.map (toLinear a).toLinearMap
    have heU : e 0 ∈ U := ⟨e 0, he, ha⟩
    have hwU : a • w ∈ U := ⟨w, hwW, rfl⟩
    have he1U : e 1 ∈ U := by
      have h := U.sub_mem hwU (U.smul_mem (w (.inl 0)) heU)
      rwa [haw, add_sub_cancel_left] at h
    have hplane : plane F ≤ U := by
      intro x hx
      rw [plane_decomposition x hx]
      exact U.add_mem (U.smul_mem _ heU) (U.smul_mem _ he1U)
    refine ⟨a, Or.inr ?_⟩
    apply (Submodule.eq_of_le_of_finrank_eq hplane ?_).symm
    rw [finrank_plane]
    apply Nat.le_antisymm
    · simpa only [finrank_plane] using Submodule.finrank_mono hplane
    · exact finrank_le_two_of_isotropic U (map_isotropic W hW a)

/-- Every nonzero totally isotropic subspace of symplectic four-space can
be moved by an actual symplectic matrix to the standard point or plane. -/
theorem isotropic_subspace_conjugate_standard (W : Submodule F (Vector F))
    (hne : W ≠ ⊥) (hW : ∀ x ∈ W, ∀ y ∈ W, form F x y = 0) :
    ∃ g : Sp F, W.map (toLinear g).toLinearMap = point F ∨
      W.map (toLinear g).toLinearMap = plane F := by
  obtain ⟨u, hu, hu0⟩ := W.ne_bot_iff.mp hne
  obtain ⟨k, hk⟩ := nonzero_vector_transitive hu0 e_zero_ne_zero
  obtain ⟨a, ha⟩ := standard_of_contains_point (W.map (toLinear k).toLinearMap)
    (map_isotropic W hW k) ⟨u, hu, hk⟩
  refine ⟨a * k, ?_⟩
  have hmap : W.map (toLinear (a * k)).toLinearMap =
      (W.map (toLinear k).toLinearMap).map (toLinear a).toLinearMap := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨k • u, ⟨u, hu, rfl⟩, (mul_smul a k u).symm⟩
    · rintro ⟨v, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u, hu, mul_smul a k u⟩
  rwa [hmap]

end Theory.SpecificGroups.SymplecticFour.TwoLocalCover
