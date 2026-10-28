module

public import Theory.SpecificGroups.SymplecticFour.RootNormalizerResidual.Standard
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Coordinates
public import Theory.SpecificGroups.SymplecticFour.SimpleQuotients.Primitivity
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.Parabolics
public import Mathlib.Algebra.Group.Subgroup.Order

/-!
# Normalizers and maximal parabolics in symplectic four-space

The two-root plane is the actual embedded center of the standard unipotent
Sylow subgroup, as identified by `CentralRootGeometry.parameter_range`.
Its normalizer is the Borel: conjugating the short root forces the lower-left
matrix block to vanish, and the long root forces the remaining point entry
to vanish. Conversely, both root subgroups are normalized by the Borel.

The point parabolic is the inverse image of a point stabilizer in the actual
central quotient's primitive projective action. It is therefore maximal.
The genuine exceptional graph automorphism exchanges the two parabolics and
transports maximality to the plane parabolic. Finally, the lower long root 3
centralizes root 0 and moves the standard plane, explicitly witnessing that
the full root centralizer is not contained in the Borel.

These intrinsic statements supply the subgroup geometry used in
Aschbacher–Smith, E.6.8(2), printed pp.247–248 (PDF pp.258–259) of
`refs/quasithin.pdf`, combined manuscript of 1 March 2004.
-/

public section

open Matrix Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.BorelActionGeometry
open CentralRootGeometry RootNormalizerResidual
variable {F : Type*} [Field F]

section CharacteristicTwo
variable [CharP F 2]
local notation "a" => (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "b" => (Sum.inl (1 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "c" => (Sum.inr (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "d" => (Sum.inr (1 : Fin 2) : Fin 2 ⊕ Fin 2)

private theorem parameter_matrix (p : Multiplicative F × Multiplicative F) :
    (parameter p).val = fromBlocks 1 !![p.1.toAdd, p.2.toAdd; p.2.toAdd, 0] 0 1 := by
  change (element 0 p.1.toAdd p.2.toAdd 0).val.val = _
  rw [element_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fromBlocks]

omit [CharP F 2] in
private theorem conjugate_long_entry (g : Sp F) :
    (g * rootElement 0 1 * g⁻¹).val b d = g.val b a ^ 2 := by
  have hi : (rootElement (K := F) 0 1).val - 1 = Matrix.single a c 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rootElement, rootMatrix, fromBlocks, Matrix.single]
  have hm : (g * rootElement 0 1 * g⁻¹).val =
      1 + g.val * Matrix.single a c 1 * (g⁻¹).val := by
    rw [← hi, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    have hh : g.val * (g⁻¹).val = 1 := congrArg Subtype.val (mul_inv_cancel g)
    rw [hh]
    change _ = 1 + (_ - 1)
    abel
  rw [hm, SymplecticGroup.coe_inv]
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
    Matrix.single, Matrix.J, fromBlocks, Matrix.one_apply, pow_two]

/-- The full normalizer of the embedded Sylow center is the standard Borel. -/
theorem normalizer_centralPlane_eq_borel :
    normalizer ((parameter (F := F)).range : Set (Sp F)) = borel := by
  apply le_antisymm
  · intro g hg
    have h0 : rootElement (K := F) 0 1 ∈ (parameter (F := F)).range := by
      refine ⟨(Multiplicative.ofAdd 1, Multiplicative.ofAdd 0), ?_⟩
      simp [parameter_apply, RootSubgroup.element_zero]
    have h4 : rootElement (K := F) 4 1 ∈ (parameter (F := F)).range := by
      refine ⟨(Multiplicative.ofAdd 0, Multiplicative.ofAdd 1), ?_⟩
      simp [parameter_apply, RootSubgroup.element_zero]
    obtain ⟨p, hp⟩ := (mem_normalizer_iff.mp hg _).mp h0
    obtain ⟨q, hq⟩ := (mem_normalizer_iff.mp hg _).mp h4
    have hlong := congrArg (fun x : Sp F => x.val b d) hp
    rw [parameter_matrix, conjugate_long_entry] at hlong
    have hb : g.val b a = 0 := eq_zero_of_pow_eq_zero (show g.val b a ^ 2 = 0 from hlong.symm)
    have he : g * rootElement 4 1 = parameter q * g := by
      rw [hq, mul_assoc, inv_mul_cancel, mul_one]
    apply (mem_borel_iff g).mpr
    refine ⟨hb, ?_⟩
    intro i j
    have hh := congrArg (fun x : Sp F => x.val (.inr i) (.inr (1 - j))) he
    change (g.val * (rootElement 4 (1 : F)).val) _ _ = ((parameter q).val * g.val) _ _ at hh
    rw [parameter_matrix] at hh
    fin_cases i <;> fin_cases j <;>
      simpa [rootElement, rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type,
        Fin.sum_univ_two, fromBlocks, Matrix.single, Matrix.one_apply] using hh
  · apply le_set_normalizer_iff.mpr
    intro g hg x hx
    obtain ⟨p, rfl⟩ := hx
    change MulAut.conj g (parameter p) ∈ (parameter (F := F)).range
    rw [parameter_apply, map_mul]
    change (g * rootElement 0 p.1.toAdd * g⁻¹) *
      (g * rootElement 4 p.2.toAdd * g⁻¹) ∈ (parameter (F := F)).range
    rw [point_conjugate g hg.1, plane_conjugate g hg.2]
    exact ⟨(Multiplicative.ofAdd _, Multiplicative.ofAdd _), parameter_apply _⟩

/-- An explicit lower root lies in the full ambient long-root centralizer. -/
theorem root_three_mem_centralizer_zero :
    rootElement 3 (1 : F) ∈ centralizer (RootSubgroup.group (F := F) 0 : Set (Sp F)) := by
  rw [centralizer_zero_eq, mem_pointLocal_iff]
  simp [mem_pointParabolic_iff, rootElement, rootMatrix, fromBlocks, single]

omit [CharP F 2] in
/-- The same lower root moves the standard plane, so it escapes the Borel. -/
theorem root_three_not_mem_borel : rootElement 3 (1 : F) ∉ borel := by
  intro h
  have hh := (mem_planeParabolic_iff _).mp h.2 1 1
  simp [rootElement, rootMatrix, fromBlocks, single] at hh

/-- The full ambient centralizer of root 0 is not contained in the Borel. -/
theorem centralizer_zero_not_le_borel :
    ¬ centralizer (RootSubgroup.group (F := F) 0 : Set (Sp F)) ≤ borel := by
  intro h
  exact root_three_not_mem_borel (h root_three_mem_centralizer_zero)

end CharacteristicTwo

/-- The concrete point parabolic is the inverse image of the actual projective stabilizer. -/
theorem pointParabolic_eq_projective_stabilizer_comap :
    pointParabolic (F := F) =
      (MulAction.stabilizer (Matrix.PSp4Three.PSp 2 F)
        (Matrix.PSp4Three.ePoint (n := 2) (F := F) 0)).comap
        Matrix.PSp4Three.projection := by
  ext g
  rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Matrix.PSp4Three.projection_smul,
    Matrix.PSp4Three.ePoint, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  rw [pointParabolic, mem_stabilizer_iff]
  change (∀ x ∈ point F, g • x ∈ point F) ↔ ∃ t : F, t • e 0 = g • e 0
  constructor
  · intro h
    exact Submodule.mem_span_singleton.mp (h (e 0) (Submodule.subset_span (by simp)))
  · rintro ⟨t, ht⟩ x hx
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hx
    change toLinear g (s • e 0) ∈ point F
    rw [map_smul, toLinear_apply, ← ht]
    exact (point F).smul_mem s ((point F).smul_mem t (Submodule.subset_span (by simp)))

private theorem points_nontrivial : Nontrivial (Matrix.PSp4Three.Points 2 F) := by
  refine ⟨⟨Matrix.PSp4Three.ePoint 0, Matrix.PSp4Three.ePoint 1, ?_⟩⟩
  intro h
  obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp h
  have hh := congrFun ht (.inl 0)
  simp [Matrix.PSp4Three.e] at hh

/-- Primitivity of the projective action makes the point parabolic maximal. -/
theorem pointParabolic_isCoatom [Finite F] : IsCoatom (pointParabolic (F := F)) := by
  let := points_nontrivial (F := F)
  let := SimpleQuotients.projective_preprimitive (F := F)
  rw [pointParabolic_eq_projective_stabilizer_comap]
  exact Subgroup.isCoatom_comap_of_surjective Matrix.PSp4Three.projection_surjective
    (MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive _ _)

/-- The exceptional graph automorphism transports maximality to the plane parabolic. -/
theorem planeParabolic_isCoatom [Finite F] [CharP F 2] :
    IsCoatom (planeParabolic (F := F)) := by
  rw [← DiagramAutomorphisms.ExceptionalGraph.graphAut_map_point]
  exact (OrderIso.isCoatom_iff
    (DiagramAutomorphisms.ExceptionalGraph.graphAut (F := F)).mapSubgroup _).mpr
      pointParabolic_isCoatom

end Theory.SpecificGroups.SymplecticFour.BorelActionGeometry
