module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.IsotropicStabilizers.Dimension
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.IsotropicStabilizers.Coordinates
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.IsotropicStabilizers.Transport.FormBasis

/-!
# Projective isotropic-stabilizer transport from adapted bases

An invertible matrix whose Hermitian Gram matrix is the antidiagonal form
identifies the two special unitary groups by conjugation. If it also carries
the coordinate line or plane onto a given subspace, conjugation identifies
the full setwise stabilizers. Compatibility with the actual SU-to-PGL maps
then identifies their projective images, retaining the scalar kernel.
The basis matrix itself need not have determinant one.

The equivalences here take the adapted basis as an explicit input. Existence
of an ambient isometry is proved in `Transport.FormBasis`; existence with the
specified line or plane image is the remaining geometric input.

Source: the unitary conventions and Witt's lemma, GLS3, section 2.7; the
reducible-subgroup contribution to condition K in Aschbacher–Smith,
Theorem 0.1.2(4), printed pp.4 and 482 of `refs/quasithin.pdf`.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ReducibleGeometry
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.IsotropicStabilizers
open scoped Pointwise
public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.IsotropicStabilizers

private def coordinateSpecialEquiv (C : GL (Fin 4) FiniteField.Nine)
    (hC : (form 4).conjTranspose C.val * (form 4).form * C.val = coordinateForm.form) :
    (form 4).specialSubgroup ≃* coordinateForm.specialSubgroup :=
  UnitaryFourFormTransport.specialEquiv (form 4) C hC

private def coordinateProjectiveEquiv (C : GL (Fin 4) FiniteField.Nine)
    (hC : (form 4).conjTranspose C.val * (form 4).form * C.val = coordinateForm.form) :
    Carrier 4 ≃* CoordinateCarrier :=
  UnitaryFourFormTransport.projectiveEquiv (form 4) C hC

private def coordinateSpecialStabilizer (V : Submodule FiniteField.Nine (Space 4)) :
    Subgroup coordinateForm.specialSubgroup :=
  (MulAction.stabilizer (GL (Fin 4) FiniteField.Nine) (V : Set (Space 4))).comap
    coordinateForm.specialSubgroup.subtype

private theorem mem_coordinateSpecialStabilizer_iff
    (V : Submodule FiniteField.Nine (Space 4)) (g : coordinateForm.specialSubgroup) :
    g ∈ coordinateSpecialStabilizer V ↔ ∀ v, g.val.val *ᵥ v ∈ V ↔ v ∈ V := by
  change g.val ∈ MulAction.stabilizer _ (V : Set (Space 4)) ↔ _
  rw [MulAction.mem_stabilizer_set]
  rfl

private theorem conjugate_mem_stabilizer_iff
    (W V : Submodule FiniteField.Nine (Space 4))
    (C : GL (Fin 4) FiniteField.Nine)
    (hC : (form 4).conjTranspose C.val * (form 4).form * C.val = coordinateForm.form)
    (hW : ∀ v, C.val *ᵥ v ∈ W ↔ v ∈ V)
    (g : (form 4).specialSubgroup) :
    coordinateSpecialEquiv C hC g ∈
        coordinateSpecialStabilizer V ↔ g ∈ specialStabilizer W := by
  rw [mem_coordinateSpecialStabilizer_iff, mem_specialStabilizer_iff]
  have hcanc (v : Space 4) : C.val *ᵥ ((C⁻¹).val *ᵥ v) = v := by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hconj (v : Space 4) :
      (coordinateSpecialEquiv C hC g).val.val *ᵥ v =
        (C⁻¹).val *ᵥ (g.val.val *ᵥ (C.val *ᵥ v)) := by
    have he : (coordinateSpecialEquiv C hC g).val = C⁻¹ * g.val * C :=
      UnitaryFourFormTransport.specialEquiv_apply (form 4) C hC g
    rw [he]
    simp only [Units.val_mul, mulVec_mulVec, mul_assoc]
  constructor
  · intro hg v
    have h := hg ((C⁻¹).val *ᵥ v)
    rw [hconj, hcanc] at h
    have hl := hW ((C⁻¹).val *ᵥ (g.val.val *ᵥ v))
    have hr := hW ((C⁻¹).val *ᵥ v)
    rw [hcanc] at hl hr
    exact hl.trans (h.trans hr.symm)
  · intro hg v
    rw [hconj]
    have hl := hW ((C⁻¹).val *ᵥ (g.val.val *ᵥ (C.val *ᵥ v)))
    rw [hcanc] at hl
    exact hl.symm.trans ((hg (C.val *ᵥ v)).trans (hW v))

private theorem map_specialStabilizer
    (W V : Submodule FiniteField.Nine (Space 4))
    (C : GL (Fin 4) FiniteField.Nine)
    (hC : (form 4).conjTranspose C.val * (form 4).form * C.val = coordinateForm.form)
    (hW : ∀ v, C.val *ᵥ v ∈ W ↔ v ∈ V) :
    (specialStabilizer W).map
        (coordinateSpecialEquiv C hC).toMonoidHom =
      coordinateSpecialStabilizer V := by
  let e := coordinateSpecialEquiv C hC
  ext g
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (conjugate_mem_stabilizer_iff W V C hC hW a).2 ha
  · intro hg
    refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
    apply (conjugate_mem_stabilizer_iff W V C hC hW (e.symm g)).1
    change e (e.symm g) ∈ coordinateSpecialStabilizer V
    simpa only [e.apply_symm_apply] using hg

private def projectiveStabilizerEquivOfBasis
    (W V : Submodule FiniteField.Nine (Space 4))
    (C : GL (Fin 4) FiniteField.Nine)
    (hC : (form 4).conjTranspose C.val * (form 4).form * C.val = coordinateForm.form)
    (hW : ∀ v, C.val *ᵥ v ∈ W ↔ v ∈ V) :
    projectiveStabilizer W ≃*
      (coordinateSpecialStabilizer V).map (UnitaryFourFlag.project FiniteField.Nine coordinateForm) := by
  let e := coordinateSpecialEquiv C hC
  let ep := coordinateProjectiveEquiv C hC
  have hcomm : ep.toMonoidHom.comp (project 4) =
      (UnitaryFourFlag.project FiniteField.Nine coordinateForm).comp e.toMonoidHom := by
    ext g : 1
    apply Subtype.ext
    exact UnitaryFourFormTransport.projectiveEquiv_mk (form 4) C hC g
  have hm : (projectiveStabilizer W).map ep.toMonoidHom =
      (coordinateSpecialStabilizer V).map
        (UnitaryFourFlag.project FiniteField.Nine coordinateForm) := by
    rw [projectiveStabilizer, Subgroup.map_map, hcomm, ← Subgroup.map_map,
      map_specialStabilizer W V C hC hW]
  exact (ep.subgroupMap (projectiveStabilizer W)).trans (MulEquiv.subgroupCongr hm)

/-- A form-preserving basis carrying the coordinate line to `W` identifies the
full projective stabilizers, including their scalar quotients. -/
def pointStabilizerEquivOfBasis
    (W : Submodule FiniteField.Nine (Space 4))
    (C : GL (Fin 4) FiniteField.Nine)
    (hC : (form 4).conjTranspose C.val * (form 4).form * C.val = coordinateForm.form)
    (hW : ∀ v, C.val *ᵥ v ∈ W ↔ v ∈ UnitaryFourFlag.pointSpace FiniteField.Nine) :
    projectiveStabilizer W ≃* coordinatePointStabilizer :=
  projectiveStabilizerEquivOfBasis W (UnitaryFourFlag.pointSpace FiniteField.Nine) C hC hW

/-- A form-preserving basis carrying the coordinate plane to `W` identifies the
full projective stabilizers, including their scalar quotients. -/
def planeStabilizerEquivOfBasis
    (W : Submodule FiniteField.Nine (Space 4))
    (C : GL (Fin 4) FiniteField.Nine)
    (hC : (form 4).conjTranspose C.val * (form 4).form * C.val = coordinateForm.form)
    (hW : ∀ v, C.val *ᵥ v ∈ W ↔ v ∈ UnitaryFourFlag.planeSpace FiniteField.Nine) :
    projectiveStabilizer W ≃* coordinatePlaneStabilizer :=
  projectiveStabilizerEquivOfBasis W (UnitaryFourFlag.planeSpace FiniteField.Nine) C hC hW

/-- The point-stabilizer equivalence is induced by conjugation in the actual PGL. -/
theorem pointStabilizerEquivOfBasis_apply
    (W : Submodule FiniteField.Nine (Space 4))
    (C : GL (Fin 4) FiniteField.Nine)
    (hC : (form 4).conjTranspose C.val * (form 4).form * C.val = coordinateForm.form)
    (hW : ∀ v, C.val *ᵥ v ∈ W ↔ v ∈ UnitaryFourFlag.pointSpace FiniteField.Nine)
    (x : projectiveStabilizer W) :
    (pointStabilizerEquivOfBasis W C hC hW x).val.val =
      (ProjGenLinGroup.mk C)⁻¹ * x.val.val * ProjGenLinGroup.mk C := by
  change (coordinateProjectiveEquiv C hC x.val).val = _
  exact UnitaryFourFormTransport.projectiveEquiv_apply (form 4) C hC x.val

/-- The plane-stabilizer equivalence is induced by conjugation in the actual PGL. -/
theorem planeStabilizerEquivOfBasis_apply
    (W : Submodule FiniteField.Nine (Space 4))
    (C : GL (Fin 4) FiniteField.Nine)
    (hC : (form 4).conjTranspose C.val * (form 4).form * C.val = coordinateForm.form)
    (hW : ∀ v, C.val *ᵥ v ∈ W ↔ v ∈ UnitaryFourFlag.planeSpace FiniteField.Nine)
    (x : projectiveStabilizer W) :
    (planeStabilizerEquivOfBasis W C hC hW x).val.val =
      (ProjGenLinGroup.mk C)⁻¹ * x.val.val * ProjGenLinGroup.mk C := by
  change (coordinateProjectiveEquiv C hC x.val).val = _
  exact UnitaryFourFormTransport.projectiveEquiv_apply (form 4) C hC x.val

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.IsotropicStabilizers
