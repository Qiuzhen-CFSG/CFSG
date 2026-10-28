module

public import Theory.SpecificGroups.ClassicalUnitary.SylowOvergroupParabolics
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Complete isotropic flags and their projective stabilizers

A complete isotropic flag has one totally isotropic subspace of each
dimension from one to the Witt index `d / 2`. Its Borel is the intersection
of the literal projective special-unitary stabilizers. No existence or
classification assertion is stored in this definition.

Special unitary matrices preserve the stored Hermitian pairing for arbitrary
forms. Thus they preserve total isotropy, and conjugation transports the
exact stabilizers through the canonical SU-to-PSU map.

Source: GLS3, §§2.6--2.7. The conjugation argument extends the dimension-five
calculation in `ClassicalUnitary.FiveIsotropicGeometry` to arbitrary forms
and dimensions.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix Subgroup
open scoped Pointwise

namespace Theory.SpecificGroups.ClassicalUnitary.SylowOvergroupParabolics

variable {F : Type*} [Field F] {d : ℕ} (J : HermitianForm d F)

/-- The full geometric flag, with all dimensions and isotropy explicit. -/
structure IsotropicFlag where
  space : Fin (d / 2) → Submodule F (Fin d → F)
  monotone : Monotone space
  finrank : ∀ i, Module.finrank F (space i) = i.val + 1
  isotropic : ∀ i, TotallyIsotropic J (space i)

/-- The actual projective stabilizer of every member of the flag. -/
def IsotropicFlag.borel (f : IsotropicFlag J) :
    Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  ⨅ i, parabolic J (f.space i)

theorem IsotropicFlag.borel_le (f : IsotropicFlag J) (i : Fin (d / 2)) :
    f.borel ≤ parabolic J (f.space i) := iInf_le _ i

/-- SU preserves the Hermitian pairing, with no identity-form restriction. -/
theorem hermitianPairing_linearAction (g : J.specialSubgroup) (v w : Fin d → F) :
    dotProduct (fun i => J.conj (linearAction J g v i))
        (J.form.mulVec (linearAction J g w)) =
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec w) := by
  have hg := ((J.mem_specialSubgroup_iff g.val).mp g.property).1
  change (fun i => J.conj ((g.val.val *ᵥ v) i)) ⬝ᵥ
    (J.form *ᵥ (g.val.val *ᵥ w)) = _
  rw [show (fun i => J.conj ((g.val.val *ᵥ v) i)) =
    (g.val.val.map J.conj) *ᵥ (fun i => J.conj (v i)) from
      funext (RingHom.map_mulVec J.conj.toRingHom g.val.val v)]
  rw [← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  change (fun i => J.conj (v i)) ⬝ᵥ
    (J.conjTranspose g.val.val * J.form * g.val.val) *ᵥ w = _
  rw [hg]

theorem TotallyIsotropic.map_linearAction {W : Submodule F (Fin d → F)}
    (hW : TotallyIsotropic J W) (g : J.specialSubgroup) :
    TotallyIsotropic J (W.map (linearAction J g).toLinearMap) := by
  rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
  exact (hermitianPairing_linearAction J g v w).trans (hW v hv w hw)

/-- Moving a subspace conjugates its exact special-unitary stabilizer. -/
theorem specialStabilizer_map_linearAction (g : J.specialSubgroup)
    (W : Submodule F (Fin d → F)) :
    specialStabilizer J (W.map (linearAction J g).toLinearMap) =
      (specialStabilizer J W).map (MulAut.conj g).toMonoidHom := by
  change (MulAction.stabilizer ((Fin d → F) ≃ₗ[F] (Fin d → F))
    (linearAction J g • W)).comap (linearAction J) = _
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  ext a
  simp only [Subgroup.mem_comap, Subgroup.mem_map_equiv]
  change (linearAction J g)⁻¹ * linearAction J a * linearAction J g ∈
      MulAction.stabilizer _ W ↔
    linearAction J (g⁻¹ * a * g) ∈ MulAction.stabilizer _ W
  rw [map_mul, map_mul, map_inv]

/-- The conjugation formula uses the literal SU-to-PSU projection. -/
theorem parabolic_map_linearAction (g : J.specialSubgroup)
    (W : Submodule F (Fin d → F)) :
    parabolic J (W.map (linearAction J g).toLinearMap) =
      (parabolic J W).map (MulAut.conj (project J g)).toMonoidHom := by
  have hcomm : (project J).comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (project J g)).toMonoidHom.comp (project J) := by
    ext a
    simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, map_mul, map_inv]
  rw [parabolic, specialStabilizer_map_linearAction, Subgroup.map_map, hcomm,
    ← Subgroup.map_map]
  rfl

end Theory.SpecificGroups.ClassicalUnitary.SylowOvergroupParabolics
