module

public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.OuterModel.FieldTransport
import all Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.OuterModel.FieldTransport
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.UnitaryConjugation

/-!
# Coefficient transport of the unitary conjugators

Mapping matrix coefficients along a field isomorphism intertwining the
Hermitian involutions preserves unitary matrices and their conjugation action
on the actual projective special-unitary images. The intentional implementation
import extends `FieldTransport` with its ambient PGL formula, without changing
that module or exposing its private implementation in a public type.
This supplies the unitary factor in the concrete Frobenius normalizer in
Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3, pp.10–11.
-/

public noncomputable section
open Matrix
namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Outer.OddNormalizer
variable {E F : Type*} [Field E] [Field F]

private theorem coefficientEquiv_apply_val (e : E ≃+* F)
    (J : HermitianForm 3 E) (K : HermitianForm 3 F)
    (hc : ∀ x, e (J.conj x) = K.conj (e x)) (hf : J.form.map e = K.form)
    (x : ProjectiveSpecialUnitaryMatrixGroup J) :
    (coefficientEquiv e J K hc hf x).val = ProjGenLinGroup.map e.toRingHom x.val := by
  rfl

def coefficientUnitary (e : E ≃+* F)
    (J : HermitianForm 3 E) (K : HermitianForm 3 F)
    (hc : ∀ x, e (J.conj x) = K.conj (e x)) (hf : J.form.map e = K.form)
    (u : J.unitarySubgroup) : K.unitarySubgroup := by
  refine ⟨GeneralLinearGroup.map e.toRingHom u.val, ?_⟩
  rw [mem_unitarySubgroup_iff]
  change K.conjTranspose (u.val.val.map e) * K.form * u.val.val.map e = K.form
  have hadj : K.conjTranspose (u.val.val.map e) = (J.conjTranspose u.val.val).map e := by
    ext i j
    exact (hc _).symm
  rw [hadj, ← hf, ← Matrix.map_mul, ← Matrix.map_mul]
  exact congrArg (fun A : Matrix (Fin 3) (Fin 3) E => A.map e)
    ((J.mem_unitarySubgroup_iff u.val).mp u.property)

private theorem coefficientUnitary_val (e : E ≃+* F)
    (J : HermitianForm 3 E) (K : HermitianForm 3 F)
    (hc : ∀ x, e (J.conj x) = K.conj (e x)) (hf : J.form.map e = K.form)
    (u : J.unitarySubgroup) :
    (coefficientUnitary e J K hc hf u).val = GeneralLinearGroup.map e.toRingHom u.val := by rfl

theorem coefficientEquiv_unitaryConj (e : E ≃+* F)
    (J : HermitianForm 3 E) (K : HermitianForm 3 F)
    (hc : ∀ x, e (J.conj x) = K.conj (e x)) (hf : J.form.map e = K.form)
    (u : J.unitarySubgroup) :
    MulAut.congr (coefficientEquiv e J K hc hf) (J.unitaryConj u) =
      K.unitaryConj (coefficientUnitary e J K hc hf u) := by
  apply MulEquiv.ext
  intro x
  obtain ⟨x, rfl⟩ := (coefficientEquiv e J K hc hf).surjective x
  change coefficientEquiv e J K hc hf
    (J.unitaryConj u ((coefficientEquiv e J K hc hf).symm
      (coefficientEquiv e J K hc hf x))) = _
  rw [MulEquiv.symm_apply_apply]
  apply Subtype.ext
  simp only [coefficientEquiv_apply_val, unitaryConj_apply_val, map_mul, map_inv,
    ProjGenLinGroup.map_mk, coefficientUnitary_val]

end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Outer.OddNormalizer
