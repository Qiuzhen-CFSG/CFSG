module

public import BenderSuzuki.MatrixGroups.Unitary

/-!
# Coefficient transport for identity-Gram unitary groups

An equivalence of fields compatible with their stored involutions sends
unitary matrices to unitary matrices entrywise. Applying the inverse
coefficient map proves that this is an actual group isomorphism.

This supplies the model comparison needed for the GU₂ centralizers in
Aschbacher–Smith, Lemma A.3.21(a), printed p.55 of `refs/quasithin.pdf`.
-/

open Matrix BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {F E : Type*} [Field F] [Field E] {n : ℕ}

private def coefficientGL (e : F ≃+* E) : GL (Fin n) F ≃* GL (Fin n) E :=
  { GeneralLinearGroup.map e.toRingHom with
    invFun := GeneralLinearGroup.map e.symm.toRingHom
    left_inv := by intro g; ext i j; exact e.symm_apply_apply (g i j)
    right_inv := by intro g; ext i j; exact e.apply_symm_apply (g i j) }

private theorem coefficient_mem_unitary (e : F ≃+* E)
    (J : HermitianForm n F) (K : HermitianForm n E)
    (hJ : J.form = 1) (hK : K.form = 1)
    (hc : ∀ x, e (J.conj x) = K.conj (e x)) (A : GL (Fin n) F) :
    coefficientGL e A ∈ K.unitarySubgroup ↔ A ∈ J.unitarySubgroup := by
  rw [K.mem_unitarySubgroup_iff, J.mem_unitarySubgroup_iff, hJ, hK, mul_one, mul_one]
  have hadj : K.conjTranspose (coefficientGL e A).val =
      (J.conjTranspose A.val).map e := by
    ext i j
    exact (hc (A.val j i)).symm
  have hval : (coefficientGL e A).val = A.val.map e := rfl
  rw [hadj, hval, ← Matrix.map_mul]
  constructor
  · intro hh
    ext i j
    apply e.injective
    simpa only [Matrix.map_apply, Matrix.one_apply, apply_ite, map_one, map_zero] using
      congrArg (fun B => B i j) hh
  · intro hh
    rw [hh]
    exact Matrix.map_one e (map_zero e) (map_one e)

/-- Entrywise coefficient transport between identity-Gram unitary groups. -/
public def unitaryCoefficientEquivOfIdentity (e : F ≃+* E)
    (J : HermitianForm n F) (K : HermitianForm n E)
    (hJ : J.form = 1) (hK : K.form = 1)
    (hc : ∀ x, e (J.conj x) = K.conj (e x)) :
    J.unitarySubgroup ≃* K.unitarySubgroup where
  toFun A := ⟨coefficientGL e A.val,
    (coefficient_mem_unitary e J K hJ hK hc A.val).mpr A.property⟩
  invFun B := ⟨(coefficientGL e).symm B.val,
    (coefficient_mem_unitary e J K hJ hK hc _).mp (by simp)⟩
  left_inv A := by apply Subtype.ext; exact (coefficientGL e).symm_apply_apply A.val
  right_inv B := by apply Subtype.ext; exact (coefficientGL e).apply_symm_apply B.val
  map_mul' A B := by apply Subtype.ext; exact map_mul (coefficientGL e) A.val B.val

end BenderSuzuki.MatrixGroups.HermitianForm
