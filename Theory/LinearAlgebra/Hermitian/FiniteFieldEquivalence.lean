module

public import Theory.LinearAlgebra.Hermitian.IdentityGramEquivalence
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Equivalence of finite special unitary models

Two nondegenerate Hermitian forms in the same dimension over fields of order
q², whose stored involutions have fixed fields of order q, define isomorphic
special unitary groups. The cardinalities identify both involutions with
q-Frobenius. Orthonormal bases reduce the forms to the identity, and a field
isomorphism acts entrywise, preserving the form and determinant one.

The coefficient calculation adapts the projective calculation in
`Theory/SpecificGroups/ClassicalUnitary/UnitaryFourThree/Model.lean` to the
special groups and arbitrary Gram matrices. Basis existence and the Frobenius
identification are Huppert II.10.4. The dimension-three application is the
model comparison needed for Aschbacher–Smith A.3.21(b), printed p.55.
-/

open Matrix BenderSuzuki.MatrixGroups
public noncomputable section
namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {F E : Type*} [Field F] [Field E] {n : ℕ}

private def coefficientGL (e : F ≃+* E) : GL (Fin n) F ≃* GL (Fin n) E :=
  { GeneralLinearGroup.map e.toRingHom with
    invFun := GeneralLinearGroup.map e.symm.toRingHom
    left_inv := by intro g; ext i j; exact e.symm_apply_apply (g i j)
    right_inv := by intro g; ext i j; exact e.apply_symm_apply (g i j) }

private theorem coefficient_special_iff (e : F ≃+* E)
    (J : HermitianForm n F) (K : HermitianForm n E)
    (hc : ∀ x, e (J.conj x) = K.conj (e x))
    (hform : J.form.map e = K.form) (x : GL (Fin n) F) :
    coefficientGL e x ∈ K.specialSubgroup ↔ x ∈ J.specialSubgroup := by
  rw [K.mem_specialSubgroup_iff, J.mem_specialSubgroup_iff]
  have hadj : K.conjTranspose (coefficientGL e x).val =
      (J.conjTranspose x.val).map e := by
    ext i j
    exact (hc (x.val j i)).symm
  have hval : (coefficientGL e x).val = x.val.map e := rfl
  have hu : K.conjTranspose (coefficientGL e x).val * K.form *
      (coefficientGL e x).val = K.form ↔
      J.conjTranspose x.val * J.form * x.val = J.form := by
    rw [hadj, hval, ← hform, ← Matrix.map_mul, ← Matrix.map_mul]
    exact e.toEquiv.mapMatrix.injective.eq_iff
  rw [hu]
  apply and_congr_right
  intro _
  change GeneralLinearGroup.det (GeneralLinearGroup.map e.toRingHom x) = 1 ↔ _
  rw [GeneralLinearGroup.map_det]
  constructor
  · intro hh
    apply Units.ext
    apply e.injective
    simpa using congrArg Units.val hh
  · intro hh
    rw [hh, map_one]

/-- Entrywise field transport restricts to the actual determinant-one isometry groups. -/
def coefficientSpecialEquiv (e : F ≃+* E)
    (J : HermitianForm n F) (K : HermitianForm n E)
    (hc : ∀ x, e (J.conj x) = K.conj (e x))
    (hform : J.form.map e = K.form) : J.specialSubgroup ≃* K.specialSubgroup where
  toFun x := ⟨coefficientGL e x.val, (coefficient_special_iff e J K hc hform x.val).2 x.property⟩
  invFun x := ⟨(coefficientGL e).symm x.val,
    (coefficient_special_iff e J K hc hform _).1 (by simp)⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_mul' x y := by ext; simp

/-- Equal matrix-field and fixed-field orders determine the special unitary group,
with arbitrary nondegenerate Hermitian forms on both sides. -/
theorem nonempty_specialEquiv_of_card [Finite F] [Finite E]
    (J : HermitianForm n F) (K : HermitianForm n E) (q : ℕ)
    (hF : Nat.card F = q ^ 2) (hJ : Nat.card {x : F // J.conj x = x} = q)
    (hE : Nat.card E = q ^ 2) (hK : Nat.card {x : E // K.conj x = x} = q) :
    Nonempty (J.specialSubgroup ≃* K.specialSubgroup) := by
  let : Fintype F := Fintype.ofFinite F
  let : Fintype E := Fintype.ofFinite E
  let e : F ≃+* E := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card] using hF.trans hE.symm)
  obtain ⟨C, hC⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis n J q hF hJ
  obtain ⟨D, hD⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis n K q hE hK
  let c := coefficientSpecialEquiv e (IdentityGram.identityGram J) (IdentityGram.identityGram K)
    (fun x => by
      change e (J.conj x) = K.conj (e x)
      rw [BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius J q hF hJ,
        BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius K q hE hK, map_pow])
    (by simp)
  exact ⟨(IdentityGram.specialEquiv J C hC).trans
    (c.trans (IdentityGram.specialEquiv K D hD).symm)⟩
end BenderSuzuki.MatrixGroups.HermitianForm
