module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.Descent.SymmetricForms
public import Theory.SpecificGroups.ClassicalUnitary.FiveFlag
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.FieldDescent.FixedSpace
public import Mathlib.FieldTheory.Fixed

/-!
# Five-dimensional unitary cocycle descent

A semilinear involution has a basis of fixed vectors, even in characteristic
two. Its Gram matrix is a nonsingular symmetric matrix over the fixed field.
The five-dimensional symmetric-form congruence normalizes that basis to a
unitary one. Thus a concrete unitary cocycle for Hermitian conjugation is a
unitary coboundary, with no field-size bound on a determinant polynomial.

This is the matrix descent required by the graph case of F.4.29(2), printed
p.289 of refs/quasithin.pdf. It does not provide a semilinear formula for an
abstract projective automorphism or its compatibility with a marked flag.
-/

open Matrix Module BenderSuzuki.MatrixGroups
public noncomputable section
namespace Theory.SpecificGroups.UnitaryFive.Descent
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.FieldDescent
variable {F : Type*} [Field F] (J : HermitianForm 5 F)

private def twist (u : GL (Fin 5) F) : (Fin 5 → F) →+ (Fin 5 → F) where
  toFun v := u.val *ᵥ (J.conj ∘ v)
  map_zero' := by simp
  map_add' v w := by
    change u.val *ᵥ (J.conj ∘ (v + w)) = _
    have he : J.conj ∘ (v + w) = (J.conj ∘ v) + (J.conj ∘ w) := by ext i; simp
    rw [he, Matrix.mulVec_add]

private theorem twist_smul (u : GL (Fin 5) F) (a : F) (v : Fin 5 → F) :
    twist J u (a • v) = J.conj a • twist J u v := by
  change u.val *ᵥ (J.conj ∘ (a • v)) = _
  have he : J.conj ∘ (a • v) = J.conj a • (J.conj ∘ v) := by ext i; simp
  rw [he, Matrix.mulVec_smul]
  rfl

private theorem twist_square (u : GL (Fin 5) F)
    (hu : u * GeneralLinearGroup.map J.conj.toRingHom u = 1) (v : Fin 5 → F) :
    twist J u (twist J u v) = v := by
  have hc : u.val * u.val.map J.conj = 1 := congrArg Units.val hu
  have he : J.conj ∘ (u.val *ᵥ (J.conj ∘ v)) = u.val.map J.conj *ᵥ v := by
    ext i
    change J.conj.toRingHom ((u.val *ᵥ (J.conj ∘ v)) i) = _
    rw [J.conj.toRingHom.map_mulVec]
    congr 2
    exact funext (fun j => J.conj_involutive (v j))
  change u.val *ᵥ (J.conj ∘ (u.val *ᵥ (J.conj ∘ v))) = v
  rw [he, Matrix.mulVec_mulVec, hc, Matrix.one_mulVec]

/-- A matrix cocycle has an invertible basis of fixed semilinear vectors. -/
theorem exists_linear_descent_basis (hσ : J.conj ≠ 1) (u : GL (Fin 5) F)
    (hu : u * GeneralLinearGroup.map J.conj.toRingHom u = 1) :
    ∃ P : GL (Fin 5) F, u * GeneralLinearGroup.map J.conj.toRingHom P = P := by
  classical
  obtain ⟨s,b,hb⟩ := exists_fixed_basis J.conj hσ (twist J u)
    (twist_smul J u) (twist_square J u hu)
  let c := b.reindex (b.indexEquiv (Pi.basisFun F (Fin 5)))
  let P : Matrix (Fin 5) (Fin 5) F := (Pi.basisFun F (Fin 5)).toMatrix c
  have hfix (j : Fin 5) : u.val *ᵥ (J.conj ∘ fun i => P i j) = fun i => P i j := by
    simpa [P, c, Module.Basis.toMatrix_apply, twist] using
      hb ((b.indexEquiv (Pi.basisFun F (Fin 5))).symm j)
  have hP : IsUnit P := by
    let := Module.Basis.invertibleToMatrix (Pi.basisFun F (Fin 5)) c
    exact isUnit_of_invertible P
  refine ⟨hP.unit, ?_⟩
  apply Units.ext
  ext i j
  exact congrFun (hfix j) i

private theorem adjoint_mul (A B : Matrix (Fin 5) (Fin 5) F) :
    J.conjTranspose (A * B) = J.conjTranspose B * J.conjTranspose A := by
  change ((J.conj : F →+* F).mapMatrix (A * B)).transpose = _
  rw [map_mul, transpose_mul]
  rfl

private theorem adjoint_adjoint (A : Matrix (Fin 5) (Fin 5) F) :
    J.conjTranspose (J.conjTranspose A) = A := by
  ext i j
  exact J.conj_involutive _

private theorem adjoint_form : J.conjTranspose J.form = J.form := by
  ext i j
  exact J.form_hermitian i j

variable [Finite F] [CharP F 2]

/-- Normalize a fixed symmetric Gram matrix over the actual fixed subfield. -/
theorem fixed_symmetric_congruence (hJ : J.form = 1)
    (S : Matrix (Fin 5) (Fin 5) F)
    (hs : S.transpose = S) (hfix : S.map J.conj = S) (hd : S.det ≠ 0) :
    ∃ C : GL (Fin 5) F, C.val.map J.conj = C.val ∧
      C.val.transpose * S * C.val = J.form := by
  let K := FixedBy.subfield F J.conj
  let S₀ : Matrix (Fin 5) (Fin 5) K := fun i j =>
    ⟨S i j, congrArg (fun M : Matrix (Fin 5) (Fin 5) F => M i j) hfix⟩
  have hm : S₀.map K.subtype = S := rfl
  have hs₀ : S₀.transpose = S₀ := by
    ext i j
    exact congrArg (fun M : Matrix (Fin 5) (Fin 5) F => M i j) hs
  have hd₀ : S₀.det ≠ 0 := by
    intro h
    apply hd
    have hh := congrArg K.subtype h
    rw [RingHom.map_det, map_zero] at hh
    exact hh
  obtain ⟨C,hC⟩ := SymmetricForms.exists_congruence_identity S₀ hs₀ hd₀
  refine ⟨GeneralLinearGroup.map K.subtype C, ?_, ?_⟩
  · ext i j
    exact (C.val i j).property
  · have hh := congrArg (fun M : Matrix (Fin 5) (Fin 5) K => M.map K.subtype) hC
    change (C.val.map K.subtype).transpose * S * C.val.map K.subtype = J.form
    rw [hJ]
    rw [← RingHom.mapMatrix_apply] at hh
    change K.subtype.mapMatrix (C.val.transpose * S₀ * C.val) = K.subtype.mapMatrix 1 at hh
    rw [map_mul, map_mul, map_one] at hh
    simpa only [RingHom.mapMatrix_apply, Matrix.transpose_map, hm] using hh

/-- Correct a linear descent basis by a fixed-field congruence to make it unitary. -/
theorem unitary_coboundary_of_descent_basis (hJ : J.form = 1)
    (u : J.unitarySubgroup) (P : GL (Fin 5) F)
    (hP : u.val * GeneralLinearGroup.map J.conj.toRingHom P = P) :
    ∃ v : J.unitarySubgroup,
      u.val = v.val * (GeneralLinearGroup.map J.conj.toRingHom v.val)⁻¹ := by
  have hJfix : J.form.map J.conj = J.form := by simp [hJ]
  let S := J.conjTranspose P.val * J.form * P.val
  have hu := (J.mem_unitarySubgroup_iff u.val).mp u.property
  have hPm : u.val.val * P.val.map J.conj = P.val := congrArg Units.val hP
  have hmapAdj : (J.conjTranspose P.val).map J.conj =
      J.conjTranspose (P.val.map J.conj) := by rfl
  have hSfix : S.map J.conj = S := by
    calc
      S.map J.conj = J.conjTranspose (P.val.map J.conj) * J.form *
          (P.val.map J.conj) := by
        simp only [S, Matrix.map_mul, hmapAdj, hJfix]
      _ = J.conjTranspose (P.val.map J.conj) *
          (J.conjTranspose u.val.val * J.form * u.val.val) * (P.val.map J.conj) := by
        rw [hu]
      _ = S := by
        dsimp only [S]
        conv_rhs => rw [←hPm]
        rw [adjoint_mul]
        simp only [mul_assoc]
  have hSherm : J.conjTranspose S = S := by
    simp only [S, adjoint_mul, adjoint_adjoint, adjoint_form, mul_assoc]
  have hSsymm : S.transpose = S := by
    change (S.map J.conj).transpose = S at hSherm
    rwa [hSfix] at hSherm
  have hSdet : S.det ≠ 0 := by
    have had : (J.conjTranspose P.val).det = J.conj P.val.det := by
      change ((P.val.map J.conj).transpose).det = _
      rw [Matrix.det_transpose]
      exact (J.conj.map_det P.val).symm
    dsimp only [S]
    rw [Matrix.det_mul, Matrix.det_mul, had]
    exact mul_ne_zero (mul_ne_zero (by simpa using P.det_ne_zero) J.form_nondegenerate)
      P.det_ne_zero
  obtain ⟨C,hCfix,hC⟩ := fixed_symmetric_congruence J hJ S hSsymm hSfix hSdet
  have hCadj : J.conjTranspose C.val = C.val.transpose := by
    change (C.val.map J.conj).transpose = C.val.transpose
    rw [hCfix]
  have hPC : P * C ∈ J.unitarySubgroup := by
    rw [J.mem_unitarySubgroup_iff]
    change J.conjTranspose (P.val * C.val) * J.form * (P.val * C.val) = J.form
    rw [adjoint_mul, hCadj]
    simpa only [S, mul_assoc] using hC
  refine ⟨⟨P*C,hPC⟩, (eq_mul_inv_iff_mul_eq).mpr ?_⟩
  change u.val * GeneralLinearGroup.map J.conj.toRingHom (P*C) = P*C
  have hCeq : GeneralLinearGroup.map J.conj.toRingHom C = C := Units.ext hCfix
  rw [map_mul, hCeq, ←mul_assoc, hP]

/-- Every concrete five-dimensional unitary cocycle is a unitary coboundary. -/
theorem unitary_cocycle_coboundary (hJ : J.form = 1) (hσ : J.conj ≠ 1)
    (u : J.unitarySubgroup) (hu : u.val * GeneralLinearGroup.map J.conj.toRingHom u.val = 1) :
    ∃ v : J.unitarySubgroup,
      u.val = v.val * (GeneralLinearGroup.map J.conj.toRingHom v.val)⁻¹ := by
  obtain ⟨P,hP⟩ := exists_linear_descent_basis J hσ u.val hu
  exact unitary_coboundary_of_descent_basis J hJ u P hP

end Theory.SpecificGroups.UnitaryFive.Descent
