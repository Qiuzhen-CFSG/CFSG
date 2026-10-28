module

public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.Descent.SymmetricForms.BinaryTernary
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.Descent.GramNormalization
public import Mathlib.Algebra.Ring.Action.End
public import Mathlib.Algebra.CharP.Algebra
import Mathlib.Tactic.FinCases

/-!
# Congruence of conjugation-fixed symmetric ternary forms

A matrix fixed entrywise by the Hermitian involution is a matrix over its
actual fixed subfield. That subfield is finite of characteristic two, so the
symmetric ternary normal form in `BinaryTernary` applies there. Mapping the
change of basis back to the original field preserves invertibility and makes
every coefficient fixed by the given involution.

The final theorem applies this congruence to the literal Gram matrix arising
from a linear semilinear-descent basis. It discharges the symmetric-form
premise of `unitary_coboundary_of_gram_normalization`; the linear descent basis
remains explicit. No restriction on field size or nontriviality of the
involution is required.

Source: GLS, Volume 3, §2.7 and Proposition 4.9.2(b2,g); GLS, Volume 4,
Chapter 4, Lemma 3.4(a,c).
-/

open Matrix
namespace BenderSuzuki.MatrixGroups.HermitianForm
variable {E : Type*} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 3 E)

/-- A nondegenerate symmetric ternary matrix fixed by conjugation is congruent
to the prescribed Hermitian matrix by a matrix with conjugation-fixed entries.
This supplies the literal `hsymmetric` premise of projective descent. -/
public theorem fixed_symmetric_ternary_congruence
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (S : Matrix (Fin 3) (Fin 3) E)
    (hs : S.transpose = S) (hfix : S.map J.conj = S) (hd : S.det ≠ 0) :
    ∃ C : GL (Fin 3) E, C.val.map J.conj = C.val ∧
      C.val.transpose * S * C.val = J.form := by
  let K := FixedBy.subfield E J.conj
  let S₀ : Matrix (Fin 3) (Fin 3) K := fun i j =>
    ⟨S i j, congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M i j) hfix⟩
  have hm : S₀.map K.subtype = S := rfl
  have hs₀ : S₀.transpose = S₀ := by
    ext i j
    exact congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M i j) hs
  have hd₀ : S₀.det ≠ 0 := by
    intro h
    apply hd
    have hh := congrArg K.subtype h
    rw [RingHom.map_det, map_zero] at hh
    exact hh
  obtain ⟨C, hC⟩ := Matrix.SymmetricTernary.exists_congruence_antidiagonal S₀ hs₀ hd₀
  refine ⟨GeneralLinearGroup.map K.subtype C, ?_, ?_⟩
  · ext i j
    exact (C.val i j).property
  · have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M.map K.subtype) hC
    change (C.val.map K.subtype).transpose * S * C.val.map K.subtype = J.form
    rw [hJ]
    have ht : (!![0,0,1;0,1,0;1,0,0] : Matrix (Fin 3) (Fin 3) K).map
        K.subtype = !![0,0,1;0,1,0;1,0,0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    simpa only [Matrix.map_mul, Matrix.transpose_map, hm, ht] using hh

/-- The fixed-field congruence normalizes a linear descent basis to a unitary
one. The only remaining witness is the displayed linear descent basis `P`. -/
public theorem unitary_coboundary_of_descent_basis
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (u : J.unitarySubgroup) (P : GL (Fin 3) E)
    (hP : u.val * GeneralLinearGroup.map J.conj.toRingHom P = P) :
    ∃ v : J.unitarySubgroup,
      u.val = v.val * (GeneralLinearGroup.map J.conj.toRingHom v.val)⁻¹ := by
  have hJfix : J.form.map J.conj = J.form := by
    rw [hJ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  exact J.unitary_coboundary_of_gram_normalization hJfix u P hP
    (J.fixed_symmetric_ternary_congruence hJ)

end BenderSuzuki.MatrixGroups.HermitianForm
