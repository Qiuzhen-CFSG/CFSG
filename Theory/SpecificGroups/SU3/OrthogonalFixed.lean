module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.GraphComparison
import all Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.GraphComparison

/-!
# The orthogonal fixed group of entrywise projective SU₃ conjugation

The existing fixed-point embedding restricts matrix entries to the actual
fixed subfield. Its inverse maps those entries back to the original field;
the orthogonal equation becomes the Hermitian equation and determinant one
is preserved. Together with the unique fixed lift through the scalar kernel,
this gives an actual equivalence with the ternary special orthogonal group.

The internal import is an intentional continuation of the fixed-point map's
proof, allowing its defining equation to be used without changing its public
boundary. Source: GLS3, §§2.7 and 4.3; the involution inspection in
Aschbacher–Smith E.6.18, printed p.252. No characteristic restriction is needed.
-/

public section
open Matrix
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow
variable {E : Type*} [Field E] (J : HermitianForm 3 E)
variable (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
variable {γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
variable (hγ : J.IsEntrywiseConjugation γ)

/-- Every fixed-field orthogonal matrix comes from a fixed special-unitary matrix. -/
theorem specialFixedToOrthogonal_surjective : Function.Surjective (specialFixedToOrthogonal J hJ hγ) := by
  intro x
  let K := FixedBy.subfield E J.conj
  let A : GL (Fin 3) E := GeneralLinearGroup.map K.subtype x.val
  have hAfix : A.val.map J.conj = A.val := by
    ext i j
    exact (x.val.val i j).property
  have hA : A ∈ J.specialSubgroup := by
    rw [J.mem_specialSubgroup_iff]
    constructor
    · have hx := ((splitOrthogonalForm K).mem_specialSubgroup_iff _).mp x.property |>.1
      have hm := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M.map K.subtype) hx
      have hf : (splitOrthogonalForm K).form.map K.subtype = J.form := by
        rw [hJ]
        ext i j
        fin_cases i <;> fin_cases j <;> rfl
      have ht : (splitOrthogonalForm K).conjTranspose x.val.val = x.val.val.transpose := rfl
      rw [ht, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hf] at hm
      change (A.val.map J.conj).transpose * J.form * A.val = J.form
      rw [hAfix]
      exact hm
    · apply Units.ext
      change A.val.det = 1
      have hx := congrArg Units.val x.property.2
      change x.val.val.det = 1 at hx
      have hm := congrArg K.subtype hx
      rw [RingHom.map_det, map_one] at hm
      exact hm
  let y : J.specialSubgroup := ⟨A, hA⟩
  have hy : y ∈ (specialEntrywiseAut J hγ).fixedSubgroup := by
    rw [MulAut.mem_fixedSubgroup]
    apply Subtype.ext
    apply Units.ext
    exact hAfix
  refine ⟨⟨y, hy⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  ext i j
  rfl

/-- The actual entrywise fixed group is the special orthogonal group over the
stored involution's fixed field, with its antidiagonal Gram matrix. -/
noncomputable def projectiveFixedEquivOrthogonal :
    γ.fixedSubgroup ≃*
      (splitOrthogonalForm (FixedBy.subfield E J.conj)).specialSubgroup :=
  (projectiveFixedEquivSpecial J hγ).trans
    (MulEquiv.ofBijective (specialFixedToOrthogonal J hJ hγ)
      ⟨specialFixedToOrthogonal_injective J hJ hγ,
        specialFixedToOrthogonal_surjective J hJ hγ⟩)

end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow
