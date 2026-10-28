module
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddFourComparison.HermitianModel
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# The central kernel and the Hermitian projective quotient

An SL₂ congruence which is scalar on Hermitian matrices fixes each diagonal
line. Its off-diagonal matrix entries vanish. Comparing its action on the
second diagonal matrix and the off-diagonal matrix with entries one forces
the two diagonal entries to coincide. Thus it lies in the scalar center of
SL₂; conversely every central matrix acts trivially.

A nonfixed coefficient supplies the standard SL₂ perfectness witness, so the
image lies in the commutator of the full negative-determinant isometry group.
Once the reverse containment is supplied, the actual Omega scalar quotient
is identified with PSL₂ by the first isomorphism theorem. The final map
identity preserves the two literal quotient projections. The image-equality
premise remains an independent obligation; these conditional assembly results
do not assert the finite orthogonal comparison on their own.

Sources: GLS3 §2.7; Aschbacher–Smith A.2.17, printed pp.38–39, and I.1.6(3),
printed p.408 (`refs/quasithin.pdf`).
-/

public noncomputable section
namespace ClassicalOrthogonal.Minus.OddFourComparison.HermitianModel
open Representation.OrthogonalFourMinus
universe u
variable {E : Type u} [Field E] (σ : E ≃+* E) (hσ : Function.Involutive σ)

/-- An SL₂ congruence that is scalar on Hermitian matrices already comes from the center. -/
theorem mem_center_of_scalar_action (A : Matrix.SpecialLinearGroup (Fin 2) E)
    (c : (fixedField σ)ˣ)
    (hA : ∀ X : Space σ hσ, (orthogonalAction σ hσ A).val X = (c : fixedField σ) • X) :
    A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E) := by
  have h (v : (fixedField σ × fixedField σ) × E) (i j : Fin 2) :
      (A.val * !![v.1.1.val, v.2; σ v.2, v.1.2.val] * adjoint σ A.val) i j =
      c.val.val * (!![v.1.1.val, v.2; σ v.2, v.1.2.val] : Mat E) i j := by
    exact congrArg (fun X : Space σ hσ => X.val i j) (hA ((coordinates σ hσ).symm v))
  have hc : A.val 1 0 = 0 := by
    have he : norm σ hσ (A.val 1 0) = 0 := by
      apply Subtype.ext
      simpa [Matrix.mul_apply, Fin.sum_univ_two, adjoint] using h ((1, 0), 0) 1 1
    exact (norm_eq_zero_iff σ hσ _).mp he
  have hb : A.val 0 1 = 0 := by
    have he : norm σ hσ (A.val 0 1) = 0 := by
      apply Subtype.ext
      simpa [Matrix.mul_apply, Fin.sum_univ_two, adjoint] using h ((0, 1), 0) 0 0
    exact (norm_eq_zero_iff σ hσ _).mp he
  have hd : A.val 1 1 * σ (A.val 1 1) = c.val.val := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, adjoint] using h ((0, 1), 0) 1 1
  have had : A.val 0 0 * A.val 1 1 = 1 := by
    have he : A.val.det = 1 := A.property
    rwa [Matrix.det_fin_two, hb, hc, mul_zero, sub_zero] at he
  have had' : A.val 0 0 * σ (A.val 1 1) = c.val.val := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, adjoint, hb, hc] using h ((0, 0), 1) 0 1
  have hd0 : σ (A.val 1 1) ≠ 0 := by
    apply (map_ne_zero σ).mpr
    intro hz
    simp [hz] at had
  have he : A.val 0 0 = A.val 1 1 := mul_right_cancel₀ hd0 (had'.trans hd.symm)
  apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨A.val 0 0, ?_, ?_⟩
  · simpa only [Fintype.card_fin, pow_two, ← he] using had
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, hb, hc, he]

/-- The scalar center of SL₂ acts trivially, in every characteristic. -/
theorem center_action_eq_one (A : Matrix.SpecialLinearGroup (Fin 2) E)
    (hA : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E)) :
    orthogonalAction σ hσ A = 1 := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hr2 : r ^ 2 = 1 := by simpa only [Fintype.card_fin] using hr
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  apply Subtype.ext
  change A.val * X.val * adjoint σ A.val = X.val
  rw [← hrA]
  rcases sq_eq_one_iff.mp hr2 with hr | hr <;>
    rw [hr] <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar_apply, adjoint, Matrix.mul_apply, Fin.sum_univ_two]

/-- A congruence is scalar exactly when its SL₂ matrix is central. -/
theorem scalar_action_iff_mem_center (A : Matrix.SpecialLinearGroup (Fin 2) E) :
    (∃ c : (fixedField σ)ˣ, ∀ X : Space σ hσ,
      (orthogonalAction σ hσ A).val X = (c : fixedField σ) • X) ↔
      A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E) := by
  constructor
  · rintro ⟨c, hc⟩
    exact mem_center_of_scalar_action σ hσ A c hc
  · intro hA
    refine ⟨1, ?_⟩
    intro X
    rw [center_action_eq_one σ hσ A hA]
    simp

/-- The kernel of the actual Hermitian action is the whole scalar center of SL₂. -/
theorem orthogonalAction_ker :
    (orthogonalAction σ hσ).ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E) := by
  ext A
  constructor
  · intro hA
    apply mem_center_of_scalar_action σ hσ A 1
    intro X
    rw [MonoidHom.mem_ker.mp hA]
    simp
  · intro hA
    exact MonoidHom.mem_ker.mpr (center_action_eq_one σ hσ A hA)

/-- A nonfixed field element supplies the diagonal commutator witness for SL₂. -/
theorem sl2_commutator_eq_top (hne : ∃ t : E, σ t ≠ t) :
    commutator (Matrix.SpecialLinearGroup (Fin 2) E) = ⊤ := by
  obtain ⟨t, ht⟩ := hne
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (map_zero σ)
  have ht2 : t ^ 2 ≠ 1 := by
    intro hs
    rcases sq_eq_one_iff.mp hs with h | h
    · exact ht (by rw [h, map_one])
    · exact ht (by rw [h, map_neg, map_one])
  exact Matrix.SL2.commutator_eq_top ht0 ht2

/-- Perfectness puts the actual Hermitian image inside the full orthogonal commutator. -/
theorem range_orthogonalAction_le_commutator (hne : ∃ t : E, σ t ≠ t) :
    (orthogonalAction σ hσ).range ≤
      commutator (Orthogonal (fixedField σ) (Space σ hσ) (minusForm σ hσ)) := by
  have h := map_commutator_eq _ (orthogonalAction σ hσ)
  rw [sl2_commutator_eq_top σ hne, ← MonoidHom.range_eq_map] at h
  rw [h, commutator_def]
  exact Subgroup.commutator_mono le_top le_top

/-- Restrict the actual congruences to Omega once their full image is identified. -/
def omegaActionOfRange
    (himage : (orthogonalAction σ hσ).range =
      commutator (Orthogonal (fixedField σ) (Space σ hσ) (minusForm σ hσ))) :
    Matrix.SpecialLinearGroup (Fin 2) E →*
      Omega (fixedField σ) (Space σ hσ) (minusForm σ hσ) where
  toFun A := ⟨orthogonalAction σ hσ A, by
    change orthogonalAction σ hσ A ∈ commutator _
    rw [← himage]
    exact ⟨A, rfl⟩⟩
  map_one' := Subtype.ext (map_one (orthogonalAction σ hσ))
  map_mul' A B := Subtype.ext (map_mul (orthogonalAction σ hσ) A B)

/-- Surjectivity refers to the commutator of the full isometry group. -/
theorem omegaActionOfRange_surjective
    (himage : (orthogonalAction σ hσ).range =
      commutator (Orthogonal (fixedField σ) (Space σ hσ) (minusForm σ hσ))) :
    Function.Surjective (omegaActionOfRange σ hσ himage) := by
  intro g
  have hg : g.val ∈ (orthogonalAction σ hσ).range := by
    rw [himage]
    exact g.property
  obtain ⟨A, hA⟩ := hg
  exact ⟨A, Subtype.ext hA⟩

/-- The action followed by the literal Omega scalar quotient. -/
def projectiveActionOfRange
    (himage : (orthogonalAction σ hσ).range =
      commutator (Orthogonal (fixedField σ) (Space σ hσ) (minusForm σ hσ))) :
    Matrix.SpecialLinearGroup (Fin 2) E →*
      ProjectiveOmega (fixedField σ) (Space σ hσ) (minusForm σ hσ) :=
  (QuotientGroup.mk' (scalarSubgroup (fixedField σ) (Space σ hσ) (minusForm σ hσ))).comp
    (omegaActionOfRange σ hσ himage)

/-- The projective action uses the literal scalar-quotient projection. -/
@[simp] theorem projectiveActionOfRange_apply
    (himage : (orthogonalAction σ hσ).range =
      commutator (Orthogonal (fixedField σ) (Space σ hσ) (minusForm σ hσ)))
    (A : Matrix.SpecialLinearGroup (Fin 2) E) :
    projectiveActionOfRange σ hσ himage A =
      QuotientGroup.mk' (scalarSubgroup (fixedField σ) (Space σ hσ) (minusForm σ hσ))
        (omegaActionOfRange σ hσ himage A) := by
  rfl

/-- Projectivizing the actual Omega action kills precisely the SL₂ center. -/
theorem projectiveActionOfRange_ker
    (himage : (orthogonalAction σ hσ).range =
      commutator (Orthogonal (fixedField σ) (Space σ hσ) (minusForm σ hσ))) :
    (projectiveActionOfRange σ hσ himage).ker =
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E) := by
  ext A
  rw [MonoidHom.mem_ker]
  exact (QuotientGroup.eq_one_iff (omegaActionOfRange σ hσ himage A)).trans
    (scalar_action_iff_mem_center σ hσ A)

/-- The scalar quotient of the Hermitian commutator is PSL₂ once image equality is proved.
The independent image theorem must discharge `himage` before using this as a model comparison. -/
def projectiveEquivPSLOfRange
    (himage : (orthogonalAction σ hσ).range =
      commutator (Orthogonal (fixedField σ) (Space σ hσ) (minusForm σ hσ))) :
    ProjectiveOmega (fixedField σ) (Space σ hσ) (minusForm σ hσ) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) E := by
  let f := projectiveActionOfRange σ hσ himage
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective _).comp (omegaActionOfRange_surjective σ hσ himage)
  exact ((QuotientGroup.quotientMulEquivOfEq
    (projectiveActionOfRange_ker σ hσ himage).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)).symm

/-- The comparison carries the literal Omega projection to the standard PSL projection. -/
@[simp] theorem projectiveEquivPSLOfRange_apply
    (himage : (orthogonalAction σ hσ).range =
      commutator (Orthogonal (fixedField σ) (Space σ hσ) (minusForm σ hσ)))
    (A : Matrix.SpecialLinearGroup (Fin 2) E) :
    projectiveEquivPSLOfRange σ hσ himage (projectiveActionOfRange σ hσ himage A) =
      QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E)) A := by
  apply (projectiveEquivPSLOfRange σ hσ himage).symm.injective
  rw [MulEquiv.symm_apply_apply]
  rfl

end ClassicalOrthogonal.Minus.OddFourComparison.HermitianModel
