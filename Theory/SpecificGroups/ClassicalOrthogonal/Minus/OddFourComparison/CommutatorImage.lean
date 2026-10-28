module
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddFourComparison.Projective
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddFourComparison.CommutatorImage.Frames
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddFourComparison.CommutatorImage.NormPlane
import Mathlib.Tactic.Group

/-!
# The Hermitian image is the full orthogonal commutator

SL₂ is transitive on normalized singular pairs. Their pointwise stabilizer
consists of norm-plane rotations and their products with conjugation. This
gives coverage of the full negative-determinant isometry group. Rotations
and conjugation normalize the SL₂ image. Modulo that image, rotations
commute, have square one, and commute with conjugation because conjugation
inverts them. The quotient is therefore abelian.

Perfectness of SL₂ gives the reverse containment already proved in
`Projective`. The resulting image equality discharges the premise of
`projectiveEquivPSLOfRange`, producing the actual projective Omega/PSL₂
comparison with its literal quotient-map identity. The proof works in both
characteristics, so in particular applies under the odd-cardinality
hypothesis supplied by the quadratic-transport construction.

Sources: GLS3 §2.7; Aschbacher–Smith A.2.17, printed pp.38–39
(`refs/quasithin.pdf`). This module supplies the full-isometry commutator
comparison; transport of the original chosen minus form belongs to the
parent `OddFourComparison` assembly.
-/

public noncomputable section
namespace ClassicalOrthogonal.Minus.OddFourComparison.HermitianModel

section Quotient
variable {S G U : Type*} [Group S] [Group G]

private theorem normal_of_rotations (f : S →* G) (r : U → G) (c : G)
    (t : U → S → S) (s : S → S)
    (hr : ∀ u a, r u * f a = f (t u a) * r u)
    (hc : ∀ a, c * f a = f (s a) * c)
    (hcover : ∀ g, ∃ a u, g = f a * r u ∨ g = f a * r u * c) : f.range.Normal where
  conj_mem := by
    rintro _ ⟨a, rfl⟩ g
    have hrc (u : U) (a : S) : r u * f a * (r u)⁻¹ = f (t u a) := by
      rw [hr, mul_assoc, mul_inv_cancel, mul_one]
    have hcc (a : S) : c * f a * c⁻¹ = f (s a) := by
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    obtain ⟨b, u, rfl | rfl⟩ := hcover g
    · refine ⟨b * t u a * b⁻¹, ?_⟩
      simp only [map_mul, map_inv]
      rw [← hrc]
      group
    · refine ⟨b * t u (s a) * b⁻¹, ?_⟩
      simp only [map_mul, map_inv]
      rw [← hrc, ← hcc]
      group

/-- A commuting family of rotations and an inverting element give an abelian quotient
when the squares of the rotations lie in the normalized image. -/
private theorem commutator_le_of_rotations (f : S →* G) (r : U → G) (c : G)
    (t : U → S → S) (s : S → S)
    (hr : ∀ u a, r u * f a = f (t u a) * r u)
    (hc : ∀ a, c * f a = f (s a) * c)
    (hrr : ∀ u v, Commute (r u) (r v))
    (hcr : ∀ u, c * r u = (r u)⁻¹ * c)
    (hsq : ∀ u, r u * r u ∈ f.range)
    (hcover : ∀ g, ∃ a u, g = f a * r u ∨ g = f a * r u * c) :
    commutator G ≤ f.range := by
  let : f.range.Normal := normal_of_rotations f r c t s hr hc hcover
  let q := QuotientGroup.mk' f.range
  have hqf (a : S) : q (f a) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩
  have hqr (g : G) : ∃ u, q g = q (r u) ∨ q g = q (r u) * q c := by
    obtain ⟨a, u, rfl | rfl⟩ := hcover g
    · exact ⟨u, Or.inl (by rw [map_mul, hqf, one_mul])⟩
    · exact ⟨u, Or.inr (by rw [map_mul, map_mul, hqf, one_mul])⟩
  have hqc (u : U) : Commute (q (r u)) (q c) := by
    have hsq' : q (r u) * q (r u) = 1 := by
      rw [← map_mul]
      exact (QuotientGroup.eq_one_iff _).mpr (hsq u)
    have hi : (q (r u))⁻¹ = q (r u) := (eq_inv_of_mul_eq_one_left hsq').symm
    have h := congrArg q (hcr u)
    change q (r u) * q c = q c * q (r u)
    simpa only [map_mul, map_inv, hi] using h.symm
  have hqrr (u v : U) : Commute (q (r u)) (q (r v)) := (hrr u v).map q
  apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
  refine ⟨⟨?_⟩⟩
  intro x y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective f.range x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective f.range y
  change q g * q h = q h * q g
  obtain ⟨u, hu | hu⟩ := hqr g <;> obtain ⟨v, hv | hv⟩ := hqr h
  · rw [hu, hv]
    exact hqrr u v
  · rw [hu, hv]
    exact (hqrr u v).mul_right (hqc u)
  · rw [hu, hv]
    exact (hqrr u v).mul_left (hqc v).symm
  · rw [hu, hv]
    exact ((hqrr u v).mul_right (hqc u)).mul_left
      ((hqc v).symm.mul_right (Commute.refl _))

end Quotient

universe u
variable {E : Type u} [Field E] (σ : E ≃+* E) (hσ : Function.Involutive σ)
variable [Finite E] (hdegree : Module.finrank (fixedField σ) E = 2)
    (hne : ∃ t : E, σ t ≠ t)
include hdegree hne

/-- Full isometries are congruences followed by a norm-plane rotation,
possibly followed by conjugation. -/
theorem orthogonal_normal_form
    (g : Orthogonal (fixedField σ) (Space σ hσ) (minusForm σ hσ)) :
    ∃ (A : Matrix.SpecialLinearGroup (Fin 2) E) (u : E) (hu : norm σ hσ u = 1),
      g = orthogonalAction σ hσ A * normRotation σ hσ u hu ∨
      g = orthogonalAction σ hσ A * normRotation σ hσ u hu * conjugationOrthogonal σ hσ := by
  obtain ⟨A, hA0, hA1⟩ := orthogonal_diagonal_pair_transitivity σ hσ hdegree hne g
  have h0 : ((orthogonalAction σ hσ A)⁻¹ * g).val (firstDiagonal σ hσ) =
      firstDiagonal σ hσ := by
    change (orthogonalAction σ hσ A).val.symm (g.val (firstDiagonal σ hσ)) = _
    rw [← hA0, LinearEquiv.symm_apply_apply]
  have h1 : ((orthogonalAction σ hσ A)⁻¹ * g).val (secondDiagonal σ hσ) =
      secondDiagonal σ hσ := by
    change (orthogonalAction σ hσ A).val.symm (g.val (secondDiagonal σ hσ)) = _
    rw [← hA1, LinearEquiv.symm_apply_apply]
  obtain ⟨u, hu, h | h⟩ := diagonal_stabilizer_normal_form σ hσ
    ((orthogonalAction σ hσ A)⁻¹ * g) h0 h1
  · exact ⟨A, u, hu, Or.inl (inv_mul_eq_iff_eq_mul.mp h)⟩
  · exact ⟨A, u, hu, Or.inr ((inv_mul_eq_iff_eq_mul.mp h).trans (mul_assoc _ _ _).symm)⟩

/-- The literal SL₂ congruence image is normal in the full orthogonal group. -/
theorem range_orthogonalAction_normal : (orthogonalAction σ hσ).range.Normal := by
  let U := {u : E // norm σ hσ u = 1}
  apply normal_of_rotations (orthogonalAction σ hσ)
    (fun u : U => normRotation σ hσ u.val u.property) (conjugationOrthogonal σ hσ)
    (fun u : U => rotationTwist σ hσ u.val u.property)
    (Matrix.SpecialLinearGroup.map σ.toRingHom)
  · intro u A
    exact normRotation_mul_action σ hσ u.val u.property A
  · exact conjugationOrthogonal_mul_action σ hσ
  · intro g
    obtain ⟨A, u, hu, h⟩ := orthogonal_normal_form σ hσ hdegree hne g
    exact ⟨A, ⟨u, hu⟩, h⟩

/-- The commutator of the full orthogonal group consists of SL₂ congruences. -/
theorem commutator_le_range_orthogonalAction :
    commutator (Orthogonal (fixedField σ) (Space σ hσ) (minusForm σ hσ)) ≤
      (orthogonalAction σ hσ).range := by
  let U := {u : E // norm σ hσ u = 1}
  apply commutator_le_of_rotations (orthogonalAction σ hσ)
    (fun u : U => normRotation σ hσ u.val u.property) (conjugationOrthogonal σ hσ)
    (fun u : U => rotationTwist σ hσ u.val u.property)
    (Matrix.SpecialLinearGroup.map σ.toRingHom)
  · intro u A
    exact normRotation_mul_action σ hσ u.val u.property A
  · exact conjugationOrthogonal_mul_action σ hσ
  · intro u v
    exact normRotation_commute σ hσ u.val v.val u.property v.property
  · intro u
    exact conjugation_normRotation σ hσ u.val u.property
  · intro u
    exact normRotation_sq_mem_range σ hσ u.val u.property
  · intro g
    obtain ⟨A, u, hu, h⟩ := orthogonal_normal_form σ hσ hdegree hne g
    exact ⟨A, ⟨u, hu⟩, h⟩

/-- The Hermitian image is Omega with the full-isometry commutator convention. -/
theorem range_orthogonalAction_eq_commutator :
    (orthogonalAction σ hσ).range =
      commutator (Orthogonal (fixedField σ) (Space σ hσ) (minusForm σ hσ)) :=
  le_antisymm (range_orthogonalAction_le_commutator σ hσ hne)
    (commutator_le_range_orthogonalAction σ hσ hdegree hne)

/-- The actual Hermitian projective Omega group is PSL₂ over the quadratic extension. -/
def projectiveEquivPSL :
    ProjectiveOmega (fixedField σ) (Space σ hσ) (minusForm σ hσ) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) E :=
  projectiveEquivPSLOfRange σ hσ (range_orthogonalAction_eq_commutator σ hσ hdegree hne)

/-- The comparison preserves the original Omega and PSL quotient projections. -/
@[simp] theorem projectiveEquivPSL_apply (A : Matrix.SpecialLinearGroup (Fin 2) E) :
    projectiveEquivPSL σ hσ hdegree hne
      (projectiveActionOfRange σ hσ (range_orthogonalAction_eq_commutator σ hσ hdegree hne) A) =
        QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E)) A :=
  projectiveEquivPSLOfRange_apply σ hσ _ A

end ClassicalOrthogonal.Minus.OddFourComparison.HermitianModel
