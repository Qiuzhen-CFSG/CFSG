module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.ProjectiveAction
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.FixedRadical

/-!
# Normalizing a symplectic semilinear lift

A linear equivalence preserving the zeroes of the actual symplectic form is a
similitude. To prove this, use the form to identify the vector space with its
dual: the endomorphism comparing the two forms preserves every one-dimensional
subspace, so it is scalar. Its multiplier is nonzero by nondegeneracy.

In a finite field of characteristic two every scalar has a square root.
Rescaling the linear equivalence by a square root of the inverse multiplier
therefore gives an actual symplectic matrix with the same projective action.
The final lemma applies this normalization to a specified semilinear lift of
a polar permutation. Existence of that lift is an explicit remaining premise.

Source: the geometric proof of the automorphism fact used in
Aschbacher--Smith F.1.12, printed pp.263--264 of `refs/quasithin.pdf`.
The matrix-membership calculation follows `SemilinearClassification.BinaryPolar`.
-/

public noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
open Projectivization Matrix
variable {F : Type*} [Field F]

/-- A linear equivalence preserving the zeroes of the symplectic form is a
similitude, with a single nonzero multiplier for all pairs of vectors. -/
theorem linear_polar_is_similitude (A : Vector F ≃ₗ[F] Vector F)
    (hA : ∀ v w, form F (A v) (A w) = 0 ↔ form F v w = 0) :
    ∃ c : F, c ≠ 0 ∧ ∀ v w, form F (A v) (A w) = c * form F v w := by
  let B := (form F).comp A.toLinearMap A.toLinearMap
  let T : Module.End F (Vector F) :=
    ((form F).toDual TwoLocalCover.form_nondegenerate).symm.toLinearMap.comp B
  have hT (v w : Vector F) : form F (T v) w = form F (A v) (A w) :=
    LinearMap.BilinForm.apply_toDual_symm_apply
      (hB := TwoLocalCover.form_nondegenerate) (B v) w
  have hspan (v : Vector F) : T v ∈ F ∙ v := by
    rw [← LinearMap.BilinForm.orthogonal_orthogonal
      TwoLocalCover.form_nondegenerate TwoLocalCover.form_alternating.isRefl (F ∙ v)]
    intro w hw
    apply TwoLocalCover.form_alternating.eq_iff.mp
    rw [hT]
    exact (hA v w).mpr (hw v (Submodule.mem_span_singleton_self v))
  obtain ⟨c, hc⟩ := T.exists_eq_smul_id_of_forall_notLinearIndependent (fun v => by
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hspan v)
    by_cases hv : v = 0
    · simp [hv, linearIndependent_fin2]
    · rw [LinearIndependent.pair_iff' hv]
      exact fun h => h a ha)
  have hmul (v w : Vector F) : form F (A v) (A w) = c * form F v w := by
    rw [← hT, hc]
    simp
  refine ⟨c, ?_, hmul⟩
  intro hc0
  have h := hmul (A.symm (e 0)) (A.symm (Pi.single (.inr 0) 1))
  simp [hc0, form_apply, e, Pi.single_apply] at h

/-- In a finite field of characteristic two, a symplectic similitude induces
the same projective action as an actual symplectic matrix. -/
theorem linear_polar_projective_eq_symplectic [Finite F] [CharP F 2]
    (A : Vector F ≃ₗ[F] Vector F)
    (hA : ∀ v w, form F (A v) (A w) = 0 ↔ form F v w = 0) :
    ∃ g : Sp F, ∀ p : ProjectivePoint F,
      projectiveAction g p = Projectivization.map A.toLinearMap A.injective p := by
  obtain ⟨c, hc, hmul⟩ := linear_polar_is_similitude A hA
  obtain ⟨a, ha⟩ := Finite.surjective_of_injective (CharTwo.sq_injective (R := F)) c⁻¹
  change a ^ 2 = c⁻¹ at ha
  have hnorm : a * a * c = 1 := by
    rw [← pow_two, ha, inv_mul_cancel₀ hc]
  let L : Module.End F (Vector F) := a • A.toLinearMap
  have hL (v w : Vector F) : form F (L v) (L w) = form F v w := by
    change form F (a • A v) (a • A w) = _
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hmul]
    calc
      a * (a * (c * form F v w)) = (a * a * c) * form F v w := by ring
      _ = form F v w := by rw [hnorm, one_mul]
  let g : Sp F := ⟨LinearMap.toMatrix' L, by
    apply SymplecticGroup.mem_iff'.mpr
    have he := Matrix.toBilin'_comp (-Matrix.J (Fin 2) F)
      (LinearMap.toMatrix' L) (LinearMap.toMatrix' L)
    have hpres : (form F).comp L L = form F := by
      apply LinearMap.ext
      intro v
      apply LinearMap.ext
      intro w
      exact hL v w
    simp only [Matrix.toLin'_toMatrix'] at he
    have hm := Matrix.toBilin'.injective (he.symm.trans hpres)
    simpa [Matrix.mul_neg, Matrix.neg_mul, form] using hm⟩
  have hg (v : Vector F) : g • v = a • A v :=
    LinearMap.toMatrix'_mulVec L v
  refine ⟨g, ?_⟩
  intro p
  induction p using Projectivization.ind with
  | h v hv =>
    simp only [projectiveAction_apply, smul_mk, Projectivization.map_mk]
    exact (mk_eq_mk_iff' F _ _ _ _).mpr ⟨a, (hg v).symm⟩

/-- Given a genuine semilinear lift of a polar permutation, the multiplier
normalization produces the requested inner-field permutation. Constructing
that lift from line preservation remains a separate geometric obligation. -/
theorem polar_permutation_eq_innerFieldProjective_of_lift [Finite F] [CharP F 2]
    (φ : Equiv.Perm (ProjectivePoint F))
    (hφ : ∀ p q, Orthogonal (φ p) (φ q) ↔ Orthogonal p q)
    (σ : F ≃+* F) (A : Vector F ≃ₗ[F] Vector F)
    (hlift : ∀ p, φ p =
      Projectivization.map A.toLinearMap A.injective (fieldProjective σ p)) :
    ∃ g : Sp F, φ = innerFieldProjective g σ := by
  have hproj (p q : ProjectivePoint F) :
      Orthogonal (Projectivization.map A.toLinearMap A.injective p)
        (Projectivization.map A.toLinearMap A.injective q) ↔ Orthogonal p q := by
    have h₁ := hφ ((fieldProjective σ).symm p) ((fieldProjective σ).symm q)
    have h₂ := orthogonal_fieldProjective_iff σ
      ((fieldProjective σ).symm p) ((fieldProjective σ).symm q)
    simpa only [hlift, Equiv.apply_symm_apply] using h₁.trans h₂.symm
  have hA (v w : Vector F) : form F (A v) (A w) = 0 ↔ form F v w = 0 := by
    by_cases hv : v = 0
    · simp [hv]
    by_cases hw : w = 0
    · simp [hw]
    simpa only [Projectivization.map_mk, orthogonal_mk_iff, LinearEquiv.coe_coe] using
      hproj (mk F v hv) (mk F w hw)
  obtain ⟨g, hg⟩ := linear_polar_projective_eq_symplectic A hA
  refine ⟨g, ?_⟩
  apply Equiv.ext
  intro p
  rw [hlift, ← hg]
  rfl
end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
