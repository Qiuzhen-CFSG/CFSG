module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.ProjectiveAction

/-!
# Binary polar permutations are symplectic

Over a two-element field, a projective point has a unique nonzero vector.
An orthogonality-preserving permutation therefore lifts to a permutation of
vectors preserving the actual alternating form: its values are zero or one.
Nondegeneracy forces this lift to be additive, hence linear, and its matrix
lies in the actual symplectic group.

This proves the binary geometric step in the automorphism fact used in
Aschbacher--Smith F.1.12, printed pp.263--264 of `refs/quasithin.pdf`.
Recovering such a polar permutation from a diagram-preserving group
automorphism is a separate assertion.
-/

public section

noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
open Projectivization Matrix
variable {F : Type*} [Field F]

private theorem binary_scalar (hF : Nat.card F = 2) (a : F) : a = 0 ∨ a = 1 := by
  obtain ⟨y, _, hu⟩ := (Nat.card_eq_two_iff' (0 : F)).mp hF
  by_cases ha : a = 0
  · exact Or.inl ha
  · exact Or.inr ((hu a ha).trans (hu 1 one_ne_zero).symm)

private theorem binary_scalar_eq (hF : Nat.card F = 2) {a b : F}
    (h : a = 0 ↔ b = 0) : a = b := by
  rcases binary_scalar hF a with rfl | rfl
  · exact (h.mp rfl).symm
  · rcases binary_scalar hF b with rfl | rfl
    · exact False.elim (one_ne_zero (h.mpr rfl))
    · rfl

private theorem binary_rep_mk (hF : Nat.card F = 2) (v : Vector F) (hv : v ≠ 0) :
    (mk F v hv).rep = v := by
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep F v hv
  have ha1 : (a : F) = 1 := (binary_scalar hF a).resolve_left a.ne_zero
  simpa [Units.smul_def, ha1] using ha.symm

private def binaryLift (φ : Equiv.Perm (ProjectivePoint F)) (v : Vector F) : Vector F := by
  classical
  exact if hv : v = 0 then 0 else (φ (mk F v hv)).rep

private theorem binaryLift_zero (φ : Equiv.Perm (ProjectivePoint F)) : binaryLift φ 0 = 0 := by
  simp [binaryLift]

private theorem binaryLift_nonzero (φ : Equiv.Perm (ProjectivePoint F))
    (v : Vector F) (hv : v ≠ 0) : binaryLift φ v = (φ (mk F v hv)).rep := by
  simp [binaryLift, hv]

private theorem binaryLift_surjective (hF : Nat.card F = 2)
    (φ : Equiv.Perm (ProjectivePoint F)) : Function.Surjective (binaryLift φ) := by
  intro v
  by_cases hv : v = 0
  · exact ⟨0, hv ▸ binaryLift_zero φ⟩
  · refine ⟨(φ.symm (mk F v hv)).rep, ?_⟩
    rw [binaryLift_nonzero φ _ (rep_nonzero _), mk_rep, φ.apply_symm_apply,
      binary_rep_mk hF]

private theorem binaryLift_form (hF : Nat.card F = 2)
    (φ : Equiv.Perm (ProjectivePoint F))
    (hφ : ∀ p q, Orthogonal (φ p) (φ q) ↔ Orthogonal p q) (v w : Vector F) :
    form F (binaryLift φ v) (binaryLift φ w) = form F v w := by
  by_cases hv : v = 0
  · subst v
    simp [binaryLift_zero]
  by_cases hw : w = 0
  · subst w
    simp [binaryLift_zero]
  rw [binaryLift_nonzero φ v hv, binaryLift_nonzero φ w hw]
  apply binary_scalar_eq hF
  have he (p q : ProjectivePoint F) :
      Orthogonal p q ↔ form F p.rep q.rep = 0 := by
    simpa only [mk_rep] using orthogonal_mk_iff p.rep q.rep p.rep_nonzero q.rep_nonzero
  simpa only [he, binary_rep_mk hF] using hφ (mk F v hv) (mk F w hw)

private theorem form_ext_left {v w : Vector F}
    (h : ∀ z, form F v z = form F w z) : v = w := by
  ext i
  cases i with
  | inl i => simpa [form_apply, Pi.single_apply] using h (Pi.single (.inr i) 1)
  | inr i => simpa using h (e i)

private theorem binaryLift_add (hF : Nat.card F = 2)
    (φ : Equiv.Perm (ProjectivePoint F))
    (hφ : ∀ p q, Orthogonal (φ p) (φ q) ↔ Orthogonal p q) (v w : Vector F) :
    binaryLift φ (v + w) = binaryLift φ v + binaryLift φ w := by
  apply form_ext_left
  intro z
  obtain ⟨u, rfl⟩ := binaryLift_surjective hF φ z
  simp only [map_add, LinearMap.add_apply, binaryLift_form hF φ hφ]

private def binaryLinear (hF : Nat.card F = 2)
    (φ : Equiv.Perm (ProjectivePoint F))
    (hφ : ∀ p q, Orthogonal (φ p) (φ q) ↔ Orthogonal p q) :
    Module.End F (Vector F) where
  toFun := binaryLift φ
  map_add' := binaryLift_add hF φ hφ
  map_smul' a v := by
    rcases binary_scalar hF a with rfl | rfl
    · simp [binaryLift_zero]
    · simp

private def binaryMatrix (hF : Nat.card F = 2)
    (φ : Equiv.Perm (ProjectivePoint F))
    (hφ : ∀ p q, Orthogonal (φ p) (φ q) ↔ Orthogonal p q) : Sp F :=
  ⟨LinearMap.toMatrix' (binaryLinear hF φ hφ), by
    apply SymplecticGroup.mem_iff'.mpr
    have he := Matrix.toBilin'_comp (-Matrix.J (Fin 2) F)
      (LinearMap.toMatrix' (binaryLinear hF φ hφ))
      (LinearMap.toMatrix' (binaryLinear hF φ hφ))
    have hpres : (form F).comp (binaryLinear hF φ hφ) (binaryLinear hF φ hφ) = form F := by
      apply LinearMap.ext
      intro v
      apply LinearMap.ext
      intro w
      exact binaryLift_form hF φ hφ v w
    simp only [Matrix.toLin'_toMatrix'] at he
    have hm := Matrix.toBilin'.injective (he.symm.trans hpres)
    simpa [Matrix.mul_neg, Matrix.neg_mul, form] using hm⟩

private theorem binaryMatrix_apply (hF : Nat.card F = 2)
    (φ : Equiv.Perm (ProjectivePoint F))
    (hφ : ∀ p q, Orthogonal (φ p) (φ q) ↔ Orthogonal p q) (v : Vector F) :
    binaryMatrix hF φ hφ • v = binaryLift φ v := by
  change (LinearMap.toMatrix' (binaryLinear hF φ hφ)) *ᵥ v = _
  exact LinearMap.toMatrix'_mulVec _ _

/-- Over a two-element field, every orthogonality-preserving permutation of
projective points is induced by an actual symplectic matrix. -/
theorem polar_permutation_eq_projectiveAction_of_card_two (hF : Nat.card F = 2)
    (φ : Equiv.Perm (ProjectivePoint F))
    (hφ : ∀ p q, Orthogonal (φ p) (φ q) ↔ Orthogonal p q) :
    ∃ g : Sp F, φ = projectiveAction g := by
  refine ⟨binaryMatrix hF φ hφ, ?_⟩
  ext p
  induction p using Projectivization.ind with
  | h v hv =>
    simp only [projectiveAction_apply, smul_mk, binaryMatrix_apply,
      binaryLift_nonzero φ v hv, mk_rep]

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
