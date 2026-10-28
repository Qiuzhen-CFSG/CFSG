module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Detecting field automorphisms on SL₂

Every element of a two-element field is zero or one, so all its field
automorphisms are trivial. Over an arbitrary field, an entrywise field
map on SL₂ can be inner only when it is trivial: determinant-one companion
matrices attain every trace, while conjugation preserves trace.

These are field-action facts used in the binary rigidity and nonbinary
extension arguments of Aschbacher--Smith F.1.12, printed pp.263--264 of
`refs/quasithin.pdf`. They do not classify symplectic automorphisms.
-/

@[expose] public section

noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
variable {F : Type*} [Field F]

/-- A field with two elements has no nontrivial field automorphism. -/
theorem fieldEquiv_eq_refl_of_card_two (hF : Nat.card F = 2) (σ : F ≃+* F) :
    σ = RingEquiv.refl F := by
  obtain ⟨y, hy, hu⟩ := (Nat.card_eq_two_iff' (0 : F)).mp hF
  have hc (x : F) : x = 0 ∨ x = 1 := by
    by_cases hx : x = 0
    · exact Or.inl hx
    · exact Or.inr ((hu x hx).trans (hu 1 one_ne_zero).symm)
  apply RingEquiv.ext
  intro x
  rcases hc x with rfl | rfl <;> simp

/-- The corresponding entrywise symplectic automorphism is trivial. -/
theorem fieldAutomorphism_eq_one_of_card_two (hF : Nat.card F = 2) (σ : F ≃+* F) :
    fieldAutomorphism σ = 1 := by
  rw [fieldEquiv_eq_refl_of_card_two hF σ]
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  rfl

private def traceMatrix (t : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![t,-1;1,0], by simp [Matrix.det_fin_two]⟩

/-- A field automorphism inducing an inner map on SL₂ is the identity.
Companion matrices attain every trace, and conjugation preserves trace. -/
theorem fieldEquiv_eq_refl_of_SL2_inner (σ : F ≃+* F)
    (c : Matrix.SpecialLinearGroup (Fin 2) F)
    (h : ∀ A : Matrix.SpecialLinearGroup (Fin 2) F,
      Matrix.SpecialLinearGroup.map σ.toRingHom A = c * A * c⁻¹) :
    σ = RingEquiv.refl F := by
  apply RingEquiv.ext
  intro t
  have hc : (c⁻¹).val * c.val = 1 := congrArg Subtype.val (inv_mul_cancel c)
  have he := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F => Matrix.trace A.val)
    (h (traceMatrix t))
  change Matrix.trace (((traceMatrix t).val).map σ) =
    Matrix.trace (c.val * (traceMatrix t).val * (c⁻¹).val) at he
  rw [Matrix.trace_mul_cycle, hc, Matrix.one_mul] at he
  simpa [traceMatrix, Matrix.trace, Fin.sum_univ_two] using he
end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
