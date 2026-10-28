module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.Spanning

/-!
# Explicit generator formulas for the odd tensor slot

The epsilon, quarter-weight and half-overlap signs specify a concrete action
on every marked point tensor. The actual N1 normal form shows that any two
representations with these formulas coincide. These are conditional comparison
lemmas: this module does not assert that either representation satisfies them.

The scan of 29.6(3) prints psi_2(alpha); Section 14's definitions show that
an odd second generator exchanges axes 1 and 3. The N1 action used in 29.8
requires psi_1(alpha), fixing axis 1. We use that intended first generator
and retain its odd parity correction. Composing 29.6(1)--(3) also retains
epsilon_x(e), which is omitted from the collected display on printed p.157.

Source: Aschbacher, Sporadic Groups, Section 14, pp.58--61, and 29.6--29.8,
pp.156--157 (PDF pages 35--36 and 84). Products use left composition, so the
collected word is psiAut1N alpha * psi2N e * psi1N d.
-/

@[expose] public section
open Atlas.Codes Atlas.Fischer
open Sporadic.Monster.Construction LocalC ShortFamilies TrialitySpin
open scoped TensorProduct
noncomputable section
namespace Sporadic.Monster.Construction.NMonomial.ZeroAction

/-- The explicit source generator equations in the marked odd tensor slot.
The odd automorphism clause uses the first standard generator, as required by
N1 and by the argument of 29.8; the subscript 2 in 29.6(3) is inconsistent
with the definitions in Section 14. -/
structure OddGeneratorFormulas (ρ : Representation ℝ N1 TensorTwo) : Prop where
  first : ∀ (d : ParkerLoop) (x : Omega) (b : ParkerLoop),
    ρ ⟨psi1N d, psi1N_mem_N1 d⟩ (pointVector x ⊗ₜ[ℝ] delta2 b) =
      pointVector x ⊗ₜ[ℝ]
        delta2 (parkerSign (d.1.val x + golayQuarterWeight d.1 + golayHalfOverlap d.1 b.1) b)
  second : ∀ (e : ParkerLoop) (x : Omega) (b : ParkerLoop),
    ρ ⟨psi2N e, psi2N_mem_N1 e⟩ (pointVector x ⊗ₜ[ℝ] delta2 b) =
      pointVector x ⊗ₜ[ℝ] delta2 (parkerSign (e.1.val x) (parkerLoopMultiply e b))
  standard_even : ∀ (α : ParkerStandardGroup), α.val parkerOmega = parkerOmega →
    ∀ (x : Omega) (b : ParkerLoop),
    ρ ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (pointVector x ⊗ₜ[ℝ] delta2 b) =
      pointVector ((parkerStandardProjection α).val x) ⊗ₜ[ℝ] delta2 (α.val b)
  standard_odd : ∀ (α : ParkerStandardGroup), α.val parkerOmega ≠ parkerOmega →
    ∀ (x : Omega) (b : ParkerLoop),
    ρ ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (pointVector x ⊗ₜ[ℝ] delta2 b) =
      pointVector ((parkerStandardProjection α).val x) ⊗ₜ[ℝ]
        delta2 (parkerSign (b.1.val x + golayQuarterWeight b.1) (α.val b))

/-- The literal normal form of N1 makes the independently specified generator
formulas determine the entire representation. -/
theorem representation_eq_of_oddGeneratorFormulas
    (ρ τ : Representation ℝ N1 TensorTwo)
    (hρ : OddGeneratorFormulas ρ) (hτ : OddGeneratorFormulas τ) : ρ = τ := by
  have h1 (d : ParkerLoop) : ρ ⟨psi1N d, psi1N_mem_N1 d⟩ =
      τ ⟨psi1N d, psi1N_mem_N1 d⟩ :=
    tensorTwo_ext _ _ (fun x b => (hρ.first d x b).trans (hτ.first d x b).symm)
  have h2 (e : ParkerLoop) : ρ ⟨psi2N e, psi2N_mem_N1 e⟩ =
      τ ⟨psi2N e, psi2N_mem_N1 e⟩ :=
    tensorTwo_ext _ _ (fun x b => (hρ.second e x b).trans (hτ.second e x b).symm)
  have ha (α : ParkerStandardGroup) : ρ ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ =
      τ ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ := by
    apply tensorTwo_ext
    intro x b
    by_cases hα : α.val parkerOmega = parkerOmega
    · exact (hρ.standard_even α hα x b).trans (hτ.standard_even α hα x b).symm
    · exact (hρ.standard_odd α hα x b).trans (hτ.standard_odd α hα x b).symm
  apply MonoidHom.ext
  intro g
  obtain ⟨⟨d,e,α⟩,rfl⟩ := normalForm_bijective.surjective g
  have hw : normalForm d e α =
      (⟨psiAut1N α, psiAut1N_mem_N1 α⟩ : N1) *
      ⟨psi2N e, psi2N_mem_N1 e⟩ * ⟨psi1N d, psi1N_mem_N1 d⟩ := by
    apply Subtype.ext
    rfl
  change ρ (normalForm d e α) = τ (normalForm d e α)
  rw [hw, map_mul, map_mul, map_mul, map_mul, h1, h2, ha]

/-- The collected even word, in left-composition order. The epsilon of e
comes from 29.6(2); it must be retained when composing the three generators. -/
theorem OddGeneratorFormulas.normalForm_even
    {ρ : Representation ℝ N1 TensorTwo} (hρ : OddGeneratorFormulas ρ)
    (d e : ParkerLoop) (α : ParkerStandardGroup) (hα : α.val parkerOmega = parkerOmega)
    (x : Omega) (b : ParkerLoop) :
    ρ (normalForm d e α) (pointVector x ⊗ₜ[ℝ] delta2 b) =
      pointVector ((parkerStandardProjection α).val x) ⊗ₜ[ℝ]
        delta2 (parkerSign
          (e.1.val x + (d.1.val x + golayQuarterWeight d.1 + golayHalfOverlap d.1 b.1))
          (α.val (parkerLoopMultiply e b))) := by
  have hw : normalForm d e α =
      (⟨psiAut1N α, psiAut1N_mem_N1 α⟩ : N1) *
      ⟨psi2N e, psi2N_mem_N1 e⟩ * ⟨psi1N d, psi1N_mem_N1 d⟩ := by
    apply Subtype.ext
    rfl
  rw [hw, map_mul, map_mul]
  change ρ ⟨psiAut1N α, psiAut1N_mem_N1 α⟩
    (ρ ⟨psi2N e, psi2N_mem_N1 e⟩
      (ρ ⟨psi1N d, psi1N_mem_N1 d⟩ (pointVector x ⊗ₜ[ℝ] delta2 b))) = _
  rw [hρ.first, hρ.second, hρ.standard_even α hα,
    parkerLoopMultiply_sign_right, parkerSign_add, parkerStandard_preserves_sign]

end Sporadic.Monster.Construction.NMonomial.ZeroAction
