module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co1.CentralizerSection.OrthogonalEmbedding.Coordinates
public import Mathlib.Tactic.FinCases

/-!
# The six coordinate Siegel transformations at e₀

The root parameters perpendicular to e₀ form an additive subgroup, by
`siegel_add`. Their binary coordinate expansion uses e₀ and the six displayed
vectors; the e₀ parameter acts trivially. Hence containment of these six actual
isometries suffices for containment of the entire root subgroup.

This is the fixed-root step of the Ω₈⁺(2) embedding for GLS3 Table 5.3l.
-/

@[expose] public section
open ClassicalOrthogonal Theory.AlgebraicGroup
open ClassicalOrthogonal.Quadratic
namespace Sporadic.LeechRelated.Co1.CentralizerSection.OrthogonalEmbedding

def rootDirection : Fin 6 → V := ![e 1, e 2, e 3, f 1, f 2, f 3]

theorem rootDirection_perp (i : Fin 6) : Q.polarBilin e0 (rootDirection i) = 0 := by
  rw [polar_swap Q]
  change (formD 4 (ZMod 2)).polarBilin (rootDirection i) (e 0) = 0
  rw [polarD_e]
  fin_cases i <;> decide +kernel

noncomputable def rootGenerator (i : Fin 6) : O :=
  siegelElement Q e0 (rootDirection i) (formD_e 0) (rootDirection_perp i)

private def rootParameters (H : Subgroup O) : AddSubgroup V where
  carrier := {v | ∃ hv : Q.polarBilin e0 v = 0,
    siegelElement Q e0 v (formD_e 0) hv ∈ H}
  zero_mem' := by
    refine ⟨by simp, ?_⟩
    have h : siegelElement Q e0 0 (formD_e 0) (by simp) = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      exact siegel_zero Q e0
    rw [h]
    exact H.one_mem
  add_mem' := by
    rintro v w ⟨hv, hm⟩ ⟨hw, hn⟩
    have hp : Q.polarBilin e0 (v+w) = 0 := by rw [map_add, hv, hw, add_zero]
    refine ⟨hp, ?_⟩
    have h : siegelElement Q e0 (v+w) (formD_e 0) hp =
        siegelElement Q e0 v (formD_e 0) hv * siegelElement Q e0 w (formD_e 0) hw := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      exact (siegel_add Q e0 v w x (formD_e 0) hv hw).symm
    rw [h]
    exact H.mul_mem hm hn
  neg_mem' := by
    rintro v ⟨hv, hm⟩
    have hp : Q.polarBilin e0 (-v) = 0 := by rw [map_neg, hv, neg_zero]
    refine ⟨hp, ?_⟩
    have h : siegelElement Q e0 (-v) (formD_e 0) hp =
        (siegelElement Q e0 v (formD_e 0) hv)⁻¹ := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      rfl
    rw [h]
    exact H.inv_mem hm

private theorem e0_mem_rootParameters (H : Subgroup O) : e0 ∈ rootParameters H := by
  have hp : Q.polarBilin e0 e0 = 0 := by simp [e0, e]
  refine ⟨hp, ?_⟩
  have h : siegelElement Q e0 e0 (formD_e 0) hp = 1 := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change siegel Q e0 e0 x = x
    simp only [siegel, show Q e0 = 0 from formD_e 0, zero_mul, zero_smul,
      sub_zero, add_sub_cancel_right]
  rw [h]
  exact H.one_mem

/-- The six coordinate roots generate every Siegel transformation based at e0. -/
theorem root_mem_of_six (H : Subgroup O) (hr : ∀ i, rootGenerator i ∈ H)
    (v : V) (hv : Q.polarBilin e0 v = 0) :
    siegelElement Q e0 v (formD_e 0) hv ∈ H := by
  have he (i : Fin 4) : e i ∈ rootParameters H := by
    fin_cases i
    · exact e0_mem_rootParameters H
    · exact ⟨rootDirection_perp 0, hr 0⟩
    · exact ⟨rootDirection_perp 1, hr 1⟩
    · exact ⟨rootDirection_perp 2, hr 2⟩
  have hf (i : Fin 4) (hi : i ≠ 0) : f i ∈ rootParameters H := by
    fin_cases i
    · exact (hi rfl).elim
    · exact ⟨rootDirection_perp 3, hr 3⟩
    · exact ⟨rootDirection_perp 4, hr 4⟩
    · exact ⟨rootDirection_perp 5, hr 5⟩
  have hv0 : v (.inr 0) = 0 := by
    simpa only [polar_swap Q e0, polarD_e] using hv
  have hterm (i : Index 4) : v i • Pi.single i (1 : ZMod 2) ∈ rootParameters H := by
    have hb : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
    rcases hb (v i) with h0 | h1
    · simp only [h0, zero_smul]
      exact (rootParameters H).zero_mem
    · rw [h1, one_smul]
      cases i with
      | inl j => exact he j
      | inr j =>
        apply hf j
        intro h
        subst j
        have : (0 : ZMod 2) = 1 := hv0.symm.trans h1
        exact zero_ne_one this
  have hs := (rootParameters H).sum_mem (fun i (_ : i ∈ Finset.univ) => hterm i)
  have hsum : ∑ i : Index 4, v i • Pi.single i (1 : ZMod 2) = v := by
    ext j
    simp [Pi.single_apply]
  rw [hsum] at hs
  obtain ⟨_, hm⟩ := hs
  exact hm

end Sporadic.LeechRelated.Co1.CentralizerSection.OrthogonalEmbedding
