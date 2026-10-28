module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Relations.Actions
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Relations.SuzukiRigidity.UnsignedAction
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Relations.SuzukiRigidity.OppositeScales

/-!
# Suzuki rigidity from the signed linear action

The signed linear action forces the common field map and vanishing
central displacement on each Suzuki sign, with the norm character on the
central parameter. The alternating five-factor relation between the actual
opposite central elements then forces the two nonzero scales to be inverse.
This module combines these results to construct the signed pure action.

`exists_pureSuzukiAction` uses only `m ≥ 1`, block preservation, complete
Suzuki coordinates and the signed linear action. The common field map,
vanishing displacement and inverse scales are all conclusions. Construction
of the signed linear action and the coordinates remains with the caller.

Sources: GLS3, Table 2.4, 2.4.5(d), and 2.5.1(b,c), in
`refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
variable {m : ℕ}

/-- Once the two scales are proved inverse, the unsigned action is the required
signed pure-curve action. -/
theorem pureSuzukiAction_of_unsigned (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
    (C : SuzukiCoordinates d) (c : Bool → (CoefficientField m)ˣ)
    (σ : CoefficientField m ≃+* CoefficientField m)
    (h : UnsignedSuzukiAction d a C c σ) (hinv : c false = (c true)⁻¹) :
    PureSuzukiAction d a C (c true) σ := by
  intro positive t
  have he := h positive t 0
  simp only [map_zero, mul_zero] at he
  cases positive
  · simpa only [hinv, signedScale, Bool.false_eq_true, ↓reduceIte] using he
  · exact he

/-- Assembly from an explicit opposite-scale implication. The final theorem
below discharges this premise using the central braid. -/
theorem exists_pureSuzukiAction_of_inverse_scales (hm : 1 ≤ m)
    (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
    (hb : PreservesSimpleBlocks d a) (C : SuzukiCoordinates d)
    (b : (CoefficientField m)ˣ) (σ : CoefficientField m ≃+* CoefficientField m)
    (hlin : SignedLinearAction d a b σ)
    (hinv : ∀ c : Bool → (CoefficientField m)ˣ,
      UnsignedSuzukiAction d a C c σ → c false = (c true)⁻¹) :
    ∃ c : (CoefficientField m)ˣ, PureSuzukiAction d a C c σ := by
  obtain ⟨c, hc⟩ := exists_unsigned_suzuki_action hm d a hb C b σ hlin
  exact ⟨c true, pureSuzukiAction_of_unsigned d a C c σ hc (hinv c hc)⟩

/-- Signed linear semilinearity forces compatible pure Suzuki curves on both
opposite blocks, with the same field map and inverse nonzero scales. -/
theorem exists_pureSuzukiAction (hm : 1 ≤ m)
    (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
    (hb : PreservesSimpleBlocks d a) (C : SuzukiCoordinates d)
    (b : (CoefficientField m)ˣ) (σ : CoefficientField m ≃+* CoefficientField m)
    (hlin : SignedLinearAction d a b σ) :
    ∃ c : (CoefficientField m)ˣ, PureSuzukiAction d a C c σ := by
  exact exists_pureSuzukiAction_of_inverse_scales hm d a hb C b σ hlin
    (fun c hc => suzuki_scales_inverse d a C c σ hc)

end ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
end
