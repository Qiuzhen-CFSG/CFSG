module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Parameters
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Relations.Actions
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Relations.LinearRigidity
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Relations.SuzukiRigidity

/-!
# Assembly of the Ree block parameter relations

A common field action on the opposite linear blocks gives the scaled
multiplication law for their actual induced additive map and the inverse
scale on the negative block. A compatible action on the pure Suzuki curves
then determines the central action by the square law proved in `Actions`.
This supplies all three clauses of `ParameterRelations`.

`LinearRigidity` derives the signed linear action from opposite-root braid
and conjugation relations. `SuzukiRigidity` uses that action on paired Weyl
words to force the same field map and zero central displacement on both
Suzuki curves; their central braid forces inverse scales. The final theorem
`exists_parameterRelations` discharges both action premises using these
calculations. Complete Suzuki coordinates remain an explicit input, whose
construction belongs to the caller.

Source: GLS3, Table 2.4 types V and VI, §2.4, and 2.5.1(b,c), in
`refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
variable {m : ℕ}

/-- Recover the exact parameter identities from the two signed actions. -/
theorem parameterRelations_of_signed_actions
     (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
     (hb : PreservesSimpleBlocks d a) (C : SuzukiCoordinates d)
     (b c : (CoefficientField m)ˣ) (σ : CoefficientField m ≃+* CoefficientField m)
     (hlin : SignedLinearAction d a b σ) (hsu : PureSuzukiAction d a C c σ) :
     ParameterRelations d a hb C c := by
  have hf (t : CoefficientField m) : linearParameterAut d a hb true t = b * σ t := by
    apply linearElement_injective d true
    exact (linearParameterAut_action d a hb true t).symm.trans (hlin true t)
  have h1 : linearParameterAut d a hb true 1 = (b : CoefficientField m) := by
    rw [hf, map_one, mul_one]
  have hdiv (t : CoefficientField m) :
      linearParameterAut d a hb true t / linearParameterAut d a hb true 1 = σ t := by
    rw [hf, h1, mul_div_cancel_left₀ _ b.ne_zero]
  refine ⟨?_, ?_, ?_⟩
  · intro t v
    simp only [hf, map_mul, map_one, mul_one]
    ring
  · intro t
    rw [hdiv, h1]
    simpa only [signedScale, Bool.false_eq_true, ↓reduceIte, Units.val_inv_eq_inv_val]
      using hlin false t
  · intro positive t u
    rw [hdiv, hdiv]
    exact suzuki_action_of_pure d a C c σ hsu positive t u

/-- Conditional assembly; both group-calculation premises still require proofs. -/
theorem exists_parameterRelations_of_signed_actions
     (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
     (hb : PreservesSimpleBlocks d a) (C : SuzukiCoordinates d)
     (hlin : ∃ (b : (CoefficientField m)ˣ) (σ : CoefficientField m ≃+* CoefficientField m),
       SignedLinearAction d a b σ)
     (hsu : ∀ (b : (CoefficientField m)ˣ) (σ : CoefficientField m ≃+* CoefficientField m),
       SignedLinearAction d a b σ → ∃ c : (CoefficientField m)ˣ, PureSuzukiAction d a C c σ) :
     ∃ c : (CoefficientField m)ˣ, ParameterRelations d a hb C c := by
  obtain ⟨b, σ, hlin⟩ := hlin
  obtain ⟨c, hsu⟩ := hsu b σ hlin
  exact ⟨c, parameterRelations_of_signed_actions d a hb C b c σ hlin hsu⟩

/-- Pair and block preservation force all three parameter relations on the
supplied complete Suzuki coordinates. The signed actions are derived from
the actual root relations, with no additional action hypotheses. -/
theorem exists_parameterRelations (hm : 1 ≤ m) (d : LocalBlockInput m)
    [IsSimpleGroup d.fixedGroup] [Group.IsPerfect d.fixedGroup]
    (hindex : Odd (LargeLocalSeeds.standardUnipotent d).index)
    (a : MulAut d.fixedGroup) (hp : d.PreservesUnipotentPair a)
    (hb : PreservesSimpleBlocks d a) (C : SuzukiCoordinates d) :
    ∃ c : (CoefficientField m)ˣ, ParameterRelations d a hb C c := by
  exact exists_parameterRelations_of_signed_actions d a hb C
    (exists_signedLinearAction hm d hindex a hp hb)
    (exists_pureSuzukiAction hm d a hb C)

end ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
end
