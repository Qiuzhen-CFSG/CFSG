module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.Basic
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Parameters
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.SuzukiCoordinates
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Relations
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.TorusCharacters

/-!
# Recovering field action on the four Ree simple blocks

Pair and simple-block preservation determine a common torus–field action
on all four signed fixed intersections. Complete additive coordinates on
the type VI blocks and two-parameter coordinates on the nonabelian type V
blocks identify the actual induced parameter maps. Opposite-root relations
force scaled multiplication and inverse scales on the linear blocks;
their Weyl words then force the same field map on the Suzuki blocks,
including the central parameter and the inverse scales on opposite signs.

Scalar normalization yields one field equivalence. The two long simple-root
scales determine a torus whose characters are twist-compatible on every
root. Its word formulas extend to every element of all four blocks by full
fixed-intersection coverage. `exists_torusFieldAction` discharges all three
inputs of the conditional assembly below. Torus realization in the fixed
group remains a separate result for the caller.

Source: GLS3, Table 2.4, §2.4, 2.5.1(b,c), and 2.5.12, in
`refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.BlockParameters
open FieldRecovery
variable {m : ℕ}

/-- Assemble the three independent calculations on the full fixed intersections.
The source-theorem owner must still discharge each extra premise. -/
theorem exists_torusFieldAction_of_parameter_relations
    (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
    (hb : PreservesSimpleBlocks d a) (C : SuzukiCoordinates d)
    (hrelations : ∃ c : (CoefficientField m)ˣ, ParameterRelations d a hb C c)
    (htorus : ∀ b c : (CoefficientField m)ˣ, TorusWordLaws b c) :
    ∃ (u : TorusParameters m) (σ : CoefficientField m ≃+* CoefficientField m),
      TwistCompatible u ∧ HasTorusFieldAction d a u σ := by
  obtain ⟨c, hc⟩ := hrelations
  obtain ⟨b, σ, hlin, hsu⟩ := exists_field_on_coordinates_of_relations d a hb C c hc
  obtain ⟨hu, htl, hts⟩ := htorus b c
  refine ⟨blockTorus b c, σ, hu, ?_⟩
  intro s positive x hx
  rw [← matrixTorusConj_apply]
  cases s with
  | linear =>
      obtain ⟨t, rfl⟩ := linearElement_surjective d positive hx
      rw [hlin, linearElement_word, linearElement_word, matrixFieldMap_linearWord, htl]
  | suzuki =>
      obtain ⟨t, v, rfl⟩ := C.element_cover positive hx
      rw [hsu, SuzukiCoordinates.element_word, SuzukiCoordinates.element_word,
        matrixFieldMap_suzukiWord, hts]

/-- Pair and simple-block preservation yield one field automorphism and a
twist-compatible torus acting on all four complete fixed intersections.
The coordinate, parameter-relation and torus-character inputs are all proved. -/
theorem exists_torusFieldAction (hm : 1 ≤ m) (d : LocalBlockInput m)
    [IsSimpleGroup d.fixedGroup] [Group.IsPerfect d.fixedGroup]
    (hindex : Odd (LargeLocalSeeds.standardUnipotent d).index)
    (a : MulAut d.fixedGroup) (hp : d.PreservesUnipotentPair a)
    (hb : PreservesSimpleBlocks d a) :
    ∃ (u : TorusParameters m) (σ : CoefficientField m ≃+* CoefficientField m),
      TwistCompatible u ∧ HasTorusFieldAction d a u σ := by
  exact exists_torusFieldAction_of_parameter_relations d a hb (suzukiCoordinates d)
    (exists_parameterRelations hm d hindex a hp hb (suzukiCoordinates d))
    torusWordLaws

end ReeF4.LocalBlockInput.PairRigidity.BlockParameters
end
