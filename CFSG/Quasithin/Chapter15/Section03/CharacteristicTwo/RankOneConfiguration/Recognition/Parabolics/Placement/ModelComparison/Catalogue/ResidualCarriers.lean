module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.QuasisimpleModels
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.ProductComponents.FactorModels
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Residual carriers in the complete FF component catalogue

The existing product-factor residual theorem identifies each nontrivial
residual with a perfect projective linear group or A₅. The scalar-center
comparisons recover the special linear carriers with their binary fields.
The actual projective-line action identifies A₅ with SL₂(4). In particular,
S₅ contributes A₅, SL₂(2) contributes no component, and SL₃(2) is retained.

Model transport preserves every multiplicative equivalence, including the
center and central quotient identifications in the triple-cover case.
No perfectness hypothesis on the whole FF actor is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.6(3),(5),
printed p.105. The residual calculation reuses
`ContainedOffenderRoute.ComponentExistence.ProductComponents.factor_residual`;
its imported linear-group proofs retain their ATLAS attribution.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.ModelComparison.Catalogue
variable {D E : Type*} [Group D] [Group E]

/-- Transport every FF model through an actual isomorphism, including both
central identifications for the triple cover. -/
theorem quasisimpleModel_of_equiv (e : D ≃* E) (h : QuasisimpleModel E) :
    QuasisimpleModel D := by
  cases h with
  | linearTwo F f => exact .linearTwo F (e.trans f)
  | linearThree F f => exact .linearThree F (e.trans f)
  | symplecticFour F f => exact .symplecticFour F (e.trans f)
  | g2 F f => exact .g2 F (e.trans f)
  | alternatingSix f => exact .alternatingSix (e.trans f)
  | alternatingSeven f => exact .alternatingSeven (e.trans f)
  | tripleSix ec eq =>
    have hc : (center D).map e.toMonoidHom = center E := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact (centerCongr e ⟨x, hx⟩).property
      · intro x hx
        exact ⟨e.symm x, ((centerCongr e).symm ⟨x, hx⟩).property, e.apply_symm_apply x⟩
    exact .tripleSix ((centerCongr e).trans ec) ((QuotientGroup.congr _ _ e hc).trans eq)
  | g2DerivedTwo f => exact .g2DerivedTwo (e.trans f)
  | linearFourTwo f => exact .linearFourTwo (e.trans f)
  | linearFiveTwo f => exact .linearFiveTwo (e.trans f)

open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence in
private theorem residual_component_model (h : ProductComponents.ComponentModel D) :
    QuasisimpleModel D := by
  rcases h with h | e
  · cases h with
    | linear_two F n hn hc e =>
      let B : BinaryField :=
        { Carrier := F
          binaryAlgebra := ZMod.algebra F 2
          degree := n
          degree_pos := by omega
          card_eq := hc }
      exact .linearTwo B (e.some.trans (ProductComponents.sl2Projective B).symm)
    | linear_three F n hn ho hc e =>
      let B : BinaryField :=
        { Carrier := F
          binaryAlgebra := ZMod.algebra F 2
          degree := n
          degree_pos := hn
          card_eq := hc }
      exact .linearThree B (e.some.trans (ProductComponents.sl3Projective B ho).symm)
  · obtain ⟨e⟩ := e
    let B : BinaryField :=
      { Carrier := GaloisField 2 2
        binaryAlgebra := ZMod.algebra _ _
        degree := 2
        degree_pos := by decide
        card_eq := GaloisField.card 2 2 (by decide) }
    obtain ⟨f⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (K := B.Carrier) B.card_eq
    exact .linearTwo B (e.trans (f.symm.trans (ProductComponents.sl2Projective B).symm))

open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence in
/-- Every B.5.6 factor has trivial residual or a quasisimple residual in the
FF catalogue. This includes S₅ and both degree-one linear endpoints. -/
theorem factor_residual_model [Finite D] (h : FactorModel D) :
    solvableResidual D = ⊥ ∨
      (IsQuasisimple (solvableResidual D) ∧ QuasisimpleModel (solvableResidual D)) := by
  rcases ProductComponents.factor_residual h with ⟨_, hb⟩ | ⟨hq, hm⟩
  · exact Or.inl hb
  · exact Or.inr ⟨hq, residual_component_model hm⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.ModelComparison.Catalogue
