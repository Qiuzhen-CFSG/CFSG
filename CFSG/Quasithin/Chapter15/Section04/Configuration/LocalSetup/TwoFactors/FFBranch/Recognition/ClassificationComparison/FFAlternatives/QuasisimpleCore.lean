module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.QuasisimpleModels
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.GroupCore
public import Theory.SpecificGroups.FFG2PrimeCore

/-!
# Reducing the quasisimple FF branch to one concrete center calculation

We use the actual equivalence in each of the ten source alternatives.
The classical models and full G₂ model have trivial three-prime core by
the proved center, normal-subgroup and order calculations. The triple
cover's center of order three is enough. Only the center of the actual
binary derived octonion group remains explicit below. Quasisimplicity
is inherited from the classified group, so these statements do not ask
for a separate simplicity proof of that model.

The self-centralizing generalized Fitting subgroup then transfers this
conclusion to the original actor. This is a conditional group reduction,
not a universal B.5.1 or B.5.6 classification theorem.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.5.6(1),
printed p.105, applied in 15.4.18 on printed p.1163.
-/

public section
open Subgroup Theory.GroupTheory Theory.SpecificGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]

/-- The ten-model group list reduces to the center of G₂(2)'. The premise
is deliberately isolated for its concrete model owner to discharge. -/
theorem QuasisimpleModel.threePrimeCore_eq_bot_of_binaryDerived_center
    (h : QuasisimpleModel L)
    (hZ : IsQuasisimple (commutator (Atlas.G2.Model (ZMod 2))) →
      IsPGroup 3 (center (commutator (Atlas.G2.Model (ZMod 2))))) : pPrimeCore 3 L = ⊥ := by
  cases h with
  | linearTwo F e =>
    exact pPrimeCore_eq_bot_of_equiv e (sl_two_threePrimeCore F.Carrier)
  | linearThree F e =>
    exact pPrimeCore_eq_bot_of_equiv e (sl_three_threePrimeCore F.Carrier)
  | symplecticFour F e =>
    let := IsQuasisimple.of_mulEquiv e
    exact pPrimeCore_eq_bot_of_equiv e
      (symplectic_four_threePrimeCore F.Carrier F.degree F.card_eq)
  | g2 F e =>
    let := IsQuasisimple.of_mulEquiv e
    exact pPrimeCore_eq_bot_of_equiv e (g2_threePrimeCore F.Carrier F.degree F.card_eq)
  | alternatingSix e =>
    exact pPrimeCore_eq_bot_of_equiv e (alternating_threePrimeCore 6 (by decide))
  | alternatingSeven e =>
    exact pPrimeCore_eq_bot_of_equiv e (alternating_threePrimeCore 7 (by decide))
  | tripleSix e _ => exact quasisimple_center_three_threePrimeCore e
  | g2DerivedTwo e =>
    let := IsQuasisimple.of_mulEquiv e
    exact pPrimeCore_eq_bot_of_equiv e (g2_derived_two_threePrimeCore_of_center (hZ inferInstance))
  | linearFourTwo e =>
    exact pPrimeCore_eq_bot_of_equiv e (binary_linear_threePrimeCore 4 (Or.inl rfl))
  | linearFiveTwo e =>
    exact pPrimeCore_eq_bot_of_equiv e (binary_linear_threePrimeCore 5 (Or.inr rfl))

/-- Once the remaining concrete center calculation is available, the listed
quasisimple generalized Fitting subgroup eliminates the actor's core. -/
theorem threePrimeCore_eq_bot_of_quasisimple_alternative
    {D : Type*} [Group D] [Finite D] [IsQuasisimple (generalizedFitting D)]
    (h : QuasisimpleModel (generalizedFitting D))
    (hZ : IsQuasisimple (commutator (Atlas.G2.Model (ZMod 2))) →
      IsPGroup 3 (center (commutator (Atlas.G2.Model (ZMod 2))))) : pPrimeCore 3 D = ⊥ :=
  pPrimeCore_eq_bot_of_selfCentralizing (generalizedFitting D)
    (h.threePrimeCore_eq_bot_of_binaryDerived_center hZ)
    ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
