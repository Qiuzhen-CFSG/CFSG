module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.BorelPlacement.QuotientDichotomy

/-!+# Field four from a characteristic-controlled Borel

The root-or-module dichotomy proves the numerical deduction in the last
paragraph of 15.4.20. Characteristic-normalizer control places the constructed
Borel in M₁, where two-perfection makes it normalize the actual V₁.

The present theorem is conditional on block commutation and construction of
the Borel inside C(G,R). Neither is an additional source assumption: both
remain structural proof obligations before `source_parameter_eq_two` can be
exported from just ContraryData and ExchangedBlock. No field-four or
seed-centrality premise occurs in the reduction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.9,
printed p.123, and the proof of 15.4.20, printed p.1164.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.BorelPlacement
open Subgroup ChapterC
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {d : Source.Geometry G} {i j : Bool}

/-- The final field bound once the genuine earlier structural inputs are proved. -/
theorem parameter_eq_two_of_characteristic_control
    (c : ContraryData κ d i j) (b : ExchangedBlock c)
    (hc : ⁅b.first, ExchangedBlock.second b⁆ = ⊥)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (model : BlockModuleModel b.first (Matrix.SL2.naturalAction F))
    (hcard : Nat.card F = 2 ^ b.n)
    (hB : ExchangedBlock.ambientBorel b hc model ≤
      characteristicNormalizerClosure ((d.wholeX ⊔ c.U : Subgroup G).pCoreIn 2)) :
    b.n = 2 :=
  ExchangedBlock.parameter_eq_two_of_borel_placement b hc model hcard
    (hB.trans c.core_characteristic_control)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.BorelPlacement
