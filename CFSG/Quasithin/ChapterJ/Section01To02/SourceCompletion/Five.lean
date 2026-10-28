module

public import CFSG.Quasithin.ChapterJ.Section01To02.SourceCompletion.FiveArithmetic
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.FiveCore.SourceCompletion.Noncentral

/-!
# The unconditional source five-centralizer conclusion

The actual quaternion centralizer and noncentral inverter are constructed
from the original Ru hypotheses. The order-45 exclusion then gives the
source five-core order125, quaternion supplement, and nonconjugacy to LB.

Source: Aschbacher–Smith, J.2.7(5–6), printed pp.435–436.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.SourceCompletion
open Centralizers Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- J.2.7(5–6) for the actual source centralizer, with all geometric inputs discharged. -/
theorem five_core_source (B5 : Sylow 5 d.toTypeRuSetup.H) :
    G5 B5 = pCoreIn 5 (G5 B5) ⊔ CQ B5 ∧
      Nonempty (CQ B5 ≃* QuaternionGroup 2) ∧
      Nat.card (pCoreIn 5 (G5 B5)) = 125 ∧ NotConjToLB c B5 := by
  obtain ⟨v⟩ := c.fiveInverterData_source B5
  exact five_core_of_inverter c B5 v

include c in
/-- The original five-centralizer supplies the subgroup of order125 used in J.3. -/
theorem five_core_card (B5 : Sylow 5 d.toTypeRuSetup.H) :
    Nat.card (pCoreIn 5 (G5 B5)) = 125 := (five_core_source c B5).2.2.1

include c in
/-- The source odd core itself has order125, before identifying it with O₅. -/
theorem five_oddPart_card (B5 : Sylow 5 d.toTypeRuSetup.H) :
    Nat.card (fiveOddPart B5) = 125 := by
  obtain ⟨q⟩ := c.fiveQuaternionData_source B5
  obtain ⟨v⟩ := c.fiveInverterData_source B5
  obtain ⟨e,_⟩ := cubic_quotient c
  have hn := (five_core_source c B5).2.2.2
  have hnot := c.B5Image_not_sylow_of_notConj B5 d.card_Z hn
    (c.residual_sylow_five_card (B_card c) e)
  rcases v.oddPart_card_cases c B5 d.card_Z q d.toTypeRuSetup.odd_subgroup_card
    with h5 | h45 | h125
  · exact (c.fiveOddPart_card_ne_five B5 d.card_Z q hnot h5).elim
  · exact (five_odd_card_ne_45 c B5 q v h45).elim
  · exact h125

include c in
/-- The source odd core and five-core are the same literal subgroup. -/
theorem five_oddPart_eq_core (B5 : Sylow 5 d.toTypeRuSetup.H) :
    fiveOddPart B5 = pCoreIn 5 (G5 B5) :=
  fiveOddPart_eq_fiveCore_of_isPGroup B5 (IsPGroup.of_card (p := 5) (n := 3)
    (five_oddPart_card c B5))

end CFSG.Quasithin.ChapterJ.SourceCompletion
