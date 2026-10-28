module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalPresentation
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.OrderNine
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.Contracts
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.PowerRelations
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations

/-!
# Source lifting for the fixed local generators of G₂(3)

The involution identity is `localRelator_zero_holds` from `LocalPresentation`.
The order-nine identity is a checked word consequence of the original ATLAS
relations. `PowerRelations` derives the two further power identities by
conjugacy to the original involution; `MixedRelations` derives the three mixed
identities by a checked cyclic-factor trace. These proofs retain the fifth
displayed ATLAS relation and use no permutation faithfulness, ambient
finiteness, or cardinal bound.

The assembled `local_relations` discharges all seven identities needed by
`localHom`. Its application to the actual marked subgroup retains only the
independent finite order bound for `LocalPresented`.

Source: Wilson–Nickerson–Bray, ATLAS G23G1-P1 and G23G1-max3W1.
See `LocalRelations/source/README.md` for the derivations.
-/

namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound
open Subgroup.CosetWordCertificate

/-- The second literal local relator holds on the actual subgroup generators. -/
public theorem localRelator_one_holds : eval boundGenerator (localRelatorLetters 1) = 1 :=
  LocalRelations.OrderNine.localRelator_one_holds

/-- The fixed second max3 word has ninth power one in the original presentation. -/
public theorem boundGenerator_true_pow_nine : boundGenerator true ^ 9 = 1 := by
  simpa [localRelatorLetters, eval_cons, pow_succ, mul_assoc] using localRelator_one_holds

/-- Assemble the seven literal identities from the two remaining families. -/
public theorem local_relations_of_remaining
    (hp : LocalRelations.RemainingPowerRelations)
    (hm : LocalRelations.RemainingMixedRelations) :
    ∀ i : Fin 7, eval boundGenerator (localRelatorLetters i) = 1 := by
  intro i
  fin_cases i
  · exact localRelator_zero_holds
  · exact localRelator_one_holds
  · exact hp.1
  · exact hm.1
  · exact hp.2
  · exact hm.2.1
  · exact hm.2.2

/-- All seven fixed local words hold on the actual max3 subgroup generators
in the original six-relator presentation. -/
public theorem local_relations :
    ∀ i : Fin 7, eval boundGenerator (localRelatorLetters i) = 1 :=
  local_relations_of_remaining LocalRelations.remaining_power_relations
    (LocalRelations.remaining_mixed_relations_of_power LocalRelations.remaining_power_relations)

/-- Apply the two-family assembly to the marked-subgroup consumer. -/
public theorem finite_card_boundSubgroup_le_of_remaining
    (hp : LocalRelations.RemainingPowerRelations)
    (hm : LocalRelations.RemainingMixedRelations)
    (hlocal : Finite LocalPresented ∧ Nat.card LocalPresented ≤ 11664) :
    Finite boundSubgroup ∧ Nat.card boundSubgroup ≤ 11664 :=
  finite_card_boundSubgroup_le_of_local (local_relations_of_remaining hp hm) hlocal

/-- The lifted relations discharge the relation premise of the actual subgroup
bound; only the independent local-presentation order bound remains. -/
public theorem finite_card_boundSubgroup_le_of_local_order
    (hlocal : Finite LocalPresented ∧ Nat.card LocalPresented ≤ 11664) :
    Finite boundSubgroup ∧ Nat.card boundSubgroup ≤ 11664 :=
  finite_card_boundSubgroup_le_of_local local_relations hlocal

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound
