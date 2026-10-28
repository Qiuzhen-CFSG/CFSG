module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.Words
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Base
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases

/-!
# The retained relators hold on the literal permutation carrier

The packed permutations from the existing HS order certificate equal the
defining generators, including the inversion of the source right action.
Checking the thirteen relators on all 100 letters therefore supplies an actual
surjection from the presented group onto this carrier.

This only proves one inclusion between the relation subgroup and the carrier
kernel. The reverse inclusion remains the presentation-completeness obligation.
A finite upper bound for the presented group, compared along the constructed
surjection, is sufficient; an abstract equality of group orders is not used as
a substitute for this map.

Source: ATLAS HSG1-P1.M and HSG1-p100B0; see `Descent/source/` and the existing
`AtlasCarriers/source/`. The finite checks use Lean kernel reduction.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent
open Sporadic.LeechRelated.HS
open Sporadic.LeechRelated.HS.OrderCertificate

private theorem packed_relations (i : Fin 13) : relation p0 p1 i = 1 := by
  fin_cases i <;> apply Equiv.ext <;> apply allFin <;> decide +kernel

/-- All thirteen source relators hold with the literal carrier marking. -/
theorem carrier_relations (i : Fin 13) :
    relation generatorAElement generatorBElement i = 1 := by
  apply inclusion_injective
  rw [map_relation, map_one]
  change relation generatorA generatorB i = 1
  rw [← a_eq_generator, ← b_eq_generator]
  exact packed_relations i

theorem carrierEvaluation_relator (i : Fin 13) : carrierEvaluation (relator i) = 1 := by
  rw [relator, map_relation, carrierEvaluation_a, carrierEvaluation_b]
  exact carrier_relations i

/-- The easy inclusion is proved by the finite permutation checks. -/
theorem normalClosure_le_carrierEvaluation_ker :
    Subgroup.normalClosure relators ≤ carrierEvaluation.ker := by
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨i, rfl⟩
  exact carrierEvaluation_relator i

/-- The group defined by the thirteen retained relators. -/
abbrev Presentation := PresentedGroup relators

/-- The actual marked epimorphism from the presented group to the carrier. -/
def presentedToCarrier : Presentation →* Carrier :=
  PresentedGroup.toGroup (f := carrierGenerator) (fun r hr => by
    obtain ⟨i, rfl⟩ := hr
    exact carrierEvaluation_relator i)

@[simp] theorem presentedToCarrier_a :
    presentedToCarrier (PresentedGroup.of false) = generatorAElement :=
  PresentedGroup.toGroup.of _

@[simp] theorem presentedToCarrier_b :
    presentedToCarrier (PresentedGroup.of true) = generatorBElement :=
  PresentedGroup.toGroup.of _

theorem presentedToCarrier_mk (w : FreeGroup Bool) :
    presentedToCarrier (PresentedGroup.mk relators w) = carrierEvaluation w := rfl

theorem presentedToCarrier_surjective : Function.Surjective presentedToCarrier := by
  apply MonoidHom.range_eq_top.mp
  exact eq_top_of_generators_mem _ ⟨PresentedGroup.of false, presentedToCarrier_a⟩
    ⟨PresentedGroup.of true, presentedToCarrier_b⟩

/-- Faithfulness of the constructed marked map proves presentation completeness. -/
theorem relatorsPresentCarrier_of_injective (hi : Function.Injective presentedToCarrier) :
    RelatorsPresentCarrier := by
  intro w hw
  apply PresentedGroup.mk_eq_one_iff.mp
  apply hi
  rw [presentedToCarrier_mk, map_one]
  exact hw

/-- A finite cardinal bound suffices because the marked surjection is proved. -/
theorem relatorsPresentCarrier_of_card_le [Finite Presentation]
    (hc : Nat.card Presentation ≤ Nat.card Carrier) : RelatorsPresentCarrier :=
  relatorsPresentCarrier_of_injective
    (presentedToCarrier_surjective.bijective_of_nat_card_le hc).injective

end Representation.HigmanSims.LargeModels.TracePair.Descent
