module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Presentation
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.GeneratorCover
import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Base
import Mathlib.Tactic.FinCases

/-!
# The sourced presentation maps onto the literal HS carrier

All thirteen ATLAS words vanish in the inverse degree-100 permutations.
The universal property constructs a homomorphism with the exact marked
generator images, and generation makes it surjective. Its injectivity is
not established here: finite permutation checks cannot bound the universal
group. A separate abstract presentation certificate must supply that step.

Source: HSG1-P1.M and HSG1-p100B0, with their published product conventions.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation

private theorem packed_words (i : Fin 13) :
    word OrderCertificate.p0 OrderCertificate.p1 i = 1 := by
  fin_cases i <;> apply Equiv.ext <;> apply OrderCertificate.allFin <;> decide +kernel

/-- Every source relator holds on the defining permutation pair. -/
theorem permutation_words (i : Fin 13) : word generatorA generatorB i = 1 := by
  rw [← OrderCertificate.a_eq_generator, ← OrderCertificate.b_eq_generator]
  exact packed_words i

/-- The same relations in the subtype defining the actual HS carrier. -/
theorem carrier_words (i : Fin 13) :
    word generatorAElement generatorBElement i = 1 := by
  apply Subtype.ext
  change inclusion (word generatorAElement generatorBElement i) = 1
  rw [map_word]
  exact permutation_words i

/-- The canonical homomorphism from the abstract presentation to HS. -/
def toCarrier : Universal →* Carrier :=
  pairHom generatorAElement generatorBElement carrier_words

@[simp] theorem toCarrier_generator_false :
    toCarrier (generator false) = generatorAElement := pairHom_generator_false ..

@[simp] theorem toCarrier_generator_true :
    toCarrier (generator true) = generatorBElement := pairHom_generator_true ..

/-- The literal generators give surjectivity; no order comparison is used. -/
theorem toCarrier_surjective : Function.Surjective toCarrier := by
  apply MonoidHom.range_eq_top.mp
  exact eq_top_of_generators_mem _
    ⟨generator false, toCarrier_generator_false⟩
    ⟨generator true, toCarrier_generator_true⟩

/-- A bound on the abstract group, together with this actual surjection,
would establish the missing faithfulness. -/
theorem toCarrier_injective_of_card_le [Finite Universal]
    (h : Nat.card Universal ≤ Nat.card Carrier) : Function.Injective toCarrier :=
  (toCarrier_surjective.bijective_of_nat_card_le h).1

end Sporadic.LeechRelated.HS.AtlasPresentation
