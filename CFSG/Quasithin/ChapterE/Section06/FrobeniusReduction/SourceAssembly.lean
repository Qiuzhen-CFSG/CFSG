module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.ExceptionalCompatibility
public import CFSG.Quasithin.RegularCyclicNormalClosure.FactorConstruction.SourceAssembly

/-!
# Literal E.6 regular-cyclic factor seed

The original E.6.11 cyclic section supplies `Input` through
`RegularCyclicSection.toInput`. The source assembly then produces a factor
seed for the actual automizer subgroup and actual induced cyclic actor. This
wrapper keeps the original group, quotient action, and corank hypotheses in
the consumer signature; it adds no TI or fixed-space premise.

Source: Aschbacher--Smith E.6.24, printed p.255, using Aschbacher 10.4.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction

open Subgroup Representation.BinaryOffender
open Representation.RegularCyclicNormalClosure
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- The literal E.6 factor-seed consumer for an actual regular cyclic section. -/
theorem RegularCyclicSection.exists_factorSeed_of_input
    {𝒦 : GroupClass} {T : Sylow 2 G} {M V U X : Subgroup G}
    [IsElementaryAbelian 2 V]
    (hE : HypothesisE61 𝒦 T M V) (hU : U ∈ obstructionFamily M V)
    (h : RegularCyclicSection M V U X)
    (hlower : 1 < subgroupCorank V U) (hupper : subgroupCorank V U < localM V) :
    ∃ B : Subgroup (Automizer V),
      FactorSeed (W := Additive V) (automizerRepresentation V)
        (inducedAutomizer V X) B := by
  exact CFSG.Quasithin.RegularCyclicNormalClosure.exists_factorSeed_of_input
    (h.toInput hE hU hlower hupper)

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
