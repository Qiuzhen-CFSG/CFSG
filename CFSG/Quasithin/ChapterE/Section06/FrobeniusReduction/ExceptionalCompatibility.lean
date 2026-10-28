module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.ONan
public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction.ExceptionalCompatibility

/-!
# The exceptional compatibility step in the literal E.6 action

The original regular cyclic section gives Input for the faithful automizer
representation of V. Applying the geometric compatibility theorem turns
its actual exceptional candidate B into FactorSeed with that same B.
The finite two-actor dimension bound remains the one independent source
premise, owned by the O'Nan pair theorem. No global commutation is assumed.

Source: Aschbacher–Smith E.6.24, printed p.255.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
open Subgroup Representation.BinaryOffender
open Representation.RegularCyclicNormalClosure
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- The E.6 automizer consumer, retaining the same exceptional factor. -/
theorem RegularCyclicSection.exceptional_factorSeed_of_pair_bound
    {𝒦 : GroupClass} {T : Sylow 2 G} {M V U X : Subgroup G}
    [IsElementaryAbelian 2 V]
    (hE : HypothesisE61 𝒦 T M V) (hU : U ∈ obstructionFamily M V)
    (h : RegularCyclicSection M V U X)
    (hlower : 1 < subgroupCorank V U) (hupper : subgroupCorank V U < localM V)
    {B : Subgroup (Automizer V)}
    (hB : ExceptionalCandidate (automizerRepresentation V) (inducedAutomizer V X) B)
    (hpair : ∀ a b : Automizer V,
      (¬ ∀ c ∈ (inducedAutomizer V X).map (MulAut.conj a).toMonoidHom,
        ∀ d ∈ (inducedAutomizer V X).map (MulAut.conj b).toMonoidHom, Commute c d) →
      Module.finrank (ZMod 2)
        ↥(displacementSpan (automizerRepresentation V)
            ((inducedAutomizer V X).map (MulAut.conj a).toMonoidHom) ⊤ ⊔
          displacementSpan (automizerRepresentation V)
            ((inducedAutomizer V X).map (MulAut.conj b).toMonoidHom) ⊤) ≤ 3) :
    FactorSeed (W := Additive V) (automizerRepresentation V) (inducedAutomizer V X) B :=
  hB.factorSeed_of_pair_bound (h.toInput hE hU hlower hupper) hpair

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
