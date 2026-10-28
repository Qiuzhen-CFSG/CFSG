module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalSmallGeneration
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalSmallGenerationTorus

/-!
# Assembly of the small-Cartan consequence of original 5.1.6

The actual Hall Cartan has order 2ⁿ−1. Once the earlier module and
field-action reduction is supplied, the central-omega and local-control
arguments construct exactly the three factors required by 5.2.2.
The final export separates the two still-unproved source branches:
evenness of n, and the higher-degree torus geometry with evenness explicit.
Their premises are discharged here only conditionally on those producers.

Source: Aschbacher--Smith, 5.1.6 and 5.2.2, printed pp.631--633,647.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The n=2 and n=4 branches of the small-Cartan source reduction are
available directly from the literal Hall order.  Only the n=8 row needs the
higher-field producer used by the general assembly below. -/
theorem Input.cartanSmallGeneration_of_degree_two_or_four
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hn : n = 2 ∨ n = 4) :
    CartanSmallGeneration A H n := by
  exact _root_.CFSG.Quasithin.Chapter6.Source.RankOneGeneric.cartanSmallGeneration_of_degree_two_or_four hH
      (c.left_card h.linear h.sylow_normalizes) hn

/-- An actual Input/CartanPair consumer: the Hall-order premise is
proved through the original quotient, and only the earlier field reduction
remains explicit. -/
theorem Input.cartanSmallGeneration_of_fieldReduction
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B)
    (hr : CartanFieldReduction T H A n) (hc : CartanLocalControl A H)
    (hzero : (A ⊔ H).pCoreIn 2 = ⊥) : CartanSmallGeneration A H n :=
  CFSG.Quasithin.Chapter6.Source.RankOneGeneric.cartanSmallGeneration_of_fieldReduction
    h hH hr hc hzero
    (c.left_card h.linear h.sylow_normalizes)

/-- Conditional source assembly; the module and field-action reduction
of original 5.1.6 is still a genuine proof obligation. -/
theorem sourceCartanSmallGeneration_of_fieldReduction {κ : GroupClass.{u}}
    (hfield : SourceCartanFieldReduction κ G) : SourceCartanSmallGeneration κ G := by
  intro T L W n h H hH hgen A B c hc hzero
  exact h.cartanSmallGeneration_of_fieldReduction hH c
    (hfield T L W n h H hH hgen A B c hzero) hc hzero

/-- Final assembly boundary for the independent original-source proofs.
This does not assert that either source obligation has been proved. -/
theorem sourceCartanSmallGeneration_of_even_and_higher {κ : GroupClass.{u}}
    (heven : SourceCartanEvenExponent κ G)
    (hhigher : SourceCartanHigherFieldReduction κ G) :
    SourceCartanSmallGeneration κ G :=
  sourceCartanSmallGeneration_of_fieldReduction
    (sourceCartanFieldReduction_of_even_and_higher heven hhigher)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
