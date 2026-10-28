module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Alternatives.Source
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Alternatives.RankEight

/-!
# Terminal assembly after excluding the swapping endpoint

The source-exact alternatives of 14.6.13 give either the marked orthogonal
critical pair or a rank-eight endpoint with both point containments. The
separately constructed relative Sylow placement and suitable point exclude
the latter using the 14.6.14--16 conclusions. The surviving marked pair feeds
the complete parabolic, residual-coordinate, crossing and module-rank proofs.

Only the earlier exchanged factors, fitting containment in Mc, and normalizer
equality remain explicit. Their final discharge belongs to
qt-e-suitable-existence. No geometric or dimension premise remains here.

Source: Aschbacher--Smith 14.6.13 and 14.6.17, printed pp.1031--1036.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
open OddNormalizer OrthogonalSource SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter13.Section08 Chapter13.Section08.SourceCompletion Chapter13.Section08.CriticalGeometry
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
include hG hempty hM hunique hmany hcard e hab hH

/-- The original orthogonal critical pair after the genuine earlier
14.6.14--16 conclusions. There is no remaining swapping or rank premise. -/
theorem source_rankTwo_orthogonal_pair
    (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (hF : residual H ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc)
    (hN : Mc ⊓ normalizer
      (((T : Subgroup G) ⊓ normalizer (H1 : Set G) : Subgroup G) : Set G) = (T : Subgroup G)) :
    ∃ o : SourceOrthogonalFourAction H (conjugateSpanBy (localModule T M) H)
      (centralInvolutions T) (H.pCoreIn 2),
      ∃ critical : SourceOrthogonalCriticalPair o Mc,
        o.plane critical.first = firstSupport a H1 := by
  rcases source_critical_alternatives hG T hempty hM hunique hmany hcard e hab
      H hH a 3 H0 H1 H2 d with ⟨_,o,critical,hi⟩ | ⟨_,he⟩
  · exact ⟨o,critical,hi⟩
  · exact False.elim (source_rankEight_impossible
      hG T hempty hM hunique hmany hcard e hab H hH a H0 H1 H2 d hF hN he)

/-- Choose the suitable vector and construct its complete literal terminal
geometry from the unchanged rank-two hypotheses and earlier source inputs. -/
theorem source_terminal_witness_of_exchanged_factors
    (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (hF : residual H ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc)
    (hN : Mc ⊓ normalizer
      (((T : Subgroup G) ⊓ normalizer (H1 : Set G) : Subgroup G) : Set G) = (T : Subgroup G)) :
    SourceTerminalWitness hG T hempty hM hunique hmany hcard e hab := by
  obtain ⟨o,critical,hi⟩ := source_rankTwo_orthogonal_pair hG T hempty hM hunique hmany hcard e hab
    H hH a H0 H1 H2 d hF hN
  exact source_terminal_witness_of_marked_orthogonal_pair hG T hempty hM hunique hmany hcard e hab
    H hH o critical a H0 H1 H2 d hi hF hN

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
