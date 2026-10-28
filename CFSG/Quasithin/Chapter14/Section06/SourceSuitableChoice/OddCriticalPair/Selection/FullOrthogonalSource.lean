module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Selection.ReturnedGeometry
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Selection.FullDenominatorSource
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.OrthogonalSource.Recognition
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Coordinates.Source

/-!
# The full-denominator orthogonal branch of original 14.6.13

The returned endpoint acts through a noncentral commutator line. Its
transvections force the actual moved section to have dimension four and
preserve both exchanged planes. Faithfulness on the moved space ensures
that one plane is moved. Conjugation by the original factor exchanger, when
needed, marks the first plane without changing H, M or Mc. Recognition then
supplies the actual orthogonal coordinates and the marked critical pair.

The terminal consumer discharges the critical-pair premise of the orthogonal
suitable-element construction in this branch. The exchanged factors and
14.6.14--16 inputs remain with qt-e-14612-singleton and
qt-e-suitable-odd-normalizer, discharged by qt-e-suitable-existence.
The strict-denominator alternative remains a separate source obligation.

Source: Aschbacher--Smith, 14.6.13, printed p.1031, and 14.6.17,
printed pp.1035--1036.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
open OddNormalizer OrthogonalSource SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter13.Section08 Chapter13.Section08.CriticalGeometry
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

/-- The full-denominator returned line gives the complete marked first
alternative of 14.6.13, with the original first factor and one actual g. -/
theorem source_rankTwo_orthogonal_of_returned_line
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (l : ReturnedLineAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    (hout : l.g ∉ Mc) :
    p = 3 ∧ ∃ o : SourceOrthogonalFourAction H (conjugateSpanBy (localModule T M) H)
      (centralInvolutions T) (H.pCoreIn 2),
      ∃ c : SourceOrthogonalCriticalPair o Mc, o.plane c.first = firstSupport a H1 := by
  let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  have hHMc : H ≤ Mc := by
    have hHZ := (Section02.source_lemma_14_2_3 hG T hempty hM hunique hmany hcard e H hH.1 hH.2).1
    have hm : Mc ∈ maximalTwoLocalOvergroups H := hHZ ▸ Set.mem_singleton _
    exact hm.2
  have hf (g : H ⧸ pCore 2 H)
      (hfix : ∀ v ∈ subspaceCommutator a.representation ⊤ ⊤, a.representation g v = v) : g = 1 := by
    apply source_rankTwo_residual_moved_faithful hG T hempty hM hunique hmany hcard e hab H hH a g
    rw [← source_rankTwo_whole_moved_eq_residual hG T hempty hM hunique hmany hcard e hab H hH a]
    exact hfix
  obtain ⟨hp,⟨c⟩⟩ := returned_line_four_geometry a h.H_centralizes h.point_card
    (T : Subgroup G) hH.1.2 p H0 H1 H2 d Mc hHMc l hout hf
  obtain ⟨_,o,i,hi⟩ := source_rankFour_orthogonal_action hG T hempty hM hunique hmany hcard e hab
    H hH a p H0 H1 H2 d c.dimension
  refine ⟨hp,o,⟨i,c.g,c.outside,?_,c.reverse,?_⟩,hi⟩
  · simpa only [hi] using c.normalizes
  · simpa only [hi] using c.noncentral

/-- Original 14.6.13(1) for an actual critical pair with full right
denominator; the endpoint construction discharges all returned-line premises. -/
theorem source_rankTwo_orthogonal_of_full
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (c : CriticalPair (sourceResidual M Mc) (T : Subgroup G) H (localModule T M))
    (hfull : Source.Dgamma (c.Ugamma (localModule T M))
      (conjugateSpanBy (localModule T M) H) (centralInvolutions T) = c.Ugamma (localModule T M)) :
    p = 3 ∧ ∃ o : SourceOrthogonalFourAction H (conjugateSpanBy (localModule T M) H)
      (centralInvolutions T) (H.pCoreIn 2),
      ∃ critical : SourceOrthogonalCriticalPair o Mc,
        o.plane critical.first = firstSupport a H1 := by
  obtain ⟨_,_,l,_,hout⟩ := source_rankTwo_returned_line_of_full hG T hempty hM hunique hmany hcard e hab H hH c hfull
  exact source_rankTwo_orthogonal_of_returned_line hG T hempty hM hunique hmany hcard e hab
    H hH a p H0 H1 H2 d l hout

/-- The original endpoint selection with the full-denominator branch discharged.
The remaining selected endpoint is genuinely strict and quadratic; proving its
factor geometry remains with this source assembly. -/
theorem source_rankTwo_marked_or_strict
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
    letI : IsElementaryAbelian 2 D.UH :=
      ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    (p = 3 ∧ ∃ o : SourceOrthogonalFourAction H D.UH D.V₁ (H.pCoreIn 2),
      ∃ c : SourceOrthogonalCriticalPair o Mc, o.plane c.first = firstSupport a H1) ∨
      (∃ c : SelectedQuadraticEndpoint h a, c.endpoint.representative ∉ Mc) := by
  rcases source_rankTwo_endpoint_selection hG T hempty hM hunique hmany hcard e hab H hH a with
    ⟨l,hout⟩ | hs
  · exact Or.inl (source_rankTwo_orthogonal_of_returned_line hG T hempty hM hunique hmany hcard
      e hab H hH a p H0 H1 H2 d l hout)
  · exact Or.inr hs

/-- The suitable-element terminal witness in the full-denominator branch.
The original earlier-source factors, fitting and normalizer conclusions are
explicit; no orthogonal-action, critical-pair, rank or coordinate premise remains. -/
theorem source_terminal_witness_of_full_endpoint
    (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (c : CriticalPair (sourceResidual M Mc) (T : Subgroup G) H (localModule T M))
    (hfull : Source.Dgamma (c.Ugamma (localModule T M))
      (conjugateSpanBy (localModule T M) H) (centralInvolutions T) = c.Ugamma (localModule T M))
    (hF : residual H ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc)
    (hN : Mc ⊓ normalizer
      (((T : Subgroup G) ⊓ normalizer (H1 : Set G) : Subgroup G) : Set G) = (T : Subgroup G)) :
    SourceTerminalWitness hG T hempty hM hunique hmany hcard e hab := by
  obtain ⟨_,o,critical,hi⟩ := source_rankTwo_orthogonal_of_full hG T hempty hM hunique hmany hcard e hab
    H hH a 3 H0 H1 H2 d c hfull
  exact source_terminal_witness_of_marked_orthogonal_pair hG T hempty hM hunique hmany hcard e hab
    H hH o critical a H0 H1 H2 d hi hF hN

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
