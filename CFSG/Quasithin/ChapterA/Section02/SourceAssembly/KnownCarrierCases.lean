module
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.CarrierPartition
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.Complete
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.Complete
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly.Fi23Source
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Components.SemisimpleSource
/-!
# Full-carrier source cases in the simultaneous A.2 induction

The literal full known-simple catalogue is split into all source families.
Both Lie-characteristic families and all alternating branches are discharged.
The simple case retains only the actual Fi24 centralizer map; the quasisimple
and full semisimple cases additionally retain the actual McL comparison and
O'Nan compatible lift. These are concrete model producers, not family
classification premises. The nonsemisimple rank-two sieve remains separate.
Source: Aschbacher--Smith A.2.12--19, printed pp.36--41.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

theorem MinimalCounterexample.simple_false_of_fi24_section
    (h : MinimalCounterexample KnownSimple.IsKnownSimple G) [IsSimpleGroup G]
    (d24 : InvolutionCentralizerQuotientData _root_.Sporadic.Fischer.Fi24Prime.Carrier
      _root_.Sporadic.Fischer.Fi22.Carrier) : False := by
  rcases knownCarrier_source_partition (h.simple_knownCarrier inferInstance) with
    hc | ⟨n,hn,⟨e⟩⟩ | he | ho | hs
  · exact h.simple_not_cyclic inferInstance hc
  · exact h.simple_not_alternating inferInstance n e
  · exact EvenLie.not_minimalCounterexample_evenLieCarrier h he
  · exact OddLie.not_minimalCounterexample_oddLieCarrier h ho
  · obtain ⟨hna,hqt,hk,hfail⟩ := h.simple_case inferInstance
    obtain ⟨hb,hc⟩ := Sporadic.SourceAssembly.sporadic_caseI_of_fi24_section
      h.2 hqt hk hna hs d24
    rcases hfail with hn | ⟨hq,hn⟩
    · exact hn hb
    · exact hn (hc hq)

theorem CounterexampleToTheoremA.quasisimple_false_of_fi24_mcl_onan
    [IsQuasisimple G] {S : Type u} [Group S] [Finite S] {p : ℕ}
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (comparison : _root_.Sporadic.LeechRelated.McL.Carrier ≃*
      Atlas.Sporadic.McLaughlin.Model)
    (d24 : InvolutionCentralizerQuotientData _root_.Sporadic.Fischer.Fi24Prime.Carrier
      _root_.Sporadic.Fischer.Fi22.Carrier)
    (hlift : ∀ e : G ⧸ center G ≃* ONan.Model,
      ∃ F : ONan.Cover.linearSubgroup →* G,
        (Sporadic.SourceAssembly.projection e).comp F = ONan.Cover.projection) : False := by
  rcases knownCarrier_source_partition h.centralQuotient_knownSimple.2.2 with
    hc | ⟨n,hn,⟨e⟩⟩ | he | ho | hs
  · let : IsSimpleGroup (G ⧸ center G) := IsQuasisimple.simple
    let : Group.IsPerfect (G ⧸ center G) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center G))
    obtain ⟨q,hq,⟨e⟩⟩ := hc
    exact Group.IsPerfect.not_isMulCommutative (G ⧸ center G)
      ⟨⟨fun x y => e.injective (by simp only [map_mul]; exact mul_comm _ _)⟩⟩
  · exact EvenLie.caseII_alternating_of_source h ih.theoremA hn e
  · exact EvenLie.caseII_of_evenLieCarrier h ih.theoremA he
  · exact OddLie.caseII_of_oddLieCarrier h ih ho
  · exact Sporadic.SourceAssembly.sporadic_caseII_of_fi24_mcl_onan h ih hs
      comparison d24 hlift

theorem CounterexampleToTheoremA.semisimple_false_of_fi24_mcl_onan
    {S : Type u} [Group S] [Finite S] {p : ℕ}
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G) (hsemi : IsSemisimple G)
    (comparison : _root_.Sporadic.LeechRelated.McL.Carrier ≃*
      Atlas.Sporadic.McLaughlin.Model)
    (d24 : InvolutionCentralizerQuotientData _root_.Sporadic.Fischer.Fi24Prime.Carrier
      _root_.Sporadic.Fischer.Fi22.Carrier)
    (hlift : ∀ e : G ⧸ center G ≃* ONan.Model,
      ∃ F : ONan.Cover.linearSubgroup →* G,
        (Sporadic.SourceAssembly.projection e).comp F = ONan.Cover.projection) : False := by
  let : IsQuasisimple G := h.quasisimple_of_semisimple ih hsemi
  exact h.quasisimple_false_of_fi24_mcl_onan ih comparison d24 hlift
end CFSG.Quasithin.ChapterA.Section02
