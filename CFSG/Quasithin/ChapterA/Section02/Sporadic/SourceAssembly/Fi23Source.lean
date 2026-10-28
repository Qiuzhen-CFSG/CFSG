module
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly.FischerSymplectic
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.SourceSection
/-!
# The original Fi23 source branches

The actual involution-centralizer quotient removes the Fi23 model premise
from both simple and central-cover source consumers. The remaining sporadic
assembly retains only Fi24's map, the McL comparison and the O'Nan lift.
Source: Aschbacher--Smith A.2.19, printed pp.40--41.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly
universe u
variable {G : Type u} [Group G] [Finite G]

noncomputable def fi23_source_data :
    InvolutionCentralizerQuotientData _root_.Sporadic.Fischer.Fi23.Carrier
      _root_.Sporadic.Fischer.Fi22.Carrier := Classical.choice (by
  obtain ⟨t,L,f,ht,hL,hf⟩ :=
    _root_.Sporadic.Fischer.Fi23.CentralizerSection.exists_source_section
  exact ⟨⟨t,ht,L,hL,f,hf⟩⟩)

theorem cover_fi23 [IsQuasisimple G]
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (e : G ⧸ center G ≃* _root_.Sporadic.Fischer.Fi23.Carrier) : False :=
  cover_fischer_of_source_data ih hG hK e fi23_source_data

theorem simple_fi23 [IsSimpleGroup G]
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (hna : ¬ IsMulCommutative G)
    (e : G ≃* _root_.Sporadic.Fischer.Fi23.Carrier) : False :=
  simple_fischer_of_source_data ih hG hK hna e fi23_source_data

theorem sporadic_caseI_of_fi24_section [IsSimpleGroup G]
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hG : IsQuasithin G) (hK : IsKGroup KnownSimple.IsKnownSimple G)
    (hna : ¬ IsMulCommutative G) (hspor : KnownSimple.IsSporadicCarrier G)
    (d24 : InvolutionCentralizerQuotientData _root_.Sporadic.Fischer.Fi24Prime.Carrier
      _root_.Sporadic.Fischer.Fi22.Carrier) :
    IsTheoremBModel G ∧ (IsStronglyQuasithin G → IsTheoremCModel G) :=
  sporadic_caseI_of_fischer_sections ih hG hK hna hspor fi23_source_data d24

theorem sporadic_caseII_of_fi24_mcl_onan [IsQuasisimple G]
    {S : Type u} [Group S] [Finite S] {p : ℕ}
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hspor : KnownSimple.IsSporadicCarrier (G ⧸ center G))
    (comparison : _root_.Sporadic.LeechRelated.McL.Carrier ≃*
      Atlas.Sporadic.McLaughlin.Model)
    (d24 : InvolutionCentralizerQuotientData _root_.Sporadic.Fischer.Fi24Prime.Carrier
      _root_.Sporadic.Fischer.Fi22.Carrier)
    (hlift : ∀ e : G ⧸ center G ≃* ONan.Model,
      ∃ F : ONan.Cover.linearSubgroup →* G, (projection e).comp F = ONan.Cover.projection) :
    False :=
  sporadic_caseII_of_remaining_model_inputs h ih hspor comparison fi23_source_data d24 hlift

end CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly
