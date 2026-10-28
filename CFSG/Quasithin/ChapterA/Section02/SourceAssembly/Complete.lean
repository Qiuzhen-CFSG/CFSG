module
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Fi24Only
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi24Centralizer.SourceSection
/-!
# The original simultaneous A.2.1--3 classification

The literal Fi24 involution-centralizer section supplies the final concrete
source input to simultaneous induction. Thus every finite group satisfies the
original Theorems A, B and C for the complete known-simple carrier catalogue.
All family, proper-section and model comparison inputs are discharged.
Source: Aschbacher--Smith A.2.1--3 and A.2.8--19, printed pp.33--41.
-/
public section
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

theorem theoremsABC_knownSimple : TheoremsABC KnownSimple.IsKnownSimple G := by
  obtain ⟨t,L,f,ht,hL,hf⟩ :=
    _root_.Sporadic.Fischer.Fi24Prime.CentralizerSection.exists_source_section
  exact theoremsABC_of_fi24_source ⟨t,ht,L,hL,f,hf⟩

theorem theoremA_knownSimple : TheoremA KnownSimple.IsKnownSimple G :=
  (theoremsABC_knownSimple (G := G)).1

theorem theoremB_knownSimple : TheoremB KnownSimple.IsKnownSimple G :=
  (theoremsABC_knownSimple (G := G)).2.1

theorem theoremC_knownSimple : TheoremC KnownSimple.IsKnownSimple G :=
  (theoremsABC_knownSimple (G := G)).2.2
end CFSG.Quasithin.ChapterA.Section02
