module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearResidualEmbeddingJankoFourExclusion
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearResidualEmbeddingJankoFour

/-!
# The proper-containing-component exclusion for the exceptional residual

The checked containing catalogue leaves only J₂, M₂₃ and J₄. The first two
are excluded by the existing literal quotient and diagram arguments. The
normal J₄ quotient supplies a surjective realization retaining the full
Sylow actor and the original graph action; the native J₄ theorem excludes it.
This discharges the exact shared embedding interface from5.1.12 and gives
unconditional maximality of the actual H-star residual. Nonfaithfulness is
assembled with the proved FSU exclusion in the Chapter12 extension.

The `import all` intentionally reuses the private field-marking bridge in
the sibling JankoFour module, without changing its existing public boundary.
Source: Aschbacher–Smith A.3.12,1.2.4,5.1.12 and5.1.14(1),
printed pp.47–48,505,635 and638 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

/-- The graph actor is incompatible with a proper normal containing component.
All three exceptional containing rows are discharged on their literal quotients. -/
theorem linearFourEmbeddingExclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) : LinearFourEmbeddingExclusion G := by
  intro T K hK hn Y hY C hC hnC hKC hne hg
  have hKY : K ≤ Y := hKC.trans (map_subtype_le _)
  rcases linear_four_containing_component_eq_or_janko hG T hK hn hg hY C hC hnC hKC
    with he | hJ2 | hJ4
  · exact hne he
  · have hlinear : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4 := by
      obtain ⟨F,hF,hfin,hcard,e,_⟩ := hg
      exact ⟨F,hF,hfin,hcard,⟨e⟩⟩
    exact linear_four_quotient_excludes_jankoTwo_container hKY C hKC hlinear hJ2
  · obtain ⟨e⟩ := hJ4
    let := hnC
    let S := T.subtype hY.2
    let B := K.subgroupOf Y
    have hl : B ∈ localCComponents S :=
      ((Chapter1.mem_LIn_iff_subgroupOf hY.2 hKY).mp ⟨hKY,hK⟩).1
    have hnB : (S : Subgroup Y) ≤ normalizer (B : Set Y) := by
      intro s hs
      apply mem_normalizer_iff.mpr
      intro b
      exact mem_normalizer_iff.mp (hn hs) (b : G)
    have hBC : B ≤ C := by
      intro b hb
      obtain ⟨c,hc,he⟩ := hKC hb
      exact Y.subtype_injective he ▸ hc
    obtain ⟨f,P,_,_,_,hBP,hNP,hgraph,_⟩ := exists_jankoFour_graph_section S B C
      hl hnB hBC (hg.subgroupOf hY.2 hKY) e
    exact jankoFour_no_graph_section P (B.map f) hBP hNP hgraph.exceptionalModel hgraph

/-- Original5.1.14(1)'s maximality assertion for the embedded two-residual. -/
theorem linear_residual_maximal
    {T : Sylow 2 G} {M H : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    residual H ∈ Chapter1.LStar G (T : Subgroup G) :=
  linear_residual_maximal_of_embedding_exclusion hG hTM hH hlinear
    (linearFourEmbeddingExclusion hG)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
