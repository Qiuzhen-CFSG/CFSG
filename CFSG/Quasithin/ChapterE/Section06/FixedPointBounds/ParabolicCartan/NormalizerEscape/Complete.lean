module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape.Bender
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape.EmbeddedCases
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape.Symplectic
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape.Exchanged
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape.LinearThree

/-!
# Full-Hall normalizer generation in the original source

The actual embedded SQTK group yields the E.2.2 component and its marked
binary models. Each model row gives escape for the prescribed subgroup of the
full odd Hall subgroup, so maximality yields the original generation conclusion.
Source: Aschbacher–Smith 4.4.13(1), printed pp.623–624.
-/
public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape
open MarkedModels ChapterB
universe u

/-- Source 4.4.13(1) for the known-simple class, retaining the actual
embedding, full odd Hall subgroup and prescribed elementary subgroup. -/
theorem source4413One_knownSimple
    (G : Type u) [Group G] [Finite G] : Source4413One KnownSimple.IsKnownSimple G := by
  intro hG X hgroup hfin emb hemb hcore hn S hP Y hYM hHall p hp A hA hAY hperm
  have hX := sqtk_of_embedding_with_nontrivial_twoCore hG emb hemb hcore
  obtain ⟨K,n,hK,hqK,hgen,hf,hcases⟩ :=
    source_embedded_generating_binary_cases_knownSimple hG emb hemb hcore S hP hn
  cases hcases with
  | exchanged hc hm =>
    have hquot : IsStronglyQuasithin (X ⧸ sourceKernel (minimalParabolicMax S hP)) := by
      have hJ : IsPGroup 2 (sourceKernel (minimalParabolicMax S hP)) := by
        rw [hc.kernel_eq]
        exact pCore_isPGroup
      exact (Structure.sqtk_two_quotient hX _ hJ).stronglyQuasithin
    exact exchanged_original_generation S hP K hK hc hm hgen.symm hquot Y hYM hHall p hp A hA hAY
  | bender hc hm =>
    exact bender_original_generation S hP K hK hqK hc hm Y hYM hHall p hp A hA hAY
  | diagram hc hm =>
    rcases hm with ⟨F,hfield,hfinite,hchar,_,hF,e,he,hmove⟩ |
      ⟨F,hfield,hfinite,hchar,_,hF,e,he,hmove⟩
    · let := hfield
      let := hfinite
      let := hchar
      exact linear_original_generation hf hF S hP K hK hqK hc e he hmove
        Y hYM hHall p hp A hA hAY hperm
    · let := hfield
      let := hfinite
      let := hchar
      exact symplectic_original_generation S hP K hK hc hf hF e he hmove
        Y hYM hHall p hp A hA hAY hperm

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape
