module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowResidualsPreliminaries
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisNormalizer

/-!
# LocalAnalysisSylowResidualsPreliminaries at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisSylowResidualsPreliminaries`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

variable {E : S.NaturalCoordinates}

namespace Setup.NaturalCoordinates

end Setup.NaturalCoordinates

namespace SylowNormalizer.Points

variable (P : Points E)

theorem fixed_centralizer_le_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {c : G} (hc : c ∈ P.fixed) (hne : c ≠ 1) :
    centralizer ({c} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨N, hCN, hN⟩ := Finite.exists_le_maximal
    (isTwoLocal_involution_centralizer (P.fixed_order_two hc hne))
  have he := (S.hypothesis.source_normalizer_maximal_unique_at structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2 N hN
      ((sup_le (P.fixed_component_le hc) (P.fixed_sylow_le hc)).trans hCN)
  exact he ▸ hCN

theorem fixed_component_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    {c : G} (hc : c ∈ P.fixed) (hne : c ≠ 1) :
    (L.subgroupOf (centralizer ({c} : Set G))).IsCComponent := by
  exact (S.hypothesis.source_normalizer_component_at structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).subgroupOf_of_le
      (P.fixed_component_le hc) (P.fixed_centralizer_le_at structural hc hne)

end SylowNormalizer.Points

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

