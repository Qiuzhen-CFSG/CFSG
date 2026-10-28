module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersTwoSourceModule
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisCentralizersTwoSourceComponents
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalComponentProperNatural

/-!
# LocalAnalysisCentralizersTwoSourceModule at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisCentralizersTwoSourceModule`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Subgroup Theory.GroupTheory Section02 BinarySevenCode BinaryPermutation

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

variable {E : S.NaturalCoordinates}

namespace SylowNormalizer.Points

variable (P : Points E)

theorem two_section_fixes_moved_of_normalizes_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hn : ChapterA.Section04.twoSectionCentralizer P.five
      (centralizer ({(P.two : G)} : Set G)) ≤ normalizer ((⁅V,P.five⁆ : Subgroup G) : Set G)) :
    ChapterA.Section04.twoSectionCentralizer P.five
      (centralizer ({(P.two : G)} : Set G)) ≤ centralizer ((⁅V,P.five⁆ : Subgroup G) : Set G) := by
  let d := P.five_moved_natural
  refine d.centralizes_of_faithful_trivial_commutant ?_ _ hn ?_
  · intro f hf
    apply LinearEquiv.ext
    intro w
    apply FiveCentralExtension.core_commuting_eq_id f.toLinearMap ?_ f.injective w
    intro g hg v
    obtain ⟨k,hk⟩ := (P.fiveCoreEquiv.surjective.comp
      (QuotientGroup.mk'_surjective (pCore 2 P.five))) ⟨g,hg⟩
    have he := hf k v
    change f (alternatingCoreRepresentation (Fin 5)
      (P.fiveCoreEquiv (QuotientGroup.mk' _ k)) v) =
      alternatingCoreRepresentation (Fin 5) (P.fiveCoreEquiv (QuotientGroup.mk' _ k)) (f v) at he
    change P.fiveCoreEquiv (QuotientGroup.mk' (pCore 2 P.five) k) = ⟨g,hg⟩ at hk
    rw [hk] at he
    exact he
  · have hcore : P.five.pCoreIn 2 ≤ (P.five ⊔ (T : Subgroup G)).pCoreIn 2 :=
      pCoreIn_mono_of_normalizes le_sup_left (sup_le P.five.le_normalizer
        (pointResidual_normalized S.chosen.sylow_normalizes_component P.two_central))
    have hfix : P.five.pCoreIn 2 ≤ centralizer ((⁅V,P.five⁆ : Subgroup G) : Set G) := by
      apply le_centralizer_iff.mp
      apply (P.five_moved_le_core_omega_at structural).trans
      exact (fun x hx => centralizer_le hcore ((mem_omegaCenterIn_iff _ _).mp hx).2.1)
    apply le_trans ?_ hfix
    rw [commutator_comm]
    exact ((ChapterA.Section04.le_twoSectionCentralizer_iff _ _ _).mp le_rfl).2.2

end SylowNormalizer.Points

namespace PointCentralizers

def localAnalysis_of_quasisimple_models_and_moved_normalized_at
    (P : SylowNormalizer.Points E)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates)
    (models : ∀ Y : Subgroup G, Y ∈ Chapter1.LStar G (T : Subgroup G) →
      P.five < Y → IsQuasisimple (Y ⧸ pCore 2 Y) →
      ∃ W : Subgroup G, Nonempty (Setup T Y W))
    (hn : ChapterA.Section04.twoSectionCentralizer P.five
      (centralizer ({(P.two : G)} : Set G)) ≤ normalizer ((⁅V,P.five⁆ : Subgroup G) : Set G)) :
    S.LocalAnalysis :=
  localAnalysis_of_twoInput_at P structural
    ⟨P.two_normalizes_of_quasisimple_maximal_models_at structural escape natural models,
      P.two_section_fixes_moved_of_normalizes_at structural hn⟩

end PointCentralizers

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Subgroup Theory.GroupTheory Section02

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

variable {E : S.NaturalCoordinates}

namespace SylowNormalizer.Points

variable (P : Points E)

end SylowNormalizer.Points

namespace PointCentralizers

def localAnalysis_of_quasisimple_models_and_omegaSpan_at
    (P : SylowNormalizer.Points E)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates)
    (models : ∀ Y : Subgroup G, Y ∈ Chapter1.LStar G (T : Subgroup G) →
      P.five < Y → IsQuasisimple (Y ⧸ pCore 2 Y) →
      ∃ W : Subgroup G, Nonempty (Setup T Y W))
    (hm : ⁅P.twoOmegaSpan,P.five⁆ = ⁅V,P.five⁆) : S.LocalAnalysis := by
  have hK := P.two_normalizes_of_quasisimple_maximal_models_at structural escape natural models
  exact localAnalysis_of_quasisimple_models_and_moved_normalized_at P structural escape natural models
    ((ChapterA.Section04.twoSectionCentralizer_le _ _).trans
      (P.two_moved_normalized_of_omegaSpan_commutator hK hm))

end PointCentralizers

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

