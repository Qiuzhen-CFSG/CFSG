module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalG2SourceExclusion
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalLinearComparison
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalSymplecticComparison
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairNativeSource

/-!
# Two original chosen modules exclude every genuine A₅ source pair

The actual F.1.1 hypotheses produce the native reduced comparison. Each
native endpoint geometry contradicts the original chosen orthogonal module;
the G₂ branch uses the Context at whichever original endpoint is short.
The full source subgroup S is arbitrary and remains unchanged.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source ChapterF.Source
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ K W W₁ W₂ W₃ S : Subgroup G}

/-- Genuine F.1.1 cannot join two factors carrying the original chosen
orthogonal A₅ modules. No comparison or classification premise is assumed. -/
theorem original_context_pair_not_hypothesisF11
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (h : HypothesisF11 ![L,K] S) : False := by
  have a : ∀ i, Nonempty ((![L,K] i ⧸ pCore 2 (![L,K] i)) ≃*
      alternatingGroup (Fin 5)) := by
    intro i
    fin_cases i
    · exact ⟨d.quotient⟩
    · exact ⟨e.quotient⟩
  rcases a5_pair_native_comparisons_from_source h a with hc | hc | hc
  · obtain ⟨F,hF,hfinite,hchar,n,hn,hcard,hc⟩ := hc
    rcases hc with ⟨b,⟨c⟩⟩ | ⟨b,⟨c⟩⟩
    · exact original_context_not_reduced_linear d h a F hcard hn b c
    · exact original_context_not_reduced_symplectic d h a F hcard hn b c
  · obtain ⟨b,⟨c⟩⟩ := hc
    exact original_pair_not_reduced_g2_of_source d e h (GaloisField 2 2) b c
  · obtain ⟨b,⟨c⟩⟩ := hc
    exact original_pair_not_reduced_g2_of_source e d h.swap (GaloisField 2 2) b c

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
