module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalNormalizedRankOneF11
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalResidualPerfect
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalTerminalPairExclusion

/-!
# Excluding the whole rank-one residual in the original terminal context

The actual normalized residual supplies F.1.1, with its two-core killed by
the original uniqueness over L T. E.2.2 proves that this same residual is
perfect. The original central line then contradicts the complete critical
pair analysis. No selected comparison or earlier 5.2.3 theorem is assumed.

The exchanged and diagram source rows still require the generated-core
argument for a proper selected factor.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}

/-- The original terminal normalized H has no rank-one model for the
literal quotient of its whole two-residual. -/
theorem original_terminal_residual_not_rankOne
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHC : H ≤ centralizer (V₁ : Set G))
    (hgen : 1 < ChapterE.generationParameter H)
    (hN : localBorel T L ≤ normalizer (residual H : Set G)) :
    ¬ ChapterF.Source.IsRankOneModel
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) := by
  intro hrank
  obtain ⟨A,B,c,r,hf,_⟩ := original_normalized_rankOne_hypothesisF11 d hH hgen hrank
    (by simpa only [localBorel_eq_map] using hN)
  exact original_terminal_pair_impossible d hH hHC (map_subtype_le _) hf
    (original_hstar_residual_perfect d hH hgen)
    (fun he => r.outside (by change residual H = ⊥ at he; rw [he]; exact bot_le))

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
