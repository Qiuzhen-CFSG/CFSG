module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalNormalizedRankOneExclusion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalRightBender

/-!
# The remaining original terminal source rows

The genuine E.2.2 dispatcher keeps the original generating C-component,
Sylow, overlap and quotient markings. Its single Bender row identifies
that component with the whole two-residual, whose literal rank-one quotient
has now been excluded. Only the exchanged and rank-two diagram rows remain.

These are source alternatives, not an assumed exhaustive amalgam catalogue.
Their proper-factor generated-core obligation remains separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source Chapter6.Source.RankOneGeneric
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}

/-- The actual terminal E.2.2 source has an exchanged component or a
diagram marking, with the original whole kernels and Sylow retained. -/
theorem original_terminal_right_source_cases
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHC : H ≤ centralizer (V₁ : Set G))
    (hgen : 1 < ChapterE.generationParameter H)
    (hN : localBorel T L ≤ normalizer (residual H : Set G)) :
    (∃ (C : Subgroup H) (f : ℕ), C.IsCComponent ∧
      IsQuasisimple (C ⧸ pCore 2 C) ∧
      C ⊔ (T : Subgroup G).subgroupOf H = ⊤ ∧ 1 < f ∧
      ExchangedClauses ((normalizer (L : Set G)).subgroupOf H) C
        ((T : Subgroup G).subgroupOf H) ∧
      ExchangedModel ((normalizer (L : Set G)).subgroupOf H) C f) ∨
    Global.RightDiagramSource T L H := by
  rcases Global.right_source_cases d.hypothesis.qtke d.normalizes_L hH hgen with
    ⟨C,f,hC,hqs,hjoin,hf,hcases⟩ | hdiagram
  · rcases hcases with hexchanged | hbender
    · exact Or.inl ⟨C,f,hC,hqs,hjoin,hf,hexchanged.1,hexchanged.2⟩
    · exfalso
      have hO : pCore 2 H ≤ sourceKernel ((normalizer (L : Set G)).subgroupOf H) := by
        apply normal_le_normalCore.mpr
        exact (pCore_isPGroup.le_sylow_of_normal (T.subtype hH.1.1.2)).trans
          (comap_mono d.normalizes_L)
      have hrank := Prime.single_bender_component_quotient hC hqs hO
        hbender.1 hbender.2
      have he : C = pResidual 2 H :=
        BenderHall.SingleClauses.component_eq_residual
          (S := T.subtype hH.1.1.2) hbender.1 hC
      apply original_terminal_residual_not_rankOne d hH hHC hgen hN
      rwa [he] at hrank
  · exact Or.inr hdiagram

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
