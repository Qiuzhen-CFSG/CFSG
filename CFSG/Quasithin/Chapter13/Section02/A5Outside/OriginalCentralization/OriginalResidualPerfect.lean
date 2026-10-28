module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalNormality
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalRightSource
public import Theory.GroupTheory.PResidual.ConjugateGeneration
public import Theory.GroupTheory.PResidual.PerfectImage

/-!
# The whole residual of the original terminal H is perfect

The actual E.2.2 source supplies a perfect C-component generating H with
the original Sylow. The Sylow conjugates of that component generate the
literal two-residual. Thus perfectness belongs to the whole residual,
including the exchanged and diagram rows; no selected-factor identity or
rank-one quotient classification is assumed.

This is the perfectness input for the original whole-residual F.1.1
consumer. Source: Aschbacher--Smith E.2.2 and 5.1.10, pp.215--216,634.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}

/-- Actual generation greater than one makes the whole original residual
perfect, without identifying a selected factor with it. -/
theorem original_hstar_residual_perfect
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) :
    Group.IsPerfect (residual H) := by
  have hC : ∃ C : Subgroup H, C.IsCComponent ∧
      C ⊔ (T : Subgroup G).subgroupOf H = ⊤ := by
    rcases Global.right_source_cases d.hypothesis.qtke d.normalizes_L hH hgen with
      ⟨C,f,hC,_,hj,_,_⟩ | ⟨C,f,hC,_,hj,_,_,_⟩
    · exact ⟨C,hC,hj⟩
    · exact ⟨C,hC,hj⟩
  obtain ⟨C,hC,hjoin⟩ := hC
  let : Group.IsPerfect C := hC.perfect
  have hr := pResidual_eq_iSup_conjugates C ((T : Subgroup G).subgroupOf H)
    ((pResidual_eq_top_iff 2 C).mp (pResidual_eq_top_of_isPerfect 2))
    T.isPGroup'.comap_subtype hjoin
  let : Group.IsPerfect (pResidual 2 H) := by
    rw [hr]
    exact isPerfect_iSup_conjugates C ((T : Subgroup G).subgroupOf H)
  exact Group.IsPerfect.map H.subtype

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
