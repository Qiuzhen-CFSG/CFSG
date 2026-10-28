module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.NormalizedResidualF11
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalSourcePairExclusion

/-!
# The original normalized residual branch is impossible

The compatible Cartans construct F.1.1 at the actual source intersection.
The two original chosen modules then exclude the resulting source pair.
No global model alternative or earlier 5.2.3 classifier is needed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H W W₁ W₂ W₃ : Subgroup G}

/-- With both actual chosen modules present, the left Borel cannot normalize
the full residual of a nonsmall outside H-star member. -/
theorem original_residual_borel_not_normalizes
    (d : Context T L V V₁ V₂ V₃)
    (e : Context T (residual H) W W₁ W₂ W₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hm : Nonempty (((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃*
      alternatingGroup (Fin 5))) :
    ¬ (normalizer (((T : Subgroup G).subgroupOf L) : Set L)).map L.subtype ≤
      normalizer (residual H : Set G) := by
  intro hN
  obtain ⟨A,B,c,r,hF11,_⟩ := original_normalized_residual_hypothesisF11 d hH hgen hm hN
  exact original_context_pair_not_hypothesisF11 d e hF11

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
