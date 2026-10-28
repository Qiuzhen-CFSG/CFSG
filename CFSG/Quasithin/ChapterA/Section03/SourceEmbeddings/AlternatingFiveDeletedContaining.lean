module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuasisimpleContaining
public import CFSG.Quasithin.ChapterC.Section01.LocalCoreDisplacement
public import Theory.ElementaryAbelian.PrimeRankCard

/-!
# Quasisimple containers of a deleted alternating-five block

The block's elementary moved layer has order sixteen and hence two-rank
four. The noncentral-Fitting alternatives in the actual SQTK structure
 theorem have two-rank one, so every containing C-component is quasisimple.
The known-simple catalogue then gives the literal simple or triple-cover
carrier. No odd-core vanishing is passed through a two-group quotient.

Source: Aschbacher–Smith A.3.6 and the surviving-block case of 10.2.1,
printed pp.43–44 and743.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- A surviving deleted-five layer excludes every nonquasisimple containing component. -/
theorem alternatingFive_containing_component_quasisimple
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    {B L : Subgroup G} (hL : L.IsCComponent) (hBL : B ≤ L)
    (hB : IsAlternatingBlock B 5) : IsQuasisimple L := by
  let := hB.2.1.elementary
  have hu : primeRank 2 (blockU B) = 4 := by
    rw [←IsElementaryAbelian.log_card_eq_primeRank (p := 2),hB.blockU_card]
    norm_num
  apply NoncentralFitting.quasisimple_of_two_le_two_rank hG hO hL
  have hr := (_root_.primeRank_le_of_injective 2 (blockU B).subtype
    (blockU B).subtype_injective).trans
      (_root_.primeRank_le_of_injective 2 (inclusion hBL) (inclusion_injective hBL))
  rw [hu] at hr
  omega

/-- The full actual carrier catalogue for a containing component of a deleted-five block. -/
theorem alternatingFive_containing_component_models_knownSimple
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    {B L : Subgroup G} (hL : L.IsCComponent) (hBL : B ≤ L)
    (hB : IsAlternatingBlock B 5) :
    IsQuasisimple L ∧
      ((IsSimpleGroup L ∧ Chapter1.Section02.LocalModels.TheoremCModel L) ∨
        (Nonempty (center L ≃* Multiplicative (ZMod 3)) ∧
          Chapter1.Section02.LocalModels.ThreeCoverModel L)) := by
  have hq := alternatingFive_containing_component_quasisimple hG hO hL hBL hB
  let := hq
  exact ⟨hq,quasisimple_containing_component_models_knownSimple hG hO hL⟩

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
