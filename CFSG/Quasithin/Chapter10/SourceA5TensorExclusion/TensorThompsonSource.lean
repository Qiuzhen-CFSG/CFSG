module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorCorankComplete
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.SylowThompson.KnownSimple

/-!
# Higher Thompson movement in the generation-one tensor branch

The completed tensor bound r(G,V) ≥ 2 allows E.6.26 with j=1. If the
first higher Thompson subgroup of the actual Sylow group centralizes V,
E.6.26 puts every generation-one H-star subgroup inside M, contradicting
its defining escape. This proves the movement assertion of source 9.2.4(2)
on the original field-four tensor model and its prescribed H-star subgroup.

Source: Aschbacher--Smith 9.2.4(2), printed p.730, using E.6.26.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

theorem thompson_one_moves_of_generation_one
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hgen : generationParameter H = 1) :
    ¬ ChapterB.thompsonJ (T : Subgroup G) 1 ≤ centralizer (D.fullModule : Set G) := by
  intro hJ
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hs : ((T.subtype hTH : Sylow 2 H) : Subgroup H).map H.subtype = T := by
    change ((T : Subgroup G).subgroupOf H).map H.subtype = T
    exact map_subgroupOf_eq_of_le hTH
  have hr : (1 : ℕ∞) < globalR D.fullModule :=
    lt_of_lt_of_le (by norm_num) (m.globalR_ge_two_source hout)
  have hc := ChapterE.Section06.FixedPointBounds.SylowThompson.source_E_6_26_knownSimple
    m.tensor_hypothesisE61 (j := 1) (by omega) H (T.subtype hTH)
    (Chapter3.sqtk_of_mem_H D.simpleQTKE hH.1.1.1) (by omega)
    (by rw [hs]; exact inf_le_left) (by rw [hs]) hr (by rwa [hs])
  exact hH.1.2 hc.1
end CFSG.Quasithin.Chapter10.SourceA5TensorModel
