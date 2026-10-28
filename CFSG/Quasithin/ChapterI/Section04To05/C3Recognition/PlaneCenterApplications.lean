module

public import CFSG.Quasithin.ChapterI.Section04To05.C3Recognition.PlaneCenter

/-!
# The literal original third-vertex center contradiction

In 13.7.5–6 the recognized system lives inside a generated subgroup E,
and its third vertex is the restriction of the original KT to E. The
subgroup equivalence below carries that exact restriction back to KT.
It therefore kills a central element of KT itself, rather than silently
replacing centrality in KT by centrality in E.

The independent 13.7 family producer supplies the actual D-system and
third-vertex equality. No unmarked recognition equivalence is assumed.
-/

public noncomputable section
namespace Quasithin.I5.C3Recognition
open Subgroup
variable {G : Type*} [Group G]

theorem original_plane_vertex_center_eq_bot (E K : Subgroup G) (hKE : K ≤ E)
    (S : DSystem .C3 E) (hthird : S.family 2 = K.subgroupOf E) : center K = ⊥ := by
  let e : S.family 2 ≃* K := (MulEquiv.subgroupCongr hthird).trans (subgroupOfEquivOfLe hKE)
  apply le_bot_iff.mp
  intro a ha
  have hz : e.symm a ∈ center (S.family 2) := by
    rw [mem_center_iff]
    intro b
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_center_iff.mp ha (e b)
  rw [plane_center_eq_bot S, mem_bot] at hz
  exact mem_bot.mpr (e.symm.injective (hz.trans (map_one _).symm))

theorem original_plane_central_element_eq_one (E K : Subgroup G) (hKE : K ≤ E)
    (S : DSystem .C3 E) (hthird : S.family 2 = K.subgroupOf E)
    (z : K) (hz : z ∈ center K) : (z : G) = 1 := by
  rw [original_plane_vertex_center_eq_bot E K hKE S hthird, mem_bot] at hz
  exact congrArg Subtype.val hz

end Quasithin.I5.C3Recognition
