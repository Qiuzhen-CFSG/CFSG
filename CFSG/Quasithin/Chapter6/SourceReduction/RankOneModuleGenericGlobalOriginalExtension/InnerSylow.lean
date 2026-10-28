module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.Marked
/-!
# Full endpoint restriction from the original inner Sylow image

The residual markings place L and the selected perfect R in the native inner
images. An inner image of the actual source S in the right endpoint then
transfers through the whole-overlap square. Each source Borel lies in the
opposite endpoint and in its own residual; their images are therefore inner
as well. The original endpoint generation formulas remove both outer parts.

The Ree application proves the inner-image premise from the native odd-outer
restriction, for every field parameter. This lemma does not require S = T or
R = O²(H). Source: Aschbacher--Smith F.1.12, printed p.264
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
namespace Preparation
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  {K₀ K₁ Q₀ Q₁ : Subgroup X}
  (e : OriginalExtension.Marking L R (sourceS L H) K₀ K₁ Q₀ Q₁)

include d h hTH hp in
/-- An inner image of the original S in the right endpoint forces both
whole endpoints inner, using the marked residuals and full-overlap agreement. -/
theorem original_extension_endpoints_inner_of_sourceS_inner
    (hS : ((sourceS L H).subgroupOf
      (ChapterF.Source.parabolic ![L,R] (sourceS L H) 1)).map e.right ≤
        MulAut.innerSubgroup X) :
    e.left.range ≤ MulAut.innerSubgroup X ∧
    e.right.range ≤ MulAut.innerSubgroup X := by
  let P₀ := ChapterF.Source.parabolic ![L,R] (sourceS L H) 0
  let P₁ := ChapterF.Source.parabolic ![L,R] (sourceS L H) 1
  let I := MulAut.innerSubgroup X
  let K₀ := (I.comap e.left).map P₀.subtype
  let K₁ := (I.comap e.right).map P₁.subtype
  have hL₀ : L ≤ P₀ := le_sup_left.trans le_sup_left
  have hR₁ : R ≤ P₁ := le_sup_left.trans le_sup_left
  have hS₀ : sourceS L H ≤ P₀ := le_sup_right.trans le_sup_left
  have hS₁ : sourceS L H ≤ P₁ := le_sup_right.trans le_sup_left
  have hL : L ≤ K₀ := by
    intro x hx
    refine ⟨⟨x,hL₀ hx⟩,?_,rfl⟩
    change e.left ⟨x,hL₀ hx⟩ ∈ I
    have he := e.left_residual ▸ (mem_map_of_mem e.left
      ((d.original_local_eq_residual h hTH hp 0).le (show (⟨x,hL₀ hx⟩ : P₀) ∈ L.subgroupOf P₀ from hx)))
    exact (Subgroup.map_le_range _ _) he
  have hR : R ≤ K₁ := by
    intro x hx
    refine ⟨⟨x,hR₁ hx⟩,?_,rfl⟩
    change e.right ⟨x,hR₁ hx⟩ ∈ I
    have he := e.right_residual ▸ (mem_map_of_mem e.right
      ((d.original_local_eq_residual h hTH hp 1).le (show (⟨x,hR₁ hx⟩ : P₁) ∈ R.subgroupOf P₁ from hx)))
    exact (Subgroup.map_le_range _ _) he
  have hsame (x : (P₀ ⊓ P₁ : Subgroup G)) : (x : G) ∈ K₀ ↔ (x : G) ∈ K₁ := by
    change (x : G) ∈ (I.comap e.left).map P₀.subtype ↔
      (x : G) ∈ (I.comap e.right).map P₁.subtype
    change P₀.subtype ⟨x,x.property.1⟩ ∈ (I.comap e.left).map P₀.subtype ↔
      P₁.subtype ⟨x,x.property.2⟩ ∈ (I.comap e.right).map P₁.subtype
    rw [mem_map_iff_mem P₀.subtype_injective,mem_map_iff_mem P₁.subtype_injective]
    change e.left ((sourceParabolicAmalgam ![L,R] (sourceS L H)).left x) ∈ I ↔
      e.right ((sourceParabolicAmalgam ![L,R] (sourceS L H)).right x) ∈ I
    rw [e.agrees]
  have hs : sourceS L H ≤ K₁ := by
    intro x hx
    refine ⟨⟨x,hS₁ hx⟩,?_,rfl⟩
    exact hS (mem_map_of_mem e.right hx)
  have hs' : sourceS L H ≤ K₀ := fun x hx =>
    (hsame ⟨x,hS₀ hx,hS₁ hx⟩).mpr (hs hx)
  have hbR₀ : ChapterF.Source.borel R (sourceS L H) ≤ P₀ := le_sup_right
  have hbL₁ : ChapterF.Source.borel L (sourceS L H) ≤ P₁ := le_sup_right
  have hbR : ChapterF.Source.borel R (sourceS L H) ≤ K₀ := fun x hx =>
    (hsame ⟨x,hbR₀ hx,hR₁ hx.1⟩).mpr (hR hx.1)
  have hbL : ChapterF.Source.borel L (sourceS L H) ≤ K₁ := fun x hx =>
    (hsame ⟨x,hL₀ hx.1,hbL₁ hx⟩).mp (hL hx.1)
  have hP₀ : P₀ ≤ K₀ := sup_le (sup_le hL hs') hbR
  have hP₁ : P₁ ≤ K₁ := sup_le (sup_le hR hs) hbL
  constructor
  · rintro _ ⟨x,rfl⟩
    exact (mem_map_iff_mem P₀.subtype_injective).mp (hP₀ x.property)
  · rintro _ ⟨x,rfl⟩
    exact (mem_map_iff_mem P₁.subtype_injective).mp (hP₁ x.property)

end Preparation
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
