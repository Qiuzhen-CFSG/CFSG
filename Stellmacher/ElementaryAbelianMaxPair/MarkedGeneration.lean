module
public import Stellmacher.ElementaryAbelianMaxPair.MarkedCover
public import Theory.GroupTheory.TwoPlaneCover.Rows
/-! # Generation by the marked maximum planes
The two elementary preimages are the full maximum family. Their join is the
whole marked Sylow group, so its elementary Thompson subgroup is the whole
group as well. Source application: Aschbacher--Smith 2.5.7.
-/
public section
open Subgroup
namespace Stellmacher
variable {G Q:Type*} [Group G] [Group Q] [Finite G]
theorem thompson_top_of_marked_planes
    (f:G→*Q) (hf:Function.Surjective f) (P₀ P₁:Subgroup Q)
    [IsElementaryAbelian 2 (P₀.comap f)] [IsElementaryAbelian 2 (P₁.comap f)]
    (hcard:Nat.card P₀=Nat.card P₁) (hne:P₀≠P₁)
    (hcover:∀A:Subgroup Q,IsElementaryAbelian 2 A→A≤P₀∨A≤P₁)
    (hgen:P₀⊔P₁=⊤) : elementaryAbelianMaxJ (⊤:Subgroup G)=⊤ := by
  have hp:=(maxFamily_pair_of_marked_preimages f hf P₀ P₁ hcard hne hcover).1
  change sSup (elementaryAbelianMaxSubgroups (⊤:Subgroup G))=⊤
  rw [hp,sSup_insert,sSup_singleton]
  exact Subgroup.TwoPlaneCover.comap_sup_eq_top f hf P₀ P₁ hgen

omit [Finite G] in
theorem thompson_subgroup_eq_of_intrinsic_top (S:Subgroup G)
    (h:elementaryAbelianMaxJ (⊤:Subgroup S)=⊤) : elementaryAbelianMaxJ S=S := by
  have hm:=elementaryAbelianMaxJ_map_injective S.subtype S.subtype_injective (⊤:Subgroup S)
  simpa only [h,←MonoidHom.range_eq_map,S.range_subtype] using hm
end Stellmacher
