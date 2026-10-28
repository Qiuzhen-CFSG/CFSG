module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.ComponentOrbit
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Kernel
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
/-!
# The selected factor retains its actual moved and fixed subgroups

Equal original action images identify the elementary commutators. The
factor kernel fixes alpha, so its alpha centralizer also agrees with that
of the genuine selected component. Their literal local module is elementary:
it is the moved subgroup joined with the alpha summand central in the
component–Baumann join.

Source: Aschbacher–Smith B.6.10 and C.1.26, printed pp.117 and132.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB
variable {G H : Type*} [Group G] [Group H]

theorem fixed_alpha_eq_of_same_image
    (q : G →* H) (E L K : Subgroup G) (hLK : L ≤ K)
    (hi : L.map q = K.map q) (hk : K ⊓ q.ker ≤ centralizer (E : Set G)) :
    E ⊓ centralizer (L : Set G) = E ⊓ centralizer (K : Set G) := by
  apply le_antisymm ?_ (inf_le_inf_left E (centralizer_le hLK))
  intro e he
  refine ⟨he.1,?_⟩
  intro k hK
  obtain ⟨l,hl,hql⟩ := hi.symm ▸ mem_map_of_mem q hK
  let c := l⁻¹*k
  have hcK : c ∈ K := K.mul_mem (K.inv_mem (hLK hl)) hK
  have hcq : c ∈ q.ker := by
    change q (l⁻¹*k)=1
    rw [map_mul,map_inv,hql,inv_mul_cancel]
  have hce : e*c=c*e := hk ⟨hcK,hcq⟩ e he.1
  have hle : l*e=e*l := he.2 l hl
  have hlc : l*c=k := by dsimp [c]; group
  rw [←hlc]
  calc
    l*c*e = l*(c*e) := mul_assoc _ _ _
    _ = l*(e*c) := by rw [hce]
    _ = (l*e)*c := (mul_assoc _ _ _).symm
    _ = (e*l)*c := by rw [hle]
    _ = e*(l*c) := mul_assoc _ _ _

theorem moved_eq_of_same_image
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q) (hk : q.ker = centralizer (U : Set G))
    (L K : Subgroup G) (hi : L.map q = K.map q) :
    (⁅U,L⁆ : Subgroup G) = ⁅U,K⁆ := by
  have he : NormalElementaryQuotient.commutatorSpace U L =
      NormalElementaryQuotient.commutatorSpace U K := by
    rw [NormalElementaryQuotient.commutatorSpace_eq U q hq hk,
      NormalElementaryQuotient.commutatorSpace_eq U q hq hk,hi]
  ext x
  by_cases hx : x ∈ U
  · exact Iff.of_eq (congrArg (fun W : Submodule (ZMod 2) (Additive U) =>
      Additive.ofMul (⟨x,hx⟩ : U) ∈ W) he)
  · exact iff_of_false (fun h => hx (commutator_le_left U L h))
      (fun h => hx (commutator_le_left U K h))

theorem factor_localV_elementary
    (T U L : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hUL : U ≤ normalizer (L : Set G))
    (hv : (GlaubermanNiles.localV (inclusion (show baumann T ≤ L ⊔ baumann T from le_sup_right))).map
      (L ⊔ baumann T).subtype = ⁅U,L⁆ ⊔ (thompsonAlpha T ⊓ centralizer (L : Set G))) :
    IsElementaryAbelian 2 (GlaubermanNiles.localV (inclusion
      (show baumann T ≤ L ⊔ baumann T from le_sup_right))) := by
  let N := L ⊔ baumann T
  let b := inclusion (show baumann T ≤ N from le_sup_right)
  let W := ⁅U,L⁆
  let D := thompsonAlpha T ⊓ centralizer (L : Set G)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left U L)
  let : IsElementaryAbelian 2 (thompsonAlpha T) := omegaOneCenterAmbient_elementaryAbelian _
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le (show D ≤ thompsonAlpha T from inf_le_left)
  have hWN : W ≤ N := (le_normalizer_iff_commutator_le_right.mp hUL).trans le_sup_left
  have hDW : D ≤ centralizer (W : Set G) :=
    (fixed_alpha_central_selected T L).trans (centralizer_le hWN)
  let : IsElementaryAbelian 2 (W ⊔ D : Subgroup G) := IsElementaryAbelian.sup_of_le_centralizer hDW
  let : IsElementaryAbelian 2 ((GlaubermanNiles.localV b).map N.subtype) := hv.symm ▸ inferInstance
  exact IsElementaryAbelian.of_injective
    ((GlaubermanNiles.localV b).equivMapOfInjective N.subtype N.subtype_injective).toMonoidHom
    ((GlaubermanNiles.localV b).equivMapOfInjective N.subtype N.subtype_injective).injective
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
