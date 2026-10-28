module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedLinearGeometry
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedSupport
/-!
# The actual selected component module in the paired source

The genuine first component and raw factor have the same original action
image. Their moved subgroups and their centralizers in alpha therefore agree.
Thus the exact local module for the original Baumann inclusion is the selected
component moved subgroup times its central alpha summand, and is elementary.
All geometry and field-size inputs come from the same original B.5.6 pair.

Source: Aschbacher–Smith C.1.26, printed p.132, using B.6.10.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB ChapterB.SourceInduction ChapterB.QuasisimpleSource ChapterB.RankOneBaumann.PairedFactorOrbit
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
theorem first_component_module_geometry
    {C : GroupClass.{u}} (h36 : Chapter1.Section02.A36Input C) (hG : IsSQTK C G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q) (hk : q.ker = centralizer (U : Set G))
    (hs : ¬ Group.IsSolvable G) (hfit : generalizedFitting G = pCore 2 G)
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hk).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype))
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hk)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first) :
    let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)
    let B := baumann (T : Subgroup G)
    ∃ L : Subgroup G, L.IsCComponent ∧ L.map q = d.first.map Y.subtype ∧
      (solvableResidual (factorPreimage q Y d.first)).map (factorPreimage q Y d.first).subtype = L ∧
      U ≤ normalizer (L : Set G) ∧ B ≤ normalizer (L : Set G) ∧
      Chapter1.IsSylowIn 2 B (L ⊔ B) ∧
      generalizedFitting (L ⊔ B : Subgroup G) = pCore 2 (L ⊔ B : Subgroup G) ∧
      (∃ S : Sylow 2 (L ⊔ B : Subgroup G),
        (inclusion (show B ≤ L ⊔ B from le_sup_right)).range = S ∧ IsMinimalParabolicOver S ⊤) ∧
      (GlaubermanNiles.localV (inclusion (show B ≤ L ⊔ B from le_sup_right))).map (L ⊔ B).subtype =
        (⁅U,L⁆ : Subgroup G) ⊔ (thompsonAlpha (T : Subgroup G) ⊓ centralizer (L : Set G)) ∧
      IsElementaryAbelian 2 (GlaubermanNiles.localV (inclusion (show B ≤ L ⊔ B from le_sup_right))) := by
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let A := d.first.map Y.subtype
  let K := factorResidual q Y d.first
  let B := baumann (T : Subgroup G)
  obtain ⟨L,hL,hi,hcan,hLK,hBL,hS,hN,hP',hv⟩ :=
    first_component_geometry h36 hG T hP U hU hJ q hq hk hs hfit d F c hexchange
  have hUker : U ≤ q.ker := by
    rw [hk]
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm (⟨y,hy⟩ : U) ⟨x,hx⟩)
  have hUL : U ≤ normalizer (L : Set G) := selected_component_normalized q A L U hcan (by
    rintro x ⟨y,hy,rfl⟩
    have hh : q y = 1 := hUker hy
    rw [hh]
    exact one_mem _)
  have hKI : K.map q = A := by
    apply le_antisymm ?_ (hi.symm.le.trans (map_mono hLK))
    exact (map_mono (map_subtype_le (pResidual 2 (factorPreimage q Y d.first)))).trans
      ((map_comap_le q A))
  have ha := (source_global_baumann_and_alpha T hP U hU hJ q hq hk d F c hexchange).2
  have ha' : thompsonAlpha (T : Subgroup G) ≤ U ⊔
      (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) :=
    ha.le.trans (sup_le le_sup_right (inf_le_left.trans le_sup_left))
  have hfix := fixed_alpha_eq_of_same_image q (thompsonAlpha (T : Subgroup G)) L K hLK
    (hi.trans hKI.symm) (factor_kernel_centralizes_alpha (T : Subgroup G) U (pResidual 2 G) K
      (factorResidual_le_residual q Y d.first) q hk.le ha')
  have hmov := moved_eq_of_same_image U q hq hk L K (hi.trans hKI.symm)
  rw [←hfix,←hmov] at hv
  exact ⟨L,hL,hi,hcan,hUL,hBL,hS,hN,hP',hv,factor_localV_elementary (T : Subgroup G) U L hUL hv⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
