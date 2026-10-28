module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedLinearNatural
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedLinearModule
public import GorensteinWalter.SL2ProjectiveCover
/-!
# The original paired natural source supplies an actual C.1.17 group

The same original marked B.5.6 pair determines its canonical genuine first
component. Its original Baumann join is minimal parabolic and of
characteristic two; the exact first-coordinate quotient and retained
fixed kernel give its natural local module. Thus the inclusion of the
original Baumann subgroup belongs to the local class used by the one
uniform C.1.18 characteristic pair.

Source: Aschbacher–Smith C.1.26, printed p.132, using B.6.10.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB ChapterB.SourceInduction ChapterB.QuasisimpleSource ChapterB.RankOneBaumann.PairedFactorOrbit
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
private theorem perfect_isTwoPerfect {K : Type*} [Group K] [Finite K] [Group.IsPerfect K] : IsPPerfect 2 K := by
  intro N hN hp
  let := hN
  let : Group.IsNilpotent (K ⧸ N) := hp.isNilpotent
  apply top_unique
  rw [←solvableResidual_eq_top (G := K)]
  exact solvableResidual_le_of_solvable_quotient N
theorem first_component_localClass
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
      GlaubermanNiles.InLocalClass (inclusion (show B ≤ L ⊔ B from le_sup_right)) ∧
      (GlaubermanNiles.localV (inclusion (show B ≤ L ⊔ B from le_sup_right))).map (L ⊔ B).subtype =
        (⁅U,L⁆ : Subgroup G) ⊔ (thompsonAlpha (T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let A := Matrix.SpecialLinearGroup (Fin 2) F.Carrier
  let e := c.action.groupEquiv
  let B := baumann (T : Subgroup G)
  obtain ⟨L,hL,hi,hcan,hUL,hBL,hS,hN,hP',hv,hve⟩ :=
    first_component_module_geometry h36 hG T hP U hU hJ q hq hk hs hfit d F c hexchange
  let := hL.perfect
  have hF := paired_linear_field_large T hP U hU hJ q hq hk hs d F c
  have hlarge : 3 < Nat.card F.Carrier := by
    rw [F.card_eq] at hF ⊢
    have hd : 2 ≤ F.degree := by
      by_contra! hh
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hh
      norm_num at hp
      omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hd
    norm_num at hp
    omega
  let : Group.IsPerfect A := GorensteinWalter.sl2_isPerfect_of_card_gt_three F.Carrier hlarge
  let : IsQuasisimple A := ⟨Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)⟩
  obtain ⟨ρ,hρ,hnat,heρ,⟨hJq,hBq⟩,hfix⟩ := source_images_and_fixedSpace T hP U hU hJ q hq hk d F c hexchange
  have hNY : (L ⊔ B).map q ≤ Y := by
    rw [Subgroup.map_sup,hi]
    exact sup_le (map_subtype_le d.first) (hBq.le.trans inf_le_right)
  have haxis : (⊤ : Subgroup A).map (MonoidHom.inl A A) = (⊤ : Subgroup A).prod ⊥ := by
    ext x
    constructor
    · rintro ⟨a,_,rfl⟩
      exact ⟨mem_top _,mem_bot.mpr rfl⟩
    · rintro ⟨_,hx⟩
      exact ⟨x.1,mem_top _,Prod.ext rfl hx.symm⟩
  have hLI : L.map q = (⊤ : Subgroup A).map
      (Y.subtype.comp (e.symm.toMonoidHom.comp (MonoidHom.inl A A))) := by
    rw [←map_map,←map_map,haxis,c.first_eq,hi]
  have hfk : c.quotientMap.ker ≤ fixedSpace α (Y.subtype.comp e.symm.toMonoidHom).range := by
    rw [c.quotientMap_ker]
    intro v hv' a
    obtain ⟨g,hg⟩ := a.property
    change α a v = v
    rw [←hg]
    exact hv' (e.symm g)
  have he : ∀ g v, c.quotientMap (α ((Y.subtype.comp e.symm.toMonoidHom) g) v) =
      (linearNatural F 2 g.1 (c.quotientMap v).1,linearNatural F 2 g.2 (c.quotientMap v).2) := by
    intro g v
    have hh := c.quotientMap_action (e.symm g) v
    rw [e.apply_symm_apply] at hh
    exact hh
  have hmodel := paired_first_natural_model F (T : Subgroup G) U L perfect_isTwoPerfect hUL hBL
    q hq hk Y e perfect_isTwoPerfect hNY hLI c.quotientMap c.quotientMap_surjective hfk he hv
  exact ⟨L,hL,hi,hcan,hUL,hBL,⟨inclusion_injective _,hP',hN,F.degree,F.degree_pos,
    F.Carrier,inferInstance,inferInstance,inferInstance,F.card_eq,hmodel⟩,hv⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
