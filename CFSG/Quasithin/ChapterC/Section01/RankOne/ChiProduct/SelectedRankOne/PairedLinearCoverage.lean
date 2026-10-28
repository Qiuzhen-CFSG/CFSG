module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedLinearFixedAlpha
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedFactorOrbit.PerfectLift
/-!
# The selected paired component covers the residual with its actual conjugate

The exact two-core action kernel identifies the selected component quotient
with the marked first SL₂ factor. The canonical perfect factor lift and the
prescribed Sylow exchanger give the actual two-residual cover. Thus this same
component generates with the original Sylow; its local class and nonzero
alpha fixed subgroup are retained.
Source: Aschbacher--Smith B.6.9, C.1.26 and E.2.3, pp.115--116,132,216--217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB ChapterB.SourceInduction ChapterB.QuasisimpleSource ChapterB.RankOneBaumann.PairedFactorOrbit
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
theorem first_component_localClass_with_coverage
    {C : GroupClass.{u}} (h36 : Chapter1.Section02.A36Input C) (hG : IsSQTK C G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q) (hk : q.ker = centralizer (U : Set G))
    (hkc : q.ker = pCore 2 G)
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
        (⁅U,L⁆ : Subgroup G) ⊔ (thompsonAlpha (T : Subgroup G) ⊓ centralizer (L : Set G)) ∧
      thompsonAlpha (T : Subgroup G) ⊓ centralizer (L : Set G) ≠ ⊥ ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier) ∧
      L ⊔ (T : Subgroup G) = ⊤ ∧
      ∃ t ∈ (T : Subgroup G), pResidual 2 G = L ⊔ L.map (MulAut.conj t).toMonoidHom := by
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  let := d.product.first_normal
  let := d.product.second_normal
  obtain ⟨L,hL,hi,hcan,hUL,hBL,hlocal,hv,hfixed⟩ :=
    first_component_localClass_with_alpha_fixed h36 hG T hP U hU hJ q hq hk hs hfit d F c hexchange
  let := hL.perfect
  let : Group.IsPerfect (L.map q) := Group.IsPerfect.ofSurjective
    (f := q.subgroupMap L) (q.subgroupMap_surjective L)
  let : Group.IsPerfect (d.first.map Y.subtype) := hi ▸ (inferInstance : Group.IsPerfect (L.map q))
  let : Group.IsPerfect d.first := Group.IsPerfect.ofSurjective
    (f := (d.first.equivMapOfInjective Y.subtype Y.subtype_injective).symm.toMonoidHom)
    (d.first.equivMapOfInjective Y.subtype Y.subtype_injective).symm.surjective
  have hkernel : (q.subgroupMap L).ker = pCore 2 L := by
    rw [ker_subgroupMap,hkc,pCore_subnormal_eq_comap 2 hL.subnormal]
    rfl
  let eq : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier :=
    ((QuotientGroup.quotientMulEquivOfEq hkernel.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (q.subgroupMap L) (q.subgroupMap_surjective L))).trans
      ((MulEquiv.subgroupCongr hi).trans (first_axis_equiv Y d.first c.action.groupEquiv c.first_eq))
  have hcore : pCore 2 H = ⊥ := by
    let eq := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [←pCore_map_iso 2 eq,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hn : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hk ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T:Subgroup G) ≤ ⊤)))
  have hp := (minimalParabolic_reduced_image T hP q hq hcore hn).2
  have hff : IsFFModule α := by
    obtain hf | ⟨_,hff,_,_,_⟩ := lemma_B_2_7 U q hq hk T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hf.1)).elim
    · exact hff
  have hRY : (pResidual 2 G).map q ≤ Y := by
    rw [map_pResidual_of_surjective 2 q hq,←offender_residual_eq (T.mapSurjective hq) hp α hff hcore]
    exact map_subtype_le _
  obtain ⟨t,ht₁,ht₂⟩ := hexchange
  obtain ⟨g,hg,he⟩ := (show (t:H) ∈ (T:Subgroup G).map q from t.property)
  have hc : Y.subtype.comp (MulAut.conjNormal (t:H)).toMonoidHom =
      (MulAut.conj (t:H)).toMonoidHom.comp Y.subtype := by ext; rfl
  have hm := congrArg (map Y.subtype) ht₁
  rw [map_map,hc,←map_map,←he] at hm
  have hcover := selected_perfect_factor_sup_conjugate q hq
    (hkc.symm ▸ (pCore_isPGroup : IsPGroup 2 (pCore 2 G)))
    Y d.first d.second d.product.sup_eq_top hRY L hcan g hm
  have hgen : L ⊔ (T : Subgroup G) = ⊤ := by
    apply top_unique
    rw [←pResidual_sup_sylow_eq_top T,hcover]
    apply sup_le (sup_le le_sup_left ?_) le_sup_right
    rintro _ ⟨x,hx,rfl⟩
    exact (L ⊔ (T : Subgroup G)).mul_mem
      ((L ⊔ (T : Subgroup G)).mul_mem ((show (T : Subgroup G) ≤ L ⊔ T from le_sup_right) hg)
        ((show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) hx))
      ((show (T : Subgroup G) ≤ L ⊔ T from le_sup_right) ((T : Subgroup G).inv_mem hg))
  exact ⟨L,hL,hi,hcan,hUL,hBL,hlocal,hv,hfixed,⟨eq⟩,hgen,g,hg,hcover⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
