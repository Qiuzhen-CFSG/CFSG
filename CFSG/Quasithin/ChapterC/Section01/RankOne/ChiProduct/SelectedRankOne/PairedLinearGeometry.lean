module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.ComponentGeometry
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.ComponentOrbit
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedFactorOrbit.Source
public import GorensteinWalter.SL2ProjectiveCover
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedLinearField
/-!
# The genuine first component of the paired natural source

Select the solvable residual of the original first-factor preimage. The
component lifting theorem supplies its intrinsic Frattini kernel. The
original Baumann subgroup remains Sylow in its join, and the already-proved
factor alpha orbit transfers through the same actual quotient image. This
constructs the precise C.1.17 local module and minimal-parabolic geometry;
no Frattini restriction to the raw two-residual is assumed.

Source: Aschbacher–Smith C.1.26, printed p.132, and B.6.10.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB ChapterB.SourceInduction ChapterB.QuasisimpleSource ChapterB.RankOneBaumann.PairedFactorOrbit
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]

noncomputable def first_axis_equiv {D : Type*} [Group D] (Y : Subgroup H)
    (A : Subgroup Y) (e : Y ≃* D × D)
    (ha : ((⊤ : Subgroup D).prod ⊥).map e.symm.toMonoidHom = A) :
    A.map Y.subtype ≃* D :=
  (A.equivMapOfInjective Y.subtype Y.subtype_injective).symm.trans
    ((MulEquiv.subgroupCongr ha.symm).trans
      ((((⊤ : Subgroup D).prod ⊥).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm.trans
        (((⊤ : Subgroup D).prodEquiv (⊥ : Subgroup D)).trans
          ((MulEquiv.prodUnique : (⊤ : Subgroup D) × (⊥ : Subgroup D) ≃* (⊤ : Subgroup D)).trans topEquiv))))

theorem first_component_geometry
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
    let K := factorResidual q Y d.first
    let B := baumann (T : Subgroup G)
    ∃ L : Subgroup G, L.IsCComponent ∧ L.map q = d.first.map Y.subtype ∧
      (solvableResidual (factorPreimage q Y d.first)).map (factorPreimage q Y d.first).subtype = L ∧
      L ≤ K ∧ B ≤ normalizer (L : Set G) ∧ Chapter1.IsSylowIn 2 B (L ⊔ B) ∧
      generalizedFitting (L ⊔ B : Subgroup G) = pCore 2 (L ⊔ B : Subgroup G) ∧
      (∃ S : Sylow 2 (L ⊔ B : Subgroup G),
        (inclusion (show B ≤ L ⊔ B from le_sup_right)).range = S ∧ IsMinimalParabolicOver S ⊤) ∧
      (GlaubermanNiles.localV (inclusion (show B ≤ L ⊔ B from le_sup_right))).map (L ⊔ B).subtype =
        (⁅U,K⁆ : Subgroup G) ⊔ (thompsonAlpha (T : Subgroup G) ⊓ centralizer (K : Set G)) := by
  have hF := paired_linear_field_large T hP U hU hJ q hq hk hs d F c
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let A := d.first.map Y.subtype
  let K := factorResidual q Y d.first
  let B := baumann (T : Subgroup G)
  let D := Matrix.SpecialLinearGroup (Fin 2) F.Carrier
  let := offenderSubgroup_normal α
  let := d.product.first_normal
  let e : A ≃* D := first_axis_equiv Y d.first c.action.groupEquiv c.first_eq
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
  let : Group.IsPerfect D := GorensteinWalter.sl2_isPerfect_of_card_gt_three F.Carrier hlarge
  let : IsQuasisimple D := ⟨Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)⟩
  let : IsQuasisimple A := IsQuasisimple.of_mulEquiv e.symm
  have hA : IsComponent H A := ⟨(inferInstance : d.first.Normal).isSubnormal.trans'
    (inferInstance : Y.Normal).isSubnormal,inferInstance⟩
  obtain ⟨L,hL,himage,hqs,hfr,hcanonical⟩ := exists_component_with_intrinsic_frattini_kernel
    h36 hG T hP U hU hJ q hq hk hs A hA
  let := hqs
  have hLK : L ≤ K := by
    rw [←hcanonical]
    apply map_mono
    let : Group.IsNilpotent (factorPreimage q Y d.first ⧸ pResidual 2 (factorPreimage q Y d.first)) :=
      (isPGroup_quotient_pResidual (G := factorPreimage q Y d.first) 2).isNilpotent
    exact solvableResidual_le_of_solvable_quotient _
  obtain ⟨_,hK,_⟩ := source_factor_conclusions T hP U hU hJ q hq hk d F c hexchange
  obtain ⟨ρ,hρ,hnat,he,⟨hJq,hBq⟩,hfix⟩ := source_images_and_fixedSpace T hP U hU hJ q hq hk d F c hexchange
  have hYA : Y ≤ normalizer (A : Set H) := by
    have hh := d.first.le_normalizer_map Y.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  have hBL : B ≤ normalizer (L : Set G) := selected_component_normalized q A L B hcanonical
    ((hBq.le.trans inf_le_right).trans hYA)
  have hS : Chapter1.IsSylowIn 2 B (L ⊔ B) :=
    Chapter1.IsSylowIn.restrict hK.2.1 le_sup_right (sup_le_sup_right hLK B)
  have hcore : pCore 2 H = ⊥ := by
    let eq := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [←pCore_map_iso 2 eq,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hKI : K.map q = A := by
    rw [factorResidual_image q hq]
    let : IsQuasisimple d.first := IsQuasisimple.of_mulEquiv
      ((d.first.equivMapOfInjective Y.subtype Y.subtype_injective).trans e).symm
    let : Group.IsNilpotent (d.first ⧸ pResidual 2 d.first) :=
      (isPGroup_quotient_pResidual 2).isNilpotent
    have hr : pResidual 2 d.first = ⊤ := top_unique (by
      rw [←solvableResidual_eq_top (G := d.first)]
      exact solvableResidual_le_of_solvable_quotient _)
    rw [hr,←MonoidHom.range_eq_map,range_subtype]
  have ha := (source_global_baumann_and_alpha T hP U hU hJ q hq hk d F c hexchange).2
  have ha' : thompsonAlpha (T : Subgroup G) ≤ U ⊔
      (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) := by
    exact ha.le.trans (sup_le le_sup_right (inf_le_left.trans le_sup_left))
  refine ⟨L,hL,himage,hcanonical,hLK,hBL,hS,component_baumann_fitting T L hL.subnormal hBL hfit,
    component_baumann_minimal F.Carrier T q hcore L (himage.symm ▸ hA)
      ((MulEquiv.subgroupCongr himage).trans e) hBL hS,?_⟩
  rw [localV_component_eq_factor_orbit (T : Subgroup G) U (pResidual 2 G) K L hLK
    (factorResidual_le_residual q Y d.first) hBL q hk.le (himage.trans hKI.symm) ha']
  exact hK.2.2
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
