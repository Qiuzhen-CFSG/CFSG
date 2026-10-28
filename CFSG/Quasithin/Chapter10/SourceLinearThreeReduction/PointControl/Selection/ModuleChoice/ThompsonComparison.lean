module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietAction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.ThreeFree
public import Theory.GroupTheory.CenterlessCentralizer
public import Theory.Representation.BinaryOffender.NormalClosure

/-!
# Comparing the original local and full Thompson actions

The actual component pair embeds in the full action as a centerless product.
When three divides the component order, the cubic residual makes its
centralizer three-free. An element of the local action kernel centralizes
this pair in the full action: its commutators belong to both the original
orbit and the local kernel, hence to the orbit two-core, which fixes the full
module. If Thompson centralizes the local module, every moving maximal
elementary subgroup would therefore give an offender in this three-free
normal centralizer. The complete B.5 classification excludes that offender.

Thus local and full Thompson centralization agree in these source cases.
The applications in ModuleChoice.Source recognize the actual natural rows
from full Thompson movement and extend the quiet point-selection theorem.
The component-fixed vector and even positive-kernel stabilization remain
separate mathematical obligations of the same source assembly.

Source: Aschbacher--Smith, 3.2.6, 10.1.1--3 and B.5.6,
printed pp.581,741--742 and105.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The image of the actual component orbit in the full actor is centerless. -/
theorem original_full_actor_orbit_center
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    let X := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    center X = ⊥ := by
  dsimp only
  let M := D.maximalLocal
  let R := localOrbit T L
  let U := D.fullModule.subgroupOf M
  let := (source_full_module_reduced D).normal
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let X := (R.subgroupOf M).map q
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  obtain ⟨p,hp,hpk,hl,hr⟩ := original_component_product_quotient D hn ht htn
  obtain ⟨i,hi,_,hdiagram⟩ := original_component_product_embedding D hn p hp hpk
  have hrange : i.range = X := by
    ext y
    constructor
    · rintro ⟨a,rfl⟩
      obtain ⟨x,rfl⟩ := hp a
      rw [hdiagram]
      exact ⟨inclusion R.le_normalizer x,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨p ⟨x,hx⟩,hdiagram ⟨x,hx⟩⟩
  let e := (MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hi).symm
  let := D.quasisimple
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_quotient_simple D hn
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    rcases (inferInstance : (center (L ⧸ pCore 2 L)).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative (L ⧸ pCore 2 L)
        (center_eq_top_iff.mp h)).elim
  have hpz : center ((L ⧸ pCore 2 L) × (L ⧸ pCore 2 L)) = ⊥ := by
    rw [Subgroup.center_prod,hz,bot_prod_bot]
  apply _root_.eq_bot_iff.mpr
  intro x hx
  have he := (centerCongr e ⟨x,hx⟩).property
  change e x ∈ center ((L ⧸ pCore 2 L) × (L ⧸ pCore 2 L)) at he
  rw [hpz,mem_bot] at he
  exact e.map_eq_one_iff.mp he

/-- The cubic residual excludes three from the centralizer of the actual orbit image. -/
theorem original_full_actor_centralizer_three_free
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    let X := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    Nat.Coprime 3 (Nat.card (centralizer (X : Set
      (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))))) := by
  dsimp only
  let M := D.maximalLocal
  let R := localOrbit T L
  let U := D.fullModule.subgroupOf M
  let := (source_full_module_reduced D).normal
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let X := (R.subgroupOf M).map q
  let : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : X.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have he : R.subgroupOf M = primeToResidual 3 M := by
    apply map_injective M.subtype_injective
    rw [map_subgroupOf_eq_of_le R.le_normalizer,source_nonnormal_cubic_residual D hn hd]
  have hc : Nat.Coprime 3 (R.subgroupOf M).index := by
    rw [he]
    exact primeToResidual_index_coprime 3
  exact (hc.coprime_dvd_right ((R.subgroupOf M).index_map_dvd
    (QuotientGroup.mk'_surjective _))).coprime_dvd_right
    (centralizer_card_dvd_index_of_center_eq_bot X (original_full_actor_orbit_center D hn))

/-- The local action kernel centralizes the component orbit in the full action. -/
theorem local_kernel_full_image_le_centralizer
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    let H := localJoin T L
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    let X := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    ∀ x : H, x ∈ centralizer (D.moduleSubgroup.subgroupOf H : Set H) →
      q (inclusion (sup_le (localOrbit T L).le_normalizer
        (le_normalizer_componentOrbit L T)) x) ∈ centralizer (X : Set _) := by
  dsimp only
  let H := localJoin T L
  let M := D.maximalLocal
  let R := localOrbit T L
  let U := D.fullModule.subgroupOf M
  let V := D.moduleSubgroup.subgroupOf H
  let : V.Normal := normal_subgroupOf_of_le_normalizer D.join_normalizes_module
  let := (source_full_module_reduced D).normal
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let p := QuotientGroup.mk' (centralizer (V : Set H))
  have hHM : H ≤ M := sup_le R.le_normalizer (le_normalizer_componentOrbit L T)
  let f := p.comp (inclusion (show R ≤ H from le_sup_left))
  have hk : f.ker ≤ pCore 2 R := by
    have he : f.ker = (centralizer (V : Set H)).comap
        (inclusion (show R ≤ H from le_sup_left)) := by
      change (p.comp (inclusion (show R ≤ H from le_sup_left))).ker = _
      rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    have hp := (local_module_kernel_isTwoGroup D hn).comap_of_injective
      (inclusion (show R ≤ H from le_sup_left)) (inclusion_injective _)
    exact le_sSup ⟨inferInstance,he.symm ▸ hp⟩
  intro x hx
  have hx1 : p x = 1 := (QuotientGroup.eq_one_iff _).mpr hx
  rintro y ⟨r,hr,rfl⟩
  let rR : R := ⟨r,hr⟩
  let rH : H := inclusion (show R ≤ H from le_sup_left) rR
  have hRn : H ≤ normalizer (R : Set G) :=
    sup_le R.le_normalizer (le_normalizer_componentOrbit L T)
  have hcR : (x : G)*(r : G)*(x : G)⁻¹*(r : G)⁻¹ ∈ R :=
    R.mul_mem ((mem_normalizer_iff.mp (hRn x.property) r).mp hr) (R.inv_mem hr)
  let cR : R := ⟨_,hcR⟩
  have hc : cR ∈ f.ker := by
    change p (x*rH*x⁻¹*rH⁻¹) = 1
    simp only [map_mul,map_inv,hx1,one_mul,inv_one,mul_one,mul_inv_cancel]
  have hf : q (inclusion R.le_normalizer cR) = 1 := by
    have hh := hk hc
    rw [←full_actor_restriction_kernel D hn] at hh
    exact hh
  have he : q (inclusion hHM x) * q r * (q (inclusion hHM x))⁻¹ * (q r)⁻¹ = 1 := by
    simp only [←map_inv,←map_mul]
    exact hf
  exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp he)).symm

/-- Local Thompson centralization extends to the full module when the original
component quotient has cubic order. No irreducibility or model premise is needed. -/
theorem full_thompson_centralizes_of_local_three
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G)) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) := by
  let M := D.maximalLocal
  let R := localOrbit T L
  let H := localJoin T L
  let U := D.fullModule.subgroupOf M
  let hu := source_full_module_reduced D
  let := hu.normal
  let := hu.elementary
  let Q := M ⧸ centralizer (U : Set M)
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  let X := (R.subgroupOf M).map q
  let C := centralizer (X : Set Q)
  let : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : X.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : C.Normal := inferInstance
  let S := D.ambientSylow
  have hJmap : (elementaryAbelianMaxJ (S : Subgroup M)).map M.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective]
    exact congrArg elementaryAbelianMaxJ
      (map_subgroupOf_eq_of_le (le_normalizer_componentOrbit L T))
  have hJC : (elementaryAbelianMaxJ (S : Subgroup M)).map q ≤ C := by
    rintro _ ⟨j,hj,rfl⟩
    have hjG : (j : G) ∈ elementaryAbelianMaxJ (T : Subgroup G) := by
      rw [←hJmap]
      exact mem_map_of_mem M.subtype hj
    have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
      sSup_le fun _ hA => hA.1
    have hjT : (j : G) ∈ (T : Subgroup G) := hJT hjG
    have hjH : (j : G) ∈ H := (show (T : Subgroup G) ≤ H from le_sup_right) hjT
    apply local_kernel_full_image_le_centralizer D hn (⟨j,hjH⟩ : H)
    intro v hv
    exact Subtype.ext (hJ hjG v hv)
  let c : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple Q := {
    Cover := M
    kernel := centralizer (U : Set M)
    sqtk := D.simpleQTKE.twoLocal_sqtk
      (source_module_nonsolvable_uniqueness D).normalizer_maximal.1
    equiv := MulEquiv.refl Q }
  have hno : ¬ IsFFModule (ρ.comp C.subtype) :=
    ChapterB.SourceInduction.no_ff_of_three_free
      ((ChapterB.InternalThompsonAction.action_faithful U).comp C.subtype_injective)
      (normal_subgroup_twoCore_eq_bot C hu.quotient_pCore_eq_bot)
      (c.subgroup C) (original_full_actor_centralizer_three_free D hn hd)
  have hfix : elementaryAbelianMaxJ (S : Subgroup M) ≤ centralizer (U : Set M) := by
    apply sSup_le
    intro E hE
    by_contra hEC
    have hn' : ¬ E ≤ q.ker := by
      simpa only [q,ChapterB.InternalThompsonAction.actionMk,QuotientGroup.ker_mk'] using hEC
    have hEU : U ≤ (S : Subgroup M) :=
      (IsElementaryAbelian.isPGroup 2 U).le_sylow_of_normal S
    have he : IsOffender ρ (E.map q) :=
      NormalElementaryQuotient.maxElementary_isOffender U q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
        (S : Subgroup M) E hEU hE hn'
    have hEC' : E.map q ≤ C := (map_mono (le_sSup hE)).trans hJC
    exact hno ⟨(E.map q).subgroupOf C,he.subgroupOf ρ hEC'⟩
  rw [←hJmap]
  rintro _ ⟨x,hx,rfl⟩ v hv
  have hVM : D.fullModule ≤ M := D.fullModule_le_orbit.trans R.le_normalizer
  exact congrArg M.subtype (hfix hx ⟨v,hVM hv⟩ hv)

/-- The two literal Thompson centralization conditions are equivalent. -/
theorem thompson_centralizes_full_iff_local_of_three
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L)) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) ↔
      elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G) :=
  ⟨fun h => h.trans (centralizer_le (le_componentOrbit D.moduleSubgroup D.maximalLocal)),
    full_thompson_centralizes_of_local_three D hn hd⟩

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
