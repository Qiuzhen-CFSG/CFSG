module
public import Theory.SpecificGroups.Alternating.SevenThreeSection
public import Theory.Representation.BinaryConjugationSection.LinearThreePoint
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.Source
public import CFSG.Quasithin.Chapter10.SourceA5MovedNormalizer.OppositeComponent
public import Theory.SpecificGroups.BinaryComponentResidual.AlternatingSeven
public import Theory.GroupTheory.CComponent.RankTwoResidual
public import CFSG.Quasithin.Chapter10.SourceA5PointA7Transfer
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.ExceptionalAmbient
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.BlockTyping
public import Theory.Representation.BinaryAlternatingSevenControl.Normalizer
public import Stellmacher.ElementaryAbelianMaxJFixedCenter

/-!
# The exceptional A₇ action in the original natural-three row

The opposite natural-three point stabilizer contains an element of order
three that normalizes L and centralizes [V,L]. If I/O₂(I) is A₇, the actual
cubic residual puts this element in I. The smaller image is self-normalizing,
so its faithful action on [V,L] forces that cubic into O₂(I), a contradiction.

For the literal four-dimensional reduced A₇ action, C.1.24 reconstructs the
block and its actual two-core quotient. The original Baumann subgroup and
source uniqueness exclude the characteristic-subgroup alternative. Thus
the final application requires neither a block hypothesis nor an action-kernel
identification. It retains the original orbit and quotient map throughout.

The remaining natural-cover and containing-model recognition belongs to
qt-d-10-nona5-point-constrained. This module does not assert the general
LinearFiveReductionAt or ConstrainedExclusionAt.
Source: Aschbacher--Smith 10.2.9, pp.751--752, and C.1.24, pp.130--131.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

theorem Context.component_core_centralizes_orbit (c : Context D t v I) :
    I.pCoreIn 2 ≤ centralizer (orbitModule D v I : Set G) := by
  have hn : pointJoin T v I ≤ normalizer (I : Set G) :=
    sup_le I.le_normalizer (inf_le_right.trans c.escaping.normalizes)
  have hh := pCoreIn_mono_of_normalizes (p := 2) (show I ≤ pointJoin T v I from le_sup_left) hn
  intro x hx z hz
  obtain ⟨a,ha,rfl⟩ := hh hx
  have hzU : (⟨z,c.orbit_le_join hz⟩ : pointJoin T v I) ∈ internalModule D v I := hz
  exact congrArg Subtype.val ((c.reduced.le_centralizer_pCore hzU) a ha).symm

theorem Context.component_eq_point_residual_of_alternatingSeven (c : Context D t v I)
    (e : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7)) :
    (primeToResidual 3 (centralizer ({v} : Set G))).map
      (centralizer ({v} : Set G)).subtype = I := by
  let X := centralizer ({v} : Set G)
  let K := I.subgroupOf X
  let d : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7) :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe c.escaping.le_centralizer)
      (pCore_map_iso 2 _)).trans e
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple (alternatingGroup (Fin 7)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv d.symm
  have hf := Theory.SpecificGroups.BinaryComponentResidual.Facts.of_equiv d
    Theory.SpecificGroups.BinaryComponentResidual.alternatingSeven
  have hX := D.simpleQTKE.involution_centralizer_sqtk c.point_involution
  have he := c.escaping.component.eq_primeToResidual_three_of_rank_outer_two hf.1 hf.2.1
    (hX.stronglyQuasithin 3 (by decide) (by decide)) hf.2.2
  rw [←he,map_subgroupOf_eq_of_le c.escaping.le_centralizer]

theorem Context.exists_opposite_cubic_of_natural_three (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((specialLinearNatural 3).comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    ∃ y : G, orderOf y = 3 ∧ y ∈ centralizer ({v} : Set G) ∧
      y ∈ normalizer (L : Set G) ∧ y ∈ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  obtain ⟨w,hw,hwt⟩ := c.escaping.v_mem
  let wW : (⁅D.fullModule,L⁆ : Subgroup G) := ⟨w,hw⟩
  have hwne : wW ≠ 1 := by
    intro he
    apply c.escaping.v_ne
    rw [←hwt,show w = 1 from congrArg Subtype.val he,map_one]
  let C := L ⊓ centralizer ({w} : Set G)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hi : (C.subgroupOf L).index = 7 :=
    s.linearThree_pointCentralizer_index q
      (e.surjective.comp (QuotientGroup.mk'_surjective _)) wW hwne
  have hc := (C.subgroupOf L).index_mul_card
  rw [hi,Nat.card_congr (subgroupOfEquivOfLe (show C ≤ L from inf_le_left)).toEquiv] at hc
  have hL : Nat.card L = 168 * Nat.card (pCore 2 L) := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 L),
      Nat.card_congr e.toEquiv, Matrix.PSL3Two.card_SL]
  have hC : Nat.card C = 24 * Nat.card (pCore 2 L) := by omega
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := C) 3
    (by rw [hC]; exact dvd_mul_of_dvd_left (by decide) _)
  let y := (MulAut.conj t) (x : G)
  have hyB : y ∈ L.map (MulAut.conj t).toMonoidHom := mem_map_of_mem _ x.property.1
  refine ⟨y,((MulAut.conj t).orderOf_eq (x : G)).trans ((Subgroup.orderOf_coe x).trans hx),?_,?_,?_⟩
  · apply mem_centralizer_singleton_iff.mpr
    have he := congrArg (MulAut.conj t) (mem_centralizer_singleton_iff.mp x.property.2)
    change (MulAut.conj t) w = v at hwt
    simpa only [map_mul,hwt] using he
  · have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) :=
      fun h => c.escaping.t_not_normalizes (h c.escaping.t_mem)
    apply source_nonnormal_orbit_le_normalizer D hn
    exact (mem_normalizer_iff.mp (le_normalizer_componentOrbit L T c.escaping.t_mem)
      (x : G)).mp ((le_componentOrbit L T) x.property.1)
  · exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (source_a5_moved_normalizer_opposite_cross D c.escaping.t_mem
        c.escaping.t_not_normalizes c.escaping.crossed)) hyB

end CFSG.Quasithin.Chapter10.PointControl.Constrained

namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

private theorem natural_three_normalizing_cubic_impossible (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((specialLinearNatural 3).comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (E : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7))
    {y : G} (hy : y ∈ I) (hy3 : orderOf y = 3)
    (hyn : y ∈ normalizer (L : Set G))
    (hyc : y ∈ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G)) : False := by
  let A := L.subgroupOf I
  let a : A ≃* L := subgroupOfEquivOfLe c.escaping.strict.le
  let eA : (A ⧸ pCore 2 A) ≃* SL(3,ZMod 2) :=
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e
  let f := E.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  have hk : IsPGroup 2 (f.subgroupMap A).ker := by
    let j : (f.subgroupMap A).ker →* pCore 2 I :=
      (A.subtype.comp (f.subgroupMap A).ker.subtype).codRestrict _ (fun x => by
        apply (QuotientGroup.eq_one_iff _).mp
        apply E.map_eq_one_iff.mp
        exact congrArg Subtype.val x.property)
    exact pCore_isPGroup.of_injective j (fun x z h => Subtype.ext (Subtype.ext
      (congrArg (fun k : pCore 2 I => (k : I)) h)))
  have hker := (alternatingGroup.SevenThreeSection.image_twoCore_eq_bot_and_ker_eq f A hk eA).2
  have hnorm := alternatingGroup.SevenThreeSection.image_normalizer_eq f A hk eA
  let yI : I := ⟨y,hy⟩
  have hynA : yI ∈ normalizer (A : Set I) := fun l => hyn (l : G)
  have hyf : f yI ∈ A.map f := hnorm ▸
    (A.le_normalizer_map f (mem_map_of_mem f hynA))
  obtain ⟨l,hl,hel⟩ := hyf
  have hyl : yI * l⁻¹ ∈ pCore 2 I := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply E.map_eq_one_iff.mp
    change f (yI * l⁻¹) = 1
    rw [map_mul,map_inv,hel,mul_inv_cancel]
  have hspan := c.moved_le_of_natural_three e s
  have hkc : (yI * l⁻¹ : I).val ∈ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) :=
    centralizer_le hspan (c.component_core_centralizes_orbit (mem_map_of_mem I.subtype hyl))
  have hlc : (l : G) ∈ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
    have hh := (centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G)).mul_mem
      ((centralizer _).inv_mem hkc) hyc
    simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_inv_rev,inv_inv,inv_mul_cancel_right,yI] using hh
  have hlcore : (⟨l,hl⟩ : A) ∈ pCore 2 A := by
    have hh := s.linearThree_centralizer_le_kernel
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) (l := a ⟨l,hl⟩) hlc
    have hlL : a ⟨l,hl⟩ ∈ pCore 2 L :=
      (QuotientGroup.eq_one_iff _).mp (e.map_eq_one_iff.mp hh)
    rw [←pCore_map_iso 2 a] at hlL
    exact (mem_map_equiv).mp hlL
  have hfyl : f yI = 1 := by
    rw [←hel]
    have hm : (⟨l,hl⟩ : A) ∈ (f.subgroupMap A).ker := hker.symm ▸ hlcore
    exact congrArg Subtype.val (show (f.subgroupMap A) ⟨l,hl⟩ = 1 from hm)
  have hycore : yI ∈ pCore 2 I :=
    (QuotientGroup.eq_one_iff _).mp (E.map_eq_one_iff.mp hfyl)
  have hyorder : orderOf (⟨yI,hycore⟩ : pCore 2 I) = 3 :=
    (Subgroup.orderOf_coe _).symm.trans ((Subgroup.orderOf_coe yI).symm.trans hy3)
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := I)).exists_card_eq
  have hd := orderOf_dvd_natCard (⟨yI,hycore⟩ : pCore 2 I)
  rw [hyorder,hn] at hd
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

/-- The original natural-three row cannot have an actual A₇ two-core quotient. -/
theorem Context.no_alternatingSeven_of_natural_three (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((specialLinearNatural 3).comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (E : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7)) : False := by
  obtain ⟨y,hy3,hyv,hyn,hyc⟩ := c.exists_opposite_cubic_of_natural_three e s
  have hyI : y ∈ I := by
    rw [←c.component_eq_point_residual_of_alternatingSeven E]
    apply mem_map_of_mem (centralizer ({v} : Set G)).subtype (x := ⟨y,hyv⟩)
    apply mem_primeToResidual_of_pow (n := 1)
    apply Subtype.ext
    change y ^ (3 ^ 1) = 1
    simpa only [pow_one,hy3] using pow_orderOf_eq_one y
  exact natural_three_normalizing_cubic_impossible c e s E hyI hy3 hyn hyc

end CFSG.Quasithin.Chapter10.PointControl.Constrained


open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}
private theorem point_baumann_eq {v : G} (hvT : v ∈ (T : Subgroup G))
    (hv2 : v ^ 2 = 1)
    (hJP : elementaryAbelianMaxJ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) =
      elementaryAbelianMaxJ (T : Subgroup G)) :
    ChapterB.baumann ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) =
      ChapterB.baumann (T : Subgroup G) := by
  let : IsElementaryAbelian 2 (zpowers v) := IsElementaryAbelian.zpowers_of_pow_eq_one hv2
  have hvC : v ∈ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
    intro j hj
    have hJle : elementaryAbelianMaxJ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) ≤
        (T : Subgroup G) ⊓ centralizer ({v} : Set G) := sSup_le fun _ hA => hA.1
    have hjP := hJle (hJP.symm ▸ hj)
    exact (mem_centralizer_singleton_iff.mp hjP.2)
  have hvZ := elementary_centralizer_maxJ_le_omegaCenter (T : Subgroup G) (zpowers v)
    (zpowers_le.mpr hvT) (zpowers_le.mpr hvC) (mem_zpowers v)
  have hBC : ChapterB.baumann (T : Subgroup G) ≤ centralizer ({v} : Set G) := by
    intro b hb
    exact mem_centralizer_singleton_iff.mpr ((show b ∈ centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (T : Subgroup G)) : Set G) from hb.2) v hvZ).symm
  exact baumann_eq_of_intermediate _ _ (le_inf inf_le_left hBC) inf_le_left

private theorem no_point_characteristic
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (I H : Subgroup G) (hLI : L ≤ I) (hIH : I ≤ H) (hout : ¬ I ≤ D.maximalLocal)
    (P : Sylow 2 H)
    (hb : (ChapterB.baumann (P : Subgroup H)).map H.subtype = ChapterB.baumann (T : Subgroup G))
    (R : Subgroup (ChapterB.baumann (P : Subgroup H)))
    (hchar : R.Characteristic) (hne : R ≠ ⊥)
    (hn : (R.map (ChapterB.baumann (P : Subgroup H)).subtype).Normal) : False := by
  let B := ChapterB.baumann (P : Subgroup H)
  let B0 := ChapterB.baumann (T : Subgroup G)
  let e : B ≃* B0 := (B.equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr hb)
  let R0 := R.map e.toMonoidHom
  let : R0.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    obtain ⟨y,hy,rfl⟩ := hx
    refine ⟨(MulAut.congr e.symm a) y,
      characteristic_iff_le_comap.mp hchar (MulAut.congr e.symm a) hy, ?_⟩
    exact e.apply_symm_apply (a (e y))
  have he : R0.map B0.subtype = (R.map B.subtype).map H.subtype := by
    rw [map_map,map_map]
    rfl
  have hN : I ≤ normalizer (R0.map B0.subtype : Set G) := by
    rw [he]
    have hN := (R.map B.subtype).le_normalizer_map H.subtype
    have hn' : normalizer (R.map B.subtype : Set H) = ⊤ := @normalizer_eq_top _ _ _ hn
    rw [hn',←MonoidHom.range_eq_map,range_subtype] at hN
    exact hIH.trans hN
  have hz := source_overgroup_characteristic_baumann_eq_bot D I hLI hout R0 hN
  exact hne ((map_eq_bot_iff_of_injective R e.injective).mp hz)

/-- The actual exceptional four-space action reconstructs the original A₇ head. -/
theorem Context.alternatingSeven_quotient_of_four_action (c : Context D t v I)
    (af : ActionFacts c) (hspan : ⁅D.fullModule,L⁆ ≤ orbitModule D v I)
    (e : letI := c.reduced.normal
      ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))) ≃*
        alternatingGroup (Fin 7))
    (hd : letI := c.reduced.elementary
      Module.finrank (ZMod 2) (Additive (internalModule D v I)) = 4) :
    Nonempty ((I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7)) := by
  let H := pointJoin T v I
  let K := I.subgroupOf H
  let V := orbitModule D v I
  let U := internalModule D v I
  let := c.reduced.normal
  let := c.reduced.elementary
  have hHX : H ≤ centralizer ({v} : Set G) := sup_le c.escaping.le_centralizer inf_le_right
  have hK : K.IsCComponent := c.escaping.component.subgroupOf_of_le le_sup_left hHX
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hHX.trans c.escaping.normalizes)
  let d : K ≃* I := subgroupOfEquivOfLe le_sup_left
  let A := K.map (actionMk U)
  let : A.Normal := Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hAtop : A = ⊤ := BinaryAlternatingSevenControl.normal_alternatingSeven_eq_top
    (action U) af.classification.2.2.2.2.1 hd A e
  let dQ : ActionQuotient U ≃* alternatingGroup (Fin 7) :=
    (topEquiv.symm.trans (MulEquiv.subgroupCongr hAtop.symm)).trans e
  let q := dQ.toMonoidHom.comp (actionMk U)
  have hq : Function.Surjective q := dQ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = centralizer (U : Set H) := by
    ext x
    change dQ (actionMk U x) = 1 ↔ _
    rw [dQ.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hKq : K.map q = ⊤ := by
    change K.map (dQ.toMonoidHom.comp (actionMk U)) = ⊤
    rw [←map_map,show K.map (actionMk U) = ⊤ from hAtop]
    exact map_top_of_surjective _ dQ.surjective
  let : IsQuasisimple (I ⧸ pCore 2 I) := source_a5_point_a7_head_quasisimple D
    c.point_involution I c.escaping.le_centralizer c.escaping.component c.reduced e
  let : IsQuasisimple (K ⧸ pCore 2 K) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).symm
  have hCW : centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal :=
    (Subgroup.centralizer_le_normalizer _).trans c.escaping.moved_normalizer
  have hv : v ∈ D.fullModule := partner_le_fullModule D c.escaping.t_mem c.escaping.v_mem
  have ho := source_a5_point_centralizer_oddCore_eq_bot D hv c.escaping.v_ne
    (c.escaping.crossed c.escaping.v_mem) hCW
  have hfI : generalizedFitting I = pCore 2 I := by
    let dX := subgroupOfEquivOfLe c.escaping.le_centralizer
    rcases c.escaping.component.component_or_generalizedFitting_eq_pCore ho with h | h
    · let := h.2
      exact (c.not_quasisimple (IsQuasisimple.of_mulEquiv dX)).elim
    · have hh := congrArg (Subgroup.map dX.toMonoidHom) h
      rwa [map_generalizedFitting_equiv,pCore_map_iso] at hh
  have hfK : generalizedFitting K = pCore 2 K := by
    have hh := congrArg (Subgroup.map d.symm.toMonoidHom) hfI
    rwa [map_generalizedFitting_equiv,pCore_map_iso] at hh
  obtain ⟨P,hP⟩ := c.join_sylow
  have hP' : (P : Subgroup H) = (pointSylow T v).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le (show pointSylow T v ≤ H from le_sup_right)]
  have hKP : K ⊔ (P : Subgroup H) = ⊤ := by
    rw [hP',←subgroupOf_sup (show I ≤ H from le_sup_left)
      (show pointSylow T v ≤ H from le_sup_right)]
    exact subgroupOf_self H
  have hprod : ∀ g : H, ∃ k ∈ K, ∃ s ∈ (P : Subgroup H), k*s=g := by
    intro g
    exact mem_sup_of_normal_left.mp (hKP.symm ▸ mem_top g)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) D.simpleQTKE T D.maximal
  have hvT := D.fullModule_le_sylow hu hv
  have hv2 : v ^ 2 = 1 := by simpa only [c.point_involution] using pow_orderOf_eq_one v
  have hb : (ChapterB.baumann (P : Subgroup H)).map H.subtype = ChapterB.baumann (T : Subgroup G) := by
    have hh := baumann_map_injective H.subtype H.subtype_injective (P : Subgroup H)
    change (ChapterB.baumann (P : Subgroup H)).map H.subtype =
      ChapterB.baumann ((P : Subgroup H).map H.subtype) at hh
    rw [hP] at hh
    exact hh.trans (point_baumann_eq hvT hv2 af.prepared.thompson_eq)
  have hmV : ⁅V,I⁆ = V := (source_a5_point_action_marking D I c.escaping.strict.le
    c.escaping.escapes hCW hspan c.reduced).1
  have hm : ⁅U,K⁆ = U := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le c.orbit_le_join,
      map_subgroupOf_eq_of_le (show I ≤ H from le_sup_left)]
    exact hmV
  have hne : U ≠ ⊥ := by
    intro hz
    have hh := congrArg (Subgroup.map H.subtype) hz
    have hzV : V = ⊥ := by
      change (V.subgroupOf H).map H.subtype = (⊥ : Subgroup H).map H.subtype at hh
      have hVH : V ≤ H := c.orbit_le_join
      rwa [map_subgroupOf_eq_of_le hVH,Subgroup.map_bot] at hh
    exact source_full_moved_ne_bot D (le_bot_iff.mp (hspan.trans_eq hzV))
  have hblock : ChapterC.IsBlock K :=
    (ChapterC.RankOne.SevenSource.normal_characteristic_or_block_of_exceptional_seven
      K U hK c.characteristic_two hfK P hprod q hq hk hKq hd (hm.symm ▸ hne)).resolve_left (by
        rintro ⟨R,hchar,hneR,hn⟩
        exact no_point_characteristic D I H c.escaping.strict.le le_sup_left c.escaping.escapes
          P hb R hchar hneR hn)
  let eqK := (ChapterC.RankOne.SevenSource.coreQuotientEquiv_of_full_moved K U hblock hne hm q hk).trans
    ((MulEquiv.subgroupCongr hKq).trans topEquiv)
  exact ⟨(QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).symm.trans eqK⟩

end CFSG.Quasithin.Chapter10.PointControl.Constrained

namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The literal four-dimensional A₇ action is impossible in the original
natural-three row. C.1.24 supplies its kernel; no block or kernel premise remains. -/
theorem Context.no_four_alternatingSeven_action_of_natural_three (c : Context D t v I)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (s : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((specialLinearNatural 3).comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (E : letI := c.reduced.normal
      ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))) ≃*
        alternatingGroup (Fin 7))
    (hd : letI := c.reduced.elementary
      Module.finrank (ZMod 2) (Additive (internalModule D v I)) = 4) : False := by
  obtain ⟨d⟩ := c.alternatingSeven_quotient_of_four_action
    (c.actionFacts_of_natural_three e s) (c.moved_le_of_natural_three e s) E hd
  exact c.no_alternatingSeven_of_natural_three e s d

end CFSG.Quasithin.Chapter10.PointControl.Constrained
