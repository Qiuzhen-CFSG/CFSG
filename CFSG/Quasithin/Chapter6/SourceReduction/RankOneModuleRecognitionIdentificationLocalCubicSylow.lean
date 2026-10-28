module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFieldKernel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFieldComponents
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.BorelStructure
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.GeneralizedFitting.SylowNormalizedComponent

/-!
# The original cubic and centralizer Sylow in source 6.2.7

Let U be the field plane, H = C_G(U), and D = O²(N_L(U)). The arranged
Sylow S of H normalizes D. Since D ∩ H = O₂(D), its intersection with H
lies in S; hence D normalizes S. The full ambient normalizer of this same
S lies in M.

The component orbit bound makes the original cubic normalize every
C-component with quasisimple two-core quotient. When that quotient is
PSL₃(2), its actual Sylow intersection is preserved. The outer automorphism
group is a two-group and the Sylow is self-normalizing, so the cubic acts
trivially on the quotient. The compatible component lift then proves
commutation on the original marked linear action, for every PSL₃(2)
action component.

This supplies the group-action step used in both PSL₃(2) paragraphs of
6.2.7. Triviality on their moved modules and the remaining model exclusions
are still required. The companion Chapter12 module retains the original
cubic, quotient coordinates and three-subgroups noncentrality claim.

Source: Aschbacher--Smith, 6.2.4(2,5), 6.2.7, printed pp.680,683,
and the component orbit bound 1.2.1(3), printed p.504.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem residual_normalizes_centralizer_sylow
    (D H : Subgroup G) (S : Sylow 2 H)
    (hDH : D ≤ normalizer (H : Set G))
    (hSD : (S : Subgroup H).map H.subtype ≤ normalizer (D : Set G))
    (hcore : D.pCoreIn 2 = D ⊓ H) :
    D ≤ normalizer ((S : Subgroup H).map H.subtype : Set G) := by
  let Q := D ⊓ H
  let R := (S : Subgroup H).map H.subtype
  have hRQ : R ≤ normalizer (Q : Set G) :=
    (le_inf hSD ((map_subtype_le _).trans H.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hp : IsPGroup 2 Q := by
    change IsPGroup 2 (D ⊓ H : Subgroup G)
    rw [←hcore]
    exact isPGroup_pCoreIn 2 D
  have hQH : Q ≤ H := inf_le_right
  have hn : (S : Subgroup H) ≤ normalizer (Q.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hQH]
    intro s hs
    exact hRQ (mem_map_of_mem H.subtype hs)
  have hQR : Q ≤ R := by
    have hh := map_mono (f := H.subtype)
      ((hp.comap_subtype (K := H)).le_sylow_of_normalized S hn)
    change (Q.subgroupOf H).map H.subtype ≤ R at hh
    rwa [map_subgroupOf_eq_of_le hQH] at hh
  apply le_normalizer_iff_commutator_le_right.mpr
  apply le_trans _ hQR
  apply le_inf
  · exact le_normalizer_iff_commutator_le_left.mp hSD
  · exact (commutator_mono le_rfl (map_subtype_le _)).trans
      (le_normalizer_iff_commutator_le_right.mp hDH)

/-- The actual plane-normalizer residual preserves a centralizer Sylow whose
full ambient normalizer lies in the original maximal subgroup. -/
theorem local_field_residual_sylow
    {T : Sylow 2 G} {L M R U : Subgroup G} {n : ℕ}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfield : IsInvolutoryFieldFixedSpace L M (layer L R) U n)
    (hUc : Nat.card U = 4) :
    ∃ S : Sylow 2 (centralizer (U : Set G)),
      layer L R ≤ (S : Subgroup (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype ∧
      fieldLocalResidual L U ≤ normalizer
        ((S : Subgroup (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype : Set G) ∧
      normalizer ((S : Subgroup (centralizer (U : Set G))).map
        (centralizer (U : Set G)).subtype : Set G) ≤ M := by
  let := h.layer_elementary
  let B := layer L R
  let H := centralizer (U : Set G)
  let D := fieldLocalResidual L U
  have hnat : IsNaturalModule L B n := hnatural.1 ▸ hnatural.2.1
  have hUne : U ≠ ⊥ := by intro he; rw [he,card_bot] at hUc; contradiction
  have hUB : U ≤ B := hfield.choose_spec.2.2.1.le.trans inf_le_left
  have hBH : B ≤ H := B.le_centralizer.trans (centralizer_le hUB)
  have hML := (normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal
  obtain ⟨P,_,hBP,hPL,hPB,_,hSyl⟩ := field_fixedSpace_sylow_arrangement
    T L M B U n h.sylow_normalizes_layer hE.normalizer_le hML hE.ti hnat hfield hUne
  obtain ⟨_,hJM,_,S,hS⟩ := field_fixedSpace_sylow_control hE
    (by have := h.n_gt_one; omega) hnat hML hfield hUne P hBP hPB hSyl
  have hSH : (S : Subgroup H).map H.subtype ≤ H := map_subtype_le _
  have hSU : (S : Subgroup H).map H.subtype ≤ normalizer (U : Set G) :=
    hSH.trans (Subgroup.centralizer_le_normalizer _)
  have hSL : (S : Subgroup H).map H.subtype ≤ normalizer (L : Set G) := by
    rw [hS]
    exact inf_le_left.trans hPL
  have hSD : (S : Subgroup H).map H.subtype ≤ normalizer (D : Set G) :=
    ((le_inf hSL (hSU.trans (normalizer (U : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image
        (L ⊓ normalizer (U : Set G)) (pResidual 2 (L ⊓ normalizer (U : Set G) : Subgroup G)))
  have hDU : D ≤ normalizer (U : Set G) := (map_subtype_le _).trans inf_le_right
  refine ⟨S,?_,residual_normalizes_centralizer_sylow D H S
    (hDU.trans (normalizer_le_normalizer_centralizer U)) hSD
    (field_plane_residual_structure hnat hfield hUc).1,?_⟩
  · rw [hS]
    exact le_inf hBP hBH
  · rw [hS]
    exact (normalizer_le_normalizer_elementaryAbelianMaxJ _).trans hJM

private theorem cubic_aut_eq_one_of_sylow
    {X : Type*} [Group X] [Finite X]
    (hz : center X = ⊥) (hout : IsPGroup 2 (MulAut.Outer X))
    (S : Sylow 2 X) (hself : normalizer (S : Set X) = (S : Subgroup X))
    (a : MulAut X) (ha : a ^ 3 = 1)
    (hS : (S : Subgroup X).map a.toMonoidHom = (S : Subgroup X)) : a = 1 := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup X)
  have hq : q a = 1 := by
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes
      (hout.orderOf_coprime (by decide : Nat.Coprime 2 3) (q a)) dvd_rfl
      (orderOf_dvd_of_pow_eq_one (by rw [←map_pow,ha,map_one]))
  obtain ⟨x,hx⟩ := (QuotientGroup.eq_one_iff a).mp hq
  have hx3 : x ^ 3 = 1 := (MulAut.conj_injective_of_center_eq_bot hz) (by
    rw [map_pow,hx,ha,map_one])
  have hxS : x ∈ S := by
    change x ∈ (S : Subgroup X)
    rw [←hself]
    apply mem_normalizer_iff_map_conj_eq.mpr
    rwa [hx]
  have hx1 : (⟨x,hxS⟩ : (S : Subgroup X)) = 1 := by
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes
      (S.isPGroup'.orderOf_coprime (by decide : Nat.Coprime 2 3) ⟨x,hxS⟩) dvd_rfl
      (orderOf_dvd_of_pow_eq_one (Subtype.ext hx3))
  have hxone : x = 1 := congrArg Subtype.val hx1
  rw [←hx,hxone,map_one]

private theorem binary_three_cubic_aut
    {X : Type*} [Group X] [Finite X]
    (e : X ≃* PSL(3,ZMod 2)) (S : Sylow 2 X)
    (a : MulAut X) (ha : a ^ 3 = 1)
    (hS : (S : Subgroup X).map a.toMonoidHom = (S : Subgroup X)) : a = 1 := by
  let eSL := e.trans Matrix.PSL3Two.equiv.symm
  have hz : center X = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hx1 : eSL x = 1 := Matrix.PSL3Two.center_eq_bot.le ((centerCongr eSL) ⟨x,hx⟩).property
    exact eSL.map_eq_one_iff.mp hx1
  have hout : IsPGroup 2 (MulAut.Outer X) :=
    Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup.of_equiv (MulAut.outerCongr eSL).symm
  have hself : normalizer (S : Set X) = (S : Subgroup X) := by
    apply map_injective (f := e.toMonoidHom) e.injective
    exact (map_equiv_normalizer_eq (S : Subgroup X) e).trans
      (Matrix.PSL3.LinearThree.BorelStructure.normalizer_eq_self_of_card_two
        (ZMod 2) (Nat.card_zmod 2) (S.mapSurjective (f := e.toMonoidHom) e.surjective))
  exact cubic_aut_eq_one_of_sylow hz hout S hself a ha hS

private theorem cComponent_normalized_by_cubic
    {X : Type*} [Group X] [Finite X] (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (K : Subgroup X) (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (d : X) (hd : d ^ 3 = 1) : d ∈ normalizer (K : Set X) := by
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  let q := QuotientGroup.mk' (pCore 2 X)
  let J := K.map q
  let e : (K ⧸ pCore 2 K) ≃* J := cComponentTwoCoreQuotientEquiv hK
  let : IsQuasisimple J := IsQuasisimple.of_mulEquiv e
  have hJ : IsComponent (X ⧸ pCore 2 X) J :=
    ⟨(hK.map_quotient (pCore 2 X)).subnormal,inferInstance⟩
  have hcases := cComponent_normal_or_index_two_of_quotient hK (pCore 2 X)
    (hJ.normal_or_index_two_of_odd_rank_le_two (by
      intro p hp ho
      let : Fact p.Prime := ⟨hp⟩
      exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 X) pCore_isPGroup).trans
        (hX.stronglyQuasithin p hp ho)))
  rcases hcases with hn | hi
  · exact normalizer_eq_top_iff.mpr hn ▸ mem_top d
  · have hs := (normalizer (K : Set X)).sq_mem_of_index_two hi d
    have hc : Nat.Coprime (orderOf d) 2 :=
      (by decide : Nat.Coprime 3 2).of_dvd_left (orderOf_dvd_of_pow_eq_one hd)
    exact (zpowers_le.mpr hs) (mem_zpowers_pow_iff.mpr hc.symm)

/-- The original cubic restricts to an automorphism of each component with
quasisimple two-core quotient; its ambient conjugation formula is retained. -/
theorem local_field_cubic_component_action
    {T : Sylow 2 G} {L M R U : Subgroup G} {n : ℕ}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hfield : IsInvolutoryFieldFixedSpace L M (layer L R) U n)
    (hUc : Nat.card U = 4)
    (K : Subgroup (centralizer (U : Set G))) (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (d : G) (hd : d ∈ fieldLocalResidual L U) (hd3 : d ^ 3 = 1) :
    ∃ a : MulAut K, a ^ 3 = 1 ∧
      ∀ k : K, ((a k : centralizer (U : Set G)) : G) =
        d * ((k : centralizer (U : Set G)) : G) * d⁻¹ := by
  let H := centralizer (U : Set G)
  let N := normalizer (U : Set G)
  let j : H →* N := inclusion (Subgroup.centralizer_le_normalizer _)
  let K0 := K.map j
  let e : K ≃* K0 := K.equivMapOfInjective j (inclusion_injective _)
  let eq : (K ⧸ pCore 2 K) ≃* (K0 ⧸ pCore 2 K0) :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let : IsQuasisimple (K0 ⧸ pCore 2 K0) := IsQuasisimple.of_mulEquiv eq
  have hK0 : K0.IsCComponent := by
    let H0 := H.subgroupOf N
    have hHN : H ≤ N := Subgroup.centralizer_le_normalizer _
    let : H0.Normal := normal_subgroupOf_of_le_normalizer (normalizer_le_normalizer_centralizer U)
    let f : H ≃* H0 := (subgroupOfEquivOfLe hHN).symm
    have hm := (hK.map_equiv f).map_subtype (inferInstance : H0.Normal).isSubnormal
    rw [map_map] at hm
    exact hm
  let x : N := ⟨d,(map_subtype_le _ hd).2⟩
  have hx3 : x ^ 3 = 1 := Subtype.ext hd3
  have hUne : U ≠ ⊥ := by intro he; rw [he,card_bot] at hUc; contradiction
  have hxK := cComponent_normalized_by_cubic (local_field_normalizer_sqtk h hfield hUne)
    K0 hK0 x hx3
  let y : normalizer (K0 : Set N) := ⟨x,hxK⟩
  let b := K0.normalizerMonoidHom y
  let a : MulAut K := MulAut.congr e.symm b
  have hb3 : b ^ 3 = 1 := by
    rw [←map_pow,show y ^ 3 = 1 from Subtype.ext hx3,map_one]
  refine ⟨a,?_,?_⟩
  · change (MulAut.congr e.symm b) ^ 3 = 1
    rw [←map_pow,hb3,map_one]
  · intro k
    have he : e (a k) = b (e k) := by simp [a]
    have hv := congrArg (fun z : K0 => ((z : N) : G)) he
    exact hv

/-- The original cubic acts trivially on an intrinsic PSL₃(2) component
quotient, using the actual Sylow intersection. -/
theorem local_field_binary_component_cubic
    {T : Sylow 2 G} {L M R U : Subgroup G} {n : ℕ}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfield : IsInvolutoryFieldFixedSpace L M (layer L R) U n)
    (hUc : Nat.card U = 4)
    (K : Subgroup (centralizer (U : Set G))) (hK : K.IsCComponent)
    (e : (K ⧸ pCore 2 K) ≃* PSL(3,ZMod 2))
    (d : G) (hd : d ∈ fieldLocalResidual L U) (hd3 : d ^ 3 = 1) :
    ∃ a : MulAut K, quotientAut (pCore 2 K) a = 1 ∧
      ∀ k : K, ((a k : centralizer (U : Set G)) : G) =
        d * ((k : centralizer (U : Set G)) : G) * d⁻¹ := by
  let H := centralizer (U : Set G)
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv
    (e.trans Matrix.PSL3Two.equiv.symm).symm
  obtain ⟨a,ha3,ha⟩ := local_field_cubic_component_action h hfield hUc K hK d hd hd3
  obtain ⟨S,_,hDS,_⟩ := local_field_residual_sylow h hnatural hE hfield hUc
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_subnormal K hK.subnormal
  have haP : (P : Subgroup K).map a.toMonoidHom = (P : Subgroup K) := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨k,hk,rfl⟩
      rw [hP] at hk ⊢
      apply (mem_map_iff_mem H.subtype_injective).mp
      change ((a k : H) : G) ∈ (S : Subgroup H).map H.subtype
      rw [ha]
      exact (mem_normalizer_iff.mp (hDS hd) ((k : H) : G)).mp
        (mem_map_of_mem H.subtype hk)
    · rw [card_map_of_injective a.injective]
  let q := QuotientGroup.mk' (pCore 2 K)
  let Q := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let b := quotientAut (pCore 2 K) a
  have hb3 : b ^ 3 = 1 := by rw [←map_pow,ha3,map_one]
  have hbQ : (Q : Subgroup (K ⧸ pCore 2 K)).map b.toMonoidHom = (Q : Subgroup (K ⧸ pCore 2 K)) := by
    change ((P : Subgroup K).map q).map b.toMonoidHom = (P : Subgroup K).map q
    rw [map_map]
    have hc : b.toMonoidHom.comp q = q.comp a.toMonoidHom := by
      ext k
      exact quotientAut_apply_mk _ a k
    rw [hc,←map_map,haP]
  exact ⟨a,binary_three_cubic_aut e Q b hb3 hbQ,ha⟩

namespace LocalFieldQuotientAction
/-- Centralization on every actual PSL₃(2) action component, in any extension
of the original faithful-action marking to the field-plane residual. -/
theorem binary_component_cubic_commutes
    {T : Sylow 2 G} {L M R U : Subgroup G} {n : ℕ}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N → N = M)
    (hfield : IsInvolutoryFieldFixedSpace L M (layer L R) U n)
    (hUc : Nat.card U = 4)
    (hout : ¬ Centralizer U ≤ normalizer (layer L R : Set G))
    (J : Subgroup (action (layer L R) U).range) (hJ : IsComponent _ J)
    (e : J ≃* PSL(3,ZMod 2))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (action (layer L R) U).range W)
    (η : Representation (ZMod 2) (Centralizer U ⊔ fieldLocalResidual L U : Subgroup G) W)
    (hrestrict : ∀ k : Centralizer U, η (inclusion le_sup_left k) =
      ρ ((action (layer L R) U).rangeRestrict k))
    (d : G) (hd : d ∈ fieldLocalResidual L U) (hd3 : d ^ 3 = 1) :
    ∀ j : J, Commute (η.asGroupHom ⟨d,mem_sup_right hd⟩) (ρ.asGroupHom j) := by
  let H := Centralizer U
  let P := H ⊔ fieldLocalResidual L U
  let π := (action (layer L R) U).rangeRestrict
  obtain ⟨K,hK,_,eK,heK⟩ := action_component_lift h hnatural hE hfactor hu hfield hUc hout J hJ
  obtain ⟨a,haq,ha⟩ := local_field_binary_component_cubic h hnatural hE hfield hUc
    K hK (eK.trans e) d hd hd3
  let q := QuotientGroup.mk' (pCore 2 K)
  have hπ (k : K) : π (a k) = π k := by
    have hq : q (a k) = q k := by
      have hh := congrArg (fun b : MulAut (K ⧸ pCore 2 K) => b (q k)) haq
      simpa only [q,quotientAut_apply_mk,MulAut.one_apply] using hh
    rw [←heK (a k),←heK k,hq]
  have hr (k : H) : η.asGroupHom (inclusion le_sup_left k) = ρ.asGroupHom (π k) :=
    Units.ext (hrestrict k)
  intro j
  obtain ⟨k,hk⟩ := QuotientGroup.mk'_surjective (pCore 2 K) (eK.symm j)
  have hkj : π k = (j : (action (layer L R) U).range) := by
    rw [←heK k,hk,eK.apply_symm_apply]
  let x : P := ⟨d,mem_sup_right hd⟩
  have hap : inclusion (show H ≤ P from le_sup_left) (a k : H) =
      x * inclusion le_sup_left (k : H) * x⁻¹ := Subtype.ext (ha k)
  have hc : η.asGroupHom x * ρ.asGroupHom (π k) * (η.asGroupHom x)⁻¹ =
      ρ.asGroupHom (π k) := by
    calc
      _ = η.asGroupHom (x * inclusion le_sup_left (k : H) * x⁻¹) := by
        rw [map_mul,map_mul,map_inv,hr]
      _ = ρ.asGroupHom (π (a k)) := by rw [←hap,hr]
      _ = ρ.asGroupHom (π k) := congrArg ρ.asGroupHom (hπ k)
  rw [hkj] at hc
  exact mul_inv_eq_iff_eq_mul.mp hc

/-- The original cubic section, with its marking and noncentrality claim,
augmented by centralization of every actual PSL₃(2) action component. -/
@[expose] def CubicBinarySection (L B A U : Subgroup G)
    [IsElementaryAbelian 2 (space B U)] : Prop :=
    let H := LocalFieldQuotientAction.Centralizer U
    let J := conjugateSpanBy B H
    let P := H ⊔ fieldLocalResidual L U
    let W := Additive (LocalFieldQuotientAction.space B U)
    let π := (LocalFieldQuotientAction.action B U).rangeRestrict
    let I := (A.subgroupOf H).map π
    ∃ (ρ : Representation (ZMod 2) (LocalFieldQuotientAction.action B U).range W)
      (c : BinaryConjugationSection H J U (ρ.comp π)),
      Function.Injective ρ ∧ IsOffender ρ I ∧ Nat.card I = 4 ∧
      ∃ (d : G) (hd : d ∈ fieldLocalResidual L U), orderOf d = 3 ∧ ⁅B,zpowers d⁆ = B ∧
        ∃ (η : Representation (ZMod 2) P W) (c' : BinaryConjugationSection P J U η),
          c'.coordinates = c.coordinates ∧
          (∀ a : H, η (inclusion le_sup_left a) = ρ (π a)) ∧
          (∃ hd : d ∈ P, orderOf (η.asGroupHom ⟨d,hd⟩) = 3) ∧
          (∀ K : Subgroup G, A ≤ K → K ≤ H →
            (⁅K,zpowers d⁆.subgroupOf P).map η.asGroupHom = ⊥ →
            c'.imageSpace ⁅⁅J,K⁆,zpowers d⁆ ≠ ⊥) ∧
          (∀ j : J, ∃ hj : (j : G) ∈ H, LocalFieldQuotientAction.projection U ⟨j,hj⟩ =
            ((c'.coordinates j).toAdd.toMul : LocalFieldQuotientAction.Ambient U)) ∧
          ∀ K : Subgroup (LocalFieldQuotientAction.action B U).range, IsComponent _ K →
            Nonempty (K ≃* PSL(3,ZMod 2)) → ∀ k : K,
              Commute (η.asGroupHom ⟨d,mem_sup_right hd⟩)
                (ρ.asGroupHom k)
end LocalFieldQuotientAction

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
