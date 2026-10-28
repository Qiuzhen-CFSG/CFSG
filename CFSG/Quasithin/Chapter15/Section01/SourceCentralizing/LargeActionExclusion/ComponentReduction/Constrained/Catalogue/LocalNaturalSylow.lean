module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalNaturalIntersection
public import Theory.GroupTheory.CoprimeFixedDisplacement
public import Theory.GroupTheory.Commutator.CoprimeQuadratic

/-!
# Sylow normalization of the remaining natural local member

The natural Borel acts nontrivially on V. Its image is therefore the whole
original prime-order residual, and its displacement on V is invariant under
M intersect G₁. In particular S preserves that displacement. If an element
of S moved K to a distinct block, the displacement would lie in both blocks.
Distinct short blocks commute, so every odd subgroup of the Borel would act
quadratically on V and hence trivially. The full-cover Sylow/odd-subgroup
fixer theorem would then put K in M_Z, a contradiction. Thus S normalizes K;
this is proved from the original hypotheses, not assumed.

The actual S-orbit Borel consequently equals B_K. In the literal local
group K S, the marked intersection and the normalizer of the original Q₁
are both exactly S. The actual-marker consumer combines these identities
with the cubic field-four restriction and retains both source primes.

This still does not prove B_K ≤ M_Z or M_Z-invariance of B_K. The remaining
natural exclusion and original 15.1.20(2)/15.1.22 assembly stay open.
Original 15.1.14 and whole-core A₆ reconstruction retain their independent
producers and final assembly owners.

Source: Aschbacher--Smith 15.1.16--20 and the natural-block argument in
15.1.21(i), printed pp.1092--1095 and 1097--1098; C.1.9 for block commutation.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem marked_prime_displacement
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hVC : V ≤ M ⊓ d.G1) {B : Subgroup G} (hBC : B ≤ M ⊓ d.G1)
    (hpB : IsPPerfect 2 B) (hne : ¬ B ≤ centralizer (V : Set G)) (hp2 : p ≠ 2) :
    M ⊓ d.G1 ≤ normalizer (⁅V,B⁆ : Subgroup G) ∧
      ∀ P : Subgroup G, P ≤ B → IsPGroup 2 P → P ≤ centralizer (V : Set G) := by
  let C := M ⊓ d.G1
  let V0 := V.subgroupOf C
  let B0 := B.subgroupOf C
  let N := (M ⊓ centralizer (V : Set G)).subgroupOf C
  let : N.Normal := caseI_module_centralizer_normal (Z1 := d.Z1) h.normalized
  let q := QuotientGroup.mk' N
  let R := pResidual 2 (C ⧸ N)
  have hker : q.ker ≤ centralizer (V0 : Set C) := by
    intro x hx v hv
    exact Subtype.ext (((QuotientGroup.eq_one_iff x).mp hx).2 v hv)
  have hB0 : IsPPerfect 2 B0 := hpB.of_surjective
    (subgroupOfEquivOfLe hBC).symm.toMonoidHom (subgroupOfEquivOfLe hBC).symm.surjective
  have hBR : B0.map q ≤ R :=
    (map_mono (le_pResidual_of_isPPerfect B0 hB0)).trans
      (map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective N)).le
  have hcard : Nat.card R = p := s.residual_card
  have hnon : B0.map q ≠ ⊥ := by
    intro hz
    apply hne
    intro b hb
    have hk := (map_eq_bot_iff B0).mp hz (show (⟨b,hBC hb⟩ : C) ∈ B0 from hb)
    exact ((QuotientGroup.eq_one_iff _).mp hk).2
  have himage : B0.map q = R := by
    apply eq_of_le_of_card_ge hBR
    have hd : Nat.card (B0.map q) ∣ p := hcard ▸ card_dvd_of_le hBR
    have he : Nat.card (B0.map q) = p :=
      (Nat.dvd_prime s.prime_prime).mp hd |>.resolve_left (fun he => hnon (card_eq_one.mp he))
    exact le_of_eq (hcard.trans he.symm)
  have hCV : (⊤ : Subgroup C) ≤ normalizer (V0 : Set C) := by
    intro c _
    apply mem_normalizer_iff.mpr
    intro v
    exact mem_normalizer_iff.mp (h.normalized c.property.1) v
  have hn := normalizes_commutator_of_normalizes_image V0 B0 ⊤ q hker hCV (by
    rw [himage]
    exact le_normalizer_of_normal)
  have hm := (map_mono (f := C.subtype) hn).trans ((⁅V0,B0⁆).le_normalizer_map C.subtype)
  rw [←MonoidHom.range_eq_map,range_subtype,map_commutator,
    map_subgroupOf_eq_of_le hVC,map_subgroupOf_eq_of_le hBC] at hm
  refine ⟨hm,?_⟩
  intro P hPB hP
  let P0 := P.subgroupOf C
  have hPR : P0.map q ≤ R := (map_mono (show P0 ≤ B0 from fun _ hx => hPB hx)).trans hBR
  have hpR : IsPGroup p R := IsPGroup.of_card_dvd_pow (n := 1) (by rw [hcard,pow_one])
  have hz : P0.map q = ⊥ := by
    apply bot_unique
    have hd := IsPGroup.disjoint_of_coprime (hP.comap_subtype.map q) hpR
      (Nat.coprime_primes Nat.prime_two s.prime_prime |>.mpr hp2.symm)
    exact fun x hx => disjoint_def.mp hd hx (hPR hx)
  intro x hx
  have hk := (map_eq_bot_iff P0).mp hz
    (show (⟨x,hBC (hPB hx)⟩ : C) ∈ P0 from hx)
  exact ((QuotientGroup.eq_one_iff _).mp hk).2

private theorem conjugate_blocks_commute
    (d : CaseIComponentData T M Mc V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) {n : ℕ} (hb : IsL2EvenBlock K n)
    (x : G) (hx : x ∈ d.S) (hne : K.map (MulAut.conj x).toMonoidHom ≠ K) :
    ⁅K.map (MulAut.conj x).toMonoidHom,K⁆ = ⊥ := by
  let H := K ⊔ d.S
  let K0 := K.subgroupOf H
  let e := subgroupOfEquivOfLe (show K ≤ H from le_sup_left)
  let x0 : H := ⟨x,mem_sup_right hx⟩
  have hb0 : IsBlock K0 := ⟨inferInstance,hb.2.1.of_mulEquiv e.symm,hK.2.1.subnormal⟩
  let := hq
  have hq0 : IsQuasisimple (K0 ⧸ pCore 2 K0) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hmap : (K0.map (MulAut.conj x0).toMonoidHom).map H.subtype =
      K.map (MulAut.conj x).toMonoidHom := by
    rw [map_map]
    change K0.map ((MulAut.conj x).toMonoidHom.comp H.subtype) = _
    rw [←map_map,map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left)]
  have hne0 : K0 ≠ K0.map (MulAut.conj x0).toMonoidHom := by
    intro he
    have hh := congrArg (map H.subtype) he
    rw [hmap,map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left)] at hh
    exact hne hh.symm
  have hc := hb0.commutator_eq_bot_of_quasisimple_quotient
    (hb0.map_equiv (MulAut.conj x0)) hq0 hne0
  have hm := congrArg (map H.subtype) hc
  rw [map_commutator,hmap,map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),Subgroup.map_bot] at hm
  exact (commutator_comm _ _).trans hm

/-- The original prime residual prevents S from permuting distinct natural
blocks: their common displacement would lie in two commuting blocks. -/
theorem PreExclusionSource.localFamily_linearTwo_sylow_normalizes
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    {n : ℕ} (hb : IsL2EvenBlock K n) (hp2 : p ≠ 2) :
    d.S ≤ normalizer (K : Set G) := by
  let := h.elementary
  let B := d.localSylowBorel K
  have hBC : B ≤ M ⊓ d.G1 := le_inf
    (d.localFamily_linearTwo_borel_le_selected hG hM hJ hu h hK hq hout hb)
    (inf_le_left.trans hK.1)
  have hVG : V ≤ d.G1 := V.le_centralizer.trans
    (centralizer_le (d.Z1_le_fixed.trans inf_le_left))
  have hVC := le_inf h.le_selected hVG
  have hne : ¬ B ≤ centralizer (V : Set G) := by
    intro hc
    apply s.localFamily_linearTwo_borel_not_le_MZ (h := h) hG hM hJ hu hfull hK hq hout hb
    rw [hfull] at hc
    exact le_inf (inf_le_left.trans hK.1) (hc.trans (localModule_centralizer_le_partner T M hu))
  obtain ⟨hnW,hpfix⟩ := marked_prime_displacement (h := h) s hVC hBC
    (d.localFamily_linearTwo_borel_twoPerfect hK hb) hne hp2
  have hVJ : V ≤ elementaryAbelianMaxJ d.S := by
    have he := (h.caseI_marked_thompson_control hG T hM hJ d.Z1_le_fixed).1
    change elementaryAbelianMaxJ d.S = elementaryAbelianMaxJ (T : Subgroup G) at he
    rw [he,hfull]
    intro v hv
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp
      ((source_centralizing_baumann_control hG T hM hJ).1 hv)).1
  have hVN : V ≤ normalizer (K : Set G) := hVJ.trans
    (d.localFamily_thompson_normalizes h hM.1.2 hu hK hq hout hb.2.1.fitting)
  have hWK : ⁅V,B⁆ ≤ K := (commutator_mono le_rfl (show B ≤ K from inf_le_left)).trans
    (le_normalizer_iff_commutator_le_right.mp hVN)
  have hSNW : d.S ≤ normalizer (⁅V,B⁆ : Subgroup G) :=
    (le_inf (d.S_le_T.trans hM.1.2) d.S_le_G1).trans hnW
  intro x hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  by_contra hnx
  have hc := conjugate_blocks_commute d hK hq hb x hx hnx
  have hWconj : ⁅V,B⁆ ≤ K.map (MulAut.conj x).toMonoidHom := by
    have hh := map_mono (f := (MulAut.conj x).toMonoidHom) hWK
    have he : (⁅V,B⁆ : Subgroup G).map (MulAut.conj x).toMonoidHom = ⁅V,B⁆ :=
      mem_normalizer_iff_map_conj_eq.mp (hSNW hx)
    rwa [he] at hh
  have hWB : ⁅V,B⁆ ≤ centralizer (B : Set G) := hWconj.trans
    ((commutator_eq_bot_iff_le_centralizer.mp hc).trans (centralizer_le inf_le_left))
  obtain ⟨P,hP⟩ := ComponentModels.source20_sylow_intersection hK.2
  have heP : (P : Subgroup K) = (d.S ⊓ K).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le inf_le_right]
  have hB : (normalizer (P : Set K)).map K.subtype = B := by
    change (normalizer (P : Set K)).map K.subtype = d.localSylowBorel K
    rw [d.localSylowBorel_eq,←heP]
    rfl
  have hPB : (P : Subgroup K).map K.subtype ≤ B := by
    rw [←hB]
    exact map_mono (P : Subgroup K).le_normalizer
  have hPV := hpfix _ hPB (P.isPGroup'.map K.subtype)
  obtain ⟨D,hDB,hDo,hDne⟩ := hb.exists_odd_borel_subgroup P
  let E := D.map K.subtype
  have hEB : E ≤ B := (map_mono hDB).trans_eq hB
  have hEo : Odd (Nat.card E) := by rwa [card_map_of_injective K.subtype_injective]
  have hEne : E ≠ ⊥ := fun he => hDne ((map_eq_bot_iff_of_injective D K.subtype_injective).mp he)
  have hquad : ⁅⁅V,E⁆,E⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    ((commutator_mono le_rfl hEB).trans (hWB.trans (centralizer_le hEB)))
  have hVE : ⁅V,E⁆ = ⊥ := commutator_eq_bot_of_coprime_quadratic V E
    (hEB.trans (hBC.trans inf_le_left) |>.trans h.normalized)
    (Group.isSolvable_of_comm fun a b : V => mul_comm a b)
    (by
      obtain ⟨a,ha⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
      rw [ha]
      exact hEo.coprime_two_right.pow_right a) hquad
  have hKV := hb.centralizes_of_sylow_odd_fixed K V E P hVN hPV
    (map_subtype_le _) hEo hEne (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hVE))
  rw [hfull] at hKV
  exact hout (le_inf hK.1 (hKV.trans (localModule_centralizer_le_partner T M hu)))


/-- The original orbit collapses to one Borel. In the same local group KS,
the marked intersection and the normalizer of the original Q₁ are exactly S. -/
theorem PreExclusionSource.localFamily_linearTwo_local_geometry
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    {n : ℕ} (hb : IsL2EvenBlock K n) (hp2 : p ≠ 2) :
    d.S ≤ normalizer (K : Set G) ∧
      d.orbitSylowBorel K = d.localSylowBorel K ∧
      d.MZ ⊓ (K ⊔ d.S) = d.S ∧
      (K ⊔ d.S) ⊓ normalizer (d.Q1 : Set G) = d.S := by
  have hn := s.localFamily_linearTwo_sylow_normalizes (h := h) hG hM hJ hu hfull hK hq hout hb hp2
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hSM : d.S ≤ d.MZ := by
    intro x hx
    exact ⟨d.S_le_G1 hx,hMc.2 (fun z hz =>
      (centralInvolutions_le_centralizer_sylow T hz x (d.S_le_T hx)).symm)⟩
  have hSB : d.S ≤ normalizer (d.localSylowBorel K : Set G) := by
    rw [d.localSylowBorel_eq]
    exact (le_inf hSM hn).trans (d.localFamily_linearTwo_borel_normalized hu hK hout hb)
  have hpoint := s.localFamily_linearTwo_marked_eq_sylow (h := h)
    hG hM hJ hu hfull hK hq hout hb hp2
  have he : d.MZ ⊓ (K ⊔ d.S) = d.S := by
    apply le_antisymm ?_ (le_inf hSM le_sup_right)
    intro z hz
    have hzprod : z ∈ (K : Set G) * (d.S : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left K d.S hn]
      exact hz.2
    obtain ⟨k,hk,t,ht,rfl⟩ := hzprod
    have hkM : k ∈ d.MZ := (d.MZ.mul_mem_cancel_right (hSM ht)).mp hz.1
    have hkS : k ∈ d.S := ((show k ∈ d.S ⊓ K from hpoint ▸ ⟨hkM,hk⟩)).1
    exact d.S.mul_mem hkS ht
  refine ⟨hn,le_antisymm (conjugateSpanBy_le le_rfl hSB) (le_conjugateSpanBy _ _),he,?_⟩
  apply le_antisymm ?_ (le_inf le_sup_right (d.S_le_T.trans s.sylow_normalizes_Q1))
  intro z hz
  have hzG : z ∈ d.G1 := (sup_le hK.1 d.S_le_G1) hz.1
  have hzM : z ∈ d.MZ := s.core_normalizer ▸ ⟨hzG,hz.2⟩
  exact he ▸ ⟨hzM,hz.1⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The remaining original natural row has cubic field order four and a
single S-invariant Borel. Its local Q₁-normalizer is computed in the literal KS.
No ambient C-component hypothesis or new selection is imposed on K. -/
theorem PreparedChosenModule.source_preExclusion_local_natural_sylow
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hp : m.prime = 3 ∨ m.prime = 5)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → ∀ n : ℕ, IsL2EvenBlock K n →
          m.prime = 3 ∧ n = 2 ∧ d.S ≤ normalizer (K : Set G) ∧
            d.orbitSylowBorel K = d.localSylowBorel K ∧
            d.MZ ⊓ (K ⊔ d.S) = d.S ∧
            (K ⊔ d.S) ⊓ normalizer (d.Q1 : Set G) = d.S := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout n hb
  obtain ⟨hp3,hn⟩ := s.localFamily_linearTwo_small_field (h := h)
    hp hG hM hJ hu hfull hK hq hout hb
  exact ⟨hp3,hn,s.localFamily_linearTwo_local_geometry (h := h)
    hG hM hJ hu hfull hK hq hout hb (by omega)⟩

end CFSG.Quasithin.Chapter15.Section01
