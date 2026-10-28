module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Sporadic.JankoFour.LocalFamily
public import Theory.Mathieu.SchurMultipliers.Models
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary
public import Theory.SpecificGroups.Janko4.Model.OddLocalRanks
public import Theory.GroupTheory.GeneralizedFitting.ComponentCoprimeRankNormal
public import Theory.GroupTheory.PCorePreimageCentralizer
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.CentralCover

/-!
# Excluding the original ordinary J₄ component

The native nonabelian subgroup of order 27 gives three-rank at least two.
The ambient strongly quasithin rank bound then makes L normal in G₁. The
Sylow-compatible Mathieu seed in the retained central two-cover is therefore
normalized by S. Its two-residual is a genuine member of L(G₁,S), with
F* equal to O₂ and literal two-core quotient M₂₄.

The full FF catalogue forces that residual, and hence the seed, into M_Z.
Generation with the fixed points of the original central involution gives
L ≤ M_c, contradicting the original component choice. This proves the
J₄ exclusion before any exchanged-component or noncentral-plane selection.

Source: Aschbacher--Smith 15.1.20(3), printed p.1097. The local-containment
step uses the proved general-family FF action directly and needs no extra
Borel-placement premise. Final catalogue exhaustion remains with the
ordinary pre-exclusion owner.
-/

public section
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
  Janko4.Cardinality.max1Subgroup Janko4.Cardinality.localKernel

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open Representation Representation.BinaryOffender Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem m24_twoResidual : pResidual 2 Sporadic.Mathieu.M24 = ⊤ := by
  apply (pResidual_eq_top_iff 2 _).mpr
  intro N hN hq
  let := hN
  let : Group.IsNilpotent (Sporadic.Mathieu.M24 ⧸ N) := hq.isNilpotent
  exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ N)

private theorem mathieu_seed_le_MZ (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hs : Chapter1.IsSylowIn 2 d.S d.G1) (hSM : d.S ≤ d.MZ)
    (B : Subgroup G) (hBG : B ≤ d.G1) (hn : d.S ≤ normalizer (B : Set G))
    (hc : centralizer (pCore 2 B : Set B) ≤ pCore 2 B)
    (P : Sylow 2 B) (hPS : (P : Subgroup B).map B.subtype ≤ d.S)
    (f : B →* Sporadic.Mathieu.M24) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) : B ≤ d.MZ := by
  let R := pResidual 2 B
  let K := R.map B.subtype
  let e : R ≃* K := R.equivMapOfInjective B.subtype B.subtype_injective
  let fr := f.comp R.subtype
  have hfr : Function.Surjective fr := by
    apply MonoidHom.range_eq_top.mp
    change (f.comp R.subtype).range = ⊤
    rw [MonoidHom.range_comp,range_subtype]
    rw [map_pResidual_of_surjective 2 f hf,m24_twoResidual]
  have hkr : IsPGroup 2 fr.ker := by
    rw [←MonoidHom.comap_ker]
    exact hk.comap_subtype
  let fK := fr.comp e.symm.toMonoidHom
  have hfK : Function.Surjective fK := hfr.comp e.symm.surjective
  have hkK : IsPGroup 2 fK.ker := by
    rw [←MonoidHom.comap_ker]
    exact hkr.comap_of_injective _ e.symm.injective
  have hker := Sporadic.Mathieu.ker_eq_twoCore_of_surjective_m24 fK hfK hkK
  let eqK : (K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24 :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective fK hfK)
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv eqK.symm
  let : IsQuasisimple (R ⧸ pCore 2 R) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hcR := normal_core_selfCentralizing hc R
  have hcK : centralizer (pCore 2 K : Set K) ≤ pCore 2 K := by
    have he : (pCore 2 R).map e.toMonoidHom = pCore 2 K := pCore_map_iso 2 e
    intro x hx
    have hxR : e.symm x ∈ pCore 2 R := hcR (by
      intro y hy
      apply e.injective
      simpa only [map_mul,e.apply_symm_apply] using hx (e y) (he ▸ mem_map_of_mem _ hy))
    rw [←he]
    exact ⟨e.symm x,hxR,e.apply_symm_apply x⟩
  have hKG : K ≤ d.G1 := (map_subtype_le _).trans hBG
  let H := B ⊔ d.S
  have hBH : B ≤ H := le_sup_left
  let : (B.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer (sup_le B.le_normalizer hn)
  let eb := subgroupOfEquivOfLe hBH
  have hRcomp : R.IsCComponent := isCComponent_of_isPPerfect_of_quasisimple_core_quotient
    (inferInstance : R.Normal).isSubnormal (isPPerfect_pResidual 2)
  have hKcomp := (hRcomp.map_equiv eb.symm).map_subtype
    (inferInstance : (B.subgroupOf H).Normal).isSubnormal
  have heK : (R.map eb.symm.toMonoidHom).map (B.subgroupOf H).subtype = K.subgroupOf H := by
    rw [map_map]
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y,hy,rfl⟩
    · rintro ⟨y,hy,he⟩
      exact ⟨y,hy,Subtype.ext he⟩
  rw [heK] at hKcomp
  have hO : B.pCoreIn 2 ≠ ⊥ := by
    intro he
    have ho : pCore 2 B = ⊥ := (map_eq_bot_iff_of_injective _ B.subtype_injective).mp he
    have hevery (x : B) : x = 1 := by
      have hx : x ∈ pCore 2 B := hc (by
        intro y hy
        have hy1 : y = 1 := by
          change y ∈ pCore 2 B at hy
          rwa [ho,mem_bot] at hy
        simp only [hy1,one_mul,mul_one])
      simpa only [ho,mem_bot] using hx
    let := Sporadic.Mathieu.m24_isSimpleGroup
    obtain ⟨y,hy⟩ := exists_ne (1 : Sporadic.Mathieu.M24)
    obtain ⟨x,rfl⟩ := hf y
    exact hy (by rw [hevery x,map_one])
  have hOH : B.pCoreIn 2 ≤ H.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 B) ((pCoreIn_le 2 B).trans hBH)
    ((sup_le B.le_normalizer hn).trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))
  have hloc : K ∈ Chapter1.LIn d.G1 d.S := ⟨hKG,Chapter1.mem_L_of_cComponent
    (fun he => hO (bot_unique (he ▸ hOH)))
    (hs.restrict le_sup_right (sup_le hBG (Chapter1.isSylowIn_iff.mp hs).2.1))
    ((map_subtype_le _).trans hBH) hKcomp⟩
  have hKM := d.localFamily_mathieuTwentyFour_le_MZ hG hempty hM hJ hu h hloc
    inferInstance (generalizedFitting_eq_pCore_of_selfCentralizing 2 hcK) eqK
  have hgen := congrArg (Subgroup.map B.subtype) (pResidual_sup_sylow_eq_top P)
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hgen
  exact hgen.ge.trans (sup_le hKM (hPS.trans hSM))
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open Representation Representation.BinaryOffender Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

private theorem normal_of_odd_rank
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {r : ℕ} (hr : r.Prime) (ho : Odd r) (hR : 2 ≤ primeRank r d.L) :
    (d.L.subgroupOf d.G1).Normal := by
  let : Fact r.Prime := ⟨hr⟩
  let := h.elementary
  have hsq : IsSQTK KnownSimple.IsKnownSimple d.G1 := caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
    ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left))
  let e := subgroupOfEquivOfLe (show d.L ≤ d.G1 from d.L_component.1)
  have hZ : IsPGroup 2 (center d.L) := by
    rw [(s.ordinary hL).center_eq]
    exact pCore_isPGroup
  have hZ' : IsPGroup 2 (center (d.L.subgroupOf d.G1)) := hZ.of_equiv (centerCongr e.symm)
  obtain ⟨n,hn⟩ := hZ'.exists_card_eq
  have hc : Nat.Coprime r (Nat.card (center (d.L.subgroupOf d.G1))) := by
    rw [hn]
    exact (Nat.coprime_two_right.mpr ho).pow_right n
  have hR' : 2 ≤ primeRank r (d.L.subgroupOf d.G1) := by
    rwa [primeRank_equiv r e]
  exact hL.normal_of_coprime_center_primeRank r hc (by
    have hh := hsq.stronglyQuasithin r hr ho
    omega)

private theorem marked_fixer
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) :
    ∃ P : Sylow 2 d.L, (P : Subgroup d.L).map d.L.subtype = d.SL ∧
      ∃ α : MulAut d.L, α^2=1 ∧ α≠1 ∧ (∀ x ∈ P, α x=x) ∧
        α.fixedSubgroup.map d.L.subtype ≤ Mc := by
  obtain ⟨z,hz,hzne⟩ := (Subgroup.bot_or_exists_ne_one (centralInvolutions T)).resolve_left
    (centralInvolutions_ne_bot_of_maximal_local T hM.1)
  obtain ⟨α,ha,_⟩ := s.ordinary_marked_model (h := h) hL hz hzne
  obtain ⟨R,hR,h115⟩ := d.ordinary_involution_inputs hG hu h s.centralizer_sylow
  have hzc : z ∈ centralizer (d.S : Set G) := by
    intro x hx
    exact (h115 z hz hzne).central x (hR.symm ▸ hx)
  have hz2 : z*z=1 := by
    simpa only [(h115 z hz hzne).involution,pow_two] using pow_orderOf_eq_one z
  have hα2 : α^2=1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (α (α x) : G) = x
    rw [ha,ha]
    calc
      z*(z*(x:G)*z⁻¹)*z⁻¹ = (z*z)*x*(z*z)⁻¹ := by group
      _ = x := by rw [hz2]; simp
  have hαne : α ≠ 1 := by
    intro he
    have hc : z ∈ centralizer (d.L : Set G) := by
      intro x hx
      have hh := ha (⟨x,hx⟩:d.L)
      rw [he] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
    have hzbot : z ∈ (⊥ : Subgroup G) := (s.ordinary hL).central_faithful ▸ ⟨hz,hc⟩
    exact hzne (mem_bot.mp hzbot)
  obtain ⟨P,hP⟩ := s.component_sylow
  refine ⟨P,hP,α,hα2,hαne,?_,?_⟩
  · intro x hx
    apply Subtype.ext
    rw [ha]
    exact mul_inv_eq_iff_eq_mul.mpr
      (hzc x (d.SL_le_S (hP ▸ mem_map_of_mem d.L.subtype hx))).symm
  · rintro _ ⟨x,hx,rfl⟩
    apply (h115 z hz hzne).centralizer_le
    apply mem_centralizer_singleton_iff.mpr
    have he := ha x
    rw [(MulAut.mem_fixedSubgroup _ _).mp hx] at he
    exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm


private theorem j4_odd_rank : 2 ≤ primeRank 3 Janko4.Model := by
  by_contra hh
  have hr : primeRank 3 Janko4.Model ≤ 1 := by omega
  let P := Janko4.Simplicity.threeLocalSubgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four
  have hc : Nat.card P = 3^3 := Janko4.Simplicity.threeLocal_card _ _
  obtain ⟨Q,hPQ⟩ := (IsPGroup.of_card hc).exists_le_sylow
  let : IsCyclic Q := Q.isCyclic_of_odd_of_primeRank_le_one (by decide) hr
  exact Janko4.Simplicity.threeLocal_not_isMulCommutative _ _
    (IsMulCommutative.of_setLike_mul_comm fun x hx y hy =>
      (isMulCommutative_iff_of_setLike.mp (inferInstance : IsMulCommutative Q))
        x (hPQ hx) y (hPQ hy))

private theorem j4_normal (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Janko4.Model) :
    (d.L.subgroupOf d.G1).Normal := by
  apply normal_of_odd_rank (h := h) s hG hL (by decide : Nat.Prime 3) (by decide)
  rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 d.L) pCore_isPGroup,
    primeRank_equiv 3 e]
  exact j4_odd_rank

private theorem seed_normalized
    (hn : d.S ≤ normalizer (d.L : Set G))
    (P : Sylow 2 d.L) (hP : (P : Subgroup d.L).map d.L.subtype = d.SL)
    (B : Subgroup d.L)
    (hi : ∀ a : MulAut d.L, (P : Subgroup d.L).map a.toMonoidHom = P →
      B.map a.toMonoidHom = B) : d.S ≤ normalizer (B.map d.L.subtype : Set G) := by
  have hP' : (P : Subgroup d.L)=d.SL.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le d.SL_le_L]
  intro t ht
  let a := d.L.normalizerMonoidHom ⟨t,hn ht⟩
  have ha : (P : Subgroup d.L).map a.toMonoidHom = P := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      rw [hP'] at hx ⊢
      change t * (x : G) * t⁻¹ ∈ d.S ⊓ d.L
      exact ⟨d.S.mul_mem (d.S.mul_mem ht hx.1) (d.S.inv_mem ht),(a x).property⟩
    · exact (Nat.card_congr (a.subgroupMap (P : Subgroup d.L)).toEquiv).le
  have hb := hi a ha
  have hm : (B.map d.L.subtype).map (MulAut.conj t).toMonoidHom = B.map d.L.subtype := by
    rw [map_map]
    have he : (MulAut.conj t).toMonoidHom.comp d.L.subtype = d.L.subtype.comp a.toMonoidHom := by
      ext x
      rfl
    rw [he,←map_map,hb]
  exact (mem_normalizer_iff_map_conj_eq).mpr hm

/-- The original ordinary component cannot have J₄ as its two-core quotient,
including every retained central two-cover. -/
theorem PreExclusionSource.false_of_jankoFour_quotient
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Janko4.Model) : False := by
  let : IsQuasisimple (d.L.subgroupOf d.G1) := hL.2
  let eL : d.L.subgroupOf d.G1 ≃* d.L := subgroupOfEquivOfLe d.L_component.1
  let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv eL
  let ez : (d.L ⧸ center d.L) ≃* Janko4.Model :=
    (QuotientGroup.quotientMulEquivOfEq (s.ordinary hL).center_eq).trans e
  obtain ⟨P,hP,a,ha,hne,hfix,hfixed⟩ := marked_fixer (h := h) s hG hM hu hL
  obtain ⟨B,hPB,hi,hgen,hself,f,hf,hk⟩ := Janko4.LocalStructure.exists_sylow_mathieu_seed_of_central_two_cover ez (s.ordinary hL).center_two P a ha hne hfix
  let C := B.map d.L.subtype
  let eB : B ≃* C := B.equivMapOfInjective d.L.subtype d.L.subtype_injective
  have hnL : d.S ≤ normalizer (d.L : Set G) := d.S_le_G1.trans
    ((normal_subgroupOf_iff_le_normalizer d.L_component.1).mp (j4_normal (h := h) s hG hL e))
  have hnC := seed_normalized hnL P hP B hi
  have hselfC : centralizer (pCore 2 C : Set C) ≤ pCore 2 C :=
    eB.symm.toMonoidHom.centralizer_pCore_le_of_surjective_pKernel eB.symm.surjective
      (by rw [eB.symm.toMonoidHom.ker_eq_bot eB.symm.injective]; exact IsPGroup.of_card (n := 0) (by simp)) hself
  let Q := (P.subtype hPB).mapSurjective (f := eB.toMonoidHom) eB.surjective
  have hQ : (Q : Subgroup C).map C.subtype = d.SL := by
    change (((P.subtype hPB) : Subgroup B).map eB.toMonoidHom).map C.subtype = _
    rw [map_map]
    have he : C.subtype.comp eB.toMonoidHom = d.L.subtype.comp B.subtype := by ext x; rfl
    rw [he,←map_map,Sylow.coe_subtype,map_subgroupOf_eq_of_le hPB,hP]
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hCM : C ≤ d.MZ := mathieu_seed_le_MZ d hG hempty hM hJ hu h s.centralizer_sylow
    (le_inf d.S_le_G1 (d.S_le_T.trans hTMc)) C
    ((map_subtype_le _).trans d.L_component.1) hnC hselfC Q
    (hQ.le.trans d.SL_le_S) (f.comp eB.symm.toMonoidHom) (hf.comp eB.symm.surjective)
    (by rw [←MonoidHom.comap_ker]; exact hk.comap_of_injective _ eB.symm.injective)
  have hg := congrArg (Subgroup.map d.L.subtype) hgen
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hg
  exact d.L_not_le_Mc (hg.ge.trans (sup_le hfixed (hCM.trans inf_le_right)))
/-- The impossible J₄ marking closes its branch of the initial ordinary catalogue. -/
theorem PreExclusionSource.ordinary20_of_jankoFour_quotient
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Janko4.Model) : d.Ordinary20Alternatives :=
  (s.false_of_jankoFour_quotient (h := h) hG hempty hM hJ hu hL e).elim

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData