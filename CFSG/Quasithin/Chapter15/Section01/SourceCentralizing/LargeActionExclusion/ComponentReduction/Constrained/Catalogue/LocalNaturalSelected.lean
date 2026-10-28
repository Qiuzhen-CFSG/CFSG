module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalNaturalOvergroup
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.ShortSeedPropagation

/-!
# The original selected carrier of a natural local escape

An escaping natural member K has its original moving plane in U(K) and
lies properly in a unique normal ambient C-component A. If A differed
from the selected L, the component commutator bound would put [K,L] in
O₂(G₁). The full Sylow normalizes K, so this quotient commutation lifts
to normalization. The perfect-actor theorem for short groups then gives
[K,L]=1, contradicting the original movement of the same plane by L.
Consequently A=L; no new component selection or source record is made.

In the constrained branch, O₂(L) normalizes K and K normally generates L.
The short-seed propagation theorem therefore proves that L is short.
The actual original-marker consumer uses the existing quasisimple quotient
of L and discharges its ordinary/constrained dichotomy from O(G₁)=1. It
retains the cubic field-four restriction, moving plane of order four,
normality and maximality of L, and every group/intersection row supplied
by the maximal-member catalogue, including both binary flag parabolics.

The remaining proper embeddings K<L are not excluded here. In particular,
K need not be an ambient C-component, and neither K-invariance of V nor
M_Z-invariance of its Borel is inferred. Original 15.1.14 and the whole-core
A₆ reconstruction retain their earlier producers and assembly owners.

Source: Aschbacher--Smith 1.2.1(2), 1.2.4, C.1.10 and C.1.21,
printed pp.504--505,124,128; 15.1.19(7) and 15.1.20(2), pp.1093--1095.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem perfect_twoPerfect {B : Type*} [Group B] [Finite B] [Group.IsPerfect B] :
    IsPPerfect 2 B := by
  intro N hn hp
  let := hn
  by_contra he
  let : Nontrivial (B ⧸ N) := QuotientGroup.nontrivial_iff.mpr he
  let : Group.IsPerfect (B ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (B ⧸ N) := hp.isNilpotent
  exact Group.IsPerfect.not_isSolvable (B ⧸ N) inferInstance

private theorem short_commutes_of_core_bound
    (K B : Subgroup G) (hK : IsShort K) [Group.IsPerfect B]
    (hn : pCore 2 G ≤ normalizer (K : Set G))
    (hc : ⁅K,B⁆ ≤ pCore 2 G) : ⁅K,B⁆ = ⊥ := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hqb : ⁅K.map q,B.map q⁆ = ⊥ := by
    rwa [←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
  have hbn : B.map q ≤ normalizer (K.map q : Set (G ⧸ pCore 2 G)) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hqb)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hbjoin : B ≤ normalizer ((K ⊔ pCore 2 G : Subgroup G) : Set G) := by
    have hh := (map_le_iff_le_comap.mp hbn).trans ((K.map q).le_normalizer_comap q)
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk'] using hh
  have hbK : B ≤ normalizer (K : Set G) := by
    rw [←embedded_pResidual_join_pGroup K (pCore 2 G) hK.twoPerfect pCore_isPGroup hn]
    exact hbjoin.trans (normalizer_le_normalizer_characteristic_image _ _)
  let H := K ⊔ B
  let K0 := K.subgroupOf H
  let B0 := B.subgroupOf H
  have hKH : K ≤ H := le_sup_left
  have hBH : B ≤ H := le_sup_right
  let : K0.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hbK)
  let : Group.IsPerfect B0 := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hBH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hBH).symm.surjective
  have hc0 : ⁅K0,B0⁆ ≤ (pCore 2 G).subgroupOf H := by
    apply map_le_iff_le_comap.mp
    rwa [map_commutator,map_subgroupOf_eq_of_le hKH,map_subgroupOf_eq_of_le hBH]
  have hp : IsPGroup 2 ↥(⁅K0,B0⁆ : Subgroup H) := pCore_isPGroup.comap_subtype.to_le hc0
  have hcK : ⁅K0,B0⁆ ≤ K0.pCoreIn 2 := le_pCoreIn_of_normalizes hp
    (commutator_le_left _ _) (normalizer_commutator_ge_left _ _)
  have he := BlockCommutation.perfect_actor_centralizes K0 B0
    (hK.of_mulEquiv (subgroupOfEquivOfLe hKH).symm) perfect_twoPerfect hcK
  have hh := congrArg (map H.subtype) he
  rwa [map_commutator,map_subgroupOf_eq_of_le hKH,map_subgroupOf_eq_of_le hBH,
    Subgroup.map_bot] at hh

/-- A local natural escape lies properly in the original selected component.
The original moving plane rules out every other ambient carrier. -/
theorem PreExclusionSource.localFamily_linearTwo_selected_carrier
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    {n : ℕ} (hb : IsL2EvenBlock K n) (hp2 : p ≠ 2) :
    K < d.L ∧ d.L ∈ Chapter1.LStarIn d.G1 d.S ∧
      (d.L.subgroupOf d.G1).Normal ∧ d.G1 ≤ normalizer (d.L : Set G) ∧
      ∀ A : Subgroup G, A ∈ Chapter1.cComponentsIn d.G1 → K ≤ A → A = d.L := by
  let := h.elementary
  have hLG : d.L ≤ d.G1 := d.L_component.1
  have hcL : (d.L.subgroupOf d.G1).IsCComponent := d.L_component.2
  obtain ⟨A,hAc,hKA,hAl,houtA,hAn,hGn,hunique⟩ :=
    s.localFamily_linearTwo_strict_carrier (h := h)
      hG hM hJ hu hne hmany hfull hres hK hq hout hb hp2
  have he : A = d.L := by
    by_contra hneA
    have hsq : IsSQTK KnownSimple.IsKnownSimple d.G1 := caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
      ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left))
    have hquot : IsSQTK KnownSimple.IsKnownSimple (d.G1 ⧸ pCore 2 d.G1) := by
      refine ⟨?_,hsq.isKGroup.quotient (pCore 2 d.G1)⟩
      intro q hq ho
      let : Fact q.Prime := ⟨hq⟩
      exact (primeRank_quotient_le_of_isTwoGroup q ho (pCore 2 d.G1) pCore_isPGroup).trans
        (hsq.stronglyQuasithin q hq ho)
    have hne0 : A.subgroupOf d.G1 ≠ d.L.subgroupOf d.G1 := by
      intro hh
      have hh := congrArg (map d.G1.subtype) hh
      rw [map_subgroupOf_eq_of_le hAc.1,map_subgroupOf_eq_of_le hLG] at hh
      exact hneA hh
    have hcomm := ChapterA.Section03.CComponentCommutation.proposition_1_2_1_two
      hquot hAc.2 hcL hne0
    have hKL : ⁅K.subgroupOf d.G1,d.L.subgroupOf d.G1⁆ ≤ pCore 2 d.G1 :=
      (commutator_mono (comap_mono hKA.le) le_rfl).trans (hcomm.1.trans hcomm.2)
    obtain ⟨P,hP⟩ := s.centralizer_sylow
    have hnorm : pCore 2 d.G1 ≤ normalizer (K.subgroupOf d.G1 : Set d.G1) := by
      have hnK := s.localFamily_linearTwo_sylow_normalizes (h := h)
        hG hM hJ hu hfull hK hq hout hb hp2
      intro x hx
      apply mem_normalizer_iff.mpr
      intro k
      exact mem_normalizer_iff.mp
        (hnK (hP ▸ mem_map_of_mem d.G1.subtype (pCore_isPGroup.le_sylow_of_normal P hx))) k
    let := hcL.perfect
    have hz := short_commutes_of_core_bound (K.subgroupOf d.G1) (d.L.subgroupOf d.G1)
      (hb.2.1.of_mulEquiv (subgroupOfEquivOfLe hK.1).symm) hnorm hKL
    have hzG := congrArg (map d.G1.subtype) hz
    rw [map_commutator,map_subgroupOf_eq_of_le hK.1,
      map_subgroupOf_eq_of_le hLG,Subgroup.map_bot] at hzG
    have hW := (s.localFamily_linearTwo_moving_plane_bound (h := h)
      hG hM hJ hu hfull hK hq hout hb hp2).1
    exact s.moving_noncentral (commutator_eq_bot_iff_le_centralizer.mpr
      ((commutator_eq_bot_iff_le_centralizer.mp (commutator_comm _ _ |>.trans hzG)).trans
        (centralizer_le (hW.trans (map_subtype_le _)))))
  subst A
  exact ⟨hKA,hAl,hAn,hGn,hunique⟩

/-- In its genuine constrained branch, the original selected carrier is short:
its normalizing two-core and the nonsolvable local seed supply normal generation. -/
theorem PreExclusionSource.localFamily_linearTwo_constrained_carrier_short
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    {n : ℕ} (hb : IsL2EvenBlock K n) (hp2 : p ≠ 2)
    (hf : generalizedFitting d.L = pCore 2 d.L) :
    IsShort d.L := by
  have hKL := (s.localFamily_linearTwo_selected_carrier (h := h)
    hG hM hJ hu hne hmany hfull hres hK hq hout hb hp2).1.le
  let K0 := K.subgroupOf d.L
  let e : K0 ≃* K := subgroupOfEquivOfLe hKL
  let := Chapter1.mem_L_isPerfect hK.2
  let := Chapter1.mem_L_isPerfect s.local_component
  let : Group.IsPerfect K0 := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let := s.quasisimple
  have hK0 : IsShort K0 := hb.2.1.of_mulEquiv e.symm
  obtain ⟨P,hP⟩ := s.component_sylow
  have hcoreS : d.L.pCoreIn 2 ≤ d.S := (pCoreIn_le_sylow d.L P).trans (hP.le.trans inf_le_left)
  have hSN := s.localFamily_linearTwo_sylow_normalizes (h := h)
    hG hM hJ hu hfull hK hq hout hb hp2
  have hQK : pCore 2 d.L ≤ normalizer (K0 : Set d.L) := by
    apply le_normalizer_iff.mpr
    intro q hq k hk
    exact le_normalizer_iff.mp hSN q (hcoreS (mem_map_of_mem d.L.subtype hq)) k hk
  have hnon : ¬ K0.map (QuotientGroup.mk' (pCore 2 d.L)) ≤ center (d.L ⧸ pCore 2 d.L) := by
    intro hc
    let q := QuotientGroup.mk' (pCore 2 d.L)
    let : Group.IsPerfect (K0.map q) := Group.IsPerfect.map q
    have hz : K0.map q = ⊥ := by
      have hh : ⁅K0.map q,K0.map q⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
        (hc.trans (center_le_centralizer _))
      rwa [commutator_eq_self] at hh
    have hi : K0 ≤ pCore 2 d.L := by
      simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff K0).mp hz
    let : Group.IsNilpotent K0 := (pCore_isPGroup.to_le hi).isNilpotent
    exact Chapter1.mem_L_not_isSolvable hK.2
      (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  exact RankOne.GlaubermanArgument.isShort_of_normal_generation K0 hK0 perfect_twoPerfect hf
    (Or.inl s.quasisimple) hQK
    (RankOne.GlaubermanArgument.normal_generation_of_noncentral_core_image K0 perfect_twoPerfect hnon)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original marker's natural local members have the same selected carrier.
Its genuine ordinary or constrained branch is discharged from the original odd-core
identity. In the constrained branch the carrier is short and has the full local
source rows, using its existing quasisimple quotient. -/
theorem PreparedChosenModule.source_preExclusion_local_natural_selected_carrier
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
          m.prime = 3 ∧ n = 2 ∧ m.movingPlane ≤ (blockU K).map K.subtype ∧
            Nat.card m.movingPlane = 4 ∧ K < d.L ∧
            d.L ∈ Chapter1.LStarIn d.G1 d.S ∧
            (d.L.subgroupOf d.G1).Normal ∧ d.G1 ≤ normalizer (d.L : Set G) ∧
            (IsComponent d.G1 (d.L.subgroupOf d.G1) ∨
              (generalizedFitting d.L = pCore 2 d.L ∧ IsShort d.L ∧
                ⁅d.L,elementaryAbelianMaxJ d.S⁆ = d.L ∧
                CaseIComponentData.LocalConstrainedSourceRows d d.L)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout n hb
  obtain ⟨hp3,hn,hW,hcard⟩ := s.localFamily_linearTwo_moving_plane_four (h := h)
    hp hG hM hJ hu hfull hK hq hout hb
  have hG1 : d.G1 = centralizer (m.Z1 : Set G) := by
    change centralizer (d.Z1 : Set G) = _
    rw [hZ]
  rw [hG1] at hW hcard
  obtain ⟨hKL,hLmax,hLn,hGn,_⟩ := s.localFamily_linearTwo_selected_carrier (h := h)
    hG hM hJ hu hne hmany hfull hres hK hq hout hb (by omega)
  refine ⟨hp3,hn,hW,hcard,hKL,hLmax,hLn,hGn,?_⟩
  rcases d.ordinary_or_constrained s.odd_core with hc | hf
  · exact Or.inl hc
  · exact Or.inr ⟨hf,s.localFamily_linearTwo_constrained_carrier_short (h := h)
      hG hM hJ hu hne hmany hfull hres hK hq hout hb (by omega) hf,
      s.localFamily_maximal_constrained_source_rows (h := h) (by omega)
        hG hempty hM hJ hu hne hmany hfull hres hLmax s.quasisimple d.L_not_le_MZ hf⟩

end CFSG.Quasithin.Chapter15.Section01
