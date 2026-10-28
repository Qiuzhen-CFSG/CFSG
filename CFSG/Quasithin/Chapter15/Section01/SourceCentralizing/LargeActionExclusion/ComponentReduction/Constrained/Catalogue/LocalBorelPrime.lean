module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalBorel
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalRows
public import Theory.NumberTheory.BinaryTorusParity

/-!
# Source-prime restrictions on the general natural Borel

For every natural L₂(2ⁿ) block K in the original L(G₁,S), the literal
Borel has order 2ᵃ(2ⁿ−1). Its containment in M and two-perfectness put
its action on V inside the original marked residual of prime order p.
If p does not divide the torus order, that action vanishes. With the
source equality V=V(M), this places the whole Borel in M_Z and identifies
both original intersections with that Borel.

In fact the same prime avoidance places K itself in M_Z: V lies in S,
and the centralizer comparison inside K S lifts its centralization of
the Borel to centralization of K. Thus an escaping natural member forces
p to divide 2ⁿ−1. For the two original primes, the remaining degrees are
even n at p=3 and multiples of four at p=5. This is a necessary restriction;
it does not prove the general lower Borel containment in those degrees.

The original-marker consumer retains every local-family row and its
quotient markings together with this restriction. No ambient C-component
hypothesis on K or invariance under M_Z is assumed. The later exchanged
application retains its original cubic marker and either plane size.
Original 15.1.14 remains explicit in marker construction. The general
Borel containment and final source assembly remain open, as does the
independently owned whole-core A₆ reconstruction input.

Source: Aschbacher--Smith 15.1.16--20, printed pp.1092--1095;
the natural Borel centralizer comparison in 15.1.21(i), pp.1097--1098.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem natural_borel_order (d : CaseIComponentData T M Mc V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    {n : ℕ} (hb : IsL2EvenBlock K n) :
    ∃ a : ℕ, Nat.card (d.localSylowBorel K) = 2 ^ a * (2 ^ n - 1) := by
  obtain ⟨P,hP⟩ := ComponentModels.source20_sylow_intersection hK.2
  have he : (P : Subgroup K) = (d.S ⊓ K).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le inf_le_right]
  have hB : (normalizer (P : Set K)).map K.subtype = d.localSylowBorel K := by
    rw [d.localSylowBorel_eq,←he]
    rfl
  let N := normalizer (P : Set K)
  let e : N ≃* d.localSylowBorel K :=
    (equivMapOfInjective N K.subtype K.subtype_injective).trans (MulEquiv.subgroupCongr hB)
  obtain ⟨_,_,F,_,_,hF,_,r,⟨m⟩,_⟩ := hb
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let q := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := m.quotientIso.surjective.comp
    (QuotientGroup.mk'_surjective _)
  have hk : q.ker ≤ (P : Subgroup K) := by
    rw [MonoidHom.ker_comp_of_injective _ _ m.quotientIso.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal P
  obtain ⟨f,hf,hker⟩ := Matrix.SpecialLinearGroup.exists_sylowNormalizer_diagonal q hq P hk
  have hp : IsPGroup 2 f.ker := by
    have heK : f.ker = (P : Subgroup K).subgroupOf N := by
      ext x
      exact hker x
    rw [heK]
    exact P.isPGroup'.comap_subtype
  obtain ⟨a,ha⟩ := hp.exists_card_eq
  refine ⟨a,?_⟩
  rw [←Nat.card_congr e.toEquiv,←f.ker.card_mul_index,index_ker,
    MonoidHom.range_eq_top.mpr hf,Nat.card_congr Subgroup.topEquiv.toEquiv,
    Nat.card_units,hF,ha]

private theorem centralizes_of_prime_avoidance
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    {B : Subgroup G} (hBC : B ≤ M ⊓ d.G1) (hp : IsPPerfect 2 B)
    (hcard : ¬ p ∣ Nat.card B) : B ≤ centralizer (V : Set G) := by
  let C := M ⊓ d.G1
  let N := (M ⊓ centralizer (V : Set G)).subgroupOf C
  let : N.Normal := caseI_module_centralizer_normal (Z1 := d.Z1) h.normalized
  let q := QuotientGroup.mk' N
  let A := B.subgroupOf C
  have hA : IsPPerfect 2 A := hp.of_surjective
    (subgroupOfEquivOfLe hBC).symm.toMonoidHom (subgroupOfEquivOfLe hBC).symm.surjective
  have hR : A.map q ≤ pResidual 2 (C ⧸ N) :=
    (map_mono (le_pResidual_of_isPPerfect A hA)).trans
      (map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective N)).le
  have hd : Nat.card (A.map q) ∣ p := by
    rw [←s.residual_card]
    exact card_dvd_of_le hR
  have hone : Nat.card (A.map q) = 1 := by
    rcases (Nat.dvd_prime s.prime_prime).mp hd with he | he
    · exact he
    · apply False.elim
      apply hcard
      have hdiv := A.card_map_dvd q
      rw [he,Nat.card_congr (subgroupOfEquivOfLe hBC).toEquiv] at hdiv
      exact hdiv
  have hz : A.map q = ⊥ := card_eq_one.mp hone
  have hker := (Subgroup.map_eq_bot_iff A (f := q)).mp hz
  intro b hb
  exact ((QuotientGroup.eq_one_iff _).mp (hker (show (⟨b,hBC hb⟩ : C) ∈ A from hb))).2

/-- Prime avoidance in the literal marked action places the whole natural
Borel in the original module centralizer. -/
theorem PreExclusionSource.localFamily_linearTwo_borel_centralizes_of_prime_avoidance
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    {n : ℕ} (hb : IsL2EvenBlock K n) (hp2 : p ≠ 2) (hpn : ¬ p ∣ 2 ^ n - 1) :
    d.localSylowBorel K ≤ centralizer (V : Set G) := by
  apply centralizes_of_prime_avoidance (h := h) s
    (le_inf (d.localFamily_linearTwo_borel_le_selected hG hM hJ hu h hK hq hout hb)
      (inf_le_left.trans hK.1)) (d.localFamily_linearTwo_borel_twoPerfect hK hb)
  obtain ⟨a,ha⟩ := natural_borel_order d hK hb
  rw [ha]
  intro hd
  rcases s.prime_prime.dvd_mul.mp hd with hd | hd
  · have hd2 := s.prime_prime.dvd_of_dvd_pow hd
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp hd2 |>.resolve_left s.prime_prime.ne_one)
  · exact hpn hd


/-- The complete lower Borel containment when the source prime avoids the
natural torus. Both original intersections retain the identical Borel. -/
theorem PreExclusionSource.localFamily_linearTwo_borel_of_prime_avoidance
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    {n : ℕ} (hb : IsL2EvenBlock K n) (hp2 : p ≠ 2) (hpn : ¬ p ∣ 2 ^ n - 1) :
    d.MZ ⊓ K = d.localSylowBorel K ∧ M ⊓ K = d.MZ ⊓ K := by
  have hc := s.localFamily_linearTwo_borel_centralizes_of_prime_avoidance
    (h := h) hG hM hJ hu hK hq hout hb hp2 hpn
  have hc := hc.trans (centralizer_le hfull.ge)
  have hB : d.localSylowBorel K ≤ d.MZ :=
    le_inf (inf_le_left.trans hK.1) (hc.trans (localModule_centralizer_le_partner T M hu))
  have he : d.MZ ⊓ K = d.localSylowBorel K := le_antisymm
    ((d.localFamily_linearTwo_borel_bound hu hK hout hb).trans_eq
      (d.localSylowBorel_eq K).symm) (le_inf hB inf_le_left)
  exact ⟨he,(d.localFamily_linearTwo_selected_borel hG hempty hM hJ hu h hK hq hout hb).trans he.symm⟩

/-- An escaping natural local member forces the original source prime into
its actual torus order. This uses the centralizer comparison in K S. -/
theorem PreExclusionSource.localFamily_linearTwo_prime_dvd
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    {n : ℕ} (hb : IsL2EvenBlock K n) (hp2 : p ≠ 2) : p ∣ 2 ^ n - 1 := by
  by_contra hpn
  have hc := s.localFamily_linearTwo_borel_centralizes_of_prime_avoidance
    (h := h) hG hM hJ hu hK hq hout hb hp2 hpn
  let := h.elementary
  have hVT : V ≤ (T : Subgroup G) := by
    let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer h.normalized
    let := IsElementaryAbelian.subgroupOf h.le_selected (p := 2)
    have hh := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf M)).le_sylow_of_normal
      (T.subtype hM.1.2)
    simpa only [map_subgroupOf_eq_of_le h.le_selected,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hM.1.2] using map_mono (f := M.subtype) hh
  have hVS : V ≤ d.S := le_inf hVT
    (V.le_centralizer.trans (centralizer_le (d.Z1_le_fixed.trans inf_le_left)))
  have hVK : V ≤ centralizer (K : Set G) :=
    ((le_inf hVS (le_centralizer_iff.mp hc)).trans_eq
      (d.localFamily_linearTwo_borel_centralizer hK hb)).trans inf_le_right
  have hKV := le_centralizer_iff.mp hVK
  rw [hfull] at hKV
  exact hout (le_inf hK.1 (hKV.trans (localModule_centralizer_le_partner T M hu)))

private theorem two_pow_mod_five (n : ℕ) :
    2 ^ n % 5 = if n % 4 = 0 then 1 else if n % 4 = 1 then 2 else
      if n % 4 = 2 then 4 else 3 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ,Nat.mul_mod,ih]
    split_ifs <;> omega

private theorem five_dvd_sub_one_iff (n : ℕ) : 5 ∣ 2 ^ n - 1 ↔ 4 ∣ n := by
  rw [Nat.dvd_iff_mod_eq_zero,Nat.dvd_iff_mod_eq_zero]
  have hm := two_pow_mod_five n
  have hp : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
  split_ifs at hm <;> omega

/-- Both original primes retain their exact field-degree obstruction, on
every eligible K, without changing the original G₁, S or marker. -/
theorem PreExclusionSource.localFamily_linearTwo_degree
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    {n : ℕ} (hb : IsL2EvenBlock K n) :
    (p = 3 → Even n) ∧ (p = 5 → 4 ∣ n) := by
  constructor
  · intro hp
    have hd := s.localFamily_linearTwo_prime_dvd (h := h) hG hM hJ hu hfull hK hq hout hb
      (by omega)
    rw [hp] at hd
    exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mp hd
  · intro hp
    have hd := s.localFamily_linearTwo_prime_dvd (h := h) hG hM hJ hu hfull hK hq hout hb
      (by omega)
    rw [hp] at hd
    exact (five_dvd_sub_one_iff n).mp hd

/-- All natural blocks whose torus avoids the source prime are contained
in the original M_Z, for the entire local family. -/
theorem PreExclusionSource.localFamily_linearTwo_le_MZ_of_prime_avoidance
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {n : ℕ} (hb : IsL2EvenBlock K n) (hp2 : p ≠ 2) (hpn : ¬ p ∣ 2 ^ n - 1) :
    K ≤ d.MZ := by
  by_contra hout
  exact hpn (s.localFamily_linearTwo_prime_dvd (h := h) hG hM hJ hu hfull hK hq hout hb hp2)

/-- The later exchanged component retains the original cubic marker and
hence the same necessary even degree, on either exchanged plane size. -/
theorem ExchangedSource.constrained_natural_even
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.ExchangedSource) (sp : d.PreExclusionSource h.normalized 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    {n : ℕ} (hb : IsL2EvenBlock d.L n) : Even n :=
  (sp.localFamily_linearTwo_degree (h := h) hG hM hJ hu hfull
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hb).1 rfl

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original marker supplies the full-family quotient rows together with
the exact remaining natural-field degrees at both original source primes.
The original 15.1.14 premise is used only by marker construction. -/
theorem PreparedChosenModule.source_preExclusion_local_constrained_rows_degrees
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → generalizedFitting K = pCore 2 K →
          (⁅K,elementaryAbelianMaxJ d.S⁆ = K ∧ CaseIComponentData.LocalConstrainedRows d K) ∧
          ∀ n : ℕ, ChapterC.IsL2EvenBlock K n →
            (m.prime = 3 → Even n) ∧ (m.prime = 5 → 4 ∣ n) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout hf
  exact ⟨d.localFamily_constrained_rows hG hempty hM hJ hu h hK hq hout hf,
    fun _ hb => s.localFamily_linearTwo_degree (h := h) hG hM hJ hu hfull hK hq hout hb⟩

end CFSG.Quasithin.Chapter15.Section01
