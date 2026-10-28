module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalBorelTorus

/-!
# The exact intersection in an escaping natural local block

The original residual-intersection identity makes a two-perfect subgroup
of M ∩ M_Z centralize V. Consequently the Borel of an escaping natural
block cannot lie in M_Z: the full-cover centralizer comparison would put
K itself in M_Z. Its Sylow subgroup has prime index p in the Borel, by
the previously proved faithful torus action. Since M_Z ∩ K is between
these two subgroups, it must equal S ∩ K. The other intersection M ∩ K
is the whole Borel, and their relative index is exactly the original p.

Thus the remaining cubic field-four case of 15.1.20(2a) requires excluding
the escaping local block; field restriction alone does not supply lower
Borel containment. For actual C-components of G₁, the established orbit
argument supplies that containment and gives the exclusion here for every
such K, without replacing the original selected-component data. The
general local-member exclusion and the final source assembly remain open.

The original-marker application retains G₁, M_Z, S, Q₁ and either source
prime. Original 15.1.14 remains explicit at its existing assembly owner;
the independently owned whole-core A₆ reconstruction is unchanged.

Source: Aschbacher--Smith 15.1.18(2), 15.1.20(2a) and 15.1.21(i), printed
pp.1092, 1094, 1097--1098.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem natural_borel_index (d : CaseIComponentData T M Mc V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    {n : ℕ} (hb : IsL2EvenBlock K n) :
    (d.S ⊓ K).relIndex (d.localSylowBorel K) = 2 ^ n - 1 := by
  obtain ⟨P,hP⟩ := ComponentModels.source20_sylow_intersection hK.2
  have he : (P : Subgroup K) = (d.S ⊓ K).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le inf_le_right]
  have hB : (normalizer (P : Set K)).map K.subtype = d.localSylowBorel K := by
    rw [d.localSylowBorel_eq,←he]
    rfl
  rw [←hP,←hB,relIndex_map_map_of_injective _ _ K.subtype_injective]
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
  have heK : f.ker = (P : Subgroup K).subgroupOf (normalizer (P : Set K)) := by
    ext x
    exact hker x
  change ((P : Subgroup K).subgroupOf (normalizer (P : Set K))).index = _
  rw [←heK,index_ker,MonoidHom.range_eq_top.mpr hf,
    Nat.card_congr Subgroup.topEquiv.toEquiv,Nat.card_units,hF]

/-- An escaping natural local block cannot have its full Borel in M_Z:
the original residual identity and Sylow centralizer comparison would
make the whole block centralize the original local module. -/
theorem PreExclusionSource.localFamily_linearTwo_borel_not_le_MZ
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    {n : ℕ} (hb : IsL2EvenBlock K n) : ¬ d.localSylowBorel K ≤ d.MZ := by
  intro hBZ
  have hBM := d.localFamily_linearTwo_borel_le_selected hG hM hJ hu h hK hq hout hb
  have hBV := s.twoPerfect_intersection_centralizes (h := h)
    (d.localFamily_linearTwo_borel_twoPerfect hK hb) hBM hBZ
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
    ((le_inf hVS (le_centralizer_iff.mp hBV)).trans_eq
      (d.localFamily_linearTwo_borel_centralizer hK hb)).trans inf_le_right
  have hKV := le_centralizer_iff.mp hVK
  rw [hfull] at hKV
  exact hout (le_inf hK.1 (hKV.trans (localModule_centralizer_le_partner T M hu)))

/-- The marked intersection of an escaping natural local member is its
actual Sylow subgroup. This is a necessary condition on the remaining
case, not the Borel conclusion of original 15.1.20. -/
theorem PreExclusionSource.localFamily_linearTwo_marked_eq_sylow
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
    d.MZ ⊓ K = d.S ⊓ K := by
  have hSM : d.S ≤ d.MZ := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    intro x hx
    exact ⟨d.S_le_G1 hx,hMc.2 (fun z hz =>
      (centralInvolutions_le_centralizer_sylow T hz x (d.S_le_T hx)).symm)⟩
  have hPA : d.S ⊓ K ≤ d.MZ ⊓ K := inf_le_inf_right K hSM
  have hAB : d.MZ ⊓ K ≤ d.localSylowBorel K :=
    (d.localFamily_linearTwo_borel_bound hu hK hout hb).trans_eq
      (d.localSylowBorel_eq K).symm
  apply le_antisymm ?_ hPA
  by_contra hnot
  have he := relIndex_mul_relIndex (d.S ⊓ K) (d.MZ ⊓ K) (d.localSylowBorel K) hPA hAB
  rw [natural_borel_index d hK hb,
    s.localFamily_linearTwo_torus_eq_prime (h := h) hG hM hJ hu hfull hK hq hout hb hp2] at he
  have hp : ((d.S ⊓ K).relIndex (d.MZ ⊓ K) *
      (d.MZ ⊓ K).relIndex (d.localSylowBorel K)).Prime := he ▸ s.prime_prime
  rcases Nat.prime_mul_iff.mp hp with ⟨_,heB⟩ | ⟨_,heP⟩
  · exact s.localFamily_linearTwo_borel_not_le_MZ (h := h) hG hM hJ hu hfull hK hq hout hb
      ((relIndex_eq_one.mp heB).trans inf_le_left)
  · exact hnot (relIndex_eq_one.mp heP)

/-- Both original intersections and their relative index, retaining the
same K and the prime in the original marked action. -/
theorem PreExclusionSource.localFamily_linearTwo_intersections
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
    {n : ℕ} (hb : IsL2EvenBlock K n) (hp2 : p ≠ 2) :
    M ⊓ K = d.localSylowBorel K ∧ d.MZ ⊓ K = d.S ⊓ K ∧
      (d.MZ ⊓ K).relIndex (M ⊓ K) = p := by
  have hB := d.localFamily_linearTwo_selected_borel hG hempty hM hJ hu h hK hq hout hb
  have hP := s.localFamily_linearTwo_marked_eq_sylow (h := h) hG hM hJ hu hfull hK hq hout hb hp2
  refine ⟨hB,hP,?_⟩
  rw [hB,hP,natural_borel_index d hK hb]
  exact s.localFamily_linearTwo_torus_eq_prime (h := h) hG hM hJ hu hfull hK hq hout hb hp2

/-- The natural local-member exclusion is complete in the actual ambient
C-component branch. No new component selection or source record is used. -/
theorem PreExclusionSource.localFamily_linearTwo_le_MZ_of_cComponent
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
    (hcomp : (K.subgroupOf d.G1).IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {n : ℕ} (hb : IsL2EvenBlock K n) : K ≤ d.MZ := by
  by_contra hout
  have he := s.localFamily_linearTwo_borel_of_cComponent (h := h)
    hG hM hu hne hmany hres hK hcomp hq hout hb
  apply s.localFamily_linearTwo_borel_not_le_MZ (h := h) hG hM hJ hu hfull hK hq hout hb
  rw [d.localSylowBorel_eq,←he]
  exact inf_le_left

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Stellmacher ChapterC
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- On the original marked action, every escaping natural local member
has the exact cubic Sylow intersection and fails ambient C-componenthood.
This retains both source primes and the earlier 15.1.14 premise; it does
not assume or conclude the missing general Borel containment. -/
theorem PreparedChosenModule.source_preExclusion_local_natural_intersections
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
          m.prime = 3 ∧ n = 2 ∧
            M ⊓ K = d.localSylowBorel K ∧ d.MZ ⊓ K = d.S ⊓ K ∧
            (d.MZ ⊓ K).relIndex (M ⊓ K) = 3 ∧
            ¬ (K.subgroupOf d.G1).IsCComponent := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout n hb
  obtain ⟨hp3,hn⟩ := s.localFamily_linearTwo_small_field (h := h)
    hp hG hM hJ hu hfull hK hq hout hb
  obtain ⟨hB,hP,hi⟩ := s.localFamily_linearTwo_intersections (h := h)
    hG hempty hM hJ hu hfull hK hq hout hb (by omega)
  refine ⟨hp3,hn,hB,hP,hi.trans hp3,?_⟩
  intro hcomp
  exact hout (s.localFamily_linearTwo_le_MZ_of_cComponent (h := h)
    hG hM hJ hu hne hmany hfull hres hK hcomp hq hb)

end CFSG.Quasithin.Chapter15.Section01
