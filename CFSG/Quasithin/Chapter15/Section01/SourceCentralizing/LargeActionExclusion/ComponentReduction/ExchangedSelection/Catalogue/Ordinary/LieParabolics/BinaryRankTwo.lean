module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.LieParabolics.RankTwoRefinement
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.HigherField.Triality
public import Theory.GroupTheory.InnerSylowNormalizer
public import Theory.SpecificGroups.Triality.BinaryParabolicGeometry

/-!
# Complete ordinary binary rank-two rows before exchanged selection

The genuine triality carrier has no outer two-automorphisms. Its original
component is normal by cubic rank, so the original Sylow action is inner.
Sylow maximality in the inner automorphism group splits S into S_L and
C_S(L). The entire component Borel therefore normalizes S and J(S)=J(T),
and the original Thompson-normalizer control places it in M.

The already proved cubic residual escape makes M ∩ L strictly contain
that Borel. Genuine graph-field D₄ geometry makes every proper strict
Borel overgroup a maximal parabolic. Together with the original maximal
Sylow-center centralizer and the literal residual-centralizer identity,
this proves every clause of the binary triality row. Combining it with
G₂(2)′ and Tits completes the entire OrdinaryBinaryRankTwo family at both
source primes. The same-marker application retains d, Z₁, row and prime.

No parabolic-placement or exchanged-plane premise is added. The linear
and remaining sporadic Ordinary22 branches stay with
qt-e-15122-ordinary-pre-exclusion. The earlier 15.1.14 residual premise
and final catalogue discharge stay with qt-e-15122-pre-exclusion-catalogue.
Source: Aschbacher--Smith, 15.1.17 and 15.1.22(4), printed pp.1093,
1098--1099, refs/quasithin.pdf; the genuine root geometry follows
GLS3 §§2.3--2.6 as cited in the model construction.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- Innerness of the original Sylow action places the entire triality Borel
in the original Thompson normalizer and therefore in M. -/
theorem PreExclusionSource.triality_borel_le_selected
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : d.L ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) : d.ordinaryBorel ≤ M := by
  have hn : d.S ≤ normalizer (d.L : Set G) := d.S_le_G1.trans
    ((normal_subgroupOf_iff_le_normalizer d.L_component.1).mp
      (s.triality_normal (h := h) hG hL 1 Nat.zero_lt_one e))
  have hS : IsPGroup 2 d.S := T.isPGroup'.to_le d.S_le_T
  obtain ⟨P,hP⟩ := s.component_sylow
  let a := d.L.normalizerMonoidHom.comp (inclusion hn)
  let A := a.range
  have hA : IsPGroup 2 A := hS.of_surjective a.rangeRestrict a.rangeRestrict_surjective
  have hi (x : d.S) : a x ∈ MulAut.innerSubgroup d.L := by
    have hm : MulAut.congr e (a x) ∈ A.map (MulAut.congr e).toMonoidHom :=
      mem_map_of_mem _ (show a x ∈ A from ⟨x,rfl⟩)
    obtain ⟨u,hu⟩ := Triality.Standard.ParabolicOuterTwo.twoSubgroup_le_inner_at_two
      (A.map (MulAut.congr e).toMonoidHom) (hA.map (MulAut.congr e).toMonoidHom) hm
    obtain ⟨v,hv⟩ := (MulAut.congr_inner_iff e (a x)).mp ⟨u,hu.symm⟩
    exact ⟨v,hv.symm⟩
  have hSL : d.SL.subgroupOf d.L = (P : Subgroup d.L) := by
    apply map_injective (f := d.L.subtype) d.L.subtype_injective
    rw [map_subgroupOf_eq_of_le (show d.SL ≤ d.L from inf_le_right),hP]
  have hBN : d.ordinaryBorel ≤ normalizer (d.S : Set G) := by
    change (normalizer (d.SL.subgroupOf d.L : Set d.L)).map d.L.subtype ≤ _
    rw [hSL]
    exact embedded_sylow_normalizer_le_of_inner d.L d.S hn hS P
      (by rw [hP]; exact inf_le_left) hi
  have hJS := (h.caseI_marked_thompson_control hG T hM hJ d.Z1_le_fixed).1
  have hNJ := (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1
  rw [← hJS] at hNJ
  exact (hBN.trans (normalizer_le_normalizer_elementaryAbelianMaxJ d.S)).trans hNJ

/-- Both actual maximal parabolics and the residual-centralizer identity
of the ordinary binary triality row, under the original source hypotheses. -/
theorem PreExclusionSource.ordinary22_of_binaryTriality
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : d.L ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) : d.Ordinary22Alternatives := by
  have hp3 := s.prime_three_of_binaryRankTwo (h := h) hp hG hM hJ hu hL (.inr (.inr ⟨e⟩))
  subst p
  have hr := s.triality_localThreeResidual_escape (h := h) hG hL e
  have hmarked := s.centralizer_eq_of_sylow_fixers (h := h) hG hM hu hL e
    (fun _ a ha _ => by
      have ha2 : IsPGroup 2 (zpowers a) := IsPGroup.of_card_dvd_pow (n := 1)
        (by simpa only [Nat.card_zpowers,pow_one] using orderOf_dvd_of_pow_eq_one ha)
      obtain ⟨t,ht⟩ := Triality.Standard.ParabolicOuterTwo.twoSubgroup_le_inner_at_two
        (zpowers a) ha2 (mem_zpowers a)
      exact ⟨t,ht.symm⟩)
    (Triality.Standard.SylowCenterMaximal.centralizer_isCoatom e)
  obtain ⟨P,hP⟩ := s.component_sylow
  have hloc := s.local_intersections (h := h) hG hu hM.1.2
  have hSL : d.SL.subgroupOf d.L = (P : Subgroup d.L) := by
    apply map_injective (f := d.L.subtype) d.L.subtype_injective
    rw [map_subgroupOf_eq_of_le (show d.SL ≤ d.L from inf_le_right),hP]
  have hB : d.ordinaryBorel = (normalizer (P : Set d.L)).map d.L.subtype := by
    change (normalizer (d.SL.subgroupOf d.L : Set d.L)).map d.L.subtype = _
    rw [hSL]
    rfl
  have hZ : ((center P).map (P : Subgroup d.L).subtype).map d.L.subtype =
      (center d.SL).map d.SL.subtype := by
    rw [map_map, ← map_center_image_of_injective (P : Subgroup d.L)
      d.L.subtype d.L.subtype_injective,hP]
  have hC : d.ML.subgroupOf d.L =
      centralizer ((center P).map (P : Subgroup d.L).subtype : Set d.L) := by
    rw [hmarked]
    ext x
    constructor
    · intro hx z hz
      exact Subtype.ext (hx.2 z (hZ ▸ mem_map_of_mem d.L.subtype hz))
    · intro hx
      refine ⟨x.property,?_⟩
      intro z hz
      obtain ⟨w,hw,rfl⟩ := hZ.symm ▸ hz
      exact congrArg Subtype.val (hx w hw)
  have hgeo := Triality.Standard.BinaryParabolicGeometry.borel_geometry e P
  have hBML : d.ordinaryBorel ≤ d.ML := by
    rw [hB]
    have hm := map_mono (f := d.L.subtype) hgeo.1
    rw [← hC,map_subgroupOf_eq_of_le (show d.ML ≤ d.L from inf_le_right)] at hm
    exact hm
  have hBother : d.ordinaryBorel ≤ M ⊓ d.L := le_inf
    (s.triality_borel_le_selected (h := h) hG hM hJ hL e)
    (by rw [hB]; exact map_subtype_le _)
  have hout : ¬ M ⊓ d.L ≤ d.ML := fun hh => hr ((map_subtype_le _).trans hh)
  have hother : IsCoatom ((M ⊓ d.L).subgroupOf d.L) := by
    apply hgeo.2 _
    · intro he
      exact (not_le_of_gt hloc.2.2.2.2.1) (subgroupOf_eq_top.mp he)
    · apply map_le_iff_le_comap.mp
      exact hB ▸ hBother
    · rw [← hC]
      intro hh
      have hm := map_mono (f := d.L.subtype) hh
      rw [map_subgroupOf_eq_of_le inf_le_right,
        map_subgroupOf_eq_of_le (show d.ML ≤ d.L from inf_le_right)] at hm
      exact hout hm
  exact .binaryRankTwo (.inr (.inr ⟨e⟩)) hmarked ⟨hloc.2.2.1,hBML⟩
    ⟨hloc.2.2.2.2.1,hBother⟩ (hC.symm ▸ Triality.Standard.SylowCenterMaximal.centralizer_isCoatom e P)
    hother (fun he => hout he.ge)
    (s.triality_ordinaryCentralizerIdentity (h := h) (.inl rfl) hG hM hJ hu hL e)

/-- All three original ordinary binary rank-two rows are complete. -/
theorem PreExclusionSource.ordinary22_of_binaryRankTwo
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : OrdinaryBinaryRankTwo d.L) : d.Ordinary22Alternatives := by
  unfold OrdinaryBinaryRankTwo at hm
  rcases hm with he | he | he <;> obtain ⟨e⟩ := he
  · exact s.ordinary22_of_binaryG2Derived (h := h) hp hG hM hJ hu hL e
  · exact s.ordinary22_of_tits (h := h) hp hG hM hJ hu hL e
  · exact s.ordinary22_of_binaryTriality (h := h) hp hG hM hJ hu hL e
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original marker receives the complete G₂(2)′, Tits and binary
triality rows, with the same d, Z₁, source row and literal prime. -/
theorem PreparedChosenModule.source_preExclusion_binary_rankTwo_catalogue
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized) (hp : m.prime = 3 ∨ m.prime = 5)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (IsComponent d.G1 (d.L.subgroupOf d.G1) →
        CaseIComponentData.OrdinaryBinaryRankTwo d.L →
          m.prime = 3 ∧ d.Ordinary22Alternatives) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hL hm =>
    ⟨s.prime_three_of_binaryRankTwo (h := h) hp hG hM hJ hu hL hm,
      s.ordinary22_of_binaryRankTwo (h := h) hp hG hM hJ hu hL hm⟩⟩

end CFSG.Quasithin.Chapter15.Section01
