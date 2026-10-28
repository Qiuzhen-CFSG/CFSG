module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryParabolics
public import Theory.SpecificGroups.BinaryLinear.CoreParabolicPair
public import Theory.SpecificGroups.BinaryLinear.SmallCubicRank

/-!
# Generating parabolics in the original constrained binary component

The literal SL₄(2) or SL₅(2) quotient has cubic rank two, so the original
Sylow subgroup normalizes the component. Lift the interior and endpoint
parabolics through its actual two-core. They are proper, contain S∩L,
are S-invariant, have characteristic two, and generate L. The endpoint
has core quotient S₃ × S₃; the interior image is the centralizer of the
center of the quotient Sylow. Both have flag descriptions under the same
original quotient marking.

These are the actual candidate subgroups in the binary branch of
15.1.22. Their placement in M or M_Z still requires the source family
argument, including the graph action in degree five; this does not yet
identify the generating pair with the two original intersections.
The catalogue owner retains that assembly and all small-block and general
Borel clauses. Original 15.1.14 remains with its existing producer.

Source: Aschbacher--Smith 15.1.22(3), printed pp.1099--1100.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The concrete interior/endpoint pair before its source placement. -/
structure BinaryGeneratingParabolics (d : CaseIComponentData T M Mc V) {n : ℕ}
    (e : (d.L ⧸ pCore 2 d.L) ≃* SL(n,ZMod 2)) where
  interior : Subgroup G
  endpoint : Subgroup G
  interior_proper : interior < d.L
  endpoint_proper : endpoint < d.L
  sylow_interior : d.SL ≤ interior
  sylow_endpoint : d.SL ≤ endpoint
  normalizes_interior : d.S ≤ normalizer (interior : Set G)
  normalizes_endpoint : d.S ≤ normalizer (endpoint : Set G)
  interior_fitting : generalizedFitting interior = pCore 2 interior
  endpoint_fitting : generalizedFitting endpoint = pCore 2 endpoint
  endpoint_quotient : Nonempty ((endpoint ⧸ pCore 2 endpoint) ≃*
    (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
  interior_parabolic : d.ConstrainedLinearParabolic e interior
  endpoint_parabolic : d.ConstrainedLinearParabolic e endpoint
  interior_image :
    let q := (e.trans (slEquivLinear n)).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L))
    (interior.subgroupOf d.L).map q =
      centralizer (centerIn ((d.SL.subgroupOf d.L).map q) : Set (LinearGroup n))
  generated : interior ⊔ endpoint = d.L

/-- Cubic rank two supplies S-normalization for every binary linear member
of the original local family, without ambient componenthood. -/
theorem localFamily_binary_linear_normalizes (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {n : ℕ} (hn : n = 4 ∨ n = 5) (e : (K ⧸ pCore 2 K) ≃* SL(n,ZMod 2)) :
    d.S ≤ normalizer (K : Set G) := by
  apply d.localFamily_normalizes_of_oddRank hG h hK hq Nat.prime_three (by decide)
  rw [primeRank_equiv 3 e]
  exact BinaryLinear.SmallCubicRank.four_or_five hn

omit [Finite G] in
private theorem embedded_sylow_invariant {K A : Subgroup G}
    (Q : Sylow 2 K) (hQ : (Q : Subgroup K).map K.subtype = A ⊓ K)
    (hn : A ≤ normalizer (K : Set G)) (C : Subgroup K)
    (hi : ∀ a : MulAut K, (Q : Subgroup K).map a.toMonoidHom = Q →
      C.map a.toMonoidHom = C) :
    A ≤ normalizer (C.map K.subtype : Set G) := by
  have hnQ : A ≤ normalizer ((A ⊓ K) : Set G) :=
    (le_inf A.le_normalizer hn).trans inf_normalizer_le_normalizer_inf
  intro x hx
  let a := K.normalizerMonoidHom ⟨x,hn hx⟩
  have he : K.subtype.comp a.toMonoidHom = (MulAut.conj x).toMonoidHom.comp K.subtype := rfl
  have ha : (Q : Subgroup K).map a.toMonoidHom = Q := by
    apply map_injective K.subtype_injective
    rw [map_map,he,←map_map,hQ]
    exact mem_normalizer_iff_map_conj_eq.mp (hnQ hx)
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (C.map K.subtype).map (MulAut.conj x).toMonoidHom = C.map K.subtype
  rw [map_map,←he,←map_map,hi a ha]

/-- Construct the actual generating pair on the specified literal quotient.
All invariance and fitting assertions are derived from the source hypotheses. -/
theorem constrained_binary_generating_parabolics (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    (hK : d.L ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (d.L ⧸ pCore 2 d.L))
    (hf : generalizedFitting d.L = pCore 2 d.L)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (e : (d.L ⧸ pCore 2 d.L) ≃* SL(n,ZMod 2)) :
    Nonempty (d.BinaryGeneratingParabolics e) := by
  obtain ⟨Q,hQ⟩ := ComponentModels.source20_sylow_intersection hK.2
  change (Q : Subgroup d.L).map d.L.subtype = d.SL at hQ
  have hnL := d.localFamily_binary_linear_normalizes hG h hK hq hn e
  obtain ⟨C,E,hgen,hC,hE,hQC,hQE,hCf,hEf,⟨eqE⟩,himage,hinv⟩ :=
    BinaryLinear.InvariantNodeActions.exists_core_parabolic_pair hf hn e Q
  let B := C.map d.L.subtype
  let D := E.map d.L.subtype
  have hBL : B < d.L := by
    apply lt_of_le_of_ne (map_subtype_le _)
    intro he
    apply hC
    apply map_injective d.L.subtype_injective
    simpa only [←MonoidHom.range_eq_map,range_subtype] using he
  have hDL : D < d.L := by
    apply lt_of_le_of_ne (map_subtype_le _)
    intro he
    apply hE
    apply map_injective d.L.subtype_injective
    simpa only [←MonoidHom.range_eq_map,range_subtype] using he
  have hSB : d.SL ≤ B := hQ ▸ map_mono hQC
  have hSD : d.SL ≤ D := hQ ▸ map_mono hQE
  let eB := C.equivMapOfInjective d.L.subtype d.L.subtype_injective
  let eD := E.equivMapOfInjective d.L.subtype d.L.subtype_injective
  have hBf : generalizedFitting B = pCore 2 B := by
    rw [←map_generalizedFitting_equiv eB,←pCore_map_iso 2 eB,hCf]
  have hDf : generalizedFitting D = pCore 2 D := by
    rw [←map_generalizedFitting_equiv eD,←pCore_map_iso 2 eD,hEf]
  refine ⟨⟨B,D,hBL,hDL,hSB,hSD,
    embedded_sylow_invariant Q hQ hnL C (fun a ha => (hinv a ha).1),
    embedded_sylow_invariant Q hQ hnL E (fun a ha => (hinv a ha).2),hBf,hDf,
    ⟨((QuotientGroup.congr _ _ eD (pCore_map_iso 2 eD)).symm.trans eqE)⟩,
    d.localFamily_binary_flag hK (by omega) e B hSB hBL,
    d.localFamily_binary_flag hK (by omega) e D hSD hDL,?_,?_⟩⟩
  · have hQ' : (Q : Subgroup d.L) = d.SL.subgroupOf d.L := by
      rw [←hQ]
      exact (comap_map_eq_self_of_injective d.L.subtype_injective _).symm
    rw [show B.subgroupOf d.L = C from
      comap_map_eq_self_of_injective d.L.subtype_injective C,←hQ']
    exact himage
  · have hh := congrArg (map d.L.subtype) hgen
    simpa only [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] using hh

/-- The original FF marking gives both original flag intersections and an
actual generating pair for the remaining binary placement argument. -/
theorem PreExclusionSource.constrained_binary_generation
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (e : d.normalizerImage d.L ≃* SL(n,ZMod 2)) :
    ∃ t : (d.L ⧸ pCore 2 d.L) ≃* SL(n,ZMod 2),
      (∀ x : d.L, t (QuotientGroup.mk' (pCore 2 d.L) x) = e (d.toNormalizerImage d.L x)) ∧
      d.ConstrainedLinearParabolic t d.ML ∧
      d.ConstrainedLinearParabolic t (M ⊓ d.L) ∧ Nonempty (d.BinaryGeneratingParabolics t) := by
  obtain ⟨t,ht,hML,hM⟩ := s.constrained_binary_linear_geometry (h := h) hG hempty hM hJ hu hf hn e
  exact ⟨t,ht,hML,hM,d.constrained_binary_generating_parabolics hG h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple hf hn t⟩

/-- Exchanged selection retains the same quotient and generating pair on
both plane sizes. -/
theorem ExchangedSource.constrained_binary_generation
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hf : generalizedFitting d.L = pCore 2 d.L)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (e : d.normalizerImage d.L ≃* SL(n,ZMod 2)) :
    ∃ t : (d.L ⧸ pCore 2 d.L) ≃* SL(n,ZMod 2),
      (∀ x : d.L, t (QuotientGroup.mk' (pCore 2 d.L) x) = e (d.toNormalizerImage d.L x)) ∧
      d.ConstrainedLinearParabolic t d.ML ∧
      d.ConstrainedLinearParabolic t (M ⊓ d.L) ∧ Nonempty (d.BinaryGeneratingParabolics t) := by
  obtain ⟨t,ht,hML,hM⟩ := s.constrained_binary_linear_geometry hG hempty hM hJ hu h hf hn e
  exact ⟨t,ht,hML,hM,d.constrained_binary_generating_parabolics hG h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple hf hn t⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]

/-- The actual original marker supplies the binary linear generating parabolics
on its selected component. Both original primes are retained; the earlier
15.1.14 input remains explicit for its existing producer and assembly owner. -/
theorem PreparedChosenModule.source_preExclusion_constrained_binary_generation
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
      (generalizedFitting d.L = pCore 2 d.L →
        ∀ n : ℕ, n = 4 ∨ n = 5 →
        ∀ e : d.normalizerImage d.L ≃* SL(n,ZMod 2),
        ∃ t : (d.L ⧸ pCore 2 d.L) ≃* SL(n,ZMod 2),
          (∀ x : d.L, t (QuotientGroup.mk' (pCore 2 d.L) x) = e (d.toNormalizerImage d.L x)) ∧
          d.ConstrainedLinearParabolic t d.ML ∧
          d.ConstrainedLinearParabolic t (M ⊓ d.L) ∧
          Nonempty (d.BinaryGeneratingParabolics t)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hf _ hn e =>
    s.constrained_binary_generation (h := h) hG hempty hM hJ hu hf hn e⟩
end CFSG.Quasithin.Chapter15.Section01
