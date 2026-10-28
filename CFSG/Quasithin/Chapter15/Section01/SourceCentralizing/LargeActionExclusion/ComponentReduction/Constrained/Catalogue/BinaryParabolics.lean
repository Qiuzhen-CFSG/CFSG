module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.ReducedModels
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.BinaryProperFlags
public import Theory.Alternating.OddCentralCovers
public import Theory.SpecificGroups.PSL5Two.UniversalCover
public import Theory.GroupTheory.PerfectCentralCoverEmbeddingRigidity

/-!
# Literal binary linear quotients and the two original parabolics

For the SL₄(2) and SL₅(2) FF rows, the original map K/O₂(K) → K* is
bijective. In degree four, the A₈ covering bound and the original odd
center restriction remove its kernel. In degree five, the actual universal
cover has trivial kernel. Thus the model isomorphism identifies the literal
two-core quotient, compatibly with every original element.

Every proper overgroup of S∩K has a nonempty flag image under that same
marking. Applied to the selected component this identifies both M_Z∩L and
M∩L as parabolics. The original pre-exclusion and exchanged applications
retain the same component, seed and maps, without a choice of source prime.

This discharges the quotient and parabolic assertions for the binary linear
branch of ConstrainedAlternatives. Generation of L by the two parabolics,
the remaining small block branches, and general local-family Borel placement
remain with qt-e-1515-constrained-source-catalogue. Original 15.1.14 retains
its existing producer and pre-exclusion assembly owner.

Source: Aschbacher--Smith 15.1.20(2c) and 15.1.22(3), printed pp.1095,
1098--1100; I.1.3 and GLS3 5.2.3 for the covering calculations.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The binary linear FF rows have no comparison kernel above O₂(K). -/
theorem NormalizerAction.binary_linear_core_bijective
    {d : CaseIComponentData T M Mc V} {K : Subgroup G}
    (a : d.NormalizerAction K)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    (hK : K ≤ d.G1) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {n : ℕ} (hn : n = 4 ∨ n = 5) (e : d.normalizerImage K ≃* SL(n,ZMod 2)) :
    Function.Bijective a.coreToImage := by
  let := hq
  rcases hn with rfl | rfl
  · let t : d.normalizerImage K ≃* alternatingGroup (Fin 8) :=
      e.trans (Atlas.Order20160A8.sl4TwoEquivPSL.trans
        Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm)
    let c : PerfectCentralCovering.Cover (K ⧸ pCore 2 K) (alternatingGroup (Fin 8)) :=
      { toMonoidHom := t.toMonoidHom.comp a.coreToImage
        surjective := t.surjective.comp a.coreToImage_surjective
        isPerfect := hq.toIsPerfect
        ker_le_center := by
          rw [MonoidHom.ker_comp_of_injective _ _ t.injective]
          exact a.coreToImage_ker_central hq }
    let z := c.quotientCenterEquiv.trans
      ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by simp))).trans
        QuotientGroup.quotientBot)
    have hd := GLS3.Chapter5.OddCentralCovers.center_card_dvd_two_of_nonexceptional
      8 (by decide) (by decide) (by decide) z
    have hz : center (K ⧸ pCore 2 K) = ⊥ := by
      apply (eq_bot_iff_card _).mpr
      rcases d.localFamily_coreQuotient_center_card hG h hK hq with hc | hc
      · exact hc
      · rw [hc] at hd
        norm_num at hd
    exact ⟨(MonoidHom.ker_eq_bot_iff _).mp (bot_unique
      ((a.coreToImage_ker_central hq).trans hz.le)),a.coreToImage_surjective⟩
  · let t := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 5)).symm
    let c : PerfectCentralCovering.Cover (K ⧸ pCore 2 K) PSL(5,ZMod 2) :=
      { toMonoidHom := t.toMonoidHom.comp a.coreToImage
        surjective := t.surjective.comp a.coreToImage_surjective
        isPerfect := hq.toIsPerfect
        ker_le_center := by
          rw [MonoidHom.ker_comp_of_injective _ _ t.injective]
          exact a.coreToImage_ker_central hq }
    have hi := c.injective_of_universalProjection_ker_eq_bot
      (Theory.SpecificGroups.PSL5Two.UniversalCover.field_universalProjection_ker_eq_bot
        (ZMod 2) (by simp))
    exact ⟨fun _ _ hh => hi (congrArg t hh),a.coreToImage_surjective⟩

open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

/-- Proper overgroups of the original Sylow intersection have actual flag
images under the specified isomorphism of the literal two-core quotient. -/
theorem localFamily_binary_flag (d : CaseIComponentData T M Mc V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    {n : ℕ} (hn : 0 < n) (e : (K ⧸ pCore 2 K) ≃* SL(n,ZMod 2))
    (P : Subgroup G) (hSP : d.S ⊓ K ≤ P) (hP : P < K) :
    ∃ k : ℕ, 0 < k ∧ ∃ f : LinearFlag (ZMod 2) n k,
      ((P.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))).map e.toMonoidHom =
        f.stabilizer := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  obtain ⟨S,hS⟩ := ComponentModels.source20_sylow_intersection hK.2
  let q := QuotientGroup.mk' (pCore 2 K)
  have hPS : (S : Subgroup K) ≤ P.subgroupOf K := by
    intro x hx
    exact hSP (hS ▸ mem_map_of_mem K.subtype hx)
  have hk : q.ker ≤ P.subgroupOf K := by
    rw [QuotientGroup.ker_mk']
    exact (pCore_isPGroup.le_sylow_of_normal S).trans hPS
  have hp : (P.subgroupOf K).map q ≠ ⊤ := by
    intro he
    have hh := comap_map_eq_self hk
    rw [he,comap_top] at hh
    exact hP.ne (le_antisymm hP.le (subgroupOf_eq_top.mp hh.symm))
  exact binary_flag_of_sylow_overgroup e _
    (S.mapSurjective (QuotientGroup.mk'_surjective _)) (map_mono hPS) hp

/-- Both original intersections are proper flag parabolics under the same
literal quotient marking. No generation conclusion is inferred here. -/
theorem constrained_binary_flags (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hK : d.L ∈ Chapter1.LIn d.G1 d.S)
    {n : ℕ} (hn : 0 < n) (e : (d.L ⧸ pCore 2 d.L) ≃* SL(n,ZMod 2)) :
    d.ConstrainedLinearParabolic e d.ML ∧
      d.ConstrainedLinearParabolic e (M ⊓ d.L) := by
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hS : d.S ≤ d.MZ := by
    refine le_inf d.S_le_G1 ?_
    intro x hx
    apply hMc.2
    intro z hz
    exact (centralInvolutions_le_centralizer_sylow T hz x (d.S_le_T hx)).symm
  constructor
  · apply d.localFamily_binary_flag hK hn e d.ML (inf_le_inf_right _ hS)
    exact lt_of_le_of_ne inf_le_right (fun he => d.L_not_le_MZ (he ▸ inf_le_left))
  · apply d.localFamily_binary_flag hK hn e (M ⊓ d.L)
      (inf_le_inf_right _ (d.S_le_T.trans hM.1.2))
    exact lt_of_le_of_ne inf_le_right
      (fun he => d.localFamily_not_le_M hG hempty hM hu hK d.L_not_le_MZ (he ▸ inf_le_left))

/-- The binary linear FF row supplies its actual two-core quotient and
both required source parabolics, preserving the given FF marking. -/
theorem localFamily_binary_linear_geometry (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hK : d.L ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (d.L ⧸ pCore 2 d.L))
    (hf : generalizedFitting d.L = pCore 2 d.L)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (e : d.normalizerImage d.L ≃* SL(n,ZMod 2)) :
    ∃ t : (d.L ⧸ pCore 2 d.L) ≃* SL(n,ZMod 2),
      (∀ x : d.L, t (QuotientGroup.mk' (pCore 2 d.L) x) = e (d.toNormalizerImage d.L x)) ∧
      d.ConstrainedLinearParabolic t d.ML ∧
      d.ConstrainedLinearParabolic t (M ⊓ d.L) := by
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h hK hq d.L_not_le_MZ hf
  let t := (MulEquiv.ofBijective a.coreToImage
    (a.binary_linear_core_bijective hG h hK.1 hq hn e)).trans e
  exact ⟨t,fun _ => rfl,d.constrained_binary_flags hG hempty hM hu hK (by omega) t⟩

/-- Original pre-exclusion application, independent of the source prime. -/
theorem PreExclusionSource.constrained_binary_linear_geometry
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
      d.ConstrainedLinearParabolic t (M ⊓ d.L) :=
  d.localFamily_binary_linear_geometry hG hempty hM hJ hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple hf hn e

/-- The later exchanged source uses the identical maps on both planes. -/
theorem ExchangedSource.constrained_binary_linear_geometry
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hf : generalizedFitting d.L = pCore 2 d.L)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (e : d.normalizerImage d.L ≃* SL(n,ZMod 2)) :
    ∃ t : (d.L ⧸ pCore 2 d.L) ≃* SL(n,ZMod 2),
      (∀ x : d.L, t (QuotientGroup.mk' (pCore 2 d.L) x) = e (d.toNormalizerImage d.L x)) ∧
      d.ConstrainedLinearParabolic t d.ML ∧
      d.ConstrainedLinearParabolic t (M ⊓ d.L) :=
  d.localFamily_binary_linear_geometry hG hempty hM hJ hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple hf hn e

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]

/-- The actual original marker supplies the binary linear parabolic clauses
on its selected component. Both original primes are retained; the earlier
15.1.14 input remains explicit for its existing producer and assembly owner. -/
theorem PreparedChosenModule.source_preExclusion_constrained_binary_parabolics
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
          d.ConstrainedLinearParabolic t (M ⊓ d.L)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hf _ hn e =>
    s.constrained_binary_linear_geometry (h := h) hG hempty hM hJ hu hf hn e⟩
end CFSG.Quasithin.Chapter15.Section01
