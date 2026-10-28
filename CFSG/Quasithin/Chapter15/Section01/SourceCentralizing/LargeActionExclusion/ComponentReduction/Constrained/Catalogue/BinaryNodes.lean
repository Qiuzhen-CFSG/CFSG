module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryExtensions
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.CoreFlags

/-!
# Node selection for the constrained binary generating pair

The original Sylow action on the literal two-core quotient either is
inner on every element or contains a graph automorphism. In the first
case every partial flag has an S-invariant full preimage. In the second,
both original intersections are S_L, the interior parabolic, or the
endpoint parabolic. The interior is identified by the quotient Sylow
center; generation forces the endpoint to be the complementary flag.
Thus these are the same actual pair and quotient marking as before.

This proves the node alternatives used in 15.1.22(3). Selecting the wreath
quotient, excluding A₃ products, and placing the two generators in opposite
original intersections remain source obligations. The small-block and
general Borel clauses also remain with the catalogue owner. The original
15.1.14 input stays with its existing producer and assembly owner.

Source: Aschbacher--Smith 15.1.22(3), printed pp.1099--1100.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open BinaryLinear.InvariantNodeActions BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Positions in the actual previously constructed generating pair. -/
def BinaryNodePosition (d : CaseIComponentData T M Mc V) {m : ℕ}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(m+1,ZMod 2)}
    (a : d.BinaryGeneratingParabolics e) (P : Subgroup G) : Prop :=
  P = d.SL ∨ P = a.interior ∨ P = a.endpoint

/-- A common node marking, with the actual action on both original intersections. -/
structure BinaryNodeGeometry (d : CaseIComponentData T M Mc V) {m : ℕ}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(m+1,ZMod 2)}
    (a : d.BinaryGeneratingParabolics e) where
  normalizes : d.S ≤ normalizer (d.L : Set G)
  basis : Basis m
  sylow_image : (d.SL.subgroupOf d.L).map (coreFlagMap d.L e) =
    cutStabilizer basis Set.univ
  interior_marking : a.interior = EquivariantLift.lift d.L (coreFlagMap d.L e)
    (cutStabilizer basis {i | i.val=0 ∨ i.val=m-1})
  action :
    ((∀ x : d.S, coreFlagAction d.L d.S normalizes e x ∈ MulAut.innerSubgroup _) ∧
      ∀ cuts : Set (Fin m), d.S ≤ normalizer
        (EquivariantLift.lift d.L (coreFlagMap d.L e) (cutStabilizer basis cuts) : Set G)) ∨
    ((∃ x : d.S, coreFlagAction d.L d.S normalizes e x ∉ MulAut.innerSubgroup _) ∧
      a.endpoint = EquivariantLift.lift d.L (coreFlagMap d.L e)
        (cutStabilizer basis {i | i.val=0 ∨ i.val=m-1}ᶜ) ∧
      d.BinaryNodePosition a d.ML ∧ d.BinaryNodePosition a (M ⊓ d.L))

/-- The original Sylow action either fixes every node, or both original
intersections are one of the three exact graph-invariant preimages. -/
theorem constrained_binary_node_geometry (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hK : d.L ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (d.L ⧸ pCore 2 d.L))
    {m : ℕ} (hm : m=3 ∨ m=4) (e : (d.L ⧸ pCore 2 d.L) ≃* SL(m+1,ZMod 2))
    (a : d.BinaryGeneratingParabolics e) : Nonempty (d.BinaryNodeGeometry a) := by
  have hn := d.localFamily_binary_linear_normalizes hG h hK hq (by omega) e
  obtain ⟨Q,hQ⟩ := ComponentModels.source20_sylow_intersection hK.2
  obtain ⟨b,hb,hbctrl⟩ := exists_core_flag_control d.L d.S hn Q hQ hm e
  let q := coreFlagMap d.L e
  have hQS : (Q : Subgroup d.L) = d.SL.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [map_subgroupOf_eq_of_le (show d.SL ≤ d.L from inf_le_right)]
    exact hQ
  let U := Q.mapSurjective (coreFlagMap_surjective d.L e)
  have hU : (U : Subgroup (LinearGroup (m+1))) = (d.SL.subgroupOf d.L).map q := by
    change (Q : Subgroup d.L).map q = _
    rw [hQS]
  have hbU : (U : Subgroup (LinearGroup (m+1))) = cutStabilizer b Set.univ := hU.trans hb
  have hCI := a.interior_image
  change (a.interior.subgroupOf d.L).map q =
    centralizer (centerIn ((d.SL.subgroupOf d.L).map q) : Set (LinearGroup (m+1))) at hCI
  rw [←hU,centerIn_eq_map_center,sylow_center_centralizer_eq_endCuts (by omega) U b hbU] at hCI
  have hkI : q.ker ≤ a.interior.subgroupOf d.L := by
    rw [coreFlagMap_ker]
    apply (pCore_isPGroup.le_sylow_of_normal Q).trans
    rw [hQS]
    exact subgroupOf_mono d.L a.sylow_interior
  have hC : a.interior = EquivariantLift.lift d.L q
      (cutStabilizer b {i | i.val=0 ∨ i.val=m-1}) := by
    have he := EquivariantLift.lift_map_subgroupOf d.L q a.interior a.interior_proper.le hkI
    rw [hCI] at he
    exact he.symm
  refine ⟨⟨hn,b,hb,hC,?_⟩⟩
  rcases hbctrl with hi | ⟨ho,hctrl⟩
  · exact Or.inl hi
  · have hnot : ¬ a.endpoint ≤ a.interior := by
      intro he
      exact a.interior_proper.ne ((sup_eq_left.mpr he).symm.trans a.generated)
    have hE : a.endpoint = EquivariantLift.lift d.L q
        (cutStabilizer b {i | i.val=0 ∨ i.val=m-1}ᶜ) := by
      rcases hctrl a.endpoint a.sylow_endpoint a.endpoint_proper a.normalizes_endpoint with he | he | he
      · exact (hnot (he.symm ▸ a.sylow_interior)).elim
      · exact (hnot (he.trans hC.symm).le).elim
      · exact he
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    have hSMZ : d.S ≤ d.MZ := by
      refine le_inf d.S_le_G1 ?_
      intro x hx
      exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz x (d.S_le_T hx)).symm)
    have hSM : d.S ≤ M := d.S_le_T.trans hM.1.2
    have hML : d.ML < d.L :=
      lt_of_le_of_ne inf_le_right (fun he => d.L_not_le_MZ (he ▸ inf_le_left))
    have hML' : M ⊓ d.L < d.L := lt_of_le_of_ne inf_le_right
      (fun he => d.localFamily_not_le_M hG hempty hM hu hK d.L_not_le_MZ (he ▸ inf_le_left))
    have hnML : d.S ≤ normalizer (d.ML : Set G) :=
      (le_inf (hSMZ.trans d.MZ.le_normalizer) hn).trans inf_normalizer_le_normalizer_inf
    have hnML' : d.S ≤ normalizer ((M ⊓ d.L) : Set G) :=
      (le_inf (hSM.trans M.le_normalizer) hn).trans inf_normalizer_le_normalizer_inf
    have hpos (P : Subgroup G) (hSP : d.SL ≤ P) (hP : P < d.L)
        (hnP : d.S ≤ normalizer (P : Set G)) : d.BinaryNodePosition a P := by
      have hp := hctrl P hSP hP hnP
      change P = d.SL ∨ P = _ ∨ P = _ at hp
      rw [←hC,←hE] at hp
      exact hp
    exact Or.inr ⟨ho,hE,hpos d.ML (inf_le_inf_right _ hSMZ) hML hnML,
      hpos (M ⊓ d.L) (inf_le_inf_right _ hSM) hML' hnML'⟩

/-- Both original primes retain the actual generating pair and endpoint
extension together with the original action's node alternatives. -/
theorem PreExclusionSource.constrained_binary_nodes
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    {m : ℕ} (hm : m=3 ∨ m=4) (e : d.normalizerImage d.L ≃* SL(m+1,ZMod 2)) :
    ∃ t : (d.L ⧸ pCore 2 d.L) ≃* SL(m+1,ZMod 2),
      (∀ x : d.L, t (QuotientGroup.mk' (pCore 2 d.L) x) = e (d.toNormalizerImage d.L x)) ∧
      d.ConstrainedLinearParabolic t d.ML ∧
      d.ConstrainedLinearParabolic t (M ⊓ d.L) ∧
      ∃ a : d.BinaryGeneratingParabolics t,
        d.BinaryEndpointExtension a.endpoint ∧ Nonempty (d.BinaryNodeGeometry a) := by
  obtain ⟨t,ht,hML,hM',a,ha⟩ :=
    s.constrained_binary_extensions (h := h) hG hempty hM hJ hu hf (by omega) e
  exact ⟨t,ht,hML,hM',a,ha,d.constrained_binary_node_geometry hG hempty hM hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple hm t a⟩

/-- Exchanged selection uses the same marked node alternatives on both planes. -/
theorem ExchangedSource.constrained_binary_nodes
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hf : generalizedFitting d.L = pCore 2 d.L)
    {m : ℕ} (hm : m=3 ∨ m=4) (e : d.normalizerImage d.L ≃* SL(m+1,ZMod 2)) :
    ∃ t : (d.L ⧸ pCore 2 d.L) ≃* SL(m+1,ZMod 2),
      (∀ x : d.L, t (QuotientGroup.mk' (pCore 2 d.L) x) = e (d.toNormalizerImage d.L x)) ∧
      d.ConstrainedLinearParabolic t d.ML ∧
      d.ConstrainedLinearParabolic t (M ⊓ d.L) ∧
      ∃ a : d.BinaryGeneratingParabolics t,
        d.BinaryEndpointExtension a.endpoint ∧ Nonempty (d.BinaryNodeGeometry a) := by
  obtain ⟨t,ht,hML,hM',a,ha⟩ :=
    s.constrained_binary_extensions hG hempty hM hJ hu h hf (by omega) e
  exact ⟨t,ht,hML,hM',a,ha,d.constrained_binary_node_geometry hG hempty hM hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple hm t a⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]

/-- The actual original marker supplies node control without changing the
component, prime, seed, quotient map, generating pair or endpoint extension. -/
theorem PreparedChosenModule.source_preExclusion_constrained_binary_nodes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (marker : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = marker.Z1 ∧ d.row = marker.row ∧
      d.PreExclusionSource h.normalized marker.prime ∧
      (generalizedFitting d.L = pCore 2 d.L →
        ∀ m : ℕ, m=3 ∨ m=4 →
        ∀ e : d.normalizerImage d.L ≃* SL(m+1,ZMod 2),
        ∃ t : (d.L ⧸ pCore 2 d.L) ≃* SL(m+1,ZMod 2),
          (∀ x : d.L, t (QuotientGroup.mk' (pCore 2 d.L) x) = e (d.toNormalizerImage d.L x)) ∧
          d.ConstrainedLinearParabolic t d.ML ∧
          d.ConstrainedLinearParabolic t (M ⊓ d.L) ∧
          ∃ a : d.BinaryGeneratingParabolics t,
            d.BinaryEndpointExtension a.endpoint ∧ Nonempty (d.BinaryNodeGeometry a)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull marker hres
  exact ⟨d,hZ,hr,s,fun hf _ hm e =>
    s.constrained_binary_nodes (h := h) hG hempty hM hJ hu hf hm e⟩
end CFSG.Quasithin.Chapter15.Section01
