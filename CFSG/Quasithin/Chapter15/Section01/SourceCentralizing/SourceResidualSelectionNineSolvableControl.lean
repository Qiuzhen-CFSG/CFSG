module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineMarkedControl
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNine
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SolvableControl

/-!
# Solvable control from the marked residual normalizer

The original 15.1.19(2) argument uses the global residual conclusion only
to place the normalizer of O²(M_Z) in the partner. Keeping that exact local
bound gives the same control of every M_Z-invariant characteristic-two
subgroup with odd quotient over its two-core.

The actual Nine source obtains the bound from its maximal-overgroup pair
and the marked normalization already present in its component source.
No global residual centralization or classification of K is assumed.

Source: Aschbacher--Smith 15.1.19(2), printed p.1093;
C.2.5--6, printed pp.144--145.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Original 15.1.19(2), in the exact fixed centralizer and marked subgroup.
The odd quotient is the literal condition K=O₂,₂′(K). -/
theorem constrained_solvable_control_of_local_residual (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hSyl : Chapter1.IsSylowIn 2 d.S d.G1)
    (hcontrol : d.Q1.characteristicNormalizerClosure ≤ Mc)
    (hbound : normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc)
    {K : Subgroup G} (hK : K ≤ d.G1)
    (hn : d.MZ ≤ normalizer (K : Set G))
    (hf : generalizedFitting K = pCore 2 K)
    (ho : Odd (Nat.card (K ⧸ pCore 2 K))) : K ≤ d.MZ := by
  let := h.elementary
  let H := d.G1
  let N := d.MZ.subgroupOf H
  let B := K.subgroupOf H
  let e : B ≃* K := subgroupOfEquivOfLe hK
  obtain ⟨P,hP⟩ := hSyl
  have hSM : (P : Subgroup H) ≤ N := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    intro x hx
    have hs : (x : G) ∈ d.S := hP ▸ mem_map_of_mem H.subtype hx
    exact ⟨x.property,hMc.2 (fun z hz =>
      (centralInvolutions_le_centralizer_sylow T hz x (d.S_le_T hs)).symm)⟩
  have hnB : N ≤ normalizer (B : Set H) := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro b
    exact mem_normalizer_iff.mp (hn hx) b
  have hfB : generalizedFitting B = pCore 2 B := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_generalizedFitting_equiv,pCore_map_iso,hf]
  have hoB : Odd (Nat.card (B ⧸ pCore 2 B)) := by
    rwa [Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv]
  have hc : (N.pCoreIn 2).characteristicNormalizerClosure ≤ N := by
    rw [show N = d.MZ.subgroupOf H from rfl,pCoreIn_subgroupOf 2 d.MZ H inf_le_left]
    exact caseI_intrinsic_characteristic_control H Mc d.Q1
      (d.Q1_le_MZ.trans inf_le_left) hcontrol
  have hY : ((pResidual 2 N).map N.subtype).map H.subtype =
      (pResidual 2 d.MZ).map d.MZ.subtype := by
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le (show d.MZ ≤ H from inf_le_left)]
  have hr : normalizer ((pResidual 2 N).map N.subtype : Set H) ≤ N := by
    intro x hx
    refine ⟨x.property,hbound ?_⟩
    have hm := le_normalizer_map H.subtype (mem_map_of_mem H.subtype hx)
    rwa [hY] at hm
  have hle := ConstrainedSolvable.controlled_of_odd_quotient
    (caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
      ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left)))
    P N B hSM hnB hfB hoB hc hr
  intro k hk
  exact hle (show (⟨k,hK hk⟩ : H) ∈ B from hk)

/-- The original marker supplies all source data except the literal local
residual-normalizer bound. -/
theorem PreExclusionSource.constrained_solvable_control_of_local_residual
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hbound : normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc)
    {K : Subgroup G} (hK : K ≤ d.G1)
    (hn : d.MZ ≤ normalizer (K : Set G))
    (hf : generalizedFitting K = pCore 2 K)
    (ho : Odd (Nat.card (K ⧸ pCore 2 K))) : K ≤ d.MZ :=
  d.constrained_solvable_control_of_local_residual hG hu h s.centralizer_sylow
    s.characteristic_control hbound hK hn hf ho

/-- The exchanged-source application uses the same marked residual bound. -/
theorem ExchangedSource.constrained_solvable_control_of_local_residual
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (h : PreparedChosenModule T M V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hbound : normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc)
    {K : Subgroup G} (hK : K ≤ d.G1)
    (hn : d.MZ ≤ normalizer (K : Set G))
    (hf : generalizedFitting K = pCore 2 K)
    (ho : Odd (Nat.card (K ⧸ pCore 2 K))) : K ≤ d.MZ :=
  d.constrained_solvable_control_of_local_residual hG hu h s.centralizer_sylow
    s.characteristic_control hbound hK hn hf ho

/-- In the actual Nine row the original pair supplies the residual-normalizer
bound from the component source's marked normalization. -/
theorem PreExclusionSource.nine_constrained_solvable_control
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    {K : Subgroup G} (hK : K ≤ d.G1)
    (hn : d.MZ ≤ normalizer (K : Set G))
    (hf : generalizedFitting K = pCore 2 K)
    (ho : Odd (Nat.card (K ⧸ pCore 2 K))) : K ≤ d.MZ := by
  have hpair := h.nine_maximal_overgroups hG T hempty hM hJ hu h9
  have hbound := h.marked_residual_normalizer_control_of_pair hG T hempty hM hmany hJ hu
    hpair d.Z1_le_fixed d.Z1_ne_bot s.sylow_normalizes_MZ s.centralizer_sylow
  exact s.constrained_solvable_control_of_local_residual (h := h) hG hu hbound hK hn hf ho

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
