module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.LocalTransfer

/-!
# Choosing the local group before its section action

Choose a group of least order in the actual outside family below an eligible
overgroup. Every eligible subgroup of this choice is equal to it. The
nontrivial two-core, carried by the fixed Sylow subgroup, makes intermediate
outside overgroups eligible. Consequently one outside C-component suffices
both for the replacement equality and for solvable-overgroup control.

No component-generation or solvability assumption on `M ∩ H` is used.
The component still has to be constructed from B.5.6. This is the finite
minimal-choice variant of Aschbacher–Smith, proof of 15.3.49(i)–(j),
combined manuscript (1 March 2004), printed pp.1143–1144.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute

open Subgroup ComponentReduction

variable {G : Type*} [Group G]

/-- Minimality is restricted to the genuine eligible groups below `upper`. -/
structure MinimalLocal (Y0 T M upper H : Subgroup G) : Prop where
  eligible : H ∈ outsideFamily Y0 T M
  le_upper : H ≤ upper
  card_minimal : ∀ K : Subgroup G, K ∈ outsideFamily Y0 T M → K ≤ upper →
    Nat.card H ≤ Nat.card K

/-- The initial eligible overgroup witnesses nonemptiness before actions or
offenders are selected. -/
theorem exists_minimalLocal [Finite G] (Y0 T M upper : Subgroup G)
    (hupper : upper ∈ outsideFamily Y0 T M) :
    ∃ H : Subgroup G, MinimalLocal Y0 T M upper H := by
  classical
  let S : Set (Subgroup G) := {K | K ∈ outsideFamily Y0 T M ∧ K ≤ upper}
  obtain ⟨H, hH, hmin⟩ := Set.exists_min_image S (fun K => Nat.card K)
    (Set.toFinite S) ⟨upper, hupper, le_rfl⟩
  exact ⟨H, hH.1, hH.2, fun K hK hKU => hmin K ⟨hK, hKU⟩⟩

namespace MinimalLocal

variable {Y0 T M upper H : Subgroup G} (d : MinimalLocal Y0 T M upper H)

include d

theorem twoCore_ne_bot : localTwoCore H ≠ ⊥ := d.eligible.1.1

theorem base_le : Y0 ⊔ T ≤ H := d.eligible.1.2

theorem outside : ¬ H ≤ M := d.eligible.2

/-- Ordinary cardinal minimality implies equality, not a change of action. -/
theorem eq_of_eligible [Finite G] {K : Subgroup G} (hK : K ∈ outsideFamily Y0 T M)
    (hKH : K ≤ H) : K = H :=
  eq_of_le_of_card_ge hKH (d.card_minimal K hK (hKH.trans d.le_upper))

/-- The normal two-core survives in any intermediate group containing it. -/
theorem intermediate_eligible (hQT : localTwoCore H ≤ T)
    {K : Subgroup G} (hbase : Y0 ⊔ T ≤ K) (hKH : K ≤ H) (hout : ¬ K ≤ M) :
    K ∈ outsideFamily Y0 T M := by
  have hQK : H.pCoreIn 2 ≤ K := hQT.trans (le_sup_right.trans hbase)
  have hcores : H.pCoreIn 2 ≤ K.pCoreIn 2 := by
    simpa only [inf_eq_right.mpr hQK] using inf_pCoreIn_le_of_le 2 hKH
  refine ⟨⟨?_, hbase⟩, hout⟩
  intro hb
  exact d.twoCore_ne_bot (le_bot_iff.mp (hcores.trans_eq hb))

/-- An ambient Sylow subgroup containing the local two-core gives the
containment needed in `intermediate_eligible`. -/
theorem twoCore_le_sylow (S : Sylow 2 G) (hS : (S : Subgroup G) = T) :
    localTwoCore H ≤ T := by
  have hSH : (S : Subgroup G) ≤ H := hS ▸ le_sup_right.trans d.base_le
  have h := pCoreIn_le_sylow H (S.subtype hSH)
  rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hSH, hS] at h
  exact h

/-- One outside component forces the source replacement to be the group
already selected, so its section action and endpoints can be retained. -/
theorem reducedOvergroup_eq [Finite G] (hQT : localTwoCore H ≤ T)
    {L : Subgroup G} (hLH : L ≤ H) (hLM : ¬ L ≤ M) :
    reducedOvergroup L Y0 T = H := by
  have hKH := reducedOvergroup_le hLH (le_sup_left.trans d.base_le)
    (le_sup_right.trans d.base_le)
  exact d.eq_of_eligible
    (d.intermediate_eligible hQT le_sup_right hKH (reducedOvergroup_outside hLM)) hKH

omit d in
/-- The selected group is nonsolvable as soon as it has a C-component. -/
theorem not_solvable_of_component {L : Subgroup G}
    (hL : (L.subgroupOf H).IsCComponent) : ¬ Group.IsSolvable H := by
  intro hs
  let := hs
  exact hL.not_isSolvable inferInstance

/-- Source clause (j) from minimality and nonsolvability. Eligibility is
proved through the actual nontrivial normal two-core. -/
theorem solvable_overgroup_le [Finite G] (hQT : localTwoCore H ≤ T)
    (hns : ¬ Group.IsSolvable H) (K : Subgroup G) (hsol : Group.IsSolvable K)
    (hbase : Y0 ⊔ T ≤ K) (hKH : K ≤ H) : K ≤ M ⊓ H := by
  refine le_inf ?_ hKH
  by_contra hout
  have he := d.eq_of_eligible (d.intermediate_eligible hQT hbase hKH hout) hKH
  exact hns (he ▸ hsol)

end MinimalLocal
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute
