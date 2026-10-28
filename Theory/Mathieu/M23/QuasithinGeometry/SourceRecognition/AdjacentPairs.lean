module
public import Theory.Mathieu.M23.QuasithinGeometry.StandardSystem
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.ConcreteLocal
public import Theory.GroupTheory.Recognition.QuasithinM23.CubicQuotient
public import Theory.GroupTheory.Recognition.QuasithinM23.AdjacentPairs

/-!
# Adjacent pair stabilizers in the native heptad

The pointwise fixer of the two adjacent pair vertices is the preimage of the
corresponding A₇ intersection, so its order is 16·12. Edge reversal preserves
the supporting triple; the native four-pair stabilizer escapes both source
parabolic overgroups.
Source: Aschbacher--Smith 5.2.20, printed p.656.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry

private theorem heptad_edge_preimage :
    (pairStabilizer ⊓ MulAction.stabilizer Sporadic.Mathieu.M23 y.val).subgroupOf heptadStabilizer =
    (MulAction.stabilizer (alternatingGroup (Fin 7)) ({5,6} : Finset (Fin 7)) ⊓
      MulAction.stabilizer (alternatingGroup (Fin 7)) ({4,5} : Finset (Fin 7))).comap
        heptadAlternatingAction := by
  ext g
  have hx : ({5,6} : Finset (Fin 7)).image label = x.val := by decide +kernel
  have hy : ({4,5} : Finset (Fin 7)).image label = y.val := by decide +kernel
  have hhx := heptadAction_stabilizes_labels g ({5,6} : Finset (Fin 7))
  have hhy := heptadAction_stabilizes_labels g ({4,5} : Finset (Fin 7))
  rw [hx] at hhx
  rw [hy] at hhy
  change ((g : Sporadic.Mathieu.M23) • x.val = x.val ∧
    (g : Sporadic.Mathieu.M23) • y.val = y.val) ↔ _
  exact and_congr hhx.symm hhy.symm

/-- The edge fixer inside the heptad local has order 16 · 12. -/
theorem heptad_adjacent_pair_fixer_card :
    Nat.card ((pairStabilizer ⊓ MulAction.stabilizer Sporadic.Mathieu.M23 y.val).subgroupOf
      heptadStabilizer) = 192 := by
  rw [heptad_edge_preimage]
  let P := MulAction.stabilizer (alternatingGroup (Fin 7)) ({5,6} : Finset (Fin 7)) ⊓
    MulAction.stabilizer (alternatingGroup (Fin 7)) ({4,5} : Finset (Fin 7))
  have hq : Function.Surjective heptadAlternatingAction := fun a =>
    ⟨AlternatingSection.s a,heptadAlternatingAction_section a⟩
  have hker : heptadAlternatingAction.ker = heptadKernel := by
    ext g
    exact Subtype.ext_iff
  have hle : heptadAlternatingAction.ker ≤ P.comap heptadAlternatingAction :=
    ker_le_comap _ _
  have hc := IsElementaryAbelian.card_inf_ker_mul_card_map (P.comap heptadAlternatingAction)
    heptadAlternatingAction
  rw [inf_eq_right.mpr hle,hker,heptadKernel_card,map_comap_eq_self_of_surjective hq,
    QuasithinM23.seven_adjacent_pair_stabilizer_card] at hc
  exact hc.symm

/-- Reversing the standard edge preserves its union, the marked triple. -/
theorem heptad_edge_swap_stabilizes_triple (t : heptadStabilizer)
    (htx : (t : Sporadic.Mathieu.M23) • x = y)
    (hty : (t : Sporadic.Mathieu.M23) • y = x) :
    heptadAction t • ({4,5,6} : Set (Fin 7)) = {4,5,6} := by
  have hxy : ({4,5,6} : Finset (Fin 7)).image label = x.val ∪ y.val := by decide +kernel
  have htx' := congrArg Subtype.val htx
  have hty' := congrArg Subtype.val hty
  change (t : Sporadic.Mathieu.M23) • x.val = y.val at htx'
  change (t : Sporadic.Mathieu.M23) • y.val = x.val at hty'
  have hh : heptadAction t • ({4,5,6} : Finset (Fin 7)) = {4,5,6} := by
    apply (heptadAction_stabilizes_labels t _).mpr
    rw [hxy,Finset.smul_finset_union,htx',hty',Finset.union_comm]
  have hh' := congrArg (fun s : Finset (Fin 7) => (s : Set (Fin 7))) hh
  simpa only [Finset.coe_smul_finset,Finset.coe_insert,Finset.coe_singleton] using hh'

/-- The vertex intersection escapes both the pointwise-pair and triple subgroups. -/
theorem fourPair_not_le_marked_overgroups :
    ¬ fourPairStabilizer.subgroupOf heptadStabilizer ≤
      (fixingSubgroup (Equiv.Perm (Fin 7)) ({5,6} : Set (Fin 7))).comap heptadAction ∧
    ¬ fourPairStabilizer.subgroupOf heptadStabilizer ≤
      (MulAction.stabilizer (Equiv.Perm (Fin 7)) ({4,5,6} : Set (Fin 7))).comap heptadAction := by
  let a : alternatingGroup (Fin 7) := ⟨Equiv.swap 0 1 * Equiv.swap 5 6, by
    change Equiv.Perm.sign _ = 1; decide⟩
  let b : alternatingGroup (Fin 7) := ⟨Equiv.swap 0 1 * Equiv.swap 3 4, by
    change Equiv.Perm.sign _ = 1; decide⟩
  have ha : AlternatingSection.s a ∈ fourPairStabilizer.subgroupOf heptadStabilizer := by
    apply (mem_fourPairStabilizer_iff_labelled _).mpr
    rw [AlternatingSection.heptadAction_s,mem_heptadPartitionStabilizer]
    decide +kernel
  have hb : AlternatingSection.s b ∈ fourPairStabilizer.subgroupOf heptadStabilizer := by
    apply (mem_fourPairStabilizer_iff_labelled _).mpr
    rw [AlternatingSection.heptadAction_s,mem_heptadPartitionStabilizer]
    decide +kernel
  constructor
  · intro hh
    have ht := hh ha
    change heptadAction (AlternatingSection.s a) ∈ fixingSubgroup _ _ at ht
    rw [AlternatingSection.heptadAction_s] at ht
    have ht5 := ht ⟨5,by simp⟩
    change (6 : Fin 7) = 5 at ht5
    exact (by decide : (6 : Fin 7) ≠ 5) ht5
  · intro hh
    have ht := hh hb
    change heptadAction (AlternatingSection.s b) • ({4,5,6} : Set (Fin 7)) = {4,5,6} at ht
    rw [AlternatingSection.heptadAction_s] at ht
    have hin : (3 : Fin 7) ∈ (b : Equiv.Perm (Fin 7)) • ({4,5,6} : Set (Fin 7)) :=
      ⟨4,by simp,by decide⟩
    rw [ht] at hin
    norm_num [Fin.ext_iff] at hin

end Sporadic.Mathieu.M23Geometry
