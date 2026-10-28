module

public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.LocalClassification.NativeOrders
public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.LocalClassification.PairPlacement.PermutationFive

/-!
# Hexad placement of order-384 subgroups in M₂₂ pair stabilizers

An order-384 subgroup containing an ambient Sylow two-subgroup and stabilizing
a pair stabilizes a hexad in the actual degree-22 Witt design. At the marked
pair, the kernel of the five-hexad action lies in the subgroup, so its image
has order 24. A subgroup of S₅ of that order fixes a point; `pairAction_spec`
identifies this fixed point with an invariant hexad. Two-transitivity and
actual conjugation in M₂₂ transport the witness to any pair.

This proves the pair-to-hexad placement step used in the local subgroup
argument of Aschbacher–Smith 13.8.21(2), printed p.956 (PDF p.973), through
the genuine five-hexad action associated to E.4.3(2). The hypotheses are just
pair placement, order 384, and containment of an ambient Sylow two-subgroup.
-/

open Subgroup MulAction
open scoped Pointwise

namespace Sporadic.Mathieu.M22SolvableSylow.LocalClassification
open M22ValueBound.Concrete

/-- An order-384 Sylow overgroup in the marked pair stabilizer fixes an actual hexad. -/
public theorem standard_pair_hexad_of_order (X : Subgroup M22) (hX : X ≤ first)
    (hcard : Nat.card X = 384)
    (hU : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X) :
    ∃ B ∈ m22Blocks, X ≤ stabilizer M22 B := by
  have hc : Nat.card ((X.subgroupOf first).map pairAction) = 24 := by
    have hm := pair_card_formula X hX hU
    omega
  obtain ⟨i, hi⟩ := s5_exists_fixed_point_of_card_eq_24 _ hc
  refine ⟨M22ValueBound.Concrete.pairHexad i, (pairHexad_mem i).1, ?_⟩
  intro g hg
  change (g : Equiv.Perm (Fin 22)) • M22ValueBound.Concrete.pairHexad i =
    M22ValueBound.Concrete.pairHexad i
  rw [← pairAction_spec ⟨g, hX hg⟩ i]
  exact congrArg M22ValueBound.Concrete.pairHexad (hi ⟨pairAction ⟨g, hX hg⟩,
    mem_map_of_mem pairAction (show (⟨g, hX hg⟩ : first) ∈ X.subgroupOf first from hg)⟩)

/-- An order-384 Sylow overgroup stabilizing any pair stabilizes an actual hexad. -/
public theorem pair_hexad_of_order {S : Finset (Fin 22)} (hS : S.card = 2)
    (X : Subgroup M22) (hX : X ≤ stabilizer M22 S)
    (hcard : Nat.card X = 384)
    (hU : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X) :
    ∃ B ∈ m22Blocks, X ≤ stabilizer M22 B := by
  obtain ⟨g, hg⟩ := exists_smul_pair_eq_standard hS
  let e := MulAut.conj g
  have hX' : X.map e.toMonoidHom ≤ first := by
    have hm := map_mono (f := e.toMonoidHom) hX
    rwa [← stabilizer_smul_eq_stabilizer_map_conj g S, hg] at hm
  have hc : Nat.card (X.map e.toMonoidHom) = 384 := by
    rwa [card_map_of_injective e.injective]
  have hU' : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X.map e.toMonoidHom := by
    obtain ⟨U, hU⟩ := hU
    exact ⟨U.mapSurjective e.surjective, map_mono hU⟩
  obtain ⟨B, hB, hXB⟩ := standard_pair_hexad_of_order _ hX' hc hU'
  refine ⟨g⁻¹ • B, m22_smul_block_mem g⁻¹ B hB, ?_⟩
  intro x hx
  change x • (g⁻¹ • B) = g⁻¹ • B
  have hh : (g * x * g⁻¹) • B = B := hXB (mem_map_of_mem e.toMonoidHom hx)
  have hh' := congrArg (fun C : Finset (Fin 22) => g⁻¹ • C) hh
  simpa only [mul_smul, inv_smul_smul] using hh'

end Sporadic.Mathieu.M22SolvableSylow.LocalClassification
