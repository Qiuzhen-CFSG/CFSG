module
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Representatives
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Second
public import Theory.GroupTheory.SylowPrimeOrderCoverage
public import Mathlib.GroupTheory.GroupAction.Quotient
/-!
# A marked Rudvalis cubic and its involution incidence

A short word in the actual sixth ATLAS local subgroup has order three. Its
fixed set has ten points, and precisely two of those points are fixed by the
marked central involution. Evaluation uses the already certified local generator
tables, preserving the original words while avoiding repeated word expansion.
These two counts feed the elementary-sixteen obstruction by Burnside's lemma.

Source: the native degree-4060 ATLAS action and max6 words preserved in
SylowOvergroups.Definitions; used in Aschbacher--Smith 2.4.25, printed p.543.
-/

public section
open Subgroup
namespace Rudvalis.CubicElementary
open SylowOvergroups InvolutionCentralizers
open SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate
set_option maxRecDepth 12000
open LocalCardinality.Max6

@[expose] def cubic : Model := (max6Generators.1 ^ 2 * max6Generators.2)^2

theorem cubic_val : cubic.val = ((L0.gen 0)^2 * L0.gen 1)^2 := by
  rw [generator0_eq, generator1_eq]
  rfl

theorem cubic_mem : cubic ∈ max6 :=
  max6.pow_mem (max6.mul_mem
    (max6.pow_mem (subset_closure (Set.mem_insert _ _)) 2)
    (subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))) 2

theorem cubic_cube : cubic ^ 3 = 1 := by
  apply Subtype.ext
  change cubic.val^3 = (1 : Equiv.Perm (Fin 4060))
  rw [cubic_val]
  apply Equiv.ext
  apply Data.allFin
  decide +kernel

theorem cubic_order : orderOf cubic = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply orderOf_eq_prime_iff.mpr
  refine ⟨cubic_cube,?_⟩
  intro h
  have hh := congrArg (fun t : Model => t • (0 : Fin 4060)) h
  have hn : cubic • (0 : Fin 4060) ≠ 0 := by
    change cubic.val 0 ≠ 0
    rw [cubic_val]
    decide +kernel
  exact hn hh

private def cubicFixed : Finset (Fin 4060) :=
  {1043,1139,1188,2290,2356,2448,2535,2596,3724,3968}
private def pairFixed : Finset (Fin 4060) := {1139,2535}

private theorem cubic_fixed_check : ∀ i : Fin 4060,
    i ∈ cubicFixed ↔ cubic • i = i := by
  change ∀ i : Fin 4060, i ∈ cubicFixed ↔ cubic.val i = i
  rw [cubic_val]
  apply Data.allFin
  decide +kernel

private theorem pair_fixed_check : ∀ i : Fin 4060,
    i ∈ pairFixed ↔ cubic • i = i ∧ centralInvolution • i = i := by
  change ∀ i : Fin 4060, i ∈ pairFixed ↔ cubic.val i = i ∧ centralInvolution.val i = i
  rw [cubic_val, centralInvolution_val]
  apply Data.allFin
  decide +kernel

theorem cubic_fixed_card : Nat.card {i : Fin 4060 // cubic • i = i} = 10 := by
  rw [Nat.subtype_card cubicFixed cubic_fixed_check]
  decide +kernel

theorem pair_fixed_card : Nat.card {i : Fin 4060 //
    cubic • i = i ∧ centralInvolution • i = i} = 2 := by
  rw [Nat.subtype_card pairFixed pair_fixed_check]
  decide +kernel
end Rudvalis.CubicElementary
