module

public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.Coverage.Intransitive
public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.Coverage.Transitive

/-!
# Geometric coverage of solvable-normal Sylow overgroups in M₂₂

An overgroup X of an ambient Sylow two-subgroup, with a solvable normal
subgroup whose order is divisible by three, preserves a hexad or a pair
in the actual degree-22 action. The normal solvable subgroup rules out
transitivity; the hexad translation kernel then supplies the small invariant
set that determines one of the two configurations.

This is the geometric placement used in Aschbacher–Smith 13.8.21(2),
printed p.956 (PDF p.973). Orders and conjugacy types inside the two stabilizers
are separate local-classification results. No subgroup-table coverage,
completed classification theorem, or geometric placement is assumed here.
-/

public section

open Subgroup MulAction
open scoped Pointwise
namespace Sporadic.Mathieu.M22SolvableSylow

/-- Native solvable-normal Sylow overgroups preserve a hexad or a pair. -/
theorem geometric_coverage (X D : Subgroup M22) (hle : D ≤ X)
    (hn : (D.subgroupOf X).Normal) (hs : Group.IsSolvable D) (hthree : 3 ∣ Nat.card D)
    (hU : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X) :
    (∃ B ∈ m22Blocks, X ≤ stabilizer M22 B) ∨
      (∃ S : Finset (Fin 22), S.card = 2 ∧ X ≤ stabilizer M22 S) :=
  coverage_of_not_pretransitive X hU
    (not_pretransitive_of_solvable_normal_three X D hle hn hs hthree hU)

end Sporadic.Mathieu.M22SolvableSylow
