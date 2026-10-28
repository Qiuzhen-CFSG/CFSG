module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.C2RankThree.Commutators
public import Mathlib.GroupTheory.IndexNormal

/-!
# The original binary radical and kernel

When a simple root has order two, its canonical remainder has index two
in U and is therefore normal. Thus the exact C₂ row commutation supplies
the neighboring-orbit kernel bound without a radical-normality hypothesis.
This is the q=2 specialization of Fong–Seitz I (3G), (6A)(a) and II (7C).
It retains the whole quotient and requires no perfectness.
-/

public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.C2RankThree
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

theorem binary_remainder_normalizes (i : Fin 2)
    (hq : Nat.card (simpleRoot Q split i) = 2) :
    split.U ≤ normalizer (simpleRemainder Q split i : Set (X ⧸ Q.D)) := by
  apply (normal_subgroupOf_iff_le_normalizer (show simpleRemainder Q split i ≤ split.U from
    inf_le_left)).mp
  apply normal_of_index_eq_two
  rw [simpleRemainder_index, hq]

theorem binary_kernel_lower_bound (hm : rotationOrder Q = 4)
    (hq : ∀ i, Nat.card (simpleRoot Q split i) = 2)
    (hrow : ⁅simpleRoot Q split 1,kernelRoot Q split⁆ = ⊥) :
    2 ≤ Nat.card (fixingSubgroup (X ⧸ Q.D) (insert (rightCosetPoint Q 1 1)
      (MulAction.orbit (MulAction.stabilizer (X ⧸ Q.D) (rightCosetPoint Q 1 1)) (neighborPoint Q)))) :=
  source_kernel_lower_bound Q split hm (hq 1)
    (fun i => binary_remainder_normalizes Q split i (hq i)) hrow
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.C2RankThree
