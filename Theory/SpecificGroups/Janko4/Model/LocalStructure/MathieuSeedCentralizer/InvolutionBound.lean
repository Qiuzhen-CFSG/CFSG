module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.InvolutionBound.Reduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.InvolutionBound.FiberBounds
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarBridge
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCounts

/-!
# Seed-type involutions in the local seed centralizer

Inside the literal max1 subgroup, every seed-type centralizer element lies in
the binary kernel or over one of the two quotient involution classes. The
kernel contributes at most 2048; the two full colored fibers contribute at
most 32 and 128 respectively. Actual centralization forces the quotient's
star permutation to fix the seed pair. The certified bounds of 1600 for each
marked star-group class give at most 258048 elements, hence the bound 262144.

The only additional hypothesis is ambient nonconjugacy of the first involution
representative and the seed. The count is inside the actual max1 centralizer;
identifying it with the full ambient centralizer is a separate obligation of
the ambient order argument. Source motivation: Aschbacher--Smith,
`refs/quasithin.pdf`, A.6.1--4, printed pp.64--65. This bounds a superset of
the local version of `B₁(t)` defined there.
-/

public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound
open Cardinality
variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)

/-- Complete the local count once both marked permutation-class bounds have
been certified. The only ambient premise is separation of the two classes. -/
theorem seedType_card_le_of_star_counts
    (hn : ¬ IsConj (Simplicity.a hA) (localKernelSeed hA hB : Model))
    (hx : Nat.card (StarClass false) ≤ 1600)
    (hq : Nat.card (StarClass true) ≤ 1600) :
    Nat.card (SeedType hA hB) ≤ 262144 := by
  exact seedType_card_le_of_counts hA hB
    ((quotientClass_card_le_starClass hA hB false).trans hx)
    ((quotientClass_card_le_starClass hA hB true).trans hq)
    (baseFiber_false_card_le hA hB hn) (baseFiber_true_card_le hA hB)

/-- At most `2^18` elements of the actual local seed centralizer are
ambient-conjugate to the seed. The seed has order two by `seed_order`;
the only additional premise separates the two ambient involution classes. -/
theorem seedType_card_le
    (hn : ¬ IsConj (Simplicity.a hA) (localKernelSeed hA hB : Model)) :
    Nat.card (SeedType hA hB) ≤ 262144 := by
  exact seedType_card_le_of_star_counts hA hB hn
    starClass_false_card_le starClass_true_card_le

end Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound
