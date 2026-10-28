module

public import Stellmacher.Recognition.OddCoreBinaryFusion
public import Stellmacher.Recognition.OddCoreStrongEmbedding

/-!
# Vanishing of rank-three involution odd-core closures

In a finite nonsolvable simple N₂ group, the involution odd-core closure
of an elementary abelian two-subgroup of order at least eight is trivial.
If the closure were nontrivial, completion and binary normalizer control
would make its normalizer strongly embedded. The Bender–Suzuki elimination
for the odd completed closure excludes this possibility.

Source: the binary signalizer and uniqueness argument in GLS2, §§21–22,
assembled from `OddCoreBinaryFusion` and `OddCoreStrongEmbedding`.
-/

namespace Stellmacher.Recognition

/-- The involution odd-core closure of a rank-at-least-three elementary
abelian two-subgroup in a finite nonsolvable simple N₂ group is trivial. -/
public theorem involutionOddCoreClosure_eq_bot_of_rankThree
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A) :
    involutionOddCoreClosure A = ⊥ := by
  by_contra hR
  exact not_isStronglyEmbedded_normalizer_involutionOddCoreClosure hN A hA
    (isStronglyEmbedded_normalizer_involutionOddCoreClosure hns hN A hA hR)

end Stellmacher.Recognition
