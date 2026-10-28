module

public import Stellmacher.Recognition.OddCoreBinaryFusionReduction
public import Stellmacher.Recognition.OddCoreSmallRank

/-!
# Strong embedding of a nontrivial completed odd-core normalizer

In a finite nonsolvable simple N₂ group, the normalizer of the nontrivial
involution odd-core closure of an elementary subgroup of order at least eight
is strongly embedded.

Choose a Sylow two-subgroup containing the elementary subgroup. Completion
and simplicity make the closure normalizer proper, and Sylow control places
the chosen Sylow subgroup inside it. The binary normalizer criterion reduces
failure of strong embedding to an escaping normalizer of a nontrivial
two-subgroup of elementary rank at most two. The small-rank uniqueness
theorem controls every such normalizer, completing the argument.

Source: GLS2, Section 22, the binary-case remark following Proposition 22.4;
the N₂ uniqueness argument is supplied by `OddCoreSmallRank`. No global
connectivity, K-properness or odd-core vanishing hypothesis is assumed.
-/

namespace Stellmacher.Recognition

/-- A nontrivial completed odd-core closure attached to an elementary binary
subgroup of rank at least three has a strongly embedded normalizer. -/
public theorem isStronglyEmbedded_normalizer_involutionOddCoreClosure
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hR : involutionOddCoreClosure A ≠ ⊥) :
    IsStronglyEmbedded
      (Subgroup.normalizer (involutionOddCoreClosure A : Set G)) := by
  obtain ⟨S, hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  apply isStronglyEmbedded_normalizer_oddCoreClosure_of_smallRank_control
    hns hN S A hAS hA hR
  intro Q hQ _hQp hQS _hsmall
  exact normalizer_le_oddCore_normalizer_of_nontrivial hns hN S A Q hA hAS hQS hQ

end Stellmacher.Recognition
