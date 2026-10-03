module

public import GorensteinWalter.PGL2CanonicalOuterInvolutionFusion

/-!
# Fusion of outer involutions in the derived-subgroup formulation

Over an odd finite field of order greater than three, involutions outside
the commutator subgroup of PGL2 are conjugate. The commutator is the
canonical PSL2 image under this field-size assumption, so the all-field
canonical-image theorem applies directly. This preserves the historical
public theorem and its exact hypotheses for existing consumers.

The complete Sylow/dihedral fusion argument now lives in
PGL2CanonicalOuterInvolutionFusion, where it also applies to field order
three. Source: the outer-involution alignment in ABG II.3 Proposition3,
article p27 (PDF page28).
-/

namespace GorensteinWalter

open Matrix
open scoped MatrixGroups Pointwise

universe u

/-- For an odd finite field of order greater than three, all involutions of
PGL2(K) outside its derived PSL2(K) subgroup are conjugate. -/
public theorem pgl2_outer_involutions_conjugate
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    {a b : PGL2 K} (ha : IsInvolution a) (hb : IsInvolution b)
    (haJ : a ∉ commutator (PGL2 K))
    (hbJ : b ∉ commutator (PGL2 K)) :
    IsConj a b := by
  apply pgl2_outer_involutions_conjugate_of_odd_prime_power K hK ha hb
  · rwa [← pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard]
  · rwa [← pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard]

end GorensteinWalter
