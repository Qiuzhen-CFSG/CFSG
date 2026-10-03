module

public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.SevenNormalizerFixedBound
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Tactic.Linarith

public import Theory.GroupTheory.ElementaryPrimeNormalizer

/-!
# Odd normalizers of order-seven automorphism subgroups

An order-seven subgroup of the automorphism group of a finite elementary
abelian two-group of order eight has an odd-order ambient normalizer.
This compatibility theorem specializes the general prime-subgroup result.
The shared proof bounds an involution's group order by the square of its
fixed-subgroup order, while the prime-cycle argument permits at most two
fixed elements for a nonidentity normalizing automorphism.

This supplies the normalizer input to the order-eight automorphism-subgroup
bound, independently of the full automorphism count. The source is the
elementary-core calculation in Stellmacher Section 11,
`refs/latex/stellmacher-n-group.tex`. The original public interface is retained.
-/

open scoped IsMulCommutative

universe u

/-- Seven-subgroup normalizers in order-eight elementary automorphism groups have odd order. -/
public theorem odd_card_normalizer_of_elementary_eight_seven
    (E : Type u) [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (K : Subgroup (MulAut E)) (hK : Nat.card K = 7) :
    Odd (Nat.card (Subgroup.normalizer (K : Set (MulAut E)))) := by
  exact odd_card_normalizer_of_elementary_prime 7 (by decide) (by decide) E hE K hK
