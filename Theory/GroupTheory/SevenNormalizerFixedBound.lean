module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Tactic.NormNum.Prime

public import Theory.GroupTheory.PrimeNormalizerFixedBound

/-!
# Fixed points of order-seven subgroup normalizers

For a finite group of order eight, a nonidentity automorphism normalizing
an order-seven automorphism subgroup fixes at most two elements. This
compatibility theorem retains the involution hypothesis of its original
API. The imported prime-subgroup theorem proves the stronger result
without using that hypothesis: a seven-cycle moves all nonidentity
points, so fixing two of them would force the normalizing automorphism
to be the identity.

This supplies the upper fixed-subgroup bound in the elementary-core
normalizer calculation in Stellmacher Section 11; see
`refs/latex/stellmacher-n-group.tex`.
-/

universe u

public theorem card_fixed_le_two_of_normalizes_seven
    (E : Type u) [Group E] [Finite E] (hE : Nat.card E = 8)
    (K : Subgroup (MulAut E)) (hK : Nat.card K = 7)
    (automorphism : MulAut E)
    (hnormalizer : automorphism ∈ Subgroup.normalizer (K : Set (MulAut E)))
    (hsquare : automorphism ^ 2 = 1) (hne : automorphism ≠ 1) :
    Nat.card (automorphism.toMonoidHom.eqLocus (MonoidHom.id E)) ≤ 2 := by
  have _ := hsquare
  exact card_fixed_le_two_of_normalizes_prime 7 (by norm_num) E hE K hK
    automorphism hnormalizer hne
