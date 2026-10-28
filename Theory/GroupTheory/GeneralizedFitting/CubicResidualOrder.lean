module
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
/-!
# The order bound for a core-free cubic residual extension

When O₂(G)=1 and O²(G) has order three, the residual is self-centralizing.
Its conjugation action has kernel of order at most three and image of order
at most two. Thus |G|≤6. The bound is used for the cyclic-residual branch
of Aschbacher–Smith E.2.17, where the original pair supplies an order-six
quotient and therefore generates modulo the ambient two-core.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
theorem card_le_six_of_core_free_cubic_residual
    (hc : pCore 2 G = ⊥) (hr : Nat.card (pResidual 2 G) = 3) : Nat.card G ≤ 6 := by
  let R := pResidual 2 G
  let : R.Normal := inferInstanceAs (pResidual 2 G).Normal
  let : IsCyclic R := isCyclic_of_prime_card hr
  let f : G →* MulAut R := MulAut.conjNormal
  have hk : f.ker ≤ R := by
    rw [MulAut.conjNormal_ker_eq_centralizer]
    exact centralizer_pResidual_le_of_pCore_eq_bot hc
  have hkc : Nat.card f.ker ≤ 3 := by
    have h := Nat.card_le_card_of_injective (inclusion hk) (inclusion_injective hk)
    exact h.trans_eq hr
  have hrc : Nat.card f.range ≤ 2 := by
    have h := Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective
    rw [IsCyclic.card_mulAut, hr] at h
    exact h
  have ht := f.ker.card_mul_index
  rw [index_ker] at ht
  nlinarith
end Theory.GroupTheory
