module
public import Theory.GroupTheory.Signalizer.LocalClosure
public import Theory.GroupTheory.Signalizer.QPrime

/-!
# The local completeness condition used in the binary induction

A signalizer family is locally complete when the generated subgroup inside
the normalizer of every nontrivial signalizer subgroup is itself a signalizer
subgroup, and each q-prime subfamily is complete whenever q divides a family
value. The first condition uses the actual ambient `closureWithin`; it is
equivalent to completeness of the restricted family by the restriction API.

This is an auxiliary proposition, separate from the original family's local
hypotheses. The eventual induction proves it, and the local-to-global argument
uses it. The fixed-subgroup equality records its immediate consequence for a
normalizer closure while preserving the supplied action and its restrictions.

Source: Kurzweil–Stellmacher, *The Theory of Finite Groups*, Section 11.2,
printed pp.311–312. The condition on q is exactly membership in the family
prime spectrum, expressed by divisibility of one actual value order.
-/

namespace Theory.GroupTheory.TwoSignalizerFamily

variable {A G : Type*} [Group A] [Finite A] [Group G] [Finite G]
  [IsElementaryAbelian 2 A] [MulDistribMulAction A G]

public structure IsLocallyComplete (θ : TwoSignalizerFamily A G) : Prop where
  normalizer : ∀ U : Subgroup G, θ.IsSignalizerSubgroup U → U ≠ ⊥ →
    θ.IsSignalizerSubgroup (θ.closureWithin (Subgroup.normalizer (U : Set G)))
  qPrime : ∀ (q : ℕ) [Fact q.Prime], (∃ a, q ∣ Nat.card (θ.subgroup a)) →
    (θ.qPrime q).IsComplete

public theorem IsLocallyComplete.normalizer_fixed_eq
    {θ : TwoSignalizerFamily A G} (hθ : θ.IsLocallyComplete)
    {U : Subgroup G} (hU : θ.IsSignalizerSubgroup U) (hUn : U ≠ ⊥)
    (a : {a : A // a ≠ 1}) :
    θ.closureWithin (Subgroup.normalizer (U : Set G)) ⊓
      FixedPoints.subgroup (Subgroup.zpowers a.val) G =
        θ.subgroup a ⊓ Subgroup.normalizer (U : Set G) := by
  let := hU.2.2.1
  let := isInvariant_normalizer (A := A) U
  exact θ.closureWithin_fixed_eq _
    ((θ.isSignalizerSubgroup_closureWithin_iff _).mp (hθ.normalizer U hU hUn)) a

end Theory.GroupTheory.TwoSignalizerFamily
