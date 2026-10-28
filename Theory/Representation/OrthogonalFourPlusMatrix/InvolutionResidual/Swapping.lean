module

public import Theory.Representation.OrthogonalFourPlusMatrix.InvolutionResidual.Defs
public import Theory.Representation.OrthogonalFourPlusMatrix.InvolutionResidual.Swapping.OrderFive
public import Theory.Representation.OrthogonalFourPlusMatrix.Displacement
public import Theory.GroupTheory.TwoThreeSolvable
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# The swapped moved module for the binary determinant action

The action is literally `M ↦ A M B⁻¹` on Mat₂(F₄). Every nonsolvable
subgroup of SL₂(4) × SL₂(4) contains an element of order five: otherwise
its order has only the prime divisors two and three, so it is solvable.
Every nonidentity matrix actor moves at least four binary dimensions.
The order-five calculation therefore makes the moved space of any commuting
involution of moved rank greater than two irreducible of dimension four.

This direct proof also covers the semilinear swapping involutions and their
conjugates, without a classification of normalizer elements or an assumed
identification with a permutation module. Normalization and factor interchange
are retained in the source-facing wrapper, but the stronger theorem does not
need them. The strict rank hypothesis is essential: plain adjugation swaps
factors and has moved rank two.

Source: Aschbacher–Smith, Lemma 14.4.9, combined manuscript of 1 March 2004,
printed p.1010. The consumer
`LargerDimension/Orthogonal/Lift/SymmetricLocal/ExchangedModel` must transport
its actual exchanged quotient action to this matrix action. The cardinality
bridge accepts its joint-core bound without a second quotient-core argument.
-/

public section
namespace ClassicalOrthogonal.FourPlusMatrix.Binary.InvolutionResidual.Swapping
open Module

private theorem card_matrix_group : Nat.card G = 3600 := by
  have hc : Nat.card SL = 60 := by
    change Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 60
    rw [Atlas.card_sl_two]
    simp only [Nat.card_eq_fintype_card, Representation.SL2FourNatural.card_field]
    norm_num
  change Nat.card (SL × SL) = 3600
  rw [Nat.card_prod, hc]

private theorem exists_order_five (R : Subgroup G) (hR : ¬ Group.IsSolvable R) :
    ∃ r : R, orderOf r = 5 := by
  have hd : 5 ∣ Nat.card R := by
    by_contra hn
    apply hR
    apply Theory.GroupTheory.isSolvable_of_prime_dvd_card_eq_two_or_three R
    intro p hp hdiv
    have hpow : p ∣ 60 ^ 2 := by
      have hh := hdiv.trans R.card_subgroup_dvd_card
      rwa [card_matrix_group] at hh
    have hsixty : p ∣ 2 ^ 2 * 3 * 5 := hp.dvd_of_dvd_pow hpow
    rcases hp.dvd_mul.mp hsixty with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
          (hp.dvd_of_dvd_pow h))
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
    · have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h
      exact False.elim (hn (hp5 ▸ hdiv))
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact exists_prime_orderOf_dvd_card' 5 hd

/-- The original subgroup action preserves the actual range of `t - 1`. -/
theorem action_preserves_moved (t : V ≃ₗ[ZMod 2] V) (R : Subgroup G)
    (hcomm : ∀ r : R, Commute t (linearAction (r : G)))
    (r : R) (v : V) (hv : v ∈ LinearMap.range (t.toLinearMap - LinearMap.id)) :
    action (r : G) v ∈ LinearMap.range (t.toLinearMap - LinearMap.id) :=
  moved_invariant t (linearAction r) (hcomm r) v hv

/-- A nonsolvable matrix subgroup centralizing an involution acts irreducibly
on its moved space as soon as that space has dimension greater than two.
The dimension is then exactly four. -/
theorem moved_finrank_and_irreducible (t : V ≃ₗ[ZMod 2] V) (ht : t ^ 2 = 1)
    (R : Subgroup G) (hR : ¬ Group.IsSolvable R)
    (hcomm : ∀ r : R, Commute t (linearAction (r : G)))
    (hr : 2 < finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id))) :
    finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 4 ∧
      ∀ X : Submodule (ZMod 2) V,
        X ≤ LinearMap.range (t.toLinearMap - LinearMap.id) →
        (∀ (r : R) (v : V), v ∈ X → action (r : G) v ∈ X) →
        X = ⊥ ∨ X = LinearMap.range (t.toLinearMap - LinearMap.id) := by
  obtain ⟨r, hr5⟩ := exists_order_five R hR
  have hrne : (r : G) ≠ 1 := by
    intro he
    have h : r = 1 := Subtype.ext he
    rw [h, orderOf_one] at hr5
    norm_num at hr5
  exact moved_four_irreducible_of_order_five (action.comp R.subtype) t ht finrank_binary
    (fun g v => LinearEquiv.congr_fun (hcomm g).eq v) hr r hr5
    (Displacement.displacement_rank_four r hrne)

/-- The cardinal inequality supplied by the quotient commutator calculation
is precisely the strict moved-rank hypothesis. -/
theorem four_lt_moved_card_iff (t : V ≃ₗ[ZMod 2] V) :
    4 < Nat.card (LinearMap.range (t.toLinearMap - LinearMap.id)) ↔
      2 < finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  change (2 : ℕ) ^ 2 < 2 ^ finrank (ZMod 2)
    (LinearMap.range (t.toLinearMap - LinearMap.id)) ↔ _
  exact Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : ℕ))

/-- The exact matrix-module output for a swapping involution in the normalizer.
Preservation, rank, order and invariant intervals refer to the literal action. -/
theorem swapped_moved_module (t : V ≃ₗ[ZMod 2] V)
    (_hn : t ∈ Subgroup.normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)))
    (ht : t ^ 2 = 1) (_hs : SwapsFactors t)
    (hr : 2 < finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)))
    (R : Subgroup G) (hR : ¬ Group.IsSolvable R)
    (hcomm : ∀ r : R, Commute t (linearAction (r : G))) :
    (∀ (r : R) (v : V), v ∈ LinearMap.range (t.toLinearMap - LinearMap.id) →
      action (r : G) v ∈ LinearMap.range (t.toLinearMap - LinearMap.id)) ∧
    finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 4 ∧
    Nat.card (LinearMap.range (t.toLinearMap - LinearMap.id)) = 16 ∧
    ∀ X : Submodule (ZMod 2) V,
      X ≤ LinearMap.range (t.toLinearMap - LinearMap.id) →
      (∀ (r : R) (v : V), v ∈ X → action (r : G) v ∈ X) →
      X = ⊥ ∨ X = LinearMap.range (t.toLinearMap - LinearMap.id) := by
  obtain ⟨hd, hi⟩ := moved_finrank_and_irreducible t ht R hR hcomm hr
  refine ⟨action_preserves_moved t R hcomm, hd, ?_, hi⟩
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]
  norm_num

end ClassicalOrthogonal.FourPlusMatrix.Binary.InvolutionResidual.Swapping
