module

public import Theory.GroupTheory.Recognition.ReeTwo.Order1024RankTwoCoordinates
public import Theory.SpecificGroups.ReeTwo.TwistedParityPowerCounts

/-!
# Exact element-order counts in the rank-two residual Ree two fibers

The fibers of the three rank-two projections are fibers of the twisted parity
coordinates. Writing the rank-two coordinates as `(u,a)`, their twisted
coordinates are `(a,u,u)`, `(a,u,u+a)`, and `(a,u,a)`, respectively. A finite
certificate in the order-64 tail quotient proves this identification for the
original subgroups. The resulting bijection preserves the ambient element,
so it transports every power equation.

We reuse the kernel-checked polynomial power counts from
`TwistedParityPowerCounts`. Subtracting the identity count from the square
count gives the order-two count; subtracting the square count from the
fourth-power count gives the order-four count. This does not require identifying
either coordinate kernel with a Frattini subgroup.

Source: Shinoda (1975), (2.3), pp. 81–82, with the root and coordinate conventions
of `Order1024RankTwoCoordinates` and `TwistedParityCoordinates`.
-/

namespace ReeTwo.SylowModel
set_option maxRecDepth 32768

private theorem rankTwo_orderProfile_one {c : Fin 3} (v : OrderProfileQuotient 2) :
    Subgroup.fiberProfile (rankTwoProjection c) orderOf v 1 = if v = 1 then 1 else 0 := by
  classical
  rw [Subgroup.fiberProfile_eq_card_filter]
  by_cases h : v = 1
  · subst v
    have he : (Finset.univ.filter (fun x : residualCandidate (rankTwoIndex c) =>
        rankTwoProjection c x = 1 ∧ orderOf x = 1)) = {1} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        orderOf_eq_one_iff]
      exact ⟨And.right, fun hx => ⟨hx ▸ map_one (rankTwoProjection c), hx⟩⟩
    rw [he, Finset.card_singleton, if_pos rfl]
  · have he : (Finset.univ.filter (fun x : residualCandidate (rankTwoIndex c) =>
        rankTwoProjection c x = v ∧ orderOf x = 1)) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false, orderOf_eq_one_iff]
      rintro ⟨hx, rfl⟩
      exact h (hx.symm.trans (map_one (rankTwoProjection c)))
    rw [he, Finset.card_empty, if_neg h]

private def rankTwoTwistedEncode (c : Fin 3) (v : OrderProfileQuotient 2) :
    TwistedParityQuotient :=
  let a := v.toAdd 1
  let u := v.toAdd 0
  Multiplicative.ofAdd ![a, u, ![u, u+a, a] c]

private def rankTwoTwistedTail (q : TailQuotient.Group) : TwistedParityQuotient :=
  Multiplicative.ofAdd ![(parity q.right).toAdd,
    q.left.toAdd 1 + (q.right.toAdd.val / 2 : ℕ),
    q.left.toAdd 2 + q.left.toAdd 3 + (q.right.toAdd.val / 2 : ℕ)]

set_option maxHeartbeats 8000000 in
private theorem rankTwo_twisted_fiber_certificate : ∀ (c : Fin 3)
    (v : OrderProfileQuotient 2) (q : TailQuotient.Group),
    (rankTwoTailMember c q ∧ rankTwoCoordinates q = v) ↔
    (q.left.toAdd 0 = (parity q.right).toAdd ∧
      rankTwoTwistedTail q = rankTwoTwistedEncode c v) := by decide +kernel

private theorem rankTwo_twisted_fiber (c : Fin 3) (v : OrderProfileQuotient 2)
    (x : SylowModel) :
    (x ∈ residualCandidate (rankTwoIndex c) ∧
      rankTwoCoordinates (TailQuotient.projection x) = v) ↔
    (x ∈ (maximalCharacter 1 1 0).ker ∧
      rankTwoTwistedTail (TailQuotient.projection x) = rankTwoTwistedEncode c v) := by
  rw [rankTwoCandidate_mem, mem_twistedParityKernel]
  exact rankTwo_twisted_fiber_certificate c v (TailQuotient.projection x)

private theorem rankTwo_power_transfer (c : Fin 3) (v : OrderProfileQuotient 2) (n : ℕ) :
    MonoidHom.powerFiberCard (rankTwoProjection c) v n =
      twistedParityCoordinates.powerFiberCard (rankTwoTwistedEncode c v) n := by
  unfold MonoidHom.powerFiberCard
  apply Nat.card_congr
  refine {
    toFun := fun x => ⟨⟨x.val.val, ?_⟩, ?_, ?_⟩
    invFun := fun x => ⟨⟨x.val.val, ?_⟩, ?_, ?_⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  · exact ((rankTwo_twisted_fiber c v x.val.val).mp ⟨x.val.property, x.property.1⟩).1
  · exact ((rankTwo_twisted_fiber c v x.val.val).mp ⟨x.val.property, x.property.1⟩).2
  · apply Subtype.ext
    change x.val.val ^ n = (1 : SylowModel)
    exact congrArg (fun z : residualCandidate (rankTwoIndex c) => (z : SylowModel))
      x.property.2
  · exact ((rankTwo_twisted_fiber c v x.val.val).mpr ⟨x.val.property, x.property.1⟩).1
  · exact ((rankTwo_twisted_fiber c v x.val.val).mpr ⟨x.val.property, x.property.1⟩).2
  · apply Subtype.ext
    change x.val.val ^ n = (1 : SylowModel)
    exact congrArg (fun z : (maximalCharacter 1 1 0).ker => (z : SylowModel))
      x.property.2

private theorem rankTwo_power_counts (c : Fin 3) (v : OrderProfileQuotient 2) :
    (MonoidHom.powerFiberCard (rankTwoProjection c) v 2,
      MonoidHom.powerFiberCard (rankTwoProjection c) v 4) =
      twistedParityProfile (rankTwoTwistedEncode c v) := by
  rw [rankTwo_power_transfer, rankTwo_power_transfer]
  exact twistedParityCoordinates_powerFiberCard _

private theorem rankTwo_divisors_four (n : ℕ) : n ∣ 4 ↔ n ∣ 2 ∨ n = 4 := by
  constructor
  · intro h
    have hn := Nat.le_of_dvd (by decide : 0 < 4) h
    interval_cases n <;> norm_num at *
  · rintro (h | rfl)
    · exact dvd_trans h (by decide)
    · exact dvd_refl _

private theorem rankTwo_power_order_counts (c : Fin 3) (v : OrderProfileQuotient 2) :
    (Subgroup.fiberProfile (rankTwoProjection c) orderOf v 1,
      Subgroup.fiberProfile (rankTwoProjection c) orderOf v 2,
      Subgroup.fiberProfile (rankTwoProjection c) orderOf v 4) =
      (if v = 1 then 1 else 0,
        (MonoidHom.powerFiberCard (rankTwoProjection c) v 2) -
          (if v = 1 then 1 else 0),
        (MonoidHom.powerFiberCard (rankTwoProjection c) v 4) -
          MonoidHom.powerFiberCard (rankTwoProjection c) v 2) := by
  classical
  have htwo (x : residualCandidate (rankTwoIndex c)) : x ^ 2 = 1 ↔
      orderOf x = 1 ∨ orderOf x = 2 := by
    rw [← orderOf_dvd_iff_pow_eq_one, Nat.dvd_prime Nat.prime_two]
  have hfour (x : residualCandidate (rankTwoIndex c)) : x ^ 4 = 1 ↔
      x ^ 2 = 1 ∨ orderOf x = 4 := by
    rw [← orderOf_dvd_iff_pow_eq_one, rankTwo_divisors_four, orderOf_dvd_iff_pow_eq_one]
  have h2 : Subgroup.fiberProfile (rankTwoProjection c) orderOf v 1 +
      Subgroup.fiberProfile (rankTwoProjection c) orderOf v 2 =
      MonoidHom.powerFiberCard (rankTwoProjection c) v 2 := by
    rw [Subgroup.fiberProfile_eq_card_filter, Subgroup.fiberProfile_eq_card_filter,
      MonoidHom.powerFiberCard, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have h := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter (fun x : residualCandidate (rankTwoIndex c) =>
        rankTwoProjection c x = v ∧ x ^ 2 = 1)) (fun x => orderOf x = 1)
    simpa only [Finset.filter_filter, htwo,
      show ∀ x : residualCandidate (rankTwoIndex c),
        (rankTwoProjection c x = v ∧ (orderOf x = 1 ∨ orderOf x = 2)) ∧ orderOf x = 1 ↔
        rankTwoProjection c x = v ∧ orderOf x = 1 by
            intro x
            constructor
            · rintro ⟨⟨hx, _⟩, ho⟩; exact ⟨hx, ho⟩
            · rintro ⟨hx, ho⟩; exact ⟨⟨hx, Or.inl ho⟩, ho⟩,
      show ∀ x : residualCandidate (rankTwoIndex c),
        (rankTwoProjection c x = v ∧ (orderOf x = 1 ∨ orderOf x = 2)) ∧ ¬orderOf x = 1 ↔
        rankTwoProjection c x = v ∧ orderOf x = 2 by
            intro x
            constructor
            · rintro ⟨⟨hx, h|h⟩, hn⟩
              · exact False.elim (hn h)
              · exact ⟨hx, h⟩
            · rintro ⟨hx, ho⟩; exact ⟨⟨hx, Or.inr ho⟩, by omega⟩] using h
  have h4 : MonoidHom.powerFiberCard (rankTwoProjection c) v 2 +
      Subgroup.fiberProfile (rankTwoProjection c) orderOf v 4 =
      MonoidHom.powerFiberCard (rankTwoProjection c) v 4 := by
    rw [Subgroup.fiberProfile_eq_card_filter, MonoidHom.powerFiberCard,
      MonoidHom.powerFiberCard, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype, Fintype.card_subtype]
    have h := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter (fun x : residualCandidate (rankTwoIndex c) =>
        rankTwoProjection c x = v ∧ x ^ 4 = 1)) (fun x => x ^ 2 = 1)
    have he (x : residualCandidate (rankTwoIndex c)) : orderOf x = 4 → ¬x ^ 2 = 1 := by
      rw [htwo]; omega
    simpa only [Finset.filter_filter, hfour,
      show ∀ x : residualCandidate (rankTwoIndex c),
        (rankTwoProjection c x = v ∧ (x ^ 2 = 1 ∨ orderOf x = 4)) ∧ x ^ 2 = 1 ↔
          rankTwoProjection c x = v ∧ x ^ 2 = 1 by
            intro x
            constructor
            · rintro ⟨⟨hx, _⟩, hs⟩; exact ⟨hx, hs⟩
            · rintro ⟨hx, hs⟩; exact ⟨⟨hx, Or.inl hs⟩, hs⟩,
      show ∀ x : residualCandidate (rankTwoIndex c),
        (rankTwoProjection c x = v ∧ (x ^ 2 = 1 ∨ orderOf x = 4)) ∧ ¬x ^ 2 = 1 ↔
          rankTwoProjection c x = v ∧ orderOf x = 4 by
            intro x
            constructor
            · rintro ⟨⟨hx, h|h⟩, hn⟩
              · exact False.elim (hn h)
              · exact ⟨hx, h⟩
            · rintro ⟨hx, ho⟩; exact ⟨⟨hx, Or.inr ho⟩, he x ho⟩] using h
  rw [rankTwo_orderProfile_one] at h2 ⊢
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> dsimp only <;> omega

/-- Exact order-one, order-two and order-four counts in the three rank-two fibers. -/
public theorem rankTwoProjection_order_counts (c : Fin 3) (v : OrderProfileQuotient 2) :
    (Subgroup.fiberProfile (rankTwoProjection c) orderOf v 1,
      Subgroup.fiberProfile (rankTwoProjection c) orderOf v 2,
      Subgroup.fiberProfile (rankTwoProjection c) orderOf v 4) = rankTwoProfileCounts c v := by
  rw [rankTwo_power_order_counts]
  have hp := rankTwo_power_counts c v
  rw [show (rankTwoProjection c).powerFiberCard v 2 =
      (twistedParityProfile (rankTwoTwistedEncode c v)).1 from congrArg Prod.fst hp,
    show (rankTwoProjection c).powerFiberCard v 4 =
      (twistedParityProfile (rankTwoTwistedEncode c v)).2 from congrArg Prod.snd hp]
  exact (by decide +kernel : ∀ (c : Fin 3) (v : OrderProfileQuotient 2),
    (if v = 1 then 1 else 0,
      (twistedParityProfile (rankTwoTwistedEncode c v)).1 - (if v = 1 then 1 else 0),
      (twistedParityProfile (rankTwoTwistedEncode c v)).2 -
        (twistedParityProfile (rankTwoTwistedEncode c v)).1) = rankTwoProfileCounts c v) c v

end ReeTwo.SylowModel
