module

public import Theory.GroupTheory.Recognition.ReeTwo.Order1024OrderProfileRankThreeCoordinates
public import Theory.SpecificGroups.ReeTwo.ParityFrattiniPowerCounts

/-!
# Exact order counts for the five rank-three residual Ree two quotients

The shared seven-bit coordinates identify each rank-three projection fiber
with the full parity-projection fiber at its encoded quotient value. Ambient
inclusions preserve element orders, so their order profiles agree.

For any finite group, the solutions of x² = 1 consist of the identity and
elements of order 2; the solutions of x⁴ = 1 additionally contain exactly the
elements of order 4. Subtracting the verified parity power counts therefore
gives the three exact order counts. Only the five eight-entry quotient tables
are checked here by finite reduction; the group enumeration is reused from
`ParityFrattiniPowerCounts`. No Frattini-kernel identification is required.

Source: Shinoda (1975), (2.3), pp. 81–82, with the ordered quotient bases
specified in `Order1024OrderProfileRankThreeCoordinates` and the verified
power formulas of `ParityFrattiniPowerCounts`.
-/

namespace ReeTwo.SylowModel

/-- The identity contributes once, precisely in the trivial fiber. -/
private theorem orderProfile_one {G Q : Type*} [Group G] [Group Q] [Fintype G] [DecidableEq Q]
    (π : G →* Q) (v : Q) :
    Subgroup.fiberProfile π orderOf v 1 = if v = 1 then 1 else 0 := by
  classical
  rw [Subgroup.fiberProfile_eq_card_filter]
  by_cases h : v = 1
  · subst v
    have he : (Finset.univ.filter fun x : G => π x = 1 ∧ orderOf x = 1) = {1} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        orderOf_eq_one_iff]
      exact ⟨And.right, fun hx => ⟨hx ▸ map_one π, hx⟩⟩
    rw [he, Finset.card_singleton, if_pos rfl]
  · have he : (Finset.univ.filter fun x : G => π x = v ∧ orderOf x = 1) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false, orderOf_eq_one_iff]
      rintro ⟨hx, rfl⟩
      exact h (hx.symm.trans (map_one π))
    rw [he, Finset.card_empty, if_neg h]

private theorem divisors_four (n : ℕ) : n ∣ 4 ↔ n ∣ 2 ∨ n = 4 := by
  constructor
  · intro h
    have hn := Nat.le_of_dvd (by decide : 0 < 4) h
    interval_cases n <;> norm_num at *
  · rintro (h | rfl)
    · exact dvd_trans h (by decide)
    · exact dvd_refl _

/-- Exact orders are obtained by subtracting successive power-solution counts. -/
private theorem power_order_counts {G Q : Type*} [Group G] [Group Q] [Fintype G] [DecidableEq Q]
    (π : G →* Q) (v : Q) :
    (Subgroup.fiberProfile π orderOf v 1,
      Subgroup.fiberProfile π orderOf v 2,
      Subgroup.fiberProfile π orderOf v 4) =
    (if v = 1 then 1 else 0,
      π.powerFiberCard v 2 - (if v = 1 then 1 else 0),
      π.powerFiberCard v 4 - π.powerFiberCard v 2) := by
  classical
  have htwo (x : G) : x ^ 2 = 1 ↔ orderOf x = 1 ∨ orderOf x = 2 := by
    rw [← orderOf_dvd_iff_pow_eq_one, Nat.dvd_prime Nat.prime_two]
  have hfour (x : G) : x ^ 4 = 1 ↔ x ^ 2 = 1 ∨ orderOf x = 4 := by
    rw [← orderOf_dvd_iff_pow_eq_one, divisors_four, orderOf_dvd_iff_pow_eq_one]
  have h2 : Subgroup.fiberProfile π orderOf v 1 +
      Subgroup.fiberProfile π orderOf v 2 = π.powerFiberCard v 2 := by
    rw [Subgroup.fiberProfile_eq_card_filter, Subgroup.fiberProfile_eq_card_filter,
      MonoidHom.powerFiberCard, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have h := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter (fun x : G => π x = v ∧ x ^ 2 = 1))
      (fun x => orderOf x = 1)
    simpa only [Finset.filter_filter, htwo,
      show ∀ x : G, (π x = v ∧ (orderOf x = 1 ∨ orderOf x = 2)) ∧ orderOf x = 1 ↔
        π x = v ∧ orderOf x = 1 by
          intro x
          have hn : ¬(orderOf x = 1 ∧ orderOf x = 2) := by omega
          tauto,
      show ∀ x : G, (π x = v ∧ (orderOf x = 1 ∨ orderOf x = 2)) ∧ ¬orderOf x = 1 ↔
        π x = v ∧ orderOf x = 2 by
          intro x
          have hn : ¬(orderOf x = 1 ∧ orderOf x = 2) := by omega
          tauto] using h
  have h4 : π.powerFiberCard v 2 + Subgroup.fiberProfile π orderOf v 4 =
      π.powerFiberCard v 4 := by
    rw [Subgroup.fiberProfile_eq_card_filter,
      MonoidHom.powerFiberCard, MonoidHom.powerFiberCard,
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype, Fintype.card_subtype]
    have h := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter (fun x : G => π x = v ∧ x ^ 4 = 1))
      (fun x => x ^ 2 = 1)
    have he (x : G) : orderOf x = 4 → ¬x ^ 2 = 1 := by
      rw [htwo]; omega
    simpa only [Finset.filter_filter, hfour,
      show ∀ x : G, (π x = v ∧ (x ^ 2 = 1 ∨ orderOf x = 4)) ∧ x ^ 2 = 1 ↔
        π x = v ∧ x ^ 2 = 1 by intro x; tauto,
      show ∀ x : G, (π x = v ∧ (x ^ 2 = 1 ∨ orderOf x = 4)) ∧ ¬x ^ 2 = 1 ↔
        π x = v ∧ orderOf x = 4 by intro x; have := he x; tauto] using h
  rw [orderProfile_one] at h2 ⊢
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> dsimp only <;> omega

/-- The shared ambient representatives identify all exact-order fibers. -/
private theorem rankThree_order_transfer (j : Fin 5) (v : OrderProfileQuotient 3) (n : ℕ) :
    Subgroup.fiberProfile (rankThreeProjection j) orderOf v n =
      Subgroup.fiberProfile parityProjection orderOf (rankThreeEncode j v) n := by
  classical
  let : Fintype ParityKernel := Fintype.ofFinite _
  rw [rankThreeProjection_fiberProfile, Subgroup.fiberProfile_eq_card_filter,
    ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  refine {
    toFun := fun w => ⟨parityElement (rankThreeEncode j v) w.val,
      parityProjection_element _ _, ?_⟩
    invFun := fun x => ⟨parityRemainder x.val, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · simpa only [rankThreeElement, Subgroup.orderOf_mk, Subgroup.orderOf_coe] using w.property
  · have he : parityElement (rankThreeEncode j v) (parityRemainder x.val) = x.val := by
      simpa only [x.property.1] using parityElement_coordinates x.val
    have ho : orderOf (rankThreeElement j v (parityRemainder x.val)) = orderOf x.val := by
      change orderOf (⟨_, _⟩ : residualCandidate (rankThreeIndex j)) = _
      rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe x.val]
      exact congrArg (fun y : ParityKernel => orderOf y.val) he
    exact ho.trans x.property.2
  · intro w
    apply Subtype.ext
    funext i; fin_cases i <;> rfl
  · intro x
    apply Subtype.ext
    simpa only [x.property.1] using parityElement_coordinates x.val

set_option maxRecDepth 8192 in
/-- The small quotient tables agree after converting power counts to exact orders. -/
private theorem tables : ∀ (j : Fin 5) (v : OrderProfileQuotient 3),
    (if rankThreeEncode j v = 1 then 1 else 0,
      (parityProfile (rankThreeEncode j v)).1 -
        (if rankThreeEncode j v = 1 then 1 else 0),
      (parityProfile (rankThreeEncode j v)).2 -
        (parityProfile (rankThreeEncode j v)).1) = rankThreeCounts j v := by
  decide +kernel

/-- Counts of orders 1, 2, and 4 in each of the five rank-three projection fibers. -/
public theorem rankThreeProjection_orderCounts (j : Fin 5) (v : OrderProfileQuotient 3) :
    (Subgroup.fiberProfile (rankThreeProjection j) orderOf v 1,
      Subgroup.fiberProfile (rankThreeProjection j) orderOf v 2,
      Subgroup.fiberProfile (rankThreeProjection j) orderOf v 4) = rankThreeCounts j v := by
  classical
  let : Fintype ParityKernel := Fintype.ofFinite _
  rw [rankThree_order_transfer, rankThree_order_transfer, rankThree_order_transfer,
    power_order_counts]
  have h := parityProjection_powerFiberCounts (rankThreeEncode j v)
  rw [show parityProjection.powerFiberCard (rankThreeEncode j v) 2 =
      (parityProfile (rankThreeEncode j v)).1 from congrArg Prod.fst h,
    show parityProjection.powerFiberCard (rankThreeEncode j v) 4 =
      (parityProfile (rankThreeEncode j v)).2 from congrArg Prod.snd h]
  exact tables j v

end ReeTwo.SylowModel
