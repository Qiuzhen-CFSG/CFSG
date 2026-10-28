module

public import Stellmacher.Recognition.LyonsU3Four.ElementOrders
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismReduction
public import Theory.GroupAction.OrderFifteenOnSixteen
public import Theory.GroupAction.FourAutomorphismOrbit

/-!
# The action of an order-fifteen Sylow automorphism

An actual automorphism of order fifteen acts faithfully on the Frattini
quotient, which is the sixteen-element central quotient. The order-five
subgroup makes this quotient irreducible; the cyclic order-fifteen action
is therefore regular on its nonidentity elements.

Equal central cosets have equal squares. If the center action were trivial,
quotient transitivity would make all noncentral squares equal, contradicting
the fact that squares generate the four-element center. Its automorphism
group has order six, so the center action has order three and is transitive
on the three nonidentity elements. Finally, a fixed point upstairs maps to a fixed point in
the quotient and then lies in the fixed subgroup of the center, so is one.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), Lemma 1,
pp. 372–373. The automorphism is arbitrary; its construction is independent
of this module. In particular, its cube fixes the center.
-/

namespace Stellmacher.Recognition.LyonsU3Four

/-- The central quotient in the intrinsic Sylow configuration has order sixteen. -/
public theorem center_quotient_card {G : Type*} [Group G]
    (S : Sylow 2 G) (h : SylowStructure S) :
    Nat.card (S ⧸ Subgroup.center S) = 16 := by
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center S)
  rw [h.card, h.center_card] at hc
  omega

/-- An order-fifteen automorphism retains its full order on the central quotient. -/
public theorem order_fifteen_quotient_order
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15) :
    orderOf (Subgroup.quotientAut (Subgroup.center S) β) = 15 := by
  let A := Subgroup.zpowers β
  have hodd : Odd (Nat.card A) := by rw [Nat.card_zpowers, hβ]; decide
  have hi := SmallNonabelianTwoGroup.odd_frattini_action_injective S.isPGroup' A hodd
  have hiC (C : Subgroup S) [C.Characteristic] (hC : C = frattini S) :
      Function.Injective ((Subgroup.quotientAut C).comp A.subtype) := by
    subst C
    exact hi
  have hiZ := hiC (Subgroup.center S) h.center_eq_frattini
  let b : A := ⟨β, Subgroup.mem_zpowers β⟩
  have hh := orderOf_injective
    ((Subgroup.quotientAut (Subgroup.center S)).comp A.subtype) hiZ b
  exact hh.trans ((Subgroup.orderOf_coe b).symm.trans hβ)

/-- Powers of the induced quotient automorphism are transitive on nonidentity cosets. -/
public theorem order_fifteen_quotient_transitive
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15)
    (x y : S ⧸ Subgroup.center S) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ n : ℤ, (Subgroup.quotientAut (Subgroup.center S) β ^ n) x = y :=
  MulAut.exists_zpow_apply_eq_of_order_fifteen (center_quotient_card S h) _
    (order_fifteen_quotient_order S h β hβ) x y hx hy

private theorem square_eq_of_center_coset_eq
    {G : Type*} [Group G] (S : Sylow 2 G) (h : SylowStructure S)
    (u v : S) (he : QuotientGroup.mk' (Subgroup.center S) u =
      QuotientGroup.mk' (Subgroup.center S) v) : u ^ 2 = v ^ 2 := by
  have hz : u⁻¹ * v ∈ Subgroup.center S := QuotientGroup.eq.mp he
  have hc : Commute u (u⁻¹ * v) := Subgroup.mem_center_iff.mp hz u
  let _ := h.center_elementary
  have hz2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (u⁻¹ * v) hz
  have hh := hc.mul_pow 2
  rw [mul_inv_cancel_left, hz2, mul_one] at hh
  exact hh.symm

private theorem order_fifteen_center_ne_one
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15) :
    MulAut.characteristic (Subgroup.center S) β ≠ 1 := by
  intro htrivial
  let Z := Subgroup.center S
  let _ := h.center_elementary
  obtain ⟨u, hu⟩ : ∃ u : S, u ∉ Z := by
    by_contra! hall
    have htop : Z = ⊤ := top_unique (fun u _ => hall u)
    have hc := h.center_card
    change Nat.card Z = 4 at hc
    rw [htop, Subgroup.card_top, h.card] at hc
    omega
  have hfix (n : ℤ) (z : S) (hz : z ∈ Z) : (β ^ n) z = z := by
    have he : MulAut.characteristic Z (β ^ n) = 1 := by
      rw [map_zpow, htrivial, one_zpow]
    exact congrArg Subtype.val (DFunLike.congr_fun he ⟨z, hz⟩)
  have hsq (v : S) : v ^ 2 ∈ Subgroup.zpowers (u ^ 2) := by
    by_cases hv : v ∈ Z
    · rw [elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv]
      exact Subgroup.one_mem _
    · obtain ⟨n, hn⟩ := order_fifteen_quotient_transitive S h β hβ
        (QuotientGroup.mk' Z u) (QuotientGroup.mk' Z v)
        (fun he => hu ((QuotientGroup.eq_one_iff _).mp he))
        (fun he => hv ((QuotientGroup.eq_one_iff _).mp he))
      have hcoset : QuotientGroup.mk' Z ((β ^ n) u) = QuotientGroup.mk' Z v := by
        simpa only [Z, ← map_zpow, Subgroup.quotientAut_apply_mk] using hn
      have hsquare := square_eq_of_center_coset_eq S h _ _ hcoset
      have he : v ^ 2 = u ^ 2 := by
        rw [← hsquare, ← map_pow]
        exact hfix n _ (square_mem_center S h u)
      rw [he]
      exact Subgroup.mem_zpowers _
  have hle : Z ≤ Subgroup.zpowers (u ^ 2) := by
    change Subgroup.center S ≤ _
    rw [h.center_eq_squares]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨v, rfl⟩
    exact hsq v
  have hc := Subgroup.card_le_of_le hle
  rw [h.center_card, Nat.card_zpowers] at hc
  have hd := orderOf_dvd_of_pow_eq_one
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (u ^ 2) (square_mem_center S h u))
  have hb := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

/-- The restriction of an order-fifteen automorphism to the center has order three. -/
public theorem order_fifteen_center_order
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15) :
    orderOf (MulAut.characteristic (Subgroup.center S) β) = 3 := by
  let W := Subgroup.center S
  let a := MulAut.characteristic W β
  let _ := h.center_elementary
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by
    change 1 < Nat.card (Subgroup.center S)
    rw [h.center_card]
    decide)
  let _ : IsKleinFour W := ⟨h.center_card, IsElementaryAbelian.exponent_eq_prime⟩
  have hd6 : orderOf a ∣ 6 := IsKleinFour.card_mulAut W ▸ orderOf_dvd_natCard a
  have hd15 : orderOf a ∣ 15 := hβ ▸ orderOf_map_dvd (MulAut.characteristic W) β
  have hd3 : orderOf a ∣ 3 := Nat.dvd_gcd hd6 hd15
  exact ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd3).resolve_left
    (fun he => order_fifteen_center_ne_one S h β hβ (orderOf_eq_one_iff.mp he))

/-- The induced center automorphism is transitive on its three nonidentity elements. -/
public theorem order_fifteen_center_transitive
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15)
    (x y : Subgroup.center S) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ n : ℤ, (MulAut.characteristic (Subgroup.center S) β ^ n) x = y := by
  let _ := h.center_elementary
  let a := MulAut.characteristic (Subgroup.center S) β
  have hcard : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers]
    exact order_fifteen_center_order S h β hβ
  obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.mp
    (MulAction.nonidentity_mem_orbit_of_four_automorphism_subgroup h.center_card
      (Subgroup.zpowers a) (by rw [hcard]; decide) x hx y hy)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b.property
  refine ⟨n, ?_⟩
  change (a ^ n) x = y
  rw [hn]
  exact hb

/-- Only the identity in the center is fixed by the order-fifteen automorphism. -/
public theorem order_fifteen_center_fixed_eq_one
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15)
    (z : Subgroup.center S) (hz : MulAut.characteristic (Subgroup.center S) β z = z) :
    z = 1 := by
  by_contra hne
  have hle := card_mulAut_subgroup_le_two_of_fixed_point h.center_card z hne
    (Subgroup.zpowers (MulAut.characteristic (Subgroup.center S) β))
    (fun f hf => smul_eq_self_of_mem_zpowers hf hz)
  rw [Nat.card_zpowers, order_fifteen_center_order S h β hβ] at hle
  omega

/-- The order-fifteen automorphism fixes only the identity of the Sylow subgroup. -/
public theorem order_fifteen_fixed_eq_one
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15)
    (s : S) (hs : β s = s) : s = 1 := by
  have hq := MulAut.fixed_eq_one_of_order_fifteen (center_quotient_card S h)
    (Subgroup.quotientAut (Subgroup.center S) β) (order_fifteen_quotient_order S h β hβ)
    (QuotientGroup.mk' (Subgroup.center S) s) (by
      rw [Subgroup.quotientAut_apply_mk, hs])
  have hsZ := (QuotientGroup.eq_one_iff _).mp hq
  exact congrArg Subtype.val (order_fifteen_center_fixed_eq_one S h β hβ
    ⟨s, hsZ⟩ (Subtype.ext hs))

end Stellmacher.Recognition.LyonsU3Four
