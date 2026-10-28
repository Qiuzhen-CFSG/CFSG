module

public import Theory.GroupAction.FourthPowerFixed

/-!
# Counting fixed points of an automorphism of fourth power one

On a finite elementary binary group, an involution has at least the
square root of the group order as fixed points. Apply this first to a²
on the whole group and then to a on the fixed subgroup of a². This gives
|V| ≤ |C_V(a)|⁴. In particular an action of fourth power one on a group
of order 32 cannot have just two fixed points.

This is the counting step in Parrott, *A characterization of the Tits'
simple group* (1972), pp.674–676. The hypothesis concerns the actual
automorphism; order four only on a quotient does not suffice.
-/

namespace MulAut
open Subgroup
open scoped IsMulCommutative

/-- An involutory automorphism of an elementary binary group has at least
square-root many fixed points. The identity is allowed. -/
public theorem card_le_fixed_card_sq_of_square_eq_one
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (a : MulAut V) (ha : a ^ 2 = 1) :
    Nat.card V ≤ Nat.card (FixedPoints.subgroup (zpowers a) V) ^ 2 := by
  obtain ⟨hc, hle⟩ := involution_fixed_displacement_card_data a ha
  rw [hc, pow_two]
  exact Nat.mul_le_mul_left _ (card_le_of_le hle)

/-- Restricting to the fixed subgroup of the square gives the fourth-root
fixed-point bound for an actual automorphism of fourth power one. -/
public theorem card_le_fixed_card_pow_four_of_fourth_power_eq_one
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (a : MulAut V) (ha : a ^ 4 = 1) :
    Nat.card V ≤ Nat.card (FixedPoints.subgroup (zpowers a) V) ^ 4 := by
  let F₂ := FixedPoints.subgroup (zpowers (a ^ 2)) V
  let : IsElementaryAbelian 2 F₂ := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 V) (x : V))) }
  have htwo (v : F₂) : a (a (v : V)) = v :=
    (mem_fixed_zpowers_iff (a ^ 2) (v : V)).mp v.property
  have hstable (v : F₂) : a (v : V) ∈ F₂ := by
    apply (mem_fixed_zpowers_iff _ _).mpr
    change a (a (a (v : V))) = a (v : V)
    rw [htwo]
  let b : MulAut F₂ := {
    toFun := fun v => ⟨a v, hstable v⟩
    invFun := fun v => ⟨a v, hstable v⟩
    left_inv := fun v => Subtype.ext (htwo v)
    right_inv := fun v => Subtype.ext (htwo v)
    map_mul' := fun v w => Subtype.ext (map_mul a (v : V) (w : V)) }
  have hb : b ^ 2 = 1 := by
    ext v
    exact htwo v
  have hfixed : Nat.card (FixedPoints.subgroup (zpowers b) F₂) =
      Nat.card (FixedPoints.subgroup (zpowers a) V) := by
    let i : FixedPoints.subgroup (zpowers b) F₂ →
        FixedPoints.subgroup (zpowers a) V := fun v =>
      ⟨((v : F₂) : V), (mem_fixed_zpowers_iff a _).mpr
        (congrArg F₂.subtype ((mem_fixed_zpowers_iff b _).mp v.property))⟩
    apply Nat.card_congr (Equiv.ofBijective i ?_)
    constructor
    · intro v w hvw
      exact Subtype.ext (Subtype.ext (congrArg
        (fun x : FixedPoints.subgroup (zpowers a) V => (x : V)) hvw))
    · intro v
      have hv : a (v : V) = v := (mem_fixed_zpowers_iff a v).mp v.property
      have hv₂ : (v : V) ∈ F₂ := by
        apply (mem_fixed_zpowers_iff _ _).mpr
        change a (a (v : V)) = v
        rw [hv, hv]
      let v₂ : F₂ := ⟨v, hv₂⟩
      have hvb : v₂ ∈ FixedPoints.subgroup (zpowers b) F₂ :=
        (mem_fixed_zpowers_iff b _).mpr (Subtype.ext hv)
      exact ⟨⟨v₂, hvb⟩, rfl⟩
  have hbcard := card_le_fixed_card_sq_of_square_eq_one b hb
  rw [hfixed] at hbcard
  have hacard := card_le_fixed_card_sq_of_square_eq_one (a ^ 2) (by
    simpa only [← pow_mul] using ha)
  change Nat.card V ≤ Nat.card F₂ ^ 2 at hacard
  calc
    Nat.card V ≤ Nat.card F₂ ^ 2 := hacard
    _ ≤ (Nat.card (FixedPoints.subgroup (zpowers a) V) ^ 2) ^ 2 :=
      Nat.pow_le_pow_left hbcard 2
    _ = _ := by rw [← pow_mul]

/-- A group of order 32 has more than two fixed points under an actual
automorphism of fourth power one. -/
public theorem two_lt_fixed_card_of_card_thirty_two_of_fourth_power_eq_one
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 32) (a : MulAut V) (ha : a ^ 4 = 1) :
    2 < Nat.card (FixedPoints.subgroup (zpowers a) V) := by
  have hc := card_le_fixed_card_pow_four_of_fourth_power_eq_one a ha
  rw [hV] at hc
  by_contra hn
  have hh := Nat.pow_le_pow_left (show Nat.card
    (FixedPoints.subgroup (zpowers a) V) ≤ 2 by omega) 4
  omega

end MulAut
