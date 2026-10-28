module

public import Theory.Representation.BinaryCoprimeDegree.HyperplaneBounds.PrimeContribution
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Prime-order binary displacement

For a faithful binary representation, an odd-prime cyclic actor moves at least
as many dimensions as the multiplicative order of two modulo that prime.
Apply the hyperplane contribution bound to the trivial subgroup of the cyclic
actor: its contribution is exactly the fixed codimension. In particular an
order-eleven actor moves at least ten dimensions.

If an element inverts a cubic actor, their commutator is the cubic actor itself.
The commutator rank inequality therefore bounds its displacement by twice the
inverter's displacement. These are the elementary representation steps in
Aschbacher–Smith H.12.1, printed p.394 (combined 1 March 2004 manuscript).
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The binary prime degree bounds the moved dimension of a faithful actor. -/
theorem prime_order_le_fixedCodim (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (x : G) (hx : orderOf x = p) :
    orderOf (2 : ZMod p) ≤ fixedCodim ρ (zpowers x) := by
  let : Fact p.Prime := ⟨hp⟩
  let P := zpowers x
  let : IsElementaryAbelian p P :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (hx ▸ pow_orderOf_eq_one x)
  have hcard : Nat.card P = p := by
    change Nat.card (zpowers x) = p
    rw [Nat.card_zpowers, hx]
  have hP : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    exact hp.ne_one hcard.symm
  have hbot : invariants (ρ.comp (P.subtype.comp (⊥ : Subgroup P).subtype)) = ⊤ := by
    apply top_unique
    intro v _ g
    have hg : (g : P) = 1 := g.property
    change ρ (P.subtype (g : P)) v = v
    rw [hg, map_one, map_one]
    rfl
  have hmult : BinaryCoprimeDegree.hyperplaneMultiplicity ρ P ⊥ = fixedCodim ρ P := by
    unfold BinaryCoprimeDegree.hyperplaneMultiplicity
    rw [hbot, finrank_top]
    have h := fixedCodim_add_finrank ρ P
    change fixedCodim ρ P + Module.finrank (ZMod 2) (invariants (ρ.comp P.subtype)) = _ at h
    omega
  have hpos : 0 < BinaryCoprimeDegree.hyperplaneMultiplicity ρ P ⊥ := by
    unfold BinaryCoprimeDegree.hyperplaneMultiplicity
    rw [hbot, finrank_top]
    exact Nat.sub_pos_of_lt
      (BinaryCoprimeDegree.fixed_finrank_lt_of_faithful ρ hρ P hP)
  have h := BinaryCoprimeDegree.orderOf_le_hyperplaneMultiplicity ρ hp2 P ⊥
    (by rw [Subgroup.index_bot, hcard]) hpos
  rwa [hmult] at h


omit [Finite G] in
/-- Inversion of an order-three actor bounds its displacement by twice that
of the inverter. No order assumption on the inverter is needed. -/
theorem fixedCodim_three_le_twice_of_inverted (ρ : Representation (ZMod 2) G V)
    (x t : G) (hx : orderOf x = 3) (hi : t * x * t⁻¹ = x⁻¹) :
    fixedCodim ρ (zpowers x) ≤ 2 * fixedCodim ρ (zpowers t) := by
  have hpow : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have he : t * x * t⁻¹ * x⁻¹ = x := by
    rw [hi, ← mul_inv_rev]
    apply inv_eq_iff_eq_inv.mpr
    apply mul_eq_one_iff_eq_inv.mp
    simpa only [pow_succ, pow_zero, one_mul] using hpow
  simpa only [he] using fixedCodim_commutator_le_twice ρ t x

/-- Every faithful binary order-eleven actor moves at least ten dimensions. -/
theorem ten_le_fixedCodim_of_order_eleven (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) (x : G) (hx : orderOf x = 11) :
    10 ≤ fixedCodim ρ (zpowers x) := by
  simpa only [BinaryPrimeDegree.orderOf_two_mod_eleven] using
    prime_order_le_fixedCodim ρ hρ (by decide : Nat.Prime 11) (by decide) x hx

end Representation.BinaryOffender
