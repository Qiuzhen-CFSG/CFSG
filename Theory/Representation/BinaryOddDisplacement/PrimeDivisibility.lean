module

public import Theory.Representation.BinaryPrimeDisplacement
public import Mathlib.GroupTheory.PGroup

/-!
# Divisibility of binary displacement

Fixed-point counting for a p-group gives `|V| ≡ |C_V(P)| mod p`.
For odd p, cancellation of the power of two contributed by the fixed space
shows that the multiplicative order of two modulo p divides its codimension.
No semisimplicity or faithfulness assumption is needed.

This supplies the divisibility step in the order-five argument of
Aschbacher–Smith H.12.1, printed p.394.
-/

public section
namespace Representation.BinaryOffender

variable {G V : Type*} [Group G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The binary degree of an odd prime divides every p-group displacement. -/
theorem orderOf_two_dvd_fixedCodim_of_isPGroup
    (ρ : Representation (ZMod 2) G V) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (P : Subgroup G) (hP : IsPGroup p P) :
    orderOf (2 : ZMod p) ∣ fixedCodim ρ P := by
  let : Fact p.Prime := ⟨hp⟩
  let : MulAction P V := {
    smul g v := ρ g v
    one_smul v := by change ρ 1 v = v; simp
    mul_smul g h v := by
      change ρ ((g : G) * h) v = ρ g (ρ h v)
      simp only [map_mul, Module.End.mul_apply] }
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have hfixed : MulAction.fixedPoints P V = (fixedSpace ρ P : Set V) := rfl
  have hmod := hP.card_modEq_card_fixedPoints V
  rw [hfixed] at hmod
  change Nat.card V ≡ Nat.card (fixedSpace ρ P) [MOD p] at hmod
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ P),
    Nat.card_zmod] at hmod
  have heq : (2 : ZMod p) ^ Module.finrank (ZMod 2) V =
      2 ^ Module.finrank (ZMod 2) (fixedSpace ρ P) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (ZMod.natCast_eq_natCast_iff _ _ p).mpr hmod
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have h := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one)
  apply orderOf_dvd_of_pow_eq_one
  apply mul_right_cancel₀ (pow_ne_zero (Module.finrank (ZMod 2) (fixedSpace ρ P)) htwo)
  rw [← pow_add, fixedCodim_add_finrank, one_mul]
  exact heq

/-- A binary p-group action with no fixed vectors has degree divisible by
the multiplicative order of two modulo p. -/
theorem orderOf_two_dvd_finrank_of_isPGroup
    (ρ : Representation (ZMod 2) G V) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hG : IsPGroup p G) (hfix : ρ.invariants = ⊥) :
    orderOf (2 : ZMod p) ∣ Module.finrank (ZMod 2) V := by
  have hh : fixedSpace ρ ⊤ = ρ.invariants := by
    ext v
    constructor
    · intro h g
      exact h ⟨g, Subgroup.mem_top g⟩
    · intro h g
      exact h g.val
  have hd := fixedCodim_add_finrank ρ ⊤
  rw [hh, hfix, finrank_bot, add_zero] at hd
  simpa only [hd] using orderOf_two_dvd_fixedCodim_of_isPGroup ρ hp hp2 ⊤
    (hG.to_subgroup ⊤)

/-- A binary actor of order five has displacement divisible by four. -/
theorem four_dvd_fixedCodim_of_order_five
    (ρ : Representation (ZMod 2) G V) (x : G) (hx : orderOf x = 5) :
    4 ∣ fixedCodim ρ (Subgroup.zpowers x) := by
  simpa only [BinaryPrimeDegree.orderOf_two_mod_five] using
    orderOf_two_dvd_fixedCodim_of_isPGroup ρ (by decide : Nat.Prime 5) (by decide)
      (Subgroup.zpowers x) (IsPGroup.of_card (p := 5) (n := 1) (by
        simpa only [Nat.card_zpowers, pow_one] using hx))

end Representation.BinaryOffender
