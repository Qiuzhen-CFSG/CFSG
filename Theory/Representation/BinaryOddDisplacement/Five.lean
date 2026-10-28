module

public import Theory.Representation.BinaryOddDisplacement.PrimeDivisibility

/-!
# The binary displacement of a Frobenius complement of order five

Choose a nonidentity element of the kernel of order eleven. Fixed-point
freeness makes its commutator with the complement generator nonidentity,
so this commutator also has order eleven. Its displacement is at least ten
and at most twice that of the complement generator. The latter displacement
is divisible by four, hence is at least eight.

This is the Frobenius-group step in Aschbacher–Smith H.12.1, printed p.394.
The argument uses only the generator's fixed-point freeness; a wrapper accepts
the usual fixed-point-free complement hypothesis.
-/

public section
namespace Representation.BinaryOffender
open Subgroup

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The order-five bound only requires fixed-point freeness of the generator. -/
theorem eight_le_fixedCodim_of_five_normalizes_eleven
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (x : G) (hx : orderOf x = 5) (K : Subgroup G) (hK : Nat.card K = 11)
    (hnorm : x ∈ normalizer (K : Set G))
    (hfree : ∀ k : K, x * k * x⁻¹ = k → k = 1) :
    8 ≤ fixedCodim ρ (zpowers x) := by
  let : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨k, hk⟩ := exists_ne (1 : K)
  let c : G := x * k * x⁻¹ * (k : G)⁻¹
  have hcK : c ∈ K := K.mul_mem
    ((mem_normalizer_iff.mp hnorm (k : G)).mp k.property) (K.inv_mem k.property)
  have hc1 : c ≠ 1 := by
    intro h
    apply hk
    apply hfree
    exact mul_inv_eq_one.mp h
  have hcpow : c ^ 11 = 1 := by
    have h := pow_card_eq_one' (x := (⟨c, hcK⟩ : K))
    rw [hK] at h
    exact congrArg Subtype.val h
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hc : orderOf c = 11 := orderOf_eq_prime hcpow hc1
  have hlo := ten_le_fixedCodim_of_order_eleven ρ hρ c hc
  have hhi := fixedCodim_commutator_le_twice ρ x k
  have hdiv := four_dvd_fixedCodim_of_order_five ρ x hx
  change fixedCodim ρ (zpowers c) ≤ 2 * fixedCodim ρ (zpowers x) at hhi
  omega

/-- A faithful binary representation moves at least eight dimensions under
the complement generator in a Frobenius subgroup of order fifty-five. -/
theorem eight_le_fixedCodim_of_frobenius_fiftyFive
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (x : G) (hx : orderOf x = 5) (K : Subgroup G) (hK : Nat.card K = 11)
    (hnorm : zpowers x ≤ normalizer (K : Set G))
    (hfree : ∀ c : zpowers x, c ≠ 1 → ∀ k : K,
      (c : G) * k * (c : G)⁻¹ = k → k = 1) :
    8 ≤ fixedCodim ρ (zpowers x) := by
  apply eight_le_fixedCodim_of_five_normalizes_eleven ρ hρ x hx K hK
    (hnorm (mem_zpowers x))
  apply hfree ⟨x, mem_zpowers x⟩
  intro h
  have hx1 : x = 1 := congrArg Subtype.val h
  simp [hx1] at hx

end Representation.BinaryOffender
