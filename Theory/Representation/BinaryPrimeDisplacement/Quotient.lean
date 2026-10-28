module

public import Theory.Representation.BinaryPrimeDisplacement
public import Theory.Representation.BinaryOffender.RestrictionComparison

/-!
# Prime displacement detected in a quotient action

If the image of an element under a group homomorphism has odd prime order p,
its cyclic subgroup upstairs contains an element of order p. The latter moves
at least ord_p(2) dimensions in every faithful binary representation, and its
fixed space contains that of the original element. No condition on the kernel
of the homomorphism is required.

This is the central-cover-safe form of the prime displacement argument used
for J₁ in Aschbacher–Smith K.4, printed p.457. The underlying prime degree
bound is G.7.1(1), printed p.347.
-/

public section
namespace Representation.BinaryOffender
open Subgroup

/-- An odd prime visible in any homomorphic image bounds displacement upstairs. -/
theorem prime_order_image_le_fixedCodim
    {G H V : Type*} [Group G] [Group H] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (f : G →* H) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (x : G) (hx : orderOf (f x) = p) :
    orderOf (2 : ZMod p) ≤ fixedCodim ρ (zpowers x) := by
  let : Fact p.Prime := ⟨hp⟩
  have hdiv : p ∣ Nat.card (zpowers x) := by
    rw [Nat.card_zpowers, ← hx]
    exact orderOf_map_dvd f x
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := zpowers x) p hdiv
  have hy' : orderOf (y : G) = p := by simpa only [Subgroup.orderOf_coe] using hy
  have hlo := prime_order_le_fixedCodim ρ hf hp hp2 (y : G) hy'
  have hfix : fixedSpace ρ (zpowers x) ≤ fixedSpace ρ (zpowers (y : G)) :=
    fixedSpace_antitone ρ (zpowers_le.mpr y.property)
  have hd := Submodule.finrank_mono hfix
  have h₁ := fixedCodim_add_finrank ρ (zpowers x)
  have h₂ := fixedCodim_add_finrank ρ (zpowers (y : G))
  omega

end Representation.BinaryOffender
