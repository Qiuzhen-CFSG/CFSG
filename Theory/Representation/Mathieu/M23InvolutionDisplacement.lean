module
public import Theory.Mathieu.LargeInvolutionGeneration
public import Theory.Representation.BinaryOffender.ConjugateMovedDimension
public import Theory.Representation.BinaryPrimeDisplacement

/-!
# Four moved dimensions for a faithful binary M23 involution

Three conjugates of an involution generate the native group. An order23
actor moves at least eleven dimensions, all in the whole moved space,
so each generating involution moves at least four. Fixed layers and
reducible modules are retained.
-/

public section
open Subgroup
namespace Representation.MathieuSmall
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
open Sporadic.Mathieu BinaryOffender

/-- Every involution of a faithful binary M23 action moves at least four
 dimensions, without an irreducibility or fixed-space assumption. -/
theorem m23_involution_displacement_ge_four
    (ρ : Representation (ZMod 2) M23 V) (hf : Function.Injective ρ)
    (t : M23) (ht : orderOf t = 2) :
    4 ≤ Module.finrank (ZMod 2) (ρ t - LinearMap.id).range := by
  obtain ⟨c,hc⟩ := LargeInvolutionGeneration.m23_three_conjugates_generate t ht
  have hu := finrank_coinvariants_le_mul_displacement_of_conjugate_generation ρ t c hc
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := M23) 23
    (by rw [m23_order]; norm_num)
  have hl := prime_order_le_fixedCodim ρ hf (by decide : Nat.Prime 23) (by decide) x hx
  rw [BinaryPrimeDegree.orderOf_two_mod_twentyThree,
    fixedCodim_zpowers_eq_displacement_rank] at hl
  have hr : (ρ x - LinearMap.id).range ≤ Coinvariants.ker ρ := by
    rintro _ ⟨v,rfl⟩
    exact Representation.Coinvariants.sub_mem_ker (ρ := ρ) x v
  have hd := Submodule.finrank_mono hr
  omega

end Representation.MathieuSmall
