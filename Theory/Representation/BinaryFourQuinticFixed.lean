module
public import Theory.Representation.BinaryPrimeDisplacement

/-!
# Fixed vectors of binary four-dimensional quintic actions

A faithful element of order five moves at least four binary dimensions,
because two has multiplicative order four modulo five. In dimension four
its fixed space is therefore zero. The natural, dual and repeated-module
exclusions in Aschbacher--Smith 12.6.17 use this calculation.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem four_fixed_eq_zero_of_order_five (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    (x : G) (hx : orderOf x = 5) (v : V) (hv : ρ x v = v) : v = 0 := by
  have hl := prime_order_le_fixedCodim ρ hf (by decide : Nat.Prime 5) (by decide) x hx
  rw [BinaryPrimeDegree.orderOf_two_mod_five] at hl
  have he := fixedCodim_add_finrank ρ (zpowers x)
  rw [hd] at he
  have hz : fixedSpace ρ (zpowers x) = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
  have hvf : v ∈ fixedSpace ρ (zpowers x) := by
    rw [mem_fixedSpace_zpowers_iff]
    exact hv
  simpa only [hz, Submodule.mem_bot] using hvf
end Representation.BinaryOffender
