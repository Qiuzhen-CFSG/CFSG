module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Quotient coordinates and the three-part of the order

An order-nine quotient whose exponent divides three is a two-dimensional
vector space over `ZMod 3`. Choosing a basis constructs its multiplicative
equivalence with `E₉`. An order-three two-core quotient also gives the exact
three-part of the original group's order, without discarding its two-core.

These are the arithmetic and coordinate steps for Aschbacher–Smith 15.3.12(2),
combined manuscript (1 March 2004), printed p.1125. The component argument
must still supply the quotient orders; these lemmas do not assume exponent
three for `Y₊` itself.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.ComponentIntersection
variable {G : Type*} [Group G] [Finite G]

/-- The standard elementary abelian group of order nine. -/
abbrev ElementaryNine := Multiplicative (Fin 2 → ZMod 3)

/-- Construct the actual `E₉` equivalence from quotient order and exponent. -/
theorem quotient_equiv_elementaryNine_of_card {Y : Subgroup G}
    (hc : Nat.card (TwoCoreQuotient Y) = 9)
    (he : Monoid.exponent (TwoCoreQuotient Y) ∣ 3) :
    Nonempty (TwoCoreQuotient Y ≃* ElementaryNine) := by
  classical
  let : IsMulCommutative (TwoCoreQuotient Y) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hc
  let : IsElementaryAbelian 3 (TwoCoreQuotient Y) :=
    { toIsMulCommutative := inferInstance, exponent_dvd_p := he }
  have hpow : 3 ^ Module.finrank (ZMod 3) (Additive (TwoCoreQuotient Y)) = 3 ^ 2 := by
    have hsize := Module.natCard_eq_pow_finrank
      (K := ZMod 3) (V := Additive (TwoCoreQuotient Y))
    change Nat.card (TwoCoreQuotient Y) = _ at hsize
    simpa [Nat.card_zmod, hc] using hsize.symm
  have hdim : Module.finrank (ZMod 3) (Additive (TwoCoreQuotient Y)) = 2 :=
    Nat.pow_right_injective (by decide : 1 < 3) hpow
  let e := (Module.finBasisOfFinrankEq (ZMod 3) (Additive (TwoCoreQuotient Y)) hdim).equivFun
  refine ⟨{
    toFun := fun x => Multiplicative.ofAdd (e (Additive.ofMul x))
    invFun := fun x => (e.symm x.toAdd).toMul
    left_inv := fun x => congrArg Additive.toMul (e.symm_apply_apply (Additive.ofMul x))
    right_inv := fun x => congrArg Multiplicative.ofAdd (e.apply_symm_apply x.toAdd)
    map_mul' := fun x y => congrArg Multiplicative.ofAdd (e.map_add (Additive.ofMul x) (Additive.ofMul y))
  }⟩

/-- A two-core quotient of order three has three-part exactly three. -/
theorem three_part_eq_three_of_quotient_card {Y : Subgroup G}
    (hc : Nat.card (TwoCoreQuotient Y) = 3) :
    3 ^ (Nat.card Y).factorization 3 = 3 := by
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := Y)).exists_card_eq
  have hi : (pCore 2 Y).index = 3 := hc
  rw [← (pCore 2 Y).card_mul_index, hi, hn]
  have htwo : (2 : ℕ) ^ n ≠ 0 := pow_ne_zero _ (by decide)
  simp [Nat.factorization_mul htwo (by decide : (3 : ℕ) ≠ 0),
    Nat.factorization_pow, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2),
    Nat.Prime.factorization_self Nat.prime_three]


end CFSG.Quasithin.Chapter15.Section03.ComponentIntersection

end
