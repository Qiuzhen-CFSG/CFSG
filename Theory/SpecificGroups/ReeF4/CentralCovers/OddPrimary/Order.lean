module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Order.Bruhat
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Order.TorusCardinality
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Order.CellCardinalities

/-!
# Order of the actual Ree carrier

The proved restricted Bruhat bijection reduces exact counting to the fixed
torus and the weighted sum of inversion-subgroup sizes. The relative dihedral
root system has weights one and two; its polynomial factors as
`(q+1)(q^2+1)(q^3+1)(q^6+1)`. Combining this with `|T|=(q-1)^2`
gives the order formula in GLS3 Table 2.2.

The unconditional theorem `card_model` supplies both geometric counts from
their actual matrix parametrizations. It holds for every `m`, in particular
throughout the large Ree range `1 ≤ m`. The carrier is unchanged: `Model 0`
denotes the full binary fixed group, not the Tits simple group. No simplicity,
model comparison or multiplier theorem is used.

Source: GLS3 Table 2.2 and §§2.3–2.4, `refs/KGroup/GLS3/chapter2.tex`.
Our field size `q=2^(2*m+1)` is the square of GLS3's half-integer parameter.
-/

@[expose] public section
noncomputable section
local instance (m : ℕ) (H : Subgroup (ReeF4.Model m)) : Fintype H := Fintype.ofFinite _

namespace ReeF4.CentralCovers.OddPrimary.Order
open Parabolics Parabolics.Binary.FixedGeometry

/-- The weighted Poincaré polynomial of the relative dihedral root system. -/
def cellPolynomial (q : ℕ) : ℕ := (q + 1) * (q ^ 2 + 1) * (q ^ 3 + 1) * (q ^ 6 + 1)

private theorem order_polynomial (q : ℕ) (hq : 1 ≤ q) :
    q ^ 12 * (q - 1) ^ 2 * cellPolynomial q =
      q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show q ≠ 0 by omega)
  have h4 : (k + 1) ^ 4 - 1 = k ^ 4 + 4 * k ^ 3 + 6 * k ^ 2 + 4 * k := by
    apply Nat.sub_eq_of_eq_add
    ring
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, h4, cellPolynomial]
  ring

/-- Conditional order assembly. The torus count and the weighted counts of
actual inversion subgroups are independent geometric obligations. -/
theorem card_model_of_torus_and_cells (m : ℕ)
    (ht : Nat.card (fixedTorus m) = (2 ^ (2 * m + 1) - 1) ^ 2)
    (hc : ∑ w : weylSubgroup m, Nat.card (fixedRightUnipotent w.val) =
      cellPolynomial (2 ^ (2 * m + 1))) :
    Nat.card (Model m) = (2 ^ (2 * m + 1)) ^ 12 *
      ((2 ^ (2 * m + 1)) ^ 6 + 1) * ((2 ^ (2 * m + 1)) ^ 4 - 1) *
      ((2 ^ (2 * m + 1)) ^ 3 + 1) * (2 ^ (2 * m + 1) - 1) := by
  rw [card_model_torus_weyl_sum, ht, hc]
  exact order_polynomial _ (one_le_pow₀ (by decide))

/-- The exact order of the exceptional fixed matrix carrier, including every
large Ree group (`1 ≤ m`). At `m = 0` this counts the full binary Ree group,
not its Tits derived subgroup. Both geometric counting premises are discharged. -/
theorem card_model (m : ℕ) :
    Nat.card (Model m) = (2 ^ (2 * m + 1)) ^ 12 *
      ((2 ^ (2 * m + 1)) ^ 6 + 1) * ((2 ^ (2 * m + 1)) ^ 4 - 1) *
      ((2 ^ (2 * m + 1)) ^ 3 + 1) * (2 ^ (2 * m + 1) - 1) :=
  card_model_of_torus_and_cells m (card_fixedTorus m) (sum_card_fixedRightUnipotent m)

end ReeF4.CentralCovers.OddPrimary.Order
