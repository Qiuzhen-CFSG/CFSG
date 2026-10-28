module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.PolynomialSums
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Scalars

/-!
# The top monomial on the twisted D4 scalar grid

The three nontrivial triality orbits have parameters t, t^q, t^(q²), and the
three fixed roots have parameters in the q-element fixed field. Thus the
product of the twelve root coordinates to exponent q-1 becomes the product of
three (q³-1)-st powers and three (q-1)-st powers. Summing over the independent
parameters gives (-1)^6 = 1, including q = 2.

These are the actual fixed scalar tuples already used by the standard triality
construction. This theorem does not assert that the monomial extends to a
covariant regular function on the algebraic group. That section and the actual
cell parametrization must still be constructed before using the sum for
extremal interpolation.

Source context: Steinberg, `Chapter2St2.tex`, 11.8, 13.2(d) and 13.3(a).
-/

@[expose] public noncomputable section
open scoped BigOperators Classical
open MvPolynomial Triality.Standard Triality.Standard.PositiveCoordinates
open Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.PolynomialSums

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.TwistedSums
variable {k : Type*} [Field k]

/-- The distinguished monomial in the twelve ordered root coordinates. -/
def rootTopMonomial (q : ℕ) : MvPolynomial (Fin 12) k :=
  ∏ i : Fin 12, X i ^ (q - 1)

private theorem orbit_power (q : ℕ) (hq : 1 ≤ q) (x : k) :
    x ^ (q - 1) * (x ^ q) ^ (q - 1) * ((x ^ q) ^ q) ^ (q - 1) =
      x ^ (q ^ 3 - 1) := by
  simp only [← pow_mul, ← pow_add]
  congr 1
  have hq' : q - 1 + 1 = q := Nat.sub_add_cancel hq
  have hq3 : 1 ≤ q ^ 3 := one_le_pow₀ hq
  have hq3' := Nat.sub_add_cancel hq3
  nlinarith

/-- Restricting to the graph-field tuples collects each cubic orbit. -/
theorem rootTopMonomial_expand (P : Parameters) (ι : ExtensionField P →+* k)
    (a : OrbitParameters P) :
    eval (fun i => ι (expand P a i)) (rootTopMonomial P.q) =
      (∏ j : Fin 3, (ι (a.1 j)) ^ (P.q ^ 3 - 1)) *
        ∏ j : Fin 3, (ι (a.2 j)) ^ (P.q - 1) := by
  simp only [rootTopMonomial, map_prod, map_pow, eval_X]
  have h := orbit_power (k := k) P.q (by have := P.q_ge_two; omega)
  rw [Fin.prod_univ_three, Fin.prod_univ_three]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, expand,
    Matrix.cons_val_zero, Matrix.cons_val_succ, fieldFrobenius_apply, map_pow]
  simp_rw [← h]
  ring

private theorem sum_three_powers {F : Type*} [Field F] [Fintype F] (ι : F →+* k) :
    (∑ x : Fin 3 → F, ∏ i : Fin 3, (ι (x i)) ^ (Fintype.card F - 1)) = -1 := by
  rw [← Fintype.prod_sum (fun (_ : Fin 3) (t : F) => (ι t) ^ (Fintype.card F - 1))]
  have h (i : Fin 3) := mapped_sum_power (fun _ : Fin 3 => F) (fun _ => ι) i
  simp only [h 0, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

/-- The actual twisted scalar grid has top-monomial sum one. -/
theorem rootTopMonomial_sum (P : Parameters) (ι : ExtensionField P →+* k) :
    (∑ᶠ a : FixedCoordinates P,
      eval (fun i => ι (a.val i)) (rootTopMonomial P.q)) = 1 := by
  classical
  let := Fintype.ofFinite (ExtensionField P)
  let := Fintype.ofFinite (fixedField P)
  let := Fintype.ofFinite (FixedCoordinates P)
  have hE : (∑ x : Fin 3 → ExtensionField P,
      ∏ i : Fin 3, (ι (x i)) ^ (P.q ^ 3 - 1)) = -1 := by
    rw [← card_extensionField P, Nat.card_eq_fintype_card]
    exact sum_three_powers ι
  have hF : (∑ x : Fin 3 → fixedField P,
      ∏ i : Fin 3, (ι (x i)) ^ (P.q - 1)) = -1 := by
    rw [← card_fixedField P, Nat.card_eq_fintype_card]
    exact sum_three_powers (ι.comp (fixedField P).subtype)
  rw [finsum_eq_sum_of_fintype, ← (fixedCoordinatesEquiv P).sum_comp]
  change (∑ a : OrbitParameters P,
    eval (fun i => ι (expand P a i)) (rootTopMonomial P.q)) = 1
  simp only [rootTopMonomial_expand, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [hF, ← Finset.sum_mul, hE]
  ring

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.TwistedSums
