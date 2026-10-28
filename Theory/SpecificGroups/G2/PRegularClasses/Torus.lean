module

public import Theory.SpecificGroups.G2.PRegularClasses.FieldExtension
public import Theory.AtlasPort.LinearGroups.G2.Torus

/-!
# The characteristic polynomial of the actual G₂ split torus

The six nonconstant octonion weights partition into two reciprocal triples,
each of product one. Their cubic polynomials have their two middle
coefficients interchanged. Multiplying them and the two fixed-coordinate
factors yields `classPolynomial`, with only two free coefficients in
characteristic two. This proves the polynomial identity for torus elements
and their G₂ conjugates, without a semisimple-conjugacy assumption.

Source context: GLS III, 2.8.2 and the G₂ application in Aschbacher--Smith,
G.9.3, printed pp.356--357. The actual weights are from the licensed
`Theory.AtlasPort.LinearGroups.G2.Torus` (see `LICENSES/ATLAS.txt`).
-/

@[expose] public section

namespace Atlas.G2.PRegularClasses

open Polynomial

variable {F : Type*} [Field F]

/-- The sum of one product-one triple of octonion torus weights. -/
def torusA (l m : Fˣ) : F := ↑l + ↑(l⁻¹ * m) + ↑m⁻¹

/-- The sum of the reciprocal triple. -/
def torusB (l m : Fˣ) : F := ↑m + ↑(l * m⁻¹) + ↑l⁻¹

private theorem triple_product (l m : Fˣ) :
    (X + C (l : F)) * (X + C (↑(l⁻¹ * m) : F)) * (X + C (↑m⁻¹ : F)) =
      X ^ 3 + C (torusA l m) * X ^ 2 + C (torusB l m) * X + 1 := by
  have hprod : (l : F) * (↑(l⁻¹ * m) : F) * (↑m⁻¹ : F) = 1 := by simp
  have hpair : (l : F) * (↑(l⁻¹ * m) : F) + (l : F) * (↑m⁻¹ : F) +
      (↑(l⁻¹ * m) : F) * (↑m⁻¹ : F) = torusB l m := by
    simp [torusB]
  calc
    _ = X ^ 3 + C ((l : F) + ↑(l⁻¹ * m) + ↑m⁻¹) * X ^ 2 +
        C ((l : F) * ↑(l⁻¹ * m) + (l : F) * ↑m⁻¹ + (↑(l⁻¹ * m) : F) * ↑m⁻¹) * X +
        C ((l : F) * (↑(l⁻¹ * m) : F) * (↑m⁻¹ : F)) := by
          simp only [C_add, C_mul]
          ring
    _ = _ := by rw [hprod, hpair, C_1]; rfl

private theorem cubic_pair [CharP F 2] (a b : F) :
    (X + 1) ^ 2 * (X ^ 3 + C a * X ^ 2 + C b * X + 1) *
      (X ^ 3 + C b * X ^ 2 + C a * X + 1) =
      classPolynomial (a + b) (a * b + a + b + 1) := by
  simp only [classPolynomial, C_add, C_mul, C_pow, C_1]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

theorem charpoly_torus_product (l m : Fˣ) :
    charpoly (torus l m) = ∏ i : Fin 8, (X - C (torusWeights l m i : F)) := by
  rw [charpoly_eq_matrix]
  have hm : LinearMap.toMatrix (Pi.basisFun F (Fin 8)) (Pi.basisFun F (Fin 8))
      (action (torus l m)) = Matrix.diagonal (fun i => (torusWeights l m i : F)) := by
    ext i j
    simp [action, torus, torusEquiv, torusLinear, Matrix.diagonal, Pi.single_apply]
  rw [hm, Matrix.charpoly_diagonal]

/-- Explicit polynomial formula for the literal octonion torus action. -/
theorem charpoly_torus [CharP F 2] (l m : Fˣ) :
    charpoly (torus l m) = classPolynomial (torusA l m + torusB l m)
      (torusA l m * torusB l m + torusA l m + torusB l m + 1) := by
  rw [charpoly_torus_product]
  have hA : torusA m l = torusB l m := by simp [torusA, torusB, mul_comm]
  have hB : torusB m l = torusA l m := by simp [torusA, torusB, mul_comm]
  calc
    _ = (X + 1) ^ 2 *
        ((X + C (l : F)) * (X + C (↑(l⁻¹ * m) : F)) * (X + C (↑m⁻¹ : F))) *
        ((X + C (m : F)) * (X + C (↑(m⁻¹ * l) : F)) * (X + C (↑l⁻¹ : F))) := by
      simp only [Fin.prod_univ_succ, torusWeights, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Matrix.cons_val_fin_one, Fin.prod_univ_zero,
        mul_one, Units.val_one, CharTwo.sub_eq_add]
      rw [mul_comm m⁻¹ l]
      simp only [C_1, pow_two]
      ac_rfl
    _ = _ := by rw [triple_product, triple_product, hA, hB, cubic_pair]

/-- The two characteristic-polynomial coefficients determine every conjugate
of a split-torus element. -/
theorem charpoly_eq_classPolynomial_of_isConj_torus [CharP F 2]
    (g : Model F) (l m : Fˣ) (hc : IsConj g (torus l m)) :
    charpoly g = classPolynomial ((charpoly g).coeff 7) ((charpoly g).coeff 6) := by
  rw [charpoly_eq_of_isConj g (torus l m) hc, charpoly_torus]
  rw [classPolynomial_coeff_seven, classPolynomial_coeff_six]

/-- Actual G₂-conjugacy into a split torus over an extension already suffices
for the two-parameter polynomial identity over the original field. -/
theorem charpoly_eq_classPolynomial_of_extension_torus
    {K : Type*} [Field K] [CharP K 2] (f : F →+* K)
    (g : Model F) (l m : Kˣ)
    (hc : IsConj (FieldExtension.fieldEmbedding f g) (torus l m)) :
    charpoly g = classPolynomial ((charpoly g).coeff 7) ((charpoly g).coeff 6) := by
  apply eq_classPolynomial_of_map_eq f (charpoly g)
    (torusA l m + torusB l m) (torusA l m * torusB l m + torusA l m + torusB l m + 1)
  rw [← FieldExtension.fieldEmbedding_charpoly,
    charpoly_eq_of_isConj _ _ hc, charpoly_torus]

/-- A torus-normal-form theorem over an extension yields the polynomial shape
for every odd-order element over the original field. -/
theorem charpoly_eq_classPolynomial_of_torus_conjugacy
    {K : Type*} [Field K] [CharP K 2] (f : F →+* K)
    (hgeom : ∀ x : Model K, ¬ 2 ∣ orderOf x → ∃ l m : Kˣ, IsConj x (torus l m))
    (g : Model F) (hg : ¬ 2 ∣ orderOf g) :
    charpoly g = classPolynomial ((charpoly g).coeff 7) ((charpoly g).coeff 6) := by
  obtain ⟨l, m, hc⟩ := hgeom (FieldExtension.fieldEmbedding f g)
    (by simpa only [FieldExtension.fieldEmbedding_orderOf] using hg)
  exact charpoly_eq_classPolynomial_of_extension_torus f g l m hc

end Atlas.G2.PRegularClasses
