module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.Projection.LinearAction.Data
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.Projection.Generators
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.NormalFour.Evaluation

/-!
# Checked max4 section identities

A right inverse proves independence of all 31 numerator rows. A second
coordinate map kills the first 28 rows and identifies the three lifts with the
standard basis. The two actual generator matrices preserve these coordinates,
with induced matrices `[5,6,4]` and `[7,5,3]`. Products are ordinary products,
without transposition or inversion. Every finite identity is kernel checked.

Source: ATLAS J4G1-max4W1 and J4G1-f2r112B0; see Projection/source/README.md.
These identities supply the linear factor used in Aschbacher–Smith 1.3.4,
printed p.511/PDF p.528.
-/

@[expose] public section
namespace Janko4.LocalStructure.SymmetricLinear.Projection.LinearSection
open Matrix GeneratorCertificates Simplicity.Elevens.BridgeCertificate
open NormalFour.Certificate
set_option maxRecDepth 10000

lemma basis_dual : basis * dual = 1 := by
  let identityRows : List ℕ := List.ofFn (fun i : Fin 31 => 2 ^ i.val)
  have h := product_lists (n := 31) (m := 112) (p := 31) basisRows dualRows identityRows rfl rfl
    (by simp [identityRows]) (by decide +kernel)
  refine h.trans ?_
  decide +kernel

lemma basis_coordinates : basis * coordinates = quotient :=
  product_lists basisRows coordinateRows quotientRows rfl rfl rfl (by decide +kernel)

lemma first_basis : firstAction * basis = basis * toMatrix (first : Model) := by
  rw [show toMatrix (first : Model) = m028 from image_g029]
  exact product_eq_lists firstRows basisRows basisRows l028 rfl rfl rfl rfl (by decide +kernel)

lemma second_basis : secondAction * basis = basis * toMatrix (second : Model) := by
  rw [show toMatrix (second : Model) = m025 from image_g026]
  exact product_eq_lists secondRows basisRows basisRows l025 rfl rfl rfl rfl (by decide +kernel)

lemma first_quotient : firstAction * quotient = quotient * (firstLinear : Matrix _ _ _) := by
  have h : (unpack (vectorRows [5, 6, 4] rfl) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (firstLinear : Matrix _ _ _) := by decide +kernel
  rw [← h]
  exact product_eq_lists firstRows quotientRows quotientRows [5, 6, 4]
    rfl rfl rfl rfl (by decide +kernel)

lemma second_quotient : secondAction * quotient = quotient * (secondLinear : Matrix _ _ _) := by
  have h : (unpack (vectorRows [7, 5, 3] rfl) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (secondLinear : Matrix _ _ _) := by decide +kernel
  rw [← h]
  exact product_eq_lists secondRows quotientRows quotientRows [7, 5, 3]
    rfl rfl rfl rfl (by decide +kernel)

def liftIndex (i : Fin 3) : Fin 31 := ⟨28 + i.val, by omega⟩

lemma quotient_lifts : quotient.submatrix liftIndex id = 1 := by decide +kernel

lemma quotient_denominator : ∀ (i : Fin 28) (j : Fin 3), quotient (i.castLE (by decide)) j = 0 := by
  decide +kernel

lemma coefficient_injective : Function.Injective (fun v : Fin 31 → ZMod 2 => v ᵥ* basis) := by
  intro v w h
  have hh := congrArg (fun x => x ᵥ* dual) h
  simpa only [Matrix.vecMul_vecMul, basis_dual, Matrix.vecMul_one] using hh

lemma quotient_mul_injective (s t : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (h : quotient * s = quotient * t) : s = t := by
  have hh := congrArg (fun x : Matrix (Fin 31) (Fin 3) (ZMod 2) =>
    x.submatrix liftIndex id) h
  simpa only [Matrix.submatrix_mul _ _ liftIndex id id Function.bijective_id,
    Matrix.submatrix_id_id, quotient_lifts, Matrix.one_mul] using hh

end Janko4.LocalStructure.SymmetricLinear.Projection.LinearSection
