module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.AmbientConditions
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Data
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.Quadratic
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.ExteriorAnnihilators.Arithmetic
/-!
# Arithmetic for the concrete restriction certificates

Packed multiplication and logarithmic parity evaluate ordinary matrix products
and linear functionals. Transport moves the functionals to the original full
exterior space, so annihilation checks cover all source generators.

Source: KernelBound/source/README.md. The binary arithmetic interfaces reused
here were proved for the same ATLAS representation.
-/

@[expose] public section
open Matrix
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
open Coordinates GeneratorCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
open PolynomialCertificate.ExteriorAnnihilators PolynomialCertificate.PullbackCoefficients ExteriorInvariance

def halfRows (x : ℕ) : Vector ℕ 56 :=
  Vector.ofFn (fun i => (x >>> (56*i.val)) % 2^56)

theorem halfRows_spec (x : ℕ) : rowsMatrix (halfRows x) = decodeHalf x := by
  funext i j
  simp only [rowsMatrix, halfRows, get_ofFn, decodeHalf, bit, Nat.testBit_mod_two_pow,
    j.isLt, decide_true, Bool.true_and, Nat.testBit_shiftRight]

theorem rows_product_eq {m n k : ℕ} (a : Vector ℕ m) (b : Vector ℕ n)
    (c : Vector ℕ m) (h : ∀ i, rowProduct (a.get i) b = c.get i) :
    rowsMatrix (n := n) a * rowsMatrix (n := k) b = rowsMatrix c := by
  rw [← rowsMatrix_product]
  congr 1
  apply Vector.ext
  intro i hi
  change (rowsProduct a b).get ⟨i, hi⟩ = c.get ⟨i, hi⟩
  rw [rowsProduct, get_ofFn, h]

def halfDot (x y : ℕ) : ZMod 2 := bit (parity 12 ((x &&& y) % 2^3136)) 0

theorem halfDot_spec (x y : ℕ) : halfDot x y = pairing (decodeHalf x) (decodeHalf y) := by
  rw [halfDot, bit_parity]
  simp only [Nat.zero_add]
  change (∑ i ∈ Finset.range (3136+960), bit ((x &&& y) % 2^3136) i) = _
  rw [Finset.sum_range_add]
  have hz : (∑ i ∈ Finset.range 960, bit ((x &&& y) % 2^3136) (3136+i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp only [bit, Nat.testBit_mod_two_pow, show ¬3136+i < 3136 by omega,
      decide_false, Bool.false_and, Bool.false_eq_true, if_false]
  rw [hz, add_zero, ← Fin.sum_univ_eq_sum_range]
  have he := (finProdFinEquiv (m := 56) (n := 56)).sum_comp
    (fun i => bit ((x &&& y) % 2^3136) i.val)
  rw [← he, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro z _
  change bit ((x &&& y) % 2^3136) (z.val+56*i.val) = _
  have hb : z.val+56*i.val < 3136 := by omega
  rw [show bit ((x &&& y) % 2^3136) (z.val+56*i.val) = bit (x &&& y) (z.val+56*i.val) by
    simp only [bit, Nat.testBit_mod_two_pow, hb, decide_true, Bool.true_and], bit_and]
  simp only [decodeHalf, Nat.add_comm]

def functional (w : ℕ) : HalfMatrix →ₗ[ZMod 2] ZMod 2 where
  toFun R := pairing (decodeHalf w) R
  map_add' R S := by simp [pairing, mul_add, Finset.sum_add_distrib]
  map_smul' a R := by simp [pairing, Finset.mul_sum, mul_left_comm]

theorem functional_decode (w x : ℕ) : functional w (decodeHalf x) = halfDot w x :=
  (halfDot_spec w x).symm

def embedding : Matrix (Fin 112) (Fin 56) (ZMod 2) :=
  fun i j => adaptedBasis i (Fin.castAdd 56 j)

set_option maxRecDepth 10000 in
theorem restriction_eq (F : BinaryMatrix) :
    upperBlockLinear (formCoordinatesLinear F) = embeddingᵀ * F * embedding := by
  rfl

theorem functional_transport (w : ℕ) (F : BinaryMatrix) :
    functional w (upperBlockLinear (formCoordinatesLinear F)) =
      pairing (embedding * decodeHalf w * embeddingᵀ) F := by
  change pairing (decodeHalf w) (upperBlockLinear (formCoordinatesLinear F)) = _
  rw [restriction_eq, pairing_mul_right, transpose_transpose, pairing_mul_left, Matrix.mul_assoc]

theorem functional_restriction_zero (w : ℕ)
    (h : ∀ i : Fin 1221, functional w (upperBlockLinear (formCoordinatesLinear (exteriorBasisForm i))) = 0)
    {R : HalfMatrix} (hR : R ∈ restrictionSpace) : functional w R = 0 := by
  rcases hR with ⟨F, ⟨A, hA, rfl⟩, rfl⟩
  have hz : exteriorFormSpace ≤ (functional w ∘ₗ upperBlockLinear ∘ₗ formCoordinatesLinear).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact h i
  exact hz hA


theorem functional_restriction_zero_of_dual (w d : ℕ)
    (ht : flatMatrix d = embedding * decodeHalf w * embeddingᵀ)
    (hd : ∀ i : Fin 1221, flatDot d (basisFlat i.val) = false)
    {R : HalfMatrix} (hR : R ∈ restrictionSpace) : functional w R = 0 := by
  apply functional_restriction_zero w _ hR
  intro i
  rw [functional_transport, ← ht, ← basis_decode i, ← flatDot_spec, hd]
  rfl

theorem decodeHalf_xor (x y : ℕ) : decodeHalf (x ^^^ y) = decodeHalf x + decodeHalf y := by
  funext i j
  exact bit_xor x y _

theorem decodeHalf_xorList (xs : List ℕ) :
    decodeHalf (xorList xs) = (xs.map decodeHalf).sum := by
  induction xs with
  | nil =>
    ext i j
    simp [xorList, decodeHalf, bit]
  | cons x xs ih => simp only [xorList, decodeHalf_xor, List.map_cons, List.sum_cons, ih]

theorem functional_quadratic_zero (w : ℕ)
    (hd : ∀ i, functional w (quadraticTerm testForm (squareBasis i)) = 0)
    (hp : ∀ i j, functional w (polarTerm testForm (squareBasis i) (squareBasis j)) = 0)
    {R : HalfMatrix} (hR : R ∈ quadraticSpan testForm squareBasis) : functional w R = 0 := by
  have hz : quadraticSpan testForm squareBasis ≤ (functional w).ker := by
    apply Submodule.span_le.mpr
    rintro _ (⟨i, rfl⟩ | ⟨⟨i,j⟩, rfl⟩)
    · exact hd i
    · exact hp i j
  exact hz hR

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity.SeparationCertificate
