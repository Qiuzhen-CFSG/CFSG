module
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.MinimalDegree.Catalogue.RestrictedWords.Geometry
public import Theory.Representation.SU3.BinaryDefiningWords.WeightSeparation.Arithmetic
/-!
# The highest tensor under the literal unitary torus

Huppert's torus is diagonal with entries conj(k)⁻¹, conj(k)/k, k.
Thus the natural seed e₀ has eigenvalue k⁻q and the dual seed e₂* has
eigenvalue k⁻¹; conjugation on the trace-zero matrix unit E₀₂ multiplies
these eigenvalues. Induction through the actual Frobenius-twisted tensor
representation gives k⁻(qA+B), with (A,B) the existing binary word weight.

Sources: Huppert II.10.12 and GLS III, 2.8.6(a), 2.8.10(c).
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix BenderSuzuki.MatrixGroups BenderSuzuki.External Representation
open scoped MatrixGroups TensorProduct
open Representation.SL3.BinaryDefiningFactors
open Representation.SL3.BinaryDefiningFactors.TensorSimplicity
open Representation.SL3.BinaryDefiningFactors.TensorSimplicity.FixedLine
open Representation.SU3.BinaryDefiningWords.WeightSeparation
namespace CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.MinimalDegree.RestrictedWords.TorusSeparation
variable {F K : Type*} [Field F] [Field K]

private theorem natural_torus_apply (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) (ι : F →+* K) (k : Fˣ) (v : Fin 3 → K) :
    Representation.SL3.BinaryDefiningFactors.natural ι
      (specialLinearInclusion J (hermitianTorusSU J hJ k)) v =
    ![ι (J.conj (k : F))⁻¹ * v 0,
      ι (J.conj (k : F) * (k : F)⁻¹) * v 1, ι (k : F) * v 2] := by
  change (hermitianTorusMatrix J k).map ι *ᵥ v = _
  ext i
  fin_cases i <;> simp [hermitianTorusMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private theorem natural_torus_seed (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) (ι : F →+* K)
    (q : ℕ) (hconj : ∀ x, J.conj x = x ^ q) (k : Fˣ) :
    Representation.SL3.BinaryDefiningFactors.natural ι
      (specialLinearInclusion J (hermitianTorusSU J hJ k)) (Pi.single 0 1) =
    (ι (k : F)⁻¹) ^ q • (Pi.single 0 1) := by
  rw [natural_torus_apply]
  ext i
  fin_cases i <;> simp [hconj, map_pow, map_inv₀, inv_pow]

private theorem natural_torus_inv_last (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) (ι : F →+* K)
    (k : Fˣ) (v : Fin 3 → K) :
    (Representation.SL3.BinaryDefiningFactors.natural ι
      (specialLinearInclusion J (hermitianTorusSU J hJ k))⁻¹ v) 2 =
    ι (k : F)⁻¹ * v 2 := by
  rw [← map_inv, ← map_inv, natural_torus_apply]
  simp

/-- The four actual factors have inverse torus exponents 0, q, 1, q+1. -/
theorem factorSeed_torus (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) (ι : F →+* K)
    (q : ℕ) (hconj : ∀ x, J.conj x = x ^ q) (k : Fˣ) (a : Factor) :
    factorRep ι a (specialLinearInclusion J (hermitianTorusSU J hJ k)) (factorSeed K a) =
      (ι (k : F)⁻¹) ^ exponent q [a] • factorSeed K a := by
  cases a with
  | trivial =>
    change (1 : K) = (ι (k : F)⁻¹) ^ exponent q [.trivial] • (1 : K)
    simp [exponent, wordWeight]
  | natural =>
    change Representation.SL3.BinaryDefiningFactors.natural ι
      (specialLinearInclusion J (hermitianTorusSU J hJ k)) (Pi.single 0 1) =
      (ι (k : F)⁻¹) ^ exponent q [.natural] • (Pi.single 0 1 : Fin 3 → K)
    simpa [exponent, wordWeight] using natural_torus_seed J hJ ι q hconj k
  | dual =>
    apply LinearMap.ext
    intro v
    change (Representation.SL3.BinaryDefiningFactors.natural ι
      (specialLinearInclusion J (hermitianTorusSU J hJ k))⁻¹ v) 2 =
      ((ι (k : F)⁻¹) ^ exponent q [.dual]) * v 2
    rw [natural_torus_inv_last]
    simp [exponent, wordWeight]
  | adjoint =>
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    change Representation.SL3.BinaryDefiningFactors.natural ι
      (specialLinearInclusion J (hermitianTorusSU J hJ k))
      ((Representation.SL3.BinaryDefiningFactors.natural ι
        (specialLinearInclusion J (hermitianTorusSU J hJ k))⁻¹ v) 2 • Pi.single 0 1) =
      ((ι (k : F)⁻¹) ^ exponent q [.adjoint]) • (v 2 • Pi.single 0 1)
    rw [map_smul, natural_torus_seed J hJ ι q hconj, natural_torus_inv_last]
    simp only [exponent, wordWeight, reduceCtorEq, or_true, ite_true, mul_zero,
      add_zero, mul_one, pow_succ, smul_smul]
    congr 1
    ring

/-- The recursive highest tensor has the literal unitary torus weight -(qA+B). -/
theorem wordSeed_torus [CharP K 2] (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) (ι : F →+* K)
    (q : ℕ) (hconj : ∀ x, J.conj x = x ^ q) (k : Fˣ) (w : List Factor) :
    word J ι w (hermitianTorusSU J hJ k) (wordSeed K w) =
      (ι (k : F)⁻¹) ^ exponent q w • wordSeed K w := by
  induction w generalizing ι with
  | nil =>
    change (1 : K) = (ι (k : F)⁻¹) ^ exponent q [] • (1 : K)
    simp [exponent, wordWeight]
  | cons a w ih =>
    change factorRep ι a (specialLinearInclusion J (hermitianTorusSU J hJ k))
        (factorSeed K a) ⊗ₜ[K]
      word J ((frobenius K 2).comp ι) w (hermitianTorusSU J hJ k) (wordSeed K w) =
      (ι (k : F)⁻¹) ^ exponent q (a :: w) • (factorSeed K a ⊗ₜ[K] wordSeed K w)
    rw [factorSeed_torus J hJ ι q hconj, ih]
    simp only [RingHom.comp_apply, frobenius_def,
      TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul]
    rw [← pow_mul, ← pow_add]
    congr 2
    cases a <;> simp [exponent, wordWeight] <;> ring
end CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.MinimalDegree.RestrictedWords.TorusSeparation
