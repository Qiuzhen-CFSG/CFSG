module

public import Theory.Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue.Catalogue.RestrictedWords.Geometry
public import Theory.Representation.SU3.BinaryDefiningWords.UnitaryInterpolation.Grid
public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.OrbitSpan.PolynomialPairing

/-!
# Highest fixed lines and cyclic highest tensors for standard SU₃ words

Evaluation on the Hermitian upper grid is injective on the restricted flag
space. An upper-fixed vector therefore has constant coefficient polynomial
and lies on the highest line. The same evaluation, expressed through the
nondegenerate word pairing, proves that the transpose orbit of the seed spans.
The transpose matrices are proved to lie in the actual special unitary group.
The finite two-group criterion then gives simplicity of the literal words.

Sources: GLS III, 2.8.2, 2.8.6(a), 2.8.9 and 2.8.10(c), and
Guralnick--Malle, §3.1. Neither irreducibility nor an extension or classification
result is assumed in the interpolation argument.
Reused from `CFSG/Quasithin/ChapterK/Section01To04/RankOne/UnitaryRecognition/MinimalDegree/Catalogue/RestrictedWords/StandardGeometry.lean`, with the original
proofs retained in a reusable Theory namespace for Fong--Seitz I (4D).
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix BenderSuzuki.MatrixGroups BenderSuzuki.External Representation
open scoped MatrixGroups
open Representation.SL3.BinaryDefiningFactors
open Representation.SL3.BinaryDefiningFactors.TensorSimplicity
open Matrix.PSL3Even.UnipotentGeometry
open FixedLine
namespace Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue.RestrictedWords
variable {F K : Type*} [Field F] [Field K]

/-- The transpose of the literal upper matrix is special unitary for the
antidiagonal Hermitian form. -/
def lowerUnitary (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) (z : hermitianUnipotentCoord J) :
    J.specialSubgroup :=
  ⟨SpecialLinearGroup.toGL (specialLinear F (upperCoordinates J z)).transpose, by
    apply (J.mem_specialSubgroup_iff _).mpr
    constructor
    · change J.conjTranspose (matrix F (upperCoordinates J z)).transpose * J.form *
        (matrix F (upperCoordinates J z)).transpose = J.form
      rw [hJ]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [HermitianForm.conjTranspose, matrix, upperCoordinates,
          Matrix.mul_apply, Fin.sum_univ_three]
      all_goals try rw [J.conj_involutive z.val.1, neg_add_cancel]
      linear_combination z.property
    · apply Units.ext
      change (matrix F (upperCoordinates J z)).transpose.det = 1
      rw [Matrix.det_transpose]
      exact (specialLinear F (upperCoordinates J z)).property⟩

/-- The actual special-linear image of the opposite element is exactly the
transpose appearing in the polynomial pairing identity. -/
theorem lower_inclusion (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) (z : hermitianUnipotentCoord J) :
    specialLinearInclusion J (lowerUnitary J hJ z) =
      (specialLinear F (upperCoordinates J z)).transpose := by
  apply Subtype.ext
  rfl

section
variable [Finite F] [CharP K 2]

/-- A restricted word coefficient vanishing on the unitary upper group is zero. -/
theorem wordPolynomial_eq_zero_of_unitary_eval (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (s : ℕ) (hs : 0 < s) (hcard : Nat.card F = (2^s)^2)
    (hconj : ∀ x, J.conj x = x^(2^s)) (ι : F →+* K)
    (w : List Factor) (hw : w.length = s) (v : WordSpace K w)
    (hv : ∀ z : hermitianUnipotentCoord J,
      MvPolynomial.eval (point ι (upperCoordinates J z)) (wordPolynomial K w v) = 0) :
    wordPolynomial K w v = 0 := by
  let : CharP F 2 := ι.charP ι.injective 2
  have hweight : (wordWeight w).1 < 2^s ∧ (wordWeight w).2 < 2^s := by
    simpa only [hw] using wordWeight_lt w
  exact SU3.BinaryDefiningWords.UnitaryInterpolation.eq_zero_of_eval_eq_zero J hJ
    s hs hcard hconj ι _ _ hweight.1 hweight.2 _ (wordPolynomial_mem_flagSpace K w v) hv

/-- Every upper-unitary fixed vector belongs to the concrete highest-tensor line. -/
theorem word_fixed_mem_span_standard (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (s : ℕ) (hs : 2 ≤ s) (hcard : Nat.card F = (2^s)^2)
    (hconj : ∀ x, J.conj x = x^(2^s)) (ι : F →+* K)
    (w : List Factor) (hw : w.length = s) (v : WordSpace K w)
    (hv : ∀ z : hermitianUnipotentCoord J,
      word J ι w (hermitianUnipotentSU J hJ z) v = v) :
    v ∈ Submodule.span K {wordSeed K w} := by
  let c := MvPolynomial.eval (0 : Fin 3 → K) (wordPolynomial K w v)
  have he : wordPolynomial K w (v - c • wordSeed K w) = 0 := by
    apply wordPolynomial_eq_zero_of_unitary_eval J hJ s (by omega) hcard hconj ι w hw
    intro z
    rw [map_sub, map_smul, wordPolynomial_seed, map_sub, MvPolynomial.smul_eval,
      map_one, mul_one, wordPolynomial_eval, ← upper_inclusion J hJ]
    change MvPolynomial.eval (0 : Fin 3 → K)
      (wordPolynomial K w (word J ι w (hermitianUnipotentSU J hJ z) v)) - c = 0
    rw [hv z]
    exact sub_self c
  have hz : v - c • wordSeed K w = 0 :=
    wordPolynomial_injective K w (he.trans (map_zero _).symm)
  exact Submodule.mem_span_singleton.mpr ⟨c, (sub_eq_zero.mp hz).symm⟩

/-- Exact equality of the upper fixed space and the seed line. -/
theorem word_fixed_iff_mem_span_standard (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (s : ℕ) (hs : 2 ≤ s) (hcard : Nat.card F = (2^s)^2)
    (hconj : ∀ x, J.conj x = x^(2^s)) (ι : F →+* K)
    (w : List Factor) (hw : w.length = s) (v : WordSpace K w) :
    (∀ z : hermitianUnipotentCoord J,
      word J ι w (hermitianUnipotentSU J hJ z) v = v) ↔
      v ∈ Submodule.span K {wordSeed K w} := by
  refine ⟨word_fixed_mem_span_standard J hJ s hs hcard hconj ι w hw v, ?_⟩
  intro hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  intro z
  rw [map_smul, word_seed_fixed]

private theorem wordPairing_injective_standard (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (s : ℕ) (hs : 0 < s) (hcard : Nat.card F = (2^s)^2)
    (hconj : ∀ x, J.conj x = x^(2^s)) (ι : F →+* K)
    (w : List Factor) (hw : w.length = s) :
    Function.Injective (wordPairing K w) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  apply wordPolynomial_injective K w
  rw [map_zero]
  apply wordPolynomial_eq_zero_of_unitary_eval J hJ s hs hcard hconj ι w hw
  intro z
  rw [wordPolynomial_eval_pairing, hv]
  rfl

/-- The actual lower-unitary orbit already spans the word carrier. -/
theorem wordSeed_lower_span_standard (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (s : ℕ) (hs : 2 ≤ s) (hcard : Nat.card F = (2^s)^2)
    (hconj : ∀ x, J.conj x = x^(2^s)) (ι : F →+* K)
    (w : List Factor) (hw : w.length = s) :
    Submodule.span K (Set.range fun z : hermitianUnipotentCoord J =>
      word J ι w (lowerUnitary J hJ z) (wordSeed K w)) = ⊤ := by
  apply Submodule.dualAnnihilator_eq_bot_iff.mp
  apply bot_unique
  intro f hf
  have hsurj : Function.Surjective (wordPairing K w) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      Subspace.dual_finrank_eq.symm).mp
        (wordPairing_injective_standard J hJ s (by omega) hcard hconj ι w hw)
  obtain ⟨v, rfl⟩ := hsurj f
  have hv : v = 0 := by
    apply wordPolynomial_injective K w
    rw [map_zero]
    apply wordPolynomial_eq_zero_of_unitary_eval J hJ s (by omega) hcard hconj ι w hw
    intro z
    rw [wordPolynomial_eval_pairing, ← lower_inclusion J hJ]
    exact (Submodule.mem_dualAnnihilator _).mp hf _ (Submodule.subset_span ⟨z, rfl⟩)
  simp [hv]

/-- The full special-unitary orbit of the concrete highest tensor spans the word. -/
theorem wordSeed_orbit_span_standard (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (s : ℕ) (hs : 2 ≤ s) (hcard : Nat.card F = (2^s)^2)
    (hconj : ∀ x, J.conj x = x^(2^s)) (ι : F →+* K)
    (w : List Factor) (hw : w.length = s) :
    Submodule.span K (Set.range fun g : J.specialSubgroup =>
      word J ι w g (wordSeed K w)) = ⊤ := by
  apply top_unique
  rw [← wordSeed_lower_span_standard J hJ s hs hcard hconj ι w hw]
  apply Submodule.span_mono
  rintro _ ⟨z, rfl⟩
  exact ⟨lowerUnitary J hJ z, rfl⟩

/-- Every source-restricted standard-form word is irreducible, by the proved
fixed-line and spanning results for its literal unitary action. -/
theorem word_isIrreducible_standard (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (s : ℕ) (hs : 2 ≤ s) (hcard : Nat.card F = (2^s)^2)
    (hconj : ∀ x, J.conj x = x^(2^s)) (ι : F →+* K)
    (w : List Factor) (hw : w.length = s) : IsIrreducible (word J ι w) := by
  let : CharP F 2 := ι.charP ι.injective 2
  exact word_isIrreducible_of_fixedLine_and_span J hJ ι w
    (word_fixed_mem_span_standard J hJ s hs hcard hconj ι w hw)
    (wordSeed_orbit_span_standard J hJ s hs hcard hconj ι w hw)

end
end Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue.RestrictedWords
