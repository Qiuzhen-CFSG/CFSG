module

public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.HighestVector
public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.FixedLine.PolynomialModel
public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.FixedLine.TensorEmbedding
public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.FixedLine.FlagInterpolation

/-!
# The upper-fixed line in binary SL₃ tensor words

The concrete orbit coefficient is constant for an upper-fixed vector.
Injectivity of the tensor-to-polynomial map and of evaluation on the embedded
finite-field grid therefore put that vector on the actual highest-vector line.
For a word of length `n` over a field of order `2^n`, both binary highest
weights are below the field cardinality, so the proved interpolation and tensor
embedding theorems discharge those injectivity inputs. Conversely, the literal
upper subgroup fixes the seed and all its scalar multiples. Thus its fixed
space is exactly the seed line, including at `q=2` and for trivial or adjoint
factors. The coefficient field need only have characteristic two; algebraic
closure is unnecessary.

Source: GLS III, 2.8.6(a), 2.8.9 and 2.8.10(c). The source's Curtis theorem
assumes irreducibility and is not used to supply the missing tensor simplicity.
-/

public section
noncomputable section
namespace Representation.SL3.BinaryDefiningFactors.TensorSimplicity.FixedLine
open Matrix.PSL3Even.UnipotentGeometry
variable {K F : Type*} [Field K] [Field F] [CharP K 2]

/-- The two independent polynomial embeddings give the required fixed line.
Their injectivity hypotheses must be discharged before using this as an
unconditional fixed-line theorem. -/
theorem fixed_mem_span_of_polynomial_embeddings (ι : F →+* K) (w : List Factor)
    (a b : ℕ)
    (hpoly : Function.Injective (wordPolynomial K w))
    (hspace : ∀ v, wordPolynomial K w v ∈ flagSpace K a b)
    (hgrid : ∀ p ∈ flagSpace K a b,
      (∀ u : U F, MvPolynomial.eval (point ι u) p = 0) → p = 0)
    (v : WordSpace K w)
    (hv : ∀ u : U F, wordRep ι w (specialLinear F u) v = v) :
    v ∈ Submodule.span K {wordSeed K w} := by
  let c := MvPolynomial.eval (0 : Fin 3 → K) (wordPolynomial K w v)
  have he : wordPolynomial K w (v - c • wordSeed K w) = 0 := by
    apply hgrid _ (hspace _)
    intro u
    rw [map_sub, map_smul, wordPolynomial_seed, map_sub, MvPolynomial.smul_eval,
      map_one, mul_one, wordPolynomial_eval, hv u]
    exact sub_self c
  have hz : v - c • wordSeed K w = 0 := hpoly (he.trans (map_zero _).symm)
  exact Submodule.mem_span_singleton.mpr ⟨c, (sub_eq_zero.mp hz).symm⟩

/-- Every vector fixed by the literal upper-unitriangular subgroup lies on the
highest-vector line. This supplies the fixed-line premise for tensor simplicity
without assuming irreducibility. -/
theorem fixed_mem_span [Finite F] (ι : F →+* K) (n : ℕ)
    (hcard : Nat.card F = 2 ^ n) (w : List Factor) (hw : w.length = n)
    (v : WordSpace K w)
    (hv : ∀ u : U F, wordRep ι w (specialLinear F u) v = v) :
    v ∈ Submodule.span K {wordSeed K w} := by
  have hweight : (wordWeight w).1 < 2 ^ n ∧ (wordWeight w).2 < 2 ^ n := by
    simpa only [hw] using wordWeight_lt w
  exact fixed_mem_span_of_polynomial_embeddings ι w (wordWeight w).1 (wordWeight w).2
    (wordPolynomial_injective K w) (wordPolynomial_mem_flagSpace K w)
    (eq_zero_of_flagSpace_eval_eq_zero ι n _ _ hcard hweight.1 hweight.2) v hv

/-- The fixed vectors of the literal upper subgroup are exactly the scalar
multiples of the concrete nonzero highest tensor. -/
theorem fixed_iff_mem_span [Finite F] (ι : F →+* K) (n : ℕ)
    (hcard : Nat.card F = 2 ^ n) (w : List Factor) (hw : w.length = n)
    (v : WordSpace K w) :
    (∀ u : U F, wordRep ι w (specialLinear F u) v = v) ↔
      v ∈ Submodule.span K {wordSeed K w} := by
  refine ⟨fixed_mem_span ι n hcard w hw v, ?_⟩
  intro hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  intro u
  rw [map_smul, wordSeed_fixed]

omit [CharP K 2] in
/-- A word made entirely of trivial factors has its whole carrier on the seed line. -/
theorem seed_span_eq_top_of_counts_zero (w : List Factor)
    (hn : naturalCount w = 0) (ha : adjointCount w = 0) :
    Submodule.span K {wordSeed K w} = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_span_singleton (wordSeed_ne_zero K w), finrank_wordSpace, wordDegree_eq,
    hn, ha]
  simp

end Representation.SL3.BinaryDefiningFactors.TensorSimplicity.FixedLine
