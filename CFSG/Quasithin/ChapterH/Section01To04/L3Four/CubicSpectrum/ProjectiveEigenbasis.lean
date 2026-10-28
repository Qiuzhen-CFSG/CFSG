module

public import CFSG.Quasithin.ChapterH.Section01To04.L3Four.CubicSpectrum.Definitions
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# From natural cubic eigenvectors to the actual adjoint eigenbasis

An eigenbasis with natural weights `1, ω, ω²` gives an eigenbasis of the
trace-zero endomorphisms. In its matrix coordinates the first two vectors are
`E₀₀ - E₂₂` and `E₁₁ - E₂₂`. The next three are `E₀₂, E₁₀, E₂₁`, and the last
three are `E₀₁, E₁₂, E₂₀`. Conjugation has weights `1,1,ω,ω,ω,ω²,ω²,ω²`.
The coordinate equivalence proves spanning and independence as well as the
trace-zero condition; the action calculation uses the actual `factorRep`.

The final helper applies this construction to both literal coefficient
embeddings with the same primitive cubic root. Existence of the natural
eigenbases remains an explicit premise: this module does not yet prove that
premise for every projective cubic in SL₃(4).

Source: Aschbacher–Smith H.4.7, refs/quasithin.pdf, printed pp.382–383.
The trace-kernel coordinate method follows the existing private construction in
Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.RestrictedFactors.
-/

public section

open scoped MatrixGroups
open Representation.SL3.BinaryDefiningFactors
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace CFSG.Quasithin.ChapterH.Section01To04.L3Four.CubicSpectrum
variable {F K : Type*} [Field F] [Field K]

private def matrixOf (v : Fin 8 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![v 0, v 5, v 2; v 3, v 1, v 6; v 7, v 4, -(v 0 + v 1)]

private def readMatrix (a : Matrix (Fin 3) (Fin 3) K) : Fin 8 → K :=
  ![a 0 0, a 1 1, a 0 2, a 1 0, a 2 1, a 0 1, a 1 2, a 2 0]

private theorem matrixOf_trace (v : Fin 8 → K) : (matrixOf v).trace = 0 := by
  simp [matrixOf, Matrix.trace, Fin.sum_univ_three]

private theorem matrixOf_readMatrix (a : Matrix (Fin 3) (Fin 3) K)
    (ha : a.trace = 0) : matrixOf (readMatrix a) = a := by
  have hdiag : -(a 0 0 + a 1 1) = a 2 2 := by
    have he : a 0 0 + a 1 1 + a 2 2 = 0 := by
      simpa [Matrix.trace, Fin.sum_univ_three] using ha
    exact (eq_neg_of_add_eq_zero_right he).symm
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixOf, readMatrix, hdiag]

private def coordinates (b : Module.Basis (Fin 3) K (Fin 3 → K)) :
    Space K .adjoint ≃ₗ[K] (Fin 8 → K) where
  toFun f := readMatrix (LinearMap.toMatrix b b f.val)
  invFun v := ⟨Matrix.toLin b b (matrixOf v), by
    change LinearMap.trace K (Fin 3 → K) (Matrix.toLin b b (matrixOf v)) = 0
    rw [Matrix.trace_toLin_eq]
    exact matrixOf_trace v⟩
  left_inv f := by
    apply Subtype.ext
    change Matrix.toLin b b (matrixOf (readMatrix (LinearMap.toMatrix b b f.val))) = f.val
    rw [matrixOf_readMatrix, Matrix.toLin_toMatrix]
    rw [← LinearMap.trace_eq_matrix_trace K b]
    exact f.property
  right_inv v := by
    change readMatrix (LinearMap.toMatrix b b (Matrix.toLin b b (matrixOf v))) = v
    rw [LinearMap.toMatrix_toLin]
    funext i
    fin_cases i <;> rfl
  map_add' f h := by
    change readMatrix (LinearMap.toMatrix b b (f.val + h.val)) = _
    rw [map_add]
    funext i
    fin_cases i <;> rfl
  map_smul' c f := by
    change readMatrix (LinearMap.toMatrix b b (c • f.val)) = _
    rw [map_smul]
    funext i
    fin_cases i <;> rfl

private theorem natural_matrix (ι : F →+* K) (g : SL(3,F)) (ω : K)
    (b : Module.Basis (Fin 3) K (Fin 3 → K))
    (hb : ∀ i, natural ι g (b i) = ω ^ i.val • b i) :
    LinearMap.toMatrix b b (natural ι g) = Matrix.diagonal (fun i => ω ^ i.val) := by
  classical
  ext i j
  by_cases h : i = j
  · subst j; simp [LinearMap.toMatrix_apply, hb]
  · simp [LinearMap.toMatrix_apply, hb, h]

private theorem natural_inv_action (ι : F →+* K) (g : SL(3,F)) (ω : K)
    (hω : ω ≠ 0) (b : Module.Basis (Fin 3) K (Fin 3 → K))
    (hb : ∀ i, natural ι g (b i) = ω ^ i.val • b i) (i : Fin 3) :
    natural ι g⁻¹ (b i) = (ω⁻¹) ^ i.val • b i := by
  have hh : natural ι g⁻¹ ∘ₗ natural ι g = LinearMap.id := by
    rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hi := congrArg (fun f : Module.End K (Fin 3 → K) => f (b i)) hh
  change natural ι g⁻¹ (natural ι g (b i)) = b i at hi
  rw [hb, map_smul] at hi
  calc
    natural ι g⁻¹ (b i) = (ω ^ i.val)⁻¹ • (ω ^ i.val • natural ι g⁻¹ (b i)) := by
      rw [← mul_smul, inv_mul_cancel₀ (pow_ne_zero _ hω), one_smul]
    _ = (ω⁻¹) ^ i.val • b i := by rw [hi, inv_pow]

private theorem coordinates_action (ι : F →+* K) (g : SL(3,F)) (ω : K)
    (hω : ω ^ 3 = 1) (b : Module.Basis (Fin 3) K (Fin 3 → K))
    (hb : ∀ i, natural ι g (b i) = ω ^ i.val • b i)
    (f : Space K .adjoint) (i : Fin 8) :
    coordinates b (factorRep ι .adjoint g f) i =
      ω ^ adjointCubicExponent i * coordinates b f i := by
  have hω0 : ω ≠ 0 := by intro h; simp [h] at hω
  have hωinv : ω⁻¹ = ω ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [← pow_succ'] using hω
  have hmat : LinearMap.toMatrix b b (factorRep ι .adjoint g f).val =
      Matrix.diagonal (fun j : Fin 3 => ω ^ j.val) * LinearMap.toMatrix b b f.val *
        Matrix.diagonal (fun j : Fin 3 => (ω⁻¹) ^ j.val) := by
    change LinearMap.toMatrix b b (natural ι g ∘ₗ f.val ∘ₗ natural ι g⁻¹) = _
    rw [LinearMap.toMatrix_comp b b b, LinearMap.toMatrix_comp b b b,
      natural_matrix ι g ω b hb,
      natural_matrix ι g⁻¹ ω⁻¹ b (natural_inv_action ι g ω hω0 b hb), mul_assoc]
  change readMatrix (LinearMap.toMatrix b b (factorRep ι .adjoint g f).val) i =
    ω ^ adjointCubicExponent i * readMatrix (LinearMap.toMatrix b b f.val) i
  rw [hmat]
  fin_cases i <;>
    simp [readMatrix, adjointCubicExponent, Matrix.mul_diagonal, Matrix.diagonal_mul,
      hωinv, ← pow_mul] <;>
    ring_nf <;>
    simp only [hω, show ω ^ 4 = ω by rw [show 4 = 3 + 1 from rfl, pow_succ, hω, one_mul],
      show ω ^ 5 = ω ^ 2 by rw [show 5 = 3 + 2 from rfl, pow_add, hω, one_mul], one_mul]

/-- The trace-zero matrix units, transported through an actual natural eigenbasis. -/
def adjointCubicEigenbasisOfNatural (ι : F →+* K) (g : SL(3,F)) (ω : K)
    (hω : ω ^ 3 = 1) (b : Module.Basis (Fin 3) K (Fin 3 → K))
    (hb : ∀ i, natural ι g (b i) = ω ^ i.val • b i) :
    AdjointCubicEigenbasis ι g ω := by
  classical
  let b' := (Pi.basisFun K (Fin 8)).map (coordinates b).symm
  have hcoord (i : Fin 8) : coordinates b (b' i) = Pi.single i 1 := by
    simp [b', Module.Basis.map_apply, Pi.basisFun_apply]
  refine ⟨b', fun i => ?_⟩
  apply (coordinates b).injective
  ext j
  rw [LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul, coordinates_action ι g ω hω b hb,
    hcoord]
  by_cases hij : i = j
  · subst j; rfl
  · simp [hij]

/-- An algebraically closed field of characteristic two has a primitive cubic root. -/
private theorem exists_cubic_root [IsAlgClosed K] [CharP K 2] : ∃ ω : K, orderOf ω = 3 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  let : NeZero (3 : K) := ⟨by simpa only [show (3 : K) = 2 + 1 from by norm_num,
    h2, zero_add] using (one_ne_zero : (1 : K) ≠ 0)⟩
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K 3
  exact ⟨ω, hω.eq_orderOf.symm⟩

/-- Apply the matrix-unit construction to both literal coefficient embeddings. -/
theorem paired_adjointCubicEigenbasis_of_natural [IsAlgClosed K] [CharP K 2]
    (ι : F →+* K) (g : SL(3,F))
    (hnat : ∀ (η : F →+* K) (ω : K), orderOf ω = 3 →
      ∃ b : Module.Basis (Fin 3) K (Fin 3 → K),
        ∀ i, natural η g (b i) = ω ^ i.val • b i) :
    ∃ ω : K, orderOf ω = 3 ∧ Nonempty (AdjointCubicEigenbasis ι g ω) ∧
      Nonempty (AdjointCubicEigenbasis ((frobenius K 2).comp ι) g ω) := by
  obtain ⟨ω, hω⟩ := exists_cubic_root (K := K)
  have hω3 : ω ^ 3 = 1 := by simpa only [hω] using pow_orderOf_eq_one ω
  obtain ⟨b, hb⟩ := hnat ι ω hω
  obtain ⟨c, hc⟩ := hnat ((frobenius K 2).comp ι) ω hω
  exact ⟨ω, hω, ⟨adjointCubicEigenbasisOfNatural ι g ω hω3 b hb⟩,
    ⟨adjointCubicEigenbasisOfNatural ((frobenius K 2).comp ι) g ω hω3 c hc⟩⟩

end CFSG.Quasithin.ChapterH.Section01To04.L3Four.CubicSpectrum
