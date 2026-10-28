module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.AdjointWords.Models
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.GraphCentralizer.Actors
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.NormalForm
public import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Tactic.Group
/-!
# Literal graph operators on pure-adjoint tensor words

On each adjoint factor use conjugation after transpose, through that factor's
actual coefficient embedding. Tensor these operators recursively, retaining
trivial factors and every successive Frobenius twist. They intertwine the word
representation with the specified inner-diagonal graph automorphism of SL₃.

For a symmetric conjugating matrix, finite binary ternary congruence normalizes
one adjoint factor to transpose. Remove only the preceding trivial factors;
identify the entire remaining tensor word with its finite basis coordinates.
Its actual operator becomes the unrestricted residual operator. The matrix
helpers imported from the single-adjoint branch are general conjugation and
congruence lemmas; no single-adjoint estimate is used.

Source: GM, Classification of 2F-modules II, Proposition 4.8 step 3A,
manuscript p.27; Aschbacher–Smith K.3.2, printed pp.454–456.
-/

public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Representation Representation.SL3.BinaryDefiningFactors
open Representation.SL3.BinaryDefiningFactors.AdjointTensorTranspose
open Matrix.PSL3.OuterSolvable Matrix.PSL3.OddInvolutionFixed
open scoped MatrixGroups TensorProduct
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.AdjointWords
namespace WordOperators
open CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.GraphCentralizer
variable {F K : Type*} [Field F] [Field K]
local instance : AddCommGroup (AdjointSpace K) := inferInstance

private def transposeEquiv : AdjointSpace K ≃ₗ[K] AdjointSpace K :=
  LinearEquiv.ofInvolutive (adjointTranspose K) (by
    intro x
    apply matrix_injective
    simp only [matrix, matrix_adjointTranspose, Matrix.transpose_transpose])

private def adjoint (ι : F →+* K) (c : GL (Fin 3) F) :
    AdjointSpace K ≃ₗ[K] AdjointSpace K :=
  transposeEquiv.trans (adjointConj (Matrix.GeneralLinearGroup.map ι c))

private theorem matrix_adjoint (ι : F →+* K) (c : GL (Fin 3) F) (x : AdjointSpace K) :
    matrix (adjoint ι c x) = graph (Matrix.GeneralLinearGroup.map ι c) (matrix x) := by
  rw [adjoint, LinearEquiv.trans_apply, matrix_adjointConj]
  congr 1
  exact matrix_adjointTranspose K x

private theorem matrix_factor (ι : F →+* K) (g : SL(3,F)) (x : AdjointSpace K) :
    matrix (factorRep ι .adjoint g x) =
      inner (Matrix.GeneralLinearGroup.map ι (Matrix.SpecialLinearGroup.toGL g)) (matrix x) := by
  change LinearMap.toMatrix' (natural ι g ∘ₗ x.val ∘ₗ natural ι g⁻¹) = _
  have hn (a : SL(3,F)) : LinearMap.toMatrix' (natural ι a) = a.val.map ι :=
    LinearMap.toMatrix'_toLin' _
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, hn, hn]
  exact (mul_assoc _ _ _).symm

private theorem map_graph (ι : F →+* K) (c : GL (Fin 3) F) (g : SL(3,F)) :
    Matrix.GeneralLinearGroup.map ι
      (Matrix.SpecialLinearGroup.toGL (linearConjSL F c (graphSL F g))) =
    Matrix.GeneralLinearGroup.map ι c *
      (transposeGL (Matrix.GeneralLinearGroup.map ι (Matrix.SpecialLinearGroup.toGL g)))⁻¹ *
      (Matrix.GeneralLinearGroup.map ι c)⁻¹ := by
  rw [linearConjSL_toGL, graphSL_toGL, map_mul, map_mul, map_inv]
  congr 2

private theorem adjoint_intertwines (ι : F →+* K) (c : GL (Fin 3) F) (g : SL(3,F))
    (x : AdjointSpace K) :
    adjoint ι c (factorRep ι .adjoint g x) =
      factorRep ι .adjoint (linearConjSL F c (graphSL F g)) (adjoint ι c x) := by
  apply matrix_injective
  rw [matrix_adjoint, matrix_factor, matrix_factor, matrix_adjoint, map_graph,
    Adjoint.GraphCentralizer.graph, transpose_inner, Adjoint.GraphCentralizer.graph]
  simp only [← inner_mul]
  congr 1
  group

variable [CharP K 2]
private def factor (ι : F →+* K) (c : GL (Fin 3) F) :
    (a : Factor) → Space K a ≃ₗ[K] Space K a
  | .trivial => LinearEquiv.refl K K
  | .natural => LinearEquiv.refl K _
  | .dual => LinearEquiv.refl K _
  | .adjoint => adjoint ι c

/-- The actual factorwise graph operator, with successive Frobenius twists. -/
def word (ι : F →+* K) (c : GL (Fin 3) F) :
    (w : List Factor) → WordSpace K w ≃ₗ[K] WordSpace K w
  | [] => LinearEquiv.refl K K
  | a :: w => TensorProduct.congr (factor ι c a) (word ((frobenius K 2).comp ι) c w)

/-- The word operator implements the specified graph action on SL₃. -/
theorem word_intertwines (ι : F →+* K) (c : GL (Fin 3) F)
    (w : List Factor) (hw : naturalCount w = 0) (g : SL(3,F)) :
    (word ι c w).toLinearMap * wordRep ι w g =
      wordRep ι w (linearConjSL F c (graphSL F g)) * (word ι c w).toLinearMap := by
  induction w generalizing ι with
  | nil => rfl
  | cons a w ih =>
    have hw' : naturalCount w = 0 := by
      cases a <;> simp_all [naturalCount]
    have hf : (factor ι c a).toLinearMap * factorRep ι a g =
        factorRep ι a (linearConjSL F c (graphSL F g)) * (factor ι c a).toLinearMap := by
      cases a with
      | trivial => rfl
      | natural => simp [naturalCount] at hw
      | dual => simp [naturalCount] at hw
      | adjoint => ext x; exact adjoint_intertwines ι c g x
    change TensorProduct.map (factor ι c a).toLinearMap
      (word ((frobenius K 2).comp ι) c w).toLinearMap *
      TensorProduct.map (factorRep ι a g) (wordRep ((frobenius K 2).comp ι) w g) =
      TensorProduct.map (factorRep ι a (linearConjSL F c (graphSL F g)))
        (wordRep ((frobenius K 2).comp ι) w (linearConjSL F c (graphSL F g))) *
      TensorProduct.map (factor ι c a).toLinearMap (word ((frobenius K 2).comp ι) c w).toLinearMap
    rw [← TensorProduct.map_mul, ← TensorProduct.map_mul, hf, ih _ hw']

private theorem symmetric_identity [Finite F] [CharP F 2] (c : GL (Fin 3) F)
    (hc : c.val.transpose = c.val) :
    ∃ d : GL (Fin 3) F, d.val * c.val * d.val.transpose = 1 := by
  obtain ⟨C, hC⟩ := symmetric_gram c hc
  let P : Matrix (Fin 3) (Fin 3) F := !![1,0,1;0,1,1;1,1,1]
  have hP : P * Adjoint.gram F * P.transpose = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, Adjoint.gram, Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]
  have hd : P.det ≠ 0 := by
    simp [P, Matrix.det_fin_three, CharTwo.add_self_eq_zero, CharTwo.neg_eq]
  let Q := Matrix.GeneralLinearGroup.mkOfDetNeZero P hd
  refine ⟨Q * C, ?_⟩
  change (P * C.val) * c.val * (P * C.val).transpose = 1
  rw [Matrix.transpose_mul]
  calc
    _ = P * (C.val * c.val * C.val.transpose) * P.transpose := by simp only [mul_assoc]
    _ = 1 := by rw [hC, hP]

omit [CharP K 2] in
private theorem adjoint_normalized (ι : F →+* K) (c d : GL (Fin 3) F)
    (hd : d.val * c.val * d.val.transpose = 1) (x : AdjointSpace K) :
    adjointConj (Matrix.GeneralLinearGroup.map ι d) (adjoint ι c x) =
      adjointTranspose K (adjointConj (Matrix.GeneralLinearGroup.map ι d) x) := by
  have he : Matrix.GeneralLinearGroup.map ι d * Matrix.GeneralLinearGroup.map ι c *
      transposeGL (Matrix.GeneralLinearGroup.map ι d) = 1 := by
    apply Units.ext
    change d.val.map ι * c.val.map ι * (d.val.map ι).transpose = 1
    have hh := congrArg (fun X : Matrix (Fin 3) (Fin 3) F => X.map ι) hd
    simpa only [Matrix.map_mul, Matrix.map_one _ (map_zero ι) (map_one ι), Matrix.transpose_map] using hh
  have hT (y : AdjointSpace K) : matrix (adjointTranspose K y) = (matrix y).transpose :=
    matrix_adjointTranspose K y
  apply matrix_injective
  rw [matrix_adjointConj, matrix_adjoint, hT,
    matrix_adjointConj, graph_conj, he]
  simp only [Adjoint.GraphCentralizer.graph, Adjoint.GraphCentralizer.inner, Units.val_one, inv_one, Matrix.one_mul, Matrix.mul_one]


/-- Transpose on the first adjoint factor, and the actual remaining word operator. -/
theorem coordinates [Finite F] [CharP F 2] (ι : F →+* K) (c : GL (Fin 3) F)
    (hc : c.val.transpose = c.val) (w : List Factor)
    (hn : naturalCount w = 0) (ha : 0 < adjointCount w) :
    ∃ (n : ℕ) (r : Module.End K (Fin n → K))
      (e : WordSpace K w ≃ₗ[K] (AdjointSpace K ⊗[K] (Fin n → K))),
      ∀ v, e (word ι c w v) = TensorProduct.map (adjointTranspose K) r (e v) := by
  obtain ⟨d, hd⟩ := symmetric_identity c hc
  induction w generalizing ι with
  | nil => simp [adjointCount] at ha
  | cons a w ih =>
    cases a with
    | natural => simp [naturalCount] at hn
    | dual => simp [naturalCount] at hn
    | trivial =>
      have hn' : naturalCount w = 0 := by simpa [naturalCount] using hn
      have ha' : 0 < adjointCount w := by simpa [adjointCount] using ha
      obtain ⟨n, r, e, he⟩ := ih ((frobenius K 2).comp ι) hn' ha'
      refine ⟨n, r, (TensorProduct.lid K (WordSpace K w)).trans e, ?_⟩
      intro v
      induction v using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul x y =>
        change K at x
        change e (x • word ((frobenius K 2).comp ι) c w y) =
          TensorProduct.map (adjointTranspose K) r (e (x • y))
        rw [map_smul, he, map_smul, map_smul]
    | adjoint =>
      let e := (Module.finBasis K (WordSpace K w)).equivFun
      let r := e.conj (word ((frobenius K 2).comp ι) c w).toLinearMap
      refine ⟨Module.finrank K (WordSpace K w), r,
        TensorProduct.congr (adjointConj (Matrix.GeneralLinearGroup.map ι d)) e, ?_⟩
      intro v
      induction v using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul x y =>
        change adjointConj (Matrix.GeneralLinearGroup.map ι d) (adjoint ι c x) ⊗ₜ[K]
            e (word ((frobenius K 2).comp ι) c w y) =
          adjointTranspose K (adjointConj (Matrix.GeneralLinearGroup.map ι d) x) ⊗ₜ[K]
            e (word ((frobenius K 2).comp ι) c w (e.symm (e y)))
        rw [e.symm_apply_apply, adjoint_normalized ι c d hd]

end WordOperators
end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.AdjointWords
