module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.AdjointWords.Models
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.AdjointWords.GraphModels.Normalization
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.AdjointWords.GraphModels.WordOperators
public import Theory.Representation.TensorInvolutionIntertwiners
/-!
# Graph realizations on the original Schur extension

The central kernel and the square-one equation force a symmetric graph matrix.
The genuine repeated word then has a factorwise graph operator, conjugate to
transpose on its first adjoint factor tensor its actual residual operator.
Transport it back along the given representation equivalence. Absolute Schur
rigidity compares it with the original Schur-linear actor; absorb their scalar
ratio into the residual operator.

This proves the exact `GraphModels` contract, including trivial positions and
Frobenius twists, without a displacement premise or absolute irreducibility over
F₂. In fact the realization also holds for the single-adjoint word. The separate
outer-type analysis is not needed because the literal graph equation is an input.

Source: GM, Classification of 2F-modules II, Proposition 4.8 step 3A,
manuscript p.27; Aschbacher–Smith K.3.2, printed pp.454–456.
-/

public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Representation Representation.BinaryOffender
open Representation.BinaryOffender.SchurNormalizer
open Representation.SL3.BinaryDefiningFactors
open Representation.SL3.BinaryDefiningFactors.AdjointTensorTranspose
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Matrix.PSL3.OuterSolvable
open scoped MatrixGroups TensorProduct
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.AdjointWords
variable {B : BinaryField} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    {σ : Representation (ZMod 2) SL(3,B.Carrier) V} [IsIrreducible σ]

private theorem absolute_intertwines (t : linearNormalizer σ) (hs : IsSchurLinear σ t)
    (α : MulAut SL(3,B.Carrier))
    (hi : ∀ g, t.val.val * σ g = σ (α g) * t.val.val) (g : SL(3,B.Carrier)) :
    absoluteActor σ (SplittingField σ) t hs *
      extendScalars (SplittingField σ) σ.endFieldRep g =
    extendScalars (SplittingField σ) σ.endFieldRep (α g) *
      absoluteActor σ (SplittingField σ) t hs := by
  have h : schurActor σ t hs * σ.endFieldRep g =
      σ.endFieldRep (α g) * schurActor σ t hs := by
    ext v
    apply σ.asModuleEquiv.injective
    exact LinearMap.congr_fun (hi g) (σ.asModuleEquiv v)
  change LinearMap.baseChange _ _ * LinearMap.baseChange _ _ =
    LinearMap.baseChange _ _ * LinearMap.baseChange _ _
  rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, h]

/-- Realize the original actor on an actual adjoint tensor, allowing a central kernel. -/
theorem graphRealization_of_graphAction (hk : σ.ker ≤ Subgroup.center _)
    (M : RepeatedModel B σ) (hn : naturalCount M.block = 0)
    (ha : 0 < adjointCount M.block) (t : linearNormalizer σ) (ht : t ^ 2 = 1)
    (hs : IsSchurLinear σ t) (hgraph : GraphAction B σ t) :
    Nonempty (GraphRealization B σ t hs) := by
  obtain ⟨c, hc⟩ := hgraph
  have hsym := graph_matrix_symmetric ht hk c hc
  let K := SplittingField σ
  let w := (List.replicate M.repetitions M.block).flatten
  have hn' : naturalCount w = 0 := by
    simp only [w, naturalCount_repeat, hn, mul_zero]
  have ha' : 0 < adjointCount w := by
    rw [adjointCount_repeat]
    exact Nat.mul_pos M.repetitions_pos ha
  obtain ⟨n, r, E, hE⟩ := WordOperators.coordinates M.coefficientEmbedding c hsym w hn' ha'
  let e := M.equiv.toLinearEquiv
  let S := e.trans ((WordOperators.word M.coefficientEmbedding c w).trans e.symm)
  let τ := extendScalars K σ.endFieldRep
  let α := linearConjSL B.Carrier c * graphSL B.Carrier
  let : IsAbsolutelyIrreducible σ.endFieldRep := endFieldRep_isAbsolutelyIrreducible σ
  let : IsIrreducible τ := IsAbsolutelyIrreducible.irreducible_of_extension σ.endFieldRep K
  have hS (v) : e (S v) = WordOperators.word M.coefficientEmbedding c w (e v) := e.apply_symm_apply _
  have he (g : SL(3,B.Carrier)) (v) :
      e (τ g v) = wordRep M.coefficientEmbedding w g (e v) :=
    LinearMap.congr_fun (M.equiv.isIntertwining' g) v
  have hSi (g : SL(3,B.Carrier)) : S.toLinearMap * τ g = τ (α g) * S.toLinearMap := by
    apply LinearMap.ext
    intro v
    apply e.injective
    change e (S (τ g v)) = e (τ (α g) (S v))
    rw [hS, he, he, hS]
    exact LinearMap.congr_fun (WordOperators.word_intertwines M.coefficientEmbedding c w hn' g) (e v)
  obtain ⟨a, hT⟩ := TensorInvolutionIntertwiners.same_automorphism_scalar τ α
    (absoluteActor σ K t hs) S (absolute_intertwines t hs α hc) hSi
  refine ⟨{ size := n, residual := a • r, equiv := e.trans E, action := ?_ }⟩
  intro v
  change E (e (absoluteActor σ K t hs v)) =
    TensorProduct.map (adjointTranspose K) (a • r) (E (e v))
  rw [hT, LinearMap.smul_apply, map_smul, map_smul]
  change a • E (e (S v)) = _
  rw [hS, hE, TensorProduct.map_smul_right, LinearMap.smul_apply]

/-- The published graph-model premise is discharged without additional geometric inputs. -/
theorem graph_models (hk : σ.ker ≤ Subgroup.center _) : GraphModels B σ := by
  intro M hn ha _ t ht _ hs hgraph
  exact graphRealization_of_graphAction hk M hn ha t ht hs hgraph
end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.AdjointWords
