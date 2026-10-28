module
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.BasicSpaces
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.RootCurves
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.PositivePrimitives.ContravariantForm.Opposition
import all Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.PositivePrimitives.ContravariantForm.Opposition

/-!
# The native Ree opposition in the actual algebraic carrier

The fixed sixth power of the native Coxeter word maps to the proved algebraic
opposition element. Its simple factors are the same root words; the reverse
word equals the inverse, and native opposition is self-inverse. Thus the
pairing test uses an element of the original finite Ree group.
Source: GLS3 Section 2.3 and Steinberg (1963), Section 12.
-/
public section
open Theory.AlgebraicGroup StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
open AlgebraicTensor ContravariantForm
open LocalBlockInput.PairNormalization
variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]
noncomputable local instance oppositionComparisonRootNeg : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

@[expose] noncomputable def oppositionModel (m : ℕ) : Model m :=
  (canonicalLocalBlockInput m).modelEquiv (opposition (canonicalLocalBlockInput m))

theorem oppositionModel_split (m : ℕ) :
    toSplitGroup m (oppositionModel m) = splitOpposition m := by
  rw [toSplitGroup_apply, oppositionModel, LocalBlockInput.modelEquiv_coe]
  rfl

private theorem simpleLift_embedding {m : ℕ} (f : CoefficientField m →+* F) (i : Fin 4) :
    splitEmbedding f (simpleLift m i) = algebraicNElement (typeF4SimpleRootIndex i) 1 := by
  simp only [simpleLift, map_mul, splitEmbedding_rootGenerator, map_one,
    algebraicNElement, Units.val_one, inv_one, CharTwo.neg_eq]

theorem opposition_embedding {m : ℕ} (f : CoefficientField m →+* F) :
    modelEmbedding f (oppositionModel m) = oppositionElement := by
  change splitEmbedding f (toSplitGroup m (oppositionModel m)) = _
  rw [oppositionModel_split]
  have hn (i : Fin 4) : (algebraicNElement (typeF4SimpleRootIndex i) (1 : Fˣ))⁻¹ =
      algebraicNElement (typeF4SimpleRootIndex i) (1 : Fˣ) := by
    simp only [algebraicNElement, Units.val_one, inv_one, CharTwo.neg_eq,
      mul_inv_rev, ContravariantForm.algebraicRootElement_inv, mul_assoc]
  have he : oppositionElement (F := F) = (splitEmbedding f (splitOpposition m))⁻¹ := by
    unfold oppositionElement oppositionWord halfWord coxeterWord
    change EndNode.normalizerWord (List.replicate 6 [0,1,2,3]).flatten = _
    dsimp only [List.replicate, List.flatten, List.append]
    simp only [splitOpposition, map_pow, coxeterElement, map_mul,
      simpleLift_embedding, EndNode.normalizerWord, one_mul]
    rw [← inv_pow]
    simp only [mul_inv_rev, hn, pow_succ, pow_zero, mul_assoc]
    group
  rw [he, ← map_inv, splitOpposition_inv]

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
