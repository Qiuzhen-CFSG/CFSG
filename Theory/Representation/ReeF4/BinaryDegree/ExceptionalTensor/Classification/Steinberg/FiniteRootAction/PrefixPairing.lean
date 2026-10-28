module
public import Theory.Representation.FrobeniusPositiveIrreducibility
public import Theory.Representation.TensorInvariantPairing
import all Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.PositivePrimitives.ContravariantForm.Opposition
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.FactorPairing
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.OppositionComparison
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.PrefixPrimitives
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.TensorGrading.OrdinaryPoints

/-!
# The invariant pairing on the original ordinary Ree tensor action

Tensor the actual invariant self-dualities of the basic factors. Their product
is nondegenerate and invariant for the literal ordinary Frobenius action.
Native opposition is fixed by Frobenius and has nonzero pairing against the
source tensor highest vector. The final consumer uses this to discharge all
pairing and opposition premises in the invariant-annihilator criterion.

Only the positive highest-line assertion remains with the tensor-filtration
producer. Source: Steinberg (1963), finite twisted tensor theorem 12.2.
-/

public section

open Theory.AlgebraicGroup
open scoped TensorProduct
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
open AlgebraicTensor
variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]
variable (m : ℕ) (B : ZMod (2*m+1) → AlgebraicFactor F)

@[expose] noncomputable def prefixPairing
    (e : ∀i, (basicFactor m B i).Space ≃ₗ[F] Module.Dual F (basicFactor m B i).Space) :
    (n : ℕ) → basicTensorSpace m B n ≃ₗ[F] Module.Dual F (basicTensorSpace m B n)
  | 0 => (LinearMap.ringLmapEquivSelf F F F).symm
  | n+1 => TensorProduct.pairingTensor (prefixPairing e n) (e n)

set_option backward.isDefEq.respectTransparency false in
theorem prefixPairing_invariant
    (e : ∀i, (basicFactor m B i).Space ≃ₗ[F] Module.Dual F (basicFactor m B i).Space)
    (he : ∀i g x y, e i (((basicFactor m B i).action.action g : Module.End F _) x)
      (((basicFactor m B i).action.action g : Module.End F _) y) = e i x y)
    (f : CoefficientField m →+* F) (n : ℕ) (g : Model m)
    (x y : basicTensorSpace m B n) :
    prefixPairing m B e n (ordinaryAction m B f n g x) (ordinaryAction m B f n g y) =
      prefixPairing m B e n x y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change TensorProduct.pairingTensor (prefixPairing m B e n) (e n)
      (TensorProduct.map (ordinaryAction m B f n g) _ x)
      (TensorProduct.map (ordinaryAction m B f n g) _ y) = _
    exact TensorProduct.pairingTensor_invariant _ _ _ _ (ih) (he n _) x y

private theorem frobenius_opposition :
    Geometry.frobeniusEnd (F := F) ContravariantForm.oppositionElement =
      ContravariantForm.oppositionElement := by
  have hn (i : Fin 4) : Geometry.frobeniusEnd (F := F)
      (algebraicNElement (StandardRootSystem.typeF4SimpleRootIndex i) 1) =
      algebraicNElement (StandardRootSystem.typeF4SimpleRootIndex i) 1 := by
    simp only [algebraicNElement, map_mul, Geometry.frobeniusEnd_root,
      Units.val_one, inv_one, CharTwo.neg_eq, one_pow]
  have hw (w : List (Fin 4)) : Geometry.frobeniusEnd (F := F) (EndNode.normalizerWord w) =
      EndNode.normalizerWord w := by
    induction w with
    | nil => exact map_one _
    | cons i w ih => simp only [EndNode.normalizerWord, map_mul, ih, hn]
  exact hw ContravariantForm.oppositionWord

private theorem frobenius_pow_opposition (n : ℕ) :
    (Geometry.frobeniusEnd (F := F)^n) ContravariantForm.oppositionElement =
      ContravariantForm.oppositionElement := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    change Geometry.frobeniusEnd ((Geometry.frobeniusEnd^n) _) = _
    rw [ih, frobenius_opposition]

set_option backward.isDefEq.respectTransparency false in
theorem prefixPairing_opposition_ne_zero
    (e : ∀i, (basicFactor m B i).Space ≃ₗ[F] Module.Dual F (basicFactor m B i).Space)
    (v : ∀i, (basicFactor m B i).Space)
    (he : ∀i, e i (v i) (((basicFactor m B i).action.action
      ContravariantForm.oppositionElement : Module.End F _) (v i)) ≠ 0)
    (f : CoefficientField m →+* F) (n : ℕ) :
    prefixPairing m B e n (highestTensor m B v n)
      (ordinaryAction m B f n (oppositionModel m) (highestTensor m B v n)) ≠ 0 := by
  induction n with
  | zero =>
    change ((LinearMap.ringLmapEquivSelf F F F).symm (1 : F)) (1 : F) ≠ 0
    simp
  | succ n ih =>
    change TensorProduct.pairingTensor (prefixPairing m B e n) (e n)
      (highestTensor m B v n ⊗ₜ[F] v n)
      (TensorProduct.map (ordinaryAction m B f n (oppositionModel m)) _
        (highestTensor m B v n ⊗ₜ[F] v n)) ≠ 0
    rw [TensorProduct.map_tmul, TensorProduct.pairingTensor_tmul]
    apply mul_ne_zero ih
    change e n (v n) (((basicFactor m B n).action.action
      ((Geometry.frobeniusEnd^n) (modelEmbedding f (oppositionModel m))) : Module.End F _) (v n)) ≠ 0
    rw [opposition_embedding, frobenius_pow_opposition]
    exact he n

/-- Actual source pairings remove the self-duality and opposition inputs from
finite irreducibility. The remaining highest-line premise belongs to the
positive root-filtration producer. -/
theorem ordinary_isIrreducible_of_highest_mem
    (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    (p : ∀i, RootExpansion (basicFactor m B i).action)
    (b : ℕ → BasicWeight) (v : ∀i, (basicFactor m B i).Space)
    (hv : ∀i, (basicFactor m B i).IsBasicHighestWeightVector (b i) (v i))
    (f : CoefficientField m →+* F) (n : ℕ)
    (hline : ∀ W : Subrepresentation (ordinaryAction m B f n),
      W ≠ ⊥ → highestTensor m B v n ∈ W) :
    Representation.IsIrreducible (ordinaryAction m B f n) := by
  classical
  choose e hinv hpair using fun i => exists_factor_pairing hU (p i) (hv i)
  exact Representation.irreducible_of_common_line_and_pairing
    (ordinaryAction m B f n) (highestTensor m B v n) (prefixPairing m B e n)
    (prefixPairing_invariant m B e hinv f n) (oppositionModel m)
    (prefixPairing_opposition_ne_zero m B e v hpair f n) hline

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
