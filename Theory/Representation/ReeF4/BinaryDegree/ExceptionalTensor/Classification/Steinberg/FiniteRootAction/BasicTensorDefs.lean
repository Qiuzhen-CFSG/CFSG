module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Basic
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.CyclicOrder
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.RootCurves

/-!
# The ordinary Frobenius tensor on a fixed basic tensor space

Reorder the source basic factors by the proved ordinary index permutation.
Their untwisted tensor prefix provides a single vector space, independent of
all pullback maps. On that space the finite Ree action twists factor `i` by
the `i`th ordinary Frobenius and the actual coefficient embedding. Factorwise
weight spaces will therefore measure the unweighted sum of basic deficits,
separately from the doubled algebraic weights of these pullbacks.

Source: Steinberg (1963), Section 12; GLS3 Theorem 2.8.2 and Remark 2.8.4.
-/

public section
noncomputable section
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction

open Theory.AlgebraicGroup
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]

/-- The factor belonging to ordinary Frobenius position `i`. -/
@[expose] def basicFactor (m : ℕ) (B : ZMod (2 * m + 1) → AlgebraicFactor F) (i : ℕ) :
    AlgebraicFactor F := B (ordinaryIndex m (i : ZMod (2 * m + 1)))

/-- A canonical tensor space without any Frobenius pullback in its definition. -/
abbrev basicTensorSpace (m : ℕ) (B : ZMod (2 * m + 1) → AlgebraicFactor F) (n : ℕ) :=
  ↥(tensorPrefix (fun i => (basicFactor m B i).restrict (MonoidHom.id _)) n)

variable [CharP F 2]

/-- The actual finite action with ordinary Frobenius exponents `0,...,n-1`. -/
@[expose] def ordinaryAction (m : ℕ) (B : ZMod (2 * m + 1) → AlgebraicFactor F)
    (f : CoefficientField m →+* F) :
    (n : ℕ) → Representation F (Model m) (basicTensorSpace m B n)
  | 0 => Representation.trivial F (Model m) F
  | n + 1 => Representation.tprod (ordinaryAction m B f n)
      ((basicFactor m B n).restrict ((Geometry.frobeniusEnd ^ n).comp
        (modelEmbedding f))).ρ

/-- The recursive action is equivalent to the existing tensor prefix with
its literal Frobenius pullbacks. -/
def ordinaryAction_equiv_tensorPrefix (m : ℕ)
    (B : ZMod (2 * m + 1) → AlgebraicFactor F) (f : CoefficientField m →+* F) (n : ℕ) :
    Representation.Equiv (ordinaryAction m B f n)
      (tensorPrefix (fun i => (basicFactor m B i).restrict
        ((Geometry.frobeniusEnd ^ i).comp (modelEmbedding f))) n).ρ := by
  induction n with
  | zero => exact Representation.Equiv.refl _
  | succ n ih =>
    let e := Representation.Equiv.refl
      ((basicFactor m B n).restrict ((Geometry.frobeniusEnd ^ n).comp
        (modelEmbedding f))).ρ
    exact .mk (TensorProduct.congr ih.toLinearEquiv e.toLinearEquiv)
      (ih.toIntertwiningMap.tensor e.toIntertwiningMap).2

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
