module

public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.Displacements
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Concrete binary normalizer and its proposed normal forms

The component is the faithful natural-plus-dual copy of SL₃(4) in GL₁₂(2).
The displayed forms allow a general invertible three-by-three matrix, an
independent nonzero scalar on the dual summand, one common field automorphism,
and interchange of the summands. In particular the centralizer scalars and
all diagonal, field and graph operators are retained. `HasStandardForm` is
an explicit coordinate predicate, not an asserted normalizer classification.

This interface supports the normalizer reduction in Aschbacher--Smith,
proof of 13.8.20, printed p.955 (1 March 2004 manuscript).
-/

@[expose] public section
noncomputable section
namespace Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction
/-- All invertible binary operators on the specified twelve-dimensional space. -/
abbrev BinaryGL := V ≃ₗ[ZMod 2] V

/-- The actual matrix representation, with invertibility retained. -/
def linearAction : SL →* BinaryGL :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp
    representation.asGroupHom

lemma linearAction_apply (g : SL) (v : V) : linearAction g v = representation g v := rfl

lemma linearAction_injective : Function.Injective linearAction := by
  intro g h he
  apply representation_injective
  exact congrArg LinearEquiv.toLinearMap he

/-- The image of the specified SL₃(4), including its order-three center. -/
def component : Subgroup BinaryGL := linearAction.range

/-- The full binary linear normalizer of that image. -/
def normalizer : Subgroup BinaryGL := Subgroup.normalizer (component : Set BinaryGL)

/-- Evaluation of invertible binary operators on the module. -/
def binaryRepresentation : Representation (ZMod 2) BinaryGL V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom

/-- A common field twist followed by a natural matrix and a scalar multiple
of its contragredient matrix. -/
def standardPair (M : Matrix.GeneralLinearGroup (Fin 3) F)
    (c : Fˣ) (σ : F ≃+* F) (v : V) : V :=
  (M.val.mulVec (σ ∘ v.1), (c : F) • (M⁻¹).val.transpose.mulVec (σ ∘ v.2))

/-- The explicit preserving or exchanging coordinate forms. Coverage of the
normalizer by these forms remains a separate mathematical obligation. -/
def HasStandardForm (f : BinaryGL) : Prop :=
  ∃ (M : Matrix.GeneralLinearGroup (Fin 3) F) (c : Fˣ) (σ : F ≃+* F),
    (∀ v, f v = standardPair M c σ v) ∨
      (∀ v, f v = standardPair M c σ (v.2, v.1))

/-- Independent field scalars on the two summands, as a binary endomorphism. -/
def blockScalar (a b : F) : V →ₗ[ZMod 2] V where
  toFun v := (a • v.1, b • v.2)
  map_add' v w := by simp [smul_add]
  map_smul' c v := by
    change (a • (c • v.1), b • (c • v.2)) = (c • (a • v.1), c • (b • v.2))
    rw [smul_comm a c, smul_comm b c]

lemma blockScalar_apply (a b : F) (v : V) : blockScalar a b v = (a • v.1, b • v.2) := rfl

lemma blockScalar_commutes (a b : F) (g : SL) (v : V) :
    blockScalar a b (representation g v) = representation g (blockScalar a b v) := by
  simp only [blockScalar_apply, representation_apply, Matrix.mulVec_smul]

end Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction
