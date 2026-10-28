module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Remaining
public import Theory.Representation.BinaryOffender.SchurNormalizerAction
public import Theory.Representation.TensorInterchange

/-!
# Actual tensor-exchange data for the SL₃ outer actor

The exchange model is a linear equivalence on the scalar extension of the
original component Schur module. It identifies one member of the given actor
with tensor interchange. For actor rank greater than two it also identifies
a member with a nonidentity diagonal involution. It includes no fixed-space
bound, and does not assume linearity over the defining field of SL₃.

The two source obligations below separate words containing a natural or dual
factor from words containing only adjoint and trivial factors. Their producers
must construct the exchange data or prove the adjoint-tensor estimate. Neither
is asserted in this module. Source: GM, Classification of 2F-modules II,
Proposition 4.8 steps 2–5, manuscript pp.26–28; Aschbacher–Smith K.3.2.
-/

@[expose] public section
noncomputable section
open Representation Representation.BinaryOffender
open Representation.BinaryOffender.SchurNormalizer
open Representation.SL3.BinaryDefiningFactors
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open scoped MatrixGroups TensorProduct

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors

variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V) [IsIrreducible σ]

/-- Literal exchange and diagonal actions, with no numerical fixed-space premise. -/
structure SwapRealization (A : Subgroup (linearNormalizer σ))
    (hs : ∀ t ∈ A, IsSchurLinear σ t) where
  size : ℕ
  three_le : 3 ≤ size
  equiv : (SplittingField σ ⊗[SchurField σ] σ.asModule) ≃ₗ[SplittingField σ]
    TensorInterchange.Space (SplittingField σ) size
  outer : A
  outer_action : ∀ v, equiv (absoluteActor σ (SplittingField σ) outer.val
      (hs outer.val outer.property) v) =
    TensorInterchange.flip (SplittingField σ) size (equiv v)
  pair_action : 2 < rank A → ∃ u : A,
    ∃ f : Module.End (SplittingField σ) (Fin size → SplittingField σ),
      f ^ 2 = 1 ∧ f ≠ 1 ∧ ∀ v,
        equiv (absoluteActor σ (SplittingField σ) u.val (hs u.val u.property) v) =
          TensorProduct.map f f (equiv v)

/-- The field and graph-field analysis must realize every remaining word
with a natural or dual factor on the actual extended module. -/
def NaturalSwapModels : Prop :=
  ∀ M : RepeatedModel B σ, 0 < naturalCount M.block → ¬ M.Small →
    ∀ A : Subgroup (linearNormalizer σ), IsElementaryTwo A →
      IsCubic (normalizerRepresentation σ) A → rank A ≤ 2 * B.degree →
      ¬ A.map (linearNormalizer σ).subtype ≤ actionImage σ →
      ∀ hs : ∀ t ∈ A, IsSchurLinear σ t, Nonempty (SwapRealization B σ A hs)

/-- The remaining pure-adjoint words have at least two adjoint factors in
the full repeated word. The single adjoint belongs to the separate branch. -/
def AdjointTensorEstimate : Prop :=
  ∀ M : RepeatedModel B σ, naturalCount M.block = 0 →
    0 < adjointCount M.block → ¬ SingleAdjoint B σ M →
    ∀ A : Subgroup (linearNormalizer σ), IsElementaryTwo A →
      IsCubic (normalizerRepresentation σ) A → rank A ≤ 2 * B.degree →
      ¬ A.map (linearNormalizer σ).subtype ≤ actionImage σ →
      (∀ t ∈ A, IsSchurLinear σ t) →
      2 * rank A < fixedCodim (normalizerRepresentation σ) A

/-- A sufficient single-actor calculation on pure-adjoint tensor words.
Their proved degree gap of 32r makes this quarter-displacement estimate
strong enough for the original actor's common-fixed-space inequality. -/
def AdjointTensorDisplacement : Prop :=
  ∀ M : RepeatedModel B σ, naturalCount M.block = 0 →
    0 < adjointCount M.block → ¬ SingleAdjoint B σ M →
    ∀ t : linearNormalizer σ, t ^ 2 = 1 → t.val ∉ actionImage σ →
      IsSchurLinear σ t → Module.finrank (ZMod 2) V ≤
        4 * Module.finrank (ZMod 2) (t.val.val - 1).range

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors
