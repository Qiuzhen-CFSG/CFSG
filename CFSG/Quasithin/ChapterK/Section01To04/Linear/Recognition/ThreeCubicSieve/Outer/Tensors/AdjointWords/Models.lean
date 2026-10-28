module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Estimate
public import Theory.Representation.SL3.BinaryDefiningFactors.AdjointTensorTranspose
public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions

/-!
# Operator models for pure-adjoint tensor words

The graph alternative records the literal inner-diagonal/graph automorphism
of SL₃ implemented by the given binary operator. Its realization singles out
one trace-zero adjoint factor on which the extended operator is transpose.
The field alternative identifies the same extended operator with interchange.
Neither model includes a displacement inequality. The graph and field model
producers remain separate obligations in GM Proposition 4.8 steps 2–5;
`AdjointWords` owns their assembly for Aschbacher–Smith K.3.2.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender
open Representation.BinaryOffender.SchurNormalizer
open Representation.SL3.BinaryDefiningFactors
open Representation.SL3.BinaryDefiningFactors.AdjointTensorTranspose
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open scoped MatrixGroups TensorProduct

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.AdjointWords
variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V) [IsIrreducible σ]

/-- The given binary operator implements a genuine graph automorphism, up to
inner-diagonal conjugation; the equation uses the original SL₃ representation. -/
def GraphAction (t : linearNormalizer σ) : Prop :=
  ∃ c : GL (Fin 3) B.Carrier, ∀ g : SL(3,B.Carrier),
    t.val.val * σ g =
      σ (Matrix.PSL3.OuterSolvable.linearConjSL B.Carrier c
        (Matrix.PSL3.OuterSolvable.graphSL B.Carrier g)) * t.val.val

/-- Actual transpose on one adjoint factor. Scalar ambiguity may be absorbed
into the residual operator, on which no involution or rank premise is imposed. -/
structure GraphRealization (t : linearNormalizer σ) (hs : IsSchurLinear σ t) where
  size : ℕ
  residual : Module.End (SplittingField σ) (Fin size → SplittingField σ)
  equiv : (SplittingField σ ⊗[SchurField σ] σ.asModule) ≃ₗ[SplittingField σ]
    (AdjointSpace (SplittingField σ) ⊗[SplittingField σ] (Fin size → SplittingField σ))
  action : ∀ v, equiv (absoluteActor σ (SplittingField σ) t hs v) =
    TensorProduct.map (adjointTranspose (SplittingField σ)) residual (equiv v)

/-- Actual interchange, with both tensor factors nontrivial. The size condition
is structural; the displacement bound is proved from interchange itself. -/
structure ExchangeRealization (t : linearNormalizer σ) (hs : IsSchurLinear σ t) where
  size : ℕ
  two_le : 2 ≤ size
  equiv : (SplittingField σ ⊗[SchurField σ] σ.asModule) ≃ₗ[SplittingField σ]
    TensorInterchange.Space (SplittingField σ) size
  action : ∀ v, equiv (absoluteActor σ (SplittingField σ) t hs v) =
    TensorInterchange.flip (SplittingField σ) size (equiv v)

/-- The graph producer has the actual graph-action equation as its input;
it need not wait for the independent outer-type analysis. -/
def GraphModels : Prop :=
  ∀ M : RepeatedModel B σ, naturalCount M.block = 0 →
    0 < adjointCount M.block → ¬ SingleAdjoint B σ M →
    ∀ t : linearNormalizer σ, t ^ 2 = 1 → t.val ∉ actionImage σ →
      ∀ hs : IsSchurLinear σ t, GraphAction B σ t →
        Nonempty (GraphRealization B σ t hs)

/-- Outer-type analysis either supplies the literal graph-action equation or
constructs the field/graph-field exchange, on the original Schur extension. -/
def OuterModels : Prop :=
  ∀ M : RepeatedModel B σ, naturalCount M.block = 0 →
    0 < adjointCount M.block → ¬ SingleAdjoint B σ M →
    ∀ t : linearNormalizer σ, t ^ 2 = 1 → t.val ∉ actionImage σ →
      ∀ hs : IsSchurLinear σ t,
        GraphAction B σ t ∨ Nonempty (ExchangeRealization B σ t hs)

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.AdjointWords
