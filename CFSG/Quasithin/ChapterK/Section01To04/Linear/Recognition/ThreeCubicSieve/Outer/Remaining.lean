module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.TensorEstimates
public import Theory.Representation.BinaryOffender.SchurNormalizerDisplacement

/-!
# The remaining Schur-linear outer calculations

The scalar-moving case is proved in `Outer.Schur`. These two independent
contracts concern actors linear over the actual component Schur field.
They separate one trace-zero adjoint factor from the other non-small tensor
words. Neither contract is asserted here. In particular, Schur linearity
does not imply that an outer automorphism of the component is inner.

Source: Guralnick–Malle, Classification of 2F-modules II, Proposition 4.8,
manuscript pp.26–28. Step 3A uses the strict trace-zero comparison for SL₃;
steps 2–5 distinguish field, graph, graph-field and combined actors.
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer

open Representation Representation.BinaryOffender
open Representation.BinaryOffender.SchurNormalizer
open Representation.SL3.BinaryDefiningFactors
open ChapterB.QuasisimpleSource
open scoped MatrixGroups

variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V) [IsIrreducible σ]

/-- The actual repeated word has precisely one adjoint factor and no
natural or dual factors. Its single block is repeated once. -/
def SingleAdjoint (M : RepeatedModel B σ) : Prop :=
  naturalCount M.block = 0 ∧ adjointCount M.block = 1 ∧ M.repetitions = 1

/-- The trace-zero adjoint branch, for the literal binary actor. -/
def SchurLinearAdjointEstimate : Prop :=
  ∀ M : RepeatedModel B σ, SingleAdjoint B σ M →
    ∀ A : Subgroup (linearNormalizer σ), IsElementaryTwo A →
      IsCubic (normalizerRepresentation σ) A → rank A ≤ 2 * B.degree →
      ¬ A.map (linearNormalizer σ).subtype ≤ actionImage σ →
      (∀ t ∈ A, IsSchurLinear σ t) →
      2 * rank A < fixedCodim (normalizerRepresentation σ) A

/-- All other non-small words, allowing every component outer type whose
operator is linear over the actual Schur field. -/
def SchurLinearTensorEstimate : Prop :=
  ∀ M : RepeatedModel B σ,
    0 < naturalCount M.block + adjointCount M.block → ¬ M.Small →
    ¬ SingleAdjoint B σ M →
    ∀ A : Subgroup (linearNormalizer σ), IsElementaryTwo A →
      IsCubic (normalizerRepresentation σ) A → rank A ≤ 2 * B.degree →
      ¬ A.map (linearNormalizer σ).subtype ≤ actionImage σ →
      (∀ t ∈ A, IsSchurLinear σ t) →
      2 * rank A < fixedCodim (normalizerRepresentation σ) A

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer
