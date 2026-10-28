module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization.Paired

/-!
# Character invariance for the original SL₃ word

A Schur-linear actor preserves the character after extending the original
component Schur field. Its literal intertwining equation and square-one equation
prove this by cyclic invariance of trace. Transport through the repeated-model
equivalence gives invariance of the actual tensor word, ready for the word
uniqueness and graph/field calculations. No defining-field linearity is assumed.

Source: GM, Classification of 2F-modules II, Proposition 4.8 steps 2–5,
manuscript pp.26–28; Aschbacher–Smith K.3.2, printed pp.454–456.
-/

public section
noncomputable section
open Representation Representation.BinaryOffender
open Representation.BinaryOffender.SchurNormalizer
open Representation.SL3.BinaryDefiningFactors
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization

variable {B : BinaryField} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    {σ : Representation (ZMod 2) SL(3,B.Carrier) V} [IsIrreducible σ]

/-- Conjugation by the original absolute actor preserves the absolute character. -/
theorem LiftedInvolution.absolute_character_fixed {t : linearNormalizer σ}
    (L : LiftedInvolution B σ t) (ht : IsSchurLinear σ t) (g : SL(3,B.Carrier)) :
    (extendScalars (SplittingField σ) σ.endFieldRep).character (L.automorphism g) =
      (extendScalars (SplittingField σ) σ.endFieldRep).character g := by
  let T := absoluteActor σ (SplittingField σ) t ht
  let τ := extendScalars (SplittingField σ) σ.endFieldRep
  have h2 : T * T = 1 := by
    simpa only [pow_two] using absoluteActor_square σ (SplittingField σ) t ht L.actor_square
  have he : T * τ g * T = τ (L.automorphism g) := by
    rw [L.absolute_intertwines ht, mul_assoc, h2, mul_one]
  change LinearMap.trace _ _ _ = LinearMap.trace _ _ _
  rw [← he, LinearMap.trace_mul_cycle, h2, one_mul]

/-- The actual repeated tensor word, with its actual coefficient embedding,
has invariant character under the lifted automorphism. -/
theorem LiftedInvolution.word_character_fixed {t : linearNormalizer σ}
    (L : LiftedInvolution B σ t) (ht : IsSchurLinear σ t)
    (M : RepeatedModel B σ) (g : SL(3,B.Carrier)) :
    (wordRep M.coefficientEmbedding (List.replicate M.repetitions M.block).flatten).character
        (L.automorphism g) =
      (wordRep M.coefficientEmbedding (List.replicate M.repetitions M.block).flatten).character g := by
  rw [← char_iso M.equiv]
  exact L.absolute_character_fixed ht g

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization
