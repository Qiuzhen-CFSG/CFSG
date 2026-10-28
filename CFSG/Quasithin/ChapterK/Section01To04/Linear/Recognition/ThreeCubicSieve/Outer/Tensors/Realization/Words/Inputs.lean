module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization.Words.CharacterAction

/-!
# The two geometric inputs for paired SL₃ words

A half-turn form specifies a literal automorphism of SL₃: a GL₃ conjugation
followed by the half-degree field automorphism and an optional graph action.
Character invariance proves that the actual repeated word has the corresponding
paired halves. The remaining independent inputs are the automorphism normal
form and an actual tensor intertwiner from this explicit pairing.

Neither input assumes the outer operator is tensor interchange, or that a
half representation descends to the image of the full component action.
Source: Guralnick--Malle, Classification of 2F-modules II, Proposition 4.8,
steps 2--5, manuscript pp.26--28; Aschbacher--Smith K.3.2, printed pp.454--456.
-/

@[expose] public section
noncomputable section
open Representation Representation.BinaryOffender
open Representation.BinaryOffender.SchurNormalizer
open Representation.SL3.BinaryDefiningFactors
open Matrix.PSL3.OuterSolvable
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization

/-- A field or graph-field half-turn, retaining its actual GL₃ twist. -/
structure HalfTurnForm (B : BinaryField) (α : MulAut SL(3,B.Carrier)) where
  halfDegree : ℕ
  half_pos : 0 < halfDegree
  degree_eq : B.degree = 2 * halfDegree
  matrix : GL (Fin 3) B.Carrier
  withGraph : Bool
  automorphism_eq : α = linearConjSL B.Carrier matrix *
    Words.fieldGraph (F := B.Carrier) halfDegree withGraph

variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V) [IsIrreducible σ]

/-- The involution normal-form obligation for the original outer operator.
The pure graph branch is excluded by the proved word-character calculation. -/
def OuterInvolutionForms : Prop :=
  ∀ t : linearNormalizer σ, t.val ∉ actionImage σ → IsSchurLinear σ t →
    ∀ L : LiftedInvolution B σ t,
      (∃ m : GL (Fin 3) B.Carrier,
        L.automorphism = linearConjSL B.Carrier m * graphSL B.Carrier) ∨
      Nonempty (HalfTurnForm B L.automorphism)

/-- Tensor geometry from an explicit paired word and a literal half-turn form.
There is no normalizer, outer-actor or automorphism-coverage premise here. -/
def HalfTurnWordPairing : Prop :=
  ∀ (M : RepeatedModel B σ) (α : MulAut SL(3,B.Carrier)) (H : HalfTurnForm B α),
    let w := (List.replicate M.repetitions M.block).flatten
    0 < naturalCount (w.take H.halfDegree) →
    w.drop H.halfDegree = (w.take H.halfDegree).map (Words.actFactor H.withGraph) →
    Nonempty (PairedTensorCoordinates B σ α)

variable {B σ}

/-- Character invariance gives the exact half-word equation for the actual
coefficient embedding, including graph-field and inner-diagonal twists. -/
theorem HalfTurnForm.word_pair {α : MulAut SL(3,B.Carrier)} (H : HalfTurnForm B α)
    (M : RepeatedModel B σ)
    (hfix : ∀ g, (wordRep M.coefficientEmbedding
      (List.replicate M.repetitions M.block).flatten).character (α g) =
      (wordRep M.coefficientEmbedding
        (List.replicate M.repetitions M.block).flatten).character g) :
    (List.replicate M.repetitions M.block).flatten.drop H.halfDegree =
      ((List.replicate M.repetitions M.block).flatten.take H.halfDegree).map
        (Words.actFactor H.withGraph) := by
  apply Words.drop_eq_map_take_of_character_fixed M.coefficientEmbedding _
    (by rw [repeated_word_length M]; exact B.card_eq) H.matrix H.halfDegree
    ((repeated_word_length M).trans H.degree_eq) H.withGraph
  intro g
  rw [← H.automorphism_eq]
  exact hfix g

/-- The selected half of a natural-containing actual word still contains an
endpoint factor, as required for the eventual dimension bound size ≥ 3. -/
theorem HalfTurnForm.half_naturalCount_pos {α : MulAut SL(3,B.Carrier)}
    (H : HalfTurnForm B α) (M : RepeatedModel B σ)
    (hn : 0 < naturalCount M.block)
    (hfix : ∀ g, (wordRep M.coefficientEmbedding
      (List.replicate M.repetitions M.block).flatten).character (α g) =
      (wordRep M.coefficientEmbedding
        (List.replicate M.repetitions M.block).flatten).character g) :
    0 < naturalCount ((List.replicate M.repetitions M.block).flatten.take H.halfDegree) := by
  apply Words.naturalCount_take_pos _ H.halfDegree H.withGraph (H.word_pair M hfix)
  rw [naturalCount_repeat]
  exact Nat.mul_pos M.repetitions_pos hn

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization
