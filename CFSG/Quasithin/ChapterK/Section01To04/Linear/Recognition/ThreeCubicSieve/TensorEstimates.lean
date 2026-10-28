module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Actors
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.AbsoluteExhaustion

/-!
# Repeated tensor words and the two remaining actor estimates

A repeated model is an actual equivalence after extending the commuting
endomorphism field, with its exact Frobenius period. The existing absolute
exhaustion theorem constructs it without a degree bound. Its small patterns
are a single natural or dual factor, repeated once or twice. The inner and
outer estimates below are separate proof obligations on the common fixed
space of an elementary actor; neither estimate is asserted here.

The conditional deduction uses the actual cubic actor and excludes all other
word patterns. It is not an unconditional classification: the two estimates
still have to be proved, including the trace-zero adjoint case at degree 8r.

Source: Aschbacher–Smith K.3.2, printed pp.454–456, citing GM04 Proposition
4.6/Table 7. The available GM author manuscript separates the inner and outer
arguments as Propositions 4.7 and 4.8, pp.25–28, with Lemma 4.5, pp.23–24.
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve

open Representation Representation.BinaryOffender
open Representation.SL3.BinaryDefiningFactors
open ChapterB.QuasisimpleSource
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.AbsoluteExhaustion
open scoped TensorProduct MatrixGroups

variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V) [IsIrreducible σ]

/-- Actual scalar-extension data and its proved field-of-definition period.
It contains no degree estimate or actor estimate. -/
structure RepeatedModel where
  coefficientEmbedding : B.Carrier →+* SplittingField σ
  repetitions : ℕ
  block : List Factor
  repetitions_pos : 0 < repetitions
  block_length : block.length = schurDegree σ
  field_degree : B.degree = schurDegree σ * repetitions
  equiv : (extendScalars (SplittingField σ) σ.endFieldRep).Equiv
    (wordRep coefficientEmbedding (List.replicate repetitions block).flatten)

/-- The model is supplied by the proved tensor-word catalogue and period
arithmetic, without any cubic, faithfulness or dimension premise. -/
theorem repeatedModel_nonempty : Nonempty (RepeatedModel B σ) := by
  obtain ⟨ι, t, b, ht, hb, hn, ⟨e⟩⟩ :=
    exists_repeated_word_model σ B.degree B.degree_pos B.card_eq
  exact ⟨⟨ι, t, b, ht, hb, hn, e⟩⟩

namespace RepeatedModel
variable {B σ} (M : RepeatedModel B σ)

/-- The two exceptional word patterns retain duality in the actual word. -/
def Small : Prop :=
  naturalCount M.block = 1 ∧ adjointCount M.block = 0 ∧
    (M.repetitions = 1 ∨ M.repetitions = 2)

/-- The binary degree follows from the actual scalar-extension equivalence. -/
theorem finrank_eq : Module.finrank (ZMod 2) V =
    schurDegree σ * (3 ^ naturalCount M.block * 8 ^ adjointCount M.block) ^
      M.repetitions :=
  finrank_of_repeated_word_model σ M.coefficientEmbedding M.block M.repetitions ⟨M.equiv⟩

/-- Nontriviality of the original action excludes the all-trivial word. -/
theorem counts_pos (hact : ∃ g, σ g ≠ 1) :
    0 < naturalCount M.block + adjointCount M.block :=
  counts_pos_of_repeated_word_model σ hact M.coefficientEmbedding M.block
    M.repetitions ⟨M.equiv⟩

/-- Both exceptional patterns give the strict degree window needed by K.3.2. -/
theorem finrank_lt_eight_mul (hsmall : M.Small) :
    Module.finrank (ZMod 2) V < 8 * B.degree := by
  obtain ⟨ha, hb, ht | ht⟩ := hsmall
  · have hd := M.finrank_eq
    have hn := M.field_degree
    have hs := schurDegree_pos σ
    simp only [ha, hb, ht, pow_one, pow_zero, mul_one] at hd hn
    omega
  · have hd := M.finrank_eq
    have hn := M.field_degree
    have hs := schurDegree_pos σ
    norm_num [ha, hb, ht] at hd hn
    omega

end RepeatedModel

/-- Inner-actor fixed-space contract on nonexceptional tensor words. The
inclusion refers to the actual image, allowing a nonfaithful SL₃ cover. -/
def InnerWordEstimate : Prop :=
  ∀ M : RepeatedModel B σ,
    0 < naturalCount M.block + adjointCount M.block → ¬ M.Small →
    ∀ A : Subgroup (linearNormalizer σ), IsElementaryTwo A →
      IsCubic (normalizerRepresentation σ) A →
      A.map (linearNormalizer σ).subtype ≤ actionImage σ →
      2 * rank A < fixedCodim (normalizerRepresentation σ) A

/-- Independent outer-actor contract. It retains the original actor rank
bound, but does not assume a bound on the dimension of the representation. -/
def OuterWordEstimate : Prop :=
  ∀ M : RepeatedModel B σ,
    0 < naturalCount M.block + adjointCount M.block → ¬ M.Small →
    ∀ A : Subgroup (linearNormalizer σ), IsElementaryTwo A →
      IsCubic (normalizerRepresentation σ) A → rank A ≤ 2 * B.degree →
      ¬ A.map (linearNormalizer σ).subtype ≤ actionImage σ →
      2 * rank A < fixedCodim (normalizerRepresentation σ) A

/-- A genuine small cubic actor rules out every other word pattern once the
two independent common-fixed-space estimates are supplied. -/
theorem small_of_actor_estimates
    (hinner : InnerWordEstimate B σ) (houter : OuterWordEstimate B σ)
    (hact : ∃ g, σ g ≠ 1) (M : RepeatedModel B σ)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hc : IsCubic (normalizerRepresentation σ) A) (hr : rank A ≤ 2 * B.degree)
    (hd : fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A) : M.Small := by
  by_contra hn
  have hp := M.counts_pos hact
  by_cases hi : A.map (linearNormalizer σ).subtype ≤ actionImage σ
  · exact (not_lt_of_ge hd) (hinner M hp hn A hA hc hi)
  · exact (not_lt_of_ge hd) (houter M hp hn A hA hc hr hi)

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve
