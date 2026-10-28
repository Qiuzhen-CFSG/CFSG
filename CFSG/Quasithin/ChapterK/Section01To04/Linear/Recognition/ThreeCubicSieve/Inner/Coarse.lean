module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Inner.Reduction
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Inner.Coarse.Geometry
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Inner.Coarse.WordArithmetic
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Inner.Coarse.TensorFixed

/-!
# The inner SL₃ parabolic degree bound

An elementary offender saturates to a full point or line root plane with
fixed codimension at most 4r. The repeated model has exactly r Frobenius
positions; a non-small positive word has at least two natural/dual factors
or an adjoint factor. Its actual scalar-extension equivalence transports a
half-degree estimate for that root plane to the binary representation,
yielding the bound 8r.

The concrete tensor common-fixed-space estimate discharges the final input in
`finrank_le_eight_mul_of_inner_actor`. No faithfulness, central-kernel or cubicity
hypothesis is needed: the actor is already a nontrivial elementary subgroup of
the literal SL₃ cover. The earlier conditional assembly interfaces are retained.

Source: Guralnick–Malle, Classification of 2F-modules II, author manuscript
Lemma 2.1 and Proposition 4.7, pp.5–6 and 25–26; Aschbacher–Smith K.3.2,
printed pp.454–456. Opposite parabolics are not identified by inner conjugacy.
-/

@[expose] public section
noncomputable section
open Representation Representation.BinaryOffender
open Representation.SL3.BinaryDefiningFactors
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Matrix.PSL3.RootPlaneGeometry
open scoped MatrixGroups TensorProduct

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Inner

variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V) [IsIrreducible σ]

/-- The full repeated word has exactly the field degree many Frobenius positions. -/
theorem repeated_word_length (M : RepeatedModel B σ) :
    (List.replicate M.repetitions M.block).flatten.length = B.degree := by
  rw [List.length_flatten]
  simp only [List.map_replicate, List.sum_replicate, M.block_length, nsmul_eq_mul,
    Nat.cast_id]
  rw [M.field_degree, Nat.mul_comm]

/-- Non-small positive words have enough nontrivial factors for the parabolic
half-degree estimate. Trivial positions and dual labels are retained. -/
theorem repeated_word_large (M : RepeatedModel B σ)
    (hp : 0 < naturalCount M.block + adjointCount M.block) (hn : ¬ M.Small) :
    2 ≤ naturalCount (List.replicate M.repetitions M.block).flatten ∨
      0 < adjointCount (List.replicate M.repetitions M.block).flatten := by
  rw [naturalCount_repeat, adjointCount_repeat]
  by_cases hb : adjointCount M.block = 0
  · left
    have ha : 1 ≤ naturalCount M.block := by omega
    by_cases ht : M.repetitions = 1
    · rw [ht, one_mul]
      by_contra hh
      exact hn ⟨by omega, hb, Or.inl ht⟩
    · have ht2 : 2 ≤ M.repetitions := by have := M.repetitions_pos; omega
      have hm := Nat.mul_le_mul ht2 ha
      simpa only [mul_one] using hm
  · right
    exact Nat.mul_pos M.repetitions_pos (by omega)

/-- Conditional assembly from the literal root-plane half-degree estimate.
Its input concerns a tensor fixed space, not an offender or a binary degree
bound. No kernel or faithfulness hypothesis is needed for this deduction. -/
theorem finrank_le_eight_mul_of_rootPlane_half_bound (M : RepeatedModel B σ)
    (hhalf : ∀ point : Bool,
      Module.finrank (SplittingField σ)
        (WordSpace (SplittingField σ) (List.replicate M.repetitions M.block).flatten) ≤
      2 * Module.finrank (SplittingField σ)
        (WordSpace (SplittingField σ) (List.replicate M.repetitions M.block).flatten ⧸
          invariants ((wordRep M.coefficientEmbedding
            (List.replicate M.repetitions M.block).flatten).comp
              (rootPlaneSL B.Carrier point).subtype)))
    (E : Subgroup SL(3,B.Carrier)) (hE : IsElementaryTwo E)
    (hd : fixedCodim σ E ≤ 2 * rank E) :
    Module.finrank (ZMod 2) V ≤ 8 * B.degree := by
  obtain ⟨point,hpoint⟩ := Coarse.exists_rootPlane_small_codim B.Carrier
    B.degree_pos B.card_eq σ E hE hd
  have hc := fixedCodim_eq_of_splitting_equiv B σ M.equiv (rootPlaneSL B.Carrier point)
  have htotal : Module.finrank (ZMod 2) V = schurDegree σ *
      Module.finrank (SplittingField σ)
        (WordSpace (SplittingField σ) (List.replicate M.repetitions M.block).flatten) := by
    rw [finrank_wordSpace, wordDegree_repeat]
    exact M.finrank_eq
  have hs := Nat.mul_le_mul_left (schurDegree σ) (hhalf point)
  rw [← htotal] at hs
  nlinarith

/-- A concrete `2^(a+b)` upper bound on both root-plane fixed spaces is
sufficient. The numerical half-degree step and scalar transport are discharged
here; the input still needs a proof on the actual tensor action. -/
theorem finrank_le_eight_mul_of_rootPlane_fixed_bound (M : RepeatedModel B σ)
    (hp : 0 < naturalCount M.block + adjointCount M.block) (hn : ¬ M.Small)
    (hfixed : ∀ point : Bool,
      Module.finrank (SplittingField σ)
        (invariants ((wordRep M.coefficientEmbedding
          (List.replicate M.repetitions M.block).flatten).comp
            (rootPlaneSL B.Carrier point).subtype)) ≤
        2 ^ (naturalCount (List.replicate M.repetitions M.block).flatten +
          adjointCount (List.replicate M.repetitions M.block).flatten))
    (E : Subgroup SL(3,B.Carrier)) (hE : IsElementaryTwo E)
    (hd : fixedCodim σ E ≤ 2 * rank E) :
    Module.finrank (ZMod 2) V ≤ 8 * B.degree := by
  apply finrank_le_eight_mul_of_rootPlane_half_bound B σ M _ E hE hd
  intro point
  exact Coarse.half_degree_of_word_fixed_bound M.coefficientEmbedding _ _
    (repeated_word_large B σ M hp hn) (hfixed point)

/-- Uniform assembly contract for a word estimate. The period and
non-small hypotheses of that estimate are proved from the supplied model here.
The unconditional theorem below supplies `hword` on the concrete action. -/
theorem finrank_le_eight_mul_of_word_estimate
    (hword : ∀ (ι : B.Carrier →+* SplittingField σ) (w : List Factor),
      w.length = B.degree → (2 ≤ naturalCount w ∨ 0 < adjointCount w) →
      ∀ point : Bool, Module.finrank (SplittingField σ) (WordSpace (SplittingField σ) w) ≤
        2 * Module.finrank (SplittingField σ)
          (WordSpace (SplittingField σ) w ⧸
            invariants ((wordRep ι w).comp (rootPlaneSL B.Carrier point).subtype)))
    (M : RepeatedModel B σ)
    (hp : 0 < naturalCount M.block + adjointCount M.block) (hn : ¬ M.Small)
    (E : Subgroup SL(3,B.Carrier)) (hE : IsElementaryTwo E)
    (hd : fixedCodim σ E ≤ 2 * rank E) :
    Module.finrank (ZMod 2) V ≤ 8 * B.degree :=
  finrank_le_eight_mul_of_rootPlane_half_bound B σ M
    (hword M.coefficientEmbedding _ (repeated_word_length B σ M)
      (repeated_word_large B σ M hp hn)) E hE hd

/-- An elementary inner offender on a non-small positive repeated word forces
binary degree at most eight times the group-field degree. This supplies exactly
the degree premise of `inner_word_estimate_of_degree_and_adjoint`; the actual
root-plane fixed-space estimate, word conditions and scalar transport are all
discharged here. The independent strict adjoint estimate remains with that
source-theorem assembly. -/
theorem finrank_le_eight_mul_of_inner_actor (M : RepeatedModel B σ)
    (hp : 0 < naturalCount M.block + adjointCount M.block) (hn : ¬ M.Small)
    (E : Subgroup SL(3,B.Carrier)) (hE : IsElementaryTwo E)
    (hd : fixedCodim σ E ≤ 2 * rank E) :
    Module.finrank (ZMod 2) V ≤ 8 * B.degree :=
  finrank_le_eight_mul_of_word_estimate B σ
    (fun ι w hlen hlarge side =>
      Coarse.word_rootPlane_half_degree ι B.degree B.card_eq w hlen hlarge side)
    M hp hn E hE hd

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Inner
