module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Geometry.Data

/-!
# Soundness of the two-point representative certificate

The checked recurrence follows the original representative words. Strictly
smaller parent codes justify induction, identifying both stored images with
the actual packed evaluator. The existing word and seventh-power certificates
identify the candidate table without any source-map hypothesis.
Source: ATLAS F23G1-p31671B0; application: GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.Exhaustion.Geometry
open Fi24Prime.Fi23Lift.Certificate
open GeneratorLiftCertificate

/-- Reuse the independently checked twelve-letter word and seventh power. -/
theorem candidateMap_eq_action (x : Fin 31671) : candidateMap x = candidateAction x := by
  have hw : wordMap = wordAction := funext wordMap_eq_evalWord
  rw [(candidate_checks x).1, hw]
  rfl

private theorem bits_nonempty (n : Nat) (hn : n ≠ 0) : n.bits ≠ [] := by
  induction n using Nat.binaryRec' with
  | zero => exact (hn rfl).elim
  | bit b n h ih => rw [Nat.bits_append_bit n b h]; exact List.cons_ne_nil _ _

private theorem bits_step (n p : Nat) (hp : p ≠ 0)
    (he : n = Nat.bit n.bodd p) :
    n.bits.dropLast = n.bodd :: p.bits.dropLast := by
  conv_lhs => rw [he, Nat.bits_append_bit p n.bodd (fun h => (hp h).elim)]
  exact List.dropLast_cons_of_ne_nil (bits_nonempty p hp)

/-- Each record certifies its shorter parent, both images, and separation. -/
def EvaluationCheck (x : Fin 31671) : Prop :=
  (if x = base then
    imageZero x = 0 ∧ imageCandidateZero x = candidateMap 0
  else
    wordCode (parent x) < wordCode x ∧
    wordCode (parent x) ≠ 0 ∧
    wordCode x = Nat.bit (wordCode x).bodd (wordCode (parent x)) ∧
    imageZero x = packedLetter (wordCode x).bodd (imageZero (parent x)) ∧
    imageCandidateZero x = packedLetter (wordCode x).bodd (imageCandidateZero (parent x))) ∧
  (imageCandidateZero x ≠ candidateMap (imageZero x) ∨ x = base)

instance (x : Fin 31671) : Decidable (EvaluationCheck x) := inferInstanceAs (Decidable (_ ∧ _))

/-- The recurrence is enough to certify the unchanged representative evaluator. -/
theorem images_eq_of_checks (h : ∀ x, EvaluationCheck x) (x : Fin 31671) :
    imageZero x = representativeAction x 0 ∧
    imageCandidateZero x = representativeAction x (candidateAction 0) := by
  have aux : ∀ n, ∀ x : Fin 31671, wordCode x = n →
      imageZero x = representativeAction x 0 ∧
      imageCandidateZero x = representativeAction x (candidateAction 0) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hn
      by_cases hx : x = base
      · subst x
        have hb : wordCode base = 1 := by decide +kernel
        simpa only [EvaluationCheck, if_pos rfl, representativeAction, hb,
          Nat.one_bits, List.dropLast_singleton, List.foldr_nil, candidateMap_eq_action, ↓reduceIte]
          using (h base).1
      · have hc := (h x).1
        rw [if_neg hx] at hc
        obtain ⟨hlt, hp, hcode, hzero, hone⟩ := hc
        have hbits := bits_step _ _ hp hcode
        obtain ⟨iz, io⟩ := ih (wordCode (parent x)) (hn ▸ hlt) (parent x) rfl
        simp only [representativeAction, hbits, List.foldr_cons]
        exact ⟨hzero.trans (congrArg _ iz), hone.trans (congrArg _ io)⟩
  exact aux _ x rfl

/-- Completeness of the balanced checker, used after symbolic table transport. -/
theorem checkPow_of_all (f : Nat → Bool) (h : ∀ i, f i = true) (s k : Nat) :
    checkPow f s k = true := by
  induction k generalizing s with
  | zero => exact h s
  | succ k ih => exact checkPow_join f k s (ih s) (ih (s + 2^k))

/-- The table inequality discharges the literal separation Boolean. -/
theorem separation_of_checks (h : ∀ x, EvaluationCheck x) :
    checkPow separationCheck 0 15 = true := by
  apply checkPow_of_all
  intro i
  let x : Fin 31671 := ⟨i % 31671, Nat.mod_lt _ (by decide)⟩
  have he := images_eq_of_checks h x
  have hi := (h x).2
  rw [he.1, he.2, candidateMap_eq_action] at hi
  exact decide_eq_true hi

end Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.Exhaustion.Geometry
