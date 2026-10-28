module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel2Data
import Mathlib.Tactic.FinCases

/-!
# Reduction of the Rudvalis index-1024 certificate

Free cancellation settles many transition words. The remaining forward
transitions are finite permutation identities. The inverse-generator
transitions follow algebraically, and the word-subgroup transversal theorem
then gives the index.

Source: the ATLAS degree-4060 witnesses documented in `OrderLevel2Data` and
`OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.Level2Reduction
open Theory.GroupTheory
set_option Elab.async false

@[expose] public def push (i : Fin 6) : List (Fin 6) → List (Fin 6)
  | [] => [i]
  | j :: w => if i = L2Inv j then w else i :: j :: w

private theorem push_eval (i : Fin 6) (w : List (Fin 6)) :
    evalWord L2Gen (push i w) = L2Gen i * evalWord L2Gen w := by
  cases w with
  | nil => rfl
  | cons j w =>
    simp only [push]
    split
    · rename_i h
      rw [h, evalWord, L2Inv_spec, ← mul_assoc, inv_mul_cancel, one_mul]
    · rfl

@[expose] public def normalize : List (Fin 6) → List (Fin 6)
  | [] => []
  | i :: w => push i (normalize w)

private theorem normalize_eval (w : List (Fin 6)) :
    evalWord L2Gen (normalize w) = evalWord L2Gen w := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [normalize, push_eval, ih]

private theorem expand_eval (w : List (Fin 4)) :
    evalWord L2Gen (w.flatMap L3GenWord) = evalWord L3Gen w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [List.flatMap_cons, evalWord_append, ← L3Gen_eq_word, ih, evalWord]

@[expose] public def algebraic (i : Fin 6) (r : Fin 1024) : Prop :=
  normalize (i :: L2RepWord r) =
    normalize (L2RepWord (L2Act i r) ++ (L2Factor i r).flatMap L3GenWord)

public instance (i : Fin 6) (r : Fin 1024) : Decidable (algebraic i r) :=
  inferInstanceAs (Decidable (_ = _))

public theorem algebraic_step (i : Fin 6) (r : Fin 1024) (h : algebraic i r) :
    L2Gen i * L2Rep r = L2Rep (L2Act i r) * evalWord L3Gen (L2Factor i r) := by
  have he := congrArg (evalWord L2Gen) h
  simpa only [normalize_eval, evalWord_append, expand_eval, evalWord, L2Rep] using he

@[expose] public def batchRep (b : Fin 256) (r : Fin 4) : Fin 1024 :=
  ⟨4 * b.val + r.val, by omega⟩

@[expose] public def stepBatch (i : Fin 3) (b : Fin 256) : Prop :=
  ∀ r : Fin 4,
    L2Gen (i.castLE (by decide)) * L2Rep (batchRep b r) =
      L2Rep (L2Act (i.castLE (by decide)) (batchRep b r)) *
        evalWord L3Gen (L2Factor (i.castLE (by decide)) (batchRep b r))

@[expose] public def stepBatchCheck (i : Fin 3) (b : Fin 256) : Prop :=
  ∀ r : Fin 4,
    algebraic (i.castLE (by decide)) (batchRep b r) ∨
      checkFin (fun x : Fin 4060 => decide (
        (L2Gen (i.castLE (by decide)) * L2Rep (batchRep b r)) x =
          (L2Rep (L2Act (i.castLE (by decide)) (batchRep b r)) *
            evalWord L3Gen (L2Factor (i.castLE (by decide)) (batchRep b r))) x)) = true

public theorem ofStepBatchCheck (i : Fin 3) (b : Fin 256)
    (h : stepBatchCheck i b) : stepBatch i b := by
  intro r
  rcases h r with ha | hp
  · exact algebraic_step _ _ ha
  · exact Equiv.ext (allFin _ hp)

public theorem positiveStep_of_batches (i : Fin 3) (h : ∀ b, stepBatch i b)
    (r : Fin 1024) :
    L2Gen (i.castLE (by decide)) * L2Rep r =
      L2Rep (L2Act (i.castLE (by decide)) r) *
        evalWord L3Gen (L2Factor (i.castLE (by decide)) r) := by
  let b : Fin 256 := ⟨r.val / 4, by omega⟩
  let s : Fin 4 := ⟨r.val % 4, by omega⟩
  have hrs : batchRep b s = r := by
    apply Fin.ext
    dsimp [batchRep, b, s]
    omega
  simpa only [hrs] using h b s

private def certificateFactor : Fin 6 → Fin 1024 → List (Fin 4)
  | 0 => L2Factor 0
  | 1 => L2Factor 1
  | 2 => L2Factor 2
  | 3 => fun r => (L2Factor 0 (L2Act 3 r)).reverse.map L3Inv
  | 4 => fun r => (L2Factor 1 (L2Act 4 r)).reverse.map L3Inv
  | 5 => fun r => (L2Factor 2 (L2Act 5 r)).reverse.map L3Inv

set_option maxRecDepth 30000 in
private theorem act_inverse : ∀ (i : Fin 3) (r : Fin 1024),
    L2Act (i.castLE (by decide)) (L2Act ⟨i.val + 3, by omega⟩ r) = r := by
  apply allFin₂
  decide +kernel

private theorem inverse_step {G : Type*} [Group G] (g a b f : G)
    (h : g * a = b * f) : g⁻¹ * b = a * f⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq).2
  rw [mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem certificateStep_of_positive
    (h : ∀ (i : Fin 3) (r : Fin 1024),
      L2Gen (i.castLE (by decide)) * L2Rep r =
        L2Rep (L2Act (i.castLE (by decide)) r) *
          evalWord L3Gen (L2Factor (i.castLE (by decide)) r))
    (i : Fin 6) (r : Fin 1024) :
    L2Gen i * L2Rep r = L2Rep (L2Act i r) * evalWord L3Gen (certificateFactor i r) := by
  fin_cases i
  · exact h 0 r
  · exact h 1 r
  · exact h 2 r
  · have hp := h 0 (L2Act 3 r)
    change L2Gen 0 * L2Rep (L2Act 3 r) =
      L2Rep (L2Act 0 (L2Act 3 r)) * evalWord L3Gen (L2Factor 0 (L2Act 3 r)) at hp
    have ha := act_inverse 0 r
    change L2Act 0 (L2Act 3 r) = r at ha
    rw [ha] at hp
    change (L2Gen 0)⁻¹ * L2Rep r = L2Rep (L2Act 3 r) *
      evalWord L3Gen ((L2Factor 0 (L2Act 3 r)).reverse.map L3Inv)
    rw [evalWord_reverse_map_inv L3Gen L3Inv L3Inv_spec]
    exact inverse_step _ _ _ _ hp
  · have hp := h 1 (L2Act 4 r)
    change L2Gen 1 * L2Rep (L2Act 4 r) =
      L2Rep (L2Act 1 (L2Act 4 r)) * evalWord L3Gen (L2Factor 1 (L2Act 4 r)) at hp
    have ha := act_inverse 1 r
    change L2Act 1 (L2Act 4 r) = r at ha
    rw [ha] at hp
    change (L2Gen 1)⁻¹ * L2Rep r = L2Rep (L2Act 4 r) *
      evalWord L3Gen ((L2Factor 1 (L2Act 4 r)).reverse.map L3Inv)
    rw [evalWord_reverse_map_inv L3Gen L3Inv L3Inv_spec]
    exact inverse_step _ _ _ _ hp
  · have hp := h 2 (L2Act 5 r)
    change L2Gen 2 * L2Rep (L2Act 5 r) =
      L2Rep (L2Act 2 (L2Act 5 r)) * evalWord L3Gen (L2Factor 2 (L2Act 5 r)) at hp
    have ha := act_inverse 2 r
    change L2Act 2 (L2Act 5 r) = r at ha
    rw [ha] at hp
    change (L2Gen 2)⁻¹ * L2Rep r = L2Rep (L2Act 5 r) *
      evalWord L3Gen ((L2Factor 2 (L2Act 5 r)).reverse.map L3Inv)
    rw [evalWord_reverse_map_inv L3Gen L3Inv L3Inv_spec]
    exact inverse_step _ _ _ _ hp

/-- The three forward-generator certificates imply the index 1024. -/
public theorem card_step_of_positive
    (h : ∀ (i : Fin 3) (r : Fin 1024),
      L2Gen (i.castLE (by decide)) * L2Rep r =
        L2Rep (L2Act (i.castLE (by decide)) r) *
          evalWord L3Gen (L2Factor (i.castLE (by decide)) r)) :
    Nat.card H2 = 1024 * Nat.card H3 := by
  exact wordSubgroup_card_eq_mul_next
    L2Gen L2Inv L2Inv_spec L3Gen L3Inv L3Inv_spec
    L2Rep L2Act certificateFactor (2 : Fin 4060) L2Point (0 : Fin 1024)
    L2Rep_mem H3_le L2Rep_base L2Rep_point L2Point_injective H3_fix
    (certificateStep_of_positive h)

end Rudvalis.OrderCertificate.Level2Reduction
