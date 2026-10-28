module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel1Data
import Mathlib.Tactic.FinCases

/-!
# Reducing the Rudvalis index-1755 certificate to forward transitions

Free cancellation proves the transitions that are literal word identities.
The remaining forward transitions may be checked pointwise in bounded batches.
Inverse transitions follow from forward transitions at the inverse orbit image;
we use the reversed inverse factor word, so no second permutation check is needed.
The word-subgroup bijection then gives the index 1755.

Source: the ATLAS degree-4060 witnesses documented in `OrderLevel1Data` and
`OrderCertificate/GenerateChain.g`. The orbit inverse identity is kernel checked.
-/

namespace Rudvalis.OrderCertificate.Level1Reduction
open Theory.GroupTheory
set_option Elab.async false

@[expose] public def push (i : Fin 4) : List (Fin 4) → List (Fin 4)
  | [] => [i]
  | j :: w => if i = L1Inv j then w else i :: j :: w

private theorem push_eval (i : Fin 4) (w : List (Fin 4)) :
    evalWord L1Gen (push i w) = L1Gen i * evalWord L1Gen w := by
  cases w with
  | nil => rfl
  | cons j w =>
    simp only [push]
    split
    · rename_i h
      rw [h, evalWord, L1Inv_spec, ← mul_assoc, inv_mul_cancel, one_mul]
    · rfl

@[expose] public def normalize : List (Fin 4) → List (Fin 4)
  | [] => []
  | i :: w => push i (normalize w)

private theorem normalize_eval (w : List (Fin 4)) :
    evalWord L1Gen (normalize w) = evalWord L1Gen w := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [normalize, push_eval, ih]

private theorem expand_eval (w : List (Fin 6)) :
    evalWord L1Gen (w.flatMap L2GenWord) = evalWord L2Gen w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [List.flatMap_cons, evalWord_append, ← L2Gen_eq_word, ih, evalWord]

@[expose] public def algebraic (i : Fin 4) (r : Fin 1755) : Prop :=
  normalize (i :: L1RepWord r) =
    normalize (L1RepWord (L1Act i r) ++ (L1Factor i r).flatMap L2GenWord)

public instance (i : Fin 4) (r : Fin 1755) : Decidable (algebraic i r) :=
  inferInstanceAs (Decidable (_ = _))

public theorem algebraic_step (i : Fin 4) (r : Fin 1755) (h : algebraic i r) :
    L1Gen i * L1Rep r = L1Rep (L1Act i r) * evalWord L2Gen (L1Factor i r) := by
  have he := congrArg (evalWord L1Gen) h
  simpa only [normalize_eval, evalWord_append, expand_eval, evalWord, L1Rep] using he

@[expose] public def batchRep (b : Fin 351) (r : Fin 5) : Fin 1755 :=
  ⟨5 * b.val + r.val, by omega⟩

@[expose] public def stepBatch (i : Fin 2) (b : Fin 351) : Prop :=
  ∀ r : Fin 5,
    L1Gen (i.castLE (by decide)) * L1Rep (batchRep b r) =
      L1Rep (L1Act (i.castLE (by decide)) (batchRep b r)) *
        evalWord L2Gen (L1Factor (i.castLE (by decide)) (batchRep b r))

@[expose] public def stepBatchCheck (i : Fin 2) (b : Fin 351) : Prop :=
  ∀ r : Fin 5,
    algebraic (i.castLE (by decide)) (batchRep b r) ∨
      checkFin (fun x : Fin 4060 => decide (
        (L1Gen (i.castLE (by decide)) * L1Rep (batchRep b r)) x =
          (L1Rep (L1Act (i.castLE (by decide)) (batchRep b r)) *
            evalWord L2Gen (L1Factor (i.castLE (by decide)) (batchRep b r))) x)) = true

public theorem ofStepBatchCheck (i : Fin 2) (b : Fin 351)
    (h : stepBatchCheck i b) : stepBatch i b := by
  intro r
  rcases h r with ha | hp
  · exact algebraic_step _ _ ha
  · exact Equiv.ext (allFin _ hp)

public theorem positiveStep_of_batches (i : Fin 2) (h : ∀ b, stepBatch i b)
    (r : Fin 1755) :
    L1Gen (i.castLE (by decide)) * L1Rep r =
      L1Rep (L1Act (i.castLE (by decide)) r) *
        evalWord L2Gen (L1Factor (i.castLE (by decide)) r) := by
  let b : Fin 351 := ⟨r.val / 5, by omega⟩
  let s : Fin 5 := ⟨r.val % 5, by omega⟩
  have hrs : batchRep b s = r := by
    apply Fin.ext
    dsimp [batchRep, b, s]
    omega
  simpa only [hrs] using h b s

private def certificateFactor : Fin 4 → Fin 1755 → List (Fin 6)
  | 0 => L1Factor 0
  | 1 => L1Factor 1
  | 2 => fun r => (L1Factor 0 (L1Act 2 r)).reverse.map L2Inv
  | 3 => fun r => (L1Factor 1 (L1Act 3 r)).reverse.map L2Inv

set_option maxRecDepth 30000 in
private theorem act_inverse : ∀ (i : Fin 2) (r : Fin 1755),
    L1Act (i.castLE (by decide)) (L1Act ⟨i.val + 2, by omega⟩ r) = r := by
  apply allFin₂
  decide +kernel

private theorem inverse_step {G : Type*} [Group G] (g a b f : G)
    (h : g * a = b * f) : g⁻¹ * b = a * f⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq).2
  rw [mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem certificateStep_of_positive
    (h : ∀ (i : Fin 2) (r : Fin 1755),
      L1Gen (i.castLE (by decide)) * L1Rep r =
        L1Rep (L1Act (i.castLE (by decide)) r) *
          evalWord L2Gen (L1Factor (i.castLE (by decide)) r))
    (i : Fin 4) (r : Fin 1755) :
    L1Gen i * L1Rep r = L1Rep (L1Act i r) * evalWord L2Gen (certificateFactor i r) := by
  fin_cases i
  · exact h 0 r
  · exact h 1 r
  · have hp := h 0 (L1Act 2 r)
    change L1Gen 0 * L1Rep (L1Act 2 r) =
      L1Rep (L1Act 0 (L1Act 2 r)) * evalWord L2Gen (L1Factor 0 (L1Act 2 r)) at hp
    have ha := act_inverse 0 r
    change L1Act 0 (L1Act 2 r) = r at ha
    rw [ha] at hp
    change (L1Gen 0)⁻¹ * L1Rep r = L1Rep (L1Act 2 r) *
      evalWord L2Gen ((L1Factor 0 (L1Act 2 r)).reverse.map L2Inv)
    rw [evalWord_reverse_map_inv L2Gen L2Inv L2Inv_spec]
    exact inverse_step _ _ _ _ hp
  · have hp := h 1 (L1Act 3 r)
    change L1Gen 1 * L1Rep (L1Act 3 r) =
      L1Rep (L1Act 1 (L1Act 3 r)) * evalWord L2Gen (L1Factor 1 (L1Act 3 r)) at hp
    have ha := act_inverse 1 r
    change L1Act 1 (L1Act 3 r) = r at ha
    rw [ha] at hp
    change (L1Gen 1)⁻¹ * L1Rep r = L1Rep (L1Act 3 r) *
      evalWord L2Gen ((L1Factor 1 (L1Act 3 r)).reverse.map L2Inv)
    rw [evalWord_reverse_map_inv L2Gen L2Inv L2Inv_spec]
    exact inverse_step _ _ _ _ hp

/-- Only the two forward-generator certificates remain computational inputs. -/
public theorem card_step_of_positive
    (h : ∀ (i : Fin 2) (r : Fin 1755),
      L1Gen (i.castLE (by decide)) * L1Rep r =
        L1Rep (L1Act (i.castLE (by decide)) r) *
          evalWord L2Gen (L1Factor (i.castLE (by decide)) r)) :
    Nat.card H1 = 1755 * Nat.card H2 := by
  exact wordSubgroup_card_eq_mul_next
    L1Gen L1Inv L1Inv_spec L2Gen L2Inv L2Inv_spec
    L1Rep L1Act certificateFactor (1 : Fin 4060) L1Point (0 : Fin 1755)
    L1Rep_mem H2_le L1Rep_base L1Rep_point L1Point_injective H2_fix
    (certificateStep_of_positive h)

end Rudvalis.OrderCertificate.Level1Reduction
