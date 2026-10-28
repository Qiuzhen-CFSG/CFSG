module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Data
import Mathlib.Tactic.FinCases

/-!
# Reduction of the Rudvalis index-4060 certificate

The ATLAS generators have orders 2 and 4. Normalize words in the free product
of these cyclic groups before checking residual identities pointwise. Only the
two forward generators need certificates: their inverses are positive powers.
The resulting transversal bijection gives the cardinality step for the fixed
subgroups in `OrderChainData`.

Witness source: the ATLAS degree-4060 permutations and the untrusted word
witnesses documented in `OrderCertificate/GenerateChain.g`. The finite checks
and the algebraic reduction are proved by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction
open Theory.GroupTheory
set_option maxRecDepth 20000
set_option Elab.async false

private def reducedGen (a b : Equiv.Perm (Fin 4060)) : Fin 4 → Equiv.Perm (Fin 4060)
  | 0 => a
  | 1 => b
  | 2 => b * b
  | 3 => b⁻¹

@[expose] public def push : Fin 4 → List (Fin 4) → List (Fin 4)
  | 0, 0 :: w => w
  | 1, 1 :: w => 2 :: w
  | 1, 2 :: w => 3 :: w
  | 1, 3 :: w => w
  | 2, 1 :: w => 3 :: w
  | 2, 2 :: w => w
  | 2, 3 :: w => 1 :: w
  | 3, 1 :: w => w
  | 3, 2 :: w => 1 :: w
  | 3, 3 :: w => 2 :: w
  | i, w => i :: w

private theorem push_eval (a b : Equiv.Perm (Fin 4060))
    (ha : a * a = 1) (hb : b * b * b = b⁻¹) (i : Fin 4) (w : List (Fin 4)) :
    evalWord (reducedGen a b) (push i w) = reducedGen a b i * evalWord (reducedGen a b) w := by
  have hbi : b⁻¹ * b⁻¹ = b * b := by
    calc
      b⁻¹ * b⁻¹ = (b * b * b) * b⁻¹ := by rw [hb]
      _ = b * b := by simp only [mul_assoc, mul_inv_cancel, mul_one]
  cases w with
  | nil => fin_cases i <;> simp [push, evalWord]
  | cons j w =>
    fin_cases i <;> fin_cases j <;>
      simp [push, reducedGen, evalWord, ← mul_assoc, ha, hb, hbi]

@[expose] public def normalize : List (Fin 4) → List (Fin 4)
  | [] => []
  | i :: w => push i (normalize w)

private theorem normalize_eval (a b : Equiv.Perm (Fin 4060))
    (ha : a * a = 1) (hb : b * b * b = b⁻¹) (w : List (Fin 4)) :
    evalWord (reducedGen a b) (normalize w) = evalWord (reducedGen a b) w := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [normalize, push_eval a b ha hb, ih]

@[expose] public def reduceLetter : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 3

private theorem genA_square : L0G0 * L0G0 = 1 := by
  simpa only [L0G0, pow_two] using aPerm_sq

private theorem genB_cube : L0G1 * L0G1 * L0G1 = L0G1⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simpa only [L0G1, pow_succ, pow_zero, one_mul] using bPerm_fourth

private theorem reducedGen_letter (i : Fin 4) :
    reducedGen L0G0 L0G1 (reduceLetter i) = L0Gen i := by
  have ha : L0G0⁻¹ = L0G0 := (inv_eq_of_mul_eq_one_left genA_square).symm
  fin_cases i <;> simp [reduceLetter, reducedGen, L0Gen, ha]

private theorem reduceWord_eval (w : List (Fin 4)) :
    evalWord (reducedGen L0G0 L0G1) (w.map reduceLetter) = evalWord L0Gen w := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.map_cons, evalWord, reducedGen_letter, ih]

@[expose] public def reducedWord (w : List (Fin 4)) : List (Fin 4) := normalize (w.map reduceLetter)

private theorem reducedWord_eval (w : List (Fin 4)) :
    evalWord (reducedGen L0G0 L0G1) (reducedWord w) = evalWord L0Gen w := by
  rw [reducedWord, normalize_eval _ _ genA_square genB_cube, reduceWord_eval]

private theorem expand_eval (w : List (Fin 4)) :
    evalWord L0Gen (w.flatMap L1GenWord) = evalWord L1Gen w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [List.flatMap_cons, evalWord_append, ← L1Gen_eq_word, ih, evalWord]

@[expose] public def algebraic (i : Fin 4) (r : Fin 4060) : Prop :=
  reducedWord (i :: L0RepWord r) =
    reducedWord (L0RepWord (L0Act i r) ++ (L0Factor i r).flatMap L1GenWord)

public instance (i : Fin 4) (r : Fin 4060) : Decidable (algebraic i r) :=
  inferInstanceAs (Decidable (_ = _))

private theorem algebraic_step (i : Fin 4) (r : Fin 4060) (h : algebraic i r) :
    L0Gen i * L0Rep r = L0Rep (L0Act i r) * evalWord L1Gen (L0Factor i r) := by
  have he := congrArg (evalWord (reducedGen L0G0 L0G1)) h
  simpa only [reducedWord_eval, evalWord_append, expand_eval, evalWord, L0Rep] using he

@[expose] public def batchRep (b : Fin 203) (r : Fin 20) : Fin 4060 :=
  ⟨20 * b.val + r.val, by omega⟩

@[expose] public def stepBatch (b : Fin 203) : Prop :=
  ∀ (i : Fin 2) (r : Fin 20),
    L0Gen (i.castLE (by decide)) * L0Rep (batchRep b r) =
      L0Rep (L0Act (i.castLE (by decide)) (batchRep b r)) * evalWord L1Gen (L0Factor (i.castLE (by decide)) (batchRep b r))

/-- A single transition check, kept separate to bound kernel reduction memory. -/
@[expose] public def stepCheck (i : Fin 2) (r : Fin 4060) : Prop :=
  algebraic (i.castLE (by decide)) r ∨ checkFin (fun x : Fin 4060 => decide (
    (L0Gen (i.castLE (by decide)) * L0Rep r) x =
      (L0Rep (L0Act (i.castLE (by decide)) r) *
        evalWord L1Gen (L0Factor (i.castLE (by decide)) r)) x)) = true

public instance (i : Fin 2) (r : Fin 4060) : Decidable (stepCheck i r) :=
  inferInstanceAs (Decidable (_ ∨ _))

public theorem ofStepCheck (i : Fin 2) (r : Fin 4060) (h : stepCheck i r) :
    L0Gen (i.castLE (by decide)) * L0Rep r =
      L0Rep (L0Act (i.castLE (by decide)) r) *
        evalWord L1Gen (L0Factor (i.castLE (by decide)) r) := by
  rcases h with ha | hp
  · exact algebraic_step (i.castLE (by decide)) r ha
  · exact Equiv.ext (allFin _ hp)

@[expose] public def stepBatchCheck (b : Fin 203) : Prop :=
  ∀ (i : Fin 2) (r : Fin 20), stepCheck i (batchRep b r)

public theorem ofStepBatchCheck (b : Fin 203) (h : stepBatchCheck b) : stepBatch b :=
  fun i r => ofStepCheck i (batchRep b r) (h i r)

private def certificateAct : Fin 4 → Fin 4060 → Fin 4060
  | 0 => L0Act 0
  | 1 => L0Act 1
  | 2 => L0Act 0
  | 3 => fun r => L0Act 1 (L0Act 1 (L0Act 1 r))

private def certificateFactor : Fin 4 → Fin 4060 → List (Fin 4)
  | 0 => L0Factor 0
  | 1 => L0Factor 1
  | 2 => L0Factor 0
  | 3 => fun r => L0Factor 1 (L0Act 1 (L0Act 1 r)) ++
      L0Factor 1 (L0Act 1 r) ++ L0Factor 1 r

private theorem certificateStep_of_positive
    (h : ∀ (i : Fin 2) (r : Fin 4060),
      L0Gen (i.castLE (by decide)) * L0Rep r =
        L0Rep (L0Act (i.castLE (by decide)) r) * evalWord L1Gen (L0Factor (i.castLE (by decide)) r))
    (i : Fin 4) (r : Fin 4060) :
    L0Gen i * L0Rep r = L0Rep (certificateAct i r) * evalWord L1Gen (certificateFactor i r) := by
  have h0 (r : Fin 4060) := h 0 r
  have h1 (r : Fin 4060) := h 1 r
  change ∀ r, L0Gen 0 * L0Rep r = L0Rep (L0Act 0 r) * evalWord L1Gen (L0Factor 0 r) at h0
  change ∀ r, L0Gen 1 * L0Rep r = L0Rep (L0Act 1 r) * evalWord L1Gen (L0Factor 1 r) at h1
  fin_cases i
  · exact h0 r
  · exact h1 r
  · have ha : L0G0⁻¹ = L0G0 := (inv_eq_of_mul_eq_one_left genA_square).symm
    change L0G0⁻¹ * L0Rep r = _
    rw [ha]
    exact h0 r
  · have hb : L0Gen 3 = L0Gen 1 * L0Gen 1 * L0Gen 1 := genB_cube.symm
    simp only [certificateAct, certificateFactor]
    change L0Gen 3 * L0Rep r = _
    have h2 (s : Fin 4060) :
        (L0Gen 1 * L0Gen 1) * L0Rep s = L0Rep (L0Act 1 (L0Act 1 s)) *
          (evalWord L1Gen (L0Factor 1 (L0Act 1 s)) * evalWord L1Gen (L0Factor 1 s)) := by
      rw [mul_assoc, h1, ← mul_assoc, h1, mul_assoc]
    rw [hb, mul_assoc, h1, ← mul_assoc, h2]
    simp only [evalWord_append, mul_assoc]


/-- Forward transitions suffice, since the generators have orders 2 and 4. -/
public theorem card_step_of_positive
    (h : ∀ (i : Fin 2) (r : Fin 4060),
      L0Gen (i.castLE (by decide)) * L0Rep r =
        L0Rep (L0Act (i.castLE (by decide)) r) * evalWord L1Gen (L0Factor (i.castLE (by decide)) r)) :
    Nat.card H0 = 4060 * Nat.card H1 := by
  exact wordSubgroup_card_eq_mul_next
    L0Gen L0Inv L0Inv_spec L1Gen L1Inv L1Inv_spec
    L0Rep certificateAct certificateFactor (0 : Fin 4060) L0Point (0 : Fin 4060)
    L0Rep_mem H1_le L0Rep_base L0Rep_point L0Point_injective H1_fix
    (certificateStep_of_positive h)

/-- The bounded transition batches cover all representatives. -/
public theorem card_step_of_batches (h : ∀ b : Fin 203, stepBatch b) :
    Nat.card H0 = 4060 * Nat.card H1 := by
  apply card_step_of_positive
  intro i r
  let b : Fin 203 := ⟨r.val / 20, by omega⟩
  let s : Fin 20 := ⟨r.val % 20, by omega⟩
  have hrs : batchRep b s = r := by
    apply Fin.ext
    dsimp [batchRep, b, s]
    omega
  simpa only [hrs] using h b i s

/-- Seven independent parts, each with 29 batches, suffice for the index. -/
public theorem card_step_of_parts
    (h : ∀ (k : Fin 7) (b : Fin 29), stepBatch ⟨7 * b.val + k.val, by omega⟩) :
    Nat.card H0 = 4060 * Nat.card H1 := by
  apply card_step_of_batches
  intro b
  let k : Fin 7 := ⟨b.val % 7, by omega⟩
  let q : Fin 29 := ⟨b.val / 7, by omega⟩
  have hb : (⟨7 * q.val + k.val, by omega⟩ : Fin 203) = b := by
    apply Fin.ext
    dsimp [k, q]
    omega
  simpa only [hb] using h k q

end Rudvalis.OrderCertificate.ForwardReduction
