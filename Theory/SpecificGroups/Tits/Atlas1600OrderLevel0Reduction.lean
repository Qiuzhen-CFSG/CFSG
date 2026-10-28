module

public import Theory.SpecificGroups.Tits.Atlas1600OrderLevel0Data
import Mathlib.Tactic.FinCases

/-!
# The 1600-point stabilizer-chain step in the Atlas degree-1600 model

The representatives have distinct images of base point 0. Multiplication by each
signed generator factors through another representative and the level-1 subgroup.
The word-subgroup bijection therefore gives `Nat.card H0 = 1600 * Nat.card H1`.

Most forward transitions follow by word reduction using the generator orders 2
and 3. The remaining identities are checked pointwise by the kernel, in 80
sequential batches of 20 representatives. The inverse transitions follow
algebraically from the forward transitions. These two reductions avoid redundant
checks of the same permutation identities.

The witnesses originate from the Atlas permutations in
`refs/original/n-group-global/atlas-tits-p1600-{a,b}.g`.
-/

namespace Tits.Atlas1600OrderCertificate.ForwardReduction
open Theory.GroupTheory
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000
set_option Elab.async false

private def reducedGen (a b : Equiv.Perm (Fin 1600)) : Fin 3 → Equiv.Perm (Fin 1600)
  | 0 => a
  | 1 => b
  | 2 => b⁻¹

@[expose] public def push : Fin 3 → List (Fin 3) → List (Fin 3)
  | 0, 0 :: w => w
  | 1, 1 :: w => 2 :: w
  | 2, 2 :: w => 1 :: w
  | 1, 2 :: w => w
  | 2, 1 :: w => w
  | i, w => i :: w

private theorem push_eval (a b : Equiv.Perm (Fin 1600))
    (ha : a * a = 1) (hb : b * b = b⁻¹) (i : Fin 3) (w : List (Fin 3)) :
    evalWord (reducedGen a b) (push i w) = reducedGen a b i * evalWord (reducedGen a b) w := by
  have hbi : b⁻¹ * b⁻¹ = b := by
    simpa using (congrArg Inv.inv hb)
  cases w with
  | nil => fin_cases i <;> simp [push, evalWord]
  | cons j w =>
    fin_cases i <;> fin_cases j <;>
      simp [push, reducedGen, evalWord, ← mul_assoc, ha, hb, hbi]

@[expose] public def normalize : List (Fin 3) → List (Fin 3)
  | [] => []
  | i :: w => push i (normalize w)

private theorem normalize_eval (a b : Equiv.Perm (Fin 1600))
    (ha : a * a = 1) (hb : b * b = b⁻¹) (w : List (Fin 3)) :
    evalWord (reducedGen a b) (normalize w) = evalWord (reducedGen a b) w := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [normalize, push_eval a b ha hb, ih]

@[expose] public def reduceLetter : Fin 4 → Fin 3
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 2

private theorem genA_square : L0G0 * L0G0 = 1 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem genB_square : L0G1 * L0G1 = L0G1⁻¹ := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem reducedGen_letter (i : Fin 4) :
    reducedGen L0G0 L0G1 (reduceLetter i) = L0Gen i := by
  have ha : L0G0⁻¹ = L0G0 := (inv_eq_of_mul_eq_one_left genA_square).symm
  fin_cases i <;> simp [reduceLetter, reducedGen, L0Gen, ha]

private theorem reduceWord_eval (w : List (Fin 4)) :
    evalWord (reducedGen L0G0 L0G1) (w.map reduceLetter) = evalWord L0Gen w := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.map_cons, evalWord, reducedGen_letter, ih]

@[expose] public def reducedWord (w : List (Fin 4)) : List (Fin 3) := normalize (w.map reduceLetter)

private theorem reducedWord_eval (w : List (Fin 4)) :
    evalWord (reducedGen L0G0 L0G1) (reducedWord w) = evalWord L0Gen w := by
  rw [reducedWord, normalize_eval _ _ genA_square genB_square, reduceWord_eval]

private theorem expand_eval (w : List (Fin 6)) :
    evalWord L0Gen (w.flatMap L1GenWord) = evalWord L1Gen w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [List.flatMap_cons, evalWord_append, ← L1Gen_eq_word, ih, evalWord]

@[expose] public def algebraic (i : Fin 4) (r : Fin 1600) : Prop :=
  reducedWord (i :: L0RepWord r) =
    reducedWord (L0RepWord (L0Act i r) ++ (L0Factor i r).flatMap L1GenWord)

public instance (i : Fin 4) (r : Fin 1600) : Decidable (algebraic i r) :=
  inferInstanceAs (Decidable (_ = _))

private theorem algebraic_step (i : Fin 4) (r : Fin 1600) (h : algebraic i r) :
    L0Gen i * L0Rep r = L0Rep (L0Act i r) * evalWord L1Gen (L0Factor i r) := by
  have he := congrArg (evalWord (reducedGen L0G0 L0G1)) h
  simpa only [reducedWord_eval, evalWord_append, expand_eval, evalWord, L0Rep] using he

@[expose] public def batchRep (b : Fin 80) (r : Fin 20) : Fin 1600 :=
  ⟨20 * b.val + r.val, by omega⟩

@[expose] public def stepBatch (b : Fin 80) : Prop :=
  ∀ (i : Fin 2) (r : Fin 20),
    L0Gen (i.castLE (by decide)) * L0Rep (batchRep b r) =
      L0Rep (L0Act (i.castLE (by decide)) (batchRep b r)) * evalWord L1Gen (L0Factor (i.castLE (by decide)) (batchRep b r))

@[expose] public def stepBatchCheck (b : Fin 80) : Prop :=
  ∀ (i : Fin 2) (r : Fin 20),
    algebraic (i.castLE (by decide)) (batchRep b r) ∨ checkFin (fun x : Fin 1600 => decide (
      (L0Gen (i.castLE (by decide)) * L0Rep (batchRep b r)) x =
        (L0Rep (L0Act (i.castLE (by decide)) (batchRep b r)) * evalWord L1Gen (L0Factor (i.castLE (by decide)) (batchRep b r))) x)) = true

public theorem ofStepBatchCheck (b : Fin 80) (h : stepBatchCheck b) : stepBatch b := by
  intro i r
  rcases h i r with ha | hp
  · exact algebraic_step (i.castLE (by decide)) (batchRep b r) ha
  · exact Equiv.ext (allFin _ hp)

private def certificateAct : Fin 4 → Fin 1600 → Fin 1600
  | 0 => L0Act 0
  | 1 => L0Act 1
  | 2 => L0Act 0
  | 3 => fun r => L0Act 1 (L0Act 1 r)

private def certificateFactor : Fin 4 → Fin 1600 → List (Fin 6)
  | 0 => L0Factor 0
  | 1 => L0Factor 1
  | 2 => L0Factor 0
  | 3 => fun r => L0Factor 1 (L0Act 1 r) ++ L0Factor 1 r

private theorem certificateStep_of_positive
    (h : ∀ (i : Fin 2) (r : Fin 1600),
      L0Gen (i.castLE (by decide)) * L0Rep r =
        L0Rep (L0Act (i.castLE (by decide)) r) * evalWord L1Gen (L0Factor (i.castLE (by decide)) r))
    (i : Fin 4) (r : Fin 1600) :
    L0Gen i * L0Rep r = L0Rep (certificateAct i r) * evalWord L1Gen (certificateFactor i r) := by
  have h0 (r : Fin 1600) := h 0 r
  have h1 (r : Fin 1600) := h 1 r
  change ∀ r, L0Gen 0 * L0Rep r = L0Rep (L0Act 0 r) * evalWord L1Gen (L0Factor 0 r) at h0
  change ∀ r, L0Gen 1 * L0Rep r = L0Rep (L0Act 1 r) * evalWord L1Gen (L0Factor 1 r) at h1
  fin_cases i
  · exact h0 r
  · exact h1 r
  · have ha : L0G0⁻¹ = L0G0 := (inv_eq_of_mul_eq_one_left genA_square).symm
    change L0G0⁻¹ * L0Rep r = _
    rw [ha]
    exact h0 r
  · have hb : L0Gen 3 = L0Gen 1 * L0Gen 1 := genB_square.symm
    simp only [certificateAct, certificateFactor]
    change L0Gen 3 * L0Rep r = _
    rw [hb, mul_assoc, h1 r, ← mul_assoc, h1 (L0Act 1 r), evalWord_append, mul_assoc]

/-- Forward transitions suffice, since the generators have orders 2 and 3. -/
public theorem card_step_of_positive
    (h : ∀ (i : Fin 2) (r : Fin 1600),
      L0Gen (i.castLE (by decide)) * L0Rep r =
        L0Rep (L0Act (i.castLE (by decide)) r) * evalWord L1Gen (L0Factor (i.castLE (by decide)) r)) :
    Nat.card H0 = 1600 * Nat.card H1 := by
  exact wordSubgroup_card_eq_mul_next
    L0Gen L0Inv L0Inv_spec L1Gen L1Inv L1Inv_spec
    L0Rep certificateAct certificateFactor (0 : Fin 1600) L0Point (0 : Fin 1600)
    L0Rep_mem H1_le L0Rep_base L0Rep_point L0Point_injective H1_fix
    (certificateStep_of_positive h)

end Tits.Atlas1600OrderCertificate.ForwardReduction
