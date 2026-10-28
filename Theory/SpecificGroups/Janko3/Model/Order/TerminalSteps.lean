module

public import Theory.SpecificGroups.Janko3.Model.Order.Level2Data
import Mathlib.Tactic.FinCases

/-!
# Certified transitions in the terminal J₃ subgroup

Six signed generators permute sixteen word representatives. Their images of
point 2 are distinct. The complete permutation identities are checked by the
kernel. The order and trivial terminal stabilizer are deduced in `Terminal`.
Source: ATLAS J3G1-p6156B0, retained under `Model/data/`.
-/

namespace Sporadic.Janko3.OrderCertificate
open Theory.GroupTheory
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option Elab.async false

private def stepCheck (i : Fin 6) : Bool :=
  checkFin (fun r : Fin 16 => checkLetters (fun x => decide
    ((L2Gen i * L2Rep r) x = L2Rep (L2Act i r) x)))

private theorem step_of_check (i : Fin 6) (h : stepCheck i = true) :
    ∀ r, L2Gen i * L2Rep r = L2Rep (L2Act i r) := by
  have hr := allFin (fun r : Fin 16 => checkLetters (fun x => decide
    ((L2Gen i * L2Rep r) x = L2Rep (L2Act i r) x)) = true) (by
      simpa only [stepCheck, Bool.decide_eq_true] using h)
  intro r
  apply Equiv.ext
  exact allLetters _ (hr r)

private theorem step0 : ∀ r, L2Gen 0 * L2Rep r = L2Rep (L2Act 0 r) :=
  step_of_check 0 (by decide +kernel)
private theorem step1 : ∀ r, L2Gen 1 * L2Rep r = L2Rep (L2Act 1 r) :=
  step_of_check 1 (by decide +kernel)
private theorem step2 : ∀ r, L2Gen 2 * L2Rep r = L2Rep (L2Act 2 r) :=
  step_of_check 2 (by decide +kernel)
private theorem step3 : ∀ r, L2Gen 3 * L2Rep r = L2Rep (L2Act 3 r) :=
  step_of_check 3 (by decide +kernel)
private theorem step4 : ∀ r, L2Gen 4 * L2Rep r = L2Rep (L2Act 4 r) :=
  step_of_check 4 (by decide +kernel)
private theorem step5 : ∀ r, L2Gen 5 * L2Rep r = L2Rep (L2Act 5 r) :=
  step_of_check 5 (by decide +kernel)

public theorem L2Step (i : Fin 6) (r : Fin 16) :
    L2Gen i * L2Rep r = L2Rep (L2Act i r) := by
  fin_cases i
  · exact step0 r
  · exact step1 r
  · exact step2 r
  · exact step3 r
  · exact step4 r
  · exact step5 r

end Sporadic.Janko3.OrderCertificate
