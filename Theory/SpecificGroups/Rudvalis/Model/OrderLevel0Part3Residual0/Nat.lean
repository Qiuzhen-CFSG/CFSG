module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3ResidualReduction
import Mathlib.Tactic.FinCases

/-!
# Packed natural-number evaluation for Rudvalis residual group 0

Evaluate each generator by shifting its original packed permutation table.
The index occurs only once in each lookup, so intermediate indices need no
repeated evaluation or dependent bounds. Induction on words identifies this
evaluator with the original permutation action; slices cover all 4060 points.
Source: the ATLAS tables and word witnesses in `OrderLevel0Data` and
`OrderChainData`, documented in `OrderCertificate/GenerateChain.g`.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual0Nat
open Theory.GroupTheory

@[expose] public def lookup (t x : Nat) : Nat := (t >>> (12 * x)) % 4096 % 4060

@[expose] public def gen0 : Fin 4 → Nat → Nat
  | 0, x => lookup Data.aMapPacked x
  | 1, x => lookup Data.bMapPacked x
  | 2, x => lookup Data.aMapPacked x
  | 3, x => lookup Data.bMapPacked (lookup Data.bMapPacked (lookup Data.bMapPacked x))

@[expose] public def gen1 : Fin 4 → Nat → Nat
  | 0, x => lookup L1G0MapPacked x
  | 1, x => lookup L1G1MapPacked x
  | 2, x => lookup L1G0InvMapPacked x
  | 3, x => lookup L1G1InvMapPacked x

private theorem gen0_eq (i : Fin 4) (x : Fin 4060) :
    gen0 i x.val = (L0Gen i x).val := by
  fin_cases i <;> rfl

private theorem gen1_eq (i : Fin 4) (x : Fin 4060) :
    gen1 i x.val = (L1Gen i x).val := by
  fin_cases i <;> rfl

@[expose] public def eval (g : Fin 4 → Nat → Nat) : List (Fin 4) → Nat → Nat
  | [], x => x
  | i :: w, x => g i (eval g w x)

private theorem eval_eq (g : Fin 4 → Nat → Nat)
    (G : Fin 4 → Equiv.Perm (Fin 4060))
    (h : ∀ i x, g i x.val = (G i x).val) (w : List (Fin 4)) (x : Fin 4060) :
    eval g w x.val = (evalWord G w x).val := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simpa only [eval, ih, evalWord, Equiv.Perm.mul_apply] using h i (evalWord G w x)

@[expose] public def point (i : Fin 2) (r : Fin 4060) (x : Nat) : Bool :=
  decide (gen0 (i.castLE (by decide)) (eval gen0 (L0RepWord r) x) =
    eval gen0 (L0RepWord (L0Act (i.castLE (by decide)) r))
      (eval gen1 (L0Factor (i.castLE (by decide)) r) x))

/-- Each of the 29 slices checks 140 points. -/
@[expose] public def slice (i : Fin 2) (r : Fin 4060) (b : Fin 29) : Bool :=
  checkFin (fun x : Fin 140 => point i r (140 * b.val + x.val))

/-- The slice checks prove the prescribed transition on every point. -/
public theorem ofSlices (i : Fin 2) (r : Fin 4060)
    (h : ∀ b, slice i r b = true) : stepCheck i r := by
  right
  apply (checkFin_spec _).mpr
  intro x
  have hx := (checkFin_spec _).mp (h ⟨x.val / 140, by omega⟩) ⟨x.val % 140, by omega⟩
  change point i r (140 * (x.val / 140) + x.val % 140) = true at hx
  have he : 140 * (x.val / 140) + x.val % 140 = x.val := by omega
  rw [he] at hx
  simp only [point, decide_eq_true_eq] at hx ⊢
  apply Fin.ext
  simpa only [eval_eq _ _ gen0_eq, eval_eq _ _ gen1_eq, gen0_eq,
    Equiv.Perm.mul_apply, L0Rep] using hx

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Residual0Nat
