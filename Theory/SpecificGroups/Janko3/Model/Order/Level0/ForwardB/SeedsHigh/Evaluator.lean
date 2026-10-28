module
public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.CycleData
import Mathlib.Tactic.FinCases

/-!
# Strict evaluation of packed J3 permutation words

Case analysis forces intermediate natural-number point values before the next
lookup. The soundness theorem relates this evaluator to ordinary permutation
multiplication; all numerical certificates are checked in the kernel.
Source: the existing J3 ATLAS tables and `Order/data/witnesses.json`.
-/
namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsHigh
open Theory.GroupTheory

@[expose] public def lookup (p x : Nat) : Nat := (p >>> (13 * x)) % 8192 % 6156

@[expose] public def run {α : Type} (g : α → Nat → Nat) : List α → Nat → Nat
  | [], x => x
  | i :: w, x => match run g w x with
    | 0 => g i 0
    | y + 1 => g i (y + 1)

public theorem run_cons {α : Type} (g : α → Nat → Nat) (i : α) (w : List α) (x : Nat) :
    run g (i :: w) x = g i (run g w x) := by
  simp only [run]
  split <;> rename_i h <;> simp only [h]

public theorem run_eq {n : Nat} (g : Fin n → Nat → Nat)
    (G : Fin n → Equiv.Perm (Fin 6156))
    (hg : ∀ i x, g i x.val = (G i x).val) (w : List (Fin n)) (x : Fin 6156) :
    run g w x.val = (evalWord G w x).val := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [run_cons, ih, hg]; rfl

@[expose] public def mixedNat : Fin 8 → Nat → Nat
  | 0 => lookup fastAMapPacked
  | 1 => lookup fastBMapPacked
  | 2 => lookup fastAInvMapPacked
  | 3 => lookup fastBInvMapPacked
  | 4 => lookup L1G0MapPacked
  | 5 => lookup L1G1MapPacked
  | 6 => lookup L1G0InvMapPacked
  | 7 => lookup L1G1InvMapPacked

@[expose] public def mixedGen : Fin 8 → Equiv.Perm (Fin 6156)
  | 0 => fastA
  | 1 => fastB
  | 2 => fastA⁻¹
  | 3 => fastB⁻¹
  | 4 => L1G0
  | 5 => L1G1
  | 6 => L1G0⁻¹
  | 7 => L1G1⁻¹

public theorem mixedNat_eq (i : Fin 8) (x : Fin 6156) :
    mixedNat i x.val = (mixedGen i x).val := by
  fin_cases i <;> rfl

@[expose] public def lift0 (i : Fin 4) : Fin 8 := ⟨i.val, by omega⟩
@[expose] public def lift1 (i : Fin 4) : Fin 8 := ⟨i.val + 4, by omega⟩

private theorem mixedGen_lift0 (i : Fin 4) : mixedGen (lift0 i) = fastL0Gen i := by
  fin_cases i <;> rfl
private theorem mixedGen_lift1 (i : Fin 4) : mixedGen (lift1 i) = L1Gen i := by
  fin_cases i <;> rfl

public theorem eval_lift0 (w : List (Fin 4)) :
    evalWord mixedGen (w.map lift0) = evalWord fastL0Gen w := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.map_cons, evalWord, mixedGen_lift0, ih]

public theorem eval_lift1 (w : List (Fin 4)) :
    evalWord mixedGen (w.map lift1) = evalWord L1Gen w := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.map_cons, evalWord, mixedGen_lift1, ih]

public theorem eval_flatMap {n : Nat} (ws : Fin n → List (Fin 8)) (w : List (Fin n)) :
    evalWord (fun b => evalWord mixedGen (ws b)) w =
      evalWord mixedGen (w.flatMap ws) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.flatMap_cons, evalWord_append, evalWord, ih]

/-- A block table certificate suffices for evaluation of every list of blocks. -/
public theorem run_blocks_eq {n : Nat} (ws : Fin n → List (Fin 8))
    (table : Fin n → Nat)
    (h : ∀ b (x : Fin 6156), lookup (table b) x.val = run mixedNat (ws b) x.val)
    (w : List (Fin n)) (x : Fin 6156) :
    run (fun b => lookup (table b)) w x.val =
      (evalWord mixedGen (w.flatMap ws) x).val := by
  rw [run_eq _ (fun b => evalWord mixedGen (ws b))]
  · rw [eval_flatMap]
  · intro b y
    rw [h, run_eq mixedNat mixedGen mixedNat_eq]

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsHigh
