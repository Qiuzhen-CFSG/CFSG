module

public import Theory.SpecificGroups.Janko3.Model.Order.Level1.Reduction
import Mathlib.Tactic.FinCases

/-!
# Bounded kernel checks for the second J3 Schreier step

Each batch contains five representatives, two forward generators and 513
letters. Algebraically reducible transitions short-circuit the letter check.
Twelve letter batches cover the entire permutation domain; 102 representative
batches cover the transversal. The soundness lemmas assemble the finite checks
into permutation identities.
Source: ATLAS J3G1-p6156B0, retained under `Model/data/`.
-/

namespace Sporadic.Janko3.OrderCertificate.Level1
open Theory.GroupTheory

@[expose] public def genMap : Fin 4 → Fin 6156 → Fin 6156
  | 0 => L1G0Map
  | 1 => L1G1Map
  | 2 => L1G0InvMap
  | 3 => L1G1InvMap

@[expose] public def nextMap : Fin 6 → Fin 6156 → Fin 6156
  | 0 => L2G0Map
  | 1 => L2G1Map
  | 2 => L2G2Map
  | 3 => L2G0InvMap
  | 4 => L2G1InvMap
  | 5 => L2G2InvMap

@[expose] public def wordMap {n : Nat} (gen : Fin n → Fin 6156 → Fin 6156) :
    List (Fin n) → Fin 6156 → Fin 6156
  | [], x => x
  | i :: w, x => gen i (wordMap gen w x)

private theorem genMap_eq (i : Fin 4) (x : Fin 6156) : genMap i x = L1Gen i x := by
  fin_cases i <;> rfl

private theorem nextMap_eq (i : Fin 6) (x : Fin 6156) : nextMap i x = L2Gen i x := by
  fin_cases i <;> rfl

private theorem wordMap_eq {n : Nat} (gen : Fin n → Equiv.Perm (Fin 6156))
    (maps : Fin n → Fin 6156 → Fin 6156) (h : ∀ i x, maps i x = gen i x)
    (w : List (Fin n)) (x : Fin 6156) : wordMap maps w x = evalWord gen w x := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [wordMap, evalWord, Equiv.Perm.mul_apply, h, ih]

@[expose] public def batchRep (b : Fin 102) (r : Fin 5) : Fin 510 :=
  ⟨5 * b.val + r.val, by omega⟩

@[expose] public def batchLetter (c : Fin 12) (x : Fin 513) : Fin 6156 :=
  ⟨513 * c.val + x.val, by omega⟩

@[expose] public def partialCheck (b : Fin 102) (c : Fin 12) : Prop :=
  ∀ (i : Fin 2) (r : Fin 5),
    let j := i.castLE (by decide : 2 ≤ 4)
    algebraic j (batchRep b r) ∨
      checkFin (fun x : Fin 513 => decide
        (genMap j (wordMap genMap (L1RepWord (batchRep b r)) (batchLetter c x)) =
          wordMap genMap (L1RepWord (L1Act j (batchRep b r)))
            (wordMap nextMap (L1Factor j (batchRep b r)) (batchLetter c x)))) = true

@[expose] public def partialStep (b : Fin 102) (c : Fin 12) : Prop :=
  ∀ (i : Fin 2) (r : Fin 5) (x : Fin 513),
    let j := i.castLE (by decide : 2 ≤ 4)
    (L1Gen j * L1Rep (batchRep b r)) (batchLetter c x) =
      (L1Rep (L1Act j (batchRep b r)) *
        evalWord L2Gen (L1Factor j (batchRep b r))) (batchLetter c x)

public theorem ofPartialCheck (b : Fin 102) (c : Fin 12)
    (h : partialCheck b c) : partialStep b c := by
  intro i r x
  rcases h i r with ha | hp
  · exact congrArg (fun g : Equiv.Perm (Fin 6156) => g (batchLetter c x))
      (algebraic_step _ _ ha)
  · have hx := allFin _ hp x
    simpa only [genMap_eq, wordMap_eq L1Gen genMap genMap_eq,
      wordMap_eq L2Gen nextMap nextMap_eq, L1Rep, Equiv.Perm.mul_apply] using hx

@[expose] public def stepBatch (b : Fin 102) : Prop :=
  ∀ (i : Fin 2) (r : Fin 5),
    let j := i.castLE (by decide : 2 ≤ 4)
    L1Gen j * L1Rep (batchRep b r) =
      L1Rep (L1Act j (batchRep b r)) * evalWord L2Gen (L1Factor j (batchRep b r))

public theorem ofPartialSteps (b : Fin 102) (h : ∀ c, partialStep b c) : stepBatch b := by
  intro i r
  apply Equiv.ext
  intro x
  let c : Fin 12 := ⟨x.val / 513, by omega⟩
  let y : Fin 513 := ⟨x.val % 513, by omega⟩
  have hxy : batchLetter c y = x := by
    apply Fin.ext
    dsimp [batchLetter, c, y]
    omega
  simpa only [hxy] using h c i r y

public theorem forward_of_batches (h : ∀ b, stepBatch b) (i : Fin 2) (r : Fin 510) :
    let j := i.castLE (by decide : 2 ≤ 4)
    L1Gen j * L1Rep r = L1Rep (L1Act j r) * evalWord L2Gen (L1Factor j r) := by
  let b : Fin 102 := ⟨r.val / 5, by omega⟩
  let s : Fin 5 := ⟨r.val % 5, by omega⟩
  have hrs : batchRep b s = r := by
    apply Fin.ext
    dsimp [batchRep, b, s]
    omega
  simpa only [hrs] using h b i s

end Sporadic.Janko3.OrderCertificate.Level1
