module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part0ResidualReduction
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Nat
import Mathlib.Tactic.FinCases

/-!
# Soundness of cached residual factor compositions

A table of 4060 images represents an action on the original point set.
Composition certificates identify each table with its factor word; the final
comparison transfers the shortened computation to the fixed `stepCheck`.
Source: `OrderLevel0Data`, `OrderChainData`, and the certified part-6 tables.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Cache2
open Theory.GroupTheory

@[expose] public def lookup (table : Nat → Nat) (x : Nat) : Nat :=
  Part6Nat.force (fun v => (table (v / 64) >>> (12 * (v % 64))) % 4096 % 4060) x

public theorem lookup_lt (table : Nat → Nat) (x : Nat) : lookup table x < 4060 := by
  cases x <;> exact Nat.mod_lt _ (by decide)

@[expose] public def tableMap (table : Nat → Nat) (x : Fin 4060) : Fin 4060 :=
  ⟨lookup table x.val, lookup_lt table x.val⟩

public theorem compose_sound (f a b : Fin 4060 → Fin 4060) (u v : List (Fin 4))
    (ha : ∀ x, a x = evalWord L1Gen u x)
    (hb : ∀ x, b x = evalWord L1Gen v x)
    (h : ∀ x, f x = a (b x)) :
    ∀ x, f x = evalWord L1Gen (u ++ v) x := by
  intro x
  rw [h, ha, hb, evalWord_append, Equiv.Perm.mul_apply]

public theorem eval1_eq (w : List (Fin 4)) (x : Fin 4060) :
    Part6Tables.eval Part6Tables.gen1 w x = evalWord L1Gen w x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simpa only [Part6Tables.eval, evalWord, Equiv.Perm.mul_apply, Part6Tables.gen1_eq]
      using congrArg (L1Gen i) ih

@[expose] public def fastGen0 : Fin 4 → Fin 4060 → Fin 4060
  | 0 => tableMap Part6Tables.aMapBlock
  | 1 => tableMap Part6Tables.bMapBlock
  | 2 => tableMap Part6Tables.aMapBlock
  | 3 => tableMap Part6Tables.bInvMapBlock

public theorem fastGen0_eq (i : Fin 4) (x : Fin 4060) :
    fastGen0 i x = Part6Tables.gen0 i x := by
  rcases x with ⟨n, hn⟩
  fin_cases i <;> cases n <;> rfl

public theorem fastEval0_eq (w : List (Fin 4)) (x : Fin 4060) :
    Part6Tables.eval fastGen0 w x = Part6Tables.eval Part6Tables.gen0 w x := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [Part6Tables.eval, fastGen0_eq, ih]

public theorem finish (i : Fin 2) (r : Fin 4060) (f : Fin 4060 → Fin 4060)
    (w : List (Fin 4)) (hf : ∀ x, f x = evalWord L1Gen w x)
    (hw : L0Factor (i.castLE (by decide)) r = w)
    (hc : checkFin (fun x => decide
      (fastGen0 (i.castLE (by decide)) (Part6Tables.eval fastGen0 (L0RepWord r) x) =
        Part6Tables.eval fastGen0 (L0RepWord (L0Act (i.castLE (by decide)) r)) (f x))) = true) :
    stepCheck i r := by
  have ht : Part6Tables.check i r = true := by
    simpa only [Part6Tables.check, hw, eval1_eq, hf, fastGen0_eq, fastEval0_eq] using hc
  right
  apply (checkFin_spec _).mpr
  intro x
  simpa only [decide_eq_true_eq] using
    congrArg (fun p : Equiv.Perm (Fin 4060) => p x) (Part6Tables.ofCheck i r ht)

@[expose] public def word0 : List (Fin 4) := [0]
@[expose] public def map0 : Fin 4060 → Fin 4060 := tableMap Part6Tables.L1G0MapBlock
public theorem sound0 (x : Fin 4060) : map0 x = evalWord L1Gen word0 x := by
  have h : map0 x = Part6Tables.gen1 0 x := by
    rcases x with ⟨n, hn⟩
    cases n <;> rfl
  simpa only [word0, evalWord, mul_one] using h.trans (Part6Tables.gen1_eq 0 x)

@[expose] public def word1 : List (Fin 4) := [1]
@[expose] public def map1 : Fin 4060 → Fin 4060 := tableMap Part6Tables.L1G1MapBlock
public theorem sound1 (x : Fin 4060) : map1 x = evalWord L1Gen word1 x := by
  have h : map1 x = Part6Tables.gen1 1 x := by
    rcases x with ⟨n, hn⟩
    cases n <;> rfl
  simpa only [word1, evalWord, mul_one] using h.trans (Part6Tables.gen1_eq 1 x)

@[expose] public def word2 : List (Fin 4) := [2]
@[expose] public def map2 : Fin 4060 → Fin 4060 := tableMap Part6Tables.L1G0InvMapBlock
public theorem sound2 (x : Fin 4060) : map2 x = evalWord L1Gen word2 x := by
  have h : map2 x = Part6Tables.gen1 2 x := by
    rcases x with ⟨n, hn⟩
    cases n <;> rfl
  simpa only [word2, evalWord, mul_one] using h.trans (Part6Tables.gen1_eq 2 x)

@[expose] public def word3 : List (Fin 4) := [3]
@[expose] public def map3 : Fin 4060 → Fin 4060 := tableMap Part6Tables.L1G1InvMapBlock
public theorem sound3 (x : Fin 4060) : map3 x = evalWord L1Gen word3 x := by
  have h : map3 x = Part6Tables.gen1 3 x := by
    rcases x with ⟨n, hn⟩
    cases n <;> rfl
  simpa only [word3, evalWord, mul_one] using h.trans (Part6Tables.gen1_eq 3 x)

end Rudvalis.OrderCertificate.ForwardReduction.Part0Residual.Cache2
