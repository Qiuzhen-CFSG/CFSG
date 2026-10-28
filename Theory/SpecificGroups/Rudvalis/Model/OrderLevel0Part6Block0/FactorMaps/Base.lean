module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.FactorWords
import Mathlib.Tactic.FinCases

/-!
# Composition certificates for cached Rudvalis factor actions

A cached table is certified against the composition of two earlier tables.
Word concatenation then transfers this finite certificate to word evaluation.
The words and generator actions are the ATLAS witnesses already certified in
`FactorWords` and `OrderLevel0Part6Tables`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps

public theorem force_eq (f : Nat → Nat) (x : Nat) : Part6Nat.force f x = f x := by
  cases x <;> rfl

public theorem gen1_eq (i : Fin 4) (x : Fin 4060) :
    Part6Nat.gen1 i x.val = (Part6Tables.gen1 i x).val := by
  fin_cases i <;> rfl

public theorem eval_eq (w : List (Fin 4)) (x : Fin 4060) :
    Part6Nat.eval Part6Nat.gen1 w x.val = (Part6Tables.eval Part6Tables.gen1 w x).val := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simpa only [Part6Nat.eval, force_eq, Part6Tables.eval, ih] using
      gen1_eq i (Part6Tables.eval Part6Tables.gen1 w x)

public theorem eval_append (u v : List (Fin 4)) (x : Fin 4060) :
    Part6Tables.eval Part6Tables.gen1 (u ++ v) x =
      Part6Tables.eval Part6Tables.gen1 u (Part6Tables.eval Part6Tables.gen1 v x) := by
  induction u with
  | nil => rfl
  | cons i u ih => exact congrArg (Part6Tables.gen1 i) ih

public theorem ofComp (m a b : Nat → Nat) (u v : List (Fin 4))
    (ha : ∀ x : Fin 4060, a x.val = (Part6Tables.eval Part6Tables.gen1 u x).val)
    (hb : ∀ x : Fin 4060, b x.val = (Part6Tables.eval Part6Tables.gen1 v x).val)
    (hc : ∀ x : Fin 4060, m x.val = Part6Nat.force a (b x.val))
    (x : Fin 4060) : m x.val = (Part6Tables.eval Part6Tables.gen1 (u ++ v) x).val := by
  rw [hc, force_eq, hb, ha, eval_append]

/-- Twenty-point checks cover the entire permutation domain. -/
public theorem ofMapSlices (m a b : Nat → Nat)
    (h : ∀ j : Fin 203, checkFin (fun x : Fin 20 => decide
      (m (20 * j.val + x.val) = Part6Nat.force a (b (20 * j.val + x.val)))) = true)
    (x : Fin 4060) : m x.val = Part6Nat.force a (b x.val) := by
  have hx := allFin _ (h ⟨x.val / 20, by omega⟩) ⟨x.val % 20, by omega⟩
  change m (20 * (x.val / 20) + x.val % 20) =
    Part6Nat.force a (b (20 * (x.val / 20) + x.val % 20)) at hx
  have he : 20 * (x.val / 20) + x.val % 20 = x.val := by omega
  simpa only [he] using hx

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps

namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps

/-- A transition slice using an arbitrary certified cached factor action. -/
@[expose] public def cachedSlice (m : Nat → Nat) (i : Fin 2)
    (w v : List (Fin 4)) (b : Fin 203) : Bool :=
  checkFin (fun x : Fin 20 => decide
    (Part6Nat.gen0 (i.castLE (by decide))
        (Part6Nat.eval Part6Nat.gen0 w (20 * b.val + x.val)) =
      Part6Nat.eval Part6Nat.gen0 v (m (20 * b.val + x.val))))

/-- The only remaining factor premise is pointwise correctness of the cache. -/
public theorem ofCachedSlices (k : Fin 100) (m : Nat → Nat)
    (hm : ∀ x : Fin 4060, m x.val =
      (Part6Tables.eval Part6Tables.gen1 (FactorWords.word k) x).val)
    (w v : List (Fin 4))
    (hw : L0RepWord (FactorWords.row k).2 = w)
    (hv : L0RepWord (L0Act ((FactorWords.row k).1.castLE (by decide))
      (FactorWords.row k).2) = v)
    (h : ∀ b, cachedSlice m (FactorWords.row k).1 w v b = true) :
    stepCheck (FactorWords.row k).1 (FactorWords.row k).2 := by
  apply Part6Nat.ofSlices
  intro b
  apply (checkFin_spec _).mpr
  intro x
  have hx := (checkFin_spec _).mp (h b) x
  have bound : 20 * b.val + x.val < 4060 := by omega
  have he := (hm ⟨20 * b.val + x.val, bound⟩).trans
    (eval_eq (FactorWords.word k) ⟨20 * b.val + x.val, bound⟩).symm
  simpa only [Part6Nat.point, hw, hv, FactorWords.word_eq, cachedSlice, he]
    using hx

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
