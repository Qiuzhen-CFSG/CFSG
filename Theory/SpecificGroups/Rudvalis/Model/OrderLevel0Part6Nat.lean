module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Tables
import Mathlib.Tactic.FinCases
/-!
# Natural-number evaluation for the part-6 certificates

Evaluate the certified lookup tables without carrying dependent point bounds
through long words. The evaluation comparison below transfers the resulting
finite checks to the original permutation identities. Source: the ATLAS
witnesses and checked tables documented in `OrderLevel0Part6Tables`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Nat
set_option Elab.async false

@[expose] public def gen0 : Fin 4 → Nat → Nat
  | 0, x => (Part6Tables.aMapBlock (x / 64) >>> (12 * (x % 64))) % 4096 % 4060
  | 1, x => (Part6Tables.bMapBlock (x / 64) >>> (12 * (x % 64))) % 4096 % 4060
  | 2, x => (Part6Tables.aMapBlock (x / 64) >>> (12 * (x % 64))) % 4096 % 4060
  | 3, x => (Part6Tables.bInvMapBlock (x / 64) >>> (12 * (x % 64))) % 4096 % 4060

private theorem gen0_eq (i : Fin 4) (x : Fin 4060) :
    gen0 i x.val = (Part6Tables.gen0 i x).val := by
  fin_cases i <;> rfl

@[expose] public def gen1 : Fin 4 → Nat → Nat
  | 0, x => (Part6Tables.L1G0MapBlock (x / 64) >>> (12 * (x % 64))) % 4096 % 4060
  | 1, x => (Part6Tables.L1G1MapBlock (x / 64) >>> (12 * (x % 64))) % 4096 % 4060
  | 2, x => (Part6Tables.L1G0InvMapBlock (x / 64) >>> (12 * (x % 64))) % 4096 % 4060
  | 3, x => (Part6Tables.L1G1InvMapBlock (x / 64) >>> (12 * (x % 64))) % 4096 % 4060

private theorem gen1_eq (i : Fin 4) (x : Fin 4060) :
    gen1 i x.val = (Part6Tables.gen1 i x).val := by
  fin_cases i <;> rfl

/-- Force each intermediate index before duplicating it in a table lookup. -/
@[expose] public def force (f : Nat → Nat) : Nat → Nat
  | 0 => f 0
  | n + 1 => f (n + 1)

private theorem force_eq (f : Nat → Nat) (n : Nat) : force f n = f n := by
  cases n <;> rfl

@[expose] public def eval (g : Fin 4 → Nat → Nat) : List (Fin 4) → Nat → Nat
  | [], x => x
  | i :: w, x => force (g i) (eval g w x)

private theorem eval_eq (g : Fin 4 → Nat → Nat)
    (G : Fin 4 → Fin 4060 → Fin 4060) (h : ∀ i x, g i x.val = (G i x).val)
    (w : List (Fin 4)) (x : Fin 4060) : eval g w x.val = (Part6Tables.eval G w x).val := by
  induction w with
  | nil => rfl
  | cons i w ih => simpa only [eval, force_eq, Part6Tables.eval, ih] using h i (Part6Tables.eval G w x)

@[expose] public def point (i : Fin 2) (r : Fin 4060) (x : Nat) : Bool :=
  decide (gen0 (i.castLE (by decide)) (eval gen0 (L0RepWord r) x) =
    eval gen0 (L0RepWord (L0Act (i.castLE (by decide)) r))
      (eval gen1 (L0Factor (i.castLE (by decide)) r) x))

@[expose] public def check (i : Fin 2) (r : Fin 4060) : Bool :=
  checkFin (fun x : Fin 4060 => point i r x.val)

public theorem ofCheck (i : Fin 2) (r : Fin 4060) (h : check i r = true) : stepCheck i r := by
  have ht : Part6Tables.check i r = true := by
    apply (checkFin_spec _).mpr
    intro x
    have hx := (checkFin_spec _).mp h x
    simp only [point, decide_eq_true_eq] at hx ⊢
    apply Fin.ext
    simpa only [eval_eq _ _ gen0_eq, eval_eq _ _ gen1_eq, gen0_eq] using hx
  right
  apply (checkFin_spec _).mpr
  intro x
  simpa only [decide_eq_true_eq] using
    congrArg (fun p : Equiv.Perm (Fin 4060) => p x) (Part6Tables.ofCheck i r ht)

/-- Twenty points per slice bound the memory used by each kernel reduction. -/
@[expose] public def slice (i : Fin 2) (r : Fin 4060) (b : Fin 203) : Bool :=
  checkFin (fun x : Fin 20 => point i r (20 * b.val + x.val))

public theorem ofSlices (i : Fin 2) (r : Fin 4060)
    (h : ∀ b, slice i r b = true) : stepCheck i r := by
  apply ofCheck
  apply (checkFin_spec _).mpr
  intro x
  have hx := (checkFin_spec _).mp (h ⟨x.val / 20, by omega⟩) ⟨x.val % 20, by omega⟩
  change point i r (20 * (x.val / 20) + x.val % 20) = true at hx
  change point i r x.val = true
  convert hx using 1
  congr 1
  omega

end Rudvalis.OrderCertificate.ForwardReduction.Part6Nat
