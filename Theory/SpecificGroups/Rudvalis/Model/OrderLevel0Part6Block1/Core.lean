module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Data
import Mathlib.Tactic.FinCases
/-!
# Sound interpretation of compressed Rudvalis word checks

Interpret the eight original letters using the two levels of ATLAS generators.
A table composition certificate transfers to a word evaluation identity, and
pointwise checks on compressed words therefore imply the original transition.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1.Compressed
open Theory.GroupTheory
set_option Elab.async false

@[expose] public def mixed : Fin 8 → Equiv.Perm (Fin 4060)
  | 0 => L0Gen 0
  | 1 => L0Gen 1
  | 2 => L0Gen 2
  | 3 => L0Gen 3
  | 4 => L1Gen 0
  | 5 => L1Gen 1
  | 6 => L1Gen 2
  | 7 => L1Gen 3

@[expose] public def up0 (i : Fin 4) : Fin 8 := ⟨i.val, by omega⟩
@[expose] public def up1 (i : Fin 4) : Fin 8 := ⟨i.val + 4, by omega⟩

private theorem mixed_up0 (i : Fin 4) : mixed (up0 i) = L0Gen i := by
  fin_cases i <;> rfl
private theorem mixed_up1 (i : Fin 4) : mixed (up1 i) = L1Gen i := by
  fin_cases i <;> rfl

private theorem eval_up0 (w : List (Fin 4)) :
    evalWord mixed (w.map up0) = evalWord L0Gen w := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.map_cons, evalWord, mixed_up0, ih]
private theorem eval_up1 (w : List (Fin 4)) :
    evalWord mixed (w.map up1) = evalWord L1Gen w := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.map_cons, evalWord, mixed_up1, ih]

public theorem force_eq (f : Nat → Nat) (x : Nat) : Part6Nat.force f x = f x := by
  cases x <;> rfl

public theorem comp_sound (a b c : Nat → Nat) (u v : List (Fin 8))
    (ha : ∀ x : Fin 4060, a x.val = (evalWord mixed u x).val)
    (hb : ∀ x : Fin 4060, b x.val = (evalWord mixed v x).val)
    (hc : ∀ x : Fin 4060, c x.val = Part6Nat.force a (b x.val)) :
    ∀ x : Fin 4060, c x.val = (evalWord mixed (u ++ v) x).val := by
  intro x
  rw [hc, force_eq, hb, ha, evalWord_append]
  rfl

public theorem sound0 (x : Fin 4060) :
    map0 x.val = (evalWord mixed word0 x).val := by
  calc
    _ = (Part6Tables.gen0 0 x).val := by rfl
    _ = _ := by
      simpa only [word0, evalWord, mixed, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using
        congrArg Fin.val (Part6Tables.gen0_eq 0 x)

public theorem sound1 (x : Fin 4060) :
    map1 x.val = (evalWord mixed word1 x).val := by
  calc
    _ = (Part6Tables.gen0 1 x).val := by rfl
    _ = _ := by
      simpa only [word1, evalWord, mixed, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using
        congrArg Fin.val (Part6Tables.gen0_eq 1 x)

public theorem sound2 (x : Fin 4060) :
    map2 x.val = (evalWord mixed word2 x).val := by
  calc
    _ = (Part6Tables.gen0 2 x).val := by rfl
    _ = _ := by
      simpa only [word2, evalWord, mixed, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using
        congrArg Fin.val (Part6Tables.gen0_eq 2 x)

public theorem sound3 (x : Fin 4060) :
    map3 x.val = (evalWord mixed word3 x).val := by
  calc
    _ = (Part6Tables.gen0 3 x).val := by rfl
    _ = _ := by
      simpa only [word3, evalWord, mixed, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using
        congrArg Fin.val (Part6Tables.gen0_eq 3 x)

public theorem sound4 (x : Fin 4060) :
    map4 x.val = (evalWord mixed word4 x).val := by
  calc
    _ = (Part6Tables.gen1 0 x).val := by rfl
    _ = _ := by
      simpa only [word4, evalWord, mixed, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using
        congrArg Fin.val (Part6Tables.gen1_eq 0 x)

public theorem sound5 (x : Fin 4060) :
    map5 x.val = (evalWord mixed word5 x).val := by
  calc
    _ = (Part6Tables.gen1 1 x).val := by rfl
    _ = _ := by
      simpa only [word5, evalWord, mixed, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using
        congrArg Fin.val (Part6Tables.gen1_eq 1 x)

public theorem sound6 (x : Fin 4060) :
    map6 x.val = (evalWord mixed word6 x).val := by
  calc
    _ = (Part6Tables.gen1 2 x).val := by rfl
    _ = _ := by
      simpa only [word6, evalWord, mixed, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using
        congrArg Fin.val (Part6Tables.gen1_eq 2 x)

public theorem sound7 (x : Fin 4060) :
    map7 x.val = (evalWord mixed word7 x).val := by
  calc
    _ = (Part6Tables.gen1 3 x).val := by rfl
    _ = _ := by
      simpa only [word7, evalWord, mixed, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using
        congrArg Fin.val (Part6Tables.gen1_eq 3 x)

@[expose] public def eval : List (Fin 96) → Nat → Nat
  | [], x => x
  | i :: w, x => Part6Nat.force (gen i) (eval w x)

public theorem eval_sound
    (hg : ∀ (i : Fin 96) (x : Fin 4060),
      gen i x.val = (evalWord mixed (word i) x).val)
    (w : List (Fin 96)) (x : Fin 4060) :
    eval w x.val = (evalWord mixed (w.flatMap word) x).val := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [eval, force_eq, ih, hg, List.flatMap_cons, evalWord_append]
    rfl

@[expose] public def slice (u v : List (Fin 96)) (b : Fin 41) : Bool :=
  checkFin (fun x : Fin 100 => decide (eval u ((100 * b.val + x.val) % 4060) =
    eval v ((100 * b.val + x.val) % 4060)))

public theorem ofSlices
    (hg : ∀ (i : Fin 96) (x : Fin 4060),
      gen i x.val = (evalWord mixed (word i) x).val)
    (i : Fin 2) (r : Fin 4060) (u v : List (Fin 96))
    (hu : u.flatMap word = ((i.castLE (by decide)) :: L0RepWord r).map up0)
    (hv : v.flatMap word = (L0RepWord (L0Act (i.castLE (by decide)) r)).map up0 ++
      (L0Factor (i.castLE (by decide)) r).map up1)
    (h : ∀ b, slice u v b = true) : stepCheck i r := by
  right
  apply (checkFin_spec _).mpr
  intro x
  simp only [decide_eq_true_eq]
  apply Fin.ext
  have hx := (checkFin_spec _).mp (h ⟨x.val / 100, by omega⟩) ⟨x.val % 100, by omega⟩
  have he : (100 * (x.val / 100) + x.val % 100) % 4060 = x.val := by omega
  change decide (eval u ((100 * (x.val / 100) + x.val % 100) % 4060) =
    eval v ((100 * (x.val / 100) + x.val % 100) % 4060)) = true at hx
  rw [he, decide_eq_true_eq, eval_sound hg, eval_sound hg, hu, hv] at hx
  simpa only [evalWord_append, eval_up0, eval_up1, evalWord,
    Equiv.Perm.mul_apply, L0Rep] using hx

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1.Compressed
