module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.PowerRootRelations.CentralErrors
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group

/-!
# Word identities with central coefficients

A checked rewrite records `value u = c * value v`, with `c` an actual central
relator error. Context, reversal and composition preserve this identity.
Rotating a source relator is valid because its value is central. These rules
allow an external word search to supply a proof trace without being trusted.

Source: Parrott (1972), §5, p.683, with commutators `a⁻¹ b⁻¹ a b`.
-/

@[expose] public section

namespace Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
abbrev E := NormalizedPresentation
abbrev C := Subgroup.center E
abbrev Word := List ℤ

def numbered : ℕ → E
  | 1 => normalizedGenerator .r1
  | 2 => normalizedGenerator .r8
  | 3 => normalizedGenerator .s1
  | 4 => normalizedGenerator .s2
  | 5 => normalizedGenerator .s3
  | 6 => normalizedGenerator .s4
  | 7 => normalizedGenerator .s5
  | 8 => normalizedGenerator .s6
  | 9 => normalizedGenerator .s7
  | 10 => normalizedGenerator .s8
  | _ => 1

def letter (i : ℤ) : E := if i < 0 then (numbered i.natAbs)⁻¹ else numbered i.natAbs

def value (w : Word) : E := (w.map letter).prod

def inverse (w : Word) : Word := w.reverse.map Neg.neg

@[simp] theorem value_nil : value [] = 1 := rfl
@[simp] theorem value_append (u v : Word) : value (u ++ v) = value u * value v := by
  simp [value]
@[simp] theorem letter_neg (i : ℤ) : letter (-i) = (letter i)⁻¹ := by
  unfold letter
  by_cases hi : i = 0
  · subst i; simp [numbered]
  · rcases lt_or_gt_of_ne hi with h | h <;> simp [h, le_of_lt h, Int.natAbs_neg]
@[simp] theorem value_inverse (w : Word) : value (inverse w) = (value w)⁻¹ := by
  induction w with
  | nil => simp [inverse]
  | cons a w ih =>
    simp [inverse, value, List.reverse_cons, letter_neg] at *
    exact ih

def Holds (c : C) (u v : Word) : Prop := value u = (c : E) * value v

theorem holds_refl (w : Word) : Holds 1 w w := by simp [Holds]
theorem holds_trans {a b : C} {u v w : Word} (h : Holds a u v) (k : Holds b v w) :
    Holds (a * b) u w := by
  dsimp [Holds] at *
  rw [h, k, mul_assoc]
theorem holds_symm {c : C} {u v : Word} (h : Holds c u v) : Holds c⁻¹ v u := by
  dsimp [Holds] at *
  rw [h, inv_mul_cancel_left]
theorem holds_context {c : C} {u v : Word} (h : Holds c u v) (p q : Word) :
    Holds c (p ++ u ++ q) (p ++ v ++ q) := by
  dsimp [Holds] at *
  simp only [value_append]
  rw [h]
  have hc := c.property.comm (value p)
  calc
    _ = (value p * (c : E)) * (value v * value q) := by group
    _ = ((c : E) * value p) * (value v * value q) := by rw [hc.eq]
    _ = _ := by group

theorem holds_factor {c d : C} {u v : Word} (h : Holds c u v) (e : c = d) :
    Holds d u v := e ▸ h

theorem holds_cancel {c : C} {w : Word} (h : Holds c w w) : c = 1 := by
  apply Subtype.ext
  exact mul_right_cancel (h.symm.trans (one_mul (value w)).symm)

theorem rotate {c : C} (p q : Word) (h : value (p ++ q) = (c : E)) :
    value (q ++ p) = (c : E) := by
  simp only [value_append] at *
  have hc := c.property.comm (value p)
  calc
    _ = (value p)⁻¹ * (value p * value q) * value p := by group
    _ = (value p)⁻¹ * (c : E) * value p := by rw [h]
    _ = (c : E) := by rw [← hc.inv_right.eq]; group

theorem split {c : C} (p q : Word) (h : value (p ++ q) = (c : E)) :
    Holds c p (inverse q) := by
  dsimp [Holds]
  rw [value_inverse, ← h, value_append]
  group

theorem inverted {c : C} {w : Word} (h : value w = (c : E)) :
    value (inverse w) = ((c⁻¹ : C) : E) := by rw [value_inverse, h, Subgroup.coe_inv]

end Tits.CentralCoverLifting.CompatibleGenerators.PowerRootWords
