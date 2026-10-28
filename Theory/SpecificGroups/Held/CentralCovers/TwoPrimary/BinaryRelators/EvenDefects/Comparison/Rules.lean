module
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer.Rules
public import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.Group

/-!
# Equality rules retaining central binary defects

A mask records a product of four central involutions. Word equalities retain
this product under reversal, cyclic normalization, composition and generator
substitution. In a substitution the equation's tail is counted once per
occurrence, with either sign. No tail is assumed to vanish.

These rules support the comparison certificate for John Bray's ATLAS Held
presentation, retained in `Held/Model/Source/HeG1-P1.M`.
-/

@[expose] public section
open Theory.GroupTheory.CosetEnumeration
open Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer
namespace Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects.Comparison
abbrev Mask := Fin 16
def mxor (a b : Mask) : Mask := Fin.ofNat 16 (Nat.xor a.val b.val)
structure Tails (G : Type*) [Group G] where
  val : Mask → G
  zero : val 0 = 1
  mul : ∀ a b, val (mxor a b) = val a * val b
  central : ∀ a, val a ∈ Subgroup.center G
  square : ∀ a, val a * val a = 1
variable {G : Type*} [Group G] (t : Tails G) (g : Nat → G)
theorem Tails.move (m : Mask) (a : G) : t.val m * a = a * t.val m :=
  (Subgroup.mem_center_iff.mp (t.central m) a).symm
theorem Tails.inv (m : Mask) : (t.val m)⁻¹ = t.val m :=
  inv_eq_of_mul_eq_one_right (t.square m)
theorem tail_symm {a b : G} {m : Mask} (h : a = b * t.val m) : b = a * t.val m := by
  rw [h, mul_assoc, t.square, mul_one]
theorem tail_trans {a b c : G} {m n : Mask}
    (h : a = b * t.val m) (k : b = c * t.val n) : a = c * t.val (mxor m n) := by
  rw [h, k, t.mul, t.move m (t.val n), mul_assoc]
theorem tail_append {a b c d : G} {m n : Mask}
    (h : a = b * t.val m) (k : c = d * t.val n) : a*c = (b*d) * t.val (mxor m n) := by
  rw [h, k, t.mul]
  simp only [mul_assoc]
  rw [← mul_assoc (t.val m) d, t.move m d, mul_assoc]
theorem tail_inverse {a b : G} {m : Mask} (h : a = b * t.val m) :
    a⁻¹ = b⁻¹ * t.val m := by rw [h, mul_inv_rev, t.inv, t.move]
theorem rotate_tail_iff (w : Word Nat) (n : Nat) (m : Mask) :
    eval g (w.rotate n) = t.val m ↔ eval g w = t.val m := by
  rw [List.rotate_eq_drop_append_take_mod, eval_append]
  conv_rhs => rw [← List.take_append_drop (n % w.length) w, eval_append]
  constructor <;> intro h
  · apply mul_left_cancel (a := eval g (w.drop (n % w.length)))
    rw [← mul_assoc, h, t.move]
  · apply mul_left_cancel (a := eval g (w.take (n % w.length)))
    rw [← mul_assoc, h, t.move]
theorem variant_tail_iff (w : Word Nat) (inv : Bool) (off : Nat) (m : Mask) :
    eval g (variant w inv off) = t.val m ↔ eval g w = t.val m := by
  rw [variant, rotate_tail_iff]
  cases inv
  · rfl
  · simp only [↓reduceIte, eval_inverse, inv_eq_iff_eq_inv, t.inv]
theorem normalize_tail_iff (w : Word Nat) (inv : Bool) (off : Nat) (m : Mask) :
    eval g (normalize w inv off) = t.val m ↔ eval g w = t.val m := by
  rw [normalize, eval_reduce, variant_tail_iff, eval_reduce]
theorem eqrel_tail (u v : Word Nat) (m : Mask)
    (h : eval g (u ++ inverse v) = t.val m) : eval g u = eval g v * t.val m := by
  rw [eval_append, eval_inverse] at h
  have he := (mul_inv_eq_iff_eq_mul).mp h
  exact he.trans (t.move m _)

def substMask (a : Nat) (m : Mask) : Word Nat → Mask
  | [] => 0
  | b :: w => if b.1 = a then mxor m (substMask a m w) else substMask a m w

theorem substitute_tail (a : Nat) (v w : Word Nat) (m : Mask)
    (ha : g a = eval g v * t.val m) :
    eval g (substitute a v w) = eval g w * t.val (substMask a m w) := by
  induction w with
  | nil => simp [substitute, substMask, t.zero]
  | cons b w ih =>
    simp only [substitute, List.flatMap_cons, eval_append] at *
    have hc : eval g (b :: w) = letterValue g b * eval g w := by simp [eval]
    rw [hc]
    by_cases hb : b.1 = a
    · rw [if_pos hb, substMask, if_pos hb]
      apply tail_append t _ ih
      rcases b with ⟨b,s⟩
      dsimp at hb
      subst b
      cases s
      · simpa only [Bool.false_eq_true, ↓reduceIte, eval_inverse, letterValue] using
          tail_inverse t (tail_symm t ha)
      · exact tail_symm t ha
    · rw [if_neg hb, substMask, if_neg hb, eval_singleton, ih, mul_assoc]
end Held.CentralCovers.TwoPrimary.BinaryRelators.EvenDefects.Comparison
