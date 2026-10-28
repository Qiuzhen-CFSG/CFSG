module
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation

/-!
# Checked relator operations for the literal J₃ local identities

The operations below preserve word identities in an arbitrary group: cyclic
shift, inversion, free cancellation, multiplication of two relators and
substitution using a letter isolated in an earlier relator. Source leaves are
checked against conjugates of the original eight relators after expanding the
auxiliary generator words. Thus a Schreier table is discovery data only.

`ambient_source_checked` applies the calculus to the literal abstract J₃
presentation, with the signed words already verified in `EnumerationSetup`.
No finiteness, subgroup bound or faithful model action is assumed.

Source: ATLAS J3G1-P1,
https://brauer.maths.qmul.ac.uk/Atlas/spor/J3/mag/J3G1-P1.M .
-/

@[expose] public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations
open Subgroup.CosetWordCertificate

/-- A cyclic shift; this definition also makes sense for an oversized cut. -/
def shift {α : Type*} (w : Word α) (n : Nat) : Word α := w.drop n ++ w.take n

def orient {α : Type*} (w : Word α) (rev : Bool) : Word α :=
  if rev then FreeGroup.invRev w else w

def normalize {α : Type*} [DecidableEq α] (w : Word α) (rev : Bool) (n : Nat) : Word α :=
  reduce (shift (orient (reduce w) rev) n)

variable {G α β : Type*} [Group G]

theorem shift_one (g : α → G) (w : Word α) (n : Nat) (h : eval g w = 1) :
    eval g (shift w n) = 1 := by
  rw [shift, eval_append, mul_eq_one_comm, ← eval_append, List.take_append_drop]
  exact h

theorem orient_one (g : α → G) (w : Word α) (rev : Bool) (h : eval g w = 1) :
    eval g (orient w rev) = 1 := by
  cases rev <;> simp [orient, eval_invRev, h]

theorem normalize_one [DecidableEq α] (g : α → G) (w : Word α)
    (rev : Bool) (n : Nat) (h : eval g w = 1) : eval g (normalize w rev n) = 1 := by
  rw [normalize, eval_reduce]
  exact shift_one g _ n (orient_one g _ rev ((eval_reduce g w).trans h))

/-- Substitute signed words for letters. -/
def expand (f : α → Word β) : Word α → Word β
  | [] => []
  | (a, sign) :: w => (if sign then f a else FreeGroup.invRev (f a)) ++ expand f w

theorem eval_expand (g : β → G) (f : α → Word β) (w : Word α) :
    eval g (expand f w) = eval (fun a => eval g (f a)) w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rcases a with ⟨a, sign⟩
    cases sign <;> simp [expand, eval_append, eval_cons, eval_invRev, ih]

theorem eval_eq_of_reduce_eq [DecidableEq α] (g : α → G) (u v : Word α)
    (h : reduce u = reduce v) : eval g u = eval g v := by
  rw [← eval_reduce g u, h, eval_reduce]

/-- The rest of a relator gives the value of one chosen signed letter. -/
def solution (left right : Word Nat) (sign : Bool) : Word Nat :=
  if sign then FreeGroup.invRev (right ++ left) else right ++ left

theorem letter_eq_solution (g : Nat → G) (left right : Word Nat) (a : Nat)
    (sign : Bool) (h : eval g (left ++ (a, sign) :: right) = 1) :
    g a = eval g (solution left right sign) := by
  have he : eval g ((a, sign) :: (right ++ left)) = 1 := by
    have h' : eval g left * eval g ((a, sign) :: right) = 1 := by
      simpa only [eval_append] using h
    have := mul_eq_one_comm.mp h'
    simpa only [eval_append, eval_cons, mul_assoc] using this
  cases sign
  · simpa [solution, eval_cons, inv_mul_eq_one] using he
  · simpa [solution, eval_invRev, eval_append, eval_cons, mul_eq_one_iff_eq_inv]
      using he

/-- One Tietze substitution, retaining the exact generator numbering. -/
def replace (a : Nat) (v w : Word Nat) : Word Nat :=
  expand (fun b => if b = a then v else [(b, true)]) w

theorem eval_replace (g : Nat → G) (a : Nat) (v w : Word Nat)
    (h : g a = eval g v) : eval g (replace a v w) = eval g w := by
  rw [replace, eval_expand]
  congr 1
  funext b
  by_cases hb : b = a
  · simp [hb, h]
  · simp [hb]

/-- Checked elimination of one letter by an earlier relator. No uniqueness of
its occurrence is required for soundness. -/
theorem substitute_checked (g : Nat → G) (u r out left right : Word Nat)
    (a : Nat) (sign rev : Bool) (n : Nat)
    (hs : r = left ++ (a, sign) :: right)
    (hc : normalize (replace a (solution left right sign) u) rev n = out)
    (hu : eval g u = 1) (hr : eval g r = 1) : eval g out = 1 := by
  rw [← hc]
  apply normalize_one
  rw [eval_replace]
  · exact hu
  · exact letter_eq_solution g left right a sign (hs ▸ hr)

/-- Cancellation between two cyclically shifted relators. -/
theorem difference_checked [DecidableEq α] (g : α → G) (u r out : Word α)
    (i j n : Nat) (flip rev : Bool)
    (hc : normalize (FreeGroup.invRev (shift (orient r flip) j) ++ shift u i)
      rev n = out)
    (hu : eval g u = 1) (hr : eval g r = 1) : eval g out = 1 := by
  rw [← hc]
  apply normalize_one
  rw [eval_append, eval_invRev, shift_one g u i hu,
    shift_one g _ j (orient_one g r flip hr)]
  simp

/-- Soundness of the freely trivial leaves, including the auxiliary definition. -/
theorem free_checked [DecidableEq β] (g : β → G) (f : α → Word β) (out : Word α)
    (hc : reduce (expand f out) = []) : eval (fun a => eval g (f a)) out = 1 := by
  rw [← eval_expand, ← eval_reduce, hc, eval_nil]

/-- A source leaf is checked by free reduction against a conjugate of a source
relator, possibly inverted. The table used to discover it is not an assumption. -/
theorem source_checked [DecidableEq β] (g : β → G) (f : α → Word β)
    (out : Word α) (r q : Word β) (rev : Bool)
    (hc : reduce (expand f out) = reduce (q ++ orient r rev ++ FreeGroup.invRev q))
    (hr : eval g r = 1) : eval (fun a => eval g (f a)) out = 1 := by
  rw [← eval_expand, eval_eq_of_reduce_eq g _ _ hc]
  rw [eval_append, eval_append, eval_invRev, orient_one g r rev hr]
  simp

/-- Apply a checked source leaf in the original abstract presentation. -/
theorem ambient_source_checked (f : Nat → Word (Fin 3)) (out : Word Nat)
    (r : Nat) (q : Word (Fin 3)) (rev : Bool)
    (hc : reduce (expand f out) =
      reduce (q ++ orient (OrderBound.relatorWords r) rev ++ FreeGroup.invRev q)) :
    eval (fun a => eval OrderBound.generator (f a)) out = 1 :=
  source_checked OrderBound.generator f out (OrderBound.relatorWords r) q rev hc
    (OrderBound.generator_relators r)

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations
