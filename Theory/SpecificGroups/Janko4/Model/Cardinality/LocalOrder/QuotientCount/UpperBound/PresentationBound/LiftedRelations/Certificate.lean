module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.UpperBound.PresentationBound.FirstStabilizer
/-!
# Elementary certificates for lifted presentation relations

Normalize signed words using only the defining relations `x² = y³ = 1`.
Cyclic shifts and inversion preserve the assertion that a word is trivial.
The rewrite rule cancels a common prefix of two words known to be trivial;
its converse reconstructs a longer relation from a shorter one.

These rules check the untrusted Tietze discovery data from GAP's multistage
presentation algorithm (see `../source/README.md`). No permutation computation
or order assertion occurs in the certificate semantics.
-/

@[expose] public section
open Subgroup.CosetWordCertificate
namespace Janko4.Cardinality.QuotientCount.UpperBound.PresentationBound.LiftedRelations

def norm : List (Bool × Bool) → List (Bool × Bool)
  | [] => []
  | (a,s) :: w =>
    match norm w with
    | [] => [(a, if a then s else true)]
    | (b,t) :: v =>
      if a = b then
        if a then (if s = t then (true, !s) :: v else v) else v
      else (a, if a then s else true) :: (b,t) :: v

variable {G : Type*} [Group G] (g : Bool → G)
variable (hx : g false * g false = 1) (hy : g true * g true * g true = 1)

include hx hy in
lemma eval_norm (w : List (Bool × Bool)) : eval g (norm w) = eval g w := by
  have ha : (g false)⁻¹ = g false := by
    exact inv_eq_of_mul_eq_one_left hx
  have hb : g true * g true = (g true)⁻¹ := by
    exact eq_inv_of_mul_eq_one_left hy
  have hc : (g true)⁻¹ * (g true)⁻¹ = g true := by
    rw [← mul_inv_rev, hb, inv_inv]
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [norm, eval_cons, ← ih]
    cases h : norm w with
    | nil => cases a with | mk a s => cases a <;> cases s <;> simp [eval_cons, ha]
    | cons b v =>
      cases a with | mk a s =>
       cases b with | mk b t =>
        cases a <;> cases b <;> cases s <;> cases t <;>
          simp [eval_cons, ha, ← mul_assoc, hx, hb, hc]

def shift (w : List (Bool × Bool)) (n : Nat) := w.drop n ++ w.take n

lemma shift_iff (w : List (Bool × Bool)) (n : Nat) :
    eval g (shift w n) = 1 ↔ eval g w = 1 := by
  conv_rhs => rw [← List.take_append_drop n w]
  rw [shift, eval_append, eval_append]
  exact mul_eq_one_comm

/-- Invert the letters, using only the involutory relation for `x`. -/
def invert (w : List (Bool × Bool)) : List (Bool × Bool) :=
  w.reverse.map (fun a => (a.1, if a.1 then !a.2 else true))

include hx in
lemma eval_invert (w : List (Bool × Bool)) : eval g (invert w) = (eval g w)⁻¹ := by
  have ha : (g false)⁻¹ = g false := inv_eq_of_mul_eq_one_left hx
  induction w with
  | nil => simp [invert]
  | cons a w ih =>
    rcases a with ⟨a, b⟩
    cases a <;> cases b <;>
      simp [invert, List.reverse_cons, List.map_append, eval_append, eval_cons,
        ← ih, invert, ha]

/-- Rotate and optionally invert; already normalized input words stay short. -/
def turn (w : List (Bool × Bool)) (flip : Bool) (n : Nat) :=
  shift (if flip then invert w else w) n

include hx in
lemma turn_iff (w : List (Bool × Bool)) (flip : Bool) (n : Nat) :
    eval g (turn w flip n) = 1 ↔ eval g w = 1 := by
  rw [turn, shift_iff]
  cases flip <;> simp [eval_invert g hx]

def adjust (w : List (Bool × Bool)) (flip : Bool) (n : Nat) :=
  norm (turn w flip n)

include hx hy in
lemma adjust_iff (w : List (Bool × Bool)) (flip : Bool) (n : Nat) :
    eval g (adjust w flip n) = 1 ↔ eval g w = 1 := by
  rw [adjust, eval_norm g hx hy, turn_iff g hx]

include hx hy in
lemma transfer (w v : List (Bool × Bool)) (flip : Bool) (n : Nat)
    (h : adjust w flip n = v) (hv : eval g v = 1) : eval g w = 1 := by
  apply (adjust_iff g hx hy w flip n).mp
  rw [h]
  exact hv

include hx hy in
lemma rewrite_step (w r out : List (Bool × Bool))
    (i : Nat) (flip : Bool) (j k : Nat) (oflip : Bool) (onum : Nat)
    (hp : (turn r flip j).take k = (turn w false i).take k)
    (ho : adjust (FreeGroup.invRev ((turn r flip j).drop k) ++
      (turn w false i).drop k) oflip onum = out)
    (hr : eval g r = 1) (hout : eval g out = 1) : eval g w = 1 := by
  have hv := transfer g hx hy _ _ oflip onum ho hout
  rw [eval_append, eval_invRev, inv_mul_eq_one] at hv
  have hr' := (turn_iff g hx r flip j).mpr hr
  apply (turn_iff g hx w false i).mp
  rw [← List.take_append_drop k (turn r flip j), eval_append, hp, hv] at hr'
  simpa only [← eval_append, List.take_append_drop] using hr'


def substitute {α β : Type*} (s : α → List (β × Bool))
    (w : List (α × Bool)) : List (β × Bool) :=
  w.flatMap (fun a => if a.2 then s a.1 else FreeGroup.invRev (s a.1))

lemma eval_substitute {α β : Type*} (f : β → G) (s : α → List (β × Bool))
    (w : List (α × Bool)) :
    eval f (substitute s w) = eval (fun a => eval f (s a)) w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rcases a with ⟨a, b⟩
    cases b <;> simp [substitute, eval_cons, eval_append, eval_invRev, ← ih]


/-- The certificate assertion is an equality in the original presentation. -/
def Valid (w : List (Bool × Bool)) : Prop :=
  eval (PresentedGroup.of : Bool → Presentation) w = 1

private theorem generator_two :
    (PresentedGroup.of false : Presentation) * PresentedGroup.of false = 1 := by
  have h := presentation_relator 0
  change eval (PresentedGroup.of : Bool → Presentation)
    [(false, true), (false, true)] = 1 at h
  simpa [eval_cons] using h

private theorem generator_three :
    (PresentedGroup.of true : Presentation) * PresentedGroup.of true *
      PresentedGroup.of true = 1 := by
  have h := presentation_relator 1
  change eval (PresentedGroup.of : Bool → Presentation)
    [(true, true), (true, true), (true, true)] = 1 at h
  simpa [eval_cons, mul_assoc] using h

theorem valid_nil : Valid [] := eval_nil _

theorem valid_original (i : Fin 47) (v : List (Bool × Bool)) (flip : Bool) (n : Nat)
    (h : adjust (relatorLetters i) flip n = v) : Valid v := by
  rw [← h]
  exact (adjust_iff _ generator_two generator_three _ _ _).mpr (presentation_relator i)

theorem valid_rewrite (w r out : List (Bool × Bool))
    (i : Nat) (flip : Bool) (j k : Nat) (oflip : Bool) (onum : Nat)
    (hp : (turn r flip j).take k = (turn w false i).take k)
    (ho : adjust (FreeGroup.invRev ((turn r flip j).drop k) ++
      (turn w false i).drop k) oflip onum = out)
    (hr : Valid r) (hout : Valid out) : Valid w :=
  rewrite_step _ generator_two generator_three w r out i flip j k oflip onum hp ho hr hout

/-- Expand a short stabilizer relator into the two original generators. -/
def expanded (i : Fin 43) : List (Bool × Bool) :=
  substitute subgroupWord (stabilizerRelator i)

theorem lifted_of_adjust (i : Fin 43) (v : List (Bool × Bool)) (flip : Bool) (n : Nat)
    (h : adjust (expanded i) flip n = v) (hv : Valid v) :
    eval subgroupGenerator (stabilizerRelator i) = 1 := by
  have he := transfer _ generator_two generator_three _ _ flip n h hv
  rw [expanded, eval_substitute] at he
  exact he

end Janko4.Cardinality.QuotientCount.UpperBound.PresentationBound.LiftedRelations
