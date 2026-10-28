module
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations.Calculus

/-!
# Incremental normalization of J₃ source leaves

A source leaf can expand to 1812 ambient letters. Reducing after each auxiliary
letter keeps every normalization input in this certificate at length at most
174. The evaluation lemma below justifies this smaller computation in any group;
the source checker then uses the original relators exactly as in `Calculus`.

Source: ATLAS J3G1-P1, https://brauer.maths.qmul.ac.uk/Atlas/spor/J3/mag/J3G1-P1.M .
-/

@[expose] public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations.SixthPower
open Subgroup.CosetWordCertificate

/-- Expand one auxiliary letter at a time, reducing between adjacent blocks. -/
def reducedExpand {α β : Type*} [DecidableEq β] (f : α → Word β) : Word α → Word β
  | [] => []
  | (a, sign) :: w =>
    reduce ((if sign then f a else FreeGroup.invRev (f a)) ++ reducedExpand f w)

theorem eval_reducedExpand {G α β : Type*} [Group G] [DecidableEq β]
    (g : β → G) (f : α → Word β) (w : Word α) :
    eval g (reducedExpand f w) = eval (fun a => eval g (f a)) w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rcases a with ⟨a, sign⟩
    cases sign <;> simp [reducedExpand, eval_reduce, eval_append, eval_cons, eval_invRev, ih]

theorem source_reduced_checked {G α β : Type*} [Group G] [DecidableEq β]
    (g : β → G) (f : α → Word β) (out : Word α)
    (r q : Word β) (rev : Bool)
    (hc : reducedExpand f out = reduce (q ++ orient r rev ++ FreeGroup.invRev q))
    (hr : eval g r = 1) : eval (fun a => eval g (f a)) out = 1 := by
  rw [← eval_reducedExpand, hc, eval_reduce]
  rw [eval_append, eval_append, eval_invRev, orient_one g r rev hr]
  simp

theorem ambient_source_reduced_checked (f : Nat → Word (Fin 3)) (out : Word Nat)
    (r : Nat) (q : Word (Fin 3)) (rev : Bool)
    (hc : reducedExpand f out =
      reduce (q ++ orient (OrderBound.relatorWords r) rev ++ FreeGroup.invRev q)) :
    eval (fun a => eval OrderBound.generator (f a)) out = 1 :=
  source_reduced_checked OrderBound.generator f out (OrderBound.relatorWords r) q rev hc
    (OrderBound.generator_relators r)

theorem free_reduced_checked {G α β : Type*} [Group G] [DecidableEq β]
    (g : β → G) (f : α → Word β) (out : Word α)
    (hc : reducedExpand f out = []) : eval (fun a => eval g (f a)) out = 1 := by
  rw [← eval_reducedExpand, hc, eval_nil]

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations.SixthPower
