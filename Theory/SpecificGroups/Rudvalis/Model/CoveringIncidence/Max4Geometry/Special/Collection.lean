module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.Coverage.Collection

/-!
# Sound collection of the fixed Rudvalis Sylow words

Replace an adjacent repeated letter by its certified square word, or an
out-of-order pair by the certified inverse-conjugate word. Every finite
number of steps preserves evaluation in the original Rudvalis model.
The later special-core relation checks run this small word calculation;
they do not repeat the degree-4060 permutation comparisons.

The relations come from ElementaryCatalogue.Coverage.Collection, retaining
the ATLAS attribution and left-action convention documented there.
Source application: GLS3 Table 5.3r and its justification, pp.291--292.
-/

@[expose] public section
namespace Rudvalis.CoveringIncidence.Max4Special.Collection
open SylowOvergroups.RadicalCoverage.LocalCover.CatalogueCertificate
open Coverage
set_option maxRecDepth 2000
set_option Elab.async false

def eval (w : List (Fin 14)) : Model := (w.map pcGenerator).prod

def step : List (Fin 14) → List (Fin 14)
  | [] => []
  | [a] => [a]
  | a :: b :: l =>
    if a = b then squareWord a ++ l
    else if b < a then b :: (conjugateWord b a ++ l)
    else a :: step (b :: l)

def collect : ℕ → List (Fin 14) → List (Fin 14)
  | 0, l => l
  | n + 1, l => collect n (step l)

theorem square (i : Fin 14) : pcGenerator i * pcGenerator i = eval (squareWord i) := by
  fin_cases i
  · exact square_0
  · exact square_1
  · exact square_2
  · exact square_3
  · exact square_4
  · exact square_5
  · exact square_6
  · exact square_7
  · exact square_8
  · exact square_9
  · exact square_10
  · exact square_11
  · exact square_12
  · exact square_13

theorem conjugate (i j : Fin 14) (h : i < j) :
    (pcGenerator i)⁻¹ * pcGenerator j * pcGenerator i = eval (conjugateWord i j) := by
  fin_cases i
  · exact conjugate_0 j h
  · exact conjugate_1 j h
  · exact conjugate_2 j h
  · exact conjugate_3 j h
  · exact conjugate_4 j h
  · exact conjugate_5 j h
  · exact conjugate_6 j h
  · exact conjugate_7 j h
  · exact conjugate_8 j h
  · exact conjugate_9 j h
  · exact conjugate_10 j h
  · exact conjugate_11 j h
  · exact conjugate_12 j h
  · exact conjugate_13 j h

theorem step_sound (w : List (Fin 14)) : eval (step w) = eval w := by
  induction w using step.induct with
  | case1 => rfl
  | case2 a => rfl
  | case3 a l =>
    simp only [step, ↓reduceIte, eval, List.map_append, List.prod_append,
      List.map_cons, List.prod_cons, ← mul_assoc]
    change eval (squareWord a) * eval l = (pcGenerator a * pcGenerator a) * eval l
    exact congrArg (· * eval l) (square a).symm
  | case4 a b l hab hlt =>
    simp only [step, if_neg hab, if_pos hlt, eval, List.map_cons, List.prod_cons,
      List.map_append, List.prod_append, ← mul_assoc]
    change (pcGenerator b * eval (conjugateWord b a)) * eval l =
      (pcGenerator a * pcGenerator b) * eval l
    rw [← conjugate b a hlt]
    group
  | case5 a b l hab hlt ih =>
    simpa only [step, if_neg hab, if_neg hlt, eval, List.map_cons, List.prod_cons] using
      congrArg (pcGenerator a * ·) ih

theorem collect_sound (n : ℕ) (w : List (Fin 14)) : eval (collect n w) = eval w := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih => exact (ih (step w)).trans (step_sound w)

theorem eq_of_collect (n : ℕ) (u v : List (Fin 14))
    (h : collect n u = collect n v) : eval u = eval v :=
  (collect_sound n u).symm.trans ((congrArg eval h).trans (collect_sound n v))


end Rudvalis.CoveringIncidence.Max4Special.Collection
