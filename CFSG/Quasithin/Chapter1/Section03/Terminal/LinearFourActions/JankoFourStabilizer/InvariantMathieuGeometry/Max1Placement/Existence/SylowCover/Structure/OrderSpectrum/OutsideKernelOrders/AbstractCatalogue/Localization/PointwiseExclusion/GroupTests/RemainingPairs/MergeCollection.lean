module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.InterpretationTools
/-!
# Collection with linear merging of polynomial sums

Equal generator exponents add modulo two. Merging two sorted monomial lists
avoids repeated insertion into the growing polynomial. The evaluation proof
works for arbitrary lists and arbitrary fuel, so sortedness is needed only
for efficient canonical output, never as an unproved soundness assumption.
All group rewrites are justified by the original Symbolic.step_sound.

Source: the unchanged SylowNormalEights power-conjugate presentation;
Aschbacher–Smith A.3.12(17), pp.47–48, is the consuming source context.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization.GroupTests.RemainingPairs.MergeCollection
open PointwiseCalculation Symbolic
open Janko4.LocalStructure.SylowNormalEights Presentation
def merge : Nat → Poly → Poly → Poly
  | 0, p, q => p ++ q
  | _+1, [], q => q
  | _+1, p, [] => p
  | n+1, a::p, b::q =>
    if a = b then merge n p q else
    if a < b then a :: merge n p (b::q) else b :: merge n (a::p) q

theorem polyValue_merge (n : Nat) (p q : Poly) (v : Monomial) :
    polyValue (merge n p q) v = (polyValue p v ^^ polyValue q v) := by
  induction n generalizing p q with
  | zero => exact polyValue_append p q v
  | succ n ih =>
    cases p with
    | nil => simp [merge]
    | cons a p =>
      cases q with
      | nil => simp [merge]
      | cons b q =>
        by_cases hab : a = b
        · subst b
          simp only [merge, ↓reduceIte, ih, polyValue_cons]
          cases monomialValue a v <;> cases polyValue p v <;> cases polyValue q v <;> rfl
        · simp only [merge, if_neg hab]
          split <;> simp only [polyValue_cons, ih]
          · cases monomialValue a v <;> cases monomialValue b v <;>
              cases polyValue p v <;> cases polyValue q v <;> rfl
          · cases monomialValue a v <;> cases monomialValue b v <;>
              cases polyValue p v <;> cases polyValue q v <;> rfl

def fastAdd (p q : Poly) : Poly := merge (p.length + q.length) p q

theorem polyValue_fastAdd (p q : Poly) (v : Monomial) :
    polyValue (fastAdd p q) v = (polyValue p v ^^ polyValue q v) :=
  polyValue_merge _ p q v

def replacement (a b : Fin 21) (p q : Poly) : Word :=
  if a = b then [(a, fastAdd p q)] ++ (squareWord a).map (fun i => (i, mul p q))
  else [(b,q), (a,p)] ++ (conjugateWord b a).tail.map (fun i => (i, mul p q))

private theorem replacement_value (a b : Fin 21) (p q : Poly) (v : Monomial) :
    value (replacement a b p q) v = value (Symbolic.replacement a b p q) v := by
  by_cases hab : a = b
  · simp only [replacement, Symbolic.replacement, if_pos hab, value_append,
      value_cons, value_nil, atomValue, polyValue_fastAdd, polyValue_add]
  · simp only [replacement, Symbolic.replacement, if_neg hab]

private theorem replacement_sound (a b : Fin 21) (p q : Poly) (h : b ≤ a)
    (v : Monomial) :
    value (replacement a b p q) v = atomValue v (a,p) * atomValue v (b,q) := by
  rw [replacement_value]
  have hs : Symbolic.step [(a,p), (b,q)] =
      some (clean (Symbolic.replacement a b p q)) := by
    simp only [Symbolic.step, if_pos h, List.append_nil]
  simpa only [value_clean, value_cons, value_nil, mul_one] using Symbolic.step_sound _ _ hs v

def step : Word → Option Word
  | [] => none
  | [_] => none
  | (a,p) :: (b,q) :: w =>
    if b ≤ a then some (clean (replacement a b p q) ++ w)
    else (step ((b,q) :: w)).map ((a,p) :: ·)

theorem step_sound (u w : Word) (h : step u = some w) (v : Monomial) :
    value w v = value u v := by
  induction u using step.induct generalizing w with
  | case1 => simp [step] at h
  | case2 a => simp [step] at h
  | case3 a p b q l hba =>
    simp only [step, if_pos hba, Option.some.injEq] at h
    subst w
    simp only [value_append, value_clean, replacement_sound a b p q hba,
      value_cons, mul_assoc]
  | case4 a p b q l hba ih =>
    simp only [step, if_neg hba] at h
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [value_cons, ih w hw]

def collect : Nat → Word → Word
  | 0, w => w
  | n+1, w => match step w with
    | none => w
    | some u => collect n u

theorem collect_sound (n : Nat) (w : Word) (v : Monomial) :
    value (collect n w) v = value w v := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    simp only [collect]
    split
    · rfl
    · rename_i u h
      exact (ih u).trans (step_sound w u h v)

theorem value_of_collect (n : Nat) (u w : Word) (h : collect n u = w) (v : Monomial) :
    value w v = value u v := by
  rw [← h]
  exact collect_sound n u v

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization.GroupTests.RemainingPairs.MergeCollection
