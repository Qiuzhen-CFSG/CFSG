module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.Basic

/-!
# Collection with linear merging of polynomial sums

The late checkpoints combine long, sorted polynomial lists. Merge addition
avoids repeated insertion scans. Its evaluation is XOR for arbitrary lists,
proved by induction on fuel; no sortedness assumption enters the soundness
proof. Multiplication and all presentation relations are unchanged.

The consumer is the seven remaining ordered products in ZeroPairs. Each
concrete checkpoint is still certified by the kernel. Source: the original
SylowNormalEights relations; Aschbacher–Smith A.3.12, pp.47–48.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization.GroupTests.ZeroPairs
open PointwiseCalculation Symbolic


def mergeAddFuel : Nat → Poly → Poly → Poly
  | 0, p, q => add p q
  | _+1, [], q => q
  | _+1, p, [] => p
  | n+1, a :: p, b :: q =>
    if a = b then mergeAddFuel n p q
    else if a < b then a :: mergeAddFuel n p (b :: q)
    else b :: mergeAddFuel n (a :: p) q

def mergeAdd (p q : Poly) : Poly := mergeAddFuel (p.length + q.length) p q

theorem polyValue_mergeAddFuel (n : Nat) (p q : Poly) (v : Monomial) :
    polyValue (mergeAddFuel n p q) v = (polyValue p v ^^ polyValue q v) := by
  induction n generalizing p q with
  | zero => exact polyValue_add p q v
  | succ n ih =>
    cases p with
    | nil => simp [mergeAddFuel]
    | cons a p =>
      cases q with
      | nil => simp [mergeAddFuel]
      | cons b q =>
        simp only [mergeAddFuel]
        split
        · rename_i h; subst b
          simp only [ih, polyValue_cons]
          cases monomialValue a v <;> cases polyValue p v <;> cases polyValue q v <;> rfl
        · split <;> simp only [ih, polyValue_cons]
          · cases monomialValue a v <;> cases monomialValue b v <;> cases polyValue p v <;> cases polyValue q v <;> rfl
          · cases monomialValue a v <;> cases monomialValue b v <;> cases polyValue p v <;> cases polyValue q v <;> rfl

theorem polyValue_mergeAdd (p q : Poly) (v : Monomial) :
    polyValue (mergeAdd p q) v = (polyValue p v ^^ polyValue q v) :=
  polyValue_mergeAddFuel _ p q v

open Janko4.LocalStructure.SylowNormalEights Presentation

def fastReplacement (a b : Fin 21) (p q : Poly) : Word :=
  if a = b then [(a, mergeAdd p q)] ++ (squareWord a).map (fun i => (i, mul p q))
  else [(b,q), (a,p)] ++ (conjugateWord b a).tail.map (fun i => (i, mul p q))

theorem fastReplacement_value (a b : Fin 21) (p q : Poly) (v : Monomial) :
    value (fastReplacement a b p q) v = value (replacement a b p q) v := by
  by_cases h : a = b
  · simp only [fastReplacement, replacement, if_pos h, value_append, value_cons,
      value_nil, mul_one, atomValue, polyValue_mergeAdd, polyValue_add]
  · simp only [fastReplacement, replacement, if_neg h]

private theorem fastReplacement_sound (a b : Fin 21) (p q : Poly)
    (h : b ≤ a) (v : Monomial) :
    value (fastReplacement a b p q) v = atomValue v (a,p) * atomValue v (b,q) := by
  have hs := step_sound [(a,p), (b,q)] (clean (replacement a b p q))
    (by simp only [step, if_pos h, List.append_nil]) v
  simpa only [fastReplacement_value, value_clean, value_cons, value_nil, mul_one] using hs

def fastStep : Word → Option Word
  | [] => none
  | [_] => none
  | (a,p) :: (b,q) :: w =>
    if b ≤ a then some (clean (fastReplacement a b p q) ++ w)
    else (fastStep ((b,q) :: w)).map ((a,p) :: ·)

theorem fastStep_sound (u w : Word) (h : fastStep u = some w) (v : Monomial) :
    value w v = value u v := by
  induction u using fastStep.induct generalizing w with
  | case1 => simp [fastStep] at h
  | case2 a => simp [fastStep] at h
  | case3 a p b q l hba =>
    simp only [fastStep, if_pos hba, Option.some.injEq] at h
    subst w
    simp only [value_append, value_clean, fastReplacement_sound a b p q hba,
      value_cons, mul_assoc]
  | case4 a p b q l hba ih =>
    simp only [fastStep, if_neg hba] at h
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [value_cons, ih w hw]

def fastCollect : Nat → Word → Word
  | 0, w => w
  | n+1, w => match fastStep w with
    | none => w
    | some u => fastCollect n u

theorem fastCollect_sound (n : Nat) (w : Word) (v : Monomial) :
    value (fastCollect n w) v = value w v := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    simp only [fastCollect]
    split
    · rfl
    · rename_i u h
      exact (ih u).trans (fastStep_sound w u h v)

theorem value_of_fastCollect (n : Nat) (u w : Word) (h : fastCollect n u = w)
    (v : Monomial) : value w v = value u v := by
  rw [← h]
  exact fastCollect_sound n u v

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization.GroupTests.ZeroPairs
