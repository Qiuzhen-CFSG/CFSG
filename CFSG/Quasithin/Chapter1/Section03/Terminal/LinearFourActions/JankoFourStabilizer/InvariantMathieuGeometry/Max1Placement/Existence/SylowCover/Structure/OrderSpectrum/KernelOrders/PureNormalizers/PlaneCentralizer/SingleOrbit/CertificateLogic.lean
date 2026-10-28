module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.PairOrbit.Arithmetic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# A finite reachability certificate for the original max2 plane word

Reachability records right-action paths from mask 6607. A balanced union of
blocks in disjoint numeric intervals certifies distinct masks without an
exhaustive orbit calculation or quadratic pairwise comparisons. `SingleOrbit`
transports the paths to actual left conjugators in the original source group.

Source: the retained ATLAS J4G1-max2W1 data and `source/plane-single-orbit.json`;
Kleidman--Wilson (1988), pp.484--510; Aschbacher--Smith A.3.12, pp.47--48.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers.PlaneCentralizer.SingleOrbitData
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData

inductive Reachable : Fin 8192 → Prop
  | root : Reachable 6607
  | step {m n : Fin 8192} (s : Bool) : Reachable m →
      maskAction s m.val = n.val → Reachable n

structure MaskBlock (lo hi n : ℕ) where
  value : Fin n → Fin 8192
  lower : ∀ i, lo ≤ (value i).val
  upper : ∀ i, (value i).val < hi
  injective : Function.Injective value
  reachable : ∀ i, Reachable (value i)

namespace MaskBlock

def leaf (m : Fin 8192) (hi : ℕ) (h : m.val < hi) (hr : Reachable m) :
    MaskBlock m.val hi 1 where
  value := fun _ => m
  lower := fun _ => le_rfl
  upper := fun _ => h
  injective := fun _ _ _ => Subsingleton.elim _ _
  reachable := fun _ => hr

def append {lo mid hi n k : ℕ} (a : MaskBlock lo mid n) (b : MaskBlock mid hi k)
    (hlo : lo ≤ mid) (hhi : mid ≤ hi) : MaskBlock lo hi (n + k) where
  value := Fin.addCases a.value b.value
  lower := by
    intro i
    cases i using Fin.addCases with
    | left i => simpa using a.lower i
    | right i => simpa using hlo.trans (b.lower i)
  upper := by
    intro i
    cases i using Fin.addCases with
    | left i => simpa using (a.upper i).trans_le hhi
    | right i => simpa using b.upper i
  injective := by
    intro i j hij
    cases i using Fin.addCases <;> cases j using Fin.addCases
    · simp only [Fin.addCases_left] at hij
      exact congrArg (Fin.castAdd k) (a.injective hij)
    · rename_i i j
      simp only [Fin.addCases_left, Fin.addCases_right] at hij
      have hx := a.upper i
      have hy := b.lower j
      have he := congrArg Fin.val hij
      omega
    · rename_i i j
      simp only [Fin.addCases_left, Fin.addCases_right] at hij
      have hx := b.lower i
      have hy := a.upper j
      have he := congrArg Fin.val hij
      omega
    · simp only [Fin.addCases_right] at hij
      exact congrArg (Fin.natAdd n) (b.injective hij)
  reachable := by
    intro i
    cases i using Fin.addCases with
    | left i => simpa using a.reachable i
    | right i => simpa using b.reachable i

end MaskBlock
end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders.PureNormalizers.PlaneCentralizer.SingleOrbitData
