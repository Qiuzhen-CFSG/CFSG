module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.BitVec
import Mathlib.Tactic.FinCases

/-!
# The non-root involution orbit in the seven core coordinates

Seven elementary transvections act on the first-row, central and last-column
coordinates. The 42 square-one elements with both side vectors nonzero have
one normal form. The finite certificate records short words in those same
seven conjugations. Matrix transport of these words is proved in `Model`.

Source: Aschbacher, *Sporadic Groups* (1994), 39.1(5), p.213.
-/

public section
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer.CoreFusion
abbrev Coords := Fin 7 → ZMod 2
/-- First row, central entry, and last column of the extraspecial radical. -/
@[expose] def step (k : Fin 7) (v : Coords) : Coords :=
  match k.val with
  | 0 => ![v 0,v 1+v 0,v 2,v 3,v 4+v 5,v 5,v 6]
  | 1 => ![v 0+v 1,v 1,v 2,v 3,v 4,v 5+v 4,v 6]
  | 2 => ![v 0,v 1,v 2+v 1,v 3,v 4,v 5+v 6,v 6]
  | 3 => ![v 0,v 1+v 2,v 2,v 3,v 4,v 5,v 6+v 5]
  | 4 => ![v 0,v 1,v 2,v 3+v 4,v 4,v 5,v 6]
  | 5 => ![v 0,v 1,v 2,v 3+v 5,v 4,v 5,v 6]
  | _ => ![v 0,v 1,v 2,v 3+v 6,v 4,v 5,v 6]
@[expose] def representative : Coords := ![0,1,0,0,1,0,0]
private def encode (v : Coords) : BitVec 7 :=
  BitVec.cons (decide (v 6 = 1)) (BitVec.cons (decide (v 5 = 1))
    (BitVec.cons (decide (v 4 = 1)) (BitVec.cons (decide (v 3 = 1))
      (BitVec.cons (decide (v 2 = 1)) (BitVec.cons (decide (v 1 = 1))
        (BitVec.cons (decide (v 0 = 1)) 0))))))
private def paths : Fin 128 → List (Fin 7) :=
  ![[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[3,2],[],[2],[],[],[],[4],[],[4,3,2],[],[4,2],[],[],[0,1],[],[],[0,1,3,2],[0,2,1],[],[],[],[5,0,1],[],[],[5,0,1,3,2],[5,0,2,1],[],[],[],[],[],[1],[1,3,2],[],[],[2,1],[],[],[],[4,1],[4,1,3,2],[],[],[4,2,1],[],[2,3,0,1],[1,0,2,3,0,1],[0,2,3,0,1],[],[],[],[],[],[6,2,3,0,1],[6,1,0,2,3,0,1],[6,0,2,3,0,1],[],[],[],[],[],[],[1,3,1],[],[],[1,3,2,1],[],[2,3,1],[],[],[4,1,3,1],[],[],[4,1,3,2,1],[],[4,2,3,1],[],[3,0,1],[],[],[],[],[1,3,0,2,1],[3,0,2,1],[],[5,3,0,1],[],[],[],[],[5,1,3,0,2,1],[5,3,0,2,1],[],[],[],[3,1],[],[3,2,1],[2,1,3,1],[],[],[],[],[4,3,1],[],[4,3,2,1],[4,2,1,3,1],[]]

def path (v : Coords) : List (Fin 7) := paths (encode v).toFin

/-- Forty-two involutions outside the two root groups have one normal form
under the specified seven elementary centralizer conjugations. -/
theorem core_normal_form (v : Coords)
    (hs : v 0 * v 4 + v 1 * v 5 + v 2 * v 6 = 0)
    (hr : ¬ (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0))
    (hc : ¬ (v 4 = 0 ∧ v 5 = 0 ∧ v 6 = 0)) :
    (path v).foldl (fun w k => step k w) v = representative := by
  have cert : ∀ a b c d e f g : ZMod 2,
      let v : Coords := ![a,b,c,d,e,f,g]
      v 0 * v 4 + v 1 * v 5 + v 2 * v 6 = 0 →
      ¬ (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0) →
      ¬ (v 4 = 0 ∧ v 5 = 0 ∧ v 6 = 0) →
      (path v).foldl (fun w k => step k w) v = representative := by decide +kernel
  have hv : v = ![v 0,v 1,v 2,v 3,v 4,v 5,v 6] := by
    funext j
    fin_cases j <;> rfl
  simpa only [← hv] using cert (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) hs hr hc

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer.CoreFusion
