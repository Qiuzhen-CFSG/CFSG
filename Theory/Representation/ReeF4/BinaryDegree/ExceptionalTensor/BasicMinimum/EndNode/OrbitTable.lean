module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.EndNode.Weights

/-!
# Reflection words for twenty-four end-node weights

The table lists twenty-four distinct nonzero integral coroot-coordinate tuples.
Each is obtained from `(0,0,0,1)` by the specified word in the simple reflections,
using the actual standard F4 Cartan matrix. All finite computations below are
checked by the Lean kernel. The words act from left to right.

Entry eight is the sum of the two adjacent short simple roots, with coroot
coordinates `(0,-1,1,1)`. It is the weight used for the local A2 multiplicity
argument. The table alone makes no assertion that these tuples occur in an
arbitrary representation; the action of normalizer words must establish that.

Source: GLS3, Sections 1.8 and 1.14. The candidate words were found in the parent
`Scratch/ReeF4BasicMinimum/orbits.py`; that search is not used as proof evidence.
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.EndNode

/-- The last fundamental weight in the fixed simple-coroot coordinates. -/
@[expose] def endHighestWeight : Weight := ![0, 0, 0, 1]
/-- The weight of the sum of the two adjacent short simple roots. -/
@[expose] def shortA2Weight : Weight := ![0, -1, 1, 1]
/-- A simple reflection on integral weights, using the actual Cartan matrix. -/
@[expose] def reflectWeight (i : Fin 4) (μ : Weight) : Weight :=
  fun j => μ j - μ i * typeF4CartanMatrix i j

/-- Twenty-four candidate nonzero weights, to be realized by the action. -/
@[expose] def endOrbitWeight : Fin 24 → Weight :=
  ![![0, 0, 0, 1],
    ![0, 0, 1, -1],
    ![0, 1, -1, 0],
    ![1, -1, 1, 0],
    ![-1, 0, 1, 0],
    ![1, 0, -1, 1],
    ![-1, 1, -1, 1],
    ![1, 0, 0, -1],
    ![0, -1, 1, 1],
    ![-1, 1, 0, -1],
    ![0, 0, -1, 2],
    ![0, -1, 2, -1],
    ![0, 0, 1, -2],
    ![0, 1, -2, 1],
    ![0, 1, -1, -1],
    ![1, -1, 0, 1],
    ![1, -1, 1, -1],
    ![-1, 0, 0, 1],
    ![-1, 0, 1, -1],
    ![1, 0, -1, 0],
    ![-1, 1, -1, 0],
    ![0, -1, 1, 0],
    ![0, 0, -1, 1],
    ![0, 0, 0, -1]]

/-- Simple-reflection words producing the coordinate table. -/
@[expose] def endOrbitWord : Fin 24 → List (Fin 4) :=
  ![[],
    [3],
    [3, 2],
    [3, 2, 1],
    [3, 2, 1, 0],
    [3, 2, 1, 2],
    [3, 2, 1, 0, 2],
    [3, 2, 1, 2, 3],
    [3, 2, 1, 0, 2, 1],
    [3, 2, 1, 0, 2, 3],
    [3, 2, 1, 0, 2, 1, 2],
    [3, 2, 1, 0, 2, 1, 3],
    [3, 2, 1, 0, 2, 1, 2, 3],
    [3, 2, 1, 0, 2, 1, 3, 2],
    [3, 2, 1, 0, 2, 1, 2, 3, 2],
    [3, 2, 1, 0, 2, 1, 3, 2, 1],
    [3, 2, 1, 0, 2, 1, 2, 3, 2, 1],
    [3, 2, 1, 0, 2, 1, 3, 2, 1, 0],
    [3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0],
    [3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 2],
    [3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2],
    [3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1],
    [3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2],
    [3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3]]

theorem endOrbitWord_spec : ∀ i : Fin 24,
    (endOrbitWord i).foldl (fun μ j => reflectWeight j μ) endHighestWeight =
      endOrbitWeight i := by decide

theorem endOrbitWeight_injective : Function.Injective endOrbitWeight := by decide

theorem endOrbitWeight_ne_zero : ∀ i : Fin 24, endOrbitWeight i ≠ 0 := by decide

theorem endHighestWeight_eq_basicCoefficient :
    endHighestWeight = fun i => (basicCoefficient (0, 1) i : ℤ) := by decide

theorem endOrbitWeight_eight : endOrbitWeight 8 = shortA2Weight := rfl

theorem shortA2Weight_eq_cartan :
    shortA2Weight = fun i => typeF4CartanMatrix 2 i + typeF4CartanMatrix 3 i := by decide

end ReeF4.BinaryDegree.ExceptionalTensor.EndNode
