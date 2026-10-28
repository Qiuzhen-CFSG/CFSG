module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.AdjointRestriction.Curves

/-!
# The integral first-order operators in the folded adjoint comparison

These are the linear coefficients of the literal curves in `Curves`: the
two paired E6 nodes contribute sums of operators, and the singleton nodes
contribute one operator. The reversal agrees with the existing F4 numbering.
No compatibility with the orbit-sum matrix is assumed by these definitions.

The higher divided-power reduction is in `IntegralIntertwining`. Its remaining
root-geometric input is the equality `foldedOperator s i * latticeMatrix =
latticeMatrix * sourceOperator s i` for both signs and all four nodes.

Sources: integral Geck operators; GLS3 §§2.2--2.6; Aschbacher--Smith A.2.17,
printed p.39.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.AdjointRestriction
open Theory.AlgebraicGroup.StandardRootSystem RootPairing.SimpleGeckGroup
attribute [local instance] Classical.decEq
local instance : Fintype typeF4Roots := Fintype.ofFinite _

/-- The signed simple F4 Geck operator over the integral lattice. -/
def sourceOperator (s : Bool) (i : Fin 4) : Matrix SourceIndex SourceIndex ℤ :=
  (simpleFamily (b := typeF4RootPairing_base)).dividedPower (s, sourceIndex i) 1

/-- The signed simple E6 Geck operator over the integral lattice. -/
def targetOperator (s : Bool) (i : Fin 6) : Matrix TwistedE6.Index TwistedE6.Index ℤ :=
  (simpleFamily (b := TwistedE6.Base)).dividedPower (s, simpleIndex i) 1

/-- Linear coefficients of the paired and singleton E6 curves, in F4 numbering. -/
def foldedOperator (s : Bool) (i : Fin 4) : Matrix TwistedE6.Index TwistedE6.Index ℤ :=
  ![targetOperator s 0 + targetOperator s 5,
    targetOperator s 1 + targetOperator s 4,
    targetOperator s 2, targetOperator s 3] i.rev

end TwistedE6.FoldedSubsystem.F4Identification.AdjointRestriction
