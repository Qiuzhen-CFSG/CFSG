module
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.SylowBasis
public import Theory.Representation.BinaryPermutation.FivePairWreath
public import Mathlib.LinearAlgebra.Basis.Prod

/-!
# The Sylow permutation basis of the deleted pair

The two four-vector core bases form an eight-vector basis. The literal
D₈ wr C₂ Sylow acts on their disjoint union, including factor exchange.
This is the pair-module input to the fixed-space calculation of
Aschbacher--Smith 10.3.1, printed pp.755--756.
-/

@[expose] public section
namespace BinaryPermutation.FiveTensorSquare.Small
abbrev PairPoint := ZMod 4 ⊕ ZMod 4

def pairPoint (g : P) (x : PairPoint) : PairPoint :=
  if g.right = 1 then Sum.map (dihedralPoint (g.left 1)) (dihedralPoint (g.left swapIndex)) x
  else Sum.map (dihedralPoint (g.left 1)) (dihedralPoint (g.left swapIndex)) x.swap

instance pairPointAction : MulAction P PairPoint where
  smul := pairPoint
  one_smul x := by
    change pairPoint 1 x = x
    cases x <;> simp [pairPoint, dihedralPoint_one]
  mul_smul a b x := by
    change pairPoint (a*b) x = pairPoint a (pairPoint b x)
    rcases index_cases a.right with ha | ha <;> rcases index_cases b.right with hb | hb <;>
      cases x <;> simp [pairPoint, RegularWreathProduct.mul_left,
        RegularWreathProduct.mul_right, ha, hb, dihedralPoint_mul]

noncomputable def pairBasis : Module.Basis PairPoint (ZMod 2) (C × C) :=
  coreBasis.prod coreBasis

theorem pairBasis_permuted (g : P) (i : PairPoint) :
    FivePair.wreathRepresentation (embed g) (pairBasis i) = pairBasis (g • i) := by
  change FivePair.wreathRepresentation (embed g) (pairBasis i) = pairBasis (pairPoint g i)
  rw [FivePair.wreathRepresentation_apply]
  change (if g.right = 1 then _ else _) = _
  cases i <;> split_ifs with hg <;>
    simp [pairPoint, pairBasis, hg, embed, coreBasis_permuted,
      FivePair.swapIndex, swapIndex]
end BinaryPermutation.FiveTensorSquare.Small
