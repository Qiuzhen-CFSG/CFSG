module

public import CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.Coordinates
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Intermediate generator contracts for the split local actions

The two source calculations have different inputs. The split natural block
supplies coordinates and three parabolic generators. The quaternion residual
supplies a cubic normalizing the same Sylow image. These contracts keep all
generators in the literal N_G(A)/C_G(A), before identifying either image with
the concrete pair. Their existence is not asserted here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
14.4.4, printed p.1007. The assembly owner must construct both contracts
from the embedded split block and actual residual K = O²(H).
-/

open Subgroup

namespace CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage

variable {G : Type*} [Group G]

/-- Output of the split block calculation. The two first quotient generators
mark the actual T_L image, and the third extends it to L₂T_L. This is a
calculation contract, not a replacement for the split natural block. -/
public structure ParabolicGenerators (A L₂ TL : Subgroup G) (z : A) where
  coordinates : A ≃* BinaryFourSplitPair.E
  point_eq : coordinates z = BinaryFourSplitPair.point
  normalizes : L₂ ⊔ TL ≤ normalizer (A : Set G)
  r : NormalizerAction.Star A
  q : NormalizerAction.Star A
  b : NormalizerAction.Star A
  sylow_generators : quotientImage A TL = closure {r, q}
  parabolic_generators : quotientImage A (L₂ ⊔ TL) = closure {r, q, b}
  row_action : coordinateAction A coordinates r = BinaryFourSplitPair.row
  column_action : coordinateAction A coordinates q = BinaryFourSplitPair.column
  cubic_action : coordinateAction A coordinates b = BinaryFourSplitPair.columnCubic

/-- Output of the quaternion residual calculation, independent of any choice
of coordinates. In particular the cubic is not assumed to be the model
cubic, and no abstract A₄ identification is an input. -/
public structure QuaternionGenerators (A K TL : Subgroup G) where
  c : NormalizerAction.Star A
  cube : c ^ 3 = 1
  nonidentity : c ≠ 1
  normalizes : c ∈ normalizer (quotientImage A TL : Set (NormalizerAction.Star A))
  generation : quotientImage A (K ⊓ normalizer (A : Set G)) =
    quotientImage A TL ⊔ zpowers c

end CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage
