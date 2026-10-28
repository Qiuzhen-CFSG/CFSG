module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow.HalfTensor.Model
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow.HalfTensor.Swap
public import Theory.Representation.TensorInvolutionDisplacement

/-!
# Inner tensor displacement on the concrete G₂ pair

The two scalar-extended natural factors have dimension six. Their actual
Frobenius-twisted actions square to one on an involution, so factor displacement
at least two gives tensor displacement at least sixteen. The tensor operator
here is literally the `TensorProduct.map` defining `Representation.tprod`.

This supplies the linear-algebra step in Guralnick–Malle, Classification of
2F-modules II, §3.5 and Lemma 8.5, manuscript pp.20,55–56. The parent `Inner`
module supplies the two natural no-transvection bounds. This module retains
those bounds explicitly and does not import that parent.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Representation.BinaryOffender.NaturalTensor

namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.TensorWindow.HalfTensor
variable (F K : Type*) [Field F] [Finite F] [CharP F 2]
  [Field K] [Algebra F K]

/-- The literal pair action moves at least sixteen dimensions once both natural
factors have displacement at least two. -/
theorem pair_inner_tensor_displacement_of_factor_bounds (i s : ℕ)
    (g : Atlas.G2.Model F) (hg : g * g = 1)
    (hi : 2 ≤ operatorFixedCodim (naturalTwist F K i g))
    (his : 2 ≤ operatorFixedCodim (naturalTwist F K (i + s) g)) :
    16 ≤ operatorFixedCodim (k := K) (V := PairSpace F K) (pairRep F K i s g) := by
  let : CharP K 2 := charP_of_injective_algebraMap (algebraMap F K).injective 2
  have hd : Module.finrank K (NaturalScalarSpace F K) = 6 := by
    rw [Module.finrank_baseChange, Atlas.G2.Natural.finrank_space]
  change 16 ≤ operatorFixedCodim (k := K) (V := PairSpace F K)
    (TensorProduct.map (naturalTwist F K i g) (naturalTwist F K (i + s) g))
  apply Representation.TensorInvolutionDisplacement.sixteen_le_tensor_displacement
    (U := NaturalScalarSpace F K) (W := NaturalScalarSpace F K)
    _ _ hd hd _ _ hi his
  all_goals rw [← map_mul, hg, map_one]

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.TensorWindow.HalfTensor
