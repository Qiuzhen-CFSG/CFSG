module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow.HalfTensor.Model
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow.HalfTensor.Swap
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow.HalfTensor.PairDisplacement.Inner.TensorRank
public import Theory.Representation.G2.NaturalInvolutionRank

/-!
# Inner involution displacement on the concrete G₂ pair

Every nonidentity involution of the actual octonion automorphism group moves
two or three dimensions on the natural quotient. Pulling back by each actual
Frobenius automorphism preserves nonidentity and the square-one equation, and
extension of scalars preserves displacement rank. These facts give the same
rank interval for both literal factors of `pairRep`. The characteristic-two
tensor displacement formula then gives displacement at least sixteen on the
pair, with no rank or conjugacy premise remaining.

This discharges the universal natural no-transvection input and the inner
tensor case of Guralnick–Malle, Classification of 2F-modules II, §3.5 and
Lemma 8.5, manuscript pp.20,55–56; see `G2CubicDegree/Source.md`. In particular,
`pair_inner_displacement` supplies exactly the `hinner` premise of
`pair_displacement_of_inner_bound_and_cases`. It holds for arbitrary twist
positions, without the half-field size or algebraic-closure assumptions.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Representation.BinaryOffender.NaturalTensor

namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.TensorWindow.HalfTensor
variable (F K : Type*) [Field F] [Finite F] [CharP F 2]
  [Field K] [Algebra F K]

/-- Exact scalar-extension rank transport for the actual Frobenius-twisted factor. -/
theorem naturalTwist_operatorFixedCodim (i : ℕ) (g : Atlas.G2.Model F) :
    operatorFixedCodim (naturalTwist F K i g) =
      operatorFixedCodim (Atlas.G2.Natural.action F
        (Atlas.G2.Restricted.frobeniusAutomorphism F i g)) := by
  exact Triality.OuterDisplacement.displacement_finrank_baseChange
    (Atlas.G2.Natural.action F (Atlas.G2.Restricted.frobeniusAutomorphism F i g)) K

/-- Each literal factor of the pair has displacement rank two or three. -/
theorem naturalTwist_involution_fixedCodim_bounds (i : ℕ)
    (g : Atlas.G2.Model F) (hne : g ≠ 1) (hg : g * g = 1) :
    2 ≤ operatorFixedCodim (naturalTwist F K i g) ∧
      operatorFixedCodim (naturalTwist F K i g) ≤ 3 := by
  rw [naturalTwist_operatorFixedCodim]
  let e := Atlas.G2.Restricted.frobeniusAutomorphism F i
  apply Atlas.G2.Natural.InvolutionRank.operatorFixedCodim_bounds
  · intro h
    exact hne (e.injective (h.trans e.map_one.symm))
  · change e g * e g = 1
    rw [← map_mul, hg, map_one]

/-- The natural rank input, on both factors used by the literal pair action. -/
theorem pair_factors_involution_data (i s : ℕ)
    (g : Atlas.G2.Model F) (hne : g ≠ 1) (hg : g * g = 1) :
    (naturalTwist F K i g * naturalTwist F K i g = 1) ∧
    (naturalTwist F K (i + s) g * naturalTwist F K (i + s) g = 1) ∧
    (2 ≤ operatorFixedCodim (naturalTwist F K i g) ∧
      operatorFixedCodim (naturalTwist F K i g) ≤ 3) ∧
    (2 ≤ operatorFixedCodim (naturalTwist F K (i + s) g) ∧
      operatorFixedCodim (naturalTwist F K (i + s) g) ≤ 3) := by
  refine ⟨?_, ?_, naturalTwist_involution_fixedCodim_bounds F K i g hne hg,
    naturalTwist_involution_fixedCodim_bounds F K (i + s) g hne hg⟩
  all_goals rw [← map_mul, hg, map_one]

/-- Every nonidentity involution of the actual G₂ model moves at least sixteen
dimensions on the literal pair. This supplies the inner premise of the full
normalizer displacement assembly. -/
theorem pair_inner_displacement (i s : ℕ)
    (g : Atlas.G2.Model F) (hne : g ≠ 1) (hg : g * g = 1) :
    16 ≤ operatorFixedCodim (k := K) (V := PairSpace F K) (pairRep F K i s g) := by
  exact pair_inner_tensor_displacement_of_factor_bounds F K i s g hg
    (naturalTwist_involution_fixedCodim_bounds F K i g hne hg).1
    (naturalTwist_involution_fixedCodim_bounds F K (i + s) g hne hg).1

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.TensorWindow.HalfTensor
