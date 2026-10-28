module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.Inputs
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Passage

/-!
# Reduction of the elementary D4 class bound to geometry

Generation identifies the elementary subgroup with the full fixed-point group.
Conjugacy descent then identifies its odd-order classes with their ambient
images. The ambient torus/Weyl bound therefore gives the required bound on
elementary conjugacy classes.

The three geometric premises below remain to be proved from `Geometry`.
This conditional reduction does not assert the source class-count theorem.

Sources: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 12.4, 12.5 and 14.8;
GLS3, Theorem 2.8.2.
-/

public section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction

open Theory.AlgebraicGroup ClassBound

universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The actual passage from an ambient count to elementary conjugacy classes.
Generation and fixed-point conjugacy descent are separate premises. -/
theorem elementaryClassBound_of_generation_of_fusion_of_ambientCount
    (S : Geometry K) (n : ℕ)
    (hgen : graphFieldElementarySubgroup S.diagram.toMulEquiv S.frobenius.onPoints n = ⊤)
    (hfusion : OddClassFusion S n) (hcount : AmbientClassBound S n) :
    ElementaryClassBound S n := by
  unfold ElementaryClassBound
  rw [elementaryOddClasses_card_eq_fixed S n hgen,
    fixedOddClasses_card_eq_ambient S n hfusion]
  exact hcount

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
