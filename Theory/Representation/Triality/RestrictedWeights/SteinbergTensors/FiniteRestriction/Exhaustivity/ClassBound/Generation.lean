module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Passage
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedSubgroups

/-!
# Reduction of D4 fixed-point generation to its geometric ingredients

Fixed positive and negative unipotents belong to the elementary subgroup.
An actual fixed opposition lift puts the fixed torus there too. Consequently
Steinberg 12.3(a), generation by these three fixed subgroups, implies generation
of all fixed points by two-elements.

The fixed-root/torus generation equality and existence of the opposition lift
remain explicit geometric premises. They must be constructed from `Geometry`
before this reduction proves the unconditional source theorem. In particular,
no representation classification or comparison with a concrete D4 carrier is
assumed here. The reduction has no small-field exception.

Source: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 11.1 and 12.2--12.4.
-/

@[expose] public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound

open Theory.AlgebraicGroup

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The assembly step after fixed-root generation and an actual opposition
lift have been supplied. These geometric premises are not fields of `Geometry`. -/
theorem elementary_eq_top_of_opposition (S : Geometry K) (n : ℕ)
    (hgen : fixedPositive S n ⊔ fixedNegative S n ⊔ fixedTorus S n = ⊤)
    (w : graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n)
    (hw : w ^ 2 ∈ fixedTorus S n)
    (hinv : ∀ t ∈ fixedTorus S n, w * t * w⁻¹ = t⁻¹) :
    graphFieldElementarySubgroup S.diagram.toMulEquiv S.frobenius.onPoints n = ⊤ := by
  apply top_unique
  rw [← hgen]
  exact sup_le (sup_le (positiveFixed_le_elementary S n)
    (fixedNegative_le_elementary S n))
      (fixedTorus_le_elementary_of_opposition S n w hw hinv)

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
