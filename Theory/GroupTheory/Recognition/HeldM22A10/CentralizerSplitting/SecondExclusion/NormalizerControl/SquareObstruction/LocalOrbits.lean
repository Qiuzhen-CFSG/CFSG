module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.Structure
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.Context
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.NormalizerControl.Geometry

/-!
# The outside local orbit in the second Held model

The elementary subgroup F of order sixteen is normal in the actual second
permutation model. Its eight points outside V are mutually conjugate locally.
These two finite calculations suffice for the seven-divisibility square
obstruction: the seven-point ambient orbit of the central involution cannot
meet an orbit containing these eight points. No automorphism classification is used.

Source problem: Huppert--Blackburn III, XII.1.18(b), printed p.314;
D. Held, J. Algebra 8 (1968), 436--449.
-/

namespace Theory.GroupTheory.HeldM22A10.SecondExclusion.NormalizerControl.SquareObstruction
open Subgroup NonsplitModels Model

set_option maxRecDepth 100000

private theorem normal_rows : ∀ i : Fin 384, ∀ j : Fin 16,
    element i * fourRows j * (element i)⁻¹ ∈ fourGroup := by decide +kernel

/-- Normality is in the concrete local group, not in the ambient group. -/
public theorem fourGroup_normal : fourGroup.Normal := by
  constructor
  intro x hx g
  obtain ⟨i, rfl⟩ := element_bijective.2 g
  obtain ⟨j, rfl⟩ := hx
  exact normal_rows i j

private theorem outside_rows : ∀ i : Fin 16, fourRows i ∉ threeGroup →
    ∃ j : Fin 384, element j * outsidePoint * (element j)⁻¹ = fourRows i := by
  decide +kernel

/-- Every point of F outside V is locally conjugate to the marked point. -/
public theorem outside_isConj (x : Second) (hx : x ∈ fourGroup) (hV : x ∉ threeGroup) :
    IsConj outsidePoint x := by
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, hj⟩ := outside_rows i hV
  exact isConj_iff.mpr ⟨element j, hj⟩

end Theory.GroupTheory.HeldM22A10.SecondExclusion.NormalizerControl.SquareObstruction
