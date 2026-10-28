module

public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.OuterElimination.SplitWords

/-!
# The remaining split-root tail of a central Ree word

The outer and middle coordinate eliminations leave the ten split roots in
`x₆ x₄ y₅ y₇ y₃` (GLS numbering). We retain their independent split parameters
for the final commutator tests. These are literal matrix words, without a
centrality or classification assertion in their definition.

Source: GLS3 Table 2.4 and 2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`.
The application is the long-root/2-central assertion of Aschbacher–Smith,
16.1.6 and 16.5.13, printed pp.1172 and 1201–1202 of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
namespace ReeF4.EvenInvolutionGeometry.UnipotentCenter
open Parabolics
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open Parabolics.RadicalCoordinates.FixedCoordinates
open MatrixRelations.LongCommutators

/-- The surviving ten split factors in the established positive block order. -/
def tailSplitWord (m : ℕ) (v : Fin 24 → CoefficientField m) : SplitGroup m :=
  X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) *
    (X m 14 (v 14) * (X m 15 (v 15) * (X m 20 (v 20) * (X m 21 (v 21) *
      (X m 8 (v 8) * (X m 9 (v 9) * 1)))))))))

private theorem fieldEnd_half (m : ℕ) (i : Fin 8) :
    rootFieldEnd m (longRoot i) = halfFrobenius m := by
  simp only [rootFieldEnd, if_pos (MatrixRelations.longRoot_isLong i), halfFrobenius]

/-- The third main curve in the split-root numbering used by collection. -/
theorem word_2 (m : ℕ) (t : CoefficientField m) :
    rootWord m 2 t = X m 6 t * X m 7 (halfFrobenius m t) *
      X m 8 (t * halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  rfl

/-- The eighth main curve in the same split-root numbering. -/
theorem word_7 (m : ℕ) (t : CoefficientField m) :
    rootWord m 7 t = X m 22 t * X m 23 (halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  change (X m 22 t * X m 23 (halfFrobenius m t)) * 1 = _
  exact mul_one _

end ReeF4.EvenInvolutionGeometry.UnipotentCenter
