module
public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.OuterElimination.FourthTest
public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.OuterElimination.SecondTest
public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.OuterElimination.SeventhTest

/-!
# Elimination of the five outer coordinates of a central positive Ree word

Commutation with `x₄(1)` kills the main parameters of blocks 1 and 7.
Commutation with `x₂(1)` then kills the paired parameter of block 8.
Finally commutation with `x₇(1)` kills the paired parameter of block 2 and
the central parameter of block 1. Each step compares genuine split-root
coordinates after applying the proved matrix exchanges. In particular no
identification of the center or exponent bound is used.

This supplies the `houter` input of
`CenterExponent.unipotent_center_sq_of_coordinate_elimination`; the two middle
main parameters remain the responsibility of its separate `hmiddle` input.
The calculation also holds at the binary endpoint.

Source: GLS3 Table 2.4 and 2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`;
the root-center assertion used in Aschbacher–Smith 13.6.6, printed p.927 of
`refs/quasithin.pdf`, with A.2.3–4 family conventions.
-/

public section
namespace ReeF4.NormalizedRootCentralizers.CenterExponent
open Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open OuterElimination

/-- The five outer coordinates vanish from literal root-word commutation alone. -/
theorem outerCoordinatesZero_of_commute (m : ℕ) (p : PositiveParameters m)
    (hcomm : ∀ i : Fin 8, ∀ t : CoefficientField m,
      Commute (positiveWord m p) (rootWord m i t)) : OuterCoordinatesZero p := by
  let v := parameters m p
  have h (i : Fin 8) : Commute (splitWord m v) (rootWord m i 1) := by
    rw [← positiveWord_split]
    exact hcomm i 1
  obtain ⟨h0, h18⟩ := detect_fourth m v (h 3)
  have hm0 : p.main 0 = 0 := h0
  have hm2 : p.main 2 = 0 := h18
  have h1 : v 1 = 0 := by
    change halfFrobenius m (p.main 0) = 0
    rw [hm0, map_zero]
  have h19 : v 19 = 0 := by
    change halfFrobenius m (p.main 2) = 0
    rw [hm2, map_zero]
  have h22 := detect_second m v h0 h1 h18 h19 (h 1)
  have hp0 : p.pair 0 = 0 := h22
  have h23 : v 23 = 0 := by
    change halfFrobenius m (p.pair 0) = 0
    rw [hp0, map_zero]
  obtain ⟨hp1, hc0⟩ := detect_seventh m v h0 h1 h18 h19 h22 h23 (h 6)
  exact ⟨hp0, hp1, hm0, hm2, hc0⟩

end ReeF4.NormalizedRootCentralizers.CenterExponent
