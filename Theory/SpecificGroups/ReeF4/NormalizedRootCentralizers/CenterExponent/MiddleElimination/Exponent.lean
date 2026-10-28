module

public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent
public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.MiddleElimination

/-!
# Applying middle-coordinate elimination to the Ree center exponent

This applies the proved middle-coordinate calculation to the original element
of the actual Ree unipotent subgroup. Only the independent outer-coordinate
elimination remains explicit; the center-exponent assembly owns its discharge.

Source: Aschbacher–Smith 13.6.6, printed p.927 of `refs/quasithin.pdf`;
GLS3 Table 2.4 and 2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
namespace ReeF4.NormalizedRootCentralizers.CenterExponent
open Parabolics
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration

/-- The actual center-exponent consumer with its middle-coordinate premise
discharged. Outer-coordinate elimination remains with its independent producer. -/
theorem unipotent_center_sq_of_outer_elimination (m : ℕ) (hm : 0 < m)
    (houter : ∀ p : PositiveParameters m,
      (∀ i : Fin 8, ∀ t : CoefficientField m,
        Commute (positiveWord m p) (rootWord m i t)) → OuterCoordinatesZero p)
    (x : Model m) (hx : x ∈ unipotent m)
    (hc : ∀ u ∈ unipotent m, Commute x u) : x ^ 2 = 1 :=
  unipotent_center_sq_of_coordinate_elimination m houter (middle_coordinates_zero m hm)
    x hx hc

end ReeF4.NormalizedRootCentralizers.CenterExponent
