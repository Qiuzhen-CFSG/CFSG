module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Inputs
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Inputs
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.TwentyOne
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty
public import Theory.Representation.SU3.FiveSmallModules.Degrees.RootEigenline.NonlinearMultiplicity

/-!
# Assembly of principal-series recognition for the small SU₃(5) modules

The nonlinear root multiplicity calculation reduces the two degrees to
different branches: the root-center fixed space has dimension zero in degree
twenty and one in degree twenty-one. The latter yields a Borel eigenline and
an actual induced-character quotient. The former is recognized as an interior
subquotient by the exhaustive degree-twenty calculation.

The conditional assembly is retained, and `principal_series_recognition`
discharges both inputs over every field of cardinality 25 in `Type` and every
finite characteristic-two coefficient field. The output uses the original
coefficient field, literal Borel induction and actual quotient equivalence.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

public section

namespace Representation.SU3.FiveSmallModules.SevenRestriction

universe u v
open Degrees.RootEigenline

/-- Assembly using the existing nonlinear-root obligation and the independent
degree-twenty branch. All its additional fixed-space premises are discharged. -/
theorem principal_series_recognition_of_nonlinear_and_twenty
    (hnonlinear : RootNonlinearMultiplicityInput.{u, v})
    (htwenty : RootCenterFreeTwentyRecognition.{u, v}) :
    PrincipalSeriesRecognition.{u, v} := by
  intro F _ _ J hc hconj K _ _ _ U _ _ _ τ hk hi hd
  rcases hd with hd | hd
  · obtain ⟨a, ha, hda⟩ := hnonlinear F J hc hconj K U τ hk
    have hz : invariants (τ.comp (standardRootCenter J).subtype) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by omega)
    exact htwenty F J hc hconj K U τ hk hi hd hz
  · exact principal_series_recognition_twenty_one_of_nonlinear
      hnonlinear J hc hconj τ hk hi hd

/-- Every absolute degree-twenty or degree-twenty-one representation of the
standard SU₃(5) group with central kernel is equivalent to a genuine
subquotient of a Borel-induced character over its original field. -/
theorem principal_series_recognition : PrincipalSeriesRecognition.{0, v} :=
  principal_series_recognition_of_nonlinear_and_twenty
    root_nonlinear_multiplicity_input root_center_free_twenty_recognition

end Representation.SU3.FiveSmallModules.SevenRestriction
