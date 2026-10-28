module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Inputs
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.PrincipalSpectra.BranchInputs
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.PrincipalSpectra.ActorCoverage
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.PrincipalSpectra.SmallFactors
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.PrincipalSpectra.Subquotients

/-!
# Order-seven spectra in the small principal-series subquotients

An order-seven operator of any principal-series subquotient is also the
operator of an actual order-seven group element. Thus the element calculation
supplies the original contract, including actors of larger order. The checked
trivial and cubic principal-series filtrations give the small simple-factor
spectra; the subquotient argument extends these to every section of dimension
20 or 21, including nonsplit extensions. The final theorem discharges both
inputs and retains arbitrary finite characteristic-two coefficient fields.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

public section

namespace Representation.SU3.FiveSmallModules.SevenRestriction

universe u v

/-- The group-order restriction can be removed without a kernel hypothesis.
The new actor induces the identical operator on the specified subquotient. -/
theorem principal_series_seven_spectra_of_element_spectra
    (h : PrincipalSeriesElementSevenSpectra.{u, v}) :
    PrincipalSeriesSevenSpectra.{u, v} := by
  intro F _ _ J hF hconj K _ _ _ χ S T hd x hx
  exact operator_property_of_order_seven_elements
    (F := F) (K := K) (U := S.toSubmodule ⧸ T.toSubmodule) J hF
    T.quotientRepresentation
    (fun a => a.charpoly = sevenSpectrum K (Module.finrank K (S.toSubmodule ⧸ T.toSubmodule)))
    (h F J hF hconj K χ S T hd) x hx

/-- Every dimension-20 or dimension-21 subquotient of a literal Borel-induced
character has three copies of every nontrivial seventh root, with all remaining
roots equal to one, whenever its operator has order seven. No order hypothesis
on the group element, irreducibility, or central-kernel assumption is needed. -/
theorem principal_series_seven_spectra : PrincipalSeriesSevenSpectra.{0, v} :=
  principal_series_seven_spectra_of_element_spectra
    (principal_series_element_seven_spectra_of_small_factors
      principal_series_small_factor_seven_spectra)

end Representation.SU3.FiveSmallModules.SevenRestriction
