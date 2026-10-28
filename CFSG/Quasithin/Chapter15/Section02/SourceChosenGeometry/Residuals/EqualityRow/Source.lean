module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.LinearThreeSource

/-!
# Excluding a characteristic-two escaping overgroup

The original equality row supplies a normalized component. The full source
action sieve leaves a marked linear-three parabolic, and the direct
natural/doubled-natural endpoint excludes that final row. Thus no actual
escaping overgroup has its generalized Fitting subgroup equal to its two-core.
No extra residual identity or plane-uniqueness premise is used.

Source: Aschbacher--Smith 15.2.16--23, printed pp.1113--1117,
refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I : Subgroup G}
variable {h : ChosenSmallSource T M Mc V}

/-- The original equality row excludes characteristic two for every
escaping overgroup; all component and model witnesses are constructed. -/
theorem ResidualInput.escaping_not_characteristicTwo_of_eq
    (r : ResidualInput h H B)
    (he : partnerSpan H Mc = residual H)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) :
    generalizedFitting I ≠ pCore 2 I := by
  intro hfit
  obtain ⟨X,selection,F,hp⟩ :=
    r.characteristicTwo_linearThree_parabolic_of_eq he hI hfit
  exact r.normalized_component_linearThree_false_of_core_model he hI hfit
    selection F.degree_pos F.card_eq hp
    (r.characteristicTwo_false_of_intersection_le_of_eq he hI hfit)

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
