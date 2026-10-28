module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.Contracts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.Setup
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.Inputs

/-!
# Assembly of the further component's model and outer action

Strict enlargement proves the order-two A-action and identifies its actual
fixed A₆ component. Theorem A justifies passing strong quasithinness to the
central quotient before Theorem C is applied. E.6.21 leaves a central
two-cover, which the independent binary calculation must eliminate.

The assembly below still depends on the two explicit outstanding inspections
in `Inputs`: screening the full quotient catalogue and proving the binary
cover and outer-action facts. It does not yet discharge `ModelIdentification`.
Its earlier-source parameters retain exact universal Theorems A and C and
every clause of E.6.8, E.6.18 and E.6.21.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.23,
printed p.254 (PDF p.265).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification
universe u
variable {G : Type u} [Group G] [Finite G] {M V : Subgroup G} {T : Sylow 2 G}

/-- Discharge the published contract once both independent model calculations
are proved. All intermediate action, component, section and cover premises
are constructed from the genuine source configuration. -/
theorem modelIdentification_of_quotient_and_cover [IsElementaryAbelian 2 V]
    (hA : ∀ (D : Type u) [Group D] [Finite D],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple D)
    (hC : ∀ (D : Type u) [Group D] [Finite D],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple D)
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (h15 : HypothesisE615 V)
    (earlier : EarlierResults T M V)
    (hquotient : QuotientRecognition T M V) (hbinary : BinaryCoverAnalysis.{u}) :
    SixAutomorphisms.ModelIdentification M V := by
  let _ := h.elementary
  intro U A L X g d hne Y hY
  let _ := extension_quasisimple hY
  have hs := extension_sqtk h d hne hY
  have hm := hquotient h h15 earlier U A L X g d hne Y hY (quotient_model hA hC h d hne hY)
  have hz := extension_center d hne earlier.odd_core_free hY
  have hp : IsPGroup 2 (center Y) := by
    rw [hz]
    exact pCore_isPGroup
  obtain ⟨hSF, hS, hmodel⟩ := six_fixed_component d hY
  obtain ⟨hcenter, houter⟩ := hbinary Y hs.stronglyQuasithin hp hm
    (actionImage A Y) (action_order_two d hY) (X.subgroupOf Y) hSF hS hmodel
  exact linearModelAction_of_quotient d hY hm hcenter houter

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification
