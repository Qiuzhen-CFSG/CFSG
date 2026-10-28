module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource.Containment
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource.Mathieu
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OrdinarySource.Complete

/-!
# Applying the original Mathieu-cover reductions to the field sieve

The ordinary local A₆ quotient directly excludes the Mathieu triple
cover. In both local cases, the native replacement reduces it to the
six-cover exclusion in a complete smaller SourceContext. Apply the exact
remaining-list sieve and the proved containment, product and commutator
consumers to these two source reductions.

The original Mathieu placement excludes the ordinary Mathieu row in the
covered local case. The higher-field, six-cover and ordinary-local Mathieu
exclusions remain with
qt-d-138-fields-source. The original source setup remains with the final
assembly owner qt-d-1381-source. These are conditional applications, not
completion of 13.8.19–21.
Source: Aschbacher–Smith 13.8.21, printed pp.955–957.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- The ordinary source sieve discharges the Mathieu triple-cover row.
The higher-field, six-cover and ordinary Mathieu exclusions remain with
the field-sieve owner. -/
theorem ordinary_remainingQuotient
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hfield : ¬ HigherFieldAlternative (K ⧸ pCore 2 K))
    (hsix : ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Components.Models.A6Triple))
    (hmathieu : ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22)) :
    RemainingQuotient (K ⧸ pCore 2 K) :=
  remainingQuotient_of_exclusions c.catalogue hfield hsix hmathieu
    (source_no_mathieu_cover_of_ordinary c eL)

/-- Apply the discharged cover row to the actual ordinary containment,
product and commutator consumers, retaining the other exclusion premises. -/
theorem ordinary_sieve_consequences
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hfield : ¬ HigherFieldAlternative (K ⧸ pCore 2 K))
    (hsix : ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Components.Models.A6Triple))
    (hmathieu : ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22)) :
    one L T V₁ ≤ K ∧ RemainingQuotient (K ⧸ pCore 2 K) ∧
      H = K ⊔ (T : Subgroup G) ∧ Source.UH H V₃ = ⁅Source.UH H V₃,K⁆ := by
  have hl := ordinary_remainingQuotient c eL hfield hsix hmathieu
  have hc := ordinary_source_consequences c hl eL
  exact ⟨hc.1,hl,hc.2⟩

/-- The genuine Mathieu replacement discharges its catalogue row in both
local cases. The six-cover, ordinary Mathieu and higher-field exclusions
remain with the field-sieve owner. -/
theorem sieve_consequences_of_six_exclusion
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hfield : ¬ HigherFieldAlternative (K ⧸ pCore 2 K))
    (hsix : ∀ (H' K' : Subgroup G), SourceContext T L V V₁ V₂ V₃ M G₁ H' K' →
      ¬ Nonempty ((K' ⧸ pCore 2 K') ≃* Components.Models.A6Triple))
    (hmathieu : ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22)) :
    one L T V₁ ≤ K ∧ RemainingQuotient (K ⧸ pCore 2 K) ∧
      H = K ⊔ (T : Subgroup G) ∧ Source.UH H V₃ = ⁅Source.UH H V₃,K⁆ :=
  source_consequences_of_exclusions c hfield (hsix H K c) hmathieu
    (source_no_mathieu_cover_of_six_exclusion c hsix)

/-- In the covered local case, the original Mathieu placement removes the
ordinary Mathieu row. The actual replacement also removes the triple
Mathieu row once the common six-cover exclusion is available. -/
theorem covered_sieve_consequences_of_six_exclusion
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (eL : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)
    (hfield : ¬ HigherFieldAlternative (K ⧸ pCore 2 K))
    (hsix : ∀ (H' K' : Subgroup G), SourceContext T L V V₁ V₂ V₃ M G₁ H' K' →
      ¬ Nonempty ((K' ⧸ pCore 2 K') ≃* Components.Models.A6Triple)) :
    one L T V₁ ≤ K ∧ RemainingQuotient (K ⧸ pCore 2 K) ∧
      H = K ⊔ (T : Subgroup G) ∧ Source.UH H V₃ = ⁅Source.UH H V₃,K⁆ :=
  sieve_consequences_of_six_exclusion c hfield hsix (source_no_mathieu_of_covered c eL)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource
