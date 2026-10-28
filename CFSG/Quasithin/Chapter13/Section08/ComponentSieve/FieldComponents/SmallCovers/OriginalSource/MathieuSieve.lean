module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource.Application
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource.MathieuComplete

/-!
# Removing the ordinary Mathieu row from the original field sieve

The original local setup now excludes M22 without an F.9.18 selection
premise. In the ordinary A6 local case the earlier argument also excludes
the Mathieu triple cover. In either local case the genuine smaller-context
replacement excludes that cover once the six-cover branch is settled.
Apply these exclusions to the literal component quotient and the already
proved containment, product and commutator deductions.

The higher-field and six-cover exclusions remain with qt-d-138-fields-source;
qt-d-1381-source supplies the preceding SourceContext. These applications
do not assert completion of the whole field sieve.
Source: Aschbacher–Smith, 13.8.21, printed pp.955–957.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- In the ordinary local case both Mathieu rows are discharged. -/
theorem ordinary_remainingQuotient_of_field_and_six_exclusion
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hfield : ¬ HigherFieldAlternative (K ⧸ pCore 2 K))
    (hsix : ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Components.Models.A6Triple)) :
    RemainingQuotient (K ⧸ pCore 2 K) :=
  ordinary_remainingQuotient c eL hfield hsix (source_no_mathieu c)

/-- Apply the completed Mathieu exclusions to the ordinary source conclusions. -/
theorem ordinary_consequences_of_field_and_six_exclusion
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hfield : ¬ HigherFieldAlternative (K ⧸ pCore 2 K))
    (hsix : ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Components.Models.A6Triple)) :
    one L T V₁ ≤ K ∧ RemainingQuotient (K ⧸ pCore 2 K) ∧
      H = K ⊔ (T : Subgroup G) ∧ Source.UH H V₃ = ⁅Source.UH H V₃,K⁆ :=
  ordinary_sieve_consequences c eL hfield hsix (source_no_mathieu c)

/-- In both local cases only the higher-field and six-cover exclusions remain.
The six-cover premise is used also on the actual smaller replacement context. -/
theorem source_consequences_of_field_and_six_exclusion
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hfield : ¬ HigherFieldAlternative (K ⧸ pCore 2 K))
    (hsix : ∀ (H' K' : Subgroup G), SourceContext T L V V₁ V₂ V₃ M G₁ H' K' →
      ¬ Nonempty ((K' ⧸ pCore 2 K') ≃* Components.Models.A6Triple)) :
    one L T V₁ ≤ K ∧ RemainingQuotient (K ⧸ pCore 2 K) ∧
      H = K ⊔ (T : Subgroup G) ∧ Source.UH H V₃ = ⁅Source.UH H V₃,K⁆ :=
  sieve_consequences_of_six_exclusion c hfield hsix (source_no_mathieu c)
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource
