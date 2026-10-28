module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.IcosianComparison.Generators
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.IcosianComparison

/-!
# Applying the concrete pair to the carrier comparison

The five relators and generation are discharged for the fixed icosian pair.
The comparison now requires only permutation presentation exactness. This
application retains the actual quotient and both concrete carriers. The
unconditional equivalence still requires that independent exactness proof.

Source: ATLAS `J2G1-P2`; Aschbacher, *Sporadic Groups* (1994), Section 47 and
Lemma 49.5. The imported icosian construction retains Gerald Höhn's attribution.
-/

public section
namespace Sporadic.LeechRelated.J2.IcosianComparison.Generators
open Atlas.Conway
open G2FourModule.Embedding.InnerRealization

/-- The certified pair discharges the comparison's entire generating-pair premise. -/
theorem nonempty_comparison_of_presentationExact
    (hp : Function.Injective Presentation.toCarrier) :
    Nonempty (Carrier ≃* IcosianProjectiveModel) :=
  nonempty_icosianComparison_of_generatingPair hp exists_generatingPair

/-- Discharge the comparison's pair input from the concrete root certificates. -/
theorem nonempty_comparison_of_315_translates
    (hp : Function.Injective Presentation.toCarrier)
    (p : IcosianRootPoint)
    (hr : icosianProjectiveReflection p ∈
      Subgroup.closure ({x, y} : Set IcosianProjectiveModel))
    (g : Fin 315 → Subgroup.closure ({x, y} : Set IcosianProjectiveModel))
    (hg : Function.Injective (fun i => (g i : IcosianProjectiveModel) • p)) :
    Nonempty (Carrier ≃* IcosianProjectiveModel) :=
  nonempty_icosianComparison_of_generatingPair hp
    (exists_generatingPair_of_315_translates p hr g hg)

end Sporadic.LeechRelated.J2.IcosianComparison.Generators
