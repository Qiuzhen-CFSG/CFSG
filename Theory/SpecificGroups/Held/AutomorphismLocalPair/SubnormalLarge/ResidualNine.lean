module

public import Theory.SpecificGroups.Held.AutomorphismLocalPair.Representative
public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SubnormalLarge.ResidualNine.Definitions
public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SubnormalLarge.ResidualNine.Comparison
public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SubnormalLarge.ResidualNine.PairAction
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual

/-!
# The literal Held residual core quotient has order nine

Conjugating the full seed normalizer to the literal pure pair transfers a
surjection of that pair onto S₃ × S₃. A two-group kernel then gives residual
core quotient of order nine by the general calculation.

The unconditional representative calculation uses the proved comparison of
the full normalizer with the pure pair and the actual quotient homomorphism.
The comparison certifies containment and a matching upper bound; the quotient
certificate identifies the image by its multiplication and the kernel by its
normal word subgroup. The conditional transport theorem remains available.

Source: Aschbacher--Smith 2.3.9(7), printed p.526; GLS3 Table 5.3p, including
the convention for local classes fused by automorphisms.
-/

public section
namespace Held.AutomorphismLocalPair
open Subgroup LocalPairs.PairCoverage.LocalActions.Exhaustion ResidualNine

/-- Transport the actual pair quotient through the marked ambient conjugation.
The two concrete premises are discharged by separate finite certificates. -/
theorem representative_residual_core_quotient_card_of_pair_quotient
    (hcomparison : representativeLargeLocal.map (MulAut.conj pairConjugator).toMonoidHom =
      candidateProduct false 0)
    (f : candidateProduct false 0 →* QuotientModel)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    Nat.card (pResidual 2 representativeLargeLocal ⧸
      pCore 2 (pResidual 2 representativeLargeLocal)) = 9 := by
  let e : representativeLargeLocal ≃* candidateProduct false 0 :=
    (representativeLargeLocal.equivMapOfInjective (MulAut.conj pairConjugator).toMonoidHom
      (MulAut.conj pairConjugator).injective).trans (MulEquiv.subgroupCongr hcomparison)
  exact SymmetricThreeProductResidual.residual_core_quotient_card_of_surjective
    (f.comp e.toMonoidHom) (hf.comp e.surjective)
    (hk.comap_of_injective e.toMonoidHom e.injective)

/-- The two-residual of the full normalizer of `ambient 20 ⊔ ambient 21`, modulo
its intrinsic two-core, has order nine in the original degree-2058 Held carrier. -/
theorem representative_residual_core_quotient_card :
    Nat.card (pResidual 2 representativeLargeLocal ⧸
      pCore 2 (pResidual 2 representativeLargeLocal)) = 9 :=
  representative_residual_core_quotient_card_of_pair_quotient
    representative_map_pairConjugator pairQuotient
    pairQuotient_surjective pairQuotient_kernel_isPGroup

end Held.AutomorphismLocalPair
