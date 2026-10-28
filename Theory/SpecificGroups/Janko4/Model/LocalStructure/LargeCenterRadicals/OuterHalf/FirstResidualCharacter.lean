module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.FirstSymmetryReduction

/-!
# The literal first-half membership criterion

The residual of the marked involution centralizer is the checked subgroup
`InvolutionCentralizers.First.QuotientExtension.H`.  This leaf records the
corresponding criterion for every element of the literal first-centralizer
census.  It is the direct bridge from `InnerRelated` to the native first-half
character and keeps the intrinsic relation and its quotient realization
distinct.

Source: Kleidman--Wilson (1988), Corollary 1.1.4; the residual identification
is proved in `OuterHalf.InnerHalves`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Janko4.Cardinality.LocalInvolutionCensus
namespace Janko4.LocalStructure.LargeCenterRadicals.OuterHalf
open Janko4.InvolutionCentralizers.First
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- Membership in the first centralizer's actual triple-cover half is exactly
the intrinsic relation to the marked involution. -/
theorem innerRelated_a_iff_firstHalf (u : H) :
    InnerRelated Janko4.a (eH u) ↔
      (⟨eH u, by
        apply mem_centralizer_singleton_iff.mpr
        simpa only [z_eq_a] using (eH_commute_z u).eq⟩ : centralizer) ∈
        InvolutionCentralizers.First.QuotientExtension.H := by
  let c : centralizer := ⟨eH u, by
    apply mem_centralizer_singleton_iff.mpr
    simpa only [z_eq_a] using (eH_commute_z u).eq⟩
  rw [InnerRelated]
  change eH u ∈ (solvableResidual (centralizer ({Janko4.a} : Set Model))).map
      (centralizer ({Janko4.a} : Set Model)).subtype ↔ c ∈
        InvolutionCentralizers.First.QuotientExtension.H
  rw [← first_innerHalf_eq_residual]
  change centralizer.subtype c ∈ InvolutionCentralizers.First.QuotientExtension.H.map
      centralizer.subtype ↔ c ∈ InvolutionCentralizers.First.QuotientExtension.H
  exact (mem_map_iff_mem (f := centralizer.subtype) centralizer.subtype_injective)

end Janko4.LocalStructure.LargeCenterRadicals.OuterHalf
