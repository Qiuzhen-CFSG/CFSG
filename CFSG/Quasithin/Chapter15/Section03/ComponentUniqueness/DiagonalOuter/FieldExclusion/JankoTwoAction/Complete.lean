module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.JankoTwoAction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InnerInvolutionCores
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterInvolutionCentralizer.FixedComponents

/-!
# The completed J₂ terminal action calculation

The actual inner-involution data and the proved outer fixed-subgroup
equivalence supply every quotient involution row. The existing perfect-cover
reduction then gives the three-core conclusion with no model premise.

Source: Aschbacher–Smith, proof of 15.3.38, printed p.1137, using the
J₂ centralizer calculations in GLS III, Table 5.3g and note (3).
-/

public section

open Subgroup Theory.GroupTheory MulAut
open Sporadic.LeechRelated.J2
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.JankoTwoAction

/-- The actual inner and outer involution calculations give every J₂ row. -/
theorem involution_data (b : MulAut Carrier) (hb : orderOf b = 2) :
    FixedResidualThreeCoreData b := by
  by_cases hi : b ∈ (MulAut.conj : Carrier →* MulAut Carrier).range
  · exact InnerInvolutionCores.inner_fixedResidualThreeCoreData b hb hi
  · obtain ⟨e⟩ := OuterInvolutionCentralizer.outer_fixed_equiv b hb hi
    exact OuterInvolutionCores.fixedResidualThreeCoreData_of_fixedEquiv b e

/-- The J₂ terminal action calculation for any finite quasisimple cover. -/
theorem threeCoreFreeAction {K A : Type*} [Group K] [Group A]
    [Finite K] [IsQuasisimple K] [IsKleinFour A]
    (e : K ⧸ center K ≃* Carrier)
    (φ : A →* MulAut K) (hinj : Function.Injective φ)
    (hφ : FixesTwoPerfectSubgroups φ) : ThreeCoreFreeAction φ :=
  threeCoreFreeAction_of_j2_involution_data e involution_data φ hinj hφ

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.JankoTwoAction
