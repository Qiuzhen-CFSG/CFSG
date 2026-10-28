module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterInvolutionCentralizer.FixedComponents
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.QuotientFixedSource

/-!
# The J₂ outer row of the original 2.5.19 component inspection

The source fixed component survives the actual containing central quotient.
The induced quotient automorphism, its order and component image are retained.
If that literal quotient action is outer on the actual J₂ model, the proved
native fixed-group comparison identifies the original component with PSL₃(2).
No fixed-component classification or representative-comparison premise remains.
The inner row is a separate source case.

Source: Aschbacher–Smith 2.5.19, case (β), pp.561–562.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
open ComponentRefinement ComponentSelection

/-- The original central-quotient outer J₂ branch has component PSL₃(2). -/
theorem source_outer_j2_component {G : Type*} [Group G] [Finite G]
    {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    {E : Type*} [Group E] [Group.IsPerfect E]
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B) (eK : K ≃* B)
    (e : (E ⧸ center E) ≃* Sporadic.LeechRelated.J2.Carrier)
    (hout : ∀ g : E ⧸ center E, quotientAut (center E) a ≠ MulAut.conj g) :
    Nonempty (K ≃* Matrix.PSL3Two.PSL) := by
  obtain ⟨hc,haq,hD,⟨eD⟩⟩ := source_fixed_component_central_quotient
    c hG hempty hgen hb a ha B hB eK
  obtain ⟨f⟩ := Sporadic.LeechRelated.J2.OuterInvolutionCentralizer.outer_component_equiv_of_equiv
    e (quotientAut (center E) a) haq hout _ hD
  exact ⟨eD.trans f⟩
end CFSG.Quasithin.Chapter2.Section05.Overcomponents
