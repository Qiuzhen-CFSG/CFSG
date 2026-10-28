module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.SourceData
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.CubicBound

/-!
# Local centralizer displacement and the prescribed cubic actor

The quotient-centralizer definition proves [B_C,⟨t⟩] ≤ O₂(B_C) for every
eligible t in T∩L. The residual inclusion supplies torus fixation, and the
actual index three supplies the small cyclic commutator quotient once the
Borel torus is abelian. Both statements retain the same marked actor.
The outer case then uses the actual higher-field model to produce its
exceptional carrier isomorphism.

The conditional APIs below retain their original intrinsic residual and
index premises. The separate `CentralizingCalculation.SourceAssembly`
extension proves the sufficient full-product source calculation in both
natural-action branches: it uses C O₂(BL₁), the actual model Borel quotient,
and the original marked inverter. It preserves these older APIs and does
not assert the incompatible stronger printed intrinsic identities.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954/PDF p.971.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open TorusModels.Assembly
universe u v
variable {G : Type u} [Group G] [Finite G]
namespace SourceContext
variable {T : Sylow 2 G} {H K L V V₁ V₂ V₃ M G₁ : Subgroup G}
  [(Source.starImage H K).Normal] {n : ℕ} {unitary four : Bool}
  (d : SourceContext.{u,v} T H K L V V₁ V₂ V₃ M G₁ n unitary four)

/-- Regard the chosen source element as an element of H, without changing it. -/
def actorElement (t : ((T : Subgroup G) ⊓ L : Subgroup G)) : H := ⟨t.val, d.T_le_H t.property.1⟩

/-- Derive both inputs to the torus theorem from local identities. The same t
may be chosen by either the ordinary or the covered cubic calculation. -/
theorem marked_calculation_of_local_identities (X : Subgroup G)
    (hR : residualIn 3 d.B ≤ centralizingResidual d.B (one L (T : Subgroup G) V₁) L)
    (habelian : ⁅d.B, d.B⁆ ≤ d.B.pCoreIn 2)
    (hindex : (centralizingResidual d.B (one L (T : Subgroup G) V₁) L ⊔ d.B.pCoreIn 2).relIndex
      (d.B ⊔ X) = 3)
    (t : ((T : Subgroup G) ⊓ L : Subgroup G)) :
    ⁅centralizingResidual d.B (one L (T : Subgroup G) V₁) L, zpowers t.val⁆ ≤
        (centralizingResidual d.B (one L (T : Subgroup G) V₁) L).pCoreIn 2 ∧
      FixesTorus (residualAt (sourceSylow H K (T : Subgroup G) d.sylow_H))
        (markedActor H K (T : Subgroup G) (d.actorElement t) t.property.1) ∧
      commutatorOrder (residualAt (sourceSylow H K (T : Subgroup G) d.sylow_H))
        (markedActor H K (T : Subgroup G) (d.actorElement t) t.property.1) ≤ 3 := by
  refine ⟨centralizingResidual_commutator_core _ _ _ d.product_normalizes_L
    t.val t.property.2 (d.T_normalizes_product t.property.1), ?_, ?_⟩
  · exact markedActor_fixes_of_residual_containment H K (T : Subgroup G) _ L
      d.component_le d.sylow_H d.one_le_H d.product_normalizes_L d.T_normalizes_product
      hR (d.actorElement t) t.property.1 t.property.2
  · exact markedActor_commutatorOrder_le_three_of_index H K (T : Subgroup G) _ L X
      d.component_le d.sylow_H d.product_normalizes_L d.borel_normalized
      (T_normalizes_one L (T : Subgroup G) V₁ d.standing.line_stable)
      habelian hindex (d.actorElement t) t.property.1 t.property.2

/-- An outer actor satisfying the local identities gives the actual exceptional
model alternative. Residual/index/inverter construction remains upstream. -/
theorem exceptionalOuter_of_local_identities (X : Subgroup G)
    (hR : residualIn 3 d.B ≤ centralizingResidual d.B (one L (T : Subgroup G) V₁) L)
    (habelian : ⁅d.B, d.B⁆ ≤ d.B.pCoreIn 2)
    (hindex : (centralizingResidual d.B (one L (T : Subgroup G) V₁) L ⊔ d.B.pCoreIn 2).relIndex
      (d.B ⊔ X) = 3)
    (t : ((T : Subgroup G) ⊓ L : Subgroup G))
    (hout : markedActor H K (T : Subgroup G) (d.actorElement t) t.property.1 ∉
      MulAut.innerSubgroup (Source.starImage H K)) :
    ExceptionalOuterAlternative.{u,v} H K (QuotientGroup.mk' (pCore 2 H) (d.actorElement t)) := by
  have hc := d.marked_calculation_of_local_identities X hR habelian hindex t
  exact exceptionalOuter_of_local_calculation H K (T : Subgroup G) d.sylow_H d.model d.degree
    (d.actorElement t) t.property.1 hout hc.2.1 hc.2.2

end SourceContext
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation
