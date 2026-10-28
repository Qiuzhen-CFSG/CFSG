module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Auxiliary
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.Assembly
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Covered.SourceCalculation

/-!
# The source marked calculation through the full product BL₁

The ordinary and covered natural-action calculations supply
O³(B) ≤ C O₂(B) and [BL₁ : C O₂(BL₁)] = 3, where C is the unchanged
centralizing residual. The actual higher-field model supplies abelianness
of B/O₂(B). Normality relative to BL₁, both normalizations by the source
t, and intrinsic-core displacement discharge the auxiliary transfer.
The output is exactly torus fixation and commutatorOrder ≤ 3 for that t.

In the covered case L₁,+ is the marked cubic subgroup; the index adapter
uses L₁ as its supplement because its full carrier is BL₁. The earlier
source factorization L₁ = L₁,+ L₀ remains explicit. No ZeroPlacement,
natural-action factorization through B*, or C ≤ K premise is used.
The existence statements retain the genuine inverter in T ∩ L, including
its action on L₀/O₂(L₀) in the covered case. The arbitrary-t statements
also allow a downstream assembly to retain an already prescribed inverter.

These complete the conditional local-calculation task from the genuine
SourceContext and ordinary/covered natural setups, using the sufficient
full-product route. The source-alternative owner still supplies the earlier
Borel placement and normalization, the earlier natural data, and the
inner-actor argument in the full proof of 13.8.20. The incompatible stronger
printed intrinsic identities and all their conditional APIs are preserved.

Source: Aschbacher–Smith 13.2.1 and 13.2.2(3), printed p.877;
13.7.3(9), p.936; proof of 13.8.20, p.954/PDF p.971.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
open TorusModels.Assembly
universe u v
variable {G : Type u} [Group G] [Finite G]
namespace SourceContext
variable {T : Sylow 2 G} {H K L V V₁ V₂ V₃ M G₁ : Subgroup G}
  [(Source.starImage H K).Normal] {n : ℕ} {unitary four : Bool}
  (d : SourceContext.{u,v} T H K L V V₁ V₂ V₃ M G₁ n unitary four)

local notation "D" => one L (T : Subgroup G) V₁
local notation "C" => centralizingResidual d.B D L
local notation "J" => (d.B ⊔ D : Subgroup G)

/-- The full-product adapter discharges normalization, model abelianness,
and displacement for the actual source t. Branch residual and index
conclusions are its only local-calculation inputs. -/
theorem marked_calculation_of_full_product
    (hR : residualIn 3 d.B ≤ C ⊔ d.B.pCoreIn 2)
    (hindex : (C ⊔ (J).pCoreIn 2).relIndex J = 3)
    (t : ((T : Subgroup G) ⊓ L : Subgroup G)) :
    ⁅C, zpowers t.val⁆ ≤ (C).pCoreIn 2 ∧
      FixesTorus (residualAt (sourceSylow H K (T : Subgroup G) d.sylow_H))
        (markedActor H K (T : Subgroup G) (d.actorElement t) t.property.1) ∧
      commutatorOrder (residualAt (sourceSylow H K (T : Subgroup G) d.sylow_H))
        (markedActor H K (T : Subgroup G) (d.actorElement t) t.property.1) ≤ 3 := by
  have hJB : J ≤ normalizer (d.B : Set G) :=
    sup_le d.B.le_normalizer (le_sup_left.trans d.borel_normalized)
  have hJC : J ≤ normalizer (C : Set G) :=
    centralizingResidual_normalized _ _ _ _ d.product_normalizes_L
      (J).le_normalizer d.product_normalizes_L
  have hJH : J ≤ H := sup_le
    ((borel_le_component H K (T : Subgroup G) d.component_le d.sylow_H).trans d.component_le)
    d.one_le_H
  have hCt := centralizingResidual_commutator_core _ _ _ d.product_normalizes_L
    t.val t.property.2 (d.T_normalizes_product t.property.1)
  refine ⟨hCt, ?_⟩
  exact marked_calculation_of_overgroup H K (T : Subgroup G) C J D
    d.component_le d.sylow_H rfl (centralizingResidual_le _ _ _) hJH hJB hJC hR
    (ModelBorel.borel_commutator_le_twoCore H K (T : Subgroup G)
      d.component_le d.sylow_H d.model d.degree)
    hindex (d.actorElement t) t.property.1
    (d.borel_normalized (mem_sup_right t.property.1))
    (d.T_normalizes_product t.property.1) hCt

/-- Ordinary source endpoints for the same prescribed member of T ∩ L. -/
theorem marked_calculation_ordinary (a : NaturalSetup L (T : Subgroup G) V V₁)
    (t : ((T : Subgroup G) ⊓ L : Subgroup G)) :
    ⁅C, zpowers t.val⁆ ≤ (C).pCoreIn 2 ∧
      FixesTorus (residualAt (sourceSylow H K (T : Subgroup G) d.sylow_H))
        (markedActor H K (T : Subgroup G) (d.actorElement t) t.property.1) ∧
      commutatorOrder (residualAt (sourceSylow H K (T : Subgroup G) d.sylow_H))
        (markedActor H K (T : Subgroup G) (d.actorElement t) t.property.1) ≤ 3 :=
  d.marked_calculation_of_full_product
    (Ordinary.LocalCalculation.saturated_residual_le d a
      (ModelBorel.borel_commutator_le_twoCore H K (T : Subgroup G)
        d.component_le d.sylow_H d.model d.degree))
    (Ordinary.LocalCalculation.cubic_index d a) t

/-- Covered source endpoints use the full L₁ carrier and the actual natural
setup. Only the exact earlier 13.2.2(3) factorization remains explicit. -/
theorem marked_calculation_covered
    (a : LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃)
    (hfactor : D = plus L (T : Subgroup G) V₁ ⊔ zero L)
    (t : ((T : Subgroup G) ⊓ L : Subgroup G)) :
    ⁅C, zpowers t.val⁆ ≤ (C).pCoreIn 2 ∧
      FixesTorus (residualAt (sourceSylow H K (T : Subgroup G) d.sylow_H))
        (markedActor H K (T : Subgroup G) (d.actorElement t) t.property.1) ∧
      commutatorOrder (residualAt (sourceSylow H K (T : Subgroup G) d.sylow_H))
        (markedActor H K (T : Subgroup G) (d.actorElement t) t.property.1) ≤ 3 :=
  d.marked_calculation_of_full_product
    (Covered.SourceCalculation.borel_threeResidual_le d a hfactor)
    (Covered.ZeroPlacement.FullProduct.cubic_index d a hfactor) t

/-- Construct the ordinary inverter and retain it in both marked endpoints. -/
theorem exists_marked_calculation_ordinary (a : NaturalSetup L (T : Subgroup G) V V₁) :
    ∃ t : ((T : Subgroup G) ⊓ L : Subgroup G),
      InvertsTwoCoreQuotient D t.val ∧
      ⁅C, zpowers t.val⁆ ≤ (C).pCoreIn 2 ∧
      FixesTorus (residualAt (sourceSylow H K (T : Subgroup G) d.sylow_H))
        (markedActor H K (T : Subgroup G) (d.actorElement t) t.property.1) ∧
      commutatorOrder (residualAt (sourceSylow H K (T : Subgroup G) d.sylow_H))
        (markedActor H K (T : Subgroup G) (d.actorElement t) t.property.1) ≤ 3 := by
  obtain ⟨t, ht, htL, hinv, _⟩ := Ordinary.Assembly.exists_marked_inverter d a
  exact ⟨⟨t, ht, htL⟩, hinv, d.marked_calculation_ordinary a ⟨t, ht, htL⟩⟩

/-- Construct the covered inverter, retaining its zero-direction fixation
and the same marked actor in the torus and commutator conclusions. -/
theorem exists_marked_calculation_covered
    (a : LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃)
    (hfactor : D = plus L (T : Subgroup G) V₁ ⊔ zero L) :
    ∃ t : ((T : Subgroup G) ⊓ L : Subgroup G),
      InvertsTwoCoreQuotient (plus L (T : Subgroup G) V₁) t.val ∧
      coreAction (zero L) ⟨t.val, L_normalizes_zero L t.property.2⟩ = 1 ∧
      ⁅C, zpowers t.val⁆ ≤ (C).pCoreIn 2 ∧
      FixesTorus (residualAt (sourceSylow H K (T : Subgroup G) d.sylow_H))
        (markedActor H K (T : Subgroup G) (d.actorElement t) t.property.1) ∧
      commutatorOrder (residualAt (sourceSylow H K (T : Subgroup G) d.sylow_H))
        (markedActor H K (T : Subgroup G) (d.actorElement t) t.property.1) ≤ 3 := by
  obtain ⟨t, hinv, hzero, _⟩ := Covered.SourceCalculation.exists_marked_inverter d a hfactor
  exact ⟨t, hinv, hzero, d.marked_calculation_covered a hfactor t⟩

/-- The ordinary outer case now has no extra local-calculation premise. -/
theorem exceptionalOuter_of_ordinary (a : NaturalSetup L (T : Subgroup G) V V₁)
    (t : ((T : Subgroup G) ⊓ L : Subgroup G))
    (hout : markedActor H K (T : Subgroup G) (d.actorElement t) t.property.1 ∉
      MulAut.innerSubgroup (Source.starImage H K)) :
    ExceptionalOuterAlternative.{u,v} H K (QuotientGroup.mk' (pCore 2 H) (d.actorElement t)) := by
  have hc := d.marked_calculation_ordinary a t
  exact exceptionalOuter_of_local_calculation H K (T : Subgroup G) d.sylow_H d.model d.degree
    (d.actorElement t) t.property.1 hout hc.2.1 hc.2.2

/-- The covered outer case uses the same original t and actual model. -/
theorem exceptionalOuter_of_covered
    (a : LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃)
    (hfactor : D = plus L (T : Subgroup G) V₁ ⊔ zero L)
    (t : ((T : Subgroup G) ⊓ L : Subgroup G))
    (hout : markedActor H K (T : Subgroup G) (d.actorElement t) t.property.1 ∉
      MulAut.innerSubgroup (Source.starImage H K)) :
    ExceptionalOuterAlternative.{u,v} H K (QuotientGroup.mk' (pCore 2 H) (d.actorElement t)) := by
  have hc := d.marked_calculation_covered a hfactor t
  exact exceptionalOuter_of_local_calculation H K (T : Subgroup G) d.sylow_H d.model d.degree
    (d.actorElement t) t.property.1 hout hc.2.1 hc.2.2

end SourceContext
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation
