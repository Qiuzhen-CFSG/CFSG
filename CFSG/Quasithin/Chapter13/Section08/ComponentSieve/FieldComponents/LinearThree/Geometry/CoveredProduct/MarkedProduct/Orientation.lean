module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.SourceActions
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Residuals

/-!
# Point orientation of the covered component

The fixed diagram involution interchanges the incident point and line
parabolics and preserves their Borel intersection. Composing the previously
marked component map with this involution when necessary therefore orients
all three marks at once. No new component identification is chosen.

Source: Aschbacher–Smith, 13.8.21(1), printed p.957.
-/

@[expose] public section
open Subgroup Matrix.PSL3Two
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct
open ResidualPlacement
namespace MarkedProduct
open Matrix.PSL3Two.MarkedAutomorphisms

private theorem line_map_diagram : lineParabolicSL.map diagram.toMonoidHom =
    pointParabolicSL := by
  rw [← pointParabolic_map_diagram, map_map]
  have he : diagram.toMonoidHom.comp diagram.toMonoidHom = MonoidHom.id SL := by
    apply MonoidHom.ext
    exact diagram_involutive
  rw [he, map_id]

/-- The orientation change preserves the marked Sylow subgroup. -/
theorem borel_map_diagram : borelSL.map diagram.toMonoidHom = borelSL := by
  change (pointParabolicSL ⊓ lineParabolicSL).map diagram.toMonoidHom =
    pointParabolicSL ⊓ lineParabolicSL
  rw [map_inf _ _ _ diagram.injective, pointParabolic_map_diagram,
    line_map_diagram, inf_comm]

variable {G : Type*} [Group G]
variable (H K L T : Subgroup G)
    (eK : Source.starImage H K ≃* BinaryLinearThree.Group)
    (p : ParabolicPlacement H K L T eK)

/-- Orient the already compatible component map to the point parabolic. -/
noncomputable def pointComponentEquiv : Source.starImage H K ≃* BinaryLinearThree.Group := by
  classical
  exact if p.standard = pointParabolicSL then markedComponentEquiv H K L T eK p
    else (markedComponentEquiv H K L T eK p).trans diagram

/-- The full parabolic in point coordinates. -/
theorem pointComponentEquiv_parabolic :
    p.parabolic.map (pointComponentEquiv H K L T eK p).toMonoidHom = pointParabolicSL := by
  classical
  unfold pointComponentEquiv
  split_ifs with h
  · rw [markedComponentEquiv_parabolic, h]
  · change p.parabolic.map (diagram.toMonoidHom.comp
      (markedComponentEquiv H K L T eK p).toMonoidHom) = _
    rw [← map_map, markedComponentEquiv_parabolic, p.standard_eq.resolve_left h,
      line_map_diagram]

/-- The full residual, including its surviving two-core, in the same coordinates. -/
theorem pointComponentEquiv_residual :
    ((Source.starImage H (zero L)).subgroupOf (Source.starImage H K)).map
      (pointComponentEquiv H K L T eK p).toMonoidHom = MarkedAutomorphisms.residual pointParabolicSL := by
  classical
  unfold pointComponentEquiv
  split_ifs with h
  · rw [markedComponentEquiv_residual, h]
    rfl
  · change ((Source.starImage H (zero L)).subgroupOf (Source.starImage H K)).map
      (diagram.toMonoidHom.comp (markedComponentEquiv H K L T eK p).toMonoidHom) = _
    rw [← map_map, markedComponentEquiv_residual, p.standard_eq.resolve_left h]
    change (MarkedAutomorphisms.residual lineParabolicSL).map _ = _
    unfold MarkedAutomorphisms.residual
    rw [map_embedded_pResidual, line_map_diagram]

/-- The actual source Sylow intersection is still the Borel after orientation. -/
theorem pointComponentEquiv_sylow :
    ((Source.starImage H T).subgroupOf (Source.starImage H K)).map
      (pointComponentEquiv H K L T eK p).toMonoidHom = borelSL := by
  classical
  unfold pointComponentEquiv
  split_ifs
  · exact markedComponentEquiv_sylow H K L T eK p
  · change ((Source.starImage H T).subgroupOf (Source.starImage H K)).map
      (diagram.toMonoidHom.comp (markedComponentEquiv H K L T eK p).toMonoidHom) = _
    rw [← map_map, markedComponentEquiv_sylow, borel_map_diagram]

end MarkedProduct
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct
