module

public import Theory.GroupTheory.CComponent.Structure

/-!
# Transport of radical--component layers

The C-component layer is preserved by isomorphisms, and is characteristic.
Radicals and C-components of a subnormal subgroup lie in the corresponding
ambient layers. Consequently a subnormal subgroup equal to its `O_{∞,E}`
maps into the ordinary component layer of the ambient radical quotient.

The equality `O_{∞,E}(G) = G` is equivalent to the radical quotient being its
ordinary component layer. This follows from the proved C-component quotient
correspondence in `CComponent.Structure`, and explains the quotient formulation
used in Aschbacher--Smith, *The Classification of Quasithin Groups*, E.1.10(4),
p.211; the component transport itself is A.3.3(2), (4)--(5), pp.42--43.
-/

@[expose] public section
open Theory.GroupTheory
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

private theorem map_cComponentLayer_le_equiv (e : G ≃* H) :
    (cComponentLayer G).map e.toMonoidHom ≤ cComponentLayer H := by
  apply map_le_iff_le_comap.mpr
  exact sSup_le fun L hL => map_le_iff_le_comap.mp
    (le_cComponentLayer (hL.map_equiv e))

/-- Isomorphisms preserve the C-component layer. -/
theorem map_cComponentLayer_equiv (e : G ≃* H) :
    (cComponentLayer G).map e.toMonoidHom = cComponentLayer H := by
  apply le_antisymm (map_cComponentLayer_le_equiv e)
  have h := map_mono (f := e.toMonoidHom) (map_cComponentLayer_le_equiv e.symm)
  simpa [map_map] using h

/-- The C-component layer is characteristic. -/
theorem cComponentLayer_characteristic : (cComponentLayer G).Characteristic := by
  apply characteristic_iff_map_eq.mpr
  exact fun e => map_cComponentLayer_equiv e

variable [Finite G] [Finite H]

/-- The source notation `G = O_{∞,E}(G)` has this exact quotient interpretation. -/
theorem oInfELayer_eq_top_iff :
    oInfELayer G = ⊤ ↔ componentLayer (G ⧸ solvableRadical G) = ⊤ := by
  rw [← map_oInfELayer_eq_componentLayer_solvableRadical]
  constructor
  · intro h
    rw [h, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  · intro h
    have hc := congrArg (Subgroup.comap (QuotientGroup.mk' (solvableRadical G))) h
    simpa only [comap_map_eq, QuotientGroup.ker_mk', comap_top,
      sup_eq_left.mpr (show solvableRadical G ≤ oInfELayer G from le_sup_left)] using hc

/-- The radical--C-component layer of a subnormal subgroup lies in the ambient one. -/
theorem map_oInfELayer_subtype_le {N : Subgroup G} (hN : N.IsSubnormal) :
    (oInfELayer N).map N.subtype ≤ oInfELayer G := by
  rw [oInfELayer, map_sup]
  apply sup_le
  · exact (map_solvableRadical_subtype_le_of_isSubnormal hN).trans le_sup_left
  · apply map_le_iff_le_comap.mpr
    exact sSup_le fun L hL => map_le_iff_le_comap.mp
      ((le_cComponentLayer (hL.map_subtype hN)).trans le_sup_right)

/-- The image of a subnormal `O_{∞,E}`-group lies in the layer modulo the radical. -/
theorem map_le_componentLayer_of_oInfELayer_eq_top {N : Subgroup G}
    (hN : N.IsSubnormal) (he : oInfELayer N = ⊤) :
    N.map (QuotientGroup.mk' (solvableRadical G)) ≤
      componentLayer (G ⧸ solvableRadical G) := by
  have hn := map_oInfELayer_subtype_le hN
  rw [he, ← MonoidHom.range_eq_map, range_subtype] at hn
  have hm := map_mono (f := QuotientGroup.mk' (solvableRadical G)) hn
  rwa [map_oInfELayer_eq_componentLayer_solvableRadical] at hm

/-- Isomorphisms preserve the radical--C-component layer. -/
theorem map_oInfELayer_equiv (e : G ≃* H) :
    (oInfELayer G).map e.toMonoidHom = oInfELayer H := by
  rw [oInfELayer, map_sup, map_solvableRadical_equiv, map_cComponentLayer_equiv]
  rfl

/-- Normality of the ordinary layer in a radical-free finite group. -/
theorem componentLayer_normal_of_solvableRadical_eq_bot
    (hG : solvableRadical G = ⊥) : (componentLayer G).Normal := by
  rw [← cComponentLayer_eq_componentLayer_of_solvableRadical_eq_bot hG]
  let := cComponentLayer_characteristic (G := G)
  infer_instance

/-- Isomorphisms of radical-free groups preserve the ordinary layer. -/
theorem map_componentLayer_equiv_of_solvableRadical_eq_bot
    (hG : solvableRadical G = ⊥) (hH : solvableRadical H = ⊥) (e : G ≃* H) :
    (componentLayer G).map e.toMonoidHom = componentLayer H := by
  rw [← cComponentLayer_eq_componentLayer_of_solvableRadical_eq_bot hG,
    ← cComponentLayer_eq_componentLayer_of_solvableRadical_eq_bot hH]
  exact map_cComponentLayer_equiv e

end Subgroup
