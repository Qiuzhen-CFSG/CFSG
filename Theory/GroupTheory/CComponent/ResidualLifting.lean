module
public import Theory.GroupTheory.CComponent.Structure

/-!
# Lifting a C-component from generation of its preimage residual

If the C-components of a quotient component's preimage generate its solvable
residual, at least one of them has nontrivial image. That image is perfect and
subnormal and hence equals the prescribed quotient C-component by minimality.
No solvability condition is imposed on the homomorphism's kernel.

This isolates the group-theoretic use of Aschbacher–Smith A.3.9 and 1.2.1(1)
in 15.3.15(2)/26(2), printed pp.46, 503, 1125 and 1130 of the combined
1 March 2004 manuscript. The residual-generation premise is essential.
-/

public section
namespace Subgroup
variable {G H : Type*} [Group G] [Group H] [Finite G]

/-- Residual generation in the literal preimage suffices to lift a specified
C-component, even when the full kernel is not solvable. -/
theorem exists_cComponent_map_eq_of_preimage_layer
    (f : G →* H) (hf : Function.Surjective f) {E : Subgroup H}
    (hE : E.IsCComponent)
    (hgen : cComponentLayer (E.comap f) = solvableResidual (E.comap f)) :
    ∃ L : Subgroup G, L.IsCComponent ∧ L.map f = E := by
  classical
  let P := E.comap f
  let := hE.perfect
  have hr : ((solvableResidual P).map P.subtype).map f = E := by
    simpa only [solvableResidual_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using map_solvableResidual_comap f hf E
  have hex : ∃ D : Subgroup P, D.IsCComponent ∧ (D.map P.subtype).map f ≠ ⊥ := by
    by_contra hn
    have hz : (cComponentLayer P).map (f.comp P.subtype) ≤ ⊥ := by
      apply map_le_iff_le_comap.mpr
      apply sSup_le
      intro D hD
      apply map_le_iff_le_comap.mp
      have hd : (D.map P.subtype).map f = ⊥ := by
        by_contra hd
        exact hn ⟨D, hD, hd⟩
      simpa only [map_map] using hd.le
    rw [hgen, ← map_map, hr] at hz
    exact hE.ne_bot (le_bot_iff.mp hz)
  obtain ⟨D, hD, hd⟩ := hex
  let L := D.map P.subtype
  have hL : L.IsCComponent := hD.map_subtype (hE.subnormal.comap f)
  have hle : L.map f ≤ E :=
    map_le_iff_le_comap.mpr (map_subtype_le D)
  let := hL.perfect
  refine ⟨L, hL, le_antisymm hle ?_⟩
  exact hE.minimal (L.map f) hle hd (Group.IsPerfect.map f) (hL.subnormal.map hf)

end Subgroup
