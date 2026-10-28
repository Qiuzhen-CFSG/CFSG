/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/OvergroupMinimumTransitivity.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.MinimumOrbitFusion
/-!
Minimum-vector and monomial stabilizer geometry for the concrete Leech isometry group.
The proofs identify coordinate stabilizers and combine orbit geometry with exact counting.

Source: Gerald Höhn, `Atlas/Conway/OvergroupMinimumTransitivity.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem strict_overgroup_minimum_orbit_full (H : Subgroup LeechIsometryGroup)
    (hH : monomialSubgroup < H) (base : leech) (hb : base.val ∈ minimumShape 0)
    (x : leech) (hx : integerDot x.val x.val = 32) : x ∈ MulAction.orbit H base := by
  have hbn := (minimumShape_sound 0 base.val hb).2
  have hs0 (z : leech) (hz : z.val ∈ minimumShape 0) : z ∈ MulAction.orbit H base :=
    overgroup_minimum_orbit_saturated H hH.le base base z 0 (MulAction.mem_orbit_self _) hb hz
  by_contra hxn
  obtain ⟨t,ht⟩ := minimumShape_exhaustive (⟨x,hx⟩ : LeechShell 4)
  have ht0 : t ≠ 0 := by intro he; subst t; exact hxn (hs0 x ht)
  have htmiss (z : leech) (hz : z ∈ MulAction.orbit H base) : z.val ∉ minimumShape t := by
    intro hzt
    exact hxn (overgroup_minimum_orbit_saturated H hH.le base z x t hz hzt ht)
  have hout : ∃ y : leech, y ∈ MulAction.orbit H base ∧ y.val ∉ minimumShape 0 := by
    by_contra hn
    have hle := first_shape_orbit_contained_forces_monomial H hH.le base hb
      (fun y hy => by by_contra hh; exact hn ⟨y,hy,hh⟩)
    exact (not_le_of_gt hH) hle
  obtain ⟨y,hy,hy0⟩ := hout
  obtain ⟨u,hu⟩ := overgroup_minimum_orbit_shape H base y hbn hy
  have hu0 : u ≠ 0 := by intro he; subst u; exact hy0 hu
  have hut : u ≠ t := by intro he; subst u; exact htmiss y hy hu
  apply overgroup_no_two_shape_orbit H base u hu0
  intro z
  constructor
  · intro hz
    obtain ⟨v,hv⟩ := overgroup_minimum_orbit_shape H base z hbn hz
    have hvt : v ≠ t := by intro he; subst v; exact htmiss z hz hv
    have hcases : v = 0 ∨ v = u := by omega
    rcases hcases with rfl | rfl
    · exact Finset.mem_union_left _ hv
    · exact Finset.mem_union_right _ hv
  · intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact hs0 z hz
    · exact overgroup_minimum_orbit_saturated H hH.le base y z u hy hu hz

theorem strict_overgroup_minimum_pretransitive (H : Subgroup LeechIsometryGroup)
    (hH : monomialSubgroup < H) : MulAction.IsPretransitive H (LeechShell 4) := by
  let i : Omega := ((0,0),0)
  let j : Omega := ((0,0),1)
  let base := minimumPairPlus i j
  have hb : base.val ∈ minimumShape 0 := minimumPairPlus_four_mem i j (by decide)
  constructor
  intro x y
  obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp (strict_overgroup_minimum_orbit_full H hH base hb x.val x.prop)
  obtain ⟨h,hh⟩ := MulAction.mem_orbit_iff.mp (strict_overgroup_minimum_orbit_full H hH base hb y.val y.prop)
  refine ⟨h*g⁻¹,?_⟩
  apply Subtype.ext
  change (h*g⁻¹) • x.val = y.val
  rw [← hg,mul_smul,inv_smul_smul,hh]

end Atlas.Conway
