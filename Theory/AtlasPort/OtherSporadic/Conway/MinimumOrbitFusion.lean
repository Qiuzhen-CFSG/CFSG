/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/MinimumOrbitFusion.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.FirstShapeFullStabilizer
public import Theory.AtlasPort.OtherSporadic.Conway.MinimumShapeSeparation
/-!
Minimum-vector and monomial stabilizer geometry for the concrete Leech isometry group.
The proofs identify coordinate stabilizers and combine orbit geometry with exact counting.

Source: Gerald Höhn, `Atlas/Conway/MinimumOrbitFusion.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

def leechSetFinsetEquiv (S : Set leech) (T : Finset IntegerCoordinates)
    (h : ∀ x : leech, x ∈ S ↔ x.val ∈ T) (hT : ∀ z ∈ T, z ∈ leech) :
    S ≃ {z // z ∈ T} where
  toFun x := ⟨x.val.val,(h x.val).mp x.prop⟩
  invFun z := ⟨⟨z.val,hT z.val z.prop⟩,(h _).mpr z.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem overgroup_minimum_orbit_saturated (H : Subgroup LeechIsometryGroup)
    (hH : monomialSubgroup ≤ H) (base x y : leech) (t : Fin 3)
    (hx : x ∈ MulAction.orbit H base) (hxt : x.val ∈ minimumShape t)
    (hyt : y.val ∈ minimumShape t) : y ∈ MulAction.orbit H base := by
  obtain ⟨r,hr⟩ := MulAction.mem_orbit_iff.mp hx
  obtain ⟨m,hm⟩ := minimumShape_transitive x y t hxt hyt
  let n : H := ⟨monomialEmbedding m,hH ⟨m,rfl⟩⟩
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨n*r,?_⟩
  rw [mul_smul,hr]
  exact hm

theorem overgroup_minimum_orbit_shape (H : Subgroup LeechIsometryGroup) (base x : leech)
    (hbase : integerDot base.val base.val = 32) (hx : x ∈ MulAction.orbit H base) :
    ∃ t : Fin 3, x.val ∈ minimumShape t := by
  obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hx
  have hn := (g.val.prop base base).trans hbase
  exact minimumShape_exhaustive ⟨g.val.val base,hn⟩

theorem first_shape_orbit_contained_forces_monomial (H : Subgroup LeechIsometryGroup)
    (hH : monomialSubgroup ≤ H) (base : leech) (hb : base.val ∈ minimumShape 0)
    (ho : ∀ x ∈ MulAction.orbit H base, x.val ∈ minimumShape 0) : H ≤ monomialSubgroup := by
  rw [← firstShapeStabilizer_eq_monomial]
  have hpres (g : H) (x : leech) (hx : x.val ∈ minimumShape 0) :
      (g.val.val x).val ∈ minimumShape 0 := by
    have hxo := overgroup_minimum_orbit_saturated H hH base base x 0 (MulAction.mem_orbit_self _) hb hx
    obtain ⟨r,hr⟩ := MulAction.mem_orbit_iff.mp hxo
    apply ho
    apply MulAction.mem_orbit_iff.mpr
    exact ⟨g*r,by rw [mul_smul,hr]; rfl⟩
  intro g hg x
  constructor
  · intro hx
    have h := hpres ⟨g⁻¹,H.inv_mem hg⟩ (g.val x) hx
    change (g.val.symm (g.val x)).val ∈ minimumShape 0 at h
    simpa [minimumShape] using h
  · exact hpres ⟨g,hg⟩ x

theorem minimum_partial_union_card (t : Fin 3) (ht : t ≠ 0) :
    (minimumShape 0 ∪ minimumShape t).card = if t = 1 then 98256 else 99408 := by
  rw [Finset.card_union_of_disjoint (minimumShape_disjoint 0 t ht.symm),minimumShape_card,minimumShape_card]
  fin_cases t <;> simp_all

theorem overgroup_no_two_shape_orbit (H : Subgroup LeechIsometryGroup) (base : leech)
    (t : Fin 3) (ht : t ≠ 0)
    (ho : ∀ x : leech, x ∈ MulAction.orbit H base ↔ x.val ∈ minimumShape 0 ∪ minimumShape t) : False := by
  have he := Nat.card_congr (leechSetFinsetEquiv (MulAction.orbit H base)
    (minimumShape 0 ∪ minimumShape t) ho (by
      intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact (minimumShape_sound 0 z hz).1
      · exact (minimumShape_sound t z hz).1))
  rw [Nat.card_eq_fintype_card (α := {z // z ∈ minimumShape 0 ∪ minimumShape t}),
    Fintype.card_coe,minimum_partial_union_card t ht] at he
  have hf := leech_forbidden_orbit_sizes H base
  split_ifs at he with ht1
  · exact hf.1 he
  · exact hf.2.1 he

end Atlas.Conway
