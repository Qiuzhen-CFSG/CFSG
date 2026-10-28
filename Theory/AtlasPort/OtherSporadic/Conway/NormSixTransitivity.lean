/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/NormSixTransitivity.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.NormSixShapes
public import Theory.AtlasPort.OtherSporadic.Conway.MinimumVectorStabilizer
/-!
The concrete norm-six Leech shell and its stabilizers.
Coordinate orbit transport and orbit-stabilizer counting identify the full stabilizer.

Source: Gerald Höhn, `Atlas/Conway/NormSixTransitivity.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev normSixBase : leech := normSixVector ((0,0),0)

def normSixOrbitShapes : Finset (Fin 4) := Finset.univ.filter fun t =>
  ∃ x : leech, x ∈ MulAction.orbit LeechIsometryGroup normSixBase ∧ x.val ∈ normSixShape t

theorem normSix_orbit_saturated (x y : leech) (t : Fin 4)
    (hx : x ∈ MulAction.orbit LeechIsometryGroup normSixBase)
    (hxt : x.val ∈ normSixShape t) (hyt : y.val ∈ normSixShape t) :
    y ∈ MulAction.orbit LeechIsometryGroup normSixBase := by
  obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp hx
  obtain ⟨m,hm⟩ := normSixShape_transitive x y t hxt hyt
  exact MulAction.mem_orbit_iff.mpr ⟨monomialEmbedding m * g,by rw [mul_smul,hg]; exact hm⟩

theorem normSix_orbit_union (x : leech) :
    x ∈ MulAction.orbit LeechIsometryGroup normSixBase ↔
      x.val ∈ normSixOrbitShapes.biUnion normSixShape := by
  constructor
  · intro hx
    have hn : integerDot x.val x.val = 48 := by
      obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hx
      exact (g.prop _ _).trans (normSixVector_norm _)
    obtain ⟨t,ht⟩ := (normSixShape_mem x.val).mpr ((sixVectors_iff _).mpr ⟨x.prop,hn⟩)
    exact Finset.mem_biUnion.mpr ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,x,hx,ht⟩,ht⟩
  · intro hx
    obtain ⟨t,ht,hxt⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨y,hy,hyt⟩ := (Finset.mem_filter.mp ht).2
    exact normSix_orbit_saturated y x t hy hyt hxt

theorem normSix_orbit_card :
    Nat.card (MulAction.orbit LeechIsometryGroup normSixBase) =
      ∑ t ∈ normSixOrbitShapes, normSixShapeSize t := by
  rw [Nat.card_congr (leechSetFinsetEquiv _ _ normSix_orbit_union (by
    intro z hz
    obtain ⟨t,_,ht⟩ := Finset.mem_biUnion.mp hz
    exact (normSixShape_sound t z ht).1)),Nat.card_eq_fintype_card,Fintype.card_coe]
  rw [Finset.card_biUnion (by intro s _ t _ hst; exact normSixShape_disjoint s t hst)]
  exact Finset.sum_congr rfl fun t _ => normSixShape_card t

theorem normSixOrbitShapes_contains_odd : 2 ∈ normSixOrbitShapes ∧ 3 ∈ normSixOrbitShapes := by
  constructor
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,zeta.val normSixBase,
      MulAction.mem_orbit_iff.mpr ⟨zeta,rfl⟩,normSixFusion_three_shape⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,normSixBase,
      MulAction.mem_orbit_self _,normSixVector_five_shape⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem normSix_shape_divisibility (T : Finset (Fin 4))
    (h2 : 2 ∈ T) (h3 : 3 ∈ T)
    (hd : (∑ t ∈ T, normSixShapeSize t) ∣ 8315553613086720000) : T = Finset.univ := by
  revert hd h3 h2 T
  decide +kernel

theorem normSixOrbitShapes_eq_univ : normSixOrbitShapes = Finset.univ := by
  apply normSix_shape_divisibility _ normSixOrbitShapes_contains_odd.1
    normSixOrbitShapes_contains_odd.2
  rw [← normSix_orbit_card]
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup LeechIsometryGroup normSixBase)
  rw [Nat.card_prod,leechIsometryGroup_order] at h
  exact ⟨_,h.symm⟩

theorem normSix_full_orbit (x : leech) (hx : integerDot x.val x.val = 48) :
    x ∈ MulAction.orbit LeechIsometryGroup normSixBase := by
  rw [normSix_orbit_union,normSixOrbitShapes_eq_univ]
  obtain ⟨t,ht⟩ := (normSixShape_mem x.val).mpr ((sixVectors_iff _).mpr ⟨x.prop,hx⟩)
  exact Finset.mem_biUnion.mpr ⟨t,Finset.mem_univ _,ht⟩

theorem full_normSix_pretransitive : MulAction.IsPretransitive LeechIsometryGroup (LeechShell 6) := by
  constructor
  intro x y
  obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp (normSix_full_orbit x.val x.prop)
  obtain ⟨h,hh⟩ := MulAction.mem_orbit_iff.mp (normSix_full_orbit y.val y.prop)
  refine ⟨h*g⁻¹,Subtype.ext ?_⟩
  change (h*g⁻¹) • x.val = y.val
  rw [← hg,mul_smul,inv_smul_smul,hh]

end Atlas.Conway
