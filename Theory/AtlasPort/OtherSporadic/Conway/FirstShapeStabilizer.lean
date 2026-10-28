/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/FirstShapeStabilizer.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalFourCount
public import Theory.AtlasPort.OtherSporadic.Conway.LeechOrbitDivisibility
/-!
Minimum-vector and monomial stabilizer geometry for the concrete Leech isometry group.
The proofs identify coordinate stabilizers and combine orbit geometry with exact counting.

Source: Gerald Höhn, `Atlas/Conway/FirstShapeStabilizer.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

def firstShapeStabilizer : Subgroup LeechIsometryGroup where
  carrier := {g | ∀ x : leech, (g.val x).val ∈ twoFourFamily 0 2 ↔ x.val ∈ twoFourFamily 0 2}
  one_mem' := fun _ => Iff.rfl
  mul_mem' ha hb x := (ha _).trans (hb x)
  inv_mem' {g} hg x := by
    have h := hg (g.val.symm x)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

theorem monomial_le_firstShapeStabilizer : monomialSubgroup ≤ firstShapeStabilizer := by
  rintro g ⟨m,rfl⟩ x
  constructor
  · intro hx
    have hh := monomial_twoFour_invariant m⁻¹ ((monomialEmbedding m).val x) 0 2 hx
    rw [map_inv] at hh
    change ((monomialEmbedding m).val.symm ((monomialEmbedding m).val x)).val ∈ twoFourFamily 0 2 at hh
    simpa only [LinearEquiv.symm_apply_apply] using hh
  · exact monomial_twoFour_invariant m x 0 2

def vectorStabilizerInclusion (H K : Subgroup LeechIsometryGroup) (hHK : H ≤ K) (v : leech) :
    leechVectorStabilizer H v →* leechVectorStabilizer K v where
  toFun g := ⟨⟨g.val.val,hHK g.val.prop⟩,g.prop⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem firstShape_point_orbit_mem (i j : Omega) (hij : i ≠ j) (x : leech)
    (hx : x ∈ MulAction.orbit (leechVectorStabilizer firstShapeStabilizer (minimumPairPlus i j))
      (minimumPairMinus i j)) :
    x.val ∈ twoFourFamily 0 2 ∧ integerDot (minimumPairPlus i j).val x.val = 0 := by
  obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hx
  refine ⟨(g.val.prop _).mpr (minimumPairMinus_four_mem i j hij),?_⟩
  have h := g.val.val.prop (minimumPairPlus i j) (minimumPairMinus i j)
  rw [leechVectorStabilizer_fixes] at h
  exact h.trans (minimumPair_orthogonal i j hij)

theorem firstShape_no_disjoint_fusion (i j : Omega) (hij : i ≠ j)
    (r : leechVectorStabilizer firstShapeStabilizer (minimumPairPlus i j)) :
    ¬ ((r.val.val.val (minimumPairMinus i j)).val i = 0 ∧
       (r.val.val.val (minimumPairMinus i j)).val j = 0) := by
  intro hr
  let K := leechVectorStabilizer firstShapeStabilizer (minimumPairPlus i j)
  let y := minimumPairMinus i j
  let z := r.val.val.val y
  have hz : z.val ∈ twoFourFamily 0 2 := (r.val.prop y).mpr (minimumPairMinus_four_mem i j hij)
  let inc := vectorStabilizerInclusion monomialSubgroup firstShapeStabilizer
    monomial_le_firstShapeStabilizer (minimumPairPlus i j)
  have horbit (x : OrthogonalFourClass i j) : x.val ∈ MulAction.orbit K y := by
    rcases four_orthogonal_partition i j hij x.val x.prop.1 x.prop.2 with (he | he) | hzero
    · rw [he]
      exact MulAction.mem_orbit_self _
    · obtain ⟨s,hs⟩ := monomial_pair_sign_swap i j hij
      apply MulAction.mem_orbit_iff.mpr
      exact ⟨inc s,hs.trans he.symm⟩
    · obtain ⟨s,hs⟩ := orthogonal_disjoint_four_transitive i j hij z x.val hz x.prop.1
        hr.1 hr.2 hzero.1 hzero.2
      apply MulAction.mem_orbit_iff.mpr
      exact ⟨inc s*r,hs⟩
  have he : MulAction.orbit K y ≃ OrthogonalFourClass i j :=
    Equiv.subtypeEquivRight (fun x => ⟨firstShape_point_orbit_mem i j hij x,fun hx => horbit ⟨x,hx⟩⟩)
  have hc : Nat.card (MulAction.orbit K y) = 926 :=
    (Nat.card_congr he).trans (orthogonalFourClass_card i j hij)
  have hd : 463 ∣ Nat.card K := by
    have he := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K y)
    rw [Nat.card_prod,hc] at he
    rw [← he]
    exact dvd_mul_of_dvd_left (by norm_num) _
  let : Fact (Nat.Prime 463) := ⟨by norm_num⟩
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := K) 463 hd
  have hp := leech_prime_order_le g.val.val 463 (by norm_num) (by simpa using hg)
  omega

end Atlas.Conway
