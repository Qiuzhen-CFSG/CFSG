/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3DecompositionFaithful.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3PointHeptadAction
public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleStabilizer
public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalFourGeometry
/-!
The norm-six stabilizer acting on decompositions into minimum Leech vectors.
The proofs connect the concrete coordinate action with Mathieu incidence geometry.

Source: Gerald Höhn, `Atlas/Conway/Co3DecompositionFaithful.lean`, ATLAS revision
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

abbrev co3MarkedCoordinate : Omega := ((0,0),0)
abbrev Co3MarkedModel := fullVectorStabilizer (normSixVector co3MarkedCoordinate)

theorem co3_point_pair_dot (a b c : Omega) (hb : b ≠ a) (hc : c ≠ a) (hbc : b ≠ c) :
    integerDot (minimumPairPlus a b).val (minimumPairPlus a c).val = 16 := by
  rw [minimumPairPlus_dot]
  simp [minimumPairPlus,coordinateVector,hb,hbc,hc.symm]

theorem co3_point_complement_dot (a b c : Omega) (hb : b ≠ a) (hc : c ≠ a) (hbc : b ≠ c) :
    integerDot (minimumPairPlus a b).val (normSixVector a-minimumPairPlus a c).val = 8 := by
  rw [minimumPairPlus_dot]
  change 4*((normSixVector a).val a-(minimumPairPlus a c).val a+
    ((normSixVector a).val b-(minimumPairPlus a c).val b)) = 8
  simp [normSixVector_apply,minimumPairPlus,coordinateVector,hb,hbc,hc.symm]

theorem co3_decomposition_fixer_point (g : Co3MarkedModel)
    (hg : ∀ p : MinimumDecompositions (normSixVector co3MarkedCoordinate), g • p = p)
    (b : Omega) (hb : b ≠ co3MarkedCoordinate) :
    g.val.val (minimumPairPlus co3MarkedCoordinate b) = minimumPairPlus co3MarkedCoordinate b ∨
    g.val.val (minimumPairPlus co3MarkedCoordinate b) =
      normSixVector co3MarkedCoordinate-minimumPairPlus co3MarkedCoordinate b := by
  have he := congrArg Subtype.val (hg (evenEndpointToDecomposition _ (co3PointEndpoint _ ⟨b,hb⟩)))
  change ({minimumPairPlus co3MarkedCoordinate b,
    normSixVector co3MarkedCoordinate-minimumPairPlus co3MarkedCoordinate b} : Finset leech).image g.val.val =
    {minimumPairPlus co3MarkedCoordinate b,normSixVector co3MarkedCoordinate-minimumPairPlus co3MarkedCoordinate b} at he
  have hm : g.val.val (minimumPairPlus co3MarkedCoordinate b) ∈
      ({minimumPairPlus co3MarkedCoordinate b,
      normSixVector co3MarkedCoordinate-minimumPairPlus co3MarkedCoordinate b} : Finset leech) := by
    rw [← he]
    exact Finset.mem_image.mpr ⟨_,Finset.mem_insert_self _ _,rfl⟩
  simpa only [Finset.mem_insert,Finset.mem_singleton] using hm

theorem co3_point_sum :
    (∑ b ∈ Finset.univ.erase co3MarkedCoordinate, minimumPairPlus co3MarkedCoordinate b) =
      9 • coordinateEight co3MarkedCoordinate + 4 • normSixVector co3MarkedCoordinate := by
  apply Subtype.ext
  decide +kernel

theorem co3_no_all_point_swaps (g : Co3MarkedModel)
    (hs : ∀ b ≠ co3MarkedCoordinate, g.val.val (minimumPairPlus co3MarkedCoordinate b) =
      normSixVector co3MarkedCoordinate-minimumPairPlus co3MarkedCoordinate b) : False := by
  have he := congrArg (fun v : leech => g.val.val v) co3_point_sum
  rw [map_sum,map_add,map_nsmul,map_nsmul,show g.val.val (normSixVector co3MarkedCoordinate) = _ from g.prop] at he
  have hh : (∑ b ∈ Finset.univ.erase co3MarkedCoordinate,
      g.val.val (minimumPairPlus co3MarkedCoordinate b)) =
      23 • normSixVector co3MarkedCoordinate -
        (9 • coordinateEight co3MarkedCoordinate + 4 • normSixVector co3MarkedCoordinate) := by
    rw [← co3_point_sum]
    calc
      _ = ∑ b ∈ Finset.univ.erase co3MarkedCoordinate,
        (normSixVector co3MarkedCoordinate-minimumPairPlus co3MarkedCoordinate b) :=
        Finset.sum_congr rfl (fun b hb => hs b (Finset.mem_erase.mp hb).1)
      _ = _ := by simp [Finset.sum_sub_distrib,Omega,HexIndex]
  rw [hh] at he
  have h := congrArg (fun v : leech => v.val co3MarkedCoordinate) he
  change 23*(normSixVector co3MarkedCoordinate).val co3MarkedCoordinate -
    (9*(coordinateEight co3MarkedCoordinate).val co3MarkedCoordinate+
      4*(normSixVector co3MarkedCoordinate).val co3MarkedCoordinate) =
    9*(g.val.val (coordinateEight co3MarkedCoordinate)).val co3MarkedCoordinate+
      4*(normSixVector co3MarkedCoordinate).val co3MarkedCoordinate at h
  norm_num [normSixVector_apply,coordinateEight,coordinateVector] at h
  omega

theorem co3_all_points_fixed (g : Co3MarkedModel)
    (hg : ∀ p : MinimumDecompositions (normSixVector co3MarkedCoordinate), g • p = p) :
    ∀ b ≠ co3MarkedCoordinate, g.val.val (minimumPairPlus co3MarkedCoordinate b) =
      minimumPairPlus co3MarkedCoordinate b := by
  have hb : ((0,0),1) ≠ co3MarkedCoordinate := by decide
  have hbase := co3_decomposition_fixer_point g hg ((0,0),1) hb
  rcases hbase with hfix | hswap
  · intro c hc
    by_cases he : c = ((0,0),1)
    · subst c; exact hfix
    rcases co3_decomposition_fixer_point g hg c hc with h | h
    · exact h
    · have hd := g.val.prop (minimumPairPlus co3MarkedCoordinate ((0,0),1))
        (minimumPairPlus co3MarkedCoordinate c)
      rw [hfix,h,co3_point_complement_dot _ _ _ hb hc (Ne.symm he),
        co3_point_pair_dot _ _ _ hb hc (Ne.symm he)] at hd
      norm_num at hd
  · exfalso
    apply co3_no_all_point_swaps g
    intro c hc
    by_cases he : c = ((0,0),1)
    · subst c; exact hswap
    rcases co3_decomposition_fixer_point g hg c hc with h | h
    · have hd := g.val.prop (minimumPairPlus co3MarkedCoordinate c)
        (minimumPairPlus co3MarkedCoordinate ((0,0),1))
      rw [h,hswap,co3_point_complement_dot _ _ _ hc hb he,
        co3_point_pair_dot _ _ _ hc hb he] at hd
      norm_num at hd
    · exact h

theorem co3_decompositions_fixer_eq_one (g : Co3MarkedModel)
    (hg : ∀ p : MinimumDecompositions (normSixVector co3MarkedCoordinate), g • p = p) : g = 1 := by
  have hf := co3_all_points_fixed g hg
  have hs := congrArg (fun v : leech => g.val.val v) co3_point_sum
  rw [map_sum,map_add,map_nsmul,map_nsmul,
    show g.val.val (normSixVector co3MarkedCoordinate) = _ from g.prop] at hs
  have he : (∑ b ∈ Finset.univ.erase co3MarkedCoordinate,
      g.val.val (minimumPairPlus co3MarkedCoordinate b)) =
      9 • coordinateEight co3MarkedCoordinate + 4 • normSixVector co3MarkedCoordinate := by
    rw [← co3_point_sum]
    exact Finset.sum_congr rfl (fun b hb => hf b (Finset.mem_erase.mp hb).1)
  rw [he] at hs
  have ha : g.val.val (coordinateEight co3MarkedCoordinate) = coordinateEight co3MarkedCoordinate := by
    apply Subtype.ext; funext i
    have h := congrArg (fun v : leech => v.val i) hs
    change 9*(coordinateEight co3MarkedCoordinate).val i+4*(normSixVector co3MarkedCoordinate).val i =
      9*(g.val.val (coordinateEight co3MarkedCoordinate)).val i+4*(normSixVector co3MarkedCoordinate).val i at h
    omega
  have haxes (i : Omega) : g.val.val (coordinateEight i) = coordinateEight i := by
    by_cases hi : i = co3MarkedCoordinate
    · subst i; exact ha
    have hh : 2 • minimumPairPlus co3MarkedCoordinate i-coordinateEight co3MarkedCoordinate =
        coordinateEight i := by
      apply Subtype.ext; funext j
      change 2*(coordinateVector co3MarkedCoordinate 4 j+coordinateVector i 4 j)-
        coordinateVector co3MarkedCoordinate 8 j = coordinateVector i 8 j
      simp only [coordinateVector,Pi.single_apply]
      split_ifs <;> ring
    rw [← hh,map_sub,map_nsmul,hf i hi,ha]
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  apply Subtype.ext
  funext i
  have h := g.val.prop v (coordinateEight i)
  rw [haxes i] at h
  change integerDot (g.val.val v).val (coordinateVector i 8) = integerDot v.val (coordinateVector i 8) at h
  rw [integerDot_coordinateVector,integerDot_coordinateVector] at h
  change (g.val.val v).val i = v.val i
  omega

theorem co3_decompositions_faithful :
    FaithfulSMul Co3MarkedModel (MinimumDecompositions (normSixVector co3MarkedCoordinate)) where
  eq_of_smul_eq_smul {g h} he := by
    have hh : g⁻¹*h = 1 := co3_decompositions_fixer_eq_one _ (by
      intro p; rw [mul_smul,← he p,inv_smul_smul])
    exact inv_mul_eq_one.mp hh

end Atlas.Conway
