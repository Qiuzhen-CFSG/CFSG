/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/McLGraphDecompositions.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.LeechTriangleSlice
public import Theory.AtlasPort.OtherSporadic.Sporadic.McLaughlin

/-!
The 275 graph vertices as a concrete Leech triangle slice.
Sending a vector to its complementary norm-six decomposition gives a bijection
with the 275 decompositions other than the marked base pair.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/McLGraphDecompositions.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definitions,
preserving source namespaces and the coordinate reductions used across modules.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open Atlas.Sporadic.Conway3
attribute [local instance] Classical.propDecidable

abbrev McLGraphPoints := LeechTriangleSlice (normSixVector co3MarkedCoordinate) mclEndpoint 32 24 16
abbrev McLDecompositionComplement := SubMulAction.ofStabilizer Model basePoint

theorem mcl_normSix_endpoint_dot :
    integerDot (normSixVector co3MarkedCoordinate).val mclEndpoint.val = 24 :=
  normSix_decomposition_dot _ _ mcl_endpoint_norm mcl_other_endpoint_norm

theorem mcl_graph_complement_norm (y : McLGraphPoints) :
    integerDot (normSixVector co3MarkedCoordinate-y.val).val
      (normSixVector co3MarkedCoordinate-y.val).val = 32 := by
  rw [leech_norm_sub,normSixVector_norm,y.prop.1,y.prop.2.1]
  norm_num

def mclGraphDecomposition (y : McLGraphPoints) : Points :=
  ⟨{y.val,normSixVector co3MarkedCoordinate-y.val},
    y.val,y.prop.1,mcl_graph_complement_norm y,rfl⟩

theorem mcl_graph_pair_ne_base (y : McLGraphPoints) : mclGraphDecomposition y ≠ basePoint := by
  intro h
  have hm : y.val ∈ ({mclEndpoint,mclOtherEndpoint} : Finset leech) := by
    rw [← mcl_base_pair,← h]
    exact Finset.mem_insert_self _ _
  rcases Finset.mem_insert.mp hm with hy | hy
  · have hd := y.prop.2.2
    rw [hy,mcl_endpoint_norm] at hd
    omega
  · have hd := y.prop.2.2
    rw [Finset.mem_singleton.mp hy] at hd
    change integerDot mclEndpoint.val ((normSixVector co3MarkedCoordinate).val-mclEndpoint.val) = 16 at hd
    rw [integerDot_sub_right,integerDot_comm mclEndpoint.val,
      mcl_normSix_endpoint_dot,mcl_endpoint_norm] at hd
    omega

def mclGraphComplementMap (y : McLGraphPoints) : McLDecompositionComplement :=
  ⟨mclGraphDecomposition y,mcl_graph_pair_ne_base y⟩

theorem mcl_graph_complement_injective : Function.Injective mclGraphComplementMap := by
  intro y z he
  have hpair : ({y.val,normSixVector co3MarkedCoordinate-y.val} : Finset leech) =
      {z.val,normSixVector co3MarkedCoordinate-z.val} := congrArg (fun p => p.val.val) he
  have hm : y.val ∈ ({z.val,normSixVector co3MarkedCoordinate-z.val} : Finset leech) := by
    rw [← hpair]; exact Finset.mem_insert_self _ _
  rcases Finset.mem_insert.mp hm with h | h
  · exact Subtype.ext h
  · have hd := y.prop.2.2
    rw [Finset.mem_singleton.mp h] at hd
    change integerDot mclEndpoint.val ((normSixVector co3MarkedCoordinate).val-z.val.val) = 16 at hd
    rw [integerDot_sub_right,integerDot_comm mclEndpoint.val,
      mcl_normSix_endpoint_dot,z.prop.2.2] at hd
    omega

theorem mcl_other_pair_endpoint_pairings (p : Points) (hp : p ≠ basePoint)
    (u : leech) (hu : integerDot u.val u.val = 32)
    (hv : integerDot (normSixVector co3MarkedCoordinate-u).val
      (normSixVector co3MarkedCoordinate-u).val = 32)
    (hpair : p.val = {u,normSixVector co3MarkedCoordinate-u}) :
    integerDot mclEndpoint.val u.val = 8 ∨ integerDot mclEndpoint.val u.val = 16 := by
  have hua : u ≠ mclEndpoint := by
    intro h
    apply hp
    apply Subtype.ext
    rw [hpair,h,mcl_base_pair]
    rfl
  have hva : normSixVector co3MarkedCoordinate-u ≠ mclEndpoint := by
    intro h
    have hu' : u = mclOtherEndpoint := by
      unfold mclOtherEndpoint
      rw [← h]; abel
    apply hp
    apply Subtype.ext
    rw [hpair,h,hu',mcl_base_pair,Finset.pair_comm]
  have hupper := leech_minimum_pair_dot_le mclEndpoint u mcl_endpoint_norm hu (Ne.symm hua)
  have hlower := leech_minimum_pair_dot_le mclEndpoint _ mcl_endpoint_norm hv (Ne.symm hva)
  change integerDot mclEndpoint.val ((normSixVector co3MarkedCoordinate).val-u.val) ≤ 16 at hlower
  rw [integerDot_sub_right,integerDot_comm mclEndpoint.val,
    mcl_normSix_endpoint_dot] at hlower
  have hd := leechIntegralPairing_mul mclEndpoint u
  omega

theorem mcl_graph_complement_surjective : Function.Surjective mclGraphComplementMap := by
  intro p
  obtain ⟨u,hu,hv,hpair⟩ := p.val.prop
  have hx := normSix_decomposition_dot co3MarkedCoordinate u hu hv
  rcases mcl_other_pair_endpoint_pairings p.val p.prop u hu hv hpair with h | h
  · let y : McLGraphPoints := ⟨normSixVector co3MarkedCoordinate-u,hv,by
      change integerDot (normSixVector co3MarkedCoordinate).val
        ((normSixVector co3MarkedCoordinate).val-u.val) = 24
      rw [integerDot_sub_right,normSixVector_norm,hx]; norm_num,by
      change integerDot mclEndpoint.val ((normSixVector co3MarkedCoordinate).val-u.val) = 16
      rw [integerDot_sub_right,integerDot_comm mclEndpoint.val,
        mcl_normSix_endpoint_dot,h]; norm_num⟩
    refine ⟨y,Subtype.ext (Subtype.ext ?_)⟩
    change {normSixVector co3MarkedCoordinate-u,
      normSixVector co3MarkedCoordinate-(normSixVector co3MarkedCoordinate-u)} = p.val.val
    rw [sub_sub_cancel,hpair,Finset.pair_comm]
    rfl
  · exact ⟨⟨u,hu,hx,h⟩,Subtype.ext (Subtype.ext hpair.symm)⟩

def mclGraphComplementEquiv : McLGraphPoints ≃ McLDecompositionComplement :=
  Equiv.ofBijective mclGraphComplementMap
    ⟨mcl_graph_complement_injective,mcl_graph_complement_surjective⟩

theorem mcl_graph_card : Nat.card McLGraphPoints = 275 := by
  let := finite_points
  rw [Nat.card_congr mclGraphComplementEquiv,SubMulAction.nat_card_ofStabilizer_eq,degree]

end Atlas.Conway
