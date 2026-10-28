/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/NormSixOctadSigns.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.GolayOctadExteriorRestriction
public import Theory.AtlasPort.OtherSporadic.Conway.MinimumShapeInvariance
/-!
The concrete norm-six Leech shell and its stabilizers.
Coordinate orbit transport and orbit-stabilizer counting identify the full stabilizer.

Source: Gerald Höhn, `Atlas/Conway/NormSixOctadSigns.lean`, ATLAS revision
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

theorem octad_twoFour_sign_transport (T U : Finset Omega) (hT : T ∈ octads)
    (hU : U.card ≤ 2) (hd : Disjoint T U) (s t : TwoFourSigns T U) :
    ∃ c : golay, signChange c.val (twoFourSignedVector T U s) = twoFourSignedVector T U t := by
  let w : BinaryWord := codeZeroExtend T (fun i => t.1.val i + s.1.val i) +
    codeZeroExtend U (fun i => t.2 i + s.2 i)
  have hwt (i : T) : w i = t.1.val i + s.1.val i := by
    have hn : i.val ∉ U := fun h => Finset.disjoint_left.mp hd i.prop h
    simp [w,codeZeroExtend,hn,i.prop]
  have hwu (i : U) : w i = t.2 i + s.2 i := by
    have hn : i.val ∉ T := fun h => Finset.disjoint_left.mp hd h i.prop
    simp [w,codeZeroExtend,hn,i.prop]
  have hw : (∑ i ∈ T, w i) = 0 := by
    rw [← Finset.sum_coe_sort]
    simp_rw [hwt]
    rw [Finset.sum_add_distrib,t.1.prop,s.1.prop]
    exact CharTwo.add_self_eq_zero _
  obtain ⟨c,hc⟩ := golay_octad_exterior_restriction T U hT hU hd w hw
  refine ⟨c,?_⟩
  funext i
  by_cases hiT : i ∈ T
  · have hiU : i ∉ U := fun h => Finset.disjoint_left.mp hd hiT h
    have he := (hc i (Finset.mem_union_left _ hiT)).trans (hwt ⟨i,hiT⟩)
    simp only [twoFourSignedVector,twoFourVector,signChange,LinearMap.coe_mk,AddHom.coe_mk,
      signedSupport,dif_pos hiT,dif_neg hiU,he]
    rcases bit_cases (s.1.val ⟨i,hiT⟩) with hs | hs <;>
      rcases bit_cases (t.1.val ⟨i,hiT⟩) with ht | ht <;> simp [hs,ht]
  by_cases hiU : i ∈ U
  · have he := (hc i (Finset.mem_union_right _ hiU)).trans (hwu ⟨i,hiU⟩)
    simp only [twoFourSignedVector,twoFourVector,signChange,LinearMap.coe_mk,AddHom.coe_mk,
      signedSupport,dif_neg hiT,dif_pos hiU,he]
    rcases bit_cases (s.2 ⟨i,hiU⟩) with hs | hs <;>
      rcases bit_cases (t.2 ⟨i,hiU⟩) with ht | ht <;> simp [hs,ht]
  simp [twoFourSignedVector,twoFourVector,signChange,signedSupport,hiT,hiU]

end Atlas.Conway
