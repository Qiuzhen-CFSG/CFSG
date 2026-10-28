/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.GolayOctadTransitivity
public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetColumnPairTransport

/-!
# Transport of mixed octad flags

Golay automorphisms transport an octad together with one interior and
one exterior point. Normalize the octad to two tetrads, match their columns
and the exterior column, and apply sextet two-point transport.

Source: `Atlas/Mathieu/OctadMixedFlagTransport.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem octad_mixed_flag_normalize (O : Finset Omega) (hO : O ∈ octads)
    (a b : Omega) (ha : a ∈ O) (hb : b ∉ O) :
    ∃ g : Mathieu24CodeModel, ∃ i j : HexIndex,
      i ≠ j ∧ permuteBlock g.val O = tetrad i ∪ tetrad j ∧
      (g.val a).1 = i ∧ (g.val b).1 ≠ i ∧ (g.val b).1 ≠ j := by
  obtain ⟨g,hg⟩ := mathieu24_octad_transitive O (distinguishedTrio 0) hO (distinguishedTrio_octads 0)
  have hga : (g.val a).1 = (0,0) ∨ (g.val a).1 = (0,1) := by
    have hm : g.val a ∈ distinguishedTrio 0 := by
      rw [← hg]; exact Finset.mem_image.mpr ⟨a,ha,rfl⟩
    simpa [distinguishedTrio] using hm
  have hgb : (g.val b).1 ≠ (0,0) ∧ (g.val b).1 ≠ (0,1) := by
    have hm : g.val b ∉ distinguishedTrio 0 := by
      rw [← hg]; intro hm
      obtain ⟨c,hc,he⟩ := Finset.mem_image.mp hm
      exact hb (g.val.injective he ▸ hc)
    simpa [distinguishedTrio] using hm
  rcases hga with ha | ha
  · exact ⟨g,(0,0),(0,1),by decide,hg,ha,hgb⟩
  · refine ⟨g,(0,1),(0,0),by decide,?_,ha,hgb.2,hgb.1⟩
    rw [hg,distinguishedTrio,Finset.union_comm]

theorem sextet_mixed_flag_transport (i j k l : HexIndex) (a b c d : Omega)
    (hij : i ≠ j) (hkl : k ≠ l) (hai : a.1 = i) (hck : c.1 = k)
    (hbi : b.1 ≠ i) (hbj : b.1 ≠ j) (hdk : d.1 ≠ k) (hdl : d.1 ≠ l) :
    ∃ s : SextetStabilizer,
      permuteBlock s.val.val (tetrad i ∪ tetrad j) = tetrad k ∪ tetrad l ∧
      s.val.val a = c ∧ s.val.val b = d := by
  have he : Function.Injective (![i,j,b.1] : Fin 3 → HexIndex) := by
    intro x y h; fin_cases x <;> fin_cases y <;> simp_all
  have hf : Function.Injective (![k,l,d.1] : Fin 3 → HexIndex) := by
    intro x y h; fin_cases x <;> fin_cases y <;> simp_all
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair _ _ he hf
  have hi : σ i = k := hσ 0
  have hj : σ j = l := hσ 1
  have hb : σ b.1 = d.1 := hσ 2
  obtain ⟨s,hs,hsa,hsb⟩ := sextet_two_point_transport σ a b c d
    (by rw [hck]; exact hdk.symm) (by rw [hai,hck,hi]) hb
  refine ⟨s,?_,hsa,hsb⟩
  change (tetrad i ∪ tetrad j).image s.val.val = _
  rw [Finset.image_union]
  exact congrArg₂ (· ∪ ·) ((sextet_tetrad_transport s σ hs i).trans (congrArg tetrad hi))
    ((sextet_tetrad_transport s σ hs j).trans (congrArg tetrad hj))

theorem mathieu24_octad_mixed_flag_transitive (O P : Finset Omega)
    (hO : O ∈ octads) (hP : P ∈ octads) (a b c d : Omega)
    (ha : a ∈ O) (hb : b ∉ O) (hc : c ∈ P) (hd : d ∉ P) :
    ∃ g : Mathieu24CodeModel, permuteBlock g.val O = P ∧ g.val a = c ∧ g.val b = d := by
  obtain ⟨g,i,j,hij,hg,hai,hbi,hbj⟩ := octad_mixed_flag_normalize O hO a b ha hb
  obtain ⟨h,k,l,hkl,hh,hck,hdk,hdl⟩ := octad_mixed_flag_normalize P hP c d hc hd
  obtain ⟨s,hs,hsa,hsb⟩ := sextet_mixed_flag_transport i j k l
    (g.val a) (g.val b) (h.val c) (h.val d) hij hkl hai hck hbi hbj hdk hdl
  refine ⟨h⁻¹*s.val*g,?_,?_,?_⟩
  · change permuteBlock (h.val⁻¹*s.val.val*g.val) O = P
    rw [permuteBlock_mul,permuteBlock_mul,hg,hs,← hh,← permuteBlock_mul,
      inv_mul_cancel,permuteBlock_one]
  · change h.val.symm (s.val.val (g.val a)) = c
    rw [hsa,Equiv.symm_apply_apply]
  · change h.val.symm (s.val.val (g.val b)) = d
    rw [hsb,Equiv.symm_apply_apply]

end Atlas.Codes
