/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.OctadInsidePairNormalize
public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetThreePointTransport
public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetColumnPairTransport

/-!
# Transport of an octad with two inside points and one outside

Golay automorphisms transport an octad, two distinct points inside it,
and a point outside it. Normalize the inside points to distinct tetrad columns,
extend the matching of three columns, and use sextet three-point transport.

Source: `Atlas/Mathieu/OctadInsidePairTransport.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem mathieu24_octad_inside_pair_outside_transitive (O P : Finset Omega)
    (hO : O ∈ octads) (hP : P ∈ octads) (a b c d e f : Omega)
    (ha : a ∈ O) (hb : b ∈ O) (hab : a ≠ b) (hc : c ∉ O)
    (hd : d ∈ P) (he : e ∈ P) (hde : d ≠ e) (hf : f ∉ P) :
    ∃ g : Mathieu24CodeModel, permuteBlock g.val O = P ∧
      g.val a = d ∧ g.val b = e ∧ g.val c = f := by
  obtain ⟨g,i,j,hij,hg,hga,hgb,hgci,hgcj⟩ := octad_inside_pair_normalize O hO a b c ha hb hab hc
  obtain ⟨h,k,l,hkl,hh,hhd,hhe,hhfk,hhfl⟩ := octad_inside_pair_normalize P hP d e f hd he hde hf
  have hi : Function.Injective (![i,j,(g.val c).1] : Fin 3 → HexIndex) := by
    intro x y hxy; fin_cases x <;> fin_cases y <;> simp_all
  have hj : Function.Injective (![k,l,(h.val f).1] : Fin 3 → HexIndex) := by
    intro x y hxy; fin_cases x <;> fin_cases y <;> simp_all
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair _ _ hi hj
  have hσi : σ i = k := hσ 0
  have hσj : σ j = l := hσ 1
  have hσc : σ (g.val c).1 = (h.val f).1 := hσ 2
  have hinj : Function.Injective (fun r : Fin 3 => ((![h.val d,h.val e,h.val f]) r).1) := by
    convert hj using 1
    funext r
    fin_cases r <;> simp [hhd,hhe]
  have hcols (r : Fin 3) : σ ((![g.val a,g.val b,g.val c]) r).1 =
      ((![h.val d,h.val e,h.val f]) r).1 := by
    fin_cases r <;> simp [hga,hgb,hhd,hhe,hσi,hσj,hσc]
  obtain ⟨s,hs,hpts⟩ := sextet_three_point_transport σ
    ![g.val a,g.val b,g.val c] ![h.val d,h.val e,h.val f] hinj hcols
  have hsa : s.val.val (g.val a) = h.val d := hpts 0
  have hsb : s.val.val (g.val b) = h.val e := hpts 1
  have hsc : s.val.val (g.val c) = h.val f := hpts 2
  have hsO : permuteBlock s.val.val (tetrad i ∪ tetrad j) = tetrad k ∪ tetrad l := by
    change (tetrad i ∪ tetrad j).image s.val.val = _
    rw [Finset.image_union]
    exact congrArg₂ (· ∪ ·)
      ((sextet_tetrad_transport s σ hs i).trans (congrArg tetrad hσi))
      ((sextet_tetrad_transport s σ hs j).trans (congrArg tetrad hσj))
  refine ⟨h⁻¹*s.val*g,?_,?_,?_,?_⟩
  · change permuteBlock (h.val⁻¹*s.val.val*g.val) O = P
    rw [permuteBlock_mul,permuteBlock_mul,hg,hsO,← hh,← permuteBlock_mul,inv_mul_cancel,permuteBlock_one]
  · change h.val.symm (s.val.val (g.val a)) = d
    rw [hsa,Equiv.symm_apply_apply]
  · change h.val.symm (s.val.val (g.val b)) = e
    rw [hsb,Equiv.symm_apply_apply]
  · change h.val.symm (s.val.val (g.val c)) = f
    rw [hsc,Equiv.symm_apply_apply]

end Atlas.Codes
