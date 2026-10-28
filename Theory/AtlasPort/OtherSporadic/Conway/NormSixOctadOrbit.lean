/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/NormSixOctadOrbit.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.NormSixOctadSigns
public import Theory.AtlasPort.OtherSporadic.Mathieu.OctadExteriorTransitivity
/-!
The concrete norm-six Leech shell and its stabilizers.
Coordinate orbit transport and orbit-stabilizer counting identify the full stabilizer.

Source: Gerald Höhn, `Atlas/Conway/NormSixOctadOrbit.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem octad_second_exterior (T : Finset Omega) (hT : T ∈ octads) (a : Omega) :
    ∃ b : Omega, b ∉ T ∧ b ≠ a := by
  by_contra h
  push Not at h
  have he : insert a T = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro b
    by_cases hb : b ∈ T
    · exact Finset.mem_insert_of_mem hb
    · exact Finset.mem_insert.mpr (Or.inl (h b hb))
  have hc := Finset.card_insert_le a T
  rw [he,octad_size T hT] at hc
  norm_num [Omega,HexIndex] at hc

theorem mathieu24_octad_exterior_transitive (T U : Finset Omega)
    (hT : T ∈ octads) (hU : U ∈ octads) (a b : Omega) (ha : a ∉ T) (hb : b ∉ U) :
    ∃ g : Mathieu24CodeModel, permuteBlock g.val T = U ∧ g.val a = b := by
  obtain ⟨a',ha',ha'a⟩ := octad_second_exterior T hT a
  obtain ⟨b',hb',hb'b⟩ := octad_second_exterior U hU b
  obtain ⟨g,hg,hga,_⟩ := mathieu24_octad_exterior_pair_transitive T U hT hU a a' b b'
    ha ha' ha'a.symm hb hb' hb'b.symm
  exact ⟨g,hg,hga⟩

theorem octad_oneFour_same_support (x y : leech)
    (hx : x.val ∈ twoFourFamily 8 1) (hy : y.val ∈ twoFourFamily 8 1)
    (h2 : evenMagnitudeSupport x.val 2 = evenMagnitudeSupport y.val 2)
    (h4 : evenMagnitudeSupport x.val 4 = evenMagnitudeSupport y.val 4) :
    ∃ c : golay, (signIsometry c).val x = y := by
  obtain ⟨⟨⟨T,hT⟩,⟨U,hU⟩,s⟩,_,hx⟩ := Finset.mem_image.mp hx
  obtain ⟨⟨⟨T',hT'⟩,⟨U',hU'⟩,t⟩,_,hy⟩ := Finset.mem_image.mp hy
  change twoFourSignedVector T U s = x.val at hx
  change twoFourSignedVector T' U' t = y.val at hy
  rw [← hx,← hy,twoFourSignedVector,twoFourSignedVector,
    twoFour_support_two _ _ hU.1,twoFour_support_two _ _ hU'.1] at h2
  rw [← hx,← hy,twoFourSignedVector,twoFourSignedVector,
    twoFour_support_four _ _ hU.1,twoFour_support_four _ _ hU'.1] at h4
  change T = T' at h2
  subst T'
  subst U'
  obtain ⟨c,hc⟩ := octad_twoFour_sign_transport T U
    (codeSupport_octad T hT.2 hT.1) (by omega) hU.1 s t
  refine ⟨c,Subtype.ext ?_⟩
  change signChange c.val x.val = y.val
  rw [← hx,← hy]
  exact hc

theorem monomial_octad_oneFour_six_transitive (x y : leech)
    (hx : x.val ∈ twoFourFamily 8 1) (hy : y.val ∈ twoFourFamily 8 1) :
    ∃ m : GolayMonomialGroup, (monomialEmbedding m).val x = y := by
  have hpx := twoFourFamily_shape 8 1 x.val hx
  have hpy := twoFourFamily_shape 8 1 y.val hy
  let T := evenMagnitudeSupport x.val 2
  let U := evenMagnitudeSupport y.val 2
  have hTx : supportWord T ∈ golay := by
    obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hx
    have ht : T = p.1.val := by
      change evenMagnitudeSupport x.val 2 = _
      rw [← hp]
      exact twoFour_support_two _ _ p.2.1.prop.1 _ _
    rw [ht]
    exact p.1.prop.1
  have hUy : supportWord U ∈ golay := by
    obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hy
    have ht : U = p.1.val := by
      change evenMagnitudeSupport y.val 2 = _
      rw [← hp]
      exact twoFour_support_two _ _ p.2.1.prop.1 _ _
    rw [ht]
    exact p.1.prop.1
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hpx.2.2
  obtain ⟨b,hb⟩ := Finset.card_eq_one.mp hpy.2.2
  have haT : a ∉ T := by
    intro h
    have h2 := (Finset.mem_filter.mp h).2
    have h4 := (Finset.mem_filter.mp (ha ▸ Finset.mem_singleton_self a)).2
    omega
  have hbU : b ∉ U := by
    intro h
    have h2 := (Finset.mem_filter.mp h).2
    have h4 := (Finset.mem_filter.mp (hb ▸ Finset.mem_singleton_self b)).2
    omega
  obtain ⟨g,hg,hga⟩ := mathieu24_octad_exterior_transitive T U
    (codeSupport_octad T hpx.2.1 hTx) (codeSupport_octad U hpy.2.1 hUy) a b haT hbU
  let z := (permutationEmbedding g).val x
  have hz : z.val ∈ twoFourFamily 8 1 :=
    monomial_twoFour_invariant (SemidirectProduct.inr g) x 8 1 hx
  have hz2 : evenMagnitudeSupport z.val 2 = evenMagnitudeSupport y.val 2 :=
    (monomial_magnitude_support (SemidirectProduct.inr g) x 2).trans hg
  have hz4 : evenMagnitudeSupport z.val 4 = evenMagnitudeSupport y.val 4 := by
    have hh := monomial_magnitude_support (SemidirectProduct.inr g) x 4
    change evenMagnitudeSupport z.val 4 = _ at hh
    rw [hh,ha,hb]
    simp [permuteBlock,hga]
  obtain ⟨c,hc⟩ := octad_oneFour_same_support z y hz hy hz2 hz4
  exact ⟨⟨Multiplicative.ofAdd c,g⟩,hc⟩

end Atlas.Conway
