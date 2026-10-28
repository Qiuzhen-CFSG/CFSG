/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/OrthogonalDisjointOrbits.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.MarkedSupportSigns
public import Theory.AtlasPort.OtherSporadic.Conway.MinimalEvenOrbits
public import Theory.AtlasPort.OtherSporadic.Conway.OddPointStabilizerOrbits
public import Theory.AtlasPort.OtherSporadic.Mathieu.OctadExteriorTransitivity
/-!
Orthogonal minimum-vector geometry in the concrete Leech lattice.
The proofs use coordinate shapes, Golay support counts, and stabilizer orbit transport.

Source: Gerald Höhn, `Atlas/Conway/OrthogonalDisjointOrbits.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem support_disjoint_of_zero (T J : Finset Omega) (s : T → Bit) (k : ℤ) (hk : k ≠ 0)
    (x : leech) (hx : x.val = fun i => k * signedSupport T s i)
    (hz : ∀ i ∈ J, x.val i = 0) : Disjoint T J := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have he := hz i hj
  rw [hx] at he
  exact (mul_ne_zero hk (signedSupport_nonzero_on T s i hi)) he

theorem fixed_axes_pair_stabilizer_transport (i j : Omega) (x y : leech)
    (m : GolayMonomialGroup) (hm : (monomialEmbedding m).val x = y)
    (hi : (monomialEmbedding m).val (coordinateEight i) = coordinateEight i)
    (hj : (monomialEmbedding m).val (coordinateEight j) = coordinateEight j) :
    ∃ g : leechVectorStabilizer monomialSubgroup (minimumPairPlus i j), g.val.val.val x = y := by
  have hp := (minimumPair_fixed_iff_axes (monomialEmbedding m) i j).mpr ⟨hi,hj⟩
  exact ⟨⟨⟨monomialEmbedding m,⟨m,rfl⟩⟩,hp.1⟩,hm⟩

theorem orthogonal_disjoint_four_transitive (i j : Omega) (hij : i ≠ j) (x y : leech)
    (hx : x.val ∈ twoFourFamily 0 2) (hy : y.val ∈ twoFourFamily 0 2)
    (hxi : x.val i = 0) (hxj : x.val j = 0) (hyi : y.val i = 0) (hyj : y.val j = 0) :
    ∃ g : leechVectorStabilizer monomialSubgroup (minimumPairPlus i j), g.val.val.val x = y := by
  let J : Finset Omega := {i,j}
  have hJ : J.card = 2 := by simp [J,hij]
  obtain ⟨S,hS,s,hs⟩ := minimum_four_parameterization x hx
  obtain ⟨T,hT,t,ht⟩ := minimum_four_parameterization y hy
  have hSJ : Disjoint S J := support_disjoint_of_zero S J s 4 (by decide) x hs
    (by intro k hk; simp only [J,Finset.mem_insert,Finset.mem_singleton] at hk
        rcases hk with rfl | rfl; exact hxi; exact hxj)
  have hTJ : Disjoint T J := support_disjoint_of_zero T J t 4 (by decide) y ht
    (by intro k hk; simp only [J,Finset.mem_insert,Finset.mem_singleton] at hk
        rcases hk with rfl | rfl; exact hyi; exact hyj)
  obtain ⟨c,hc,hec⟩ := small_support_sign_realization_zero 4 S J hSJ (by omega) s
  obtain ⟨d,hd,hed⟩ := small_support_sign_realization_zero 4 T J hTJ (by omega) t
  obtain ⟨p,hpJ,hp⟩ := mathieu24_fixing_small_set_transitive J S T 2 hSJ.symm hTJ.symm hS hT (by omega)
  obtain ⟨m,hm,hmJ⟩ := monomial_signed_support_transport_fixed_axes p 4 S T J hp hpJ c d hc hd
    x y (hs.trans hec.symm) (ht.trans hed.symm)
  exact fixed_axes_pair_stabilizer_transport i j x y m hm (hmJ i (by simp [J])) (hmJ j (by simp [J]))

theorem orthogonal_disjoint_octad_transitive (i j : Omega) (hij : i ≠ j) (x y : leech)
    (hx : x.val ∈ twoFourFamily 8 0) (hy : y.val ∈ twoFourFamily 8 0)
    (hxi : x.val i = 0) (hxj : x.val j = 0) (hyi : y.val i = 0) (hyj : y.val j = 0) :
    ∃ g : leechVectorStabilizer monomialSubgroup (minimumPairPlus i j), g.val.val.val x = y := by
  let J : Finset Omega := {i,j}
  have hJ : J.card = 2 := by simp [J,hij]
  obtain ⟨S,hS,hCS,s,hps,hs⟩ := minimum_octad_parameterization x hx
  obtain ⟨T,hT,hCT,t,hpt,ht⟩ := minimum_octad_parameterization y hy
  have hSJ : Disjoint S J := support_disjoint_of_zero S J s 2 (by decide) x hs
    (by intro k hk; simp only [J,Finset.mem_insert,Finset.mem_singleton] at hk
        rcases hk with rfl | rfl; exact hxi; exact hxj)
  have hTJ : Disjoint T J := support_disjoint_of_zero T J t 2 (by decide) y ht
    (by intro k hk; simp only [J,Finset.mem_insert,Finset.mem_singleton] at hk
        rcases hk with rfl | rfl; exact hyi; exact hyj)
  have hOS := codeSupport_octad S hS hCS
  have hOT := codeSupport_octad T hT hCT
  obtain ⟨c,hc,hec⟩ := octad_support_sign_realization_zero S J hOS hSJ (by omega) s hps
  obtain ⟨d,hd,hed⟩ := octad_support_sign_realization_zero T J hOT hTJ (by omega) t hpt
  have hnotS (k : Omega) (hk : k ∈ J) : k ∉ S := fun h => Finset.disjoint_left.mp hSJ h hk
  have hnotT (k : Omega) (hk : k ∈ J) : k ∉ T := fun h => Finset.disjoint_left.mp hTJ h hk
  obtain ⟨p,hpi,hpj,hp⟩ := mathieu24_pair_fixing_octad_avoiding_transitive S T hOS hOT i j hij
    (hnotS i (by simp [J])) (hnotS j (by simp [J])) (hnotT i (by simp [J])) (hnotT j (by simp [J]))
  have hpJ : ∀ k ∈ J, p.val k = k := by
    intro k hk
    simp only [J,Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl | rfl; exact hpi; exact hpj
  obtain ⟨m,hm,hmJ⟩ := monomial_signed_support_transport_fixed_axes p 2 S T J hp hpJ c d hc hd
    x y (hs.trans hec.symm) (ht.trans hed.symm)
  exact fixed_axes_pair_stabilizer_transport i j x y m hm (hmJ i (by simp [J])) (hmJ j (by simp [J]))

end Atlas.Conway
