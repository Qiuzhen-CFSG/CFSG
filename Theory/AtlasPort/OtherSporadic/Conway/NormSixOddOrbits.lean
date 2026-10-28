/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/NormSixOddOrbits.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.NormSixVector
public import Theory.AtlasPort.OtherSporadic.Conway.MinimalEvenOrbits
/-!
The concrete norm-six Leech shell and its stabilizers.
Coordinate orbit transport and orbit-stabilizer counting identify the full stabilizer.

Source: Gerald Höhn, `Atlas/Conway/NormSixOddOrbits.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem permutation_odd_profile (g : Mathieu24CodeModel) (T F : Finset Omega) :
    integerPermutation g.val (oddProfileBase T F) =
      oddProfileBase (permuteBlock g.val T) (permuteBlock g.val F) := by
  have hm (S : Finset Omega) (i : Omega) : g.val.symm i ∈ S ↔ i ∈ permuteBlock g.val S := by
    constructor
    · intro h; exact Finset.mem_image.mpr ⟨_,h,g.val.apply_symm_apply i⟩
    · intro h
      obtain ⟨j,hj,he⟩ := Finset.mem_image.mp h
      simpa [← he] using hj
  funext i
  change oddProfileBase T F (g.val.symm i) = _
  simp only [oddProfileBase,hm]

theorem monomial_odd_profile_transport (g : Mathieu24CodeModel) (T F : Finset Omega)
    (c d : golay) (x y : leech)
    (hx : x.val = signedOddProfile T F c)
    (hy : y.val = signedOddProfile (permuteBlock g.val T) (permuteBlock g.val F) d) :
    ∃ m : GolayMonomialGroup, (monomialEmbedding m).val x = y := by
  refine ⟨⟨Multiplicative.ofAdd (d + golayPermutationEquiv g c),g⟩,?_⟩
  apply Subtype.ext
  change signChange (d.val + coordinatePermutation g.val c.val) (integerPermutation g.val x.val) = y.val
  rw [hx,hy]
  change signChange (d.val + coordinatePermutation g.val c.val)
    (integerPermutation g.val (signChange c.val (oddProfileBase T F))) = _
  rw [permutation_sign_conjugation,signChange_add,signChange_involutive,permutation_odd_profile]
  rfl

theorem monomial_odd_three_transitive (x y : leech)
    (hx : x.val ∈ oddNoFiveVectors 3) (hy : y.val ∈ oddNoFiveVectors 3) :
    ∃ m : GolayMonomialGroup, (monomialEmbedding m).val x = y := by
  obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hx
  obtain ⟨q,_,hq⟩ := Finset.mem_image.mp hy
  obtain ⟨g,hg⟩ := mathieu24_small_set_transitive (by decide : 3 ≤ 5)
    p.1.val q.1.val p.1.prop q.1.prop
  apply monomial_odd_profile_transport g p.1.val ∅ p.2 q.2 x y hp.symm
  rw [hg]
  simpa [noFiveVector,permuteBlock] using hq.symm

theorem odd_one_five_parameterization (x : leech) (hx : x.val ∈ oddOneFiveVectors 0) :
    ∃ a c, x.val = signedOddProfile ∅ {a} c := by
  obtain ⟨a,_,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hx
  have hz := Finset.card_eq_zero.mp p.1.prop
  refine ⟨a,p.2,?_⟩
  simpa [oneFiveVector,oneFiveSupport,hz] using hp.symm

theorem monomial_odd_five_transitive (x y : leech)
    (hx : x.val ∈ oddOneFiveVectors 0) (hy : y.val ∈ oddOneFiveVectors 0) :
    ∃ m : GolayMonomialGroup, (monomialEmbedding m).val x = y := by
  obtain ⟨a,c,hc⟩ := odd_one_five_parameterization x hx
  obtain ⟨b,d,hd⟩ := odd_one_five_parameterization y hy
  obtain ⟨g,hg⟩ := golay_coordinate_transitive a b
  apply monomial_odd_profile_transport g ∅ {a} c d x y hc
  simpa [permuteBlock,hg] using hd

end Atlas.Conway
