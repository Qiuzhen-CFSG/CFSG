/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/MarkedSupportSigns.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.GolayOctadExteriorRestriction
public import Theory.AtlasPort.OtherSporadic.Conway.MonomialSupportTransport
public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalPairGeometry
/-!
Golay coordinate restrictions and signed-support transport in the Leech lattice.
The proofs retain the explicit code maps and coordinate identities used by the stabilizer geometry.

Source: Gerald Höhn, `Atlas/Conway/MarkedSupportSigns.lean`, ATLAS revision
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

theorem small_support_sign_realization_zero (k : ℤ) (T J : Finset Omega)
    (hTJ : Disjoint T J) (hcard : T.card + J.card < 8) (s : T → Bit) :
    ∃ c : golay, (∀ i ∈ J, c.val i = 0) ∧
      signChange c.val (constantSupportVector k T) = fun i => k * signedSupport T s i := by
  obtain ⟨c,hc⟩ := golay_small_restriction_surjective (T ∪ J)
    (lt_of_le_of_lt (Finset.card_union_le T J) hcard) (fun i => codeZeroExtend T s i)
  have he (i : Omega) (hi : i ∈ T ∪ J) : c.val i = codeZeroExtend T s i := congrFun hc ⟨i,hi⟩
  refine ⟨c,?_,sign_constantSupport k T s c ?_⟩
  · intro i hi
    rw [he i (Finset.mem_union_right _ hi)]
    have hn : i ∉ T := fun h => Finset.disjoint_left.mp hTJ h hi
    simp [codeZeroExtend,hn]
  · intro i
    exact (he i (Finset.mem_union_left _ i.prop)).trans (codeZeroExtend_apply T s i)

theorem octad_support_sign_realization_zero (T J : Finset Omega)
    (hT : T ∈ octads) (hTJ : Disjoint T J) (hJ : J.card ≤ 2)
    (s : T → Bit) (hs : ∑ i, s i = 0) :
    ∃ c : golay, (∀ i ∈ J, c.val i = 0) ∧
      signChange c.val (constantSupportVector 2 T) = fun i => 2 * signedSupport T s i := by
  have hw : (∑ i ∈ T, codeZeroExtend T s i) = 0 := by
    rw [← Finset.sum_coe_sort]
    simpa only [codeZeroExtend_apply] using hs
  obtain ⟨c,hc⟩ := golay_octad_exterior_restriction T J hT hJ hTJ (codeZeroExtend T s) hw
  refine ⟨c,?_,sign_constantSupport 2 T s c ?_⟩
  · intro i hi
    rw [hc i (Finset.mem_union_right _ hi)]
    have hn : i ∉ T := fun h => Finset.disjoint_left.mp hTJ h hi
    simp [codeZeroExtend,hn]
  · intro i
    exact (hc i (Finset.mem_union_left _ i.prop)).trans (codeZeroExtend_apply T s i)

theorem monomial_signed_support_transport_fixed_axes (g : Mathieu24CodeModel) (k : ℤ)
    (S T J : Finset Omega) (hg : permuteBlock g.val S = T)
    (hJ : ∀ i ∈ J, g.val i = i) (c d : golay)
    (hc : ∀ i ∈ J, c.val i = 0) (hd : ∀ i ∈ J, d.val i = 0) (x y : leech)
    (hx : x.val = signChange c.val (constantSupportVector k S))
    (hy : y.val = signChange d.val (constantSupportVector k T)) :
    ∃ m : GolayMonomialGroup, (monomialEmbedding m).val x = y ∧
      ∀ i ∈ J, (monomialEmbedding m).val (coordinateEight i) = coordinateEight i := by
  let m : GolayMonomialGroup := ⟨Multiplicative.ofAdd (d + golayPermutationEquiv g c),g⟩
  refine ⟨m,?_,?_⟩
  · apply Subtype.ext
    change signChange (d.val + coordinatePermutation g.val c.val) (integerPermutation g.val x.val) = y.val
    rw [hx,hy,permutation_sign_conjugation,signChange_add,signChange_involutive,
      permutation_constantSupport,hg]
  · intro i hi
    rw [monomial_axis_fixed_iff]
    refine ⟨hJ i hi,?_⟩
    have hinv : g.val.symm i = i := by rw [Equiv.symm_apply_eq]; exact (hJ i hi).symm
    change d.val i + c.val (g.val.symm i) = 0
    rw [hinv,hc i hi,hd i hi,add_zero]

theorem signedSupport_nonzero_on (T : Finset Omega) (s : T → Bit) (i : Omega)
    (hi : i ∈ T) : signedSupport T s i ≠ 0 := by
  simp only [signedSupport,dif_pos hi]
  split_ifs <;> norm_num

end Atlas.Conway
