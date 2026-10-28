/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/MinimalEvenOrbits.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.MonomialSupportTransport
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechShortShellCounts
/-!
Minimum-vector and monomial stabilizer geometry for the concrete Leech isometry group.
The proofs identify coordinate stabilizers and combine orbit geometry with exact counting.

Source: Gerald Höhn, `Atlas/Conway/MinimalEvenOrbits.lean`, ATLAS revision
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

theorem mathieu24_small_set_transitive {k : ℕ} (hk : k ≤ 5)
    (S T : Finset Omega) (hS : S.card = k) (hT : T.card = k) :
    ∃ g : Mathieu24CodeModel, permuteBlock g.val S = T := by
  let := mathieu24_five_transitive
  have ht : MulAction.IsMultiplyPretransitive Mathieu24CodeModel Omega k :=
    MulAction.isMultiplyPretransitive_of_le hk (by norm_num [Omega,HexIndex])
  obtain ⟨g,hg⟩ := (MulAction.isMultiplyPretransitive_iff.mp ht)
    (finiteSetEmbedding S hS) (finiteSetEmbedding T hT)
  refine ⟨g,?_⟩
  rw [← finiteSetEmbedding_image S hS,← finiteSetEmbedding_image T hT]
  change (Finset.univ.image (finiteSetEmbedding S hS)).image g.val = _
  rw [Finset.image_image]
  apply Finset.image_congr
  intro i _
  exact congrArg (fun e : Fin k ↪ Omega => e i) hg

theorem minimum_four_parameterization (x : leech) (hx : x.val ∈ twoFourFamily 0 2) :
    ∃ T : Finset Omega, T.card = 2 ∧ ∃ s : T → Bit,
      x.val = fun i => 4 * signedSupport T s i := by
  obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hx
  have hz := Finset.card_eq_zero.mp p.1.prop.2
  refine ⟨p.2.1.val,p.2.1.prop.2,p.2.2.2,?_⟩
  funext i
  have he := congrFun hp i
  change 2 * signedSupport p.1.val p.2.2.1.val i + 4 * signedSupport p.2.1.val p.2.2.2 i = x.val i at he
  have hzero : signedSupport p.1.val p.2.2.1.val i = 0 := by
    have hi : i ∉ p.1.val := by rw [hz]; simp
    simp [signedSupport,hi]
  simpa [hzero] using he.symm

theorem minimum_octad_parameterization (x : leech) (hx : x.val ∈ twoFourFamily 8 0) :
    ∃ T : Finset Omega, T.card = 8 ∧ supportWord T ∈ golay ∧
      ∃ s : T → Bit, (∑ i, s i) = 0 ∧ x.val = fun i => 2 * signedSupport T s i := by
  obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hx
  have hz := Finset.card_eq_zero.mp p.2.1.prop.2
  refine ⟨p.1.val,p.1.prop.2,p.1.prop.1,p.2.2.1.val,?_,?_⟩
  · simpa [p.2.1.prop.2] using p.2.2.1.prop
  · funext i
    have he := congrFun hp i
    change 2 * signedSupport p.1.val p.2.2.1.val i + 4 * signedSupport p.2.1.val p.2.2.2 i = x.val i at he
    have hzero : signedSupport p.2.1.val p.2.2.2 i = 0 := by
      have hi : i ∉ p.2.1.val := by rw [hz]; simp
      simp [signedSupport,hi]
    simpa [hzero] using he.symm

theorem monomial_four_minimum_transitive (x y : leech)
    (hx : x.val ∈ twoFourFamily 0 2) (hy : y.val ∈ twoFourFamily 0 2) :
    ∃ m : GolayMonomialGroup, (monomialEmbedding m).val x = y := by
  obtain ⟨S,hS,s,hs⟩ := minimum_four_parameterization x hx
  obtain ⟨T,hT,t,ht⟩ := minimum_four_parameterization y hy
  obtain ⟨c,hc⟩ := small_support_sign_realization 4 S (by omega) s
  obtain ⟨d,hd⟩ := small_support_sign_realization 4 T (by omega) t
  obtain ⟨g,hg⟩ := mathieu24_small_set_transitive (by decide : 2 ≤ 5) S T hS hT
  exact monomial_signed_support_transport g 4 S T hg c d x y (hs.trans hc.symm) (ht.trans hd.symm)

theorem codeSupport_octad (T : Finset Omega) (hT : T.card = 8) (hC : supportWord T ∈ golay) :
    T ∈ octads := by
  apply (octads_mem T).mpr
  refine ⟨⟨supportWord T,hC⟩,?_,binarySupportEquiv.right_inv T⟩
  simpa [hammingNorm,supportWord] using hT

theorem monomial_octad_minimum_transitive (x y : leech)
    (hx : x.val ∈ twoFourFamily 8 0) (hy : y.val ∈ twoFourFamily 8 0) :
    ∃ m : GolayMonomialGroup, (monomialEmbedding m).val x = y := by
  obtain ⟨S,hS,hCS,s,hps,hs⟩ := minimum_octad_parameterization x hx
  obtain ⟨T,hT,hCT,t,hpt,ht⟩ := minimum_octad_parameterization y hy
  obtain ⟨c,hc⟩ := octad_support_sign_realization S hS hCS s hps
  obtain ⟨d,hd⟩ := octad_support_sign_realization T hT hCT t hpt
  obtain ⟨g,hg⟩ := mathieu24_octad_transitive S T (codeSupport_octad S hS hCS) (codeSupport_octad T hT hCT)
  exact monomial_signed_support_transport g 2 S T hg c d x y (hs.trans hc.symm) (ht.trans hd.symm)

end Atlas.Conway
