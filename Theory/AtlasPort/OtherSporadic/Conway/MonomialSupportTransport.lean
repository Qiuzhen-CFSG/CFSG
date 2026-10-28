/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/MonomialSupportTransport.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.GolayOctadRestriction
public import Theory.AtlasPort.OtherSporadic.Conway.MonomialOrder
public import Theory.AtlasPort.OtherSporadic.Mathieu.GolayOctadTransitivity
/-!
Golay coordinate restrictions and signed-support transport in the Leech lattice.
The proofs retain the explicit code maps and coordinate identities used by the stabilizer geometry.

Source: Gerald Höhn, `Atlas/Conway/MonomialSupportTransport.lean`, ATLAS revision
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

def constantSupportVector (k : ℤ) (T : Finset Omega) : IntegerCoordinates :=
  fun i => if i ∈ T then k else 0

theorem permutation_constantSupport (g : Mathieu24CodeModel) (k : ℤ) (T : Finset Omega) :
    integerPermutation g.val (constantSupportVector k T) =
      constantSupportVector k (permuteBlock g.val T) := by
  funext i
  have hm : g.val.symm i ∈ T ↔ i ∈ permuteBlock g.val T := by
    constructor
    · intro h; exact Finset.mem_image.mpr ⟨g.val.symm i,h,g.val.apply_symm_apply i⟩
    · rintro h; obtain ⟨j,hj,he⟩ := Finset.mem_image.mp h
      simpa [← he] using hj
  change (if g.val.symm i ∈ T then k else 0) = (if i ∈ permuteBlock g.val T then k else 0)
  simp only [hm]

theorem sign_constantSupport (k : ℤ) (T : Finset Omega) (s : T → Bit) (c : golay)
    (hc : ∀ i : T, c.val i = s i) :
    signChange c.val (constantSupportVector k T) = fun i => k * signedSupport T s i := by
  funext i
  by_cases hi : i ∈ T
  · have he := hc ⟨i,hi⟩
    simp only [signChange,LinearMap.coe_mk,AddHom.coe_mk,constantSupportVector,
      signedSupport,if_pos hi,dif_pos hi,he]
    split_ifs <;> ring
  · simp [signChange,constantSupportVector,signedSupport,hi]

theorem monomial_signed_support_transport (g : Mathieu24CodeModel) (k : ℤ)
    (S T : Finset Omega) (hg : permuteBlock g.val S = T)
    (c d : golay) (x y : leech)
    (hx : x.val = signChange c.val (constantSupportVector k S))
    (hy : y.val = signChange d.val (constantSupportVector k T)) :
    ∃ m : GolayMonomialGroup, (monomialEmbedding m).val x = y := by
  refine ⟨⟨Multiplicative.ofAdd (d + golayPermutationEquiv g c),g⟩,?_⟩
  apply Subtype.ext
  change signChange (d.val + coordinatePermutation g.val c.val) (integerPermutation g.val x.val) = y.val
  rw [hx,hy,permutation_sign_conjugation,signChange_add,signChange_involutive,
    permutation_constantSupport,hg]

theorem small_support_sign_realization (k : ℤ) (T : Finset Omega) (hT : T.card < 8)
    (s : T → Bit) : ∃ c : golay,
      signChange c.val (constantSupportVector k T) = fun i => k * signedSupport T s i := by
  obtain ⟨c,hc⟩ := golay_small_restriction_surjective T hT s
  exact ⟨c,sign_constantSupport k T s c (fun i => congrFun hc i)⟩

theorem octad_support_sign_realization (T : Finset Omega) (hT : T.card = 8)
    (hC : supportWord T ∈ golay) (s : T → Bit) (hs : ∑ i, s i = 0) :
    ∃ c : golay, signChange c.val (constantSupportVector 2 T) =
      fun i => 2 * signedSupport T s i := by
  have hw : (∑ i ∈ T, codeZeroExtend T s i) = 0 := by
    rw [← Finset.sum_coe_sort]
    simpa only [codeZeroExtend_apply] using hs
  obtain ⟨c,hc⟩ := golay_octad_restriction T hT hC (codeZeroExtend T s) hw
  refine ⟨c,sign_constantSupport 2 T s c ?_⟩
  intro i
  exact (hc i i.prop).trans (codeZeroExtend_apply T s i)

end Atlas.Conway
