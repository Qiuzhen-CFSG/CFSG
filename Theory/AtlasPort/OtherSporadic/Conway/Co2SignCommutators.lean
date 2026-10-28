/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co2SignCommutators.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.ShortenedGolayDifferences
public import Theory.AtlasPort.OtherSporadic.Sporadic.Conway2Geometry

/-!
Shortened Golay signs as commutators in the norm-four vector stabilizer.
Octad differences and the shortened-code span prove perfectness inputs and a noncommuting witness.

Source: Gerald Höhn, `Atlas/Conway/Co2SignCommutators.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to Lean 4.33.0 with public imports and exposed concrete definitions
for the source cross-module reductions; the mathematical namespaces are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open scoped commutatorElement
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 10000

abbrev Co2MarkedModel := Atlas.Sporadic.Conway2.Model

def co2ShortSignElement (c : golay) (hi : c.val ((0,0),0) = 0) (hj : c.val ((0,0),1) = 0) :
    Co2MarkedModel := ⟨signEmbedding (Multiplicative.ofAdd c),by
  apply Subtype.ext
  change signChange c.val (minimumPairPlus ((0,0),0) ((0,0),1)).val = (minimumPairPlus ((0,0),0) ((0,0),1)).val
  funext k
  simp only [signChange,minimumPairPlus,coordinateVector,Pi.add_apply,Pi.single_apply]
  by_cases h0 : k = ((0,0),0)
  · subst k; simp [hi]
  by_cases h1 : k = ((0,0),1)
  · subst k; simp [hj]
  simp [h0,h1]⟩

def co2MarkedPermutation (g : Mathieu24CodeModel)
    (hi : g.val ((0,0),0) = ((0,0),0)) (hj : g.val ((0,0),1) = ((0,0),1)) :
    Co2MarkedModel := ⟨permutationEmbedding g,by
  have h := monomial_fixes_pair_plus (SemidirectProduct.inr g) ((0,0),0) ((0,0),1)
    (by decide) (Or.inl ⟨hi,hj⟩) rfl rfl
  have he := congrArg (fun f : Mathieu24CodeModel →* LeechIsometryGroup => f g) monomial_inr
  change (monomialEmbedding (SemidirectProduct.inr g)).val _ = _ at h
  rwa [show monomialEmbedding (SemidirectProduct.inr g) = permutationEmbedding g from he] at h⟩

def co2DerivedImage : Subgroup LeechIsometryGroup :=
  (commutator Co2MarkedModel).map (fullVectorStabilizer Atlas.Sporadic.Conway2.vector.val).subtype

def co2DerivedCode : Submodule Bit golay where
  carrier := {c | signEmbedding (Multiplicative.ofAdd c) ∈ co2DerivedImage}
  zero_mem' := by change signEmbedding 1 ∈ co2DerivedImage; rw [map_one]; exact Subgroup.one_mem _
  add_mem' {c d} hc hd := by
    change signEmbedding (Multiplicative.ofAdd c * Multiplicative.ofAdd d) ∈ co2DerivedImage
    rw [map_mul]
    exact co2DerivedImage.mul_mem hc hd
  smul_mem' b c hc := by
    rcases bit_cases b with rfl | rfl
    · change signEmbedding (Multiplicative.ofAdd (0 • c)) ∈ co2DerivedImage
      rw [zero_smul]
      change signEmbedding 1 ∈ co2DerivedImage
      rw [map_one]
      exact Subgroup.one_mem _
    · simpa only [one_smul] using hc

theorem short_difference_mem_co2DerivedCode (d : golay) (hd : d ∈ markedShortDifferences) :
    d ∈ co2DerivedCode := by
  obtain ⟨g,hgi,hgj,c,hci,hcj,rfl⟩ := hd
  let p := co2MarkedPermutation g hgi hgj
  let s := co2ShortSignElement c hci hcj
  have he := congrArg (fun f : Multiplicative golay →* LeechIsometryGroup => f (Multiplicative.ofAdd c))
    (sign_permutation_compatibility g)
  change signEmbedding (Multiplicative.ofAdd (golayPermutationEquiv g c)) =
    permutationEmbedding g * signEmbedding (Multiplicative.ofAdd c) * (permutationEmbedding g)⁻¹ at he
  have hh : signEmbedding (Multiplicative.ofAdd (golayPermutationEquiv g c - c)) = ⁅p.val,s.val⁆ := by
    rw [sub_eq_add_neg]
    change signEmbedding (Multiplicative.ofAdd (golayPermutationEquiv g c) * (Multiplicative.ofAdd c)⁻¹) = _
    rw [map_mul,map_inv,he]
    rfl
  change signEmbedding (Multiplicative.ofAdd (golayPermutationEquiv g c - c)) ∈ co2DerivedImage
  refine ⟨⁅p,s⁆,Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _),?_⟩
  exact hh.symm

theorem shortened_sign_mem_co2DerivedCode (c : golay)
    (hi : c.val ((0,0),0) = 0) (hj : c.val ((0,0),1) = 0) : c ∈ co2DerivedCode := by
  have hle : markedShortDifferenceSpan ≤ co2DerivedCode :=
    Submodule.span_le.mpr short_difference_mem_co2DerivedCode
  apply hle
  rw [marked_short_differences_span]
  exact Prod.ext hi hj

theorem co2_short_sign_mem_commutator (c : golay)
    (hi : c.val ((0,0),0) = 0) (hj : c.val ((0,0),1) = 0) :
    co2ShortSignElement c hi hj ∈ commutator Co2MarkedModel := by
  obtain ⟨g,hg,he⟩ := shortened_sign_mem_co2DerivedCode c hi hj
  have hh : g = co2ShortSignElement c hi hj := Subtype.ext he
  rwa [← hh]


theorem co2_noncommuting_pair : ∃ g h : Co2MarkedModel, g*h ≠ h*g := by
  have hi : (golayBasis 1).val ((0,0),0) = 0 := by rw [golayBasis_coe]; decide
  have hj : (golayBasis 1).val ((0,0),1) = 0 := by rw [golayBasis_coe]; decide
  let s := co2ShortSignElement (golayBasis 1) hi hj
  have hs := co2_short_sign_mem_commutator (golayBasis 1) hi hj
  have hn : s ≠ 1 := by
    intro he
    have he' : signEmbedding (Multiplicative.ofAdd (golayBasis 1)) = signEmbedding 1 := by
      have he0 := congrArg (fun g : Co2MarkedModel => g.val) he
      change signEmbedding (Multiplicative.ofAdd (golayBasis 1)) = 1 at he0
      exact he0.trans signEmbedding.map_one.symm
    have hc : golayBasis 1 = 0 := signEmbedding_injective he'
    have hw := golay_octad_basis.2 (1 : Fin 12)
    rw [hc] at hw
    norm_num [hammingNorm] at hw
  by_contra h
  push Not at h
  have hm : IsMulCommutative Co2MarkedModel := ⟨⟨h⟩⟩
  have hb := (commutator_eq_bot_iff Co2MarkedModel).mpr hm
  rw [hb] at hs
  exact hn hs

end Atlas.Conway
