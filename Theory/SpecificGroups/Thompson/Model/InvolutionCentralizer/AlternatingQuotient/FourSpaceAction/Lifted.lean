module
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient.FourSpaceAction.Blocks

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The 29/21 section and the nine lifted 25-spaces

The section basis embeds its 29-dimensional coordinate space. Projection
onto the last eight coordinates has a 21-dimensional kernel, whose image
is exactly the span of the first twenty-one published basis rows.
The inverse images of the nine factor four-spaces are distinct 25-spaces
in the original 248-dimensional representation. The two literal word
matrices preserve the section and denominator and give the prescribed
transitions of these lifts.

The explicit matrix identities are proved in `SectionMatrices`; the
four-space geometry is proved in `Blocks`. This realizes the source section
for GLS3 Table 5.3x and Aschbacher--Smith A.2.19 without a split-extension
or group-recognition assumption.
-/

public section
open scoped Matrix BigOperators
namespace Thompson.InvolutionCentralizer.AlternatingQuotient

@[expose] def sectionSpace : Submodule (ZMod 2) (Fin 248 → ZMod 2) :=
  LinearMap.range sectionBasisMatrix.vecMulLinear

@[expose] def denominatorSpace : Submodule (ZMod 2) (Fin 248 → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range fun i : Fin 21 => sectionBasisMatrix (i.castAdd 8))

/-- The inverse image of one factor four-space, embedded in the original representation. -/
@[expose] def liftedBlockSpace (i : Fin 9) : Submodule (ZMod 2) (Fin 248 → ZMod 2) :=
  Submodule.map sectionBasisMatrix.vecMulLinear
    (Submodule.comap factorProjection.vecMulLinear (blockSpace i))

theorem sectionBasis_vecMul_injective : Function.Injective sectionBasisMatrix.vecMulLinear := by
  intro x y h
  have := congrArg (fun v => v ᵥ* sectionRightInverseMatrix) h
  simpa only [Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul,
    sectionBasis_mul_rightInverse, Matrix.vecMul_one] using this

theorem factorProjection_vecMul_surjective : Function.Surjective factorProjection.vecMulLinear := by
  intro v
  refine ⟨v ᵥ* factorLift, ?_⟩
  change (v ᵥ* factorLift) ᵥ* factorProjection = v
  rw [Matrix.vecMul_vecMul, factorLift_mul_projection, Matrix.vecMul_one]

theorem liftedBlockSpace_injective : Function.Injective liftedBlockSpace := by
  intro i j h
  apply blockSpace_injective
  apply Submodule.comap_injective_of_surjective factorProjection_vecMul_surjective
  exact Submodule.map_injective_of_injective sectionBasis_vecMul_injective h

theorem factorProjection_vecMul (v : Fin 29 → ZMod 2) (j : Fin 8) :
    (v ᵥ* factorProjection) j = v (j.natAdd 21) := by
  change (∑ i : Fin 29, v i * factorProjection i j) = _
  have he (i : Fin 29) : (i.val = 21 + j.val) ↔ i = j.natAdd 21 := by
    exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  simp only [factorProjection_apply, he]
  simp

theorem denominatorSpace_eq_map_ker : denominatorSpace =
    (LinearMap.ker factorProjection.vecMulLinear).map sectionBasisMatrix.vecMulLinear := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single (i.castAdd 8) 1, ?_, ?_⟩
    · change (Pi.single (i.castAdd 8) (1 : ZMod 2)) ᵥ* factorProjection = 0
      ext j
      rw [factorProjection_vecMul]
      have hij : j.natAdd 21 ≠ i.castAdd 8 := by
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at this
        omega
      simp [hij.symm]
    · change (Pi.single (i.castAdd 8) (1 : ZMod 2)) ᵥ* sectionBasisMatrix = _
      simp only [Matrix.single_one_vecMul, Matrix.row_def]
  · rintro v ⟨c, hc, rfl⟩
    have hz (j : Fin 8) : c (j.natAdd 21) = 0 := by
      rw [← factorProjection_vecMul c j]
      exact congrFun hc j
    change c ᵥ* sectionBasisMatrix ∈ denominatorSpace
    rw [Matrix.vecMul_eq_sum, Fin.sum_univ_add (a := 21) (b := 8) (fun i => c i • sectionBasisMatrix i)]
    simp only [hz, zero_smul, Finset.sum_const_zero, add_zero]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem denominatorSpace_le_section : denominatorSpace ≤ sectionSpace := by
  rw [denominatorSpace_eq_map_ker]
  intro v hv
  obtain ⟨c, _, hc⟩ := hv
  exact ⟨c, hc⟩

theorem denominatorSpace_le_liftedBlock (i : Fin 9) :
    denominatorSpace ≤ liftedBlockSpace i := by
  rw [denominatorSpace_eq_map_ker]
  apply Submodule.map_mono
  intro v hv
  change v ᵥ* factorProjection ∈ blockSpace i
  rw [show v ᵥ* factorProjection = 0 from hv]
  exact (blockSpace i).zero_mem

theorem liftedBlockSpace_le_section (i : Fin 9) : liftedBlockSpace i ≤ sectionSpace :=
  by
    intro v hv
    obtain ⟨c, _, hc⟩ := hv
    exact ⟨c, hc⟩

private theorem section_maps {X : Matrix (Fin 248) (Fin 248) (ZMod 2)}
    {S : Matrix (Fin 29) (Fin 29) (ZMod 2)}
    (h : sectionBasisMatrix * X = S * sectionBasisMatrix)
    {v : Fin 248 → ZMod 2} (hv : v ∈ sectionSpace) : v ᵥ* X ∈ sectionSpace := by
  obtain ⟨c, rfl⟩ := hv
  refine ⟨c ᵥ* S, ?_⟩
  change (c ᵥ* S) ᵥ* sectionBasisMatrix = (c ᵥ* sectionBasisMatrix) ᵥ* X
  rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, h]

private theorem denominator_maps {X : Matrix (Fin 248) (Fin 248) (ZMod 2)}
    {S : Matrix (Fin 29) (Fin 29) (ZMod 2)} {F : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (h : sectionBasisMatrix * X = S * sectionBasisMatrix)
    (hF : S * factorProjection = factorProjection * F)
    {v : Fin 248 → ZMod 2} (hv : v ∈ denominatorSpace) : v ᵥ* X ∈ denominatorSpace := by
  rw [denominatorSpace_eq_map_ker] at hv ⊢
  obtain ⟨c, hc, rfl⟩ := hv
  refine ⟨c ᵥ* S, ?_, ?_⟩
  · change (c ᵥ* S) ᵥ* factorProjection = 0
    rw [Matrix.vecMul_vecMul, hF, ← Matrix.vecMul_vecMul,
      show c ᵥ* factorProjection = 0 from hc, Matrix.zero_vecMul]
  · change (c ᵥ* S) ᵥ* sectionBasisMatrix = (c ᵥ* sectionBasisMatrix) ᵥ* X
    rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, h]

private theorem liftedBlock_maps {X : Matrix (Fin 248) (Fin 248) (ZMod 2)}
    {S : Matrix (Fin 29) (Fin 29) (ZMod 2)} {F : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    {i j : Fin 9}
    (h : sectionBasisMatrix * X = S * sectionBasisMatrix)
    (hF : S * factorProjection = factorProjection * F)
    (hblock : ∀ v ∈ blockSpace i, v ᵥ* F ∈ blockSpace j)
    {v : Fin 248 → ZMod 2} (hv : v ∈ liftedBlockSpace i) :
    v ᵥ* X ∈ liftedBlockSpace j := by
  obtain ⟨c, hc, rfl⟩ := hv
  refine ⟨c ᵥ* S, ?_, ?_⟩
  · change (c ᵥ* S) ᵥ* factorProjection ∈ blockSpace j
    rw [Matrix.vecMul_vecMul, hF, ← Matrix.vecMul_vecMul]
    exact hblock _ hc
  · change (c ᵥ* S) ᵥ* sectionBasisMatrix = (c ᵥ* sectionBasisMatrix) ᵥ* X
    rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, h]

theorem sectionSpace_wordA {v : Fin 248 → ZMod 2} (hv : v ∈ sectionSpace) :
    v ᵥ* wordAMatrix ∈ sectionSpace := section_maps sectionBasis_mul_wordA hv

theorem sectionSpace_wordB {v : Fin 248 → ZMod 2} (hv : v ∈ sectionSpace) :
    v ᵥ* wordBMatrix ∈ sectionSpace := section_maps sectionBasis_mul_wordB hv

theorem denominatorSpace_wordA {v : Fin 248 → ZMod 2} (hv : v ∈ denominatorSpace) :
    v ᵥ* wordAMatrix ∈ denominatorSpace :=
  denominator_maps sectionBasis_mul_wordA sectionA_mul_projection hv

theorem denominatorSpace_wordB {v : Fin 248 → ZMod 2} (hv : v ∈ denominatorSpace) :
    v ᵥ* wordBMatrix ∈ denominatorSpace :=
  denominator_maps sectionBasis_mul_wordB sectionB_mul_projection hv

theorem liftedBlockSpace_wordA (i : Fin 9) {v : Fin 248 → ZMod 2} (hv : v ∈ liftedBlockSpace i) :
    v ᵥ* wordAMatrix ∈ liftedBlockSpace (permA⁻¹ i) :=
  liftedBlock_maps sectionBasis_mul_wordA sectionA_mul_projection (fun _ => blockSpace_factorA i) hv

theorem liftedBlockSpace_wordB (i : Fin 9) {v : Fin 248 → ZMod 2} (hv : v ∈ liftedBlockSpace i) :
    v ᵥ* wordBMatrix ∈ liftedBlockSpace (permB⁻¹ i) :=
  liftedBlock_maps sectionBasis_mul_wordB sectionB_mul_projection (fun _ => blockSpace_factorB i) hv

theorem sectionSpace_finrank : Module.finrank (ZMod 2) sectionSpace = 29 := by
  rw [sectionSpace, LinearMap.finrank_range_of_inj sectionBasis_vecMul_injective]
  simp

theorem factorProjection_ker_finrank :
    Module.finrank (ZMod 2) (LinearMap.ker factorProjection.vecMulLinear) = 21 := by
  have h := factorProjection.vecMulLinear.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr factorProjection_vecMul_surjective] at h
  simp only [Module.finrank_fin_fun, finrank_top] at h
  omega

theorem denominatorSpace_finrank : Module.finrank (ZMod 2) denominatorSpace = 21 := by
  rw [denominatorSpace_eq_map_ker,
    ← (Submodule.equivMapOfInjective _ sectionBasis_vecMul_injective _).finrank_eq]
  exact factorProjection_ker_finrank

theorem liftedBlockSpace_finrank (i : Fin 9) :
    Module.finrank (ZMod 2) (liftedBlockSpace i) = 25 := by
  rw [liftedBlockSpace,
    ← (Submodule.equivMapOfInjective _ sectionBasis_vecMul_injective _).finrank_eq]
  let f := (blockSpace i).mkQ.comp factorProjection.vecMulLinear
  have hf : Function.Surjective f :=
    (Submodule.mkQ_surjective _).comp factorProjection_vecMul_surjective
  have hk : LinearMap.ker f = (blockSpace i).comap factorProjection.vecMulLinear := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have h := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hf, finrank_top, Submodule.finrank_quotient,
    blockSpace_finrank, hk] at h
  simp only [Module.finrank_fin_fun] at h
  omega

end Thompson.InvolutionCentralizer.AlternatingQuotient
