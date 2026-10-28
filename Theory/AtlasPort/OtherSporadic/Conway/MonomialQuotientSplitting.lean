/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/MonomialQuotientSplitting.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.GolaySignQuotient

/-!
The split extension describing the monomial subgroup in the Leech central quotient.
The proof descends the semidirect product map and identifies its kernel, retraction, and section.

Source: Gerald Höhn, `Atlas/Conway/MonomialQuotientSplitting.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to Lean 4.33.0 with public imports and exposed concrete definitions
for the source cross-module reductions; the mathematical namespaces are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

/-- The quotient of the original monomial group, identified with the actual split product. -/
def monomialQuotientSplitEquiv : GolayMonomialGroup ⧸ quotientMonomialEmbedding.ker ≃*
    GolayQuotientMonomialGroup :=
  (QuotientGroup.quotientMulEquivOfEq monomialSignQuotientProjection_kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective monomialSignQuotientProjection
      monomialSignQuotientProjection_surjective)

theorem monomialQuotientSplitEquiv_mk (m : GolayMonomialGroup) :
    monomialQuotientSplitEquiv (QuotientGroup.mk' _ m) = monomialSignQuotientProjection m := rfl

/-- The actual projected monomial subgroup, with its Golay quotient semidirect decomposition. -/
def quotientMonomialSplitEquiv : GolayQuotientMonomialGroup ≃* quotientMonomialSubgroup :=
  monomialQuotientSplitEquiv.symm.trans quotientMonomialEquiv

theorem quotientMonomialSplitEquiv_compatible (m : GolayMonomialGroup) :
    (quotientMonomialSplitEquiv (monomialSignQuotientProjection m)).val =
      quotientMonomialEmbedding m := by
  rw [← monomialQuotientSplitEquiv_mk]
  change (quotientMonomialEquiv (monomialQuotientSplitEquiv.symm
    (monomialQuotientSplitEquiv (QuotientGroup.mk' _ m)))).val = _
  rw [MulEquiv.symm_apply_apply]
  rfl

def quotientMonomialInclusion : GolayQuotientMonomialGroup →* LeechCentralQuotient :=
  quotientMonomialSubgroup.subtype.comp quotientMonomialSplitEquiv.toMonoidHom

theorem quotientMonomialInclusion_injective : Function.Injective quotientMonomialInclusion :=
  Subtype.val_injective.comp quotientMonomialSplitEquiv.injective

def quotientMonomialSigns : GolaySignQuotient →* quotientMonomialSubgroup :=
  quotientMonomialSplitEquiv.toMonoidHom.comp SemidirectProduct.inl

def quotientMonomialSplitting : Mathieu24CodeModel →* quotientMonomialSubgroup :=
  quotientMonomialSplitEquiv.toMonoidHom.comp SemidirectProduct.inr

def quotientMonomialRetraction : quotientMonomialSubgroup →* Mathieu24CodeModel :=
  SemidirectProduct.rightHom.comp quotientMonomialSplitEquiv.symm.toMonoidHom

theorem quotientMonomialSplitting_compatible (g : Mathieu24CodeModel) :
    (quotientMonomialSplitting g).val = quotientPermutationEmbedding g := by
  have he := quotientMonomialSplitEquiv_compatible (SemidirectProduct.inr g)
  exact he

theorem quotientMonomialSigns_compatible (c : Multiplicative golay) :
    (quotientMonomialSigns (golaySignProjection c)).val =
      leechCentralProjection (signEmbedding c) := by
  have he := quotientMonomialSplitEquiv_compatible (SemidirectProduct.inl c)
  exact he

theorem quotientMonomialRetraction_splitting :
    quotientMonomialRetraction.comp quotientMonomialSplitting = MonoidHom.id _ := by
  apply MonoidHom.ext; intro g
  change (quotientMonomialSplitEquiv.symm
    (quotientMonomialSplitEquiv (SemidirectProduct.inr g))).right = g
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem quotientMonomialRetraction_kernel :
    quotientMonomialRetraction.ker = quotientMonomialSigns.range := by
  ext m
  constructor
  · intro hm
    have hr : (quotientMonomialSplitEquiv.symm m).right = 1 := hm
    refine ⟨(quotientMonomialSplitEquiv.symm m).left,?_⟩
    change quotientMonomialSplitEquiv (SemidirectProduct.inl _) = m
    apply quotientMonomialSplitEquiv.symm.injective
    rw [MulEquiv.symm_apply_apply]
    apply SemidirectProduct.ext
    · rfl
    · exact hr.symm
  · rintro ⟨c,rfl⟩
    change (quotientMonomialSplitEquiv.symm
      (quotientMonomialSplitEquiv (SemidirectProduct.inl c))).right = 1
    rw [MulEquiv.symm_apply_apply]
    rfl

theorem quotientMonomialSigns_injective : Function.Injective quotientMonomialSigns :=
  quotientMonomialSplitEquiv.injective.comp SemidirectProduct.inl_injective

theorem quotientMonomialSplitting_injective : Function.Injective quotientMonomialSplitting :=
  quotientMonomialSplitEquiv.injective.comp SemidirectProduct.inr_injective

end Atlas.Conway
