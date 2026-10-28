/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechVisibleSymmetries.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechFullIsometries
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechMonomial

/-!
Visible sign and permutation symmetries, including scalar negation.
The monomial embedding identifies its image and proves faithfulness of both constituent actions.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes

def monomialSubgroup : Subgroup LeechIsometryGroup := monomialEmbedding.range

def monomialSubgroupEquiv : GolayMonomialGroup ≃* monomialSubgroup :=
  MonoidHom.ofInjective monomialEmbedding_injective

theorem signEmbedding_injective : Function.Injective signEmbedding := by
  intro c d h
  have he : monomialEmbedding (SemidirectProduct.inl c) = monomialEmbedding (SemidirectProduct.inl d) := by
    simpa only [← MonoidHom.comp_apply,monomial_inl] using h
  exact congrArg SemidirectProduct.left (monomialEmbedding_injective he)

theorem permutationEmbedding_injective : Function.Injective permutationEmbedding := by
  intro g h he
  have he' : monomialEmbedding (SemidirectProduct.inr g) = monomialEmbedding (SemidirectProduct.inr h) := by
    simpa only [← MonoidHom.comp_apply,monomial_inr] using he
  exact congrArg SemidirectProduct.right (monomialEmbedding_injective he')

def negationIsometry : LeechIsometryGroup := signIsometry ⟨allOnes,C0_le_golay allOnes_mem_C0⟩

theorem negationIsometry_apply (x : leech) : negationIsometry.val x = -x := by
  apply Subtype.ext
  ext i
  simp [negationIsometry,signIsometry,signChange,allOnes]

theorem allOnes_sign_negation : signEmbedding
    (Multiplicative.ofAdd (⟨allOnes,C0_le_golay allOnes_mem_C0⟩ : golay)) = negationIsometry := rfl

theorem negationIsometry_sq : negationIsometry * negationIsometry = 1 := by
  apply Subtype.ext; apply LinearEquiv.ext; intro x
  change negationIsometry.val (negationIsometry.val x) = x
  rw [negationIsometry_apply,negationIsometry_apply,neg_neg]

theorem negationIsometry_ne_one : negationIsometry ≠ 1 := by
  intro h
  let a : Omega := ((0,0),0)
  let x : leech := ⟨coordinateVector a 8,coordinate_eight_mem a⟩
  have he := congrArg (fun g : LeechIsometryGroup => (g.val x).val a) h
  change (negationIsometry.val x).val a = x.val a at he
  rw [negationIsometry_apply] at he
  norm_num [x,coordinateVector] at he

structure VisibleSymmetryConstruction : Prop where
  finite_full_group : Finite LeechIsometryGroup
  finite_shells : ∀ r : ℤ, Finite (LeechShell r)
  faithful_minimal_shell : Function.Injective (shellRepresentation 4)
  extension_agrees : ∀ g x,
    rationalExtension g (rationalEmbedding x.val) = rationalEmbedding (g x).val
  extension_bijective : Function.Bijective fullIsometryExtension
  monomial_injective : Function.Injective monomialEmbedding
  signs_injective : Function.Injective signEmbedding
  permutations_injective : Function.Injective permutationEmbedding
  conjugation : ∀ σ, signEmbedding.comp (golayPermutationAction σ).toMonoidHom =
    (MulAut.conj (permutationEmbedding σ)).toMonoidHom.comp signEmbedding
  negation : ∀ x, negationIsometry.val x = -x
  negation_nonidentity : negationIsometry ≠ 1

theorem leech_visible_symmetries_constructed : VisibleSymmetryConstruction where
  finite_full_group := inferInstance
  finite_shells := shell_finite
  faithful_minimal_shell := minimal_shell_faithful
  extension_agrees := rationalExtension_agrees
  extension_bijective := fullIsometryExtension_bijective
  monomial_injective := monomialEmbedding_injective
  signs_injective := signEmbedding_injective
  permutations_injective := permutationEmbedding_injective
  conjugation := sign_permutation_compatibility
  negation := negationIsometry_apply
  negation_nonidentity := negationIsometry_ne_one

end Atlas.Lattices
