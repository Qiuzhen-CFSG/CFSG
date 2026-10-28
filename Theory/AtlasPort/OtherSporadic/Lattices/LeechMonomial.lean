/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechMonomial.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechPermutations
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
The Golay monomial semidirect product embeds in the full Leech isometry group.
The sign-permutation conjugation identity defines the homomorphism, whose coordinate action proves injectivity.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes

def golayPermutationEquiv (σ : Mathieu24CodeModel) : golay ≃ₗ[Bit] golay where
  toFun c := ⟨coordinatePermutation σ.val c.val,(σ.prop _).mp c.prop⟩
  invFun c := ⟨coordinatePermutation σ.val⁻¹ c.val,(codeAutomorphisms.inv_mem σ.prop _).mp c.prop⟩
  left_inv c := by apply Subtype.ext; ext i; change c.val (σ.val.symm (σ.val i)) = c.val i; simp
  right_inv c := by apply Subtype.ext; ext i; change c.val (σ.val (σ.val.symm i)) = c.val i; simp
  map_add' c d := rfl
  map_smul' r c := rfl

def golayPermutationAction : Mathieu24CodeModel →* MulAut (Multiplicative golay) where
  toFun σ := (golayPermutationEquiv σ).toAddEquiv.toMultiplicative
  map_one' := by apply MulEquiv.ext; intro c; rfl
  map_mul' σ τ := by apply MulEquiv.ext; intro c; rfl

abbrev GolayMonomialGroup := Multiplicative golay ⋊[golayPermutationAction] Mathieu24CodeModel

def signEmbedding : Multiplicative golay →* LeechIsometryGroup where
  toFun c := signIsometry c.toAdd
  map_one' := by
    apply Subtype.ext; apply LinearEquiv.ext; intro x; apply Subtype.ext
    ext i; simp [signIsometry,signChange]
  map_mul' c d := by
    apply Subtype.ext; apply LinearEquiv.ext; intro x; apply Subtype.ext
    exact signChange_add c.toAdd.val d.toAdd.val x.val

theorem sign_permutation_compatibility (σ : Mathieu24CodeModel) :
    signEmbedding.comp (golayPermutationAction σ).toMonoidHom =
      (MulAut.conj (permutationEmbedding σ)).toMonoidHom.comp signEmbedding := by
  apply MonoidHom.ext
  intro c
  change signEmbedding ((golayPermutationAction σ) c) =
    permutationEmbedding σ * signEmbedding c * (permutationEmbedding σ)⁻¹
  apply (eq_mul_inv_iff_mul_eq).mpr
  apply Subtype.ext; apply LinearEquiv.ext; intro x; apply Subtype.ext
  rfl

def monomialEmbedding : GolayMonomialGroup →* LeechIsometryGroup :=
  SemidirectProduct.lift signEmbedding permutationEmbedding sign_permutation_compatibility

theorem monomialEmbedding_apply (g : GolayMonomialGroup) (x : leech) (i : Omega) :
    ((monomialEmbedding g).val x).val i =
      if g.left.toAdd.val i = 0 then x.val (g.right.val.symm i) else -x.val (g.right.val.symm i) := rfl

theorem monomialEmbedding_injective : Function.Injective monomialEmbedding := by
  intro g h he
  have hp : g.right = h.right := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    by_contra hi
    have hj : h.right.val.symm (g.right.val i) ≠ i := by
      intro hj
      apply hi
      have h := congrArg h.right.val hj
      simpa using h
    have hh := congrArg (fun k : LeechIsometryGroup =>
      ((k.val ⟨coordinateVector i 8,coordinate_eight_mem i⟩).val (g.right.val i))) he
    simp only [monomialEmbedding_apply] at hh
    have hg : g.right.val.symm (g.right.val i) = i := g.right.val.symm_apply_apply i
    rw [hg] at hh
    simp only [coordinateVector,Pi.single_apply,ite_true,hj,ite_false] at hh
    split_ifs at hh <;> norm_num at hh
  have hc : g.left = h.left := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    ext i
    have hh := congrArg (fun k : LeechIsometryGroup =>
      ((k.val ⟨coordinateVector (g.right.val.symm i) 8,coordinate_eight_mem _⟩).val i)) he
    simp only [monomialEmbedding_apply] at hh
    rw [← hp] at hh
    simp only [coordinateVector,Pi.single_apply,ite_true] at hh
    rcases bit_cases (g.left.toAdd.val i) with hg | hg <;>
      rcases bit_cases (h.left.toAdd.val i) with hh' | hh' <;> simp_all
  exact SemidirectProduct.ext hc hp

theorem monomial_inl : monomialEmbedding.comp SemidirectProduct.inl = signEmbedding :=
  SemidirectProduct.lift_comp_inl _ _ _

theorem monomial_inr : monomialEmbedding.comp SemidirectProduct.inr = permutationEmbedding :=
  SemidirectProduct.lift_comp_inr _ _ _

end Atlas.Lattices
