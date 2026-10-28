/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechFullIsometries.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Proof syntax and simplifier arguments are adjusted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechRationalExtension

/-!
Equivalence between integral Leech isometries and rational isometries preserving the embedded lattice.
Extension and restriction are inverse, as verified on the rational lattice basis.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes

theorem rationalExtension_form (g : LeechIsometryGroup) (x y : RationalCoordinates) :
    rationalForm (rationalExtension g.val x) (rationalExtension g.val y) = rationalForm x y := by
  have h : rationalForm.comp (rationalExtension g.val).toLinearMap
      (rationalExtension g.val).toLinearMap = rationalForm := by
    apply rationalLeechBasis.ext
    intro i
    apply rationalLeechBasis.ext
    intro j
    change rationalForm (rationalExtension g.val (rationalLeechBasis i))
      (rationalExtension g.val (rationalLeechBasis j)) = rationalForm (rationalLeechBasis i) (rationalLeechBasis j)
    rw [rationalLeechBasis_apply,rationalLeechBasis_apply,rationalExtension_agrees,rationalExtension_agrees]
    exact leechIsometry_preserves_form g _ _
  exact congrArg (fun B : LinearMap.BilinForm ℚ RationalCoordinates => B x y) h

theorem rationalExtension_preserves (g : leech ≃ₗ[ℤ] leech) (w : RationalCoordinates) :
    w ∈ rationalLeech ↔ rationalExtension g w ∈ rationalLeech := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    rw [rationalExtension_agrees g ⟨x,hx⟩]
    exact ⟨g ⟨x,hx⟩,(g ⟨x,hx⟩).prop,rfl⟩
  · rintro ⟨x,hx,he⟩
    have h : rationalExtension g (rationalEmbedding (g.symm ⟨x,hx⟩).val) = rationalEmbedding x := by
      rw [rationalExtension_agrees]; simp
    have hw := (rationalExtension g).injective (h.trans he)
    rw [← hw]
    exact ⟨g.symm ⟨x,hx⟩,(g.symm ⟨x,hx⟩).prop,rfl⟩

def rationalLatticeIsometries : Subgroup (RationalCoordinates ≃ₗ[ℚ] RationalCoordinates) where
  carrier := {g | (∀ x y, rationalForm (g x) (g y) = rationalForm x y) ∧
    ∀ x, x ∈ rationalLeech ↔ g x ∈ rationalLeech}
  one_mem' := ⟨fun _ _ => rfl,fun _ => Iff.rfl⟩
  mul_mem' := by
    rintro g h ⟨hg,hgL⟩ ⟨hh,hhL⟩
    exact ⟨fun x y => (hg (h x) (h y)).trans (hh x y),fun x => (hhL x).trans (hgL (h x))⟩
  inv_mem' := by
    rintro g ⟨hg,hgL⟩
    refine ⟨fun x y => ?_,fun x => ?_⟩
    · have h := hg (g.symm x) (g.symm y)
      simpa using h.symm
    · have h := hgL (g.symm x)
      simpa using h.symm

def latticeEmbeddingEquiv : leech ≃ₗ[ℤ] rationalLeech :=
  Submodule.equivMapOfInjective rationalEmbedding rationalEmbedding_injective leech

theorem latticeEmbeddingEquiv_apply (x : leech) :
    (latticeEmbeddingEquiv x).val = rationalEmbedding x.val := rfl

def restrictRationalLattice (g : rationalLatticeIsometries) : rationalLeech ≃ₗ[ℤ] rationalLeech where
  toFun x := ⟨g.val x.val,(g.prop.2 x.val).mp x.prop⟩
  invFun x := ⟨g.val.symm x.val,by
    apply (g.prop.2 _).mpr
    simp⟩
  left_inv x := by apply Subtype.ext; exact g.val.symm_apply_apply x.val
  right_inv x := by apply Subtype.ext; exact g.val.apply_symm_apply x.val
  map_add' x y := Subtype.ext (g.val.map_add x.val y.val)
  map_smul' r x := Subtype.ext ((g.val.restrictScalars ℤ).map_smul r x.val)

def restrictToLeech (g : rationalLatticeIsometries) : leech ≃ₗ[ℤ] leech :=
  latticeEmbeddingEquiv.trans ((restrictRationalLattice g).trans latticeEmbeddingEquiv.symm)

theorem restriction_agrees (g : rationalLatticeIsometries) (x : leech) :
    rationalEmbedding (restrictToLeech g x).val = g.val (rationalEmbedding x.val) := by
  have h := congrArg Subtype.val
    (latticeEmbeddingEquiv.apply_symm_apply (restrictRationalLattice g (latticeEmbeddingEquiv x)))
  exact h

def restrictionIsometry (g : rationalLatticeIsometries) : LeechIsometryGroup :=
  ⟨restrictToLeech g,by
    intro x y
    have h := g.prop.1 (rationalEmbedding x.val) (rationalEmbedding y.val)
    rw [← restriction_agrees,← restriction_agrees,rationalForm_integer,rationalForm_integer] at h
    have hq : (integerDot (restrictToLeech g x).val (restrictToLeech g y).val : ℚ) =
        (integerDot x.val y.val : ℚ) := by linarith
    exact_mod_cast hq⟩

def fullIsometryExtension : LeechIsometryGroup →* rationalLatticeIsometries where
  toFun g := ⟨rationalExtension g.val,rationalExtension_form g,rationalExtension_preserves g.val⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply rationalLeechBasis.ext
    intro i
    change rationalExtension 1 (rationalLeechBasis i) = rationalLeechBasis i
    rw [rationalLeechBasis_apply,rationalExtension_agrees]
    rfl
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply rationalLeechBasis.ext
    intro i
    change rationalExtension (g.val*h.val) (rationalLeechBasis i) =
      rationalExtension g.val (rationalExtension h.val (rationalLeechBasis i))
    rw [rationalLeechBasis_apply,rationalExtension_agrees,rationalExtension_agrees,rationalExtension_agrees]
    rfl

theorem fullIsometryExtension_bijective : Function.Bijective fullIsometryExtension := by
  constructor
  · intro g h he
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    apply rationalEmbedding_injective
    have hi := congrArg (fun k : rationalLatticeIsometries => k.val (rationalEmbedding x.val)) he
    change rationalExtension g.val (rationalEmbedding x.val) = rationalExtension h.val (rationalEmbedding x.val) at hi
    simpa only [rationalExtension_agrees] using hi
  · intro g
    refine ⟨restrictionIsometry g,?_⟩
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply rationalLeechBasis.ext
    intro i
    change rationalExtension (restrictToLeech g) (rationalLeechBasis i) = g.val (rationalLeechBasis i)
    rw [rationalLeechBasis_apply,rationalExtension_agrees,restriction_agrees]

def fullIsometryEquiv : LeechIsometryGroup ≃* rationalLatticeIsometries :=
  MulEquiv.ofBijective fullIsometryExtension fullIsometryExtension_bijective

end Atlas.Lattices
