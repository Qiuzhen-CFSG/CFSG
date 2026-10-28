module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.ExtensionClasses.MixedCoordinates
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.ExtensionClasses.MixedExhaustion.Certificate
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.ExtensionClasses.MixedExhaustion.RootWords

/-!
# Exhaustion of normalized mixed binary SL₃(4) extensions

A normalized natural-by-dual cross block is Frobenius-semilinear. Its values
on three concrete generators therefore have 27 field coordinates. Five short
word relations impose sixteen linear equations. A kernel-checked matrix
identity expresses every solution as a section change plus a combination of
the two published mixed formulas. Explicit root words, checked together with
the values of both templates, extend this comparison to every transvection.

The result is exactly the generator comparison needed by
`BlockCocycle.equivOfTransvectionCoboundary`. Construction of the mixed model
cocycles and assembly of all four ordered pairs remain with their respective
owners; neither is an input to this upper bound.

Source context: James (1973), Lemma 8.3, cited by Aschbacher–Smith H.12.1,
printed pp.393–394. The calculation concerns the stated natural-by-dual point
restriction, without presuming a complete catalogue of irreducible constituents.
-/

noncomputable section

open Matrix
namespace Representation.SL3FourLocalCatalogue.ExtensionExhaustion
open SL3FourNaturalDual ExtensionCoordinates

private lemma semilinear_add (m n : Matrix (Fin 3) (Fin 3) F) :
    matrixSemilinear (m + n) = matrixSemilinear m + matrixSemilinear n := by
  apply LinearMap.ext
  intro v
  exact Matrix.add_mulVec m n (squareVector v)

private lemma semilinear_left (g : SL) (m : Matrix (Fin 3) (Fin 3) F) :
    matrixSemilinear (g.val * m) = (constituent .natural g).comp (matrixSemilinear m) := by
  apply LinearMap.ext
  intro v
  exact (Matrix.mulVec_mulVec (squareVector v) g.val m).symm

private lemma semilinear_right (g : SL) (m : Matrix (Fin 3) (Fin 3) F) :
    matrixSemilinear (m * right g) = (matrixSemilinear m).comp (constituent .dual g) := by
  have hs (v : W) : squareVector (constituent .dual g v) = (right g).mulVec (squareVector v) := by
    funext i
    change SL2FourNatural.fieldFrobenius (∑ j, (Matrix.SpecialLinearGroup.inverseTranspose g).val i j * v j) =
      ∑ j, SL2FourNatural.fieldFrobenius ((Matrix.SpecialLinearGroup.inverseTranspose g).val i j) *
        SL2FourNatural.fieldFrobenius (v j)
    simp only [map_sum, map_mul]
  apply LinearMap.ext
  intro v
  change (m * right g).mulVec (squareVector v) = m.mulVec (squareVector (constituent .dual g v))
  rw [hs, Matrix.mulVec_mulVec]

private lemma coboundary_of_coeff (c : BlockCocycle .natural .dual) (hc : c.value z = 0)
    (g : SL) (m : Matrix (Fin 3) (Fin 3) F) (p q : F)
    (he : coeff c g = g.val * m + m * right g + p • symmetricMatrix g + q • dualSymmetricMatrix g) :
    c.value g + (matrixSemilinear m).comp (constituent .dual g) =
      (constituent .natural g).comp (matrixSemilinear m) + mixedValue p q g := by
  have h : c.value g = matrixSemilinear (coeff c g) := by
    apply LinearMap.ext
    exact coeff_apply c hc g
  rw [h, he]
  rw [show g.val * m + m * right g + p • symmetricMatrix g + q • dualSymmetricMatrix g =
    (g.val * m + m * right g) + (p • symmetricMatrix g + q • dualSymmetricMatrix g) by abel]
  rw [semilinear_add, semilinear_add, semilinear_left, semilinear_right]
  change (_ + _ + mixedValue p q g) + _ = _
  have hz : (matrixSemilinear m).comp (constituent .dual g) +
      (matrixSemilinear m).comp (constituent .dual g) = 0 := by
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 by decide, zero_smul]
  linear_combination (norm := abel) hz

end Representation.SL3FourLocalCatalogue.ExtensionExhaustion

namespace Representation.SL3FourLocalCatalogue.BlockCocycle
open ExtensionCoordinates ExtensionExhaustion

/-- Every normalized natural-by-dual binary SL₃(4) extension agrees with the
published two-parameter formula on all elementary transvections after changing
the linear section. No cocycle law for `mixedValue` is assumed. -/
public theorem exists_mixed_transvection_coboundary
    (c : BlockCocycle .natural .dual) (hc : c.value z = 0) :
    ∃ (p q : F) (f : W →ₗ[ZMod 2] W),
      ∀ (i j : Fin 3) (hij : i ≠ j) (t : F),
        c.value (Matrix.SpecialLinearGroup.transvection hij t) +
          f.comp (constituent .dual (Matrix.SpecialLinearGroup.transvection hij t)) =
        (constituent .natural (Matrix.SpecialLinearGroup.transvection hij t)).comp f +
          mixedValue p q (Matrix.SpecialLinearGroup.transvection hij t) := by
  obtain ⟨v, hv⟩ := inputs_exhausted c hc
  refine ⟨v 0, v 1, matrixSemilinear (sectionMatrix v), ?_⟩
  intro i j hij t
  obtain ⟨a, rfl⟩ := scalar_surjective t
  apply coboundary_of_coeff c hc
  calc
    coeff c (Matrix.SpecialLinearGroup.transvection hij (scalar a)) =
        wordMap (rootWord i j a) (inputs c) := by
      rw [wordMap_value c hc, rootWord_value i j hij a]
    _ = _ := by
      rw [hv, wordMap_models]
      simp only [← right_word, rootWord_value i j hij a,
        rootWord_symmetric i j hij a, rootWord_dual i j hij a]

end Representation.SL3FourLocalCatalogue.BlockCocycle
