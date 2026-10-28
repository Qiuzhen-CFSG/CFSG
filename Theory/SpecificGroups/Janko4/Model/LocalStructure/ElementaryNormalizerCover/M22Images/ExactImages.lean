module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.EightProper
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.ThreeCases

/-!
# Exact E8 quotient image in the J4 zero-form reduction

After the actual native M22 fusion and the extension of every proper E8
subgroup, the third image case is equality with the full E8. Lifting the
conjugator through the original residual quotient retains both ambient
containment and that literal image equality. The intrinsic zero-form equation
places the source subgroup in the residual, with no additional form premise.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Proposition
2.2.2, pp.490--491. This discharges the image-size reduction for its final case;
the kernel intersection, lifted centralizer and strict normalizer enlargement
remain source obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu MathieuCode
namespace Janko4.LocalStructure.ElementaryNormalizerCover.M22Images
open Janko4.InvolutionCentralizers.Second LargeCenterRadicals.OuterHalf M22ChapterH
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- If the elementary image is not placed in an E16 source kernel, it is an
entire conjugate E8. The quotient and ambient maps are the original residual
maps, and the ambient conjugator is lifted through that same quotient. -/
theorem residual_elementary_exact_cases (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXR : X ≤ residualInclusion.range) :
    ∃ n : residual,
      X ≤ (residualLift (m22InnerHexadKernel m22SourceOctad)).map
        (MulAut.conj (residualInclusion n)).toMonoidHom ∨
      X ≤ (residualLift Sextet.innerTranslations).map
        (MulAut.conj (residualInclusion n)).toMonoidHom ∨
      (X ≤ (residualLift (smallContainer 0)).map
        (MulAut.conj (residualInclusion n)).toMonoidHom ∧
      (X.comap residualInclusion).map residualProjection =
        (smallContainer 0).map (MulAut.conj (residualProjection n)).toMonoidHom) := by
  let Xr := X.comap residualInclusion
  let : IsElementaryAbelian 2 Xr := IsElementaryAbelian.comap_of_injective
    residualInclusion residualInclusion_injective X
  let A := Xr.map residualProjection
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  obtain ⟨g,hg⟩ := elementary_native_exact_cases A
  obtain ⟨n,hn⟩ := residualProjection_surjective g
  have transfer (B : Subgroup M22) (h : A ≤ B.map (MulAut.conj g).toMonoidHom) :
      X ≤ (residualLift B).map (MulAut.conj (residualInclusion n)).toMonoidHom := by
    rw [← residualLift_conjugate,hn]
    intro x hx
    obtain ⟨r,hr⟩ := hXR hx
    refine ⟨r,?_,hr⟩
    exact h (mem_map_of_mem residualProjection
      (show r ∈ Xr from (show residualInclusion r ∈ X from hr.symm ▸ hx)))
  refine ⟨n,?_⟩
  rcases hg with h | h | h
  · exact Or.inl (transfer _ h)
  · exact Or.inr (Or.inl (transfer _ h))
  · exact Or.inr (Or.inr ⟨transfer _ h.le,by rwa [hn]⟩)

/-- Actual zero-form application with the native second-class member: the
residual-placement premise is discharged from the intrinsic outer-half form. -/
theorem zero_form_seed_exact_cases (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hzero : intrinsicElementaryForm X = 0) (hseed : (seed : Model) ∈ X) :
    ∃ n : residual,
      X ≤ (residualLift (m22InnerHexadKernel m22SourceOctad)).map
        (MulAut.conj (residualInclusion n)).toMonoidHom ∨
      X ≤ (residualLift Sextet.innerTranslations).map
        (MulAut.conj (residualInclusion n)).toMonoidHom ∨
      (X ≤ (residualLift (smallContainer 0)).map
        (MulAut.conj (residualInclusion n)).toMonoidHom ∧
      (X.comap residualInclusion).map residualProjection =
        (smallContainer 0).map (MulAut.conj (residualProjection n)).toMonoidHom) := by
  apply residual_elementary_exact_cases X
  have hseed1 : (seed : Model) ≠ 1 := by
    intro h
    have ho := seed_order
    simp [h] at ho
  have h := zero_form_le_involution_residual X hzero _ hseed hseed1
  change X ≤ (ambientCentralizer.subtype.comp residual.subtype).range
  rw [MonoidHom.range_comp,range_subtype]
  exact h

end Janko4.LocalStructure.ElementaryNormalizerCover.M22Images
