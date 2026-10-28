module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.Fusion
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.Residual

/-!
# Three actual inner-quotient image cases in J4

The native E8 fusion and extension reduce the saved six-container cover to the
source's two E16 kernels and one E8. The inverse-image calculation commutes with
conjugation through the original residual projection and ambient inclusion.
It applies to every mixed zero-form elementary subgroup, using the proved
intrinsic form. These statements concern subgroup placement; Section 2.2's
nontrivial lift geometry and whole-normalizer conclusions remain to be proved.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Lemma 2.2.1
and Proposition 2.2.2, pp.489--490.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu MathieuCode
namespace Janko4.LocalStructure.ElementaryNormalizerCover.M22Images
open Janko4.InvolutionCentralizers.Second LargeCenterRadicals.OuterHalf M22ChapterH
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- Inverse-image containment uses the original residual quotient and inclusion. -/
theorem residualLift_mono {A B : Subgroup M22} (h : A ≤ B) :
    residualLift A ≤ residualLift B := map_mono (comap_mono h)

/-- Conjugation commutes with the literal lifted subgroup. Both its actor and
its quotient image are the original maps of the second-centralizer residual. -/
theorem residualLift_conjugate (B : Subgroup M22) (n : residual) :
    residualLift (B.map (MulAut.conj (residualProjection n)).toMonoidHom) =
      (residualLift B).map (MulAut.conj (residualInclusion n)).toMonoidHom := by
  apply le_antisymm
  · rintro _ ⟨r,⟨b,hb,he⟩,rfl⟩
    have hback : residualProjection (n⁻¹*r*n) = b := by
      rw [map_mul,map_mul,map_inv,← he]
      simp [mul_assoc]
    refine ⟨residualInclusion (n⁻¹*r*n),?_,?_⟩
    · exact ⟨n⁻¹*r*n,show residualProjection (n⁻¹*r*n) ∈ B from hback.symm ▸ hb,rfl⟩
    · simp [map_mul,map_inv,mul_assoc]
  · rintro _ ⟨_,⟨r,hr,rfl⟩,rfl⟩
    refine ⟨n*r*n⁻¹,?_,?_⟩
    · exact ⟨residualProjection r,hr,by simp [map_mul,map_inv]⟩
    · simp [map_mul,map_inv]

private theorem conjugate_comp (B : Subgroup Model) (g h : Model) :
    (B.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      B.map (MulAut.conj (g*h)).toMonoidHom := by
  rw [map_map]
  apply congrArg (fun f : Model →* Model => B.map f)
  apply MonoidHom.ext
  intro x
  change g*(h*x*h⁻¹)*g⁻¹ = (g*h)*x*(g*h)⁻¹
  simp [mul_assoc]

private theorem small_lift_three_cases (k : Fin 4) : ∃ n : residual,
    residualLift (smallContainer k) ≤
      (residualLift (m22InnerHexadKernel m22SourceOctad)).map
        (MulAut.conj (residualInclusion n)).toMonoidHom ∨
    residualLift (smallContainer k) ≤ (residualLift Sextet.innerTranslations).map
        (MulAut.conj (residualInclusion n)).toMonoidHom ∨
    residualLift (smallContainer k) ≤ (residualLift (smallContainer 0)).map
        (MulAut.conj (residualInclusion n)).toMonoidHom := by
  obtain ⟨g,hg⟩ := smallContainer_three_cases k
  obtain ⟨n,hn⟩ := residualProjection_surjective g
  have transfer (B : Subgroup M22)
      (h : smallContainer k ≤ B.map (MulAut.conj g).toMonoidHom) :
      residualLift (smallContainer k) ≤ (residualLift B).map
        (MulAut.conj (residualInclusion n)).toMonoidHom := by
    have hh := residualLift_mono h
    rw [← hn,residualLift_conjugate] at hh
    exact hh
  exact ⟨n,hg.imp (transfer _) (fun h => h.imp (transfer _) (transfer _))⟩

/-- The exact three elementary-image alternatives in the native second
centralizer's residual. The same residual element conjugates each whole lift. -/
theorem residual_elementary_three_cases (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXR : X ≤ residualInclusion.range) :
    ∃ n : residual,
      X ≤ (residualLift (m22InnerHexadKernel m22SourceOctad)).map
        (MulAut.conj (residualInclusion n)).toMonoidHom ∨
      X ≤ (residualLift Sextet.innerTranslations).map
        (MulAut.conj (residualInclusion n)).toMonoidHom ∨
      X ≤ (residualLift (smallContainer 0)).map
        (MulAut.conj (residualInclusion n)).toMonoidHom := by
  obtain ⟨g,hg⟩ := residual_elementary_cover X hXR
  rcases hg with h | h | ⟨k,h⟩
  · exact ⟨g,Or.inl h⟩
  · exact ⟨g,Or.inr (Or.inl h)⟩
  · obtain ⟨n,hn⟩ := small_lift_three_cases k
    have transfer (B : Subgroup Model)
        (hB : residualLift (smallContainer k) ≤ B.map
          (MulAut.conj (residualInclusion n)).toMonoidHom) :
        X ≤ B.map (MulAut.conj (residualInclusion (g*n))).toMonoidHom := by
      have hh := h.trans (map_mono (f := (MulAut.conj (residualInclusion g)).toMonoidHom) hB)
      rw [conjugate_comp,← map_mul] at hh
      exact hh
    exact ⟨g*n,hn.imp (transfer _) (fun h => h.imp (transfer _) (transfer _))⟩

/-- Application to every nonpure zero-form elementary subgroup in J4. The
three inverse-image containers and the ambient conjugator are literal; whole
normalizer placement still requires the subsequent Section 2.2 lift geometry. -/
theorem zero_form_nonpure_three_cases (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hzero : intrinsicElementaryForm X = 0)
    (hn : ¬ ∀ x ∈ X, x ≠ 1 → IsConj a x) :
    ∃ g : Model,
      X ≤ (residualLift (m22InnerHexadKernel m22SourceOctad)).map
        (MulAut.conj g).toMonoidHom ∨
      X ≤ (residualLift Sextet.innerTranslations).map (MulAut.conj g).toMonoidHom ∨
      X ≤ (residualLift (smallContainer 0)).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g,hg⟩ := zero_form_nonpure_cover X hzero hn
  rcases hg with h | h | ⟨k,h⟩
  · exact ⟨g,Or.inl h⟩
  · exact ⟨g,Or.inr (Or.inl h)⟩
  · obtain ⟨n,hn⟩ := small_lift_three_cases k
    have transfer (B : Subgroup Model)
        (hB : residualLift (smallContainer k) ≤ B.map
          (MulAut.conj (residualInclusion n)).toMonoidHom) :
        X ≤ B.map (MulAut.conj (g*residualInclusion n)).toMonoidHom := by
      have hh := h.trans (map_mono (f := (MulAut.conj g).toMonoidHom) hB)
      rwa [conjugate_comp] at hh
    exact ⟨g*residualInclusion n,hn.imp (transfer _) (fun h => h.imp (transfer _) (transfer _))⟩

end Janko4.LocalStructure.ElementaryNormalizerCover.M22Images
