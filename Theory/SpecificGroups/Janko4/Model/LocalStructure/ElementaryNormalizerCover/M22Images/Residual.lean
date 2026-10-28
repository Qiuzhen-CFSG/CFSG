module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.Native
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.FormReduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.MathieuCase

/-!
# Literal M22 image placement in the J4 inner half

The full second-involution centralizer maps onto Aut(M22). Restricting to its
solvable residual and identifying inner automorphisms with native M22 gives a
surjective quotient map. Its kernel maps to the original embedded E2048,
and its action equation retains the original full-centralizer marking.

Every elementary subgroup in this residual has image in one of the six checked
native M22 containers. Lifting both the containers and their conjugators through
the same quotient gives actual ambient J4 containment. Zero intrinsic form and
a second-class member discharge the residual-placement premise. In the trivial
image case the existing Mathieu normalizer argument applies, including its
literal radical normalizer restriction and full local core identities.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Lemma 2.2.1
and the opening of Proposition 2.2.2, pp.489--490. The E8 normalizer recognition,
the nontrivial lifted-image configurations and the full elementary-normalizer
cover still require their source geometry. Subgroup placement here does not
assert placement of the whole normalizer in any one of these inverse images.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.M22Images
open Janko4.InvolutionCentralizers.Second LargeCenterRadicals.OuterHalf M22ChapterH
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- The intrinsic solvable residual of the FULL native second centralizer. -/
abbrev residual := solvableResidual ambientCentralizer

private def innerEquiv : M22 ≃* MulAut.innerSubgroup M22 :=
  MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot m22_center_eq_bot)

private def innerProjection : residual →* MulAut.innerSubgroup M22 :=
  (ambientExtension.rightHom.comp residual.subtype).codRestrict _ (fun x => by
    have h := x.property
    change x.val ∈ solvableResidual ambientCentralizer at h
    rw [← second_innerHalf_eq_residual] at h
    exact h)

/-- The M22 quotient map of the actual inner half. -/
def residualProjection : residual →* M22 :=
  innerEquiv.symm.toMonoidHom.comp innerProjection

/-- This quotient marking induces exactly the original full-centralizer action. -/
theorem residualProjection_action (x : residual) :
    MulAut.conj (residualProjection x) = ambientExtension.rightHom x.val := by
  exact congrArg Subtype.val (innerEquiv.apply_symm_apply (innerProjection x))

theorem residualProjection_surjective : Function.Surjective residualProjection := by
  intro g
  obtain ⟨x,hx⟩ := ambientExtension.rightHom_surjective (MulAut.conj g)
  have hr : x ∈ residual := by
    change x ∈ solvableResidual ambientCentralizer
    rw [← second_innerHalf_eq_residual]
    change ambientExtension.rightHom x ∈ MulAut.innerSubgroup M22
    rw [hx]
    exact ⟨g,rfl⟩
  refine ⟨⟨x,hr⟩,?_⟩
  apply MulAut.conj_injective_of_center_eq_bot m22_center_eq_bot
  exact (residualProjection_action _).trans hx

theorem residualProjection_ker :
    residualProjection.ker = ambientKernel.subgroupOf residual := by
  ext x
  change residualProjection x = 1 ↔ ambientExtension.rightHom x.val = 1
  rw [← residualProjection_action]
  exact ⟨fun h => by rw [h,map_one], fun h =>
    (MulAut.conj_injective_of_center_eq_bot m22_center_eq_bot) (h.trans (map_one _).symm)⟩

/-- The literal residual inclusion into the ambient J4 matrix group. -/
@[expose] def residualInclusion : residual →* Model :=
  ambientCentralizer.subtype.comp residual.subtype

theorem residualInclusion_injective : Function.Injective residualInclusion :=
  ambientCentralizer.subtype_injective.comp residual.subtype_injective

/-- The kernel of the inner quotient is the very same ambient Mathieu E. -/
theorem residualProjection_kernel_image : residualProjection.ker.map residualInclusion =
    embeddedKernel := by
  have hk : ambientKernel ≤ residual := by
    intro x hx
    change x ∈ solvableResidual ambientCentralizer
    rw [← second_innerHalf_eq_residual]
    change ambientExtension.rightHom x ∈ MulAut.innerSubgroup M22
    rw [show ambientExtension.rightHom x = 1 from hx]
    exact one_mem _
  rw [residualProjection_ker,residualInclusion,← map_map,map_subgroupOf_eq_of_le hk,
    ambientKernel_eq_map,map_map]
  have he : ambientCentralizer.subtype.comp ambientEquivLocal.symm.toMonoidHom =
      max1.subtype.comp localCentralizer.subtype := by
    ext x
    exact ambientEquivLocal_symm_val x
  rw [he,← map_map]
  change ((max1Kernel.subgroupOf localCentralizer).map localCentralizer.subtype).map
    max1.subtype = embeddedKernel
  rw [map_subgroupOf_eq_of_le max1Kernel_le_localCentralizer]

/-- The actual embedded inverse image of an M22 subgroup. -/
@[expose] def residualLift (B : Subgroup M22) : Subgroup Model :=
  (B.comap residualProjection).map residualInclusion

/-- Every elementary subgroup in the actual inner half lies in a conjugate
of one of the explicit M22 inverse images. The conjugator itself is lifted
through the same residual quotient map. -/
theorem residual_elementary_cover (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXR : X ≤ residualInclusion.range) :
    ∃ n : residual,
      X ≤ (residualLift (m22InnerHexadKernel m22SourceOctad)).map
        (MulAut.conj (residualInclusion n)).toMonoidHom ∨
      X ≤ (residualLift Sextet.innerTranslations).map
        (MulAut.conj (residualInclusion n)).toMonoidHom ∨
      ∃ k : Fin 4, X ≤ (residualLift (smallContainer k)).map
        (MulAut.conj (residualInclusion n)).toMonoidHom := by
  let Xr := X.comap residualInclusion
  let : IsElementaryAbelian 2 Xr := IsElementaryAbelian.comap_of_injective
    residualInclusion residualInclusion_injective X
  let A := Xr.map residualProjection
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  obtain ⟨g,hg⟩ := elementary_native_cover A
  obtain ⟨n,hn⟩ := residualProjection_surjective g
  have transfer (B : Subgroup M22) (hAB : A ≤ B.map (MulAut.conj g).toMonoidHom) :
      X ≤ (residualLift B).map (MulAut.conj (residualInclusion n)).toMonoidHom := by
    intro x hx
    obtain ⟨r,hr⟩ := hXR hx
    have hpr := hAB (mem_map_of_mem residualProjection (show r ∈ Xr from (show residualInclusion r ∈ X from hr.symm ▸ hx)))
    obtain ⟨b,hb,he⟩ := hpr
    have hback : residualProjection (n⁻¹ * r * n) = b := by
      rw [map_mul,map_mul,map_inv,hn,← he]
      simp [mul_assoc]
    refine ⟨residualInclusion (n⁻¹*r*n),?_,?_⟩
    · exact mem_map_of_mem residualInclusion (show n⁻¹*r*n ∈ B.comap residualProjection from
        (show residualProjection (n⁻¹*r*n) ∈ B from hback.symm ▸ hb))
    · simp [map_mul,map_inv,mul_assoc,hr]
  refine ⟨n,?_⟩
  rcases hg with h | h | ⟨k,h⟩
  · exact Or.inl (transfer _ h)
  · exact Or.inr (Or.inl (transfer _ h))
  · exact Or.inr (Or.inr ⟨k,transfer _ h⟩)

/-- The KW zero-form consumer: orthogonality to the actual second-class seed
places X in the literal M22 inner half and discharges the residual premise. -/
theorem zero_form_seed_cover (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hzero : intrinsicElementaryForm X = 0) (hseed : (seed : Model) ∈ X) :
    ∃ n : residual,
      X ≤ (residualLift (m22InnerHexadKernel m22SourceOctad)).map
        (MulAut.conj (residualInclusion n)).toMonoidHom ∨
      X ≤ (residualLift Sextet.innerTranslations).map
        (MulAut.conj (residualInclusion n)).toMonoidHom ∨
      ∃ k : Fin 4, X ≤ (residualLift (smallContainer k)).map
        (MulAut.conj (residualInclusion n)).toMonoidHom := by
  apply residual_elementary_cover X
  have hseed1 : (seed : Model) ≠ 1 := by
    intro h
    have ho := seed_order
    simp [h] at ho
  have h := zero_form_le_involution_residual X hzero _ hseed hseed1
  change X ≤ (ambientCentralizer.subtype.comp residual.subtype).range
  rw [MonoidHom.range_comp,range_subtype]
  exact h

/-- A trivial image under the original inner quotient puts X in the native E,
with no replacement of the denominator by a chosen subgroup. -/
theorem le_embeddedKernel_of_residual_image_bot (X : Subgroup Model)
    (hXR : X ≤ residualInclusion.range)
    (himage : (X.comap residualInclusion).map residualProjection = ⊥) :
    X ≤ embeddedKernel := by
  intro x hx
  obtain ⟨r,hr⟩ := hXR hx
  have hk : r ∈ residualProjection.ker := (Subgroup.map_eq_bot_iff _).mp himage
    (show residualInclusion r ∈ X from hr.symm ▸ hx)
  rw [← residualProjection_kernel_image]
  exact ⟨r,hk,hr⟩

/-- The literal radical consumer of the trivial M22-image branch. -/
theorem radical_local_of_residual_image_bot
    (P X : Subgroup Model) (hP : P.IsPRadical 2)
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model))
    (hXR : X ≤ residualInclusion.range) (hseed : (seed : Model) ∈ X)
    (himage : (X.comap residualInclusion).map residualProjection = ⊥) :
    normalizer (P : Set Model) ≤ max1 ∧ P ≤ max1 ∧
      (normalizer (P.subgroupOf max1 : Set max1)).map max1.subtype =
        normalizer (P : Set Model) ∧
      (P.subgroupOf max1).IsPRadical 2 ∧
      (normalizer (P.subgroupOf max1 : Set max1)).pCoreIn 2 = P.subgroupOf max1 ∧
      ((normalizer (P.subgroupOf max1 : Set max1)).pCoreIn 2).map max1.subtype = P := by
  exact radical_mathieu_local_of_nonfirst_kernel_involution P X hP hNX
    (le_embeddedKernel_of_residual_image_bot X hXR himage) _ hseed seed_order
    Cardinality.LocalInvolutionCensus.not_isConj_z_t

/-- Conjugation moves the zero-form reduction to any actual second-class
member of X, retaining a single ambient conjugator on the lifted containers. -/
theorem zero_form_second_cover (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hzero : intrinsicElementaryForm X = 0) (t : Model) (ht : t ∈ X)
    (hclass : IsConj (seed : Model) t) :
    ∃ g : Model,
      X ≤ (residualLift (m22InnerHexadKernel m22SourceOctad)).map
        (MulAut.conj g).toMonoidHom ∨
      X ≤ (residualLift Sextet.innerTranslations).map (MulAut.conj g).toMonoidHom ∨
      ∃ k : Fin 4, X ≤ (residualLift (smallContainer k)).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g,hg⟩ := isConj_iff.mp hclass
  let e := MulAut.conj g⁻¹
  let Y := X.map e.toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  have hs : (seed : Model) ∈ Y := by
    refine ⟨t,ht,?_⟩
    rw [← hg]
    simp [e,mul_assoc]
  have hy : intrinsicElementaryForm Y = 0 := by
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    obtain ⟨x,hx,hxu⟩ := u.toMul.property
    obtain ⟨y,hy,hyv⟩ := v.toMul.property
    change outerValue u.toMul v.toMul = 0
    rw [← hxu,← hyv]
    change outerValue (e x) (e y) = 0
    rw [outerValue_equiv]
    exact congrArg (fun B : LinearMap.BilinForm (ZMod 2) (Additive X) =>
      B (Additive.ofMul ⟨x,hx⟩) (Additive.ofMul ⟨y,hy⟩)) hzero
  obtain ⟨n,hn⟩ := zero_form_seed_cover Y hy hs
  have transfer (B : Subgroup Model)
      (h : Y ≤ B.map (MulAut.conj (residualInclusion n)).toMonoidHom) :
      X ≤ B.map (MulAut.conj (g * residualInclusion n)).toMonoidHom := by
    intro x hx
    obtain ⟨y,hy,he⟩ := h (mem_map_of_mem e.toMonoidHom hx)
    refine ⟨y,hy,?_⟩
    have hh := congrArg (MulAut.conj g) he
    simpa [e,MulAut.conj_apply,mul_assoc] using hh
  refine ⟨g * residualInclusion n,?_⟩
  rcases hn with h | h | ⟨k,h⟩
  · exact Or.inl (transfer _ h)
  · exact Or.inr (Or.inl (transfer _ h))
  · exact Or.inr (Or.inr ⟨k,transfer _ h⟩)

private theorem seed_standard_class : IsConj (seed : Model) ((a * b * a * b * b)^5) := by
  obtain ⟨g,hg⟩ := Simplicity.Max1Fusion.seed_fuses_second matrixA_mul_self matrixB_pow_four
  have ha : Simplicity.a matrixA_mul_self = a := by apply toMatrix_injective; rfl
  have hb : Simplicity.b matrixB_pow_four = b := by apply toMatrix_injective; rfl
  rw [ha,hb] at hg
  have hw : Simplicity.word a b "ababb" = a*b*a*b*b := by simp [Simplicity.word,mul_assoc]
  rw [hw] at hg
  exact isConj_iff.mpr ⟨g,hg.symm⟩

/-- The mixed zero-form branch of `maximal_twoLocal_source_cases` now has
exhaustive native quotient-image placement with all marker premises discharged.
This is containment of X; it does not assert containment of its normalizer. -/
theorem zero_form_nonpure_cover (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hzero : intrinsicElementaryForm X = 0)
    (hn : ¬ ∀ x ∈ X, x ≠ 1 → IsConj a x) :
    ∃ g : Model,
      X ≤ (residualLift (m22InnerHexadKernel m22SourceOctad)).map
        (MulAut.conj g).toMonoidHom ∨
      X ≤ (residualLift Sextet.innerTranslations).map (MulAut.conj g).toMonoidHom ∨
      ∃ k : Fin 4, X ≤ (residualLift (smallContainer k)).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨t,ht,_,_,hc⟩ := nonpure_contains_second X hn
  exact zero_form_second_cover X hzero t ht (seed_standard_class.trans hc)

end Janko4.LocalStructure.ElementaryNormalizerCover.M22Images
