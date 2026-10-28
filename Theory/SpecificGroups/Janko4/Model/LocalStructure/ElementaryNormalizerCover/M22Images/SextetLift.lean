module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.SextetImages
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.EightLift
public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.M23

/-!
# The native sextet lift and its remaining small configurations

The source sextet core is transported through its native M23 marking into
the checked E16 translation group. This marking lifts through the original
Mathieu quotient of J4. Its five octad cases give whole-normalizer coverage
by the existing E/F argument. Each remaining image contains a non-octad
four-group, forcing the actual kernel intersection into the explicit E8;
the elementary lift consequently has order at most 128.

The remaining extraspecial-core placement and pure-subgroup normalizer
analysis are not assumed here. Source: Kleidman--Wilson (1988),
Proposition 2.2.2(iii) and the following normalizer argument, pp.490--491.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu MathieuCode
open scoped Pointwise
namespace Janko4.LocalStructure.ElementaryNormalizerCover.M22Images
open Cardinality LinearFive InvolutionCentralizers.Second LargeCenterRadicals.OuterHalf
open M22ChapterH M23Geometry
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel

private theorem conjugate_comp (X : Subgroup Model) (g h : Model) :
    (X.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      X.map (MulAut.conj (g*h)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

private theorem conjugate_one (X : Subgroup Model) :
    X.map (MulAut.conj (1 : Model)).toMonoidHom = X :=
  mem_normalizer_iff_map_conj_eq.mp (normalizer (X : Set Model)).one_mem

private theorem pointwise_conjugate_le (O P : M24LocalGeometry.Octad) (g : M24)
    (hg : g • O.val = P.val) :
    (octadPointwiseKernel O).map (MulAut.conj g).toMonoidHom ≤ octadPointwiseKernel P := by
  rintro _ ⟨u,hu,rfl⟩
  apply (mem_octadPointwiseKernel P _).mpr
  intro i hi
  have hip : i ∈ g • O.val := hg.symm ▸ hi
  obtain ⟨j,hj,rfl⟩ := Finset.mem_smul_finset.mp hip
  have huj := (mem_octadPointwiseKernel O u).mp hu j hj
  change g.val (u.val (g.val.symm (g.val j))) = g.val j
  rw [Equiv.symm_apply_apply]
  exact congrArg g.val huj

/-- Any literal pointwise-octad quotient image gives the existing whole
normalizer E/F cover. No particular octad marking is imposed on X. -/
theorem mathieu_octad_image_normalizer_cover (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXM : X ≤ M) (O : M24LocalGeometry.Octad)
    (himage : (X.subgroupOf M).map projection ≤ octadPointwiseKernel O)
    (hzero : intrinsicElementaryForm X = 0)
    (t : Model) (htX : t ∈ X) (ht2 : orderOf t = 2) (hnt : ¬ IsConj a t) :
    ∃ g : Model,
      normalizer (X : Set Model) ≤ M_F.map (MulAut.conj g).toMonoidHom ∨
      normalizer (X : Set Model) ≤ max1.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨u,hu⟩ := M24LocalGeometry.exists_smul_octad_eq O LinearFive.O
  obtain ⟨s,hs⟩ := MathieuHallActors.projection_surjective u
  have hQ : X.map (MulAut.conj (s : Model)).toMonoidHom ≤ Q := by
    rintro _ ⟨x,hx,rfl⟩
    let v : M := ⟨x,hXM hx⟩
    refine ⟨s*v*s⁻¹,?_,rfl⟩
    change projection (s*v*s⁻¹) ∈ A
    rw [map_mul,map_mul,map_inv,hs]
    exact pointwise_conjugate_le O LinearFive.O u hu
      (mem_map_of_mem _ (himage (mem_map_of_mem projection (show v ∈ X.subgroupOf M from hx))))
  have hback := map_mono (f := (MulAut.conj (s : Model)⁻¹).toMonoidHom) hQ
  rw [conjugate_comp,inv_mul_cancel,conjugate_one] at hback
  exact zero_form_octad_normalizer_cover X _ hback hzero t htX ht2 hnt

/-- The explicit source-marking change from the M22 sextet to the finite E16. -/
def sextetMover : M23 := CommonFour.transport⁻¹ * Quintet.sourceConjugator⁻¹

def sextetEmbedding : M22 →* M23 :=
  (MulAut.conj CommonFour.transport⁻¹).toMonoidHom.comp Quintet.quintetInM23

theorem sextetEmbedding_image : Sextet.innerTranslations.map sextetEmbedding =
    ElementarySylow.candidate 0 := by
  rw [sextetEmbedding,← map_map,Quintet.innerTranslations_eq_core,Quintet.inner_core_image,
    CommonFour.quintet_core_eq,CommonFour.standardCandidate,map_map]
  have he : (MulAut.conj CommonFour.transport⁻¹).toMonoidHom.comp
      (MulAut.conj CommonFour.transport).toMonoidHom = MonoidHom.id M23 := by
    ext x
    simp [mul_assoc]
  rw [he,map_id]

private theorem sextetEmbedding_embedding (x : M22) :
    pointEmbedding (sextetEmbedding x) =
      pointEmbedding sextetMover * m22Embedding x * (pointEmbedding sextetMover)⁻¹ := by
  change pointEmbedding (CommonFour.transport⁻¹ * Quintet.quintetInM23 x *
    (CommonFour.transport⁻¹)⁻¹) = _
  rw [map_mul,map_mul,map_inv,Quintet.quintetInM23_embedding]
  simp only [sextetMover,map_mul,map_inv,Quintet.sourceConjugator_embedding,
    mul_inv_rev,inv_inv,MulAut.conj_inv_apply,mul_assoc]

private def sextetLocalMap (s : M) : residual →* M :=
  (MulAut.conj s).toMonoidHom.comp residualToMathieu

private theorem sextetLocalMap_ambient (s : M) :
    M.subtype.comp (sextetLocalMap s) =
      (MulAut.conj (s : Model)).toMonoidHom.comp residualInclusion := by
  ext r
  change (s : Model) * (residualToMathieu r : Model) * (s : Model)⁻¹ = _
  rw [residualToMathieu_val]
  rfl

private theorem sextetLocalMap_projection (s : M)
    (hs : projection s = pointEmbedding sextetMover * pairMover) :
    projection.comp (sextetLocalMap s) =
      pointEmbedding.comp (sextetEmbedding.comp residualProjection) := by
  apply MonoidHom.ext
  intro r
  change projection (s * residualToMathieu r * s⁻¹) =
    pointEmbedding (sextetEmbedding (residualProjection r))
  rw [map_mul,map_mul,map_inv,hs,sextetEmbedding_embedding,residualProjection_mathieu]
  simp only [mul_inv_rev,mul_assoc]

/-- The original residual inclusion and original quotient map give the actual
Mathieu E16 coordinates after one ambient conjugation. -/
theorem sextetLift_coordinates (X : Subgroup Model)
    (hX : X ≤ residualLift Sextet.innerTranslations) :
    ∃ s : M,
      X.map (MulAut.conj (s : Model)).toMonoidHom ≤ M ∧
      ((X.map (MulAut.conj (s : Model)).toMonoidHom).subgroupOf M).map projection ≤
        SextetKernel.imageGroup := by
  obtain ⟨s,hs⟩ := MathieuHallActors.projection_surjective (pointEmbedding sextetMover * pairMover)
  let Xr := X.comap residualInclusion
  let Y0 := Xr.map (sextetLocalMap s)
  let Y := Y0.map M.subtype
  have hXR : X ≤ residualInclusion.range := hX.trans (map_le_range _ _)
  have hXr : Xr.map residualInclusion = X := by
    rw [map_comap_eq,inf_eq_right.mpr hXR]
  have hY : X.map (MulAut.conj (s : Model)).toMonoidHom = Y := by
    change _ = (Xr.map (sextetLocalMap s)).map M.subtype
    rw [map_map,sextetLocalMap_ambient,← map_map,hXr]
  refine ⟨s,hY ▸ map_subtype_le Y0,?_⟩
  rw [hY,show Y.subgroupOf M = Y0 from comap_map_eq_self_of_injective M.subtype_injective Y0]
  change (Xr.map (sextetLocalMap s)).map projection ≤ _
  rw [map_map,sextetLocalMap_projection s hs,← map_map,← map_map]
  have hXi : Xr.map residualProjection ≤ Sextet.innerTranslations := by
    rintro _ ⟨r,hr,rfl⟩
    obtain ⟨q,hq,hqr⟩ := hX hr
    exact residualInclusion_injective hqr ▸ hq
  have hh := map_mono (f := pointEmbedding) (map_mono (f := sextetEmbedding) hXi)
  rw [sextetEmbedding_image] at hh
  exact hh

/-- In the sextet branch, the octad cases have their whole normalizers
covered. Every remaining lift has the source E8 kernel bound and order at
most 128, with the actual coordinate conjugator retained. -/
theorem sextetLift_normalizer_or_small (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hX : X ≤ residualLift Sextet.innerTranslations)
    (hzero : intrinsicElementaryForm X = 0)
    (hn : ¬ ∀ x ∈ X, x ≠ 1 → IsConj a x) :
    (∃ g : Model,
      normalizer (X : Set Model) ≤ M_F.map (MulAut.conj g).toMonoidHom ∨
      normalizer (X : Set Model) ≤ max1.map (MulAut.conj g).toMonoidHom) ∨
    (Nat.card X ≤ 128 ∧ ∃ (s : M) (k : Fin 30),
      X.map (MulAut.conj (s : Model)).toMonoidHom ≤ M ∧
      (∀ d : Fin 2, SextetKernel.imageElement (SextetKernel.nonOctadPair k d) ∈
        ((X.map (MulAut.conj (s : Model)).toMonoidHom).subgroupOf M).map projection) ∧
      (X ⊓ embeddedKernel).map (MulAut.conj (s : Model)).toMonoidHom ≤ SextetKernel.kernelEight) := by
  obtain ⟨s,hYM,hYi⟩ := sextetLift_coordinates X hX
  let e := MulAut.conj (s : Model)
  let Y := X.map e.toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  have hzY := intrinsicForm_zero_map X Y e rfl hzero
  have hback : Y.map (MulAut.conj (s : Model)⁻¹).toMonoidHom = X := by
    change (X.map (MulAut.conj (s : Model)).toMonoidHom).map
      (MulAut.conj (s : Model)⁻¹).toMonoidHom = X
    rw [conjugate_comp,inv_mul_cancel,conjugate_one]
  rcases SextetImages.subgroup_octad_or_pair ((Y.subgroupOf M).map projection) hYi with
    ⟨i,hi⟩ | ⟨k,hk⟩
  · obtain ⟨t,ht,ht2,hnt,_⟩ := nonpure_contains_second X hn
    have hntY : ¬ IsConj a (e t) := by
      intro h
      exact hnt (h.trans (isConj_iff.mpr ⟨(s : Model)⁻¹,by simp [e,mul_assoc]⟩))
    obtain ⟨g,hg⟩ := mathieu_octad_image_normalizer_cover Y hYM (SextetImages.octad i) hi
      hzY (e t) (mem_map_of_mem _ ht) ((e.orderOf_eq t).trans ht2) hntY
    left
    refine ⟨(s : Model)⁻¹*g,?_⟩
    have transfer (H : Subgroup Model)
        (h : normalizer (Y : Set Model) ≤ H.map (MulAut.conj g).toMonoidHom) :
        normalizer (X : Set Model) ≤ H.map (MulAut.conj ((s : Model)⁻¹*g)).toMonoidHom := by
      have hm := map_mono (f := (MulAut.conj (s : Model)⁻¹).toMonoidHom) h
      rwa [map_equiv_normalizer_eq,hback,conjugate_comp] at hm
    exact hg.imp (transfer _) (transfer _)
  · have hE : embeddedKernel.map e.toMonoidHom = embeddedKernel := by
      apply mem_normalizer_iff_map_conj_eq.mp
      rw [embedded_localKernel_normalizer_eq_max1]
      exact s.property
    have hi : (X ⊓ embeddedKernel).map e.toMonoidHom = Y ⊓ E := by
      rw [map_inf _ _ _ e.injective,hE]
    have hker := SextetKernel.kernel_intersection_le Y k hk hzY
    have hkc : Nat.card (X ⊓ embeddedKernel : Subgroup Model) ≤ 8 := by
      rw [← card_map_of_injective (K := X ⊓ embeddedKernel) (f := e.toMonoidHom) e.injective,hi]
      exact SextetKernel.kernel_intersection_card_le Y k hk hzY
    have hXR : X ≤ residualInclusion.range := hX.trans (map_le_range _ _)
    have hXi : (X.comap residualInclusion).map residualProjection ≤ Sextet.innerTranslations := by
      rintro _ ⟨r,hr,rfl⟩
      obtain ⟨q,hq,hqr⟩ := hX hr
      exact residualInclusion_injective hqr ▸ hq
    have hc : Nat.card ((X.comap residualInclusion).map residualProjection) ≤ 16 := by
      have hh := card_le_of_le hXi
      rwa [Quintet.innerTranslations_eq_core,Quintet.inner_core_card] at hh
    have hcard : Nat.card X ≤ 128 := by
      rw [residual_image_card X hXR]
      exact Nat.mul_le_mul hc hkc
    exact Or.inr ⟨hcard,s,k,hYM,hk,hi ▸ hker⟩

private theorem nonpure_conjugate (X : Subgroup Model) (g : Model)
    (hn : ¬ ∀ x ∈ X, x ≠ 1 → IsConj a x) :
    ¬ ∀ y ∈ X.map (MulAut.conj g).toMonoidHom, y ≠ 1 → IsConj a y := by
  intro hp
  apply hn
  intro x hx hx1
  have hy1 : (MulAut.conj g) x ≠ 1 := fun h => hx1 ((MulAut.conj g).injective
    (h.trans (map_one _).symm))
  exact (hp _ (mem_map_of_mem _ hx) hy1).trans
    (isConj_iff.mpr ⟨g⁻¹,by simp [mul_assoc]⟩)

/-- The sextet dichotomy under an arbitrary ambient conjugator. -/
theorem sextet_conjugate_normalizer_or_card_le (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (g : Model)
    (hX : X ≤ (residualLift Sextet.innerTranslations).map (MulAut.conj g).toMonoidHom)
    (hzero : intrinsicElementaryForm X = 0)
    (hn : ¬ ∀ x ∈ X, x ≠ 1 → IsConj a x) :
    (∃ k : Model,
      normalizer (X : Set Model) ≤ M_F.map (MulAut.conj k).toMonoidHom ∨
      normalizer (X : Set Model) ≤ max1.map (MulAut.conj k).toMonoidHom) ∨ Nat.card X ≤ 128 := by
  let Y := X.map (MulAut.conj g⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  have hY : Y ≤ residualLift Sextet.innerTranslations := by
    have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hX
    rwa [conjugate_comp,inv_mul_cancel,conjugate_one] at hm
  have hzeroY := intrinsicForm_zero_map X Y (MulAut.conj g⁻¹) rfl hzero
  have hnY := nonpure_conjugate X g⁻¹ hn
  have hback : Y.map (MulAut.conj g).toMonoidHom = X := by
    change (X.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = X
    rw [conjugate_comp,mul_inv_cancel,conjugate_one]
  rcases sextetLift_normalizer_or_small Y hY hzeroY hnY with ⟨k,hk⟩ | ⟨hc,_⟩
  · left
    refine ⟨g*k,?_⟩
    have transfer (H : Subgroup Model)
        (h : normalizer (Y : Set Model) ≤ H.map (MulAut.conj k).toMonoidHom) :
        normalizer (X : Set Model) ≤ H.map (MulAut.conj (g*k)).toMonoidHom := by
      have hm := map_mono (f := (MulAut.conj g).toMonoidHom) h
      rwa [map_equiv_normalizer_eq,hback,conjugate_comp] at hm
    exact hk.imp (transfer _) (transfer _)
  · right
    rwa [card_map_of_injective (MulAut.conj g⁻¹).injective] at hc

/-- The full mixed zero-form source image reduction leaves only groups of
order at most 128 outside the established Mathieu and linear-five branches. -/
theorem zero_form_nonpure_normalizer_or_small (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hzero : intrinsicElementaryForm X = 0)
    (hn : ¬ ∀ x ∈ X, x ≠ 1 → IsConj a x) :
    (∃ k : Model,
      normalizer (X : Set Model) ≤ M_F.map (MulAut.conj k).toMonoidHom ∨
      normalizer (X : Set Model) ≤ max1.map (MulAut.conj k).toMonoidHom) ∨ Nat.card X ≤ 128 := by
  obtain ⟨t,ht,_,_,htclass⟩ := nonpure_contains_second X hn
  have hsclass : IsConj (seed : Model) ((a * b * a * b * b)^5) :=
    ((OuterReduction.involution_isConj_of_max1_odd_index
      OuterReduction.max1_odd_index_unconditional seed_order).resolve_left
      Cardinality.LocalInvolutionCensus.not_isConj_z_t).symm
  obtain ⟨g,hg⟩ := isConj_iff.mp (hsclass.trans htclass)
  let Y := X.map (MulAut.conj g⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  have hseed : (seed : Model) ∈ Y := by
    have he : (MulAut.conj g⁻¹) t = (seed : Model) := by
      rw [← hg]
      simp [mul_assoc]
    exact he ▸ mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom ht
  have hzeroY := intrinsicForm_zero_map X Y (MulAut.conj g⁻¹) rfl hzero
  have hnY := nonpure_conjugate X g⁻¹ hn
  have hback : Y.map (MulAut.conj g).toMonoidHom = X := by
    change (X.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = X
    rw [conjugate_comp,mul_inv_cancel,conjugate_one]
  have hy : (∃ k : Model,
      normalizer (Y : Set Model) ≤ M_F.map (MulAut.conj k).toMonoidHom ∨
      normalizer (Y : Set Model) ≤ max1.map (MulAut.conj k).toMonoidHom) ∨ Nat.card Y ≤ 128 := by
    rcases zero_form_seed_normalizer_or_exceptional Y hzeroY hseed with h | ⟨n,hn⟩ | ⟨hc,_⟩
    · exact Or.inl h
    · exact sextet_conjugate_normalizer_or_card_le Y _ hn hzeroY hnY
    · exact Or.inr (by rw [hc]; decide)
  rcases hy with ⟨k,hk⟩ | hc
  · left
    refine ⟨g*k,?_⟩
    have transfer (H : Subgroup Model)
        (h : normalizer (Y : Set Model) ≤ H.map (MulAut.conj k).toMonoidHom) :
        normalizer (X : Set Model) ≤ H.map (MulAut.conj (g*k)).toMonoidHom := by
      have hm := map_mono (f := (MulAut.conj g).toMonoidHom) h
      rwa [map_equiv_normalizer_eq,hback,conjugate_comp] at hm
    exact hk.imp (transfer _) (transfer _)
  · right
    rwa [card_map_of_injective (MulAut.conj g⁻¹).injective] at hc

/-- At maximal-two-local level, the large mixed zero-form branch gives
an actual conjugate equality with one of the two native locals. -/
theorem maximal_twoLocal_of_large_zero_form
    (X H : Subgroup Model) [IsElementaryAbelian 2 X]
    (hzero : intrinsicElementaryForm X = 0)
    (hn : ¬ ∀ x ∈ X, x ≠ 1 → IsConj a x) (hcard : 128 < Nat.card X)
    (hH : IsMaximalTwoLocal H) (hHX : H = normalizer (X : Set Model)) :
    ∃ k : Model, H = M_F.map (MulAut.conj k).toMonoidHom ∨
      H = max1.map (MulAut.conj k).toMonoidHom := by
  obtain ⟨k,h | h⟩ := (zero_form_nonpure_normalizer_or_small X hzero hn).resolve_right
    (not_le_of_gt hcard)
  · exact ⟨k,Or.inl (hH.eq_of_le (nativeF_generated_isTwoLocal.map_equiv (MulAut.conj k))
      (hHX ▸ h))⟩
  · exact ⟨k,Or.inr (hH.eq_of_le (embedded_localKernel_isTwoLocal.map_equiv (MulAut.conj k))
      (hHX ▸ h))⟩

/-- Actual radical restriction in the now-closed large mixed zero-form
branch, retaining both normalizer and embedded core maps. -/
theorem radical_local_of_large_zero_form
    (P X : Subgroup Model) [IsElementaryAbelian 2 X] (hP : P.IsPRadical 2)
    (hzero : intrinsicElementaryForm X = 0)
    (hn : ¬ ∀ x ∈ X, x ≠ 1 → IsConj a x) (hcard : 128 < Nat.card X)
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model)) :
    ∃ (k : Model) (H : Subgroup Model), IsTwoLocal H ∧
      (H = M_F.map (MulAut.conj k).toMonoidHom ∨
        H = max1.map (MulAut.conj k).toMonoidHom) ∧
      normalizer (P : Set Model) ≤ H ∧ P ≤ H ∧
      (normalizer (P.subgroupOf H : Set H)).map H.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf H).IsPRadical 2 ∧
      (normalizer (P.subgroupOf H : Set H)).pCoreIn 2 = P.subgroupOf H ∧
      ((normalizer (P.subgroupOf H : Set H)).pCoreIn 2).map H.subtype = P := by
  obtain ⟨k,hk⟩ := (zero_form_nonpure_normalizer_or_small X hzero hn).resolve_right
    (not_le_of_gt hcard)
  obtain ⟨H,hH,hrow,hNH⟩ : ∃ H : Subgroup Model, IsTwoLocal H ∧
      (H = M_F.map (MulAut.conj k).toMonoidHom ∨
        H = max1.map (MulAut.conj k).toMonoidHom) ∧ normalizer (P : Set Model) ≤ H := by
    rcases hk with h | h
    · exact ⟨_,nativeF_generated_isTwoLocal.map_equiv (MulAut.conj k),Or.inl rfl,hNX.trans h⟩
    · exact ⟨_,embedded_localKernel_isTwoLocal.map_equiv (MulAut.conj k),Or.inr rfl,hNX.trans h⟩
  have hPH := P.le_normalizer.trans hNH
  have hN := hNH.trans H.le_normalizer
  have hcore := hP.normalizer_core_subgroupOf H hPH hN
  refine ⟨k,H,hH,hrow,hNH,hPH,?_,hP.subgroupOf_of_normalizer_normalizes H hPH hN,hcore,?_⟩
  · rw [← subgroupOf_normalizer_eq hPH,map_subgroupOf_eq_of_le hNH]
  · rw [hcore,map_subgroupOf_eq_of_le hPH]

end Janko4.LocalStructure.ElementaryNormalizerCover.M22Images
