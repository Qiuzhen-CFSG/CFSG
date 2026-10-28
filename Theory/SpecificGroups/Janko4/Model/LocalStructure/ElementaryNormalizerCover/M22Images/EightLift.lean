module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.EightKernel

/-!
# The exceptional E8 lift through the original residual quotient

The fixed conjugator identifying the native M22 Sylow with the permutation
certificate lifts through the original Mathieu projection. It carries the
original residual image to the checked E8, and the original central seed to
its distinguished fixed pair. The orthogonal kernel calculation therefore
identifies X intersect E with the original seed line and gives order 16.

The hypotheses are the literal residual placement, full E8 quotient image,
seed membership and zero intrinsic form from the source reduction. The
elementary 256 centralizer and strict normalizer enlargement remain separate
source obligations.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Proposition
2.2.2(iv), pp.490--491.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.M22Images
open Cardinality QuotientCount.Image KernelCount M23Geometry FusionCertificate
open LinearFive InvolutionCentralizers.Second LargeCenterRadicals.OuterHalf
open Simplicity.Max1Fusion.KernelOrbits
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel basis pairMover

private theorem alignment_point (c : M23)
    (hc : alignedEmbedding = (MulAut.conj c).toMonoidHom.comp m22InM23) :
    c.val 9 = 0 := by
  have hfixed (i : Fin 8) : pointTable (smallIndex 0 i) (c.val 9) = c.val 9 := by
    have hi : sylowElement (smallIndex 0 i) ∈ (smallContainer 0).map alignedEmbedding := by
      rw [smallContainer_map]
      exact ⟨i,rfl⟩
    obtain ⟨u,_,hu⟩ := hi
    have h9 : (m22InM23 u).val 9 = 9 := (m23EquivM22PointStabilizer u).property
    calc
      pointTable (smallIndex 0 i) (c.val 9) = (alignedEmbedding u).val (c.val 9) :=
        congrArg (fun v : M23 => v.val (c.val 9)) hu.symm
      _ = c.val 9 := by
        rw [hc]
        change c.val ((m22InM23 u).val (c.val.symm (c.val 9))) = c.val 9
        rw [Equiv.symm_apply_apply,h9]
  have huniq : ∀ j : Fin 23,
      pointTable (smallIndex 0 1) j = j → pointTable (smallIndex 0 2) j = j →
      pointTable (smallIndex 0 4) j = j → j = 0 := by decide +kernel
  exact huniq _ (hfixed 1) (hfixed 2) (hfixed 4)

private theorem projection_star (g : M) : projection g = starGroupEquivM24 (starHom g) := by
  change localQuotientEquivM24 matrixA_mul_self matrixB_pow_four (QuotientGroup.mk' _ g) = _
  rw [localQuotientEquivM24_apply]
  rfl

private theorem seed_conjugate (c : M23) (hc : c.val 9 = 0) (s : M)
    (hs : projection s = pointEmbedding c * pairMover) :
    (MulAut.conj (s : Model)) (InvolutionCentralizers.Second.seed : Model) =
      (kernelValue 633 : Model) := by
  have hmark (j : Fin 24) :
      (projection s).val (StarOrderCertificate.relabel j) =
        StarOrderCertificate.relabel ((starHom s).val j) := by
    rw [projection_star,starGroupEquivM24_apply]
    simp
  have h0 : (projection s).val (StarOrderCertificate.relabel 0) = 0 := by
    rw [hs]
    change (pointEmbedding c).val (pairMarking 0) = 0
    rw [pairMarking_zero]
    exact pointEmbedding_fixed c
  have h1 : (projection s).val (StarOrderCertificate.relabel 1) = 23 := by
    rw [hs]
    change (pointEmbedding c).val (pairMarking 1) = 23
    rw [pairMarking_one]
    have he := pointEmbedding_apply c (9 : Fin 23)
    rw [hc] at he
    rw [show m23PointEmbedding (9 : Fin 23) = (9 : Fin 24) by
        rw [m23PointEmbedding_apply]; rfl,
      show m23PointEmbedding (0 : Fin 23) = (23 : Fin 24) by
        rw [m23PointEmbedding_apply]; rfl] at he
    exact he
  have hs0 : (starHom s).val 0 = 13 :=
    StarOrderCertificate.relabel.injective ((hmark 0).symm.trans h0)
  have hs1 : (starHom s).val 1 = 5 :=
    StarOrderCertificate.relabel.injective ((hmark 1).symm.trans h1)
  have he : s * kernelValue (pairLabel 0 1) * s⁻¹ =
      kernelValue (pairLabel ((starHom s).val 0) ((starHom s).val 1)) :=
    congrArg Subtype.val (starHom_pair s 0 1)
  rw [hs0,hs1] at he
  change s * kernelValue 1 * s⁻¹ = kernelValue 633 at he
  have hseed : kernelValue 1 = InvolutionCentralizers.Second.seed :=
    maskValue_one matrixA_mul_self matrixB_pow_four
  rw [hseed] at he
  exact congrArg (fun z : M => (z : Model)) he

private def alignedLocalMap (s : M) : residual →* M :=
  (MulAut.conj s).toMonoidHom.comp residualToMathieu

private theorem alignedLocalMap_ambient (s : M) :
    M.subtype.comp (alignedLocalMap s) =
      (MulAut.conj (s : Model)).toMonoidHom.comp residualInclusion := by
  ext r
  change (s : Model) * (residualToMathieu r : Model) * (s : Model)⁻¹ = _
  rw [residualToMathieu_val]
  rfl

private theorem alignedLocalMap_projection (c : M23)
    (hc : alignedEmbedding = (MulAut.conj c).toMonoidHom.comp m22InM23)
    (s : M) (hs : projection s = pointEmbedding c * pairMover) :
    projection.comp (alignedLocalMap s) =
      pointEmbedding.comp (alignedEmbedding.comp residualProjection) := by
  apply MonoidHom.ext
  intro r
  change projection (s * residualToMathieu r * s⁻¹) =
    pointEmbedding (alignedEmbedding (residualProjection r))
  rw [map_mul,map_mul,map_inv,hs,hc]
  change (pointEmbedding c * pairMover) * projection (residualToMathieu r) *
    (pointEmbedding c * pairMover)⁻¹ =
      pointEmbedding (c * m22InM23 (residualProjection r) * c⁻¹)
  rw [map_mul,map_mul,map_inv]
  change (pointEmbedding c * pairMover) * projection (residualToMathieu r) *
    (pointEmbedding c * pairMover)⁻¹ =
      pointEmbedding c * m22Embedding (residualProjection r) * (pointEmbedding c)⁻¹
  rw [residualProjection_mathieu]
  simp only [mul_inv_rev,mul_assoc]

/-- The exceptional source lift has precisely the original central seed as
its kernel intersection. The actual M22 and Mathieu quotient markings are
used to discharge the finite model's positioning assumptions. -/
theorem residual_eight_kernel_intersection (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXR : X ≤ residualInclusion.range)
    (himage : (X.comap residualInclusion).map residualProjection = smallContainer 0)
    (hzero : intrinsicElementaryForm X = 0)
    (hseed : (InvolutionCentralizers.Second.seed : Model) ∈ X) :
    X ⊓ embeddedKernel = zpowers (InvolutionCentralizers.Second.seed : Model) := by
  obtain ⟨c,hc⟩ := alignedEmbedding_conjugator
  obtain ⟨s,hs⟩ := MathieuHallActors.projection_surjective (pointEmbedding c * pairMover)
  let Xr := X.comap residualInclusion
  let Y0 := Xr.map (alignedLocalMap s)
  let Y := Y0.map M.subtype
  have hXr : Xr.map residualInclusion = X := by
    rw [map_comap_eq,inf_eq_right.mpr hXR]
  have hY : X.map (MulAut.conj (s : Model)).toMonoidHom = Y := by
    change _ = (Xr.map (alignedLocalMap s)).map M.subtype
    rw [map_map,alignedLocalMap_ambient,← map_map,hXr]
  let : IsElementaryAbelian 2 Y := hY ▸ IsElementaryAbelian.map (MulAut.conj (s : Model)).toMonoidHom
  have hY0 : Y.subgroupOf M = Y0 := comap_map_eq_self_of_injective M.subtype_injective Y0
  have hYi : (Y.subgroupOf M).map projection = EightKernel.imageGroup := by
    rw [hY0]
    change (Xr.map (alignedLocalMap s)).map projection = _
    rw [map_map,alignedLocalMap_projection c hc s hs,← map_map,← map_map,himage,
      smallContainer_map]
    rfl
  have hYs := seed_conjugate c (alignment_point c hc) s hs
  have hYseed : (kernelValue 633 : Model) ∈ Y := by
    rw [← hY,← hYs]
    exact mem_map_of_mem _ hseed
  have hYzero := intrinsicForm_zero_map X Y (MulAut.conj (s : Model)) hY hzero
  have hk := EightKernel.kernel_intersection_eq Y hYi hYzero hYseed
  have hE : embeddedKernel.map (MulAut.conj (s : Model)).toMonoidHom = embeddedKernel := by
    apply mem_normalizer_iff_map_conj_eq.mp
    rw [embedded_localKernel_normalizer_eq_max1]
    exact s.property
  have hm : (X ⊓ embeddedKernel).map (MulAut.conj (s : Model)).toMonoidHom =
      (zpowers (InvolutionCentralizers.Second.seed : Model)).map
        (MulAut.conj (s : Model)).toMonoidHom := by
    rw [map_inf _ _ _ (MulAut.conj (s : Model)).injective,hY,hE,MonoidHom.map_zpowers]
    change Y ⊓ embeddedKernel = zpowers ((MulAut.conj (s : Model)) (InvolutionCentralizers.Second.seed : Model))
    rw [hYs]
    exact hk
  exact map_injective (f := (MulAut.conj (s : Model)).toMonoidHom)
    (MulAut.conj (s : Model)).injective hm

/-- Cardinality through the original residual quotient, retaining its full
E kernel and the actual ambient subgroup intersection. -/
theorem residual_image_card (X : Subgroup Model) (hXR : X ≤ residualInclusion.range) :
    Nat.card X = Nat.card ((X.comap residualInclusion).map residualProjection) *
      Nat.card (X ⊓ embeddedKernel : Subgroup Model) := by
  let Xr := X.comap residualInclusion
  have hXr : Xr.map residualInclusion = X := by
    rw [map_comap_eq,inf_eq_right.mpr hXR]
  have hcard : Nat.card Xr = Nat.card X := by
    rw [← hXr,card_map_of_injective residualInclusion_injective]
  have hker : Nat.card (residualProjection.ker.subgroupOf Xr) =
      Nat.card (X ⊓ embeddedKernel : Subgroup Model) := by
    rw [← card_map_of_injective Xr.subtype_injective,subgroupOf_map_subtype,
      ← card_map_of_injective residualInclusion_injective,
      map_inf _ _ _ residualInclusion_injective,residualProjection_kernel_image,hXr,inf_comm]
  have hi : (residualProjection.ker.subgroupOf Xr).index = Nat.card (Xr.map residualProjection) :=
    relIndex_ker Xr residualProjection
  have h := (residualProjection.ker.subgroupOf Xr).card_mul_index
  rw [hi,hker,hcard] at h
  exact h.symm.trans (Nat.mul_comm _ _)

/-- The exceptional E8 source image lifts to an elementary group of order
16, with the original seed line as its full kernel. -/
theorem residual_eight_card (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXR : X ≤ residualInclusion.range)
    (himage : (X.comap residualInclusion).map residualProjection = smallContainer 0)
    (hzero : intrinsicElementaryForm X = 0)
    (hseed : (InvolutionCentralizers.Second.seed : Model) ∈ X) : Nat.card X = 16 := by
  rw [residual_image_card X hXR,himage,smallContainer_card,
    residual_eight_kernel_intersection X hXR himage hzero hseed,Nat.card_zpowers,seed_order]


private theorem residual_conjugate_image (X : Subgroup Model) (hXR : X ≤ residualInclusion.range)
    (n : residual) :
    ((X.map (MulAut.conj (residualInclusion n)).toMonoidHom).comap residualInclusion).map
        residualProjection =
      ((X.comap residualInclusion).map residualProjection).map
        (MulAut.conj (residualProjection n)).toMonoidHom := by
  let Xr := X.comap residualInclusion
  have hXr : Xr.map residualInclusion = X := by
    rw [map_comap_eq,inf_eq_right.mpr hXR]
  have commute_map (f : residual →* Model) :
      f.comp (MulAut.conj n).toMonoidHom = (MulAut.conj (f n)).toMonoidHom.comp f := by
    ext r
    simp [map_mul,map_inv]
  have hcomap : (X.map (MulAut.conj (residualInclusion n)).toMonoidHom).comap residualInclusion =
      Xr.map (MulAut.conj n).toMonoidHom := by
    rw [← hXr,map_map,← commute_map,← map_map,
      comap_map_eq_self_of_injective residualInclusion_injective]
  rw [hcomap,map_map,map_map]
  congr 1
  ext r
  simp [map_mul,map_inv]

/-- The exceptional image can be aligned in the original Mathieu local,
with the actual central seed carried to the distinguished fixed pair. -/
theorem residual_eight_alignment (X : Subgroup Model)
    (hXR : X ≤ residualInclusion.range)
    (himage : (X.comap residualInclusion).map residualProjection = smallContainer 0) :
    ∃ s : M,
      ((X.map (MulAut.conj (s : Model)).toMonoidHom).subgroupOf M).map projection =
        EightKernel.imageGroup ∧
      (MulAut.conj (s : Model)) (InvolutionCentralizers.Second.seed : Model) =
        (kernelValue 633 : Model) := by
  obtain ⟨c,hc⟩ := alignedEmbedding_conjugator
  obtain ⟨s,hs⟩ := MathieuHallActors.projection_surjective (pointEmbedding c * pairMover)
  let Xr := X.comap residualInclusion
  let Y0 := Xr.map (alignedLocalMap s)
  have hXr : Xr.map residualInclusion = X := by
    rw [map_comap_eq,inf_eq_right.mpr hXR]
  have hY : X.map (MulAut.conj (s : Model)).toMonoidHom = Y0.map M.subtype := by
    change _ = (Xr.map (alignedLocalMap s)).map M.subtype
    rw [map_map,alignedLocalMap_ambient,← map_map,hXr]
  refine ⟨s,?_,seed_conjugate c (alignment_point c hc) s hs⟩
  rw [hY]
  change ((Y0.map M.subtype).comap M.subtype).map projection = _
  rw [comap_map_eq_self_of_injective M.subtype_injective]
  change (Xr.map (alignedLocalMap s)).map projection = _
  rw [map_map,alignedLocalMap_projection c hc s hs,← map_map,← map_map,himage,
    smallContainer_map]
  rfl

/-- Alignment retains every conjugator in the actual residual and fixes the
original seed before applying the Mathieu coordinate change. -/
theorem residual_eight_conjugate_alignment (X : Subgroup Model)
    (hXR : X ≤ residualInclusion.range) (n : residual)
    (himage : (X.comap residualInclusion).map residualProjection =
      (smallContainer 0).map (MulAut.conj (residualProjection n)).toMonoidHom) :
    ∃ s : M,
      ((X.map (MulAut.conj (s : Model)).toMonoidHom).subgroupOf M).map projection =
        EightKernel.imageGroup ∧
      (MulAut.conj (s : Model)) (InvolutionCentralizers.Second.seed : Model) =
        (kernelValue 633 : Model) := by
  let e := MulAut.conj (residualInclusion n⁻¹)
  let Y := X.map e.toMonoidHom
  have hYR : Y ≤ residualInclusion.range := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨r,rfl⟩ := hXR hx
    exact ⟨n⁻¹*r*n,by simp [e,map_mul,map_inv,mul_assoc]⟩
  have hYi : (Y.comap residualInclusion).map residualProjection = smallContainer 0 := by
    rw [residual_conjugate_image X hXR n⁻¹,himage,map_map]
    have he : (MulAut.conj (residualProjection n⁻¹)).toMonoidHom.comp
        (MulAut.conj (residualProjection n)).toMonoidHom = MonoidHom.id M22 := by
      ext x
      simp [map_inv,mul_assoc]
    rw [he,map_id]
  have hcomm : Commute (InvolutionCentralizers.Second.seed : Model) (residualInclusion n) :=
    (mem_centralizer_singleton_iff.mp n.val.property).symm
  have hfix : e (InvolutionCentralizers.Second.seed : Model) =
      (InvolutionCentralizers.Second.seed : Model) := by
    change residualInclusion n⁻¹ * (InvolutionCentralizers.Second.seed : Model) *
      (residualInclusion n⁻¹)⁻¹ = _
    rw [map_inv,inv_inv,mul_assoc,hcomm.eq,inv_mul_cancel_left]
  obtain ⟨s,hsi,hss⟩ := residual_eight_alignment Y hYR hYi
  let t : M := s * residualToMathieu n⁻¹
  have ht : (MulAut.conj (t : Model)).toMonoidHom =
      (MulAut.conj (s : Model)).toMonoidHom.comp e.toMonoidHom := by
    ext x
    change ((s : Model) * (residualToMathieu n⁻¹ : Model)) * x *
      ((s : Model) * (residualToMathieu n⁻¹ : Model))⁻¹ = _
    rw [residualToMathieu_val]
    simp [e,mul_assoc]
  refine ⟨t,?_,?_⟩
  · rw [ht,← map_map]
    exact hsi
  · change (MulAut.conj (t : Model)).toMonoidHom _ = _
    rw [ht,MonoidHom.comp_apply]
    change (MulAut.conj (s : Model)) (e (InvolutionCentralizers.Second.seed : Model)) = _
    rw [hfix]
    exact hss

/-- Conjugating the exceptional image within the original residual changes
neither the seed line nor the order-sixteen conclusion. -/
theorem residual_eight_conjugate_card (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXR : X ≤ residualInclusion.range) (n : residual)
    (himage : (X.comap residualInclusion).map residualProjection =
      (smallContainer 0).map (MulAut.conj (residualProjection n)).toMonoidHom)
    (hzero : intrinsicElementaryForm X = 0)
    (hseed : (InvolutionCentralizers.Second.seed : Model) ∈ X) : Nat.card X = 16 := by
  let e := MulAut.conj (residualInclusion n⁻¹)
  let Y := X.map e.toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  have hYR : Y ≤ residualInclusion.range := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨r,rfl⟩ := hXR hx
    exact ⟨n⁻¹*r*n,by simp [e,map_mul,map_inv,mul_assoc]⟩
  have hYi : (Y.comap residualInclusion).map residualProjection = smallContainer 0 := by
    rw [residual_conjugate_image X hXR n⁻¹,himage,map_map]
    have he : (MulAut.conj (residualProjection n⁻¹)).toMonoidHom.comp
        (MulAut.conj (residualProjection n)).toMonoidHom = MonoidHom.id M22 := by
      ext x
      simp [map_inv,mul_assoc]
    rw [he,map_id]
  have hcomm : Commute (InvolutionCentralizers.Second.seed : Model) (residualInclusion n) := by
    exact (mem_centralizer_singleton_iff.mp n.val.property).symm
  have hfix : e (InvolutionCentralizers.Second.seed : Model) =
      (InvolutionCentralizers.Second.seed : Model) := by
    change residualInclusion n⁻¹ * (InvolutionCentralizers.Second.seed : Model) *
      (residualInclusion n⁻¹)⁻¹ = _
    rw [map_inv,inv_inv,mul_assoc,hcomm.eq,inv_mul_cancel_left]
  have hsY : (InvolutionCentralizers.Second.seed : Model) ∈ Y :=
    hfix ▸ mem_map_of_mem e.toMonoidHom hseed
  have hzY := intrinsicForm_zero_map X Y e rfl hzero
  have hc := residual_eight_card Y hYR hYi hzY hsY
  rw [card_map_of_injective e.injective] at hc
  exact hc

/-- The seed line is also unchanged for every residual conjugate of the
exceptional image. Thus the literal source kernel-intersection clause is
retained along with the order-sixteen conclusion. -/
theorem residual_eight_conjugate_kernel_intersection
    (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXR : X ≤ residualInclusion.range) (n : residual)
    (himage : (X.comap residualInclusion).map residualProjection =
      (smallContainer 0).map (MulAut.conj (residualProjection n)).toMonoidHom)
    (hzero : intrinsicElementaryForm X = 0)
    (hseed : (InvolutionCentralizers.Second.seed : Model) ∈ X) :
    X ⊓ embeddedKernel = zpowers (InvolutionCentralizers.Second.seed : Model) := by
  have hcard := residual_eight_conjugate_card X hXR n himage hzero hseed
  have hm := residual_image_card X hXR
  rw [hcard,himage,card_map_of_injective (MulAut.conj (residualProjection n)).injective,
    smallContainer_card] at hm
  have hkcard : Nat.card (X ⊓ embeddedKernel : Subgroup Model) = 2 := by omega
  have hsE : (InvolutionCentralizers.Second.seed : Model) ∈ embeddedKernel := by
    have h := kernelValue_mem_E 1
    have hs : kernelValue 1 = InvolutionCentralizers.Second.seed :=
      maskValue_one matrixA_mul_self matrixB_pow_four
    exact hs ▸ h
  have hle : zpowers (InvolutionCentralizers.Second.seed : Model) ≤ X ⊓ embeddedKernel :=
    (zpowers_le).mpr ⟨hseed,hsE⟩
  apply (eq_of_le_of_card_ge hle ?_).symm
  rw [hkcard,Nat.card_zpowers,seed_order]

/-- The exact-image source reduction now leaves only the sextet lift or an
exceptional elementary sixteen after the first M22 lift has been covered. -/
theorem zero_form_seed_normalizer_or_exceptional
    (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hzero : intrinsicElementaryForm X = 0)
    (hseed : (InvolutionCentralizers.Second.seed : Model) ∈ X) :
    (∃ g : Model,
      normalizer (X : Set Model) ≤ LinearFive.M_F.map (MulAut.conj g).toMonoidHom ∨
      normalizer (X : Set Model) ≤ max1.map (MulAut.conj g).toMonoidHom) ∨
    (∃ n : residual, X ≤ (residualLift M22ChapterH.Sextet.innerTranslations).map
      (MulAut.conj (residualInclusion n)).toMonoidHom) ∨
    (Nat.card X = 16 ∧
      X ⊓ embeddedKernel = zpowers (InvolutionCentralizers.Second.seed : Model) ∧
      ∃ n : residual,
      X ≤ (residualLift (smallContainer 0)).map
        (MulAut.conj (residualInclusion n)).toMonoidHom ∧
      (X.comap residualInclusion).map residualProjection =
        (smallContainer 0).map (MulAut.conj (residualProjection n)).toMonoidHom) := by
  obtain ⟨n,h | h | ⟨h,hi⟩⟩ := zero_form_seed_exact_cases X hzero hseed
  · exact Or.inl (hexadLift_normalizer_cover X _ h hzero _ hseed seed_order
      Cardinality.LocalInvolutionCensus.not_isConj_z_t)
  · exact Or.inr (Or.inl ⟨n,h⟩)
  · have hXR : X ≤ residualInclusion.range := by
      have hs1 : (InvolutionCentralizers.Second.seed : Model) ≠ 1 := by
        intro he
        have ho := seed_order
        rw [he,orderOf_one] at ho
        omega
      have hr := zero_form_le_involution_residual X hzero _ hseed hs1
      change X ≤ (ambientCentralizer.subtype.comp residual.subtype).range
      rw [MonoidHom.range_comp,range_subtype]
      exact hr
    exact Or.inr (Or.inr ⟨residual_eight_conjugate_card X hXR n hi hzero hseed,
      residual_eight_conjugate_kernel_intersection X hXR n hi hzero hseed,n,h,hi⟩)

end Janko4.LocalStructure.ElementaryNormalizerCover.M22Images
