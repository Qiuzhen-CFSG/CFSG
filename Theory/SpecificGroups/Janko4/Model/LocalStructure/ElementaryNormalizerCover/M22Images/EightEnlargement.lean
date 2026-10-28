module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.EightLift
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.KernelAction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.CentralizerReduction

/-!
# Strict enlargement of the exceptional zero-form lift

The eight distinguished pair masks belong to Ω₁(Z(C(X))) for every elementary
lift of the exceptional M22 image. Their point stabilizers distinguish the
pairs, so any element of the FULL ambient centralizer fixes each pair mask.
The native kernel involution with mask 1 conjugates every element of X by one
of these central masks. It therefore normalizes C(X) and its central omega.
Its action on a displayed quotient element introduces mask 1059, which the
proved zero-form kernel intersection excludes from X. Thus the enlargement
of the whole normalizer is strict.

The original residual quotient supplies the coordinate alignment and the 2B
seed supplies ambient centralizer placement. The strict result applies to
all residual conjugates, excludes this image at maximal-TWO-local level, and
retains the full normalizer and two-core maps in the arbitrary-radical
restriction. This proves the strict-enlargement obstruction needed in the
source's maximal-two-local argument. The more specific identification
C(X) = 2^8 with nondegenerate intrinsic form remains a separate calculation;
it is not assumed or inferred here.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Proposition
2.2.3, final paragraph, p.491. The finite action retains the imported native
M22 marking and ATLAS kernel coordinates, with their original attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.M22Images.EightEnlargement
open Cardinality QuotientCount.Image KernelCount
open Simplicity.Max1Fusion.KernelOrbits
open LinearFive InvolutionCentralizers.Second LargeCenterRadicals.OuterHalf
open M23Geometry FusionCertificate EightKernel
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel basis

private def starTable : Fin 8 → Fin 24 → Fin 24 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23], ![0, 16, 11, 3, 21, 5, 6, 7, 14, 17, 12, 2, 10, 13, 8, 19, 1, 9, 18, 15, 22, 4, 20, 23], ![0, 16, 12, 18, 21, 5, 23, 7, 8, 15, 11, 10, 2, 13, 14, 9, 1, 19, 3, 17, 20, 4, 22, 6], ![0, 1, 10, 18, 4, 5, 23, 7, 14, 19, 2, 12, 11, 13, 8, 17, 16, 15, 3, 9, 22, 21, 20, 6], ![7, 1, 17, 18, 21, 5, 6, 0, 14, 11, 15, 9, 19, 13, 8, 10, 16, 2, 3, 12, 20, 4, 22, 23], ![7, 16, 9, 18, 4, 5, 6, 0, 8, 2, 19, 17, 15, 13, 14, 12, 1, 11, 3, 10, 22, 21, 20, 23], ![7, 16, 19, 3, 4, 5, 23, 0, 14, 10, 9, 15, 17, 13, 8, 11, 1, 12, 18, 2, 20, 21, 22, 6], ![7, 1, 15, 3, 21, 5, 23, 0, 8, 12, 17, 19, 9, 13, 14, 2, 16, 10, 18, 11, 22, 4, 20, 6]]
private theorem starTable_spec : ∀ (i : Fin 8) (x : Fin 24),
    StarOrderCertificate.relabel.symm
      (M23Geometry.CommonFour.extendPoint (pointTable (smallIndex 0 i))
        (StarOrderCertificate.relabel x)) = starTable i x := by decide +kernel

private def pairPoints : Fin 8 → Fin 24 × Fin 24 :=
  ![(0,7),(1,16),(3,18),(4,21),(5,13),(6,23),(8,14),(20,22)]
private def pairMask : Fin 8 → ℕ := ![79,1059,1388,1557,633,1882,822,256]
private theorem pairMask_spec (i : Fin 8) :
    pairLabel (pairPoints i).1 (pairPoints i).2 = pairMask i := by
  have h : ∀ i : Fin 8, pairLabel (pairPoints i).1 (pairPoints i).2 = pairMask i := by decide +kernel
  exact h i
private theorem star_points (x : M) (i : Fin 8) (hx : projection x = imageElement i)
    (j : Fin 24) : (starHom x).val j = starTable i j := by
  calc
    (starHom x).val j = StarOrderCertificate.relabel.symm
        ((projection x).val (StarOrderCertificate.relabel j)) := by
      rw [KernelAction.projection_star,starGroupEquivM24_apply]
      simp
    _ = StarOrderCertificate.relabel.symm
        (CommonFour.extendPoint (pointTable (smallIndex 0 i))
          (StarOrderCertificate.relabel j)) := by
      rw [hx]
      change StarOrderCertificate.relabel.symm
        ((pointEmbedding (sylowElement (smallIndex 0 i))).val (StarOrderCertificate.relabel j)) = _
      rw [CommonFour.pointEmbedding_apply_all]
      rfl
    _ = starTable i j := starTable_spec i j


private theorem pair_signature : ∀ (i : Fin 8) (j : Fin 24),
    (∀ h : Fin 8, starTable h j = j ↔
      starTable h (pairPoints i).1 = (pairPoints i).1) →
    j = (pairPoints i).1 ∨ j = (pairPoints i).2 := by decide +kernel

private theorem pair_signature_right : ∀ (i h : Fin 8),
    (starTable h (pairPoints i).2 = (pairPoints i).2 ↔
      starTable h (pairPoints i).1 = (pairPoints i).1) := by decide +kernel

private theorem pair_distinct : ∀ i : Fin 8, (pairPoints i).1 ≠ (pairPoints i).2 := by decide +kernel

private theorem pair_label_swap : ∀ i : Fin 8,
    pairLabel (pairPoints i).2 (pairPoints i).1 = pairMask i := by decide +kernel

private theorem pair_mem_omega (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (himage : (X.subgroupOf M).map projection = imageGroup)
    (hCM : centralizer (X : Set Model) ≤ M) (i : Fin 8) :
    (kernelValue (pairMask i) : Model) ∈ omegaCenterIn (centralizer (X : Set Model)) := by
  have hcomm (c : Model) (hc : c ∈ centralizer (X : Set Model)) :
      c * (kernelValue (pairMask i) : Model) = (kernelValue (pairMask i) : Model) * c := by
    let c0 : M := ⟨c,hCM hc⟩
    have hp (h : Fin 8) (j : Fin 24) :
        starTable h ((starHom c0).val j) = (starHom c0).val (starTable h j) := by
      have hh := imageElement_mem h
      rw [← himage] at hh
      obtain ⟨x,hx,hpi⟩ := hh
      have hxc : Commute x c0 := Subtype.ext (hc x hx)
      have hv := congrArg (fun p => p.val j) (hxc.map starHom).eq
      change (starHom x).val ((starHom c0).val j) =
        (starHom c0).val ((starHom x).val j) at hv
      simpa only [star_points x h hpi] using hv
    have hs (j : Fin 24) (h : Fin 8) :
        starTable h ((starHom c0).val j) = (starHom c0).val j ↔ starTable h j = j := by
      rw [hp]
      exact (starHom c0).val.injective.eq_iff
    have ha := pair_signature i ((starHom c0).val (pairPoints i).1)
      (fun h => hs (pairPoints i).1 h)
    have hb := pair_signature i ((starHom c0).val (pairPoints i).2)
      (fun h => (hs (pairPoints i).2 h).trans (pair_signature_right i h))
    have hne := (starHom c0).val.injective.ne (pair_distinct i)
    have hlabel : pairLabel ((starHom c0).val (pairPoints i).1)
        ((starHom c0).val (pairPoints i).2) = pairMask i := by
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact (hne (ha.trans hb.symm)).elim
      · rw [ha,hb,pairMask_spec]
      · rw [ha,hb,pair_label_swap]
      · exact (hne (ha.trans hb.symm)).elim
    have he := congrArg Subtype.val (starHom_pair c0 (pairPoints i).1 (pairPoints i).2)
    rw [pairMask_spec,hlabel] at he
    exact congrArg (fun x : M => (x : Model)) (mul_inv_eq_iff_eq_mul.mp he)
  apply (mem_omegaCenterIn_iff _ _).mpr
  refine ⟨?_,hcomm,?_⟩
  · intro x hx
    exact hcomm x (X.le_centralizer hx)
  · have ho := KernelAction.pair_order (pairPoints i).1 (pairPoints i).2 (pair_distinct i)
    rw [pairMask_spec] at ho
    rw [← ho]
    exact pow_orderOf_eq_one _

private def deltaMask (i : Fin 8) : ℕ :=
  Nat.xor 1 (pairLabel (starTable i 0) (starTable i 1))

private theorem delta_cases : ∀ i : Fin 8, ∃ j : Fin 8,
    deltaMask i = pairMask j ∨ deltaMask i = Nat.xor (pairMask j) 633 := by decide +kernel

private theorem kernel_square (m : ℕ) : kernelValue m * kernelValue m = 1 := by
  rw [← kernelValue_xor]
  change kernelValue (m ^^^ m) = 1
  rw [Nat.xor_self,kernelValue_zero]

private theorem shear_action (x : M) (i : Fin 8) (hx : projection x = imageElement i) :
    kernelValue 1 * x * (kernelValue 1)⁻¹ = kernelValue (deltaMask i) * x := by
  have hm : (kernelValue 1)⁻¹ = kernelValue 1 := inv_eq_of_mul_eq_one_left (kernel_square 1)
  have ha := congrArg Subtype.val (starHom_pair x 0 1)
  rw [star_points x i hx,star_points x i hx] at ha
  change x * kernelValue 1 * x⁻¹ = _ at ha
  have he := congrArg (fun z : M => kernelValue 1 * z * x) ha
  simpa only [hm,deltaMask,kernelValue_xor,mul_assoc,inv_mul_cancel,mul_one] using he

private theorem delta_mem_omega (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (himage : (X.subgroupOf M).map projection = imageGroup)
    (hCM : centralizer (X : Set Model) ≤ M) (i : Fin 8) :
    (kernelValue (deltaMask i) : Model) ∈ omegaCenterIn (centralizer (X : Set Model)) := by
  obtain ⟨j,hj | hj⟩ := delta_cases i
  · rw [hj]
    exact pair_mem_omega X himage hCM j
  · rw [hj,kernelValue_xor]
    exact mul_mem (pair_mem_omega X himage hCM j) (pair_mem_omega X himage hCM 4)

/-- The explicit native kernel involution normalizes the full centralizer of
any elementary lift with this quotient image. -/
theorem shear_mem_centralizer_normalizer (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (himage : (X.subgroupOf M).map projection = imageGroup)
    (hCM : centralizer (X : Set Model) ≤ M) :
    (kernelValue 1 : Model) ∈ normalizer (centralizer (X : Set Model) : Set Model) := by
  let k : Model := kernelValue 1
  let e := MulAut.conj k
  let C := centralizer (X : Set Model)
  let W := omegaCenterIn C
  have hXL : X ≤ M := X.le_centralizer.trans hCM
  have hmap : X.map e.toMonoidHom ≤ W := by
    rintro _ ⟨x,hx,rfl⟩
    let x0 : M := ⟨x,hXL hx⟩
    have hpi : projection x0 ∈ imageGroup := by
      rw [← himage]
      exact mem_map_of_mem _ hx
    obtain ⟨p,⟨i,hi⟩,hpi⟩ := hpi
    have hip : sylowElement (smallIndex 0 i) = p := Subtype.ext hi
    rw [← hip] at hpi
    have hi : projection x0 = imageElement i := hpi.symm
    have he : e x = (kernelValue (deltaMask i) : Model) * x :=
      congrArg (fun y : M => (y : Model)) (shear_action x0 i hi)
    change e x ∈ W
    rw [he]
    exact W.mul_mem (delta_mem_omega X himage hCM i) (elementary_le_centralizer_omegaCenter X hx)
  have hle : C ≤ C.map e.toMonoidHom := by
    have hh := centralizer_le hmap
    rw [centralizer_omegaCenter_centralizer_eq X] at hh
    rw [map_centralizer_equiv]
    exact hh
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact (eq_of_le_of_card_ge hle (by rw [card_map_of_injective e.injective])).symm

/-- The same kernel element moves every zero-form lift with its prescribed seed. -/
theorem shear_not_mem_normalizer (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (himage : (X.subgroupOf M).map projection = imageGroup)
    (hzero : intrinsicElementaryForm X = 0)
    (hseed : (kernelValue 633 : Model) ∈ X) :
    (kernelValue 1 : Model) ∉ normalizer (X : Set Model) := by
  intro hn
  have hh := imageElement_mem 1
  rw [← himage] at hh
  obtain ⟨x,hx,hpi⟩ := hh
  have he : (kernelValue 1 : Model) * (x : Model) * (kernelValue 1 : Model)⁻¹ =
      (kernelValue 1059 : Model) * (x : Model) :=
    congrArg (fun y : M => (y : Model)) (shear_action x 1 hpi)
  have hmem : (kernelValue 1059 : Model) ∈ X := by
    have hm := mem_map_of_mem (MulAut.conj (kernelValue 1 : Model)).toMonoidHom hx
    have hmap := mem_normalizer_iff_map_conj_eq.mp hn
    change X.map (MulAut.conj (kernelValue 1 : Model)).toMonoidHom = X at hmap
    rw [hmap] at hm
    change (kernelValue 1 : Model) * (x : Model) * (kernelValue 1 : Model)⁻¹ ∈ X at hm
    rw [he] at hm
    have hxi : (x : Model)⁻¹ ∈ X := X.inv_mem hx
    simpa only [mul_inv_cancel_right] using X.mul_mem hm hxi
  have hbad := kernel_mask_zero_or_seed X himage hzero hseed ⟨1059,by decide⟩ hmem
  norm_num at hbad

/-- The exceptional zero-form lift has a strictly larger two-local normalizer:
the canonical central omega is preserved, whereas the displayed shear moves X. -/
theorem normalizer_lt_omega_normalizer (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (himage : (X.subgroupOf M).map projection = imageGroup)
    (hCM : centralizer (X : Set Model) ≤ M)
    (hzero : intrinsicElementaryForm X = 0)
    (hseed : (kernelValue 633 : Model) ∈ X) :
    normalizer (X : Set Model) <
      normalizer (omegaCenterIn (centralizer (X : Set Model)) : Set Model) := by
  apply lt_of_le_not_ge (normalizer_le_centralizer_omegaCenter_normalizer X)
  intro h
  apply shear_not_mem_normalizer X himage hzero hseed
  exact h (normalizer_le_normalizer_omegaCenterIn _ (shear_mem_centralizer_normalizer X himage hCM))

/-- The original residual quotient supplies both the coordinate alignment and
the ambient centralizer placement; neither is an extra source assumption. -/
theorem residual_eight_normalizer_lt (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXR : X ≤ residualInclusion.range) (n : residual)
    (himage : (X.comap residualInclusion).map residualProjection =
      (smallContainer 0).map (MulAut.conj (residualProjection n)).toMonoidHom)
    (hzero : intrinsicElementaryForm X = 0) (hseed : (seed : Model) ∈ X) :
    normalizer (X : Set Model) <
      normalizer (omegaCenterIn (centralizer (X : Set Model)) : Set Model) := by
  obtain ⟨s,hsi,hss⟩ := residual_eight_conjugate_alignment X hXR n himage
  let e := MulAut.conj (s : Model)
  let Y := X.map e.toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  have hseedY : (kernelValue 633 : Model) ∈ Y := hss ▸ mem_map_of_mem e.toMonoidHom hseed
  have hzeroY := intrinsicForm_zero_map X Y e rfl hzero
  have hseed1 : (seed : Model) ≠ 1 := by
    intro he
    have ho := seed_order
    rw [he,orderOf_one] at ho
    contradiction
  have ht1 : (kernelValue 633 : Model) ≠ 1 := by
    rw [← hss]
    exact fun h => hseed1 (e.injective (h.trans (map_one e).symm))
  have hnot : ¬ IsConj a (kernelValue 633 : Model) := by
    intro h
    have hh : IsConj (kernelValue 633 : Model) (seed : Model) := by
      rw [← hss]
      exact isConj_iff.mpr ⟨(s : Model)⁻¹,by simp [mul_assoc]⟩
    exact first_not_isConj_second (h.trans hh)
  have hCM : centralizer (Y : Set Model) ≤ M :=
    (centralizer_le (Set.singleton_subset_iff.mpr hseedY)).trans
      (kernel_nonfirst_centralizer_le_max1 _ (kernelValue_mem_E 633) ht1 hnot)
  have hkC := shear_mem_centralizer_normalizer Y hsi hCM
  have hkX := shear_not_mem_normalizer Y hsi hzeroY hseedY
  have hmap : (normalizer (centralizer (X : Set Model) : Set Model)).map e.toMonoidHom =
      normalizer (centralizer (Y : Set Model) : Set Model) := by
    rw [map_equiv_normalizer_eq,map_centralizer_equiv]
    rfl
  rw [← hmap] at hkC
  obtain ⟨k,hk,he⟩ := hkC
  have hkn : k ∉ normalizer (X : Set Model) := by
    intro hn
    apply hkX
    have hh := mem_map_of_mem e.toMonoidHom hn
    rw [map_equiv_normalizer_eq,he] at hh
    exact hh
  apply lt_of_le_not_ge (normalizer_le_centralizer_omegaCenter_normalizer X)
  intro h
  exact hkn (h (normalizer_le_normalizer_omegaCenterIn _ hk))

/-- Strict exceptional enlargement contradicts maximality among two-locals,
without any assumption about a full ambient Sylow subgroup. -/
theorem residual_eight_not_maximal (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXR : X ≤ residualInclusion.range) (n : residual)
    (himage : (X.comap residualInclusion).map residualProjection =
      (smallContainer 0).map (MulAut.conj (residualProjection n)).toMonoidHom)
    (hzero : intrinsicElementaryForm X = 0) (hseed : (seed : Model) ∈ X) :
    ¬ IsMaximalTwoLocal (normalizer (X : Set Model)) := by
  intro hM
  have hW : omegaCenterIn (centralizer (X : Set Model)) ≠ ⊥ := by
    intro he
    have hs := elementary_le_centralizer_omegaCenter X hseed
    rw [he,mem_bot] at hs
    have ho := seed_order
    rw [hs,orderOf_one] at ho
    contradiction
  have hlt := residual_eight_normalizer_lt X hXR n himage hzero hseed
  have he := hM.eq_of_le ⟨_,hW,IsElementaryAbelian.isPGroup 2 _,rfl⟩ hlt.le
  exact hlt.ne he


/-- At an arbitrary radical normalized through the exceptional source lift,
the strict enlargement lies in the same radical and preserves the full local
normalizer and both literal two-core maps. -/
theorem residual_eight_radical_restriction (P X : Subgroup Model)
    (hP : P.IsPRadical 2) [IsElementaryAbelian 2 X]
    (hXR : X ≤ residualInclusion.range) (n : residual)
    (himage : (X.comap residualInclusion).map residualProjection =
      (smallContainer 0).map (MulAut.conj (residualProjection n)).toMonoidHom)
    (hzero : intrinsicElementaryForm X = 0) (hseed : (seed : Model) ∈ X)
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model)) :
    let W := omegaCenterIn (centralizer (X : Set Model))
    let H := normalizer (W : Set Model)
    W ≠ ⊥ ∧ X ≤ W ∧ W ≤ P ∧ IsTwoLocal H ∧
      normalizer (X : Set Model) < H ∧
      centralizer (W : Set Model) = centralizer (X : Set Model) ∧
      normalizer (P : Set Model) ≤ H ∧ P ≤ H ∧
      (normalizer (P.subgroupOf H : Set H)).map H.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf H).IsPRadical 2 ∧
      (normalizer (P.subgroupOf H : Set H)).pCoreIn 2 = P.subgroupOf H ∧
      ((normalizer (P.subgroupOf H : Set H)).pCoreIn 2).map H.subtype = P := by
  dsimp only
  let W := omegaCenterIn (centralizer (X : Set Model))
  let H := normalizer (W : Set Model)
  have hW : W ≠ ⊥ := by
    intro he
    have hs := elementary_le_centralizer_omegaCenter X hseed
    change (seed : Model) ∈ W at hs
    rw [he,mem_bot] at hs
    have ho := seed_order
    rw [hs,orderOf_one] at ho
    contradiction
  have hlt := residual_eight_normalizer_lt X hXR n himage hzero hseed
  have hNH : normalizer (P : Set Model) ≤ H := hNX.trans hlt.le
  have hPH := P.le_normalizer.trans hNH
  have hWP : W ≤ P := le_of_normalizer_le_normalizer_of_pCore_normalizer_le
    P W hP.isPGroup (IsElementaryAbelian.isPGroup 2 W) hP.2.le hNH
  have hN := hNH.trans H.le_normalizer
  have hcore := hP.normalizer_core_subgroupOf H hPH hN
  refine ⟨hW,elementary_le_centralizer_omegaCenter X,hWP,
    ⟨W,hW,IsElementaryAbelian.isPGroup 2 W,rfl⟩,hlt,
    centralizer_omegaCenter_centralizer_eq X,hNH,hPH,?_,
    hP.subgroupOf_of_normalizer_normalizes H hPH hN,hcore,?_⟩
  · rw [← subgroupOf_normalizer_eq hPH,map_subgroupOf_eq_of_le hNH]
  · rw [hcore,map_subgroupOf_eq_of_le hPH]


end Janko4.LocalStructure.ElementaryNormalizerCover.M22Images.EightEnlargement
