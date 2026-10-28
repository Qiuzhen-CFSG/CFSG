module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.CommonNontrivialPlacement
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.CommonPlacement

/-!
# Whole-normalizer placement for every image of order two

The exceptional-position involutions 64 and 88 are conjugate to 12 by
actual elements of the native pair-centralizer image. Lifting those
conjugators puts each order-two image in the common position and preserves
the original pair, purity, and both whole ambient local groups. The proved
intrinsic common-image argument then places the whole normalizer in max2.
Only the exceptional order-four image remains in the proper pure-extension
reduction. Source: Kleidman--Wilson (1988), Section 2.1, p.489.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
open Cardinality KernelCount QuotientCount.Image
open Simplicity.Max1Fusion NativePair NativePair.Stabilizer LinearFive InvolutionCentralizers.Second
open M22Images.KernelAction InvolutionCentralizers.Second.FiveAction DisplacementActions
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup
  Cardinality.localKernel basis
set_option backward.isDefEq.respectTransparency true

private def twoTransport : Fin 3 → Fin 96 := ![0,2,3]
private theorem two_transport (i : Fin 3) :
    (MulAut.conj (element (twoTransport i))) (element (pureIndex 0 i)) = element 12 := by
  apply Subtype.ext
  revert i
  decide +kernel

private theorem map_conj_mul (A : Subgroup Model) (g k : Model) :
    (A.map (MulAut.conj k).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g*k)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]
private theorem map_conj_one (A : Subgroup Model) :
    A.map (MulAut.conj (1 : Model)).toMonoidHom = A :=
  mem_normalizer_iff_map_conj_eq.mp (normalizer (A : Set Model)).one_mem

/-- The exceptional position's order-two images are carried into the common
position by an actual pair-centralizing lift. Both whole local groups are
transported by that same element. -/
theorem exceptional_two_to_common (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X) (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 0)
    (htwo : Nat.card ((X.subgroupOf M).map starHom) = 2) :
    ∃ g : localPairCentralizer,
      let Y := X.map (MulAut.conj (g.val : Model)).toMonoidHom
      nativePair ≤ Y ∧ (∀ y ∈ Y, y ≠ 1 → IsConj a y) ∧
      (Y.subgroupOf M).map starHom ≤ imageBlock 1 ∧
      (Y.subgroupOf M).map starHom ≠ ⊥ ∧
      centralizer (Y : Set Model) = (centralizer (X : Set Model)).map
        (MulAut.conj (g.val : Model)).toMonoidHom ∧
      normalizer (Y : Set Model) = (normalizer (X : Set Model)).map
        (MulAut.conj (g.val : Model)).toMonoidHom := by
  let A := (X.subgroupOf M).map starHom
  obtain ⟨p,hp,hu⟩ := (Nat.card_eq_two_iff' (1 : A)).mp htwo
  have hp1 : p.val ≠ 1 := fun he => hp (Subtype.ext he)
  obtain ⟨i,hi⟩ := pure_position_image_coordinates X hpair hpure 0 hpos p.val p.property hp1
  obtain ⟨g,hg,hgq⟩ := (mem_pair_image_iff _).mpr ⟨twoTransport i,rfl⟩
  let Y := X.map (MulAut.conj (g : Model)).toMonoidHom
  have hXM := (elementary_overgroup_placement X hpair).1
  have hgc : (g : Model) ∈ centralizer (nativePair : Set Model) := by
    rw [centralizer_eq_local_map]
    exact mem_map_of_mem M.subtype hg
  have hPY : nativePair ≤ Y := by
    intro x hx
    have he : (MulAut.conj (g : Model)) x = x := by
      change (g : Model) * x * (g : Model)⁻¹ = x
      rw [← hgc x hx,mul_inv_cancel_right]
    exact he ▸ mem_map_of_mem (MulAut.conj (g : Model)).toMonoidHom (hpair hx)
  have himage : (Y.subgroupOf M).map starHom ≤ imageBlock 1 := by
    rintro q ⟨z,hz,rfl⟩
    obtain ⟨v,hv,hvz⟩ := hz
    let w : M := ⟨v,hXM hv⟩
    have he : (MulAut.conj g) w = z := Subtype.ext hvz
    have hw : starHom w ∈ A := mem_map_of_mem starHom hv
    by_cases h1 : starHom w = 1
    · rw [← he]
      have hq : starHom ((MulAut.conj g) w) = 1 := by
        simp only [MulAut.conj_apply,map_mul,map_inv,h1,mul_one,mul_inv_cancel]
      exact hq ▸ (imageBlock 1).one_mem
    · have hwq : starHom w = p.val := congrArg Subtype.val (hu ⟨starHom w,hw⟩
        (fun he => h1 (congrArg Subtype.val he)))
      have hq : starHom z = element 12 := by
        rw [← he]
        have hh : starHom ((MulAut.conj g) w) = (MulAut.conj (starHom g)) (starHom w) := by
          simp only [MulAut.conj_apply,map_mul,map_inv]
        rw [hh,hgq,hwq,hi,two_transport]
      rw [hq]
      exact (mem_imageBlock_iff _ _).mpr ⟨4,rfl⟩
  have hn : (Y.subgroupOf M).map starHom ≠ ⊥ := by
    obtain ⟨z,hz,hzq⟩ := p.property
    have hzY : ((MulAut.conj g) z : Model) ∈ Y := mem_map_of_mem _ hz
    have hq : starHom ((MulAut.conj g) z) = element 12 := by
      have hh : starHom ((MulAut.conj g) z) = (MulAut.conj (starHom g)) (starHom z) := by
        simp only [MulAut.conj_apply,map_mul,map_inv]
      rw [hh,hgq,hzq,hi,two_transport]
    have hmem := mem_map_of_mem starHom (show (MulAut.conj g) z ∈ Y.subgroupOf M from hzY)
    rw [hq] at hmem
    intro hb
    rw [hb,mem_bot] at hmem
    have hbad := congrArg (fun u : StarGroup => u.val 0) hmem
    have hn : (element 12).val 0 ≠ 0 := by decide +kernel
    exact hn hbad
  refine ⟨⟨g,hg⟩,hPY,?_,himage,hn,?_,?_⟩
  · rintro y ⟨v,hv,rfl⟩ hy
    exact (hpure v hv (fun he => hy (by rw [he,map_one]))).trans
      (isConj_iff.mpr ⟨(g : Model),rfl⟩)
  · exact (map_centralizer_equiv (X : Set Model) (MulAut.conj (g : Model))).symm
  · exact (map_equiv_normalizer_eq X (MulAut.conj (g : Model))).symm

/-- Every actual order-two image in either position has its whole normalizer
inside a literal native max2 conjugate. -/
theorem two_image_normalizer_placement (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X) (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 0 ∨
      (X.subgroupOf M).map starHom ≤ imageBlock 1)
    (htwo : Nat.card ((X.subgroupOf M).map starHom) = 2) :
    ∃ k : Model, normalizer (X : Set Model) ≤ sourceSubgroup.map (MulAut.conj k).toMonoidHom := by
  rcases hpos with h0 | h1
  · obtain ⟨g,hP,hp,hpos,hn,_,hnt⟩ := exceptional_two_to_common X hpair hpure h0 htwo
    let Y := X.map (MulAut.conj (g.val : Model)).toMonoidHom
    let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
    obtain ⟨k,hk⟩ := common_nontrivial_normalizer_placement Y hP hp hpos hn
    rw [hnt] at hk
    have h := map_mono (f := (MulAut.conj (g.val : Model)⁻¹).toMonoidHom) hk
    rw [map_conj_mul,map_conj_mul,inv_mul_cancel,map_conj_one] at h
    exact ⟨(g.val : Model)⁻¹*k,h⟩
  · apply common_nontrivial_normalizer_placement X hpair hpure h1
    intro hb
    rw [hb,card_bot] at htwo
    contradiction

theorem two_image_maximal (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X) (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 0 ∨
      (X.subgroupOf M).map starHom ≤ imageBlock 1)
    (htwo : Nat.card ((X.subgroupOf M).map starHom) = 2)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    ∃ k : Model, normalizer (X : Set Model) = sourceSubgroup.map (MulAut.conj k).toMonoidHom := by
  obtain ⟨k,hk⟩ := two_image_normalizer_placement X hpair hpure hpos htwo
  exact ⟨k,hmax.eq_of_le (sourceSubgroup_isTwoLocal.map_equiv (MulAut.conj k)) hk⟩

/-- All remaining proper pure extensions have the exceptional order-four
image. This discharges every order-two branch with actual whole-normalizer
placement and retains both literal transports on the remaining branch. -/
theorem maximal_pure_extension_after_two_images (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X) (hlarge : 4 < Nat.card X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    (∃ k : Model, normalizer (X : Set Model) =
      sourceSubgroup.map (MulAut.conj k).toMonoidHom) ∨
    ∃ g : localPairCentralizer,
      let Y := X.map (MulAut.conj (g.val : Model)).toMonoidHom
      nativePair ≤ Y ∧ 4 < Nat.card Y ∧ Y ≤ M ∧
      centralizer (Y : Set Model) ≤ M ∧
      (∀ y ∈ Y, y ≠ 1 → IsConj a y) ∧
      IsMaximalTwoLocal (normalizer (Y : Set Model)) ∧
      Nat.card ((Y.subgroupOf M).map starHom) = 4 ∧
      (Y.subgroupOf M).map starHom ≤ imageBlock 0 ∧
      centralizer (Y : Set Model) = (centralizer (X : Set Model)).map
        (MulAut.conj (g.val : Model)).toMonoidHom ∧
      normalizer (Y : Set Model) = (normalizer (X : Set Model)).map
        (MulAut.conj (g.val : Model)).toMonoidHom := by
  rcases maximal_pure_extension_after_common_four X hpair hlarge hpure hmax with h | h
  · exact Or.inl h
  obtain ⟨g,hP,hlargeY,hM,hC,hpY,hmY,hcase,hct,hnt⟩ := h
  let Y := X.map (MulAut.conj (g.val : Model)).toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  rcases hcase with ⟨htwo,hpos⟩ | ⟨hfour,hpos⟩
  · obtain ⟨k,hk⟩ := two_image_maximal Y hP hpY hpos htwo hmY
    refine Or.inl ⟨(g.val : Model)⁻¹*k,?_⟩
    have he := congrArg (fun A : Subgroup Model =>
      A.map (MulAut.conj (g.val : Model)⁻¹).toMonoidHom) (hnt.symm.trans hk)
    rwa [map_conj_mul,map_conj_mul,inv_mul_cancel,map_conj_one] at he
  · exact Or.inr ⟨g,hP,hlargeY,hM,hC,hpY,hmY,hfour,hpos,hct,hnt⟩

/-- The order-two-image branch for an arbitrary original radical whose
whole normalizer is controlled by this elementary witness. No center-size
bound is imposed, and all restriction and denominator maps are literal. -/
theorem two_image_radical (P X : Subgroup Model) (hP : P.IsPRadical 2)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 0 ∨
      (X.subgroupOf M).map starHom ≤ imageBlock 1)
    (htwo : Nat.card ((X.subgroupOf M).map starHom) = 2)
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model)) :
    ∃ g : Model, let L := sourceSubgroup.map (MulAut.conj g).toMonoidHom
      IsTwoLocal L ∧ normalizer (P : Set Model) ≤ L ∧ P ≤ L ∧
      (normalizer (P.subgroupOf L : Set L)).map L.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf L).IsPRadical 2 ∧
      (normalizer (P.subgroupOf L : Set L)).pCoreIn 2 = P.subgroupOf L ∧
      ((normalizer (P.subgroupOf L : Set L)).pCoreIn 2).map L.subtype = P := by
  obtain ⟨g,hg⟩ := two_image_normalizer_placement X hpair hpure hpos htwo
  let L := sourceSubgroup.map (MulAut.conj g).toMonoidHom
  have hNL : normalizer (P : Set Model) ≤ L := hNX.trans hg
  have hPL := P.le_normalizer.trans hNL
  have hNN := hNL.trans L.le_normalizer
  have hc := hP.normalizer_core_subgroupOf L hPL hNN
  refine ⟨g,sourceSubgroup_isTwoLocal.map_equiv (MulAut.conj g),hNL,hPL,?_,
    hP.subgroupOf_of_normalizer_normalizes L hPL hNN,hc,?_⟩
  · rw [← subgroupOf_normalizer_eq hPL,map_subgroupOf_eq_of_le hNL]
  · rw [hc,map_subgroupOf_eq_of_le hPL]

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
