module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.FirstLiftPositioning

/-!
# Pure extensions have Mathieu image of order at most four

Each of the four certified image containers is partitioned into four fibers.
Two elements in the same fiber have a product fixing a star. The actual-lift
restriction makes every nonidentity element of a pure extension's image
fixed-point-free, so each fiber contains at most one image element. At maximal
TWO-local level the image is nontrivial and therefore has order two or four.

These native restrictions contribute to the elementary-normalizer argument
of Kleidman--Wilson (1988), Section 2.1, p.489; no identification with the
printed AAA(2) marking is asserted. The remaining common-sextet and exceptional
centralizer geometry must still use the actual lifts.
-/
set_option Elab.async false
public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
open Cardinality QuotientCount.Image NativePair NativePair.Stabilizer
open LinearFive InvolutionCentralizers.Second
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup Cardinality.localKernel
set_option backward.isDefEq.respectTransparency true

private def fiberLabel (r : Fin 4) : Fin 16 → Fin 4 :=
  if r = 0 then ![0,0,1,1,2,2,3,3,0,0,1,1,2,2,3,3]
  else ![0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3]

private theorem same_fiber_fixed : ∀ (r : Fin 4) (i j : Fin 16),
    fiberLabel r i = fiberLabel r j → ∃ t : Fin 24,
      (element (blockIndex r i)).val ((element (blockIndex r j)).val t) = t := by
  decide +kernel

/-- A fixed-point-free elementary subgroup occupies at most four coordinates
in any of the four actual native image containers. -/
theorem fixed_point_free_imageBlock_bound (r : Fin 4) (A : Subgroup StarGroup)
    [IsElementaryAbelian 2 A] (hA : A ≤ imageBlock r)
    (hfree : ∀ p ∈ A, p ≠ 1 → ∀ t : Fin 24, p.val t ≠ t) : Nat.card A ≤ 4 := by
  classical
  let c : A → Fin 16 := fun x => Classical.choose ((mem_imageBlock_iff r x.val).mp (hA x.property))
  have hc (x : A) : element (blockIndex r (c x)) = x.val :=
    Classical.choose_spec ((mem_imageBlock_iff r x.val).mp (hA x.property))
  let f : A → Fin 4 := fun x => fiberLabel r (c x)
  have hi : Function.Injective f := by
    intro x y he
    obtain ⟨t,ht⟩ := same_fiber_fixed r (c x) (c y) he
    rw [hc x,hc y] at ht
    have hxy : x.val * y.val = 1 := by
      by_contra hn
      exact hfree _ (A.mul_mem x.property y.property) hn t ht
    have hyy : y.val * y.val = 1 := by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) y.val y.property
    exact Subtype.ext (mul_right_cancel (hxy.trans hyy.symm))
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hi

/-- Purity restricts the literal image to order at most four, using the
certified actual-lift exclusion and the exhaustive image containers. -/
theorem pure_extension_image_card_le_four (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x) :
    Nat.card ((X.subgroupOf M).map starHom) ≤ 4 := by
  have hXM := (elementary_overgroup_placement X hpair).1
  let : IsElementaryAbelian 2 (X.subgroupOf M) := IsElementaryAbelian.subgroupOf hXM
  let : IsElementaryAbelian 2 ((X.subgroupOf M).map starHom) := IsElementaryAbelian.map _
  obtain ⟨r,hr⟩ := extension_image_cover X hpair
  exact fixed_point_free_imageBlock_bound r _ hr
    (pure_extension_image_fixed_point_free X hpair hpure)

/-- The two remaining image sizes for the original maximal pure extension.
Neither the image nor the choice of a lift is supplied as a premise. -/
theorem maximal_pure_extension_image_two_or_four (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    Nat.card ((X.subgroupOf M).map starHom) = 2 ∨
      Nat.card ((X.subgroupOf M).map starHom) = 4 := by
  have hb := pure_extension_image_card_le_four X hpair hpure
  have hn := maximal_pure_extension_image_ne_bot X hpair hpure hmax
  have h1 : Nat.card ((X.subgroupOf M).map starHom) ≠ 1 := fun he => hn (card_eq_one.mp he)
  obtain ⟨r,hr⟩ := extension_image_cover X hpair
  have hd := card_dvd_of_le hr
  rw [imageBlock_card] at hd
  generalize he : Nat.card ((X.subgroupOf M).map starHom) = n at *
  interval_cases n <;> norm_num at *

/-- The proper-extension consumer: a pair-centralizing conjugator preserves
the original purity and maximality and reduces the actual image to one of two
containers, with order two or four. Both full ambient local groups are carried
by that same conjugator. No lift or image alternative is a supplied premise. -/
theorem maximal_pure_extension_two_positions (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X) (hlarge : 4 < Nat.card X)
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    ∃ g : localPairCentralizer,
      let Y := X.map (MulAut.conj (g.val : Model)).toMonoidHom
      nativePair ≤ Y ∧ 4 < Nat.card Y ∧ Y ≤ M ∧
      centralizer (Y : Set Model) ≤ M ∧
      (∀ y ∈ Y, y ≠ 1 → IsConj a y) ∧
      IsMaximalTwoLocal (normalizer (Y : Set Model)) ∧
      ((Y.subgroupOf M).map starHom ≤ imageBlock 0 ∨
        (Y.subgroupOf M).map starHom ≤ imageBlock 1) ∧
      (Nat.card ((Y.subgroupOf M).map starHom) = 2 ∨
        Nat.card ((Y.subgroupOf M).map starHom) = 4) ∧
      centralizer (Y : Set Model) = (centralizer (X : Set Model)).map
        (MulAut.conj (g.val : Model)).toMonoidHom ∧
      normalizer (Y : Set Model) = (normalizer (X : Set Model)).map
        (MulAut.conj (g.val : Model)).toMonoidHom := by
  obtain ⟨g,hP,hM,hC,hpos,hct,hnt⟩ := extension_two_image_positioning X hpair
  let Y := X.map (MulAut.conj (g.val : Model)).toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  have hpY : ∀ y ∈ Y, y ≠ 1 → IsConj a y := by
    rintro y ⟨x,hx,rfl⟩ hy
    exact (hpure x hx (fun he => hy (by rw [he,map_one]))).trans
      (isConj_iff.mpr ⟨(g.val : Model),rfl⟩)
  have hmY : IsMaximalTwoLocal (normalizer (Y : Set Model)) := by
    rw [hnt]
    exact isMaximalTwoLocal_map (MulAut.conj (g.val : Model)) hmax
  refine ⟨g,hP,?_,hM,hC,hpY,hmY,hpos,
    maximal_pure_extension_image_two_or_four Y hP hpY hmY,hct,hnt⟩
  rw [card_map_of_injective (MulAut.conj (g.val : Model)).injective]
  exact hlarge

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
