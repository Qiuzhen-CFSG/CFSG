module
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativePairExclusion

/-!
# Elementary images of extensions of the marked native pair

The full pair centralizer has Mathieu image of order 96. The existing 96
certified permutations exhaust this image, by counting. Their commuting
involutions lie in four explicit elementary subgroups of order sixteen.
Thus every elementary extension of the marked pair has its literal Mathieu
image in one of these four subgroups. At maximal TWO-local level that image
is nontrivial. All statements retain the original max1 projection.

This is a finite native input to the nontrivial-image branch of
Kleidman--Wilson (1988), Section 2.1, p.489. It does not identify the marked
pair with a printed AAA type or assert whole-normalizer placement. The
remaining pure-lift and container geometry is a separate obligation.
-/

set_option Elab.async false
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
open Cardinality QuotientCount.Image KernelCount
open NativePair NativePair.Stabilizer LinearFive InvolutionCentralizers.Second
open M22Images.KernelAction
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup Cardinality.localKernel
set_option backward.isDefEq.respectTransparency true

private theorem generator_mem (j : Fin 5) :
    Stabilizer.generator j ∈ localPairCentralizer.map starHom := by
  obtain ⟨x,hx⟩ := starHom_surjective (Stabilizer.generator j)
  refine ⟨x,?_,hx⟩
  have hf (m : ℕ) (hm : SylowCore.starMask (Stabilizer.generator j) m = m) :
      x * kernelValue m * x⁻¹ = kernelValue m := by
    rw [kernel_conjugation]
    change kernelValue (SylowCore.starMask (starHom x) m) = _
    rw [hx,hm]
  rintro y (rfl | rfl)
  · exact (mul_inv_eq_iff_eq_mul.mp (hf 818 (generator_fixed j).1)).symm
  · exact (mul_inv_eq_iff_eq_mul.mp (hf 1449 (generator_fixed j).2)).symm

/-- Exact enumeration of the actual image, not merely a lower-bound certificate. -/
theorem mem_pair_image_iff (x : StarGroup) :
    x ∈ localPairCentralizer.map starHom ↔ ∃ i : Fin 96, element i = x := by
  let f : Fin 96 → localPairCentralizer.map starHom := fun i =>
    ⟨element i,element_mem _ generator_mem i⟩
  have hi : Function.Injective f := fun _ _ h => element_injective (congrArg Subtype.val h)
  have hs : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr
      ⟨hi,by rw [Nat.card_fin,centralizer_image_card]⟩).2
  constructor
  · intro hx
    obtain ⟨i,hi⟩ := hs ⟨x,hx⟩
    exact ⟨i,congrArg Subtype.val hi⟩
  · rintro ⟨i,rfl⟩
    exact element_mem _ generator_mem i

private theorem element_point : ∀ (i : Fin 96) (x : Fin 24),
    (element i).val x = point i x := by decide +kernel

@[expose] def blockBasis : Fin 4 → Fin 4 → Fin 96 :=
  ![![9,12,29,49], ![1,8,12,48], ![3,6,26,49], ![5,9,38,49]]

@[expose] def blockIndex : Fin 4 → Fin 16 → Fin 96 :=
  ![![0,9,12,19,29,32,41,46,49,56,73,78,64,69,88,95],
    ![0,1,8,9,12,13,18,19,48,49,56,57,72,73,78,79],
    ![0,3,6,9,26,29,32,35,49,50,55,56,63,64,69,70],
    ![0,5,9,10,38,41,45,46,49,52,56,59,87,88,92,95]]

/-- Four literal subgroups of the certified Mathieu image. -/
@[expose] def imageBlock (r : Fin 4) : Subgroup StarGroup :=
  closure (Set.range (fun j => element (blockBasis r j)))

private theorem block_span : ∀ (r : Fin 4) (i : Fin 16),
    binaryProduct (fun j => element (blockBasis r j)) (fun j => i.val.testBit j.val) =
      element (blockIndex r i) := by
  intro r i
  apply Subtype.ext
  revert r i
  decide +kernel

private theorem block_square : ∀ (r j : Fin 4),
    element (blockBasis r j) * element (blockBasis r j) = 1 := by
  intro r j
  apply Subtype.ext
  revert r j
  decide +kernel

private theorem block_commute : ∀ (r i j : Fin 4),
    Commute (element (blockBasis r i)) (element (blockBasis r j)) := by
  intro r i j
  apply Subtype.ext
  revert r i j
  decide +kernel

private theorem bit_vectors : ∀ v : Fin 4 → Bool,
    ∃ i : Fin 16, (fun j : Fin 4 => i.val.testBit j.val) = v := by decide +kernel

/-- Explicit binary coordinates in each image container. -/
theorem mem_imageBlock_iff (r : Fin 4) (x : StarGroup) :
    x ∈ imageBlock r ↔ ∃ i : Fin 16, element (blockIndex r i) = x := by
  constructor
  · intro hx
    obtain ⟨v,rfl⟩ := (mem_closure_iff_binaryProduct _ (block_square r)
      (block_commute r) x).mp hx
    obtain ⟨i,rfl⟩ := bit_vectors v
    exact ⟨i,(block_span r i).symm⟩
  · rintro ⟨i,rfl⟩
    rw [← block_span]
    exact binaryProduct_mem _ _ _ (fun j => subset_closure ⟨j,rfl⟩)

instance (r : Fin 4) : IsElementaryAbelian 2 (imageBlock r) := by
  let : IsMulCommutative (closure (Set.range (fun j => element (blockBasis r j)))) :=
    isMulCommutative_closure (by
      rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
      exact block_commute r i j)
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro _ ⟨j,rfl⟩
  simpa only [pow_two] using block_square r j

/-- The containers are subgroups of the full native pair-centralizer image. -/
theorem imageBlock_le (r : Fin 4) : imageBlock r ≤ localPairCentralizer.map starHom := by
  apply (closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (mem_pair_image_iff _).mpr ⟨_,rfl⟩

/-- The sixteen coordinates are distinct, so each container has order sixteen. -/
theorem imageBlock_card (r : Fin 4) : Nat.card (imageBlock r) = 16 := by
  let f : Fin 16 → imageBlock r := fun i => ⟨element (blockIndex r i),
    (mem_imageBlock_iff _ _).mpr ⟨i,rfl⟩⟩
  have hb : Function.Injective (blockIndex r) := by
    revert r
    decide +kernel
  have hi : Function.Injective f := fun _ _ h =>
    hb (element_injective (congrArg Subtype.val h))
  have hs : Function.Surjective f := by
    intro x
    obtain ⟨i,hi⟩ := (mem_imageBlock_iff r x.val).mp x.property
    exact ⟨i,Subtype.ext hi⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩),Nat.card_fin]

private def coordinate : Fin 4 → Fin 96 → Fin 16 :=
  ![![0,0,0,0,0,0,0,0,0,1,0,0,2,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,4,0,0,5,0,0,0,0,0,0,0,0,6,0,0,0,0,7,0,0,8,0,0,0,0,0,0,9,0,0,0,0,0,0,0,12,0,0,0,0,13,0,0,0,10,0,0,0,0,11,0,0,0,0,0,0,0,0,0,14,0,0,0,0,0,0,15], ![0,1,0,0,0,0,0,0,2,3,0,0,4,5,0,0,0,0,6,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,9,0,0,0,0,0,0,10,11,0,0,0,0,0,0,0,0,0,0,0,0,0,0,12,13,0,0,0,0,14,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], ![0,0,0,1,0,0,2,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,5,0,0,6,0,0,7,0,0,0,0,0,0,0,0,0,0,0,0,0,8,9,0,0,0,0,10,11,0,0,0,0,0,0,12,13,0,0,0,0,14,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], ![0,0,0,0,0,1,0,0,0,2,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,5,0,0,0,6,7,0,0,8,0,0,9,0,0,0,10,0,0,11,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,12,13,0,0,0,14,0,0,15]]
private def chosenBlock : Fin 96 → Fin 4 :=
  ![1,1,0,2,0,3,2,0,1,1,3,0,1,1,0,0,0,0,1,1,0,0,0,0,0,0,2,0,0,2,0,0,2,0,0,2,0,0,3,0,0,3,0,0,0,3,3,0,1,1,2,0,3,0,0,2,1,1,0,3,0,0,0,2,2,0,0,0,0,2,2,0,1,1,0,0,0,0,1,1,0,0,0,0,0,0,0,3,3,0,0,0,3,0,0,3]
private def testPoint : Fin 3 → Fin 24 := ![0,1,4]

private theorem involution_blocks : ∀ i : Fin 96,
    blockIndex 0 (coordinate 0 i) = i ∨
      ∀ k : Fin 96,
        (∀ x, point i (point i (testPoint x)) = testPoint x) →
        (∀ x, point k (point k (testPoint x)) = testPoint x) →
        (∀ x, point i (point k (testPoint x)) = point k (point i (testPoint x))) →
          blockIndex (chosenBlock i) (coordinate (chosenBlock i) k) = k := by
  decide +kernel

/-- Exhaustive elementary-subgroup containment in the actual 96-element image. -/
theorem elementary_image_cover (A : Subgroup StarGroup) [IsElementaryAbelian 2 A]
    (hA : A ≤ localPairCentralizer.map starHom) : ∃ r : Fin 4, A ≤ imageBlock r := by
  classical
  have hs (i : Fin 96) (hi : element i ∈ A) : ∀ x, point i (point i x) = x := by
    have he := elemPow_eq_one_of_isElementaryAbelian (p := 2) (element i) hi
    intro x
    have hh := congrArg (fun p : StarGroup => p.val x) he
    simpa only [pow_two,Subgroup.coe_mul,Subgroup.coe_one,Equiv.Perm.mul_apply,Equiv.Perm.one_apply,element_point] using hh
  by_cases h0 : A ≤ imageBlock 0
  · exact ⟨0,h0⟩
  obtain ⟨x,hx,hx0⟩ := SetLike.not_le_iff_exists.mp h0
  obtain ⟨i,rfl⟩ := (mem_pair_image_iff _).mp (hA hx)
  rcases involution_blocks i with hj | hr
  · exact (hx0 ((mem_imageBlock_iff _ _).mpr ⟨_,congrArg element hj⟩)).elim
  refine ⟨chosenBlock i,?_⟩
  intro y hy
  obtain ⟨k,rfl⟩ := (mem_pair_image_iff _).mp (hA hy)
  have hc : ∀ x, point i (point k x) = point k (point i x) := by
    have he := congrArg Subtype.val (mul_comm (⟨element i,hx⟩ : A) ⟨element k,hy⟩)
    intro x
    have hh := congrArg (fun p : StarGroup => p.val x) he
    simpa only [Subgroup.coe_mul,Equiv.Perm.mul_apply,element_point] using hh
  have hj := hr k (fun x => hs i hx (testPoint x))
    (fun x => hs k hy (testPoint x)) (fun x => hc (testPoint x))
  exact (mem_imageBlock_iff _ _).mpr ⟨_,congrArg element hj⟩

/-- Every elementary extension has its literal projection in a certified image container. -/
theorem extension_image_cover (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X) :
    ∃ r : Fin 4, (X.subgroupOf M).map starHom ≤ imageBlock r := by
  have hXM : X ≤ M := (elementary_overgroup_placement X hpair).1
  let : IsElementaryAbelian 2 (X.subgroupOf M) := IsElementaryAbelian.subgroupOf hXM
  let : IsElementaryAbelian 2 ((X.subgroupOf M).map starHom) := IsElementaryAbelian.map _
  have hlocal : X.subgroupOf M ≤ localPairCentralizer := by
    intro x hx
    rintro y (rfl | rfl)
    · apply Subtype.ext
      exact X.le_centralizer hx _ (hpair (subset_closure (by simp)))
    · apply Subtype.ext
      exact X.le_centralizer hx _ (hpair (subset_closure (by simp)))
  exact elementary_image_cover _ (map_mono hlocal)

/-- Literal application at maximal TWO-local level: the pure image is nontrivial
and its order divides sixteen, in one of the four actual containers. -/
theorem maximal_pure_extension_image_cover (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    ∃ r : Fin 4, (X.subgroupOf M).map starHom ≠ ⊥ ∧
      (X.subgroupOf M).map starHom ≤ imageBlock r ∧
      Nat.card ((X.subgroupOf M).map starHom) ∣ 16 := by
  obtain ⟨r,hr⟩ := extension_image_cover X hpair
  refine ⟨r,maximal_pure_extension_image_ne_bot X hpair hpure hmax,hr,?_⟩
  simpa only [imageBlock_card] using card_dvd_of_le hr

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
