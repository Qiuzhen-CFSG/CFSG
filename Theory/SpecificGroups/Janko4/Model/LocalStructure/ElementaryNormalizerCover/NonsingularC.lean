module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.KernelAction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.CentralizerReduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.KernelCentralizer

/-!
# Zero-form enlargement for the literal nonsingular (c) and (c′) rows

The displayed Figure 2 permutations, together with the Figure 1 pair, define
actual subgroups of the native Mathieu star quotient. Word certificates prove
membership, and the MOG conversion retains the printed coordinate convention.

The full ambient centralizer acts by translations on the unique regular
eight-orbit of the (c′) image. Its tetrad, the native kernel involution with
mask 818, therefore belongs to the central omega of C(X). Central elements of
C(X) fix four kernel pairs and the half-octad mask 7. These conditions force
the two pair characters whose product is the tetrad to agree. The tetrad
therefore lies in the intrinsic form radical of the central omega.

For either selected whole image, the original 2B seed places the full
centralizer in max1. Its form radical is thus a nontrivial zero-form subgroup
normalized by the whole N(X). This proves the weak enlargement needed for
these rows without assuming a centralizer table. The more specific assertion
in Proposition 2.3.3 that C(X) itself is elementary remains a separate source
calculation. General selection of the rows belongs to the remaining cover.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Figures 1/2,
Proposition 2.3.3 and Corollary 2.3.7, printed pp.486,490,492--493.
The native star action, MOG conversion and kernel labels retain the ATLAS
attribution of the imported model and ElementaryEightGeometry.Data.
-/

set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.NonsingularC
open Cardinality QuotientCount.Image KernelCount
open Simplicity.Max1Fusion Simplicity.Max1Fusion.KernelOrbits
open LinearFive InvolutionCentralizers.Second LargeCenterRadicals.OuterHalf
open ElementaryEightGeometry M22Images.KernelAction
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel basis

def verticalTable : Fin 2 → Fin 24 → Fin 24 :=
  ![![0, 1, 19, 20, 14, 8, 6, 15, 5, 18, 22, 11, 12, 13, 4, 7, 17, 16, 9, 2, 3, 21, 10, 23], ![0, 1, 18, 10, 7, 16, 6, 4, 17, 19, 3, 11, 12, 13, 15, 14, 5, 8, 2, 9, 22, 21, 20, 23]]
def verticalMogTable : Fin 2 → Fin 24 → Fin 24 :=
  ![![0, 1, 8, 9, 10, 11, 6, 7, 2, 3, 4, 5, 12, 13, 20, 21, 22, 23, 18, 19, 14, 15, 16, 17], ![0, 1, 14, 15, 16, 17, 6, 7, 20, 21, 22, 23, 12, 13, 2, 3, 4, 5, 18, 19, 8, 9, 10, 11]]
def verticalPermutation (i : Fin 2) : Equiv.Perm (Fin 24) where
  toFun := verticalTable i
  invFun := verticalTable i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

def verticalMogPermutation (i : Fin 2) : Equiv.Perm (Fin 24) where
  toFun := verticalMogTable i
  invFun := verticalMogTable i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

theorem vertical_mog (i : Fin 2) :
    (MulAut.conj mogToStar) (verticalMogPermutation i) = verticalPermutation i := by
  revert i
  decide +kernel

private def verticalWord : Fin 2 → List (Fin 4) :=
  ![[2, 3, 3, 0, 3, 0, 3, 0, 3, 0, 3, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 0, 3, 0, 1, 0, 3, 0, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1], [1, 2, 3, 2, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 0, 3, 0, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 1]]
private theorem vertical_word : ∀ i,
    Theory.GroupTheory.evalWord ElementaryEightGeometry.alphabet (verticalWord i) = verticalPermutation i := by
  decide +kernel

def vertical (i : Fin 2) : StarGroup := ⟨verticalPermutation i, by
  rw [← vertical_word]
  apply StarOrderCertificate.word_mem ElementaryEightGeometry.alphabet StarGroup
  intro j
  fin_cases j
  · exact subset_closure (by simp [ElementaryEightGeometry.alphabet])
  · exact subset_closure (by simp [ElementaryEightGeometry.alphabet])
  · exact StarGroup.inv_mem (subset_closure (by simp))
  · exact StarGroup.inv_mem (subset_closure (by simp))⟩

/-- Figure 2(c), with the Figure 1 pair permutation included. -/
def wholeGenerator : Fin 4 → StarGroup := ![starElement 0,vertical 0,vertical 1,starElement 5]
def primedGenerator : Fin 3 → StarGroup := ![vertical 0,vertical 1,starElement 5]
def wholeImage : Subgroup StarGroup := closure (Set.range wholeGenerator)
def primedImage : Subgroup StarGroup := closure (Set.range primedGenerator)

theorem primed_le_whole : primedImage ≤ wholeImage := by
  apply (closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  exact subset_closure ⟨i.succ,rfl⟩

private def primedProduct (k : Fin 8) : StarGroup :=
  binaryProduct primedGenerator (fun i => k.val.testBit i.val)

private def productTable : Fin 8 → Fin 24 → Fin 24 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23], ![0, 1, 19, 20, 14, 8, 6, 15, 5, 18, 22, 11, 12, 13, 4, 7, 17, 16, 9, 2, 3, 21, 10, 23], ![0, 1, 18, 10, 7, 16, 6, 4, 17, 19, 3, 11, 12, 13, 15, 14, 5, 8, 2, 9, 22, 21, 20, 23], ![0, 1, 9, 22, 15, 17, 6, 14, 16, 2, 20, 11, 12, 13, 7, 4, 8, 5, 19, 18, 10, 21, 3, 23], ![1, 0, 3, 2, 4, 5, 23, 7, 8, 22, 18, 12, 11, 21, 14, 15, 16, 17, 10, 20, 19, 13, 9, 6], ![1, 0, 20, 19, 14, 8, 23, 15, 5, 10, 9, 12, 11, 21, 4, 7, 17, 16, 22, 3, 2, 13, 18, 6], ![1, 0, 10, 18, 7, 16, 23, 4, 17, 20, 2, 12, 11, 21, 15, 14, 5, 8, 3, 22, 9, 13, 19, 6], ![1, 0, 22, 9, 15, 17, 23, 14, 16, 3, 19, 12, 11, 21, 7, 4, 8, 5, 20, 10, 18, 13, 2, 6]]
private theorem product_table : ∀ k,
    (fun i => (primedProduct k).val i) = productTable k := by decide +kernel

private theorem product_mem (k : Fin 8) : primedProduct k ∈ primedImage :=
  binaryProduct_mem _ _ _ (fun i => subset_closure (Set.mem_range_self i))

private def tetrad : Fin 4 → Fin 24 := ![2,3,19,20]
private theorem orbit_detect : ∀ j : Fin 24,
    (∀ k : Fin 8, productTable k j = j ↔ productTable k 2 = 2) →
    ∃ k : Fin 8, productTable k 2 = j := by decide +kernel
private def tetradWord : Fin 4 → Fin 8 := ![0,4,1,5]
private theorem tetrad_word : ∀ i, productTable (tetradWord i) 2 = tetrad i := by decide +kernel
private theorem table_commute : ∀ i j k,
    productTable i (productTable j k) = productTable j (productTable i k) := by decide +kernel
private theorem tetrad_label : ∀ k,
    Nat.xor (pairLabel (productTable k (tetrad 0)) (productTable k (tetrad 1)))
      (pairLabel (productTable k (tetrad 2)) (productTable k (tetrad 3))) = 818 := by decide +kernel

private def leftPair : Fin 4 → Fin 24 × Fin 24 := ![(0,1),(12,11),(13,21),(6,23)]
private def leftMask : Fin 4 → Fin 2048 := ![1,819,1128,1882]
private theorem left_mask : ∀ i, pairLabel (leftPair i).1 (leftPair i).2 = (leftMask i).val := by decide +kernel
private theorem left_distinct : ∀ i, (leftPair i).1 ≠ (leftPair i).2 := by decide +kernel
private theorem fixed_left : ∀ i j, SylowCore.starMask (wholeGenerator j) (leftMask i).val = (leftMask i).val := by decide +kernel
private theorem fixed_seven : ∀ j, SylowCore.starMask (wholeGenerator j) 7 = 7 := by decide +kernel

/-- The native tetrad in either of the two regular eight-orbits. -/
def centralInvolution : Model := kernelValue 818

theorem centralInvolution_ne_one : centralInvolution ≠ 1 := by
  intro he
  have h := kernelValue_injective (by decide : 818 < 2048) (by decide : 0 < 2048)
    ((show kernelValue 818 = 1 from Subtype.ext he).trans kernelValue_zero.symm)
  contradiction

private theorem centralInvolution_square : centralInvolution ^ 2 = 1 := by
  change ((kernelValue 818 : M) : Model) ^ 2 = 1
  have h : kernelValue 818 * kernelValue 818 = 1 := by
    rw [← kernelValue_xor]
    exact kernelValue_zero
  simpa only [pow_two,Subgroup.coe_mul,Subgroup.coe_one] using congrArg (fun x : M => (x : Model)) h

theorem centralInvolution_order : orderOf centralInvolution = 2 :=
  orderOf_eq_prime centralInvolution_square centralInvolution_ne_one

private theorem centralizer_tetrad_action (X : Subgroup Model)
    (hl : primedImage ≤ (X.subgroupOf M).map starHom)
    (c : M) (hc : (c : Model) ∈ centralizer (X : Set Model)) :
    ∃ k : Fin 8, ∀ i : Fin 4,
      (starHom c).val (tetrad i) = productTable k (tetrad i) := by
  have hcomm (k : Fin 8) (j : Fin 24) :
      (starHom c).val (productTable k j) = productTable k ((starHom c).val j) := by
    obtain ⟨x,hx,he⟩ := hl (product_mem k)
    have hcx : Commute c x := Subtype.ext (hc x hx).symm
    have hv := congrArg (fun y : StarGroup => y.val j) (hcx.map starHom).eq
    rw [he] at hv
    simpa only [coe_mul,Equiv.Perm.mul_apply,← product_table] using hv
  have hfix (k : Fin 8) : productTable k ((starHom c).val 2) = (starHom c).val 2 ↔
      productTable k 2 = 2 := by
    rw [← hcomm]
    exact (starHom c).val.injective.eq_iff
  obtain ⟨k,hk⟩ := orbit_detect _ hfix
  refine ⟨k,fun i => ?_⟩
  calc
    (starHom c).val (tetrad i) =
        (starHom c).val (productTable (tetradWord i) 2) := by rw [tetrad_word]
    _ = productTable (tetradWord i) ((starHom c).val 2) := hcomm _ _
    _ = productTable k (productTable (tetradWord i) 2) := by rw [← hk,table_commute]
    _ = productTable k (tetrad i) := by rw [tetrad_word]

/-- The full centralizer fixes the tetrad, since its action on the unique
regular eight-orbit is a translation from the displayed (c′) image. -/
theorem centralizer_le_tetrad_centralizer (X : Subgroup Model)
    (hl : primedImage ≤ (X.subgroupOf M).map starHom)
    (hCM : centralizer (X : Set Model) ≤ M) :
    centralizer (X : Set Model) ≤ centralizer ({centralInvolution} : Set Model) := by
  intro c hc
  let c0 : M := ⟨c,hCM hc⟩
  obtain ⟨k,hk⟩ := centralizer_tetrad_action X hl c0 hc
  have ht : kernelValue 818 = kernelValue (pairLabel (tetrad 0) (tetrad 1)) *
      kernelValue (pairLabel (tetrad 2) (tetrad 3)) := by
    rw [← kernelValue_xor]
    rfl
  have he : c0 * kernelValue 818 * c0⁻¹ = kernelValue 818 := by
    rw [ht]
    change (MulAut.conj c0).toMonoidHom (_ * _) = _
    rw [map_mul]
    rw [show (MulAut.conj c0).toMonoidHom (kernelValue (pairLabel (tetrad 0) (tetrad 1))) =
      kernelValue (pairLabel ((starHom c0).val (tetrad 0)) ((starHom c0).val (tetrad 1))) from
      congrArg Subtype.val (starHom_pair c0 (tetrad 0) (tetrad 1))]
    rw [show (MulAut.conj c0).toMonoidHom (kernelValue (pairLabel (tetrad 2) (tetrad 3))) =
      kernelValue (pairLabel ((starHom c0).val (tetrad 2)) ((starHom c0).val (tetrad 3))) from
      congrArg Subtype.val (starHom_pair c0 (tetrad 2) (tetrad 3))]
    rw [hk,hk,hk,hk,← kernelValue_xor,tetrad_label,← ht]
  exact mem_centralizer_singleton_iff.mpr
    (congrArg (fun x : M => (x : Model)) (mul_inv_eq_iff_eq_mul.mp he))

theorem centralInvolution_mem_omega (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hl : primedImage ≤ (X.subgroupOf M).map starHom)
    (hCM : centralizer (X : Set Model) ≤ M) :
    centralInvolution ∈ omegaCenterIn (centralizer (X : Set Model)) := by
  have hcomm (c : Model) (hc : c ∈ centralizer (X : Set Model)) :
      c * centralInvolution = centralInvolution * c :=
    mem_centralizer_singleton_iff.mp (centralizer_le_tetrad_centralizer X hl hCM hc)
  exact (mem_omegaCenterIn_iff _ _).mpr
    ⟨fun x hx => hcomm x (X.le_centralizer hx),hcomm,centralInvolution_square⟩

private theorem fixed_mask_centralizes (X : Subgroup Model) (hXM : X ≤ M)
    (hu : (X.subgroupOf M).map starHom ≤ wholeImage)
    (m : Fin 2048) (hm : ∀ j, SylowCore.starMask (wholeGenerator j) m.val = m.val) :
    (kernelValue m.val : Model) ∈ centralizer (X : Set Model) := by
  have hf := (starMask_closure_fixed_iff wholeGenerator m).mpr hm
  intro x hx
  let x0 : M := ⟨x,hXM hx⟩
  have he := kernel_conjugation x0 m.val
  change x0 * kernelValue m.val * x0⁻¹ = kernelValue (SylowCore.starMask (starHom x0) m.val) at he
  rw [hf _ (hu (mem_map_of_mem _ hx))] at he
  exact congrArg (fun y : M => (y : Model)) (mul_inv_eq_iff_eq_mul.mp he)

private theorem pair_endpoints : ∀ (i : Fin 4) (a b : Fin 24),
    pairLabel a b = (leftMask i).val →
      (a = (leftPair i).1 ∧ b = (leftPair i).2) ∨
      (a = (leftPair i).2 ∧ b = (leftPair i).1) := by decide +kernel
private def chosenPoint (i : Fin 4) (b : Bool) : Fin 24 :=
  if b then (leftPair i).2 else (leftPair i).1
private theorem seven_uniform : ∀ f : Fin 4 → Bool,
    Nat.xor (pairLabel (chosenPoint 0 (f 0)) (chosenPoint 1 (f 1)))
      (pairLabel (chosenPoint 2 (f 2)) (chosenPoint 3 (f 3))) = 7 → f 0 = f 1 := by decide +kernel

/-- Central elements of C(X) induce the same interchange on the first two
left-column pairs. The half-octad mask 7 detects the difference. -/
private theorem omega_pair_action (X : Subgroup Model) (hXM : X ≤ M)
    (hu : (X.subgroupOf M).map starHom ≤ wholeImage)
    (w : M) (hw : (w : Model) ∈ omegaCenterIn (centralizer (X : Set Model))) :
    (InnerRelated (kernelValue 1 : Model) (w : Model) ↔
      InnerRelated (kernelValue 819 : Model) (w : Model)) := by
  have hcomm (m : Fin 2048) (hm : ∀ j, SylowCore.starMask (wholeGenerator j) m.val = m.val) :
      Commute w (kernelValue m.val) := by
    apply Subtype.ext
    exact (((mem_omegaCenterIn_iff _ _).mp hw).2.1 _
      (fixed_mask_centralizes X hXM hu m hm)).symm
  have hpair (i : Fin 4) :
      pairLabel ((starHom w).val (leftPair i).1) ((starHom w).val (leftPair i).2) =
        (leftMask i).val := by
    have he := congrArg Subtype.val (starHom_pair w (leftPair i).1 (leftPair i).2)
    change w * kernelValue (pairLabel (leftPair i).1 (leftPair i).2) * w⁻¹ =
      kernelValue (pairLabel ((starHom w).val (leftPair i).1) ((starHom w).val (leftPair i).2)) at he
    rw [left_mask,(hcomm (leftMask i) (fixed_left i)).eq,mul_inv_cancel_right] at he
    exact kernelValue_injective (pairLabel_lt _ _) (leftMask i).isLt he.symm
  have hchoice (i : Fin 4) : ∃ b : Bool,
      (starHom w).val (leftPair i).1 = chosenPoint i b ∧
      (starHom w).val (leftPair i).2 = chosenPoint i (!b) := by
    rcases pair_endpoints i _ _ (hpair i) with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact ⟨false,ha,hb⟩
    · exact ⟨true,ha,hb⟩
  choose f hf using hchoice
  have hseven : Nat.xor (pairLabel (chosenPoint 0 (f 0)) (chosenPoint 1 (f 1)))
      (pairLabel (chosenPoint 2 (f 2)) (chosenPoint 3 (f 3))) = 7 := by
    have he0 := congrArg Subtype.val (starHom_pair w (leftPair 0).1 (leftPair 1).1)
    have he1 := congrArg Subtype.val (starHom_pair w (leftPair 2).1 (leftPair 3).1)
    change w * kernelValue (pairLabel (leftPair 0).1 (leftPair 1).1) * w⁻¹ =
      kernelValue (pairLabel ((starHom w).val (leftPair 0).1) ((starHom w).val (leftPair 1).1)) at he0
    change w * kernelValue (pairLabel (leftPair 2).1 (leftPair 3).1) * w⁻¹ =
      kernelValue (pairLabel ((starHom w).val (leftPair 2).1) ((starHom w).val (leftPair 3).1)) at he1
    have hc7 : Commute w (kernelValue 7) := hcomm 7 fixed_seven
    have hm : kernelValue 7 = kernelValue (pairLabel (leftPair 0).1 (leftPair 1).1) *
        kernelValue (pairLabel (leftPair 2).1 (leftPair 3).1) := by rw [← kernelValue_xor]; rfl
    have he : kernelValue 7 =
        kernelValue (Nat.xor (pairLabel (chosenPoint 0 (f 0)) (chosenPoint 1 (f 1)))
          (pairLabel (chosenPoint 2 (f 2)) (chosenPoint 3 (f 3)))) := by
      calc
        kernelValue 7 = (MulAut.conj w).toMonoidHom (kernelValue 7) := by
          change _ = w * kernelValue 7 * w⁻¹
          rw [hc7.eq,mul_inv_cancel_right]
        _ = _ := by
          rw [hm,map_mul]
          change (w * _ * w⁻¹) * (w * _ * w⁻¹) = _
          rw [he0,he1,(hf 0).1,(hf 1).1,(hf 2).1,(hf 3).1,← kernelValue_xor]
    have hb : ∀ f : Fin 4 → Bool,
        Nat.xor (pairLabel (chosenPoint 0 (f 0)) (chosenPoint 1 (f 1)))
          (pairLabel (chosenPoint 2 (f 2)) (chosenPoint 3 (f 3))) < 2048 := by decide +kernel
    exact kernelValue_injective (hb f) (by decide) he.symm
  have hf01 := seven_uniform f hseven
  have h0 := hf 0
  have h1 := hf 1
  rw [← hf01] at h1
  cases h : f 0
  · simp only [h,chosenPoint,Bool.false_eq_true,if_false,Bool.not_false,if_true] at h0 h1
    change (starHom w).val 0 = 0 ∧ (starHom w).val 1 = 1 at h0
    change (starHom w).val 12 = 12 ∧ (starHom w).val 11 = 11 at h1
    exact iff_of_true (inner_of_star_fixed w 0 1 (by decide) h0.1 h0.2)
      (inner_of_star_fixed w 12 11 (by decide) h1.1 h1.2)
  · simp only [h,chosenPoint,if_true,Bool.not_true,Bool.false_eq_true,if_false] at h0 h1
    change (starHom w).val 0 = 1 ∧ (starHom w).val 1 = 0 at h0
    change (starHom w).val 12 = 11 ∧ (starHom w).val 11 = 12 at h1
    exact iff_of_false (LinearFive.Geometry.not_inner_of_star_swap w 0 1 (by decide) h0.1 h0.2)
      (LinearFive.Geometry.not_inner_of_star_swap w 12 11 (by decide) h1.1 h1.2)

/-- The nonzero native tetrad lies in the radical of the canonical central omega. -/
theorem centralInvolution_mem_radical (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXM : X ≤ M) (hl : primedImage ≤ (X.subgroupOf M).map starHom)
    (hu : (X.subgroupOf M).map starHom ≤ wholeImage)
    (hCM : centralizer (X : Set Model) ≤ M) :
    centralInvolution ∈ formRadical (omegaCenterIn (centralizer (X : Set Model))) := by
  let W := omegaCenterIn (centralizer (X : Set Model))
  have ht := centralInvolution_mem_omega X hl hCM
  refine ⟨ht,?_⟩
  intro w hw
  by_cases hw1 : w = 1
  · rw [hw1,outerValue_one_right]
  let w0 : M := ⟨w,hCM (map_subtype_le _ hw)⟩
  have hw2 : orderOf w = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) w hw) hw1
  have hc (i : Fin 4) : Commute (kernelValue (leftMask i).val : Model) w :=
    ((mem_omegaCenterIn_iff _ _).mp hw).2.1 _ (fixed_mask_centralizes X hXM hu _ (fixed_left i))
  have ho (i : Fin 4) : orderOf (kernelValue (leftMask i).val : Model) = 2 := by
    rw [← left_mask]
    exact pair_order _ _ (left_distinct i)
  have hi := omega_pair_action X hXM hu w0 hw
  have he : InnerRelated w (kernelValue 1 : Model) ↔ InnerRelated w (kernelValue 819 : Model) :=
    (innerRelated_symm _ _ (ho 0) hw2 (hc 0)).symm.trans
      (hi.trans (innerRelated_symm _ _ (ho 1) hw2 (hc 1)))
  have hv : outerValue w (kernelValue 1 : Model) = outerValue w (kernelValue 819 : Model) := by
    simp only [outerValue,hw1,false_or]
    rw [he]
  have hprod : centralInvolution = (kernelValue 1 : Model) * (kernelValue 819 : Model) := by
    change (kernelValue 818 : Model) = ((kernelValue 1 * kernelValue 819 : M) : Model)
    rw [← kernelValue_xor]
    rfl
  have hc0 : Commute w (kernelValue 1 : Model) := (hc 0).symm
  have hc1 : Commute w (kernelValue 819 : Model) := (hc 1).symm
  have hz : outerValue w centralInvolution = 0 := by
    rw [hprod,outerValue_mul_right w hw2 _ _ hc0 hc1,hv,← two_mul]
    rw [show (2 : ZMod 2) = 0 from rfl,zero_mul]
  have hwt : Commute w centralInvolution := setLike_mul_comm hw ht
  exact (outerValue_eq_zero_iff _ _ centralInvolution_ne_one).mpr
    ((innerRelated_symm _ _ hw2 centralInvolution_order hwt).mp
      ((outerValue_eq_zero_iff _ _ hw1).mp hz))

/-- The canonical subgroup used for the weak zero-form enlargement. -/
def zeroWitness (X : Subgroup Model) : Subgroup Model :=
  formRadical (omegaCenterIn (centralizer (X : Set Model)))

instance zeroWitness_elementary (X : Subgroup Model) : IsElementaryAbelian 2 (zeroWitness X) :=
  inferInstanceAs (IsElementaryAbelian 2 (formRadical (omegaCenterIn (centralizer (X : Set Model)))))

theorem zeroWitness_form (X : Subgroup Model) : intrinsicElementaryForm (zeroWitness X) = 0 :=
  formRadical_form_zero _

theorem zeroWitness_normalizer (X : Subgroup Model) :
    normalizer (X : Set Model) ≤ normalizer (zeroWitness X : Set Model) :=
  (normalizer_le_centralizer_omegaCenter_normalizer X).trans
    (normalizer_le_formRadical_normalizer _)

/-- The selected (c) or (c′) source row supplies a NONTRIVIAL zero-form
subgroup invariant under the WHOLE normalizer. The literal seed discharges
ambient centralizer placement; no centralizer table is assumed. -/
theorem source_zeroWitness (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X)
    (hrow : (X.subgroupOf M).map starHom = wholeImage ∨
      (X.subgroupOf M).map starHom = primedImage) :
    centralInvolution ∈ zeroWitness X ∧ zeroWitness X ≠ ⊥ ∧
      intrinsicElementaryForm (zeroWitness X) = 0 ∧
      normalizer (X : Set Model) ≤ normalizer (zeroWitness X : Set Model) := by
  have hCM : centralizer (X : Set Model) ≤ M :=
    (centralizer_le (Set.singleton_subset_iff.mpr hs)).trans ambient_le_max1
  have hXM : X ≤ M := X.le_centralizer.trans hCM
  have hl : primedImage ≤ (X.subgroupOf M).map starHom := by
    rcases hrow with h | h
    · rw [h]; exact primed_le_whole
    · rw [h]
  have hu : (X.subgroupOf M).map starHom ≤ wholeImage := by
    rcases hrow with h | h
    · rw [h]
    · rw [h]; exact primed_le_whole
  have ht := centralInvolution_mem_radical X hXM hl hu hCM
  exact ⟨ht,fun he => centralInvolution_ne_one (mem_bot.mp (he ▸ ht)),
    zeroWitness_form X,zeroWitness_normalizer X⟩

/-- Literal ambient conjugation of the selected source branch. -/
theorem source_conjugate_zero_enlargement (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X)
    (hrow : (X.subgroupOf M).map starHom = wholeImage ∨
      (X.subgroupOf M).map starHom = primedImage) (g : Model) :
    let Y := (zeroWitness X).map (MulAut.conj g).toMonoidHom
    Y ≠ ⊥ ∧ ∃ _ : IsElementaryAbelian 2 Y, intrinsicElementaryForm Y = 0 ∧
      normalizer (X.map (MulAut.conj g).toMonoidHom : Set Model) ≤ normalizer (Y : Set Model) := by
  dsimp only
  let Y := (zeroWitness X).map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  obtain ⟨ht,hY,hzero,hn⟩ := source_zeroWitness X hs hrow
  have hYne : Y ≠ ⊥ := by
    intro he
    have hm := mem_map_of_mem (MulAut.conj g).toMonoidHom ht
    have ho : (MulAut.conj g) centralInvolution = 1 := mem_bot.mp (he ▸ hm)
    exact centralInvolution_ne_one ((MulAut.conj g).injective (ho.trans (map_one _).symm))
  refine ⟨hYne,inferInstance,intrinsicForm_zero_map _ Y (MulAut.conj g) rfl hzero,?_⟩
  rw [← map_equiv_normalizer_eq,← map_equiv_normalizer_eq]
  exact map_mono hn


end Janko4.LocalStructure.ElementaryNormalizerCover.NonsingularC
