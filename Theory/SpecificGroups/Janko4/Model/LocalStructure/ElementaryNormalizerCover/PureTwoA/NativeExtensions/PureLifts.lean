module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.Positioning
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion
import Mathlib.Tactic.Group

/-!
# Actual first-class lifts in a marked elementary extension

The complete max1 involution census has ten outside-kernel representatives.
Its checked odd-product identities distinguish their ambient fusion: only
representatives zero and nine are in the first class. Thus a nontrivial
Mathieu image in a pure elementary extension supplies an actual first-class
lift, and one local conjugator puts that lift, the original kernel pair,
the entire extension and its full centralizer and normalizer in the same
marking. This is a lift reduction, not a normalizer-cover assertion.

Source: Kleidman--Wilson (1988), Section 2.1, p.489. The representatives are
the existing native ATLAS max1 words, with no identification of nativePair
with printed AAA(2).
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
open Cardinality QuotientCount.Image KernelCount Simplicity
open Simplicity.Max1Fusion Simplicity.Max1Fusion.OutsideWordCertificates
open NativePair LinearFive InvolutionCentralizers.Second
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup
  Cardinality.localKernel outsideRepresentative
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 10000

private theorem isConj_of_odd_product (z t w : Model) (n : ℕ)
    (hz : z ^ 2 = 1) (ht : t ^ 2 = 1) (hn : Odd n)
    (hp : (z * (w * t * w⁻¹)) ^ n = 1) : IsConj t z := by
  have hwt : (w * t * w⁻¹) ^ 2 = 1 := by
    calc
      _ = w * t ^ 2 * w⁻¹ := by simp only [pow_two,mul_assoc,inv_mul_cancel_left]
      _ = 1 := by rw [ht,mul_one,mul_inv_cancel]
  exact (isConj_iff.mpr ⟨w,rfl⟩).trans
    (isConj_of_involutions_odd_product z (w*t*w⁻¹) hz hwt
      (hn.of_dvd_nat (orderOf_dvd_of_pow_eq_one hp))).symm

private theorem outside_middle_second (i : Fin 10) (h0 : i ≠ 0) (h9 : i ≠ 9) :
    IsConj (word (Simplicity.a matrixA_mul_self) (Simplicity.b matrixB_pow_four) "ababb" ^ 5) (outsideRepresentative matrixA_mul_self matrixB_pow_four i : Model) := by
  have ht : (word (Simplicity.a matrixA_mul_self) (Simplicity.b matrixB_pow_four) "ababb" ^ 5) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (primeRepresentative (Simplicity.a matrixA_mul_self) (Simplicity.b matrixB_pow_four) 1)
    rw [involutionRepresentative_one_orderOf matrixA_mul_self matrixB_pow_four] at h
    exact h
  fin_cases i
  · exact (h0 rfl).elim
  · exact isConj_of_odd_product _ _ _ 43 (square_1 _ _) ht (by decide) (odd_product_1 _ _)
  · exact isConj_of_odd_product _ _ _ 15 (square_2 _ _) ht (by decide) (odd_product_2 _ _)
  · exact isConj_of_odd_product _ _ _ 43 (square_3 _ _) ht (by decide) (odd_product_3 _ _)
  · exact isConj_of_odd_product _ _ 1 43 (square_4 _ _) ht (by decide)
      (by rw [one_mul,inv_one,mul_one]; exact odd_product_4 matrixA_mul_self matrixB_pow_four)
  · exact isConj_of_odd_product _ _ _ 11 (square_5 _ _) ht (by decide) (odd_product_5 _ _)
  · exact isConj_of_odd_product _ _ _ 29 (square_6 _ _) ht (by decide) (odd_product_6 _ _)
  · exact isConj_of_odd_product _ _ 1 31 (square_7 _ _) ht (by decide)
      (by rw [one_mul,inv_one,mul_one]; exact odd_product_7 matrixA_mul_self matrixB_pow_four)
  · exact isConj_of_odd_product _ _ 1 43 (square_8 _ _) ht (by decide)
      (by rw [one_mul,inv_one,mul_one]; exact odd_product_8 matrixA_mul_self matrixB_pow_four)
  · exact (h9 rfl).elim

/-- Ambient first-class fusion singles out the two actual lifts, not just
one of the two quotient involution classes. -/
theorem outside_first_iff (i : Fin 10) :
    IsConj a (outsideRepresentative matrixA_mul_self matrixB_pow_four i : Model) ↔
      i = 0 ∨ i = 9 := by
  constructor
  · intro hfirst
    by_contra h
    have hi := not_or.mp h
    obtain ⟨g,hg⟩ := seed_fuses_second matrixA_mul_self matrixB_pow_four
    apply first_not_isConj_second
    exact (hfirst.trans (outside_middle_second i hi.1 hi.2).symm).trans
      (isConj_iff.mpr ⟨g,hg.symm⟩).symm
  · rintro (rfl | rfl)
    · have he : outsideRepresentative matrixA_mul_self matrixB_pow_four 0 =
          localX matrixA_mul_self matrixB_pow_four := by
        simp [outsideRepresentative,outsideMask,binaryProduct_zero]
      rw [he]
      obtain ⟨g,hg⟩ := localX_fuses_first matrixA_mul_self matrixB_pow_four
      exact (isConj_iff.mpr ⟨g,hg.symm⟩).symm
    · exact isConj_of_odd_product _ _ _ 11 (square_9 _ _)
        (by simpa only [pow_two] using a_pow_two) (by decide) (odd_product_9 _ _)

/-- Each first-class involution outside E is locally conjugate to one of the
two certified first-class lifts in the complete max1 census. -/
theorem first_lift_normal_form (z : M) (hk : z ∉ max1Kernel)
    (hz : IsConj a (z : Model)) :
    ∃ (i : Fin 10) (g : M), (i = 0 ∨ i = 9) ∧
      (MulAut.conj g) z = outsideRepresentative matrixA_mul_self matrixB_pow_four i := by
  have ho : orderOf (z : Model) = 2 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hz
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq a).trans orderOf_a
  have hol : orderOf z = 2 := (orderOf_injective M.subtype M.subtype_injective z).symm.trans ho
  obtain ⟨i,g,hg⟩ := outside_coverage_of_quotient_and_fibers
    matrixA_mul_self matrixB_pow_four
    (quotient_involution_coverage _ _) (involution_fibers _ _) z hk hol
  have hrep : IsConj a (outsideRepresentative matrixA_mul_self matrixB_pow_four i : Model) :=
    hz.trans (isConj_iff.mpr ⟨(g : Model),congrArg (fun u : M => (u : Model)) hg.symm⟩)
  exact ⟨i,g,(outside_first_iff i).mp hrep,hg.symm⟩

namespace LiftCoordinates
open KernelCount Simplicity.Max1Fusion.KernelOrbits Simplicity.Max1Fusion.InvolutionFibers
variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
attribute [local irreducible] basis localX localY localKernelSeed

private abbrev E (m : ℕ) : max1Subgroup hA hB := maskValue hA hB m

private theorem E_xor (m n : ℕ) : E hA hB (Nat.xor m n) = E hA hB m * E hA hB n :=
  congrArg Subtype.val (maskValue_xor hA hB m n)
private theorem E_zero : E hA hB 0 = 1 := congrArg Subtype.val (maskValue_zero hA hB)
private theorem E_square (m : ℕ) : E hA hB m * E hA hB m = 1 := by
  rw [← E_xor, show Nat.xor m m = 0 from Nat.xor_self m, E_zero]
private theorem E_inv (m : ℕ) : (E hA hB m)⁻¹ = E hA hB m := by
  exact inv_eq_of_mul_eq_one_left (E_square hA hB m)

private theorem E_injective {m n : ℕ} (hm : m < 2048) (hn : n < 2048)
    (h : E hA hB m = E hA hB n) : m = n := by
  have hb := coordinates_injective hA hB (Subtype.ext h : maskValue hA hB m = maskValue hA hB n)
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 11
  · exact congrFun hb ⟨j, hj⟩
  · have hp : 2^11 ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm hp),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hn hp)]

private theorem right_conj_xy_pow (n m : ℕ) :
    ((localX hA hB * localY hA hB)^n)⁻¹ * E hA hB m *
      (localX hA hB * localY hA hB)^n = E hA hB ((xyAction^[n]) m) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    calc
      _ = (localY hA hB)⁻¹ * ((localX hA hB)⁻¹ *
        (((localX hA hB * localY hA hB)^n)⁻¹ * E hA hB m *
          (localX hA hB * localY hA hB)^n) * localX hA hB) * localY hA hB := by group
      _ = E hA hB ((xyAction^[n+1]) m) := by
        rw [ih, right_conj_mask_x, right_conj_mask_y]
        exact congrArg (E hA hB) (Function.iterate_succ_apply' xyAction n m).symm

private theorem right_conj_q (m : ℕ) :
    ((localX hA hB * localY hA hB)^7)⁻¹ * E hA hB m *
      (localX hA hB * localY hA hB)^7 = E hA hB (maskImage qMasks m) := by
  have hb (i : Fin 11) :
      ((localX hA hB * localY hA hB)^7)⁻¹ * basis hA hB i *
        (localX hA hB * localY hA hB)^7 = E hA hB (qMasks i) := by
    rw [← maskValue_basis hA hB i, right_conj_xy_pow, qMasks_basis]
  rw [show E hA hB (maskImage qMasks m) = _ from maskValue_maskImage hA hB qMasks m]
  have h := map_binaryProduct (MulAut.conj ((localX hA hB * localY hA hB)^7)⁻¹).toMonoidHom
    (basis hA hB) (fun i => m.testBit i.val)
  change ((localX hA hB * localY hA hB)^7)⁻¹ * _ *
    (((localX hA hB * localY hA hB)^7)⁻¹)⁻¹ =
      binaryProduct (fun i => ((localX hA hB * localY hA hB)^7)⁻¹ *
        basis hA hB i * (((localX hA hB * localY hA hB)^7)⁻¹)⁻¹)
        (fun i => m.testBit i.val) at h
  simpa only [inv_inv, hb, E, maskValue, coordinates_val] using h

private def base (b : Bool) : max1Subgroup hA hB :=
  if b then (localX hA hB * localY hA hB)^7 else localX hA hB

private theorem right_conj_base (b : Bool) (m : ℕ) :
    (base hA hB b)⁻¹ * E hA hB m * base hA hB b =
      E hA hB (maskImage (actionMasks b) m) := by
  cases b
  · exact right_conj_mask_x hA hB m
  · exact right_conj_q hA hB m

private theorem base_square (b : Bool) :
    base hA hB b * base hA hB b = E hA hB (squareMask b) := by
  cases b
  · exact (localX_mul_self hA hB).trans (E_zero hA hB).symm
  · change ((localX hA hB * localY hA hB)^7) *
      ((localX hA hB * localY hA hB)^7) = E hA hB 1
    rw [← pow_two, ← pow_mul]
    simpa only [localKernelSeed] using (maskValue_one hA hB).symm

private theorem square_equation (b : Bool) (m : Fin 2048)
    (h : (base hA hB b * E hA hB m.val)^2 = 1) :
    Nat.xor (maskImage (actionMasks b) m.val) m.val = squareMask b := by
  have hs : E hA hB (squareMask b) *
      E hA hB (Nat.xor (maskImage (actionMasks b) m.val) m.val) = 1 := by
    rw [E_xor, ← right_conj_base, ← base_square]
    calc
      _ = (base hA hB b * E hA hB m.val)^2 := by simp only [pow_two]; group
      _ = 1 := h
  have he : E hA hB (Nat.xor (maskImage (actionMasks b) m.val) m.val) =
      E hA hB (squareMask b) := by
    calc
      _ = E hA hB (squareMask b) * (E hA hB (squareMask b) *
          E hA hB (Nat.xor (maskImage (actionMasks b) m.val) m.val)) := by
        rw [← mul_assoc, E_square, one_mul]
      _ = _ := by rw [hs, mul_one]
  exact E_injective hA hB (square_bound b m) (by cases b <;> decide) he

private theorem kernel_conjugate (b : Bool) (m n : ℕ) :
    E hA hB n * (base hA hB b * E hA hB m) * (E hA hB n)⁻¹ =
      base hA hB b * E hA hB
        (Nat.xor (Nat.xor (maskImage (actionMasks b) n) m) n) := by
  rw [E_xor, E_xor, ← right_conj_base, E_inv]
  group

private theorem representative_eq (b : Bool) (i : Fin 10) (hi : i.val < 2 ↔ b = false) :
    outsideRepresentative hA hB i = base hA hB b * E hA hB (outsideMask i) := by
  cases b <;> simp_all [outsideRepresentative, base, E, maskValue]

end LiftCoordinates

open Simplicity.Max1Fusion.InvolutionFibers

private theorem first_q_mask (m : Fin 2048)
    (hs : (((localX matrixA_mul_self matrixB_pow_four * localY matrixA_mul_self matrixB_pow_four)^7 *
      kernelValue m.val : M) : Model)^2 = 1)
    (hp : IsConj a (((localX matrixA_mul_self matrixB_pow_four * localY matrixA_mul_self matrixB_pow_four)^7 *
      kernelValue m.val : M) : Model)) : (witness true m.val).1 = 9 ∧
      Nat.xor (maskImage qMasks m.val) m.val = 1 := by
  have hs' : (LiftCoordinates.base matrixA_mul_self matrixB_pow_four true *
      LiftCoordinates.E matrixA_mul_self matrixB_pow_four m.val)^2 = 1 := Subtype.ext hs
  have heq := LiftCoordinates.square_equation matrixA_mul_self matrixB_pow_four true m hs'
  refine ⟨?_,heq⟩
  obtain ⟨hi,he⟩ := reduction true m heq
  have hc := LiftCoordinates.kernel_conjugate matrixA_mul_self matrixB_pow_four
    true m.val (witness true m.val).2
  rw [he,← LiftCoordinates.representative_eq matrixA_mul_self matrixB_pow_four true _ hi] at hc
  have hc' := congrArg (fun u : M => (u : Model)) hc
  have hh : IsConj a (outsideRepresentative matrixA_mul_self matrixB_pow_four (witness true m.val).1 : Model) :=
    hp.trans (isConj_iff.mpr ⟨(kernelValue (witness true m.val).2 : Model),hc'⟩)
  rcases (outside_first_iff _).mp hh with h | h
  · rw [h] at hi
    have hn := hi.mp (by decide)
    cases hn
  · exact h

private theorem kernel_pair_not_first (u v : Fin 24) (huv : u ≠ v) :
    ¬ IsConj a (kernelValue (pairLabel u v) : Model) := by
  open Simplicity.Max1Fusion.KernelOrbits in
  have hn : kernelValue (pairLabel u v) ≠ 1 := by
    intro he
    exact huv ((pairLabel_eq_zero_iff u v).mp (kernelValue_injective
      (pairLabel_lt u v) (by decide) (he.trans kernelValue_zero.symm)))
  open Simplicity.Max1Fusion.KernelOrbits in
  obtain ⟨g,hg | hg⟩ := kernel_nonidentity_orbits matrixA_mul_self matrixB_pow_four
    (kernelValue (pairLabel u v)) (maskValue _ _ _).property hn
  · intro hf
    apply first_not_isConj_second
    exact hf.trans (isConj_iff.mpr ⟨(g : Model),congrArg (fun x : M => (x : Model)) hg.symm⟩)
  · open Simplicity.Max1Fusion.KernelOrbits in
    have he : kernelValue (pairLabel ((starHom g).val u) ((starHom g).val v)) = kernelValue 3 :=
      (congrArg Subtype.val (starHom_pair g u v)).symm.trans
        (hg.symm.trans (maskValue_three _ _).symm)
    open Simplicity.Max1Fusion.KernelOrbits in
    have hl := kernelValue_injective (pairLabel_lt _ _) (by decide) he
    open Simplicity.Max1Fusion.KernelOrbits in
    have hh : ∀ i j : Fin 24, pairLabel i j ≠ 3 := by decide +kernel
    exact (hh _ _ hl).elim

/-- The seven nonidentity kernel coordinates which can occur in a pure
extension containing the actual ninth outside lift. -/
@[expose] def ninthPureMask : Fin 7 → ℕ := ![457,641,840,1098,1411,1739,1794]

/-- Purity of both a kernel element and its product with the actual lift
restricts the kernel element to seven literal binary masks. -/
theorem ninth_pure_kernel_mask (m : Fin 2048)
    (hm : IsConj a (kernelValue m.val : Model))
    (hp : IsConj a ((outsideRepresentative matrixA_mul_self matrixB_pow_four 9 *
      kernelValue m.val : M) : Model))
    (hs : ((outsideRepresentative matrixA_mul_self matrixB_pow_four 9 *
      kernelValue m.val : M) : Model)^2 = 1) :
    ∃ j : Fin 7, m.val = ninthPureMask j := by
  have hb : Nat.xor 254 m.val < 2048 := by
    have h : ∀ m : Fin 2048, Nat.xor 254 m.val < 2048 := by decide +kernel
    exact h m
  let n : Fin 2048 := ⟨Nat.xor 254 m.val,hb⟩
  have he : outsideRepresentative matrixA_mul_self matrixB_pow_four 9 * kernelValue m.val =
      (localX matrixA_mul_self matrixB_pow_four * localY matrixA_mul_self matrixB_pow_four)^7 * kernelValue n.val := by
    unfold outsideRepresentative
    change (_ * kernelValue 254) * kernelValue m.val = _
    rw [mul_assoc,← kernelValue_xor]
    rfl
  have hn := first_q_mask n (by simpa only [he] using hs) (by simpa only [he] using hp)
  have h0 : m.val ≠ 0 := by
    intro h
    rw [h,kernelValue_zero] at hm
    have ha : a ≠ 1 := by
      intro ha
      have ho := orderOf_a
      rw [ha,orderOf_one] at ho
      contradiction
    exact ha (isConj_one_left.mp hm)
  have hpair : ∀ i j : Fin 24, i ≠ j → pairLabel i j ≠ m.val := by
    intro i j hij he
    exact kernel_pair_not_first i j hij (he ▸ hm)
  have sieve : ∀ m : Fin 2048, m.val ≠ 0 →
      (witness true (Nat.xor 254 m.val)).1 = 9 →
      Nat.xor (maskImage qMasks (Nat.xor 254 m.val)) (Nat.xor 254 m.val) = 1 →
      (∀ i j : Fin 24, i ≠ j → pairLabel i j ≠ m.val) →
      ∃ j : Fin 7, m.val = ninthPureMask j := by decide +kernel
  exact sieve m h0 hn.1 hn.2 hpair

/-- In a maximal pure extension, a genuine element outside E supplies the
lift normal form. The same conjugator carries the pair, the whole extension,
and both whole ambient local groups. -/
theorem maximal_pure_extension_lift_positioning (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    ∃ (i : Fin 10) (g : M), (i = 0 ∨ i = 9) ∧
      let Y := X.map (MulAut.conj (g : Model)).toMonoidHom
      nativePair.map (MulAut.conj (g : Model)).toMonoidHom ≤ Y ∧
      Y ≤ M ∧ centralizer (Y : Set Model) ≤ M ∧
      (outsideRepresentative matrixA_mul_self matrixB_pow_four i : Model) ∈ Y ∧
      (∀ y ∈ Y, y ≠ 1 → IsConj a y) ∧
      IsMaximalTwoLocal (normalizer (Y : Set Model)) ∧
      centralizer (Y : Set Model) = (centralizer (X : Set Model)).map
        (MulAut.conj (g : Model)).toMonoidHom ∧
      normalizer (Y : Set Model) = (normalizer (X : Set Model)).map
        (MulAut.conj (g : Model)).toMonoidHom := by
  have hXM := elementary_overgroup_placement X hpair
  have hn : ¬ X ≤ embeddedKernel := by
    intro hk
    exact maximal_pure_extension_image_ne_bot X hpair hpure hmax ((image_eq_bot_iff X hpair).mpr hk)
  obtain ⟨x,hx,hxk⟩ := SetLike.not_le_iff_exists.mp hn
  let z : M := ⟨x,hXM.1 hx⟩
  have hzk : z ∉ max1Kernel := fun hh => hxk (mem_map_of_mem M.subtype hh)
  have hx1 : x ≠ 1 := fun he => hxk (he ▸ embeddedKernel.one_mem)
  obtain ⟨i,g,hi,hg⟩ := first_lift_normal_form z hzk (hpure x hx hx1)
  have hM : M.map (MulAut.conj (g : Model)).toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer g.property)
  refine ⟨i,g,hi,map_mono hpair,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (map_mono hXM.1).trans hM.le
  · have hc := map_mono (f := (MulAut.conj (g : Model)).toMonoidHom) hXM.2
    rw [map_centralizer_equiv] at hc
    exact hc.trans hM.le
  · have he := congrArg (fun u : M => (u : Model)) hg
    exact he ▸ mem_map_of_mem (MulAut.conj (g : Model)).toMonoidHom hx
  · rintro y ⟨v,hv,rfl⟩ hy
    exact (hpure v hv (fun he => hy (by rw [he,map_one]))).trans
      (isConj_iff.mpr ⟨(g : Model),rfl⟩)
  · rw [← map_equiv_normalizer_eq]
    exact isMaximalTwoLocal_map (MulAut.conj (g : Model)) hmax
  · exact (map_centralizer_equiv (X : Set Model) (MulAut.conj (g : Model))).symm
  · exact (map_equiv_normalizer_eq X (MulAut.conj (g : Model))).symm

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
