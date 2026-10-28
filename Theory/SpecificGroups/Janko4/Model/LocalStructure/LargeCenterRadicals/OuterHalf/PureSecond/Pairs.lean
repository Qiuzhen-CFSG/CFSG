module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.PureSecond.Data
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.PureSecond.Bridge
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion
import Mathlib.Tactic.Group

/-!
# Pure second-class comparisons via first-class bridges

The existing max1 involution census reduces the second member to ten words.
For a fixed kernel involution, the certified binary masks provide a commuting
first-class element whose products with both members are first-class. Row
linearity and the already proved mixed comparisons settle the original pair.
All conjugations use the actual eleven-coordinate kernel and ATLAS generators.
Source: Kleidman--Wilson (1988), p.487, Corollary 1.1.4.
-/

set_option backward.isDefEq.respectTransparency true
public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.LargeCenterRadicals.OuterHalf.PureSecond
open Janko4.Cardinality Janko4.Cardinality.KernelCount Janko4.Cardinality.QuotientCount.Image
open Janko4.Simplicity.Max1Fusion KernelOrbits InvolutionFibers PureSecondData
open Janko4.InvolutionCentralizers.Second
attribute [local irreducible] basis modelGroup matrixA matrixB localKernel
  max1Subgroup localX localY localKernelSeed

private abbrev E (m : ℕ) : InvolutionCentralizers.Second.Local :=
  maskValue matrixA_mul_self matrixB_pow_four m
private abbrev R (i : Fin 10) : InvolutionCentralizers.Second.Local :=
  outsideRepresentative matrixA_mul_self matrixB_pow_four i

private theorem E_xor (m n : ℕ) : E (Nat.xor m n) = E m * E n :=
  congrArg Subtype.val (maskValue_xor matrixA_mul_self matrixB_pow_four m n)
private theorem E_zero : E 0 = 1 := congrArg Subtype.val (maskValue_zero _ _)
private theorem E_square (m : ℕ) : E m * E m = 1 := by
  rw [← E_xor, show Nat.xor m m = 0 from Nat.xor_self m, E_zero]
private theorem E_inv (m : ℕ) : (E m)⁻¹ = E m :=
  inv_eq_of_mul_eq_one_left (E_square m)
private theorem E_comm (m n : ℕ) : Commute (E m) (E n) := by
  change E m * E n = E n * E m
  rw [← E_xor, ← E_xor, show Nat.xor m n = Nat.xor n m from Nat.xor_comm m n]
private theorem E_injective {m n : ℕ} (hm : m < 2048) (hn : n < 2048)
    (he : E m = E n) : m = n := by
  exact congrArg Fin.val (Janko4.Max1RelativeRigidity.maskValue_injective
    (a₁ := ⟨m, hm⟩) (a₂ := ⟨n, hn⟩) (Subtype.ext he))

private theorem E_root (m : Fin 2048) : IsConj (E m.val) (E (orbitRoot m.val)) := by
  suffices ∀ d (m : Fin 2048), depth m = d → IsConj (E m.val) (E (orbitRoot m.val)) from
    this (depth m) m rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro m hm
    rcases tree_certificate m with h0 | h1 | h3 | ⟨hd, he⟩
    · subst m; exact IsConj.refl _
    · subst m; exact IsConj.refl _
    · subst m; exact IsConj.refl _
    · have hc : IsConj (E (parent m).val) (E m.val) := by
        rcases he with hx | hy
        · exact isConj_iff.mpr ⟨(localX matrixA_mul_self matrixB_pow_four)⁻¹, by
            simpa only [inv_inv, hx] using right_conj_mask_x matrixA_mul_self matrixB_pow_four (parent m).val⟩
        · exact isConj_iff.mpr ⟨(localY matrixA_mul_self matrixB_pow_four)⁻¹, by
            simpa only [inv_inv, hy] using right_conj_mask_y matrixA_mul_self matrixB_pow_four (parent m).val⟩
      have hp := ih (depth (parent m)) (hd.trans_eq hm) (parent m) rfl
      rw [(root_valid m).2.2] at hp
      exact hc.symm.trans hp

private theorem E_first (m : Fin 2048) (hm : orbitRoot m.val = 3) :
    IsConj Janko4.a (E m.val : Model) := by
  have hr := E_root m
  rw [hm, show E 3 = kernelPair matrixA_mul_self matrixB_pow_four from maskValue_three _ _] at hr
  obtain ⟨g, hg⟩ := isConj_iff.mp hr
  obtain ⟨k, hk⟩ := pair_fuses_first matrixA_mul_self matrixB_pow_four
  exact (isConj_iff.mpr ⟨(g : Model), congrArg Subtype.val hg⟩ |>.trans
    (isConj_iff.mpr ⟨k, hk.symm⟩)).symm

private theorem right_conj_xy_pow (n m : ℕ) :
    ((localX matrixA_mul_self matrixB_pow_four * localY matrixA_mul_self matrixB_pow_four)^n)⁻¹ * E m *
      (localX matrixA_mul_self matrixB_pow_four * localY matrixA_mul_self matrixB_pow_four)^n =
        E ((xyAction^[n]) m) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    calc
      _ = (localY matrixA_mul_self matrixB_pow_four)⁻¹ * ((localX matrixA_mul_self matrixB_pow_four)⁻¹ *
        (((localX matrixA_mul_self matrixB_pow_four * localY matrixA_mul_self matrixB_pow_four)^n)⁻¹ * E m *
          (localX matrixA_mul_self matrixB_pow_four * localY matrixA_mul_self matrixB_pow_four)^n) *
            localX matrixA_mul_self matrixB_pow_four) * localY matrixA_mul_self matrixB_pow_four := by group
      _ = E ((xyAction^[n+1]) m) := by
        rw [ih, right_conj_mask_x, right_conj_mask_y]
        exact congrArg E (Function.iterate_succ_apply' xyAction n m).symm

private theorem right_conj_q (m : ℕ) :
    ((localX matrixA_mul_self matrixB_pow_four * localY matrixA_mul_self matrixB_pow_four)^7)⁻¹ * E m *
      (localX matrixA_mul_self matrixB_pow_four * localY matrixA_mul_self matrixB_pow_four)^7 =
        E (maskImage qMasks m) := by
  have hb (i : Fin 11) :
      ((localX matrixA_mul_self matrixB_pow_four * localY matrixA_mul_self matrixB_pow_four)^7)⁻¹ *
        basis matrixA_mul_self matrixB_pow_four i *
        (localX matrixA_mul_self matrixB_pow_four * localY matrixA_mul_self matrixB_pow_four)^7 = E (qMasks i) := by
    rw [← maskValue_basis matrixA_mul_self matrixB_pow_four i, right_conj_xy_pow, qMasks_basis]
  rw [show E (maskImage qMasks m) = _ from maskValue_maskImage _ _ qMasks m]
  have h := map_binaryProduct
    (MulAut.conj ((localX matrixA_mul_self matrixB_pow_four * localY matrixA_mul_self matrixB_pow_four)^7)⁻¹).toMonoidHom
    (basis matrixA_mul_self matrixB_pow_four) (fun i => m.testBit i.val)
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hb,
    E, maskValue, coordinates_val] using h

private def base (i : Fin 10) : InvolutionCentralizers.Second.Local :=
  if i.val < 2 then localX matrixA_mul_self matrixB_pow_four
  else (localX matrixA_mul_self matrixB_pow_four * localY matrixA_mul_self matrixB_pow_four)^7

private theorem R_eq (i : Fin 10) : R i = base i * E (outsideMask i) := rfl

private theorem right_conj_base (i : Fin 10) (m : ℕ) :
    (base i)⁻¹ * E m * base i = E (action i m) := by
  by_cases hi : i.val < 2
  · have hd : decide (2 ≤ i.val) = false := by simp [show ¬ 2 ≤ i.val by omega]
    simpa only [base, hi, if_pos, action, hd, actionMasks, Bool.false_eq_true, if_false] using
      right_conj_mask_x matrixA_mul_self matrixB_pow_four m
  · have hd : decide (2 ≤ i.val) = true := by simp [show 2 ≤ i.val by omega]
    simpa only [base, hi, if_false, action, hd, actionMasks, if_true] using right_conj_q m

private theorem right_conj_R (i : Fin 10) (m : ℕ) :
    (R i)⁻¹ * E m * R i = E (action i m) := by
  rw [R_eq]
  calc
    _ = (E (outsideMask i))⁻¹ * ((base i)⁻¹ * E m * base i) * E (outsideMask i) := by group
    _ = E (action i m) := by
      rw [right_conj_base, (E_comm (outsideMask i) (action i m)).inv_left.eq]
      simp

private theorem fixed_of_commute (i : Fin 10) (m : Fin 2048)
    (hc : Commute (R i) (E m.val)) : action i m.val = m.val := by
  apply E_injective (action_bound i m) m.isLt
  rw [← right_conj_R, hc.inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]

private theorem commute_of_fixed (i : Fin 10) (n : ℕ) (hn : action i n = n) :
    Commute (R i) (E n) := by
  have h := right_conj_R i n
  rw [hn] at h
  have he := congrArg (R i * ·) h
  change R i * E n = E n * R i
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using he.symm

private theorem kernel_conjugate (i : Fin 10) (m k : ℕ) :
    E k * (base i * E m) * (E k)⁻¹ =
      base i * E (Nat.xor (Nat.xor (action i k) m) k) := by
  rw [E_xor, E_xor, ← right_conj_base, E_inv]
  group

private theorem R_zero_first : IsConj Janko4.a (R 0 : Model) := by
  have he : R 0 = localX matrixA_mul_self matrixB_pow_four := by
    change outsideRepresentative _ _ 0 = _
    simp [outsideRepresentative, outsideMask, binaryProduct_zero]
  rw [he]
  obtain ⟨g, hg⟩ := localX_fuses_first matrixA_mul_self matrixB_pow_four
  exact (isConj_iff.mpr ⟨g, hg.symm⟩).symm

private theorem R_nine_first : IsConj Janko4.a (R 9 : Model) := by
  open Janko4.Simplicity.Max1Fusion.OutsideWordCertificates in
  have hp := odd_product_9 matrixA_mul_self matrixB_pow_four
  have ha2 : Janko4.a ^ 2 = 1 := by simpa only [orderOf_a] using pow_orderOf_eq_one Janko4.a
  have ht : (Janko4.b * Janko4.a * Janko4.b⁻¹)^2 = 1 := by
    simpa only [map_pow, map_one, MulAut.conj_apply] using
      congrArg (MulAut.conj Janko4.b) ha2
  have hp' : ((R 9 : Model) * (Janko4.b * Janko4.a * Janko4.b⁻¹)) ^ 11 = 1 := by
    have ha : Simplicity.a matrixA_mul_self = Janko4.a := by apply toMatrix_injective; rfl
    have hb : Simplicity.b matrixB_pow_four = Janko4.b := by apply toMatrix_injective; rfl
    simpa [Simplicity.word, ha, hb] using hp
  have hc := isConj_of_involutions_odd_product (R 9 : Model)
    (Janko4.b * Janko4.a * Janko4.b⁻¹)
    (Janko4.Simplicity.Max1Fusion.OutsideWordCertificates.square_9 _ _) ht
    ((show Odd (11 : ℕ) by decide).of_dvd_nat (orderOf_dvd_of_pow_eq_one hp'))
  exact (isConj_iff.mpr ⟨Janko4.b, rfl⟩).trans hc.symm

private theorem R_target_first (i : Fin 10) : IsConj Janko4.a (R (target i) : Model) := by
  unfold target
  split_ifs
  · exact R_zero_first
  · exact R_nine_first

private theorem shifted_first (i : Fin 10) (n k : ℕ)
    (he : Nat.xor (Nat.xor (action i k) (Nat.xor (outsideMask i) n)) k = outsideMask (target i)) :
    IsConj Janko4.a ((R i * E n : InvolutionCentralizers.Second.Local) : Model) := by
  have hb : base i = base (target i) := by
    by_cases hi : i.val < 2 <;> simp [base, target, hi]
  have hh : E k * (R i * E n) * (E k)⁻¹ = R (target i) := by
    rw [R_eq, mul_assoc (base i), ← E_xor, kernel_conjugate, he, hb, ← R_eq]
  exact (R_target_first i).trans
    (isConj_iff.mpr ⟨(E k : Model), congrArg Subtype.val hh⟩).symm

/-- Every outside census word has symmetric intrinsic residual membership
with every commuting nonidentity element of the actual elementary kernel. -/
theorem outside_kernel_symmetry (i : Fin 10) (m : Fin 2048)
    (hx : orderOf (((maskValue matrixA_mul_self matrixB_pow_four m.val).val) : Model) = 2)
    (hy : orderOf (outsideRepresentative matrixA_mul_self matrixB_pow_four i : Model) = 2)
    (hc : Commute (((maskValue matrixA_mul_self matrixB_pow_four m.val).val) : Model)
      (outsideRepresentative matrixA_mul_self matrixB_pow_four i : Model)) :
    InnerRelated (((maskValue matrixA_mul_self matrixB_pow_four m.val).val) : Model)
      (outsideRepresentative matrixA_mul_self matrixB_pow_four i : Model) ↔
    InnerRelated (outsideRepresentative matrixA_mul_self matrixB_pow_four i : Model)
      (((maskValue matrixA_mul_self matrixB_pow_four m.val).val) : Model) := by
  change InnerRelated (E m.val : Model) (R i : Model) ↔ InnerRelated (R i : Model) (E m.val : Model)
  by_cases hi0 : i = 0
  · subst i
    exact (innerRelated_symm_of_first _ _ R_zero_first hx hc.symm).symm
  by_cases hi9 : i = 9
  · subst i
    exact (innerRelated_symm_of_first _ _ R_nine_first hx hc.symm).symm
  rcases (root_valid m).1 with hm0 | hm1 | hm3
  · have hm : m = 0 := (root_valid m).2.1.mp hm0
    subst m
    have he : (E 0 : Model) = 1 := congrArg Subtype.val E_zero
    change orderOf (E 0 : Model) = 2 at hx
    simp [he] at hx
  · have hfix := fixed_of_commute i m (Subtype.ext hc.symm.eq)
    obtain ⟨hn, hk, hmn, hnr, hmnr, hnf, he⟩ := bridge_valid i m hm1 hi0 hi9 hfix
    let n := (bridge i m.val).1
    have hcn : Commute (R i) (E n) := commute_of_fixed i n hnf
    exact innerRelated_symm_of_first_bridge _ _ (E n : Model) hx hy hc
      (congrArg Subtype.val (E_comm m.val n).eq)
      (congrArg Subtype.val hcn.eq)
      (E_first ⟨n, hn⟩ hnr)
      (by simpa only [E_xor, Subgroup.coe_mul] using E_first ⟨Nat.xor m.val n, hmn⟩ hmnr)
      (shifted_first i n (bridge i m.val).2 he)
  · exact innerRelated_symm_of_first _ _ (E_first m hm3) hy hc

end Janko4.LocalStructure.LargeCenterRadicals.OuterHalf.PureSecond
