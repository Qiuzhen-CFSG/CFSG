module
public import Theory.SpecificGroups.SU3.SylowOmega
public import Theory.SpecificGroups.SU3.BinarySylowOrder
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic.Order
public import Theory.SpecificGroups.SL2.TwoSubgroupExponent
public import Theory.SpecificGroups.Suzuki.LinearSeparation
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import CFSG.Quasithin.ClassicalModels
public import Theory.GroupTheory.GeneralizedFitting.Defs

/-!
# Separating the normalized rank-one models from the 4.4.3 exceptions

Binary Hermitian root groups have nontrivial squares, whereas every two-subgroup
of binary PSL₂ has exponent two. Suzuki groups have order prime to three,
whereas every binary PSL₂ contains an element of order three. The exact matrix
orders put both families above all the remaining exceptional quotients.

The exclusion is formulated on the actual central quotient, so it also applies
to central covers and to inclusion-induced quotients of covering residuals.
The final lemma eliminates precisely the quotient list of source 4.4.3(2).
Source: Aschbacher--Smith, printed p.619; the imported root and order calculations
use Huppert II.10.12 and Huppert--Blackburn III.XI.3.3.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
open HermitianForm.OddPrimeSylow.NormalizedOuter

/-- A binary unitary root group has elements whose square is nontrivial. -/
private theorem unitary_root_not_exponent_two {F : Type*} [Field F] [Finite F] [CharP F 2]
    (J : HermitianForm 3 F) {q : ℕ} (hc : Nat.card F = q ^ 2)
    (hf : Nat.card {x : F // J.conj x = x} = q) :
    ¬ ∀ x : BenderSuzuki.External.hermitianUnipotentCoord J, x ^ 2 = 1 := by
  intro hx
  obtain ⟨x,hx1⟩ := HermitianForm.EvenSemilinear.coord_first_surjective J hc hf (1 : F)
  have hz := (HermitianForm.EvenSemilinear.square_eq_one_iff_first_zero J x).mp (hx x)
  exact one_ne_zero (hx1.symm.trans hz)

/-- A projective unitary group in characteristic two cannot be a binary PSL₂. -/
theorem unitary_not_binary_linear_two {Q : Type*} [Group Q]
    {s : ℕ} (hs : 2 ≤ s) (hu : ClassicalGroup.IsPSU Q 3 (2 ^ s)) (n : ℕ) :
    ¬ ClassicalGroup.IsPSL Q 2 (2 ^ n) := by
  rintro ⟨E,hE,hEf,hEc,⟨e⟩⟩
  obtain ⟨F,hF,hFf,J,hFc,hconj,⟨u⟩⟩ := hu
  let : Fintype E := Fintype.ofFinite E
  let : Fintype F := Fintype.ofFinite F
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hEc)
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := s * 2) (by
    simpa only [Nat.card_eq_fintype_card, pow_mul] using hFc)
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 s (by omega) hFc hconj
  obtain ⟨t⟩ := FormTransport.exists_projectiveEquiv J (2 ^ s) hFc hf
  let K := FormTransport.standardForm J
  let f := (e.symm.trans (u.trans t)).symm.trans (Theory.PSL2.sl2QuotientEquiv E).symm
  let g := f.toMonoidHom.comp (BenderSuzuki.External.hermitianUnipotentPSU K rfl)
  have hg : Function.Injective g := f.injective.comp (HermitianForm.EvenInner.root_injective K rfl)
  have hp : IsPGroup 2 (BenderSuzuki.External.hermitianUnipotentCoord K) := by
    intro x
    refine ⟨2,?_⟩
    have hz : (x ^ 2) ^ 2 = 1 :=
      (HermitianForm.EvenSemilinear.square_eq_one_iff_first_zero K _).mpr (by
        rw [HermitianForm.EvenInner.square_coordinates])
    simpa only [← pow_mul, show 2 * 2 = 2 ^ 2 from rfl] using hz
  apply unitary_root_not_exponent_two K hFc hf
  intro x
  have hh := Matrix.SpecialLinearGroup.twoSubgroup_pow_two g.range
    (hp.of_surjective g.rangeRestrict g.rangeRestrict_surjective) (g.rangeRestrict x)
  have hh' : g x ^ 2 = 1 := congrArg g.range.subtype hh
  apply hg
  rw [map_pow,map_one]
  exact hh'


/-- The Suzuki order is prime to three, unlike every binary PSL₂. -/
theorem suzuki_not_binary_linear_two {Q : Type*} [Group Q]
    {m : ℕ} (hm : 1 ≤ m) (e : Q ≃* SuzukiMatrixGroup m) (n : ℕ) :
    ¬ ClassicalGroup.IsPSL Q 2 (2 ^ n) := by
  rintro ⟨F,hF,hfin,hcard,⟨f⟩⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  exact not_nonempty_psl2_char_two_equiv_suzuki F (by omega) ⟨f.symm.trans e⟩

/-- Even the crude scalar-kernel bound puts all these unitary groups above A₈. -/
theorem unitary_card_gt_20160 {Q : Type*} [Group Q]
    {s : ℕ} (hs : 2 ≤ s) (hu : ClassicalGroup.IsPSU Q 3 (2 ^ s)) :
    20160 < Nat.card Q := by
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hu
  rw [Nat.card_congr e.toEquiv,
    HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic.card_projective
      J hcard hconj]
  have hq : 4 ≤ 2 ^ s := Nat.pow_le_pow_right (n := 2) (by decide) hs
  have hnum : 62400 ≤ ((2 ^ s) ^ 3 + 1) * (2 ^ s) ^ 3 * ((2 ^ s) ^ 2 - 1) :=
    Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.add_le_add_right (Nat.pow_le_pow_left hq 3) 1)
        (Nat.pow_le_pow_left hq 3))
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
  have hden : Nat.gcd 3 (2 ^ s + 1) ≤ 3 := Nat.gcd_le_left _ (by decide)
  have hb := (Nat.div_le_div_right hnum (c := 3)).trans
    (Nat.div_le_div_left hden (Nat.gcd_pos_of_pos_left _ (by decide)))
  exact lt_of_lt_of_le (by decide : 20160 < 62400 / 3) hb

/-- The least positive-parameter Suzuki group already has order 29120. -/
theorem suzuki_card_gt_20160 {Q : Type*} [Group Q]
    {m : ℕ} (hm : 1 ≤ m) (e : Q ≃* SuzukiMatrixGroup m) :
    20160 < Nat.card Q := by
  rw [Nat.card_congr e.toEquiv,suzukiMatrixGroup_card m (by omega)]
  have hq : 8 ≤ 2 ^ (2 * m + 1) :=
    Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 3 ≤ 2 * m + 1)
  have hb := Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.add_le_add_right (Nat.pow_le_pow_left hq 2) 1)
      (Nat.pow_le_pow_left hq 2)) (Nat.sub_le_sub_right hq 1)
  exact lt_of_lt_of_le (by decide : 20160 < (8 ^ 2 + 1) * 8 ^ 2 * (8 - 1)) hb

/-- Passing to the center quotient does not change a binary PSL₂ model. -/
theorem binary_linear_two_central_quotient {Q : Type*} [Group Q] [Finite Q]
    {n : ℕ} (h : ClassicalGroup.IsPSL Q 2 (2 ^ n)) :
    ClassicalGroup.IsPSL (Q ⧸ center Q) 2 (2 ^ n) := by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := h
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  have hz : center Q = ⊥ := by
    apply card_eq_one.mp
    rw [Nat.card_congr (centerCongr (e.trans (Theory.PSL2.sl2QuotientEquiv F).symm)).toEquiv,
      Theory.PSL2.sl2_center_eq_bot]
    simp
  exact ⟨F,hF,hfin,hcard,⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).trans e⟩⟩

/-- The exact quotient alternatives in source 4.4.3(2), retaining the triple cover. -/
@[expose] def ExceptionalQuotient (Q : Type*) [Group Q] : Prop :=
  (∃ n : ℕ, ClassicalGroup.IsPSL Q 2 (2 ^ n)) ∨
  ClassicalGroup.IsPSL Q 3 2 ∨ ClassicalGroup.IsPSL Q 4 2 ∨
  Nonempty (Q ≃* alternatingGroup (Fin 6)) ∨
  Nonempty (Q ≃* alternatingGroup (Fin 7)) ∨
  (IsQuasisimple Q ∧ Nat.card (center Q) = 3 ∧
    Nonempty ((Q ⧸ center Q) ≃* alternatingGroup (Fin 6))) ∨
  ClassicalGroup.IsPSU Q 3 3

/-- Size and the actual binary-linear exclusion eliminate the full source list. -/
theorem not_exceptional_of_central_quotient {Q : Type*} [Group Q] [Finite Q]
    (hsize : 20160 < Nat.card (Q ⧸ center Q))
    (hlin : ∀ n : ℕ, ¬ ClassicalGroup.IsPSL (Q ⧸ center Q) 2 (2 ^ n)) :
    ¬ ExceptionalQuotient Q := by
  have hb : Nat.card (Q ⧸ center Q) ≤ Nat.card Q :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (center Q))
  have hqsize := hsize.trans_le hb
  rintro (⟨n,hn⟩ | h3 | h4 | h6 | h7 | hhat | hu)
  · exact hlin n (binary_linear_two_central_quotient hn)
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := h3
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
    norm_num [hF,Fin.prod_univ_succ] at hc
    rw [Nat.card_congr e.toEquiv,hc] at hqsize
    omega
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := h4
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
    norm_num [hF,Fin.prod_univ_succ] at hc
    rw [Nat.card_congr e.toEquiv,hc] at hqsize
    omega
  · obtain ⟨e⟩ := h6
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hqsize
    norm_num at hqsize
  · obtain ⟨e⟩ := h7
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hqsize
    norm_num at hqsize
  · obtain ⟨_,_,⟨e⟩⟩ := hhat
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hsize
    norm_num at hsize
  · obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hu
    rw [Nat.card_congr e.toEquiv,
      HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic.card_projective
        J hF hconj] at hqsize
    norm_num at hqsize

end CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
