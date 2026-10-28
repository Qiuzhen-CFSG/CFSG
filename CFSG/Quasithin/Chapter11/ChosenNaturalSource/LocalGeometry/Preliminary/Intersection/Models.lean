module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.CaseComparison
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
/-!
# Excluding the reducible B.5.1 actors in the symplectic and G₂ rows

The two-part of qᵏ(qᵏ−1)(q²−1) determines qᵏ. Equality with an SL₃ order
then cancels the common factors and forces the field orders equal, hence
k = 3. This excludes both Sp₄ and G₂. The two-part also separates nonbinary
G₂ from binary SL₄ and SL₅. These actual group comparisons are consumed by
the H-star normalization argument, without assumptions about module splitting.

Source: Aschbacher--Smith, B.5.1(1) and 11.0.3(5), printed pp.99 and760.
The group-order calculations use the attributed ATLAS carriers and proofs;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.IntersectionModels

private theorem odd_pow_sub_one {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    Odd ((2 ^ n) ^ k - 1) := by
  rw [← pow_mul]
  have hp : 0 < 2^(n*k) := by positivity
  have hm : 2^(n*k) % 2 = 0 := by simp [Nat.pow_mod, Nat.ne_of_gt (Nat.mul_pos hn hk)]
  exact Nat.odd_iff.mpr (by omega)

private theorem valuation_order (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    padicValNat 2 ((2^n)^k * ((2^n)^k-1) * ((2^n)^2-1)) = n*k := by
  have h1 := odd_pow_sub_one hn hk
  have h2 := odd_pow_sub_one hn (by decide : 0 < 2)
  rw [padicValNat.mul (Nat.mul_ne_zero (by positivity) (Nat.ne_of_gt h1.pos)) (Nat.ne_of_gt h2.pos),
    padicValNat.mul (by positivity) (Nat.ne_of_gt h1.pos),
    padicValNat.eq_zero_of_not_dvd h1.not_two_dvd_nat,
    padicValNat.eq_zero_of_not_dvd h2.not_two_dvd_nat,
    ← pow_mul, padicValNat.prime_pow]
  omega

private theorem order_parameter (n m k : ℕ) (hn : 0 < n) (hm : 0 < m) (hk : 0 < k)
    (hc : (2^n)^k * ((2^n)^k-1) * ((2^n)^2-1) =
      (2^m)^3 * ((2^m)^3-1) * ((2^m)^2-1)) : k = 3 := by
  have hv := congrArg (padicValNat 2) hc
  rw [valuation_order n k hn hk, valuation_order m 3 hm (by decide)] at hv
  have hp : (2^n)^k = (2^m)^3 := by rw [← pow_mul, ← pow_mul, hv]
  rw [hp] at hc
  have hpos : 0 < (2^m)^3 * ((2^m)^3-1) :=
    Nat.mul_pos (by positivity) (odd_pow_sub_one hm (by decide)).pos
  have he := Nat.eq_of_mul_eq_mul_left hpos hc
  have hns : 1 ≤ (2^n)^2 := Nat.succ_le_of_lt (by positivity)
  have hms : 1 ≤ (2^m)^2 := Nat.succ_le_of_lt (by positivity)
  have he2 : (2^n)^2 = (2^m)^2 := by omega
  rw [← pow_mul, ← pow_mul] at he2
  have hnm : n = m := by have := Nat.pow_right_injective (by decide : 1 < 2) he2; omega
  rw [← hnm] at hv
  exact Nat.eq_of_mul_eq_mul_left hn hv

private theorem card_linear_three (F : BinaryField) :
    Nat.card SL(3,F.Carrier) =
      (Nat.card F.Carrier)^3 * ((Nat.card F.Carrier)^3-1) * ((Nat.card F.Carrier)^2-1) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center SL(3,F.Carrier)),
    Atlas.ExceptionalSupport.card_sl_center]
  exact Matrix.PSL3.LinearThree.card_projective_mul_scalar F.Carrier

theorem no_sp4_linearThree (F K : BinaryField)
    (e : Matrix.symplecticGroup (Fin 2) F.Carrier ≃* SL(3,K.Carrier)) : False := by
  have hc := Nat.card_congr e.toEquiv
  rw [Theory.SpecificGroups.SymplecticFour.card_sp, card_linear_three,
    F.card_eq, K.card_eq] at hc
  have he := order_parameter F.degree K.degree 4 F.degree_pos K.degree_pos (by decide)
    (by convert hc using 1; ring)
  omega

theorem no_g2_linearThree (F K : BinaryField)
    (e : Atlas.G2.Model F.Carrier ≃* SL(3,K.Carrier)) : False := by
  have hc := Nat.card_congr e.toEquiv
  rw [Atlas.G2.card_Model, card_linear_three, F.card_eq, K.card_eq] at hc
  have he := order_parameter F.degree K.degree 6 F.degree_pos K.degree_pos (by decide)
    hc
  omega

private theorem binary_card (n : ℕ) [NeZero n] :
    Nat.card SL(n,ZMod 2) = ∏ i : Fin n, (2^n - 2^i.val) := by
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) n
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center SL(n,ZMod 2)),
    Atlas.ExceptionalSupport.card_sl_center]
  simpa using h

theorem no_g2_binary (F : BinaryField) (hn : 1 < F.degree) {d : ℕ}
    (hd : d = 4 ∨ d = 5) (e : Atlas.G2.Model F.Carrier ≃* SL(d,ZMod 2)) : False := by
  have hc := Nat.card_congr e.toEquiv
  rw [Atlas.G2.card_Model, F.card_eq] at hc
  have hv := congrArg (padicValNat 2) hc
  have hvF : padicValNat 2 ((2^F.degree)^6 * ((2^F.degree)^6-1) *
      ((2^F.degree)^2-1)) = F.degree*6 := valuation_order _ _ F.degree_pos (by decide)
  rw [hvF] at hv
  have h4 : padicValNat 2 20160 = 6 := by
    rw [show 20160 = 2^6 * 315 by norm_num,
      padicValNat.mul (by decide) (by decide), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 315)]
  have h5 : padicValNat 2 9999360 = 10 := by
    rw [show 9999360 = 2^10 * 9765 by norm_num,
      padicValNat.mul (by decide) (by decide), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 9765)]
  rcases hd with rfl | rfl
  · rw [binary_card] at hv
    norm_num [Fin.prod_univ_succ] at hv
    rw [h4] at hv
    omega
  · rw [binary_card] at hv
    norm_num [Fin.prod_univ_succ] at hv
    rw [h5] at hv
    omega

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.IntersectionModels
