module
public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.Contracts
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder

/-!
# Excluding the paired F.9.18 models from M₂₂

Only the concrete component comparisons used by F.9.18(4iii) are proved
here. The order of M₂₂ has two-part 2⁷. The field-order cube in SL₃ and
fourth power in Sp₄ restrict the binary field degrees to at most two and
one respectively. The remaining orders, and those of A₆, A₇, SL₄(2)
and SL₅(2), disagree with 443520.

The field groups are the actual matrix carriers. Their order theorems
are reused directly, with the scalar quotient retained in the SL₃ count.
No new simplicity or representation classification is needed.

Source: Aschbacher–Smith, F.9.18(4iii), p.325, applied in 13.8.21(2),
p.956 (1 March 2004 manuscript).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu
open scoped MatrixGroups
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.F918Source

theorem not_linearThree (F : BinaryField)
    (e : M22 ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier) : False := by
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) = 443520 :=
    (Nat.card_congr e.symm.toEquiv).trans m22_order
  have hsl := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (center (Matrix.SpecialLinearGroup (Fin 3) F.Carrier))
  rw [Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin] at hsl
  have he := hsl.trans (Matrix.PSL3.LinearThree.card_projective_mul_scalar F.Carrier)
  rw [hcard, F.card_eq] at he
  have hd : 2 ^ (F.degree * 3) ∣ 443520 := by
    rw [pow_mul]
    exact he.symm ▸ dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hn : F.degree ≤ 2 := by
    by_contra hn
    have hdiv : 2 ^ 9 ∣ 443520 :=
      (Nat.pow_dvd_pow 2 (show 9 ≤ F.degree * 3 by omega)).trans hd
    norm_num at hdiv
  have hp := F.degree_pos
  have hx : F.degree = 1 ∨ F.degree = 2 := by omega
  rcases hx with h | h <;> norm_num [h] at he

theorem not_symplecticFour (F : BinaryField)
    (e : M22 ≃* Matrix.symplecticGroup (Fin 2) F.Carrier) : False := by
  have he := (Nat.card_congr e.toEquiv).symm.trans m22_order
  rw [Theory.SpecificGroups.SymplecticFour.card_sp, F.card_eq] at he
  have hd : 2 ^ (F.degree * 4) ∣ 443520 := by
    rw [pow_mul]
    exact he ▸ dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hn : F.degree = 1 := by
    have hp := F.degree_pos
    by_contra hn
    have hdiv : 2 ^ 8 ∣ 443520 :=
      (Nat.pow_dvd_pow 2 (show 8 ≤ F.degree * 4 by omega)).trans hd
    norm_num at hdiv
  norm_num [hn] at he

theorem not_alternating_six (e : M22 ≃* alternatingGroup (Fin 6)) : False := by
  have h := Nat.card_congr e.toEquiv
  rw [m22_order, nat_card_alternatingGroup] at h
  norm_num at h

theorem not_alternating_seven (e : M22 ≃* alternatingGroup (Fin 7)) : False := by
  have h := Nat.card_congr e.toEquiv
  rw [m22_order, nat_card_alternatingGroup] at h
  norm_num at h

theorem not_binary_linear (n : ℕ) (hn : n = 4 ∨ n = 5)
    (e : M22 ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : False := by
  let : NeZero n := ⟨by omega⟩
  let eP := e.trans (slProjectiveEquiv (sl_binary_center_eq_bot n (by omega)))
  have hcard : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) = 443520 :=
    (Nat.card_congr eP.symm.toEquiv).trans m22_order
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) n
  rw [hcard] at h
  rcases hn with rfl | rfl <;> norm_num [Fin.prod_univ_succ] at h
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Recognition.F918Source
