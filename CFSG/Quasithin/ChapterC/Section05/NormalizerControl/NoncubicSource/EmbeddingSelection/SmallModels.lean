module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.Parameters
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.Mathieu.M22.Properties.Order
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import BenderSuzuki.SE.Section11Lemma115Endpoint
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore

/-!
# Distinguishing the small A.3.12 models from binary PSL₂

The exact two-part determines the field degree in each small-order model,
and the full order then contradicts the binary PSL₂ formula. Suzuki groups
instead have order prime to three, whereas every binary PSL₂ has a cubic.
The actual PSL₂ model also supplies simplicity and its trivial center.
No representation irreducibility or classification conclusion is assumed.
Source: Aschbacher–Smith A.3.12 and C.5.13, printed pp.47–48,162–163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open Chapter1.Section02.LocalModels
variable {B : Type*} [Group B] {n : ℕ}

private theorem binary_not_order (hn : 0 < n) (hB : ClassicalGroup.IsPSL B 2 (2^n))
    (k m : ℕ) (hm : Odd m)
    (hne : 2^k*((2^k)^2-1) ≠ 2^k*m) : Nat.card B ≠ 2^k*m := by
  intro hc
  have hv := binary_two_valuation hn hB
  have hmn : m ≠ 0 := by intro he; rw [he] at hm; norm_num at hm
  rw [hc,Nat.factorization_mul (by positivity) hmn,Finsupp.add_apply,
    Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by simpa only [← even_iff_two_dvd] using Nat.not_even_iff_odd.mpr hm),add_zero] at hv
  exact hne ((by simpa only [hv] using (binary_card hB).symm.trans hc))

theorem binary_not_alternating_six (hn : 0 < n)
    (hB : ClassicalGroup.IsPSL B 2 (2^n)) : ¬ IsAlternating B 6 := by
  rintro ⟨e⟩
  apply binary_not_order hn hB 3 45 (by decide) (by decide)
  rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
  norm_num

theorem binary_not_alternating_cover_six (hn : 0 < n)
    (hB : ClassicalGroup.IsPSL B 2 (2^n)) : ¬ IsAlternatingCover B 6 := by
  rintro ⟨_,⟨z⟩,⟨e⟩⟩
  apply binary_not_order hn hB 3 135 (by decide) (by decide)
  rw [card_eq_card_quotient_mul_card_subgroup (center B),
    Nat.card_congr e.toEquiv,Nat.card_congr z.toEquiv,nat_card_alternatingGroup]
  norm_num

theorem binary_not_linear_three_two (hn : 0 < n)
    (hB : ClassicalGroup.IsPSL B 2 (2^n)) : ¬ ClassicalGroup.IsPSL B 3 2 := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  apply binary_not_order hn hB 3 21 (by decide) (by decide)
  rw [Nat.card_congr e.toEquiv]
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  rw [hF] at hc
  norm_num [Fin.prod_univ_succ] at hc ⊢
  exact hc

theorem binary_not_linear_four_two (hn : 0 < n)
    (hB : ClassicalGroup.IsPSL B 2 (2^n)) : ¬ ClassicalGroup.IsPSL B 4 2 := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  apply binary_not_order hn hB 6 315 (by decide) (by decide)
  rw [Nat.card_congr e.toEquiv]
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
  rw [hF] at hc
  norm_num [Fin.prod_univ_succ] at hc ⊢
  exact hc

theorem binary_not_linear_three_four (hn : 0 < n)
    (hB : ClassicalGroup.IsPSL B 2 (2^n)) : ¬ ClassicalGroup.IsPSL B 3 4 := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  apply binary_not_order hn hB 6 315 (by decide) (by decide)
  rw [Nat.card_congr e.toEquiv]
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  rw [hF] at hc
  norm_num [Fin.prod_univ_succ] at hc ⊢
  omega

theorem binary_not_mathieu_twenty_two (hn : 0 < n)
    (hB : ClassicalGroup.IsPSL B 2 (2^n)) : ¬ Nonempty (B ≃* Sporadic.Mathieu.M22) := by
  rintro ⟨e⟩
  apply binary_not_order hn hB 7 3465 (by decide) (by decide)
  rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m22_order]
  norm_num

theorem binary_simple (hn : 1 < n) (hB : ClassicalGroup.IsPSL B 2 (2^n)) :
    IsSimpleGroup B := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hB
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [hF]
      exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ n))
  exact e.isSimpleGroup
theorem binary_three_dvd_card (hB : ClassicalGroup.IsPSL B 2 (2^n)) : 3 ∣ Nat.card B := by
  rw [binary_card hB]
  apply dvd_mul_of_dvd_right
  apply Nat.dvd_of_mod_eq_zero
  have hm : ((2^n)^2)%3 = 1 := by
    rw [← pow_mul,Nat.mul_comm n 2,pow_mul]
    simp [Nat.pow_mod]
  omega

theorem binary_not_suzuki (hB : ClassicalGroup.IsPSL B 2 (2^n))
    (m : ℕ) (hm : 0 < m) : ¬ Nonempty (B ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  rintro ⟨e⟩
  have hdiv := binary_three_dvd_card hB
  rw [Nat.card_congr e.toEquiv,BenderSuzuki.lemma115_suzukiMatrixGroup_card_formula m hm] at hdiv
  have hmod : 2^(2*m+1)%3 = 2 := by simp [pow_add,pow_mul,Nat.mul_mod,Nat.pow_mod]
  generalize hq : 2^(2*m+1) = q at hdiv hmod
  have hsub : (q-1)%3 = 1 := by omega
  have he := Nat.mod_eq_zero_of_dvd hdiv
  have hsquare : (q^2 + 1) % 3 = 2 := by
    rw [Nat.add_mod, Nat.pow_mod, hmod]
  norm_num [Nat.mul_mod, Nat.pow_mod, hmod, hsub, hsquare] at he

theorem binary_center_eq_bot (hB : ClassicalGroup.IsPSL B 2 (2^n)) : center B = ⊥ := by
  obtain ⟨F,_,_,_,⟨e⟩⟩ := hB
  exact GorensteinWalter.center_eq_bot_of_mulEquiv e (GorensteinWalter.psl2_center_eq_bot F)

theorem binary_primeCore_eq_bot [Finite B] [IsQuasisimple B]
    (hB : ClassicalGroup.IsPSL B 2 (2^n)) (p : ℕ) [Fact p.Prime] : pCore p B = ⊥ := by
  apply eq_bot_iff.mpr
  exact (IsQuasisimple.pCore_le_center p).trans (binary_center_eq_bot hB).le
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
