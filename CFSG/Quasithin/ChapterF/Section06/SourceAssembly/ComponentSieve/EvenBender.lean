module

public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import Theory.GroupTheory.SmallSylowObstructions
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv
public import Theory.SpecificGroups.Suzuki.SubgroupParameters
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic.Order
/-!
# The small-Sylow Bender alternatives in F.6.17

The actual PSU3 and Suzuki order formulas have two-part at least sixteen.
For binary PSL2 the field order divides the group order, so a Sylow bound
of eight leaves precisely field orders four and eight. The faithful
five-point comparison identifies PSL2(4) with the actual prime-field PSL2(5).

The source Bender predicate already retains its nonabelian parameter ranges.
No simplicity or recognition conclusion is assumed in the sieve.
Source: Aschbacher--Smith Theorem C and F.6.17, printed pp.33,309.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve
variable {G : Type*} [Group G] [Finite G]

private theorem sixteen_dvd_psu3_binary {F : Type*} [Field F] [Finite F]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F) {f : ℕ} (hf : 2 ≤ f)
    (hc : Nat.card F = (2 ^ f) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ f)) :
    16 ∣ Nat.card (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) := by
  let q := 2 ^ f
  have hq : 1 < q := one_lt_pow₀ (by decide) (by omega)
  rw [BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic.card_projective J hc hconj]
  have h16 : 16 ∣ q ^ 3 := by
    change 2 ^ 4 ∣ (2 ^ f) ^ 3
    rw [← pow_mul]
    exact pow_dvd_pow 2 (by omega)
  have hd : 16 ∣ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h16 _) _
  have hg : Nat.gcd 3 (q + 1) ∣ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) := by
    apply (Nat.gcd_dvd_right 3 (q + 1)).trans
    apply dvd_mul_of_dvd_left
    apply dvd_mul_of_dvd_left
    exact ⟨q ^ 2 - q + 1, by nlinarith [Nat.sub_add_cancel (show q ≤ q ^ 2 by nlinarith)]⟩
  apply Nat.dvd_div_of_mul_dvd
  rw [mul_comm]
  exact ((show Nat.Coprime 16 (Nat.gcd 3 (q + 1)) from
    (by decide : Nat.Coprime 16 3).of_dvd_right (Nat.gcd_dvd_left _ _)).mul_dvd_of_dvd_of_dvd hd hg)

theorem not_unitary_three_binary_of_small_sylow
    (P : Sylow 2 G) (hP : Nat.card P ≤ 8) {f : ℕ} (hf : 2 ≤ f) :
    ¬ ClassicalGroup.IsPSU G 3 (2 ^ f) := by
  rintro ⟨F, _, _, J, hc, hj, ⟨e⟩⟩
  apply not_sixteen_dvd_of_sylow_le_eight P hP
  rw [Nat.card_congr e.toEquiv]
  exact sixteen_dvd_psu3_binary J hf hc hj

theorem not_suzuki_of_small_sylow
    (P : Sylow 2 G) (hP : Nat.card P ≤ 8) {m : ℕ} (hm : 1 ≤ m) :
    ¬ Nonempty (G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  rintro ⟨e⟩
  apply not_sixteen_dvd_of_sylow_le_eight P hP
  rw [Nat.card_congr e.toEquiv, BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card m hm]
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_right
  change 2 ^ 4 ∣ (2 ^ (2 * m + 1)) ^ 2
  rw [← pow_mul]
  exact pow_dvd_pow 2 (by omega)

theorem binary_linear_two_small_parameters
    (P : Sylow 2 G) (hP : Nat.card P ≤ 8) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL G 2 (2 ^ f)) : f = 2 ∨ f = 3 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
    simpa [Nat.card_eq_fintype_card] using hF)
  have hcard := BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
  rw [BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
    (CharTwo.neg_eq 1), mul_one, hF] at hcard
  have hf4 : f < 4 := by
    by_contra hn
    have hf4 : 4 ≤ f := by omega
    apply not_sixteen_dvd_of_sylow_le_eight P hP
    rw [Nat.card_congr e.toEquiv, hcard]
    exact dvd_mul_of_dvd_left (show 2 ^ 4 ∣ 2 ^ f from pow_dvd_pow 2 hf4) _
  omega

omit [Finite G] in
theorem prime_five_model_of_binary_four (hm : ClassicalGroup.IsPSL G 2 4) :
    ClassicalGroup.IsPSL G 2 5 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  obtain ⟨b⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact ⟨ZMod 5, inferInstance, inferInstance, by simp, ⟨(e.trans a).trans b.symm⟩⟩

theorem bender_small_sylow_cases
    (P : Sylow 2 G) (hP : Nat.card P ≤ 8) (hm : ClassificationModels.IsBenderModel G) :
    ClassicalGroup.IsPSL G 2 5 ∨ ClassicalGroup.IsPSL G 2 8 := by
  cases hm with
  | linear f hf hm =>
    rcases binary_linear_two_small_parameters P hP hf hm with rfl | rfl
    · exact Or.inl (prime_five_model_of_binary_four hm)
    · exact Or.inr hm
  | unitary f hf hm => exact (not_unitary_three_binary_of_small_sylow P hP hf hm).elim
  | suzuki m hm he => exact (not_suzuki_of_small_sylow P hP hm he).elim
end CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve
