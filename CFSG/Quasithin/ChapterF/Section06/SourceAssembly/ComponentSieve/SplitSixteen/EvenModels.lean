module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.EvenBender
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.EvenExceptional
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.EvenLinear
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.DihedralEight.Models
public import Theory.GroupTheory.ExponentFourSylowSections

/-!
# Even-field models with Sylow order at most sixteen

The defining-characteristic factors in the actual orders or root groups
exclude the larger linear, unitary, symplectic and exceptional carriers.
The remaining concrete models are PSL2(4), PSL2(8), PSL2(16), PSL3(2)
and the binary symplectic derived group. The exceptional comparisons
identify the first, fourth and fifth with PSL2(5), PSL2(7), and A6.

Source: Aschbacher--Smith F.6.18(8)--(9), printed p.310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve.SplitSixteen
open CFSG.Quasithin.ClassificationModels
open CFSG.Quasithin.ChapterA.Section02
variable {G : Type*} [Group G] [Finite G]

private theorem no_thirty_two (P : Sylow 2 G) (hP : Nat.card P ≤ 16) :
    ¬ 32 ∣ Nat.card G := by
  intro hd
  have hb := Nat.le_of_dvd (Nat.card_pos (α := P))
    (P.pow_dvd_card_of_pow_dvd_card (n := 5) hd)
  omega

private theorem thirty_two_dvd_psu3_binary {F : Type*} [Field F] [Finite F]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F) {f : ℕ} (hf : 2 ≤ f)
    (hc : Nat.card F = (2 ^ f) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ f)) :
    32 ∣ Nat.card (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) := by
  let q := 2 ^ f
  have hq : 1 < q := one_lt_pow₀ (by decide) (by omega)
  rw [BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic.card_projective J hc hconj]
  have h32 : 32 ∣ q ^ 3 := by
    change 2 ^ 5 ∣ (2 ^ f) ^ 3
    rw [← pow_mul]
    exact pow_dvd_pow 2 (by omega)
  have hd : 32 ∣ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h32 _) _
  have hg : Nat.gcd 3 (q + 1) ∣ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) := by
    apply (Nat.gcd_dvd_right 3 (q + 1)).trans
    apply dvd_mul_of_dvd_left
    apply dvd_mul_of_dvd_left
    exact ⟨q ^ 2 - q + 1, by nlinarith [Nat.sub_add_cancel (show q ≤ q ^ 2 by nlinarith)]⟩
  apply Nat.dvd_div_of_mul_dvd
  rw [mul_comm]
  exact ((show Nat.Coprime 32 (Nat.gcd 3 (q + 1)) from
    (by decide : Nat.Coprime 32 3).of_dvd_right (Nat.gcd_dvd_left _ _)).mul_dvd_of_dvd_of_dvd hd hg)

theorem not_unitary_three_binary_of_sylow_le_sixteen
    (P : Sylow 2 G) (hP : Nat.card P ≤ 16) {f : ℕ} (hf : 2 ≤ f) :
    ¬ ClassicalGroup.IsPSU G 3 (2 ^ f) := by
  rintro ⟨F, _, _, J, hc, hj, ⟨e⟩⟩
  apply no_thirty_two P hP
  rw [Nat.card_congr e.toEquiv]
  exact thirty_two_dvd_psu3_binary J hf hc hj

theorem not_suzuki_of_sylow_le_sixteen
    (P : Sylow 2 G) (hP : Nat.card P ≤ 16) {m : ℕ} (hm : 1 ≤ m) :
    ¬ Nonempty (G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  rintro ⟨e⟩
  apply no_thirty_two P hP
  rw [Nat.card_congr e.toEquiv, BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card m hm]
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_right
  change 2 ^ 5 ∣ (2 ^ (2 * m + 1)) ^ 2
  rw [← pow_mul]
  exact pow_dvd_pow 2 (by omega)

theorem binary_linear_two_parameters
    (P : Sylow 2 G) (hP : Nat.card P ≤ 16) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL G 2 (2 ^ f)) : f = 2 ∨ f = 3 ∨ f = 4 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
    simpa [Nat.card_eq_fintype_card] using hF)
  have hcard := BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
  rw [BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
    (CharTwo.neg_eq 1), mul_one, hF] at hcard
  have hf4 : f < 5 := by
    by_contra hn
    have hf4 : 5 ≤ f := by omega
    apply no_thirty_two P hP
    rw [Nat.card_congr e.toEquiv, hcard]
    exact dvd_mul_of_dvd_left (show 2 ^ 5 ∣ 2 ^ f from pow_dvd_pow 2 hf4) _
  omega


private theorem thirty_two_dvd_binary_power {f d : ℕ} (h : 5 ≤ f * d) :
    32 ∣ (2 ^ f) ^ d := by
  rw [← pow_mul]
  exact Nat.pow_dvd_pow 2 h

/-- The genuine even symplectic model has too large a two-part. -/
theorem not_symplectic_of_sylow_le_sixteen (P : Sylow 2 G) (hP : Nat.card P ≤ 16)
    {f : ℕ} (hf : 2 ≤ f) (hmodel : ClassicalGroup.IsPSp G 2 (2 ^ f)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  apply no_thirty_two P hP
  rw [Nat.card_congr e.toEquiv,
    ← Nat.card_congr (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).toEquiv,
    Theory.SpecificGroups.SymplecticFour.card_sp, hF]
  exact dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left (thirty_two_dvd_binary_power (by omega)) _) _

/-- The actual split-octonion carrier has too large a two-part. -/
theorem not_g2_of_sylow_le_sixteen (P : Sylow 2 G) (hP : Nat.card P ≤ 16)
    {f : ℕ} (hf : 2 ≤ f) (hmodel : IsG2At G (2 ^ f)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  apply no_thirty_two P hP
  rw [Nat.card_congr e.toEquiv, Atlas.G2.card_Model, hF]
  exact dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left (thirty_two_dvd_binary_power (by omega)) _) _

/-- The descended positive root subgroup of the actual triality carrier
already has order divisible by thirty-two. -/
theorem not_triality_of_sylow_le_sixteen (P : Sylow 2 G) (hP : Nat.card P ≤ 16)
    {f : ℕ} (hf : 1 ≤ f)
    (hmodel : Triality.Standard.IsTrialityGroupAt (2 ^ f) G) : False := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff G f hf).mp hmodel
  apply no_thirty_two P hP
  rw [Nat.card_congr e.toEquiv]
  apply dvd_trans _ (Triality.Standard.Parabolics.unipotent
    (Triality.Standard.binaryParameters f hf)).card_subgroup_dvd_card
  rw [Triality.Standard.Parabolics.card_unipotent_binary _ rfl]
  change 32 ∣ (2 ^ f) ^ 12
  exact thirty_two_dvd_binary_power (by omega)

/-- The literal Ree positive root subgroup excludes every full Ree carrier,
including its binary endpoint. -/
theorem not_ree_f4_of_sylow_le_sixteen (P : Sylow 2 G) (hP : Nat.card P ≤ 16)
    (m : ℕ) (e : G ≃* ReeF4.Model m) : False := by
  apply no_thirty_two P hP
  rw [Nat.card_congr e.toEquiv]
  apply dvd_trans _ (ReeF4.Parabolics.unipotent m).card_subgroup_dvd_card
  rw [ReeF4.Parabolics.card_unipotent]
  exact thirty_two_dvd_binary_power (by omega)


/-- The binary G₂ commutator has actual order 6048. -/
theorem not_g2_derived_of_sylow_le_sixteen (P : Sylow 2 G) (hP : Nat.card P ≤ 16)
    (e : G ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  apply no_thirty_two P hP
  rw [Nat.card_congr e.toEquiv,
    Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
  norm_num

/-- The actual Parrott presentation has order 17971200. -/
theorem not_tits_of_sylow_le_sixteen (P : Sylow 2 G) (hP : Nat.card P ≤ 16)
    (e : G ≃* Tits.ParrottGroup) : False := by
  apply no_thirty_two P hP
  rw [Nat.card_congr e.toEquiv, Tits.parrottGroup_card]
  norm_num


theorem not_binary_four_or_five_of_sylow_le_sixteen
    (P : Sylow 2 G) (hP : Nat.card P ≤ 16) {n : ℕ} (hn : n = 4 ∨ n = 5) :
    ¬ ClassicalGroup.IsPSL G n 2 := by
  rintro ⟨F, _, _, hF, ⟨e⟩⟩
  apply no_thirty_two P hP
  rw [Nat.card_congr e.toEquiv]
  rcases hn with rfl | rfl
  · have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
    rw [hF] at hc
    norm_num [Fin.prod_univ_succ] at hc
    rw [hc]
    norm_num
  · have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
    rw [hF] at hc
    norm_num [Fin.prod_univ_succ] at hc
    rw [hc]
    norm_num


end CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve.SplitSixteen
