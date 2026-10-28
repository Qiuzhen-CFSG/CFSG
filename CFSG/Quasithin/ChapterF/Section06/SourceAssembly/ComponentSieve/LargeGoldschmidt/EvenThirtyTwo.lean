module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.EvenExceptional
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.EvenBender
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.EvenLinear
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.DegreeThree.RankOne
public import Theory.SpecificGroups.Classical.BinarySmallSylowOrders
public import Theory.SpecificGroups.SU3.BinaryG2Comparison
/-!
# Even and alternating source models at Sylow order thirty-two

The even rank-two order formulas and their actual positive-root subgroups
exclude every full family. The sole derived exception is G₂(2)′, identified
with the genuine projective unitary-three model over the field of order nine.
The binary rank-one candidate is excluded by the noncommutative Sylow, and
the remaining binary linear and alternating entries have incompatible two-parts.

Source: Aschbacher–Smith Theorem C and F.6.18(10), printed pp.33,310;
Fong's binary G₂ comparison is used through its proved matrix-group equivalence.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve.LargeGoldschmidt
open CFSG.Quasithin.ClassificationModels
open CFSG.Quasithin.ChapterA.Section02
variable {G : Type*} [Group G] [Finite G]
private theorem not64_of_card32 (P : Sylow 2 G) (hP : Nat.card P = 32) : ¬64 ∣ Nat.card G := by
  intro hd
  have hh := P.pow_dvd_card_of_pow_dvd_card (n := 6) hd
  rw [hP] at hh
  norm_num at hh
private theorem binary_power64 {f d : ℕ} (h : 6 ≤ f*d) : 64 ∣ (2^f)^d := by
  rw [← pow_mul]
  exact Nat.pow_dvd_pow 2 h

theorem no_bender_of_noncommutative_sylow32 (P : Sylow 2 G) (hP : Nat.card P = 32)
    (hnc : ¬ IsMulCommutative P) : ¬ IsBenderModel G := by
  have hn64 := not64_of_card32 P hP
  intro hm
  cases hm with
  | linear f _ hm => exact not_binary_psl2_of_noncommutative_sylow P hnc hm
  | unitary f hf hm =>
    obtain ⟨F,_,_,J,hc,hj,⟨e⟩⟩ := hm
    apply hn64
    rw [Nat.card_congr e.toEquiv]
    exact Theory.ClassicalSmallSylow.binary_psu3_two_power_dvd (r := 6) J (by omega) hc hj (by omega)
  | suzuki m hm he =>
    obtain ⟨e⟩ := he
    apply hn64
    rw [Nat.card_congr e.toEquiv,BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card m hm]
    apply dvd_mul_of_dvd_left
    apply dvd_mul_of_dvd_right
    exact binary_power64 (by omega)

theorem unitary_three_of_rankTwo_sylow32 (P : Sylow 2 G) (hP : Nat.card P = 32)
    {f : ℕ} (hm : IsTheoremCRankTwoModel G f) : ClassicalGroup.IsPSU G 3 3 := by
  have hn64 := not64_of_card32 P hP
  have h32 : 32 ∣ Nat.card G := hP ▸ P.card_subgroup_dvd_card
  cases hm with
  | linear hf hm =>
    obtain ⟨F,_,_,hc,⟨e⟩⟩ := hm
    by_cases hf1 : f=1
    · subst f
      have hh := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
      rw [hc] at hh
      norm_num [Fin.prod_univ_succ] at hh
      rw [Nat.card_congr e.toEquiv,hh] at h32
      norm_num at h32
    · apply (hn64 _).elim
      rw [Nat.card_congr e.toEquiv]
      exact Theory.ClassicalSmallSylow.binary_psl3_two_power_dvd (r := 6) hc (by omega)
  | symplectic hf hm =>
    obtain ⟨F,_,_,hc,⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hc
    apply (hn64 _).elim
    rw [Nat.card_congr e.toEquiv,
      ← Nat.card_congr (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).toEquiv,
      Theory.SpecificGroups.SymplecticFour.card_sp,hc]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (binary_power64 (by omega)) _) _
  | g2 hf hm =>
    obtain ⟨F,_,_,hc,⟨e⟩⟩ := hm
    apply (hn64 _).elim
    rw [Nat.card_congr e.toEquiv,Atlas.G2.card_Model,hc]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (binary_power64 (by omega)) _) _
  | triality hf hm =>
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff G f hf).mp hm
    apply (hn64 _).elim
    rw [Nat.card_congr e.toEquiv]
    apply dvd_trans _ (Triality.Standard.Parabolics.unipotent
      (Triality.Standard.binaryParameters f hf)).card_subgroup_dvd_card
    rw [Triality.Standard.Parabolics.card_unipotent_binary _ rfl]
    exact binary_power64 (f := f) (d := 12) (by omega)
  | ree_f4 m _ _ he =>
    obtain ⟨e⟩ := he
    apply (hn64 _).elim
    rw [Nat.card_congr e.toEquiv]
    apply dvd_trans _ (ReeF4.Parabolics.unipotent m).card_subgroup_dvd_card
    rw [ReeF4.Parabolics.card_unipotent]
    exact binary_power64 (by omega)
  | symplectic_derived _ he =>
    obtain ⟨e⟩ := he
    have j := e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix
    rw [Nat.card_congr j.toEquiv,nat_card_alternatingGroup,Nat.card_fin] at h32
    norm_num at h32
  | g2_derived _ he =>
    obtain ⟨e⟩ := he
    obtain ⟨j⟩ := Atlas.G2.nonempty_commutator_binary_equiv_psu3
    let : Fact (Nat.Prime 3) := ⟨by decide⟩
    refine ⟨GaloisField 3 2,inferInstance,inferInstance,ABG.unitaryForm 3 3 1 (by decide),?_,?_,⟨e.trans j⟩⟩
    · exact GaloisField.card 3 2 (by decide)
    · intro x
      rfl
  | tits _ he =>
    obtain ⟨e⟩ := he
    apply (hn64 _).elim
    rw [Nat.card_congr e.toEquiv,Tits.parrottGroup_card]
    norm_num

theorem no_binary_four_or_five_of_sylow32 (P : Sylow 2 G) (hP : Nat.card P = 32)
    {n : ℕ} (hn : n=4 ∨ n=5) : ¬ ClassicalGroup.IsPSL G n 2 := by
  rintro ⟨F,_,_,hc,⟨e⟩⟩
  apply not64_of_card32 P hP
  rw [Nat.card_congr e.toEquiv]
  rcases hn with rfl|rfl
  · have hh := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
    rw [hc] at hh
    norm_num [Fin.prod_univ_succ] at hh
    rw [hh]
    norm_num
  · have hh := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
    rw [hc] at hh
    norm_num [Fin.prod_univ_succ] at hh
    rw [hh]
    norm_num

theorem no_alternating_le_eight_of_sylow32 (P : Sylow 2 G) (hP : Nat.card P = 32)
    {n : ℕ} (hn : n ≤ 8) : ¬ Nonempty (G ≃* alternatingGroup (Fin n)) := by
  rintro ⟨e⟩
  by_cases hn8 : n=8
  · subst n
    apply not64_of_card32 P hP
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    norm_num
  have hd : 32 ∣ Nat.card (Equiv.Perm (Fin n)) := by
    have hh := P.card_subgroup_dvd_card
    rw [hP,Nat.card_congr e.toEquiv] at hh
    exact hh.trans (alternatingGroup (Fin n)).card_subgroup_dvd_card
  simp only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin] at hd
  have hn7 : n ≤ 7 := by omega
  interval_cases n <;> norm_num at hd
end CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve.LargeGoldschmidt
