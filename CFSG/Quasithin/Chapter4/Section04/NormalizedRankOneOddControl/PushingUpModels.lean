module
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.RankTwoResidualExclusions

/-!
# Rank-one residuals in the Theorem C component catalogue

The original module of rank at least twelve eliminates the finite and odd
rows. Unlike the Theorem B list, the SQTK catalogue has no unitary rank-two
rows. The actual residual embedding then excludes each linear-Levi row,
leaving the Ree central quotient with its genuine isomorphism.

Source: Aschbacher--Smith C.3.5 and 4.2.12--13, printed pp.150,610--612.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
open ChapterA.Section02 ClassificationModels

/-- The SQTK model list has no unitary rank-two alternatives. -/
theorem bender_or_CrankTwo_of_rank_twelve
    {Q : Type*} [Group Q] [Finite Q]
    (h : IsTheoremCModel Q) (hr : 12 ≤ primeRank 2 Q) :
    IsBenderModel Q ∨ ∃ f : ℕ, IsTheoremCRankTwoModel Q f := by
  have hr8 : 8 ≤ primeRank 2 Q := by omega
  cases h with
  | alternating n hn he =>
    exact (no_small_alternating_of_twoRank_ge_eight hr8 (by omega) he).elim
  | odd ho => exact (ChapterA.Section02.no_theoremB_odd_model_of_twoRank_ge_eight hr8 ho.toTheoremBOddModel).elim
  | bender hb => exact Or.inl hb
  | rank_two f hf => exact Or.inr ⟨f,hf⟩
  | linear_binary n hn he => exact (no_binary_linear_of_twoRank_ge_eight hr8 hn he).elim
  | sporadic hs =>
    obtain ⟨e⟩ := theoremBSporadic_j4_of_twoRank_ge_eight hr8 hs.toTheoremBSporadicModel
    rw [primeRank_equiv 2 e] at hr
    have := Janko4.TwoRank.model_twoRank_le_eleven
    omega

/-- The original residual and module exclude all non-Ree rows of the
rank-two Theorem C list. The containing quotient map is retained. -/
theorem ree_of_CrankTwo_residual_module
    {G S : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]
    (F K U : Subgroup G) [Group.IsPerfect F]
    (hFK : F ≤ K) (hUF : U ≤ F.pCoreIn 2) (hne : U ≠ ⊥) (hcomm : U = ⁅U,F⁆)
    (hS : ¬ Group.IsSolvable S)
    (hexp : ¬ ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (π : F →* S) (hπ : Function.Surjective π)
    (hr : 12 ≤ primeRank 2 (K ⧸ center K))
    {n : ℕ} (hm : IsTheoremCRankTwoModel (K ⧸ center K) n) :
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty ((K ⧸ center K) ≃* ReeF4.Model m) := by
  have hd : 4096 ∣ Nat.card (K ⧸ center K) := by
    by_contra hd
    have hb : primeRank 2 (K ⧸ center K) ≤ 11 := primeRank_le_of_prime_pow_not_dvd hd
    omega
  cases hm with
  | linear hn hm =>
    exfalso
    obtain ⟨E,hE,hfin,hcard,⟨e⟩⟩ := hm
    let : Fintype E := Fintype.ofFinite E
    let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
      simpa only [Nat.card_eq_fintype_card] using hcard)
    have hn2 : 2 ≤ n := by
      by_contra h
      have he : n = 1 := by omega
      rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hcard,he] at hd
      norm_num at hd
    let r := residualQuotientMap hFK e
    let := residualQuotientMap_kernel_solvable hFK e
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hUF hne hcomm e
    exact no_linear_three_local hS hexp π hπ hn2 hcard _ hp hpne r hnorm
  | symplectic hn hm =>
    exfalso
    obtain ⟨E,hE,hfin,hcard,⟨e⟩⟩ := hm
    let : CharP E 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
    let a := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := E)).symm
    let r := residualQuotientMap hFK a
    let := residualQuotientMap_kernel_solvable hFK a
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hUF hne hcomm a
    exact no_symplectic_four_local hS hexp π hπ _ hp hpne r hnorm
  | g2 hn hm =>
    exfalso
    obtain ⟨E,hE,hfin,hcard,⟨e⟩⟩ := hm
    let : Fintype E := Fintype.ofFinite E
    let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
      simpa only [Nat.card_eq_fintype_card] using hcard)
    have hbig : 2 < Nat.card E := by
      rw [hcard]
      exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
        (Nat.pow_le_pow_right (by decide) hn)
    let r := residualQuotientMap hFK e
    let := residualQuotientMap_kernel_solvable hFK e
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hUF hne hcomm e
    exact no_g2_local hS hexp π hπ hbig _ hp hpne r hnorm
  | triality hn hm =>
    exfalso
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ n (by omega)).mp hm
    let r := residualQuotientMap hFK e
    let := residualQuotientMap_kernel_solvable hFK e
    obtain ⟨hp,hpne,hnorm⟩ := residualQuotientMap_two_local hFK hUF hne hcomm e
    exact no_triality_local hS hexp π hπ n (show 0 < n from hn) _ hp hpne r hnorm
  | ree_f4 m hm _ he => exact ⟨m,hm,he⟩
  | symplectic_derived _ he =>
    exfalso
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv] at hd
    have hd' := hd.trans (commutator (ClassicalGroup.PSp 2 (ZMod 2))).card_subgroup_dvd_card
    rw [← Nat.card_congr
      (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := ZMod 2)).toEquiv,
      Theory.SpecificGroups.SymplecticFour.Binary.card_sp_two] at hd'
    norm_num at hd'
  | g2_derived _ he =>
    exfalso
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv] at hd
    have hd' := hd.trans (commutator (Atlas.G2.Model (ZMod 2))).card_subgroup_dvd_card
    rw [Atlas.G2.card_Model,Nat.card_zmod] at hd'
    norm_num at hd'
  | tits _ he =>
    exfalso
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv,Tits.parrottGroup_card] at hd
    norm_num at hd
end CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl

