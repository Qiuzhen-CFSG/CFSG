module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointSmallModels
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeAmbientSourceNormalizer
public import Theory.Quasithin.PositiveLocalRank
public import Theory.SpecificGroups.PSL2.OuterSolvable.SmallDegreeTwoGroup
public import Theory.GroupTheory.PrimeRankSquareFree
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.PrimeRankHom

/-!
# The ambient cubic-rank obstruction for the quadratic linear carrier

The actual smaller component B has a centreless PSL₃(2) two-core
quotient and full normalizer of cubic rank at most one. A subgroup
centralizing B therefore has cubic rank zero. In particular the kernel
of ambient conjugation on any normal containing K contributes no cubic
rank. The original ambient rank is bounded by that of Aut(K).

For K = PSL₂(49), its order has three-part three and its full outer
automorphism group is a two-group. Thus Aut(K) has cubic rank at most
one, excluding the actual rank-two point-centralizer quotient. Together
with the prime-field exclusion and the quadratic parameter restriction,
this excludes every odd-linear Theorem C carrier at the original point.

Source: Aschbacher--Smith A.3.12 and the setting of 15.3.23,
printed pp.47--48 and 1128--1129; GLS3 Theorem 2.5.12 for Aut(PSL₂).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
variable {X : Type*} [Group X] [Finite X]

/-- The original smaller normalizer bound removes the entire cubic rank
of the conjugation kernel on a normal containing subgroup. -/
theorem binary_three_ambient_rank_le_automorphism
    {B K : Subgroup X} [K.Normal] (hBK : B ≤ K)
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    (hr : primeRank 3 (normalizer (B : Set X)) ≤ 1) :
    primeRank 3 X ≤ primeRank 3 (MulAut K) := by
  let A := centralizer (K : Set X)
  have hc : A ≤ centralizer (B : Set X) := centralizer_le hBK
  have hn : A ≤ normalizer (B : Set X) := hc.trans (Subgroup.centralizer_le_normalizer _)
  let eSL := eB.trans Matrix.PSL3Two.equiv.symm
  have hz : Nat.Coprime 3 (Nat.card (center (B ⧸ pCore 2 B))) := by
    rw [Nat.card_congr (centerCongr eSL).toEquiv,Matrix.PSL3Two.center_eq_bot,card_bot]
    decide
  have hcomm : ⁅(pResidual 2 A).map A.subtype,B⁆ ≤ B.pCoreIn 2 := by
    have hb : ⁅A,B⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hc
    exact (commutator_mono (map_subtype_le _) le_rfl).trans (hb ▸ bot_le)
  have hsum := ResidualCentralizerRank.primeRank_sum_le_of_normalized_factor
    (by decide : Odd 3) A B hn hcomm hz
  have hB : 1 ≤ primeRank 3 B := by
    have hq : 1 ≤ primeRank 3 (B ⧸ pCore 2 B) := by
      apply Theory.Quasithin.one_le_primeRank_of_dvd_card
      rw [Nat.card_congr eSL.toEquiv,Matrix.PSL3Two.card_SL]
      decide
    rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 B) pCore_isPGroup] at hq
    exact hq
  have hu := (primeRank_mono 3 (sup_le hn B.le_normalizer)).trans hr
  have hA : primeRank 3 A = 0 := by omega
  let f : X →* MulAut K := MulAut.conjNormal
  have hh := primeRank_le_ker_add (p := 3) f
  rw [show f.ker = A from MulAut.conjNormal_ker_eq_centralizer K,hA,zero_add] at hh
  exact hh

private theorem quadratic_seven_automorphism_rank
    {K : Type*} [Group K] [Finite K] (hm : ClassicalGroup.IsPSL K 2 49) :
    primeRank 3 (MulAut K) ≤ 1 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  rw [primeRank_equiv 3 (MulAut.congr e)]
  have ho : IsPGroup 2 (MulAut.Outer PSL(2,F)) :=
    Theory.PSL2.OuterSolvable.SmallDegreeSquares.outer_isPGroup_two
      (by decide : Nat.Prime 7) (by decide : Odd 7) (n := 2) (by decide) hF
  have houter : primeRank 3 (MulAut.Outer PSL(2,F)) = 0 := by
    apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
    obtain ⟨n,hn⟩ := ho.exists_card_eq
    rw [hn]
    exact fun hd => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  have horder := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
    (hF ▸ (by decide : Odd 49))
  rw [hF] at horder
  have hcard : Nat.card PSL(2,F) = 58800 := by omega
  have hinner : primeRank 3 (MulAut.innerSubgroup PSL(2,F)) ≤ 1 := by
    apply primeRank_le_one_of_square_not_dvd
    intro hd
    have hi : Nat.card (MulAut.innerSubgroup PSL(2,F)) ∣ Nat.card PSL(2,F) :=
      card_dvd_of_surjective (MulAut.conj : PSL(2,F) →* MulAut PSL(2,F)).rangeRestrict
        (MulAut.conj : PSL(2,F) →* MulAut PSL(2,F)).rangeRestrict_surjective
    have hh := hd.trans hi
    rw [hcard] at hh
    norm_num at hh
  have hr := primeRank_le_ker_add (p := 3)
    (QuotientGroup.mk' (MulAut.innerSubgroup PSL(2,F)))
  rw [QuotientGroup.ker_mk'] at hr
  change primeRank 3 (MulAut PSL(2,F)) ≤
    primeRank 3 (MulAut.innerSubgroup PSL(2,F)) + primeRank 3 (MulAut.Outer PSL(2,F)) at hr
  rw [houter,add_zero] at hr
  exact hr.trans hinner

/-- A normal PSL₂(49) carrier cannot contain the original binary-three
subgroup in an ambient group of cubic rank at least two. -/
theorem binary_three_point_not_linear_fortyNine
    {B K : Subgroup X} [K.Normal] (hBK : B ≤ K)
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    (hr : primeRank 3 (normalizer (B : Set X)) ≤ 1)
    (hX : 2 ≤ primeRank 3 X) (hm : ClassicalGroup.IsPSL K 2 49) : False := by
  have hle := (binary_three_ambient_rank_le_automorphism hBK eB hr).trans
    (quadratic_seven_automorphism_rank hm)
  omega

/-- All odd-linear Theorem C rows are excluded with the actual full Sylow,
normal containing component, original smaller quotient, and ambient ranks. -/
theorem binary_three_point_not_odd_linear
    (S : Sylow 2 X) {B K : Subgroup X} [K.Normal]
    (hB : B ∈ ChapterA.Section03.localCComponents S) (hK : K.IsCComponent) (hBK : B < K)
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    (hr : primeRank 3 (normalizer (B : Set X)) ≤ 1) (hX : 2 ≤ primeRank 3 X)
    {p n : ℕ} (hp : p.Prime) (ho : Odd p) (hn : n = 1 ∨ n = 2)
    (hm : ClassicalGroup.IsPSL K 2 (p ^ n)) : False := by
  rcases hn with rfl | rfl
  · exact binary_three_point_not_prime_linear S hB hK hBK eB hp ho (by simpa using hm)
  · have hp7 := binary_three_point_quadratic_prime_eq_seven S hB hK hBK eB hp ho hm
    subst p
    exact binary_three_point_not_linear_fortyNine hBK.le eB hr hX hm

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
