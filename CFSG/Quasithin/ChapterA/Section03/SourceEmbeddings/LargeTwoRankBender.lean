module

public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.RemainingRows
public import CFSG.Quasithin.ChapterA.Section02.OddModelTwoRank
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank
public import Theory.SpecificGroups.Janko1.Model.SylowTwo
public import Theory.GroupTheory.PrimeRankAutomorphismOrder
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The Bender row from two-rank, cubic rank and a factor of five

Within the actual Theorem C catalogue, two-rank at least four excludes the
odd-characteristic rows, A₅ and J₁. Three-rank at most one excludes the other
alternating, sporadic, binary linear and rank-two rows except PSL₃ over a
binary field. In that last row, low cubic rank forces odd field degree, and
the general linear order is prime to five. The original factor of five
therefore leaves precisely a Bender model.

The statement is about the supplied finite carrier and its genuine model
marking. It assumes no desired classification. Source: Aschbacher--Smith
A.3.6 and the ordinary-component comparison in 10.2.6, printed pp.44–45,
748–749.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open Chapter1.Section02
open SQTKStructure.NonnormalOuterSource.FourModels

private theorem two_pow_odd_mod_five (n : ℕ) (hn : Odd n) :
    2 ^ n % 5 = 2 ∨ 2 ^ n % 5 = 3 := by
  have hn2 := Nat.odd_iff.mp hn
  have hn4 : n % 4 = 1 ∨ n % 4 = 3 := by omega
  have he : n = 4 * (n / 4) + n % 4 := by omega
  rw [he,pow_add,pow_mul,Nat.mul_mod]
  have hpow : (2 ^ 4) ^ (n / 4) % 5 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  rw [hpow]
  rcases hn4 with h | h <;> rw [h] <;> norm_num

private theorem binary_psl3_not_five
    {F : Type*} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hr : primeRank 3 PSL(3,F) ≤ 1) : ¬ 5 ∣ Nat.card PSL(3,F) := by
  have ho : Odd n := by
    apply Nat.not_even_iff_odd.mp
    intro he
    have hh := Theory.SpecificGroups.SignedThreeCubicRank.linear_projective hF he
    omega
  let q := Nat.card F
  have hq : q % 5 = 2 ∨ q % 5 = 3 := by
    rw [show q = 2 ^ n from hF]
    exact two_pow_odd_mod_five n ho
  have hqpos : 1 ≤ q := Nat.card_pos
  have h1 : 1 ≤ q ^ 3 := one_le_pow₀ hqpos
  have h2 : q ≤ q ^ 3 := by simpa using Nat.pow_le_pow_right hqpos (by decide : 1 ≤ 3)
  have h3 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right hqpos (by decide : 2 ≤ 3)
  have hsub1 := Nat.sub_add_cancel h1
  have hsub2 := Nat.sub_add_cancel h2
  have hsub3 := Nat.sub_add_cancel h3
  have ha : ¬ 5 ∣ q ^ 3 - 1 := by
    intro hd
    have hz := Nat.mod_eq_zero_of_dvd hd
    have hm := congrArg (fun n => n % 5) hsub1
    rw [Nat.add_mod,Nat.pow_mod] at hm
    rcases hq with hh | hh <;> rw [hh] at hm <;> norm_num at hm <;> omega
  have hb : ¬ 5 ∣ q ^ 3 - q := by
    intro hd
    have hz := Nat.mod_eq_zero_of_dvd hd
    have hm := congrArg (fun n => n % 5) hsub2
    rw [Nat.add_mod,Nat.pow_mod] at hm
    rcases hq with hh | hh <;> rw [hh] at hm <;> norm_num at hm <;> omega
  have hc : ¬ 5 ∣ q ^ 3 - q ^ 2 := by
    intro hd
    have hz := Nat.mod_eq_zero_of_dvd hd
    have hm := congrArg (fun n => n % 5) hsub3
    rcases hq with hh | hh <;> norm_num [Nat.add_mod,Nat.pow_mod,hh,hz] at hm
  intro hd
  have hsl := hd.trans (card_dvd_of_surjective (Matrix.PSL3.projection F)
    (Matrix.PSL3.projection_surjective F))
  have hgl := hsl.trans (card_dvd_of_injective
    (Matrix.SpecialLinearGroup.toGL : SL(3,F) →* GL (Fin 3) F)
    Matrix.SpecialLinearGroup.toGL_injective)
  let : Fintype F := Fintype.ofFinite _
  have hcard : Nat.card (GL (Fin 3) F) = (q ^ 3 - 1) * (q ^ 3 - q) * (q ^ 3 - q ^ 2) := by
    simpa [Nat.card_eq_fintype_card,q,Fin.prod_univ_succ,mul_assoc] using
      Matrix.card_GL_field (𝔽 := F) 3
  rw [hcard] at hgl
  rcases (by decide : Nat.Prime 5).dvd_mul.mp hgl with hab | hc'
  · exact ((by decide : Nat.Prime 5).dvd_mul.mp hab).elim ha hb
  · exact hc hc'

private theorem alternating_five_twoRank_le_two :
    primeRank 2 (alternatingGroup (Fin 5)) ≤ 2 := by
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro E hE
  obtain ⟨n,hn⟩ := hE.isPGroup.exists_card_eq
  have hd := E.card_subgroup_dvd_card
  rw [hn,nat_card_alternatingGroup] at hd
  norm_num at hd
  have hnle : n ≤ 2 := by
    by_contra! hnle
    have he : 8 ∣ 60 := (pow_dvd_pow 2 hnle).trans hd
    norm_num at he
  rw [hn]
  exact Nat.pow_le_pow_right (by decide) hnle

private theorem janko_one_twoRank_le_three : primeRank 2 Janko1.Model ≤ 3 := by
  let P : Sylow 2 Janko1.Model := Classical.choice inferInstance
  rw [P.primeRank_eq]
  apply primeRank_le_of_card_le_prime_pow
  rw [Janko1.SylowTwo.card]
  decide

/-- The actual Theorem C carrier is a Bender model under the three source
numerical constraints. -/
theorem bender_of_large_twoRank_low_threeRank_five
    {G : Type*} [Group G] [Finite G]
    (hm : LocalModels.TheoremCModel G)
    (h2 : 4 ≤ primeRank 2 G) (h3 : primeRank 3 G ≤ 1)
    (h5 : 5 ∣ Nat.card G) : ClassificationModels.IsBenderModel G := by
  cases hm with
  | alternating n hn he =>
    obtain ⟨e⟩ := he
    have hnlt : n < 6 := by
      by_contra! hge
      have hl := alternatingGroup.TwoThreeCycles.two_le_primeRank hge
      rw [← primeRank_equiv 3 e] at hl
      omega
    have hn5 : n = 5 := by omega
    subst n
    have hl := alternating_five_twoRank_le_two
    rw [← primeRank_equiv 2 e] at hl
    omega
  | linear_odd p n hp ho he _ iso =>
    have hr := (Section02.IsTheoremCOddModel.linear_two p n hp ho (by
      rcases he with h | h <;> omega) iso).twoRank_le_two
    omega
  | three_odd p hp ho unitary iso =>
    have hm : Section02.IsTheoremCOddModel G := by
      cases unitary with
      | false => exact .linear_three p hp ho iso
      | true => exact .unitary_three p hp ho iso
    have hr := hm.twoRank_le_two
    omega
  | rank_one iso => exact iso
  | rank_two iso =>
    rcases rank_two_rows iso with ⟨n,_,hmodel⟩ | hr
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmodel
      have hr : primeRank 3 PSL(3,F) ≤ 1 := (primeRank_equiv 3 e) ▸ h3
      exact (binary_psl3_not_five hF hr ((Nat.card_congr e.toEquiv) ▸ h5)).elim
    · omega
  | binary_linear n hn iso =>
    have hr := binary_linear_three_rank n hn iso
    omega
  | sporadic name hne iso =>
    let : Finite name.Carrier := Finite.of_equiv G iso.some.toEquiv
    have hr := sporadic_three_rank name hne
    rw [← primeRank_equiv 3 iso.some] at hr
    omega
  | janko_one iso =>
    have hr := janko_one_twoRank_le_three
    rw [← primeRank_equiv 2 iso.some] at hr
    omega

/-- The numerical inputs may be supplied by a faithful original actor,
without identifying it with a different subgroup or quotient. -/
theorem bender_of_faithful_large_twoRank_actor
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    (hm : LocalModels.TheoremCModel G) (h3 : primeRank 3 G ≤ 1)
    (f : A →* G) (hf : Function.Injective f)
    (h2 : 4 ≤ primeRank 2 A) (h5 : 5 ∣ Nat.card A) :
    ClassificationModels.IsBenderModel G :=
  bender_of_large_twoRank_low_threeRank_five hm
    (h2.trans (Theory.GroupTheory.primeRank_le_of_injective 2 f hf)) h3
    (h5.trans (card_dvd_of_injective f hf))

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
