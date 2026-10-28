module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.LargeTwoRankBender

/-!
# Theorem C at low cubic rank with a nontrivial moved binary section

Two-rank at least three excludes the odd-characteristic models and A₅.
Cubic rank at most one excludes the remaining alternating, sporadic,
higher binary-linear and rank-two models except binary PSL₃. The precise
survivors are Bender models, binary PSL₃, and J₁. All alternatives retain
actual isomorphisms with the supplied carrier; there is no factor-of-five
hypothesis. The binary-three enlargement consumer separately excludes
each survivor using its original quotient and full Sylow.

Source: Aschbacher--Smith A.3.6 and 10.2.6, printed pp.43--45,748--749.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open Chapter1.Section02
open SQTKStructure.NonnormalOuterSource.FourModels
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

/-- The complete actual-carrier alternatives under the two numerical rank bounds. -/
theorem models_of_three_le_twoRank_low_threeRank
    {G : Type*} [Group G] [Finite G]
    (hm : LocalModels.TheoremCModel G)
    (h2 : 3 ≤ primeRank 2 G) (h3 : primeRank 3 G ≤ 1) :
    ClassificationModels.IsBenderModel G ∨
      (∃ n : ℕ, 1 ≤ n ∧ ClassicalGroup.IsPSL G 3 (2 ^ n)) ∨
      Nonempty (G ≃* Janko1.Model) := by
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
  | rank_one iso => exact Or.inl iso
  | rank_two iso =>
    rcases rank_two_rows iso with ⟨n,hn,hmodel⟩ | hr
    · exact Or.inr (Or.inl ⟨n,hn,hmodel⟩)
    · omega
  | binary_linear n hn iso =>
    have hr := binary_linear_three_rank n hn iso
    omega
  | sporadic name hne iso =>
    let : Finite name.Carrier := Finite.of_equiv G iso.some.toEquiv
    have hr := sporadic_three_rank name hne
    rw [← primeRank_equiv 3 iso.some] at hr
    omega
  | janko_one iso => exact Or.inr (Or.inr iso)

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
