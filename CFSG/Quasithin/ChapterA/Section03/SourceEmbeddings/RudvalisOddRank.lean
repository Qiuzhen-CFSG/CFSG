module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.LocalRankBound
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality
public import Theory.SpecificGroups.Rudvalis.Model.LowCentralizers.Center
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.GroupTheory.PrimeRankSquareFree
public import Theory.Quasithin.Rank

/-!
# The Rudvalis containing-component exclusion

The checked odd-index maximal two-core theorem and radical-normalizer
catalogue give the full Sylow-overgroup cover by the literal max4 and
max6 carriers. Their orders contain no square of a prime greater than
three. The actual containing component supplies quasisimplicity, and
the native trivial-center theorem removes its two-core. Restriction
retains the original smaller local component and full Sylow.

Source: Aschbacher–Smith A.3.12(20), pp.47–48, used in 1.3.8, p.513.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings

private theorem ru_large_prime_square_not_dvd {p : ℕ} (hp : p.Prime) (hl : 3 < p) :
    ¬ p ^ 2 ∣ 2 ^ 14 * 3 * 5 * 7 := by
  intro hd
  have hpdiv : p ∣ 2 ^ 14 * 3 * 5 * 7 := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hd
  rcases hp.dvd_mul.mp hpdiv with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · have := Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two h
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
        omega
    · have he := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h
      subst p
      norm_num at hd
  · have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)).mp h
    subst p
    norm_num at hd

/-- Every proper full-Sylow overgroup in the genuine Rudvalis carrier
has large odd-prime rank at most one. -/
theorem rudvalis_proper_overgroup_primeRank_le_one
    (hO : pCore 2 Rudvalis.Model = ⊥)
    (S : Sylow 2 Rudvalis.Model) (D : Subgroup Rudvalis.Model)
    (hSD : (S : Subgroup Rudvalis.Model) ≤ D) (hD : D ≠ ⊤)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) : primeRank p D ≤ 1 := by
  obtain ⟨M,hM,hDM⟩ := (eq_top_or_exists_le_coatom D).resolve_left hD
  have hodd : ¬ 2 ∣ M.index := fun hd =>
    S.not_dvd_index (hd.trans (index_dvd_of_le (hSD.trans hDM)))
  have hcover := Rudvalis.SylowOvergroups.oddIndexMaximalCover_of_twoCore_of_radicalCover hO
    Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.rudvalis_oddIndexMaximalTwoCore
    Rudvalis.SylowOvergroups.oddIndexMaximalRadicalCover
  have hcard : Nat.card D ∣ 2 ^ 14 * 3 * 5 * 7 := by
    apply (card_dvd_of_le hDM).trans
    rcases hcover M hM hodd with he | he
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv, Rudvalis.SylowOvergroups.max4_card]
      norm_num
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv, Rudvalis.SylowOvergroups.max6_card]
      norm_num
  exact primeRank_le_one_of_square_not_dvd
    (fun hd => ru_large_prime_square_not_dvd Fact.out hp (hd.trans hcard))

/-- The actual quasisimple Rudvalis component cannot properly contain
the marked local component of large odd-prime rank two. -/
theorem eq_of_rudvalis_containing_component_of_large_odd_rank
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hr : 2 ≤ primeRank p B)
    (hq : IsQuasisimple L) (e : L ≃* Rudvalis.Model) : B = L := by
  let := hq
  let : IsQuasisimple Rudvalis.Model := IsQuasisimple.of_mulEquiv e
  have hO : pCore 2 Rudvalis.Model = ⊥ := bot_unique
    ((IsQuasisimple.pCore_le_center 2).trans_eq Rudvalis.LowCentralizers.model_center_eq_bot)
  apply eq_of_model_proper_local_primeRank_bound T hB hL hBL p hr e
  intro htop S D hd hproper
  have hjoin := local_sup_ne_top_of_ne_top htop S D hd hproper
  exact (primeRank_mono p (show D ≤ D ⊔ (S : Subgroup _) from le_sup_left)).trans
    (rudvalis_proper_overgroup_primeRank_le_one hO S _ le_sup_right hjoin hp)

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
