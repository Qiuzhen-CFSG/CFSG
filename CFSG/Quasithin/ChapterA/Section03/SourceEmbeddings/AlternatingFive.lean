module
public import CFSG.Quasithin.ChapterA.Section03.Basic
public import Theory.GroupTheory.GeneralizedFitting.ComponentCoprimeRankNormal
public import Theory.SpecificGroups.Alternating.SevenFivePlacement.ThreeCycles
public import Theory.SpecificGroups.AlternatingSix.ProperSylowOvergroups
public import Theory.Alternating.PrimeRank
/-!
# Full-Sylow local A5 subgroups in A6 and A7

In A6, every proper Sylow-two overgroup has order eight or twenty-four,
so adjoining an A5 gives the entire simple group. In A7, an A5 local
component is normal in its Sylow join: otherwise its distinct conjugates
would force five-rank at least two. Thus the existing seven-letter
placement theorem applies to the original subgroup.

Source: Aschbacher–Smith 2.4.25, printed p.543, the M22 and M23 local rows.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings

private theorem alternating_quasisimple (n : ℕ) (hn : 5 ≤ n) :
    IsQuasisimple (alternatingGroup (Fin n)) where
  toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simpa using hn)⟩
  simple := by
    let : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup (by simpa using hn)
    exact ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp; omega))).trans QuotientGroup.quotientBot).isSimpleGroup

/-- A local A5 in A7 is normalized by the same full Sylow subgroup. -/
theorem alternatingSeven_local_five_normalized
    (B : Subgroup (alternatingGroup (Fin 7)))
    (e : B ≃* alternatingGroup (Fin 5)) (S : Sylow 2 (alternatingGroup (Fin 7)))
    (hB : B ∈ ChapterA.Section03.localCComponents S) :
    (S : Subgroup (alternatingGroup (Fin 7))) ≤ normalizer (B : Set _) := by
  let H := B ⊔ (S : Subgroup (alternatingGroup (Fin 7)))
  let D := B.subgroupOf H
  let d : D ≃* alternatingGroup (Fin 5) := (subgroupOfEquivOfLe le_sup_left).trans e
  let := alternating_quasisimple 5 (by decide)
  let : IsQuasisimple D := IsQuasisimple.of_mulEquiv d.symm
  have hc : IsComponent H D := ⟨hB.subnormal,inferInstance⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hz : Nat.card (center D) = 1 := by
    rw [Nat.card_congr (centerCongr d).toEquiv,alternatingGroup.center_eq_bot (by simp),card_bot]
  have hrD : primeRank 5 D = 1 := by
    rw [primeRank_equiv 5 d,GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 5 5 (by decide) (by decide)]
  have hrH : primeRank 5 H ≤ 1 := by
    have hh := Theory.GroupTheory.primeRank_le_of_injective 5 H.subtype H.subtype_injective
    rw [GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 7 5 (by decide) (by decide)] at hh
    exact hh
  have hn : D.Normal := hc.normal_of_coprime_center_primeRank 5 (by rw [hz]; decide) (by omega)
  exact le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer le_sup_left).mp hn)


/-- An A5 subgroup cannot be local at a full Sylow of A6. -/
theorem alternatingSix_not_local_five
    (B : Subgroup (alternatingGroup (Fin 6)))
    (e : B ≃* alternatingGroup (Fin 5)) (S : Sylow 2 (alternatingGroup (Fin 6))) :
    B ∉ ChapterA.Section03.localCComponents S := by
  have hc : Nat.card B = 60 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num
  have hjoin : B ⊔ (S : Subgroup (alternatingGroup (Fin 6))) = ⊤ := by
    by_contra hn
    have hd := card_dvd_of_le (show B ≤ B ⊔ (S : Subgroup (alternatingGroup (Fin 6))) from le_sup_left)
    rw [hc] at hd
    rcases AlternatingSix.ProperSylowOvergroups.card_eight_or_twentyFour S _ le_sup_right hn with h | h <;>
      rw [h] at hd <;> norm_num at hd
  intro hlocal
  change (B.subgroupOf (B ⊔ (S : Subgroup (alternatingGroup (Fin 6))))).IsCComponent at hlocal
  rw [hjoin] at hlocal
  have hsub : B.IsSubnormal := by
    have hh := hlocal.subnormal.trans' IsSubnormal.top
    simpa only [map_subgroupOf_eq_of_le le_top] using hh
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rcases hsub.eq_bot_or_top_of_isSimpleGroup inferInstance with h | h
  · rw [h,card_bot] at hc
    norm_num at hc
  · rw [h,card_top,nat_card_alternatingGroup] at hc
    norm_num at hc

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
