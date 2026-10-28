module
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourceA5Local
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.TwoLocalOrders
/-!
# The ordinary Ree row is excluded by the original A₅ seed

The literal central quotient of the ordinary component contains the image
of the source span and its nontrivial radical intersection. The A₅ seed
forces both three and five to divide the order of their normalizer, because
the quotient loses only a two-group. Every nontrivial two-subgroup normalizer
in a large Ree group is fifteen-free, giving the contradiction directly.

Source: Aschbacher–Smith C.3.5, printed p.150, specialized to the genuine
A₅ covering configuration of 4.2.12–13. The concrete full-parabolic order
and normalizer-cover inputs are proved in ReeF4.ConverseParabolics.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

/-- The actual A₅ seed excludes a model whose nontrivial two-normalizers are fifteen-free. -/
theorem no_ordinary_a5_of_fifteen_free_two_normalizers
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K)
    {S : Type*} [Group S] [Finite S] (e : K ⧸ center K ≃* S)
    (hfree : ∀ P : Subgroup S, P ≠ ⊥ → IsPGroup 2 P →
      ¬ 15 ∣ Nat.card (normalizer (P : Set S))) : False := by
  obtain ⟨_,hP,hne,hn,hr⟩ := h.ordinary_quotient_local_data K hK
  let A := (((conjugateSpanBy L M).subgroupOf H).subgroupOf K).map
    (QuotientGroup.mk' (center K))
  let P := ((R.subgroupOf H).subgroupOf K).map (QuotientGroup.mk' (center K))
  let B := A.map e.toMonoidHom
  let Q := P.map e.toMonoidHom
  have hb : B ≤ normalizer (Q : Set S) :=
    (map_mono hn).trans (P.le_normalizer_map e.toMonoidHom)
  have hd (p : ℕ) (hp : p.Prime) (ho : Odd p)
      (hl : 0 < primeRank p (alternatingGroup (Fin 5))) :
      p ∣ Nat.card (normalizer (Q : Set S)) := by
    let : Fact p.Prime := ⟨hp⟩
    have hl' : 0 < primeRank p L := by
      have hle := primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 L) pCore_isPGroup
      rw [primeRank_congr p a] at hle
      omega
    have hspan : 0 < primeRank p (conjugateSpanBy L M) :=
      lt_of_lt_of_le hl' (Theory.GroupTheory.primeRank_le_of_injective p
        (inclusion (le_conjugateSpanBy L M)) (inclusion_injective _))
    have hA : 0 < primeRank p A := by rwa [hr p hp ho]
    have hB : 0 < primeRank p B := by
      exact lt_of_lt_of_eq hA (primeRank_congr p (e.subgroupMap A))
    have hN : 0 < primeRank p (normalizer (Q : Set S)) :=
      lt_of_lt_of_le hB (Theory.GroupTheory.primeRank_le_of_injective p
        (inclusion hb) (inclusion_injective hb))
    by_contra hnot
    exact (Nat.ne_of_gt hN) (PrimeRank.eq_zero_iff_not_dvd_card.mpr hnot)
  have h3 := hd 3 Nat.prime_three (by decide) (by
    rw [GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 5 3 (by decide) (by decide)]
    decide)
  have h5 := hd 5 (by decide) (by decide) (by
    rw [GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 5 5 (by decide) (by decide)]
    decide)
  apply hfree Q (fun he => hne ((map_eq_bot_iff_of_injective P e.injective).mp he)) (hP.map _)
  exact (show Nat.Coprime 3 5 by decide).mul_dvd_of_dvd_of_dvd h3 h5

/-- The genuine A₅ source configuration has no ordinary component with a large Ree central quotient. -/
theorem no_ordinary_a5_reeF4
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : IsComponent H K)
    {m : ℕ} (hm : 1 ≤ m) (e : K ⧸ center K ≃* ReeF4.Model m) : False :=
  h.no_ordinary_a5_of_fifteen_free_two_normalizers a K hK e
    (fun P hne hp => ReeF4.ConverseParabolics.normalizer_fifteen_free hm P hne hp)
end CFSG.Quasithin.ChapterC.HypothesisC28
