module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.ModelWitnesses
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.PrimeRankZero

/-!
# Selecting the diagonal branch by the actual three-rank bound

A noncyclic Sylow three-subgroup supplies an elementary subgroup of order nine.
An independent centralizing element of order three would give rank at least
three. For a component with two-group center this excludes a distinct conjugate
component, so a rank-two component is normal in its rank-two overgroup.

The orbit in 15.3.37 therefore equals L. Its containment branch contradicts
Y₊ ≰ L, and its rank-one models contradict m₃(L)=2. Only the intrinsic rank
bound for those models and the model clauses of the earlier alternatives are
inputs. The weakened rank-one clause works with the three-part correction of
15.3.37(2), without using its incompatible full-order clause.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
1.2.1 and the opening of the proof of 15.3.38, printed pp.503 and 1135.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
variable {G : Type*} [Group G] [Finite G]

theorem exists_elementary_nine (hrank : 2 ≤ primeRank 3 G) :
    ∃ E : Subgroup G, IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  classical
  let P : Sylow 3 G := Classical.choice inferInstance
  have hn : ¬ IsCyclic P := by
    intro h
    have := P.primeRank_le_one_of_isCyclic h
    omega
  obtain ⟨E, _, hc, hE⟩ :=
    P.isPGroup'.exists_normal_elementary_prime_sq_of_odd_not_isCyclic (by decide) hn
  let := hE
  refine ⟨E.map (P : Subgroup G).subtype, IsElementaryAbelian.map _, ?_⟩
  exact (Nat.card_congr (equivMapOfInjective E _ Subtype.val_injective).toEquiv).symm.trans hc

theorem no_centralizing_three {L : Subgroup G}
    (hrank : primeRank 3 G ≤ 2) (hLrank : 2 ≤ primeRank 3 L)
    (hcenter : center L ≤ pCore 2 L)
    {x : G} (hx : orderOf x = 3) (hxC : x ∈ centralizer (L : Set G)) : False := by
  obtain ⟨E, hE, hcard⟩ := exists_elementary_nine hLrank
  let := hE
  let A := E.map L.subtype
  let : IsElementaryAbelian 3 A := IsElementaryAbelian.map _
  have hxL : x ∉ L := by
    intro hxL
    have hxZ : (⟨x, hxL⟩ : L) ∈ center L := by
      exact mem_center_iff.mpr (fun l => Subtype.ext (hxC l l.property))
    have hp := (pCore_isPGroup (p := 2) (G := L)).orderOf_coprime
      (by decide : Nat.Coprime 2 3) (⟨⟨x, hxL⟩, hcenter hxZ⟩ : pCore 2 L)
    simp only [Subgroup.orderOf_mk, hx] at hp
    norm_num at hp
  have hAcard : Nat.card A = 3 ^ 2 :=
    (Nat.card_congr (equivMapOfInjective E _ L.subtype_injective).toEquiv).symm.trans hcard
  have hfix : A ≤ centralizer ({x} : Set G) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (hxC a ((map_subtype_le E) ha))
  have h := IsElementaryAbelian.primeRank_ge_of_fixed_join A x hx
    (fun ha => hxL ((map_subtype_le E) ha)) hfix hAcard
  omega

theorem rank_two_component_normal {L : Subgroup G}
    (hL : IsComponent G L) (hodd : pPrimeCore 2 G = ⊥)
    (hrank : primeRank 3 G ≤ 2) (hLrank : primeRank 3 L = 2) : L.Normal := by
  have hcenter := (component_center_eq_twoCore hL hodd).le
  have hdvd : 3 ∣ Nat.card L := by
    by_contra hd
    have := PrimeRank.eq_zero_iff_not_dvd_card.mpr hd
    omega
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := L) 3 hdvd
  have hnorm : (⊤ : Subgroup G) ≤ normalizer (L : Set G) := by
    intro g _
    apply mem_normalizer_iff_map_conj_eq.mpr
    by_contra he
    have hcomm := (hL.map_conj g).commutator_eq_bot_of_ne hL he
    have hxC := (commutator_eq_bot_iff_le_centralizer.mp hcomm)
      (mem_map_of_mem (MulAut.conj g).toMonoidHom y.property)
    have hx : orderOf ((MulAut.conj g) (y : G)) = 3 :=
      ((MulAut.conj g).orderOf_eq (y : G)).trans ((orderOf_injective L.subtype L.subtype_injective y).trans hy)
    exact no_centralizing_three hrank hLrank.ge hcenter hx hxC
  exact normalizer_eq_top_iff.mp (top_unique hnorm)

/-- Relative normality follows from the actual three-rank bound. -/
theorem rank_two_component_normal_in {I L : Subgroup G}
    (hLI : L ≤ I) (hL : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥) (hrank : primeRank 3 I ≤ 2)
    (hLrank : primeRank 3 L = 2) : (L.subgroupOf I).Normal := by
  apply rank_two_component_normal hL hodd hrank
  exact (primeRank_equiv 3 (subgroupOfEquivOfLe hLI)).trans hLrank

/-- Only the model clauses of 15.3.37 are needed; this also accepts the
three-part repair of its rank-one branch. The diagonal branch is a deduction. -/
theorem diagonal_of_rank_two {I L S Yplus : Subgroup G}
    (hLI : L ≤ I) (hSI : S ≤ I) (hL : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥) (hrank : primeRank 3 I ≤ 2)
    (hLrank : primeRank 3 L = 2) (hYL : ¬ Yplus ≤ L)
    (hmodels : Candidates.RankOneModel L → primeRank 3 L ≤ 1)
    (h37 : Yplus ≤ localSpan L S ∨ Candidates.RankOneModel L ∨
      Candidates.RankTwoDiagonal Yplus L (localSpan L S)) :
    (L.subgroupOf I).Normal ∧ Candidates.RankTwoDiagonal Yplus L (localSpan L S) := by
  have hn := rank_two_component_normal_in hLI hL hodd hrank hLrank
  have hIL := (normal_subgroupOf_iff_le_normalizer hLI).mp hn
  have hspan : localSpan L S ≤ L := conjugateSpanBy_le le_rfl (hSI.trans hIL)
  refine ⟨hn, ?_⟩
  rcases h37 with h | h | h
  · exact (hYL (h.trans hspan)).elim
  · have := hmodels h
    omega
  · exact h

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
