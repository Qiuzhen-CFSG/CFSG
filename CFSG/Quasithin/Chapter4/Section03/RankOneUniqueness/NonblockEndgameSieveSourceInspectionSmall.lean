module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceInspectionRankOne
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceModelsRank
public import Theory.SpecificGroups.Alternating.TwoThreeCycles
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Alternating and small binary linear rows of the source inspection

The secondary image is proper in the inner component: it normalizes the
nontrivial radical image whereas the entire component does not. Its binary
PSL₂ section therefore has strictly smaller order. In the alternating rows
of Theorem C this leaves degrees six through eight. The cubic-index argument
excludes odd source degree, and the source cubic-rank restriction excludes
the remaining case. The same order and cubic-index calculation excludes
PSL₄(2) and PSL₅(2).

These arguments use the literal inner image, so they also control possible
central covers of the full quotient. Together with the Bender exclusions,
they reduce Theorem C to its odd, rank-two and sporadic rows. The remaining
proper two-local inspection and the full exceptional-model conclusion are
still required. Natural coordinates discharge generation in the source
assembly consumer.
Source: Aschbacher--Smith, 4.3.12--16, printed pp.617--618; A.2.3, p.33.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- The rank-one section has order strictly smaller than the inner component:
the secondary normalizes the radical, but the whole component does not. -/
theorem SecondarySourceData.secondary_order_lt_inner (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    2^n * ((2^n)^2-1) < Nat.card (SecondarySourceData.componentImage s) := by
  let := s.normal
  let X := SourceImages.image c s.component (secondary c)
  let I := SecondarySourceData.componentImage s
  have hlt : X < I := lt_of_le_of_ne (SecondarySourceData.secondaryImage_le_componentImage s) (by
    intro he
    have hn := (SourceImages.radical_geometry c s.component s.radical_normalizer).2.2.2.1
    have hn' : X ≤ normalizer (SecondarySourceData.radicalImage s : Set _) := hn
    rw [he] at hn'
    exact (SecondarySourceData.localImageData s D).proper_normalizer hn')
  have hcard : 2^n * ((2^n)^2-1) ≤ Nat.card X := by
    have hm : ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 (2^n) :=
      SourceImages.secondaryImage_model c s.component s.secondary_le s.secondary_model
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
      simpa only [Nat.card_eq_fintype_card] using hF)
    have hd := card_quotient_dvd_card (pCore 2 X)
    rw [Nat.card_congr (e.trans (Theory.PSL2.sl2QuotientEquiv F).symm).toEquiv,
      BenderSuzuki.External.huppert614_card_specialLinearGroup,hF] at hd
    exact Nat.le_of_dvd Nat.card_pos hd
  apply hcard.trans_lt
  by_contra! hh
  exact hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le hh)

/-- The cubic-index obstruction applies to the literal inner image as well. -/
theorem SecondarySourceData.nine_not_dvd_secondary_order_of_inner
    (s : SecondarySourceData c n)
    (h27 : ¬27 ∣ Nat.card (SecondarySourceData.componentImage s))
    (hr : 2 ≤ primeRank 3 (SecondarySourceData.componentImage s)) :
    ¬9 ∣ 2^n * ((2^n)^2-1) := by
  let := s.normal
  let X := SourceImages.image c s.component (secondary c)
  let I := SecondarySourceData.componentImage s
  let B := X.subgroupOf I
  let e : B ≃* X := subgroupOfEquivOfLe (SecondarySourceData.secondaryImage_le_componentImage s)
  have hm : ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 (2^n) :=
    SourceImages.secondaryImage_model c s.component s.secondary_le s.secondary_model
  have hcard : 2^n * ((2^n)^2-1) ∣ Nat.card B := by
    obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
      simpa only [Nat.card_eq_fintype_card] using hF)
    have hd := card_quotient_dvd_card (pCore 2 X)
    rw [Nat.card_congr (a.trans (Theory.PSL2.sl2QuotientEquiv F).symm).toEquiv,
      BenderSuzuki.External.huppert614_card_specialLinearGroup,hF] at hd
    rwa [Nat.card_congr e.toEquiv]
  intro hd
  have hB : 9 ∣ Nat.card B := hd.trans hcard
  have hi : ¬3 ∣ B.index := by
    intro hi
    have hh := Nat.mul_dvd_mul hB hi
    rw [B.card_mul_index] at hh
    exact h27 hh
  have hb : primeRank 3 B ≤ 1 := by
    rw [primeRank_congr 3 e]
    exact odd_primeRank_le_one hm (by decide)
  rw [B.primeRank_eq_of_not_dvd_index hi] at hb
  change primeRank 3 (SecondarySourceData.componentImage s) ≤ 1 at hb
  omega

/-- Every alternating row of Theorem C is excluded on the actual inner image,
so this also retains all possible central covers of the full quotient. -/
theorem SecondarySourceData.not_alternating_inner (s : SecondarySourceData c n)
    (hn : 1<n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {m : ℕ} (hm : m≤8)
    (e : SecondarySourceData.componentImage s ≃* alternatingGroup (Fin m)) : False := by
  have hdiv := SecondarySourceData.secondary_order_dvd_inner s
  have hpow : 4≤2^n := Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) (by omega : 2≤n)
  have hpow2 : 16≤(2^n)^2 := Nat.pow_le_pow_left hpow 2
  have h60 : 60≤2^n*((2^n)^2-1) := Nat.mul_le_mul hpow (by omega : 15≤(2^n)^2-1)
  have hm2 : 2≤m := by
    by_contra! hh
    have hc : Nat.card (SecondarySourceData.componentImage s) = 1 := by
      rw [Nat.card_congr e.toEquiv]
      interval_cases m <;> exact Nat.card_unique
    rw [hc] at hdiv
    have := Nat.le_of_dvd (by decide : 0<1) hdiv
    omega
  let : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm2
  have hlt := SecondarySourceData.secondary_order_lt_inner s D
  rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin] at hdiv hlt
  have hm6 : 6≤m := by
    by_contra! hh
    interval_cases m <;> norm_num [Nat.factorial] at hlt <;> omega
  have h9 := SecondarySourceData.nine_not_dvd_secondary_order_of_inner s
    (by rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
        interval_cases m <;> norm_num [Nat.factorial])
    (by rw [primeRank_congr 3 e]
        exact alternatingGroup.TwoThreeCycles.two_le_primeRank hm6)
  have hn7 : n<7 := by
    by_contra! hh
    have hd2 := (Nat.pow_dvd_pow 2 hh).trans ((dvd_mul_right _ _).trans hdiv)
    interval_cases m <;> norm_num [Nat.factorial] at hd2
  have hn2 : n=2 := by
    interval_cases m
    all_goals norm_num [Nat.factorial] at hdiv
    all_goals interval_cases n
    all_goals omega
  have hz := SecondarySourceData.componentQuotient_center_eq_bot_of_three_dvd s D h
    (by rw [hn2]; decide)
  let a : (s.component ⧸ pCore 2 s.component) ≃* alternatingGroup (Fin m) :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.trans
      ((SecondarySourceData.centralQuotientEquiv s).trans e)
  have hr := SecondarySourceData.component_primeRank_eq_one_of_alternating s D h
    Nat.prime_three (by decide) (by rw [hn2]; decide) (by omega) a
  have hl : 2≤primeRank 3 s.component := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup,
      primeRank_congr 3 a]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank hm6
  omega

/-- The two higher-dimensional binary linear rows also fail the source prime
restriction. The index argument removes every odd candidate source degree. -/
theorem SecondarySourceData.not_binary_linear_inner (s : SecondarySourceData c n)
    (hn : 1<n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {m : ℕ} (hm : m=4 ∨ m=5)
    (hmodel : ClassicalGroup.IsPSL (SecondarySourceData.componentImage s) m 2) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let a := (e.trans (Atlas.fieldEquivPSL m eF)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega : 0<m))
  let b := a.trans ((BinaryLinear.OuterCyclic.slEquivLinear m).trans
    (BinaryLinear.OuterCyclic.matrixEquivLinear m).symm)
  have hc : Nat.card (SecondarySourceData.componentImage s) =
      ∏ i : Fin m, (2^m - 2^i.val) := by
    rw [Nat.card_congr b.toEquiv,Matrix.card_GL_field]
    simp
  have hr : 2≤primeRank 3 (SecondarySourceData.componentImage s) := by
    rw [primeRank_congr 3 a]
    exact BinaryLinear.SmallCubicRank.four_or_five hm
  have h9 := SecondarySourceData.nine_not_dvd_secondary_order_of_inner s
    (by rw [hc]; rcases hm with rfl | rfl <;> norm_num [Fin.prod_univ_succ]) hr
  have hd := SecondarySourceData.secondary_order_dvd_inner s
  rw [hc] at hd
  have hn11 : n<11 := by
    by_contra! hh
    have hd2 := (Nat.pow_dvd_pow 2 hh).trans ((dvd_mul_right _ _).trans hd)
    rcases hm with rfl | rfl <;> norm_num [Fin.prod_univ_succ] at hd2
  have hnE : Even n := by
    rcases hm with rfl | rfl
    all_goals norm_num [Fin.prod_univ_succ] at hd
    all_goals interval_cases n
    all_goals first | decide | (solve | norm_num at h9) | (solve | norm_num at hd)
  have hz := SecondarySourceData.componentQuotient_center_eq_bot_of_three_dvd s D h
    ((Nat.BinaryTorusParity.three_dvd_sub_one_iff _).mpr hnE)
  let bfull : (s.component ⧸ pCore 2 s.component) ≃* SecondarySourceData.componentImage s :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.trans
      (SecondarySourceData.centralQuotientEquiv s)
  have hmfull : ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) m 2 :=
    (show ClassicalGroup.IsPSL (SecondarySourceData.componentImage s) m 2 from
      ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩).of_mulEquiv bfull
  have hu := SecondarySourceData.component_primeRank_eq_one_of_binary_linear s D h
    Nat.prime_three (by decide) ((Nat.BinaryTorusParity.three_dvd_sub_one_iff _).mpr hnE) hm hmfull
  have hl : 2≤primeRank 3 s.component := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup,
      primeRank_congr 3 bfull]
    exact hr
  omega

/-- After excluding alternating, Bender and the higher binary linear rows on the
literal inner image, Theorem C leaves only its odd, rank-two and sporadic rows.
This is a reduced catalogue, not the final four-row inspection. -/
theorem SecondarySourceData.inspection_remaining_models (s : SecondarySourceData c n)
    (hn : 1<n) (hg : SecondarySourceData.ActionGeneration s)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    ChapterA.Section02.IsTheoremCOddModel (SecondarySourceData.componentImage s) ∨
      (∃ f : ℕ, ChapterA.Section02.IsTheoremCRankTwoModel
        (SecondarySourceData.componentImage s) f) ∨
      ChapterA.Section02.IsTheoremCSporadicModel (SecondarySourceData.componentImage s) := by
  have hm := SecondarySourceData.componentImage_theoremC s D h
  cases hm with
  | alternating m hm he =>
    exact (SecondarySourceData.not_alternating_inner s hn D h hm (Classical.choice he)).elim
  | odd hm => exact Or.inl hm
  | bender hm => exact (SecondarySourceData.not_bender_inner_of_generation s hn hg hm).elim
  | rank_two f hm => exact Or.inr (Or.inl ⟨f,hm⟩)
  | linear_binary m hm he =>
    exact (SecondarySourceData.not_binary_linear_inner s hn D h hm he).elim
  | sporadic hm => exact Or.inr (Or.inr hm)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
