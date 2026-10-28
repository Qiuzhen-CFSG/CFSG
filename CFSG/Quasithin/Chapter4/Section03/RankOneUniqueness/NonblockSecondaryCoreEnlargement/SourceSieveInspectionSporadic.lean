module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceSieveInspectionOdd
public import Theory.Mathieu.M11.Properties.RankLower
public import Theory.Mathieu.M12.Properties.ThreeRank
public import Theory.Mathieu.M22.Properties.ThreeRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.ThreeRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound
/-!
# Six sporadic exclusions on the actual source inner image

The ordinary cubic ranks of M₁₁, M₁₂, M₂₂, M₂₃ and HS are at least two.
The source secondary order and the cubic-index obstruction force even source
degree in these models. The original torus then has a cubic actor, making the
full quotient centerless and contradicting the proved sporadic rank-one
restriction. For HS the certified order divisibility bound suffices.

The J₁ order forces degree two directly. The same center calculation recovers
the full quotient model, where the checked core-movement and generation
argument excludes it. All isomorphisms concern the literal inner image; no
central cover is discarded. The consumer leaves only M₂₄, J₂, J₄, He and Ru
in the sporadic part of the remaining catalogue.
Source: Aschbacher--Smith, 4.3.12--16, printed pp.617--618; A.2.3, p.33.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
open ClassificationModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- A cubic rank of at least two excludes every sporadic row in even source degree. -/
theorem SecondaryActionData.not_sporadic_inner_of_even
    (s : SecondaryActionData c n) (he : Even n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hm : ChapterA.Section02.IsTheoremCSporadicModel (SecondaryActionData.componentImage s))
    (hr : 2 ≤ primeRank 3 (SecondaryActionData.componentImage s)) : False := by
  have hd := (Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mpr he
  have hz := SecondaryActionData.componentQuotient_center_eq_bot_of_three_dvd s D h hd
  let a : (s.component ⧸ pCore 2 s.component) ≃* SecondaryActionData.componentImage s :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.trans
      (SecondaryActionData.sieveCentralQuotientEquiv s)
  have hu := SecondaryActionData.component_primeRank_eq_one_of_sporadic s D h
    Nat.prime_three (by decide) hd hz (hm.of_mulEquiv a)
  have hl : 2 ≤ primeRank 3 s.component := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup,
      primeRank_congr 3 a]
    exact hr
  omega

private theorem five_sporadic_rank {name : SporadicName}
    (hn : name = .m11 ∨ name = .m12 ∨ name = .m22 ∨ name = .m23 ∨ name = .hs) :
    2 ≤ primeRank 3 name.Carrier := by
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact Sporadic.Mathieu.m11_primeRank_three_ge_two
  · exact Sporadic.Mathieu.m12_three_rank_ge_two
  · exact Sporadic.Mathieu.m22_primeRank_three.ge
  · have h1 := Theory.GroupTheory.primeRank_le_of_injective 3
      Sporadic.Mathieu.m23EquivM22PointStabilizer.toMonoidHom
      Sporadic.Mathieu.m23EquivM22PointStabilizer.injective
    have h2 := Theory.GroupTheory.primeRank_le_of_injective 3
      (MulAction.stabilizer Sporadic.Mathieu.M23 (9 : Fin 23)).subtype
      (MulAction.stabilizer Sporadic.Mathieu.M23 (9 : Fin 23)).subtype_injective
    exact Sporadic.Mathieu.m22_primeRank_three.ge.trans (h1.trans h2)
  · exact Sporadic.LeechRelated.HS.ThreeRank.two_le_primeRank

private theorem small_sporadic_order_even {k m : ℕ} (hk : 1<k)
    (hm : m=7920 ∨ m=443520 ∨ m=10200960 ∨ m=44352000)
    (hd : 2^k*((2^k)^2-1) ∣ m) (h9 : ¬9 ∣ 2^k*((2^k)^2-1)) : Even k := by
  have hk10 : k<10 := by
    by_contra! hh
    have hd2 := (Nat.pow_dvd_pow 2 hh).trans ((dvd_mul_right _ _).trans hd)
    rcases hm with rfl | rfl | rfl | rfl <;> norm_num at hd2
  rcases hm with rfl | rfl | rfl | rfl
  all_goals interval_cases k
  all_goals first | decide | (solve | norm_num at h9) | (solve | norm_num at hd)

private theorem m12_order_even {k : ℕ} (hk : 1<k)
    (hd : 2^k*((2^k)^2-1) ∣ 95040) : Even k := by
  have hk7 : k<7 := by
    by_contra! hh
    have hd2 := (Nat.pow_dvd_pow 2 hh).trans ((dvd_mul_right _ _).trans hd)
    norm_num at hd2
  interval_cases k
  all_goals first | decide | (solve | norm_num at hd)

/-- Order and cubic-index calculations exclude these five actual sporadic carriers. -/
theorem SecondaryActionData.not_five_sporadic_inner
    (s : SecondaryActionData c n) (hn : 1<n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {name : SporadicName}
    (hm : name = .m11 ∨ name = .m12 ∨ name = .m22 ∨ name = .m23 ∨ name = .hs)
    (e : SecondaryActionData.componentImage s ≃* name.Carrier) : False := by
  classical
  let : Finite name.Carrier := Finite.of_equiv (SecondaryActionData.componentImage s) e.toEquiv
  have hr : 2 ≤ primeRank 3 (SecondaryActionData.componentImage s) := by
    rw [primeRank_congr 3 e]
    exact five_sporadic_rank hm
  apply SecondaryActionData.not_sporadic_inner_of_even s ?_ D h
    (Or.inl ⟨name,by rcases hm with rfl | rfl | rfl | rfl | rfl <;> (intro hh; cases hh),⟨e⟩⟩) hr
  have hd := SecondaryActionData.secondary_order_dvd_inner s
  by_cases hm12 : name = .m12
  · subst name
    simp only [Nat.card_congr e.toEquiv,SporadicName.Carrier,Sporadic.Mathieu.m12_order] at hd
    exact m12_order_even hn hd
  have hbound : ∃ m : ℕ, (m=7920 ∨ m=443520 ∨ m=10200960 ∨ m=44352000) ∧
      Nat.card (SecondaryActionData.componentImage s) ∣ m := by
    rw [Nat.card_congr e.toEquiv]
    rcases hm with rfl | rfl | rfl | rfl | rfl
    · exact ⟨7920,by simp,by simp only [SporadicName.Carrier,Sporadic.Mathieu.m11_order,dvd_refl]⟩
    · exact (hm12 rfl).elim
    · exact ⟨443520,by simp,by simp only [SporadicName.Carrier,Sporadic.Mathieu.m22_order,dvd_refl]⟩
    · exact ⟨10200960,by simp,by simp only [SporadicName.Carrier,Sporadic.Mathieu.m23_order,dvd_refl]⟩
    · exact ⟨44352000,by simp,Sporadic.LeechRelated.HS.card_carrier_dvd⟩
  obtain ⟨m,hm,hb⟩ := hbound
  have h27 : ¬27 ∣ Nat.card (SecondaryActionData.componentImage s) := by
    intro hh
    have ht := hh.trans hb
    rcases hm with rfl | rfl | rfl | rfl <;> norm_num at ht
  exact small_sporadic_order_even hn hm (hd.trans hb)
    (SecondaryActionData.nine_not_dvd_secondary_order_of_inner s h27 hr)

/-- The J₁ inner model forces degree two, so the full-quotient exclusion applies. -/
theorem SecondaryActionData.not_janko_inner_of_generation
    (s : SecondaryActionData c n) (hn : 1<n) (hg : SecondaryActionData.ActionGeneration s)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (e : SecondaryActionData.componentImage s ≃* Janko1.Model) : False := by
  have hd := SecondaryActionData.secondary_order_dvd_inner s
  rw [Nat.card_congr e.toEquiv,Janko1.card_model] at hd
  have hn4 : n<4 := by
    by_contra! hh
    have hd2 := (Nat.pow_dvd_pow 2 hh).trans ((dvd_mul_right _ _).trans hd)
    norm_num at hd2
  have hn2 : n=2 := by
    interval_cases n
    all_goals first | rfl | (solve | norm_num at hd)
  subst n
  have hz := SecondaryActionData.componentQuotient_center_eq_bot_of_three_dvd s D h (by decide)
  let a : (s.component ⧸ pCore 2 s.component) ≃* Janko1.Model :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.trans
      ((SecondaryActionData.sieveCentralQuotientEquiv s).trans e)
  exact SecondaryActionData.not_nonexceptional_of_generation s (by decide) hg
    (Or.inr (Or.inr ⟨rfl,Or.inr ⟨a⟩⟩))
/-- The sporadic inspection retains five actual model carriers. No family
name is used without the corresponding isomorphism of the literal inner image. -/
theorem SecondaryActionData.inspection_sporadic_remaining
    (s : SecondaryActionData c n) (hn : 1<n) (hg : SecondaryActionData.ActionGeneration s)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hm : ChapterA.Section02.IsTheoremCSporadicModel (SecondaryActionData.componentImage s)) :
    ∃ name : SporadicName,
      (name = .m24 ∨ name = .j2 ∨ name = .j4 ∨ name = .he ∨ name = .ru) ∧
      Nonempty (SecondaryActionData.componentImage s ≃* name.Carrier) := by
  rcases hm with ⟨name,hname,⟨e⟩⟩ | ⟨e⟩
  · cases name with
    | m11 => exact (SecondaryActionData.not_five_sporadic_inner s hn D h (by simp) e).elim
    | m12 => exact (SecondaryActionData.not_five_sporadic_inner s hn D h (by simp) e).elim
    | m22 => exact (SecondaryActionData.not_five_sporadic_inner s hn D h (by simp) e).elim
    | m23 => exact (SecondaryActionData.not_five_sporadic_inner s hn D h (by simp) e).elim
    | hs => exact (SecondaryActionData.not_five_sporadic_inner s hn D h (by simp) e).elim
    | m24 => exact ⟨.m24,by simp,⟨e⟩⟩
    | j2 => exact ⟨.j2,by simp,⟨e⟩⟩
    | j3 => exact (hname rfl).elim
    | j4 => exact ⟨.j4,by simp,⟨e⟩⟩
    | he => exact ⟨.he,by simp,⟨e⟩⟩
    | ru => exact ⟨.ru,by simp,⟨e⟩⟩
  · exact (SecondaryActionData.not_janko_inner_of_generation s hn hg D h e.some).elim

/-- The source image catalogue after the odd rank-one and six sporadic
exclusions. The remaining proper two-local rows stay with the final sieve. -/
theorem SecondaryActionData.inspection_remaining_ternary_rank_two_large_sporadic
    (s : SecondaryActionData c n) (hn : 1<n) (hg : SecondaryActionData.ActionGeneration s)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    (∃ p : ℕ, p.Prime ∧ Odd p ∧
      (ClassicalGroup.IsPSL (SecondaryActionData.componentImage s) 3 p ∨
        ClassicalGroup.IsPSU (SecondaryActionData.componentImage s) 3 p)) ∨
      (∃ f : ℕ, ChapterA.Section02.IsTheoremCRankTwoModel
        (SecondaryActionData.componentImage s) f) ∨
      (∃ name : SporadicName,
        (name = .m24 ∨ name = .j2 ∨ name = .j4 ∨ name = .he ∨ name = .ru) ∧
        Nonempty (SecondaryActionData.componentImage s ≃* name.Carrier)) := by
  rcases SecondaryActionData.inspection_remaining_models_without_odd_rank_one s hn hg D h
    with hm | hm | hm
  · exact Or.inl hm
  · exact Or.inr (Or.inl hm)
  · exact Or.inr (Or.inr (SecondaryActionData.inspection_sporadic_remaining s hn hg D h hm))

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
