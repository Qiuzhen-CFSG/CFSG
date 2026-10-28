module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceInspectionHeld
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.Mathieu.M23.Properties.PointStabilizer
public import Theory.SpecificGroups.Rudvalis.Model.Order
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.FourSporadic
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceInspectionTernary
/-!
# Remaining source degrees and model rows

Held is excluded on the literal inner image. Each of the four remaining
sporadic carriers has cubic rank at least two, so the original source torus
forces odd degree. The actual orders of M₂₄, J₂ and Ru then force degree
three. J₄ remains at odd degree; no unproved order bound is used for it.

The final catalogue combines these restrictions with the odd ternary section
bound and preserves every binary rank-two row still needing local inspection.
Natural coordinates discharge generation in the source assembly consumer.
Source: Aschbacher--Smith 4.3.12(2), 4.3.16 and A.2.3, printed pp.617--618, 33.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
open ClassificationModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

private theorem remaining_sporadic_cubic_rank {name : SporadicName}
    (hn : name = .m24 ∨ name = .j2 ∨ name = .j4 ∨ name = .ru) :
    2 ≤ primeRank 3 name.Carrier := by
  rcases hn with rfl | rfl | rfl | rfl
  · change 2 ≤ primeRank 3 Sporadic.Mathieu.M24
    have h1 := Theory.GroupTheory.primeRank_le_of_injective 3
      Sporadic.Mathieu.m23EquivM22PointStabilizer.toMonoidHom
      Sporadic.Mathieu.m23EquivM22PointStabilizer.injective
    have h2 := Theory.GroupTheory.primeRank_le_of_injective 3
      (MulAction.stabilizer Sporadic.Mathieu.M23 (9 : Fin 23)).subtype
      (MulAction.stabilizer Sporadic.Mathieu.M23 (9 : Fin 23)).subtype_injective
    let f := Sporadic.Mathieu.m23ExtendHom.codRestrict Sporadic.Mathieu.M24
      Sporadic.Mathieu.m23Extend_mem_M24
    have hf : Function.Injective f := fun x y hh =>
      Sporadic.Mathieu.m23ExtendHom_injective (congrArg Subtype.val hh)
    exact Sporadic.Mathieu.m22_primeRank_three.ge.trans
      (h1.trans (h2.trans (Theory.GroupTheory.primeRank_le_of_injective 3 f hf)))
  · exact Sporadic.LeechRelated.J2.three_rank_ge_two
  · exact ChapterA.Section03.OddPrime.SourceModels.FourSporadic.j4_three_rank_ge_two
  · exact ChapterA.Section03.OddPrime.SourceModels.FourSporadic.rudvalis_three_rank_ge_two

/-- Seven sporadic exclusions leave four carriers, all in odd source degree. -/
theorem SecondarySourceData.sporadic_remaining_odd_degree
    (s : SecondarySourceData c n) (hn : 1<n) (hg : SecondarySourceData.ActionGeneration s)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hm : ChapterA.Section02.IsTheoremCSporadicModel (SecondarySourceData.componentImage s)) :
    Odd n ∧ ∃ name : SporadicName,
      (name = .m24 ∨ name = .j2 ∨ name = .j4 ∨ name = .ru) ∧
      Nonempty (SecondarySourceData.componentImage s ≃* name.Carrier) := by
  obtain ⟨name,hname,⟨e⟩⟩ := SecondarySourceData.inspection_sporadic_remaining s hn hg D h hm
  have hnames : name = .m24 ∨ name = .j2 ∨ name = .j4 ∨ name = .ru := by
    rcases hname with hname | hname | hname | rfl | hname
    · exact Or.inl hname
    · exact Or.inr (Or.inl hname)
    · exact Or.inr (Or.inr (Or.inl hname))
    · exact (SecondarySourceData.not_held_inner s hn D h e).elim
    · exact Or.inr (Or.inr (Or.inr hname))
  let : Finite name.Carrier := Finite.of_equiv (SecondarySourceData.componentImage s) e.toEquiv
  refine ⟨Nat.not_even_iff_odd.mp ?_, name,hnames,⟨e⟩⟩
  intro he
  exact SecondarySourceData.not_sporadic_inner_of_even s he D h hm (by
    rw [primeRank_congr 3 e]
    exact remaining_sporadic_cubic_rank hnames)

private theorem degree_three_of_order {k m : ℕ} (hk : 1<k) (ho : Odd k)
    (hm : m=244823040 ∨ m=604800 ∨ m=145926144000)
    (hd : 2^k*((2^k)^2-1) ∣ m) : k=3 := by
  have hk15 : k<15 := by
    by_contra! hh
    have hd2 := (Nat.pow_dvd_pow 2 hh).trans ((dvd_mul_right _ _).trans hd)
    rcases hm with rfl | rfl | rfl <;> norm_num at hd2
  rcases hm with rfl | rfl | rfl
  all_goals interval_cases k
  all_goals first | rfl | (solve | norm_num at hd) | (solve | norm_num at ho)

/-- The concrete M₂₄, J₂ and Ru orders force degree three; J₄ retains odd degree. -/
theorem SecondarySourceData.sporadic_remaining_degree_three_or_janko_four
    (s : SecondarySourceData c n) (hn : 1<n) (hg : SecondarySourceData.ActionGeneration s)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hm : ChapterA.Section02.IsTheoremCSporadicModel (SecondarySourceData.componentImage s)) :
    Odd n ∧ ((n=3 ∧ ∃ name : SporadicName,
      (name = .m24 ∨ name = .j2 ∨ name = .ru) ∧
      Nonempty (SecondarySourceData.componentImage s ≃* name.Carrier)) ∨
      Nonempty (SecondarySourceData.componentImage s ≃* Janko4.Model)) := by
  obtain ⟨ho,name,hname,⟨e⟩⟩ :=
    SecondarySourceData.sporadic_remaining_odd_degree s hn hg D h hm
  refine ⟨ho,?_⟩
  have hd := SecondarySourceData.secondary_order_dvd_inner s
  rw [Nat.card_congr e.toEquiv] at hd
  rcases hname with rfl | rfl | rfl | rfl
  · left
    refine ⟨degree_three_of_order hn ho (m := 244823040) (by simp) ?_,.m24,by simp,⟨e⟩⟩
    simpa only [SporadicName.Carrier,Sporadic.Mathieu.m24_order] using hd
  · left
    refine ⟨degree_three_of_order hn ho (m := 604800) (by simp) ?_,.j2,by simp,⟨e⟩⟩
    simpa only [SporadicName.Carrier,
      Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier] using hd
  · exact Or.inr ⟨e⟩
  · left
    refine ⟨degree_three_of_order hn ho (m := 145926144000) (by simp) ?_,.ru,by simp,⟨e⟩⟩
    simpa only [SporadicName.Carrier,Rudvalis.model_card] using hd

/-- The remaining actual inner models, including their source-degree restrictions.
This is the input frontier for the remaining proper two-local inspection. -/
theorem SecondarySourceData.inspection_remaining_rows
    (s : SecondarySourceData c n) (hn : 1<n) (hg : SecondarySourceData.ActionGeneration s)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    ((n=2 ∨ n=3) ∧ ∃ p : ℕ, p.Prime ∧ Odd p ∧
      (ClassicalGroup.IsPSL (SecondarySourceData.componentImage s) 3 p ∨
        ClassicalGroup.IsPSU (SecondarySourceData.componentImage s) 3 p)) ∨
      (∃ f : ℕ, ChapterA.Section02.IsTheoremCRankTwoModel
        (SecondarySourceData.componentImage s) f) ∨
      (Odd n ∧ ((n=3 ∧ ∃ name : SporadicName,
        (name = .m24 ∨ name = .j2 ∨ name = .ru) ∧
        Nonempty (SecondarySourceData.componentImage s ≃* name.Carrier)) ∨
        Nonempty (SecondarySourceData.componentImage s ≃* Janko4.Model))) := by
  rcases SecondarySourceData.inspection_remaining_models_without_odd_rank_one s hn hg D h
    with ⟨p,hp,ho,hm⟩ | hm | hm
  · have hb := SecondarySourceData.odd_ternary_degree_le_three s hp ho hm
    exact Or.inl ⟨by omega,p,hp,ho,hm⟩
  · exact Or.inr (Or.inl hm)
  · exact Or.inr (Or.inr
      (SecondarySourceData.sporadic_remaining_degree_three_or_janko_four s hn hg D h hm))

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
