module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceInspectionCentralCore
public import Theory.Mathieu.M24.Properties.CubicExponent
public import Theory.SpecificGroups.Rudvalis.CubicExponent
public import Theory.SpecificGroups.PSL2.EightOrderNine
public import Theory.SpecificGroups.Janko4.BinaryEightSection

/-!
# Cubic Sylow obstructions in the remaining sporadic source rows

The actual secondary image has a PSL₂(8) quotient at source degree three.
An element of order nine in that quotient lifts to an element whose order
is divisible by nine in the inner component. The checked exponent-three
Sylow subgroups of M₂₄, Ru and J₄ exclude this, without killing either the
secondary two-core or a central cover of the full component quotient.

The previous degree restrictions therefore remove M₂₄ and Ru completely.
The actual J₄ order leaves only source degree five. The remaining catalogue
retains that row, the degree-two odd ternary rows and all binary rank-two
rows; it does not assume the final exceptional-model alternative.
Natural coordinates discharge generation in NonblockEndgameSieveSourceAssembly.
Source: Aschbacher--Smith 4.3.12(2), 4.3.14--16 and A.2.3,
printed pp.617--618 and 33; the ATLAS carriers and attribution remain in
CubicExponent and BinaryEightSection.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- The literal inner component contains an element with order divisible by nine. -/
theorem SecondarySourceData.inner_nine_dvd_element_order (s : SecondarySourceData c 3) :
    ∃ a : SecondarySourceData.componentImage s, 9 ∣ orderOf a := by
  let := s.normal
  let X := SecondarySourceData.secondaryImage s
  have hm : ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 (2^3) :=
    SourceImages.secondaryImage_model c s.component s.secondary_le s.secondary_model
  obtain ⟨F,_,_,hF,⟨d⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 3) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let a := d.trans (Theory.PSL2.sl2QuotientEquiv F).symm
  let f := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hf : Function.Surjective f := a.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨y,hy⟩ := Matrix.SL2.exists_orderOf_nine hF
  obtain ⟨z,hz⟩ := hf y
  let j := inclusion (SecondarySourceData.secondaryImage_le_componentImage s)
  refine ⟨j z,?_⟩
  rw [orderOf_injective j (inclusion_injective _),←hy,←hz]
  exact orderOf_map_dvd f z

/-- The actual M₂₄ carrier excludes the degree-three secondary quotient. -/
theorem SecondarySourceData.not_mathieu_twenty_four_inner_degree_three
    (s : SecondarySourceData c 3)
    (e : SecondarySourceData.componentImage s ≃* Sporadic.Mathieu.M24) : False := by
  obtain ⟨a,ha⟩ := SecondarySourceData.inner_nine_dvd_element_order s
  exact Sporadic.Mathieu.m24_not_nine_dvd_orderOf (e a) (by rwa [e.orderOf_eq])

/-- The actual Rudvalis carrier excludes the degree-three secondary quotient. -/
theorem SecondarySourceData.not_rudvalis_inner_degree_three
    (s : SecondarySourceData c 3)
    (e : SecondarySourceData.componentImage s ≃* Rudvalis.Model) : False := by
  obtain ⟨a,ha⟩ := SecondarySourceData.inner_nine_dvd_element_order s
  exact Rudvalis.not_nine_dvd_orderOf (e a) (by rwa [e.orderOf_eq])

/-- The actual J₄ carrier excludes the degree-three secondary quotient. -/
theorem SecondarySourceData.not_janko_four_inner_degree_three
    (s : SecondarySourceData c 3)
    (e : SecondarySourceData.componentImage s ≃* Janko4.Model) : False := by
  obtain ⟨a,ha⟩ := SecondarySourceData.inner_nine_dvd_element_order s
  let P := Classical.choice (inferInstance : Nonempty (Sylow 3 Janko4.Model))
  exact not_nine_dvd_orderOf_of_sylow_cube P
    (Janko4.three_subgroup_cube_eq_one _ P.isPGroup') (e a) (by rwa [e.orderOf_eq])

/-- The J₄ row forces source degree five once the earlier odd-degree restriction holds. -/
theorem SecondarySourceData.janko_four_degree_eq_five
    (s : SecondarySourceData c n) (hn : 1<n) (ho : Odd n)
    (e : SecondarySourceData.componentImage s ≃* Janko4.Model) : n=5 := by
  have hd := SecondarySourceData.secondary_order_dvd_inner s
  rw [Nat.card_congr e.toEquiv,Janko4.Cardinality.model_card] at hd
  have hb : n<22 := by
    by_contra! hh
    have hdiv := (Nat.pow_dvd_pow 2 hh).trans ((dvd_mul_right _ _).trans hd)
    norm_num at hdiv
  have hchoices : n=3 ∨ n=5 := by
    interval_cases n
    all_goals first | (solve | left; rfl) | (solve | right; rfl) |
      (solve | norm_num at hd) | (solve | omega) | (solve | norm_num at ho)
  rcases hchoices with rfl | hh
  · exact (SecondarySourceData.not_janko_four_inner_degree_three s e).elim
  · exact hh

/-- The source catalogue after the cubic Sylow exclusions, retaining all remaining rows. -/
theorem SecondarySourceData.inspection_remaining_rows_after_sporadic_exponent
    (s : SecondarySourceData c n) (hn : 1<n) (hg : SecondarySourceData.ActionGeneration s)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    (n=2 ∧ ∃ p : ℕ, p.Prime ∧ Odd p ∧
      (ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 p ∨
        ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 p)) ∨
      (∃ f : ℕ, ChapterA.Section02.IsTheoremCRankTwoModel
        (SecondarySourceData.componentImage s) f) ∨
      (n=5 ∧ Nonempty (SecondarySourceData.componentImage s ≃* Janko4.Model)) := by
  rcases SecondarySourceData.inspection_remaining_rows_after_core_analysis s hn hg D h with
    hm | hm | ⟨ho,hm⟩
  · exact Or.inl hm
  · exact Or.inr (Or.inl hm)
  · rcases hm with ⟨rfl,name,hname,⟨e⟩⟩ | ⟨e⟩
    · rcases hname with rfl | rfl
      · exact (SecondarySourceData.not_mathieu_twenty_four_inner_degree_three s e).elim
      · exact (SecondarySourceData.not_rudvalis_inner_degree_three s e).elim
    · obtain ⟨e⟩ := e
      exact Or.inr (Or.inr ⟨SecondarySourceData.janko_four_degree_eq_five s hn ho e,⟨e⟩⟩)
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
