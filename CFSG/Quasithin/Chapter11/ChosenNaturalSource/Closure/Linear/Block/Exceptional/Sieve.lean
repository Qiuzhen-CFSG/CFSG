module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Sections
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Statements
public import Mathlib.GroupTheory.Schreier

/-!
# The surviving exceptional case on the original SL₃ marking

The full 11.1.2 alternatives force n=2 under L₁<K. The marked quotient
L/O₂(L) is the full SL₃(4), which excludes case (2). The preceding
11.4.1(2) triangle exclusion then leaves case (1), with its literal
iterated odd-core quotient. Rank 4n becomes eight.

The complete 11.1.2 and triangle conclusions remain explicit inputs;
their producers are qt-d-1222-natural-relative-components and
qt-d-1222-shadow-component-triangle. They belong to the outer assembly.
The special-factor producer supplies the elementary rank-4n conclusion.
This module does not claim the partial classifier is exhaustive.
Source: Aschbacher--Smith 11.1.2, 11.4.1(2), 11.5.7, pp.761,775,782.
-/

@[expose] public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterG.Section02.LinearThree
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D) {x y : G}
  (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)

theorem field_degree_two_of_strict
    (h : RefinementAlternative T L E.L₁ E.L₂ E.K E.X 0 E.input.field.degree)
    (hlt : E.L₁ < E.K) : E.input.field.degree = 2 := by
  cases h with
  | equal he => exact (hlt.ne (by simpa using he)).elim
  | sl2 _ hn _ _ _ => exact hn
  | psl2 _ hn _ _ _ _ _ => exact hn
  | triangle _ hn _ => exact hn

include d in
theorem case_one_of_strict
    (h : RefinementAlternative T L E.L₁ E.L₂ E.K E.X 0 E.input.field.degree)
    (htriangle : ¬ FieldFourTriangle T L E.L₁ E.L₂ E.K E.X)
    (hlt : E.L₁ < E.K) :
    E.input.field.degree = 2 ∧ Nat.card E.input.field.Carrier = 4 ∧
      ∃ p : ℕ, (p = 5 ∨ (p.Prime ∧ 11 ≤ p)) ∧
        Source.IsSL (Source.TwoOddQuotient E.K) 2 p := by
  have hn := field_degree_two_of_strict E h hlt
  have hq : Nat.card E.input.field.Carrier = 4 := by
    rw [d.field_card,hn]
    norm_num
  refine ⟨hn,hq,?_⟩
  cases h with
  | equal he => exact (hlt.ne (by simpa using he)).elim
  | sl2 _ _ p hp hm => exact ⟨p,hp,hm⟩
  | psl2 _ _ p hp hlarge hm hex =>
    exact (hex ⟨E.input.field.Carrier,inferInstance,inferInstance,hq,
      ⟨componentQuotientEquiv E d⟩⟩).elim
  | triangle _ _ ht => exact (htriangle ht).elim

theorem rank_eight_of_strict
    (h : RefinementAlternative T L E.L₁ E.L₂ E.K E.X 0 E.input.field.degree)
    (hlt : E.L₁ < E.K)
    (hr : Group.rank (CentralQuotient E) = 4 * E.input.field.degree) :
    Group.rank (CentralQuotient E) = 8 := by
  rw [hr,field_degree_two_of_strict E h hlt]

open scoped IsMulCommutative in
theorem centralQuotient_card_le_of_rank_eight
    [IsElementaryAbelian 2 (CentralQuotient E)]
    (hr : Group.rank (CentralQuotient E) = 8) :
    Nat.card (CentralQuotient E) ≤ 256 := by
  have hd := card_dvd_exponent_pow_rank' (CentralQuotient E)
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p (p := 2) (G := CentralQuotient E)))
  rw [hr] at hd
  exact Nat.le_of_dvd (by decide) hd

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional
