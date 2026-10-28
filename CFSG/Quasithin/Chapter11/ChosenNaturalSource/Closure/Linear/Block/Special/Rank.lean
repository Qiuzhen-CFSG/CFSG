module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special.Center
public import Theory.ElementaryAbelian.GeneratorRank
public import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# The exact rank of U/Z(U)

Counting the original center V₁ C_U(L) cancels the same central
supplement in the order of U. The elementary central quotient has
order q⁴, hence generator rank 4n for q=2ⁿ.
Source: Aschbacher--Smith 11.5.7, refs/quasithin.pdf, printed p.782.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterG.Section02.LinearThree
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D) {x y : G}
  (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)
include d

theorem center_card
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y) :
    Nat.card (center E.W) = 2 ^ E.input.field.degree *
      Nat.card (E.W ⊓ centralizer (L : Set G) : Subgroup G) := by
  rw [Nat.card_congr ((center E.W).equivMapOfInjective E.W.subtype E.W.subtype_injective).toEquiv]
  change Nat.card (closureCenter E) = _
  rw [closureCenter_eq E d hUT hf hc,
    card_sup_eq_mul_of_normalizes_of_disjoint, point_card E d]
  · exact (inf_le_right.trans (centralizer_le (E.V₁_le.trans D.le_component))).trans
      (centralizer_le_normalizer _)
  · apply disjoint_iff.mpr
    exact bot_unique ((inf_le_inf E.V₁_le inf_le_right).trans (chosen_fixed_eq_bot E d).le)

theorem centralQuotient_card
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y) :
    Nat.card (CentralQuotient E) = 2 ^ (4 * E.input.field.degree) := by
  have h := (center E.W).card_mul_index
  rw [index_eq_card, center_card E d hUT hf hc,
    closure_card_mul_centralizer E d hUT hf hc] at h
  have hh : 2 ^ E.input.field.degree * Nat.card (CentralQuotient E) =
      (2 ^ E.input.field.degree) ^ 5 := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < Nat.card
      (E.W ⊓ centralizer (L : Set G) : Subgroup G) from Nat.card_pos)
    calc
      _ = (2 ^ E.input.field.degree * Nat.card
        (E.W ⊓ centralizer (L : Set G) : Subgroup G)) * Nat.card (CentralQuotient E) := by ac_rfl
      _ = _ := h
  apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 ^ E.input.field.degree by positivity)
  rw [hh, Nat.mul_comm 4 E.input.field.degree, pow_mul]
  ring

theorem centralQuotient_rank
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y) :
    Group.rank (CentralQuotient E) = 4 * E.input.field.degree := by
  let := centralQuotient_elementary E d hUT hf
  let : CommGroup (CentralQuotient E) := IsMulCommutative.instCommGroup
  have hcard := centralQuotient_card E d hUT hf hc
  apply le_antisymm (IsElementaryAbelian.rank_le_of_card_le (CentralQuotient E) hcard.le)
  have hd := card_dvd_exponent_pow_rank' (CentralQuotient E)
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (CentralQuotient E)))
  rw [hcard] at hd
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (Nat.le_of_dvd (by positivity) hd)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Special
