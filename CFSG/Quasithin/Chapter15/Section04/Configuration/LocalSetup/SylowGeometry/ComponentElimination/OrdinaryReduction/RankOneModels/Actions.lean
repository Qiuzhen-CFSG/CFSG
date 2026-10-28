module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.Inputs
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.Actions
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.Orders

/-!
# Comparing ordinary rank-one seeds with the actions in 1.1.5

The center of the ordinary component is its two-core because the ambient odd
core is trivial. This excludes both alternating triple covers. The orders of
A₆ and A₇ exclude the remaining alternating alternatives from the actual
rank-one quotient. Every surviving clause of 1.1.5 supplies an inner witness;
transport through the component inclusion implements every source actor by
an element of that same component.

The companion comparison modules address the component identification. The
inner-action theorem here is independent of those model comparisons and
does not assume or assert the resulting simple-model identification.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.4.20, printed p.1164; all six clauses of 1.1.5(3), printed pp.501–503.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination
open OrdinaryReduction OrdinaryReduction.RankOneModels
open Chapter15.Section03.Candidates.ComponentStructure

namespace OrdinaryReduction.RankOneModels
variable {L : Type*} [Group L]

private theorem not_three_center (hcenter : center L = pCore 2 L)
    (he : Nonempty (center L ≃* Multiplicative (ZMod 3))) : False := by
  obtain ⟨e⟩ := he
  have hc : Nat.card (pCore 2 L) = 3 := by
    rw [← hcenter, Nat.card_congr e.toEquiv]
    simp
  rcases (pCore_isPGroup (p := 2) (G := L)).card_eq_or_dvd with h | h <;>
    rw [hc] at h <;> norm_num at h

private theorem core_eq_bot_of_alternating {n : ℕ} (hn : 4 ≤ n)
    (e : L ≃* alternatingGroup (Fin n)) (hcenter : center L = pCore 2 L) :
    pCore 2 L = ⊥ := by
  apply Subgroup.card_eq_one.mp
  rw [← hcenter, Nat.card_congr (Subgroup.centerCongr e).toEquiv,
    alternatingGroup.center_eq_bot (by simpa using hn), Subgroup.card_bot]

/-- Both alternating actions, including their nonsplit triple covers, are
incompatible with the given rank-one quotient and component center. -/
theorem not_alternating_action (hm : RankOneQuotientModel L)
    (hcenter : center L = pCore 2 L) {α : MulAut L} {n : ℕ}
    (hn : n = 6 ∨ n = 7) (σ : Equiv.Perm (Fin n)) :
    ¬ AlternatingAction α n σ := by
  rintro (⟨e, _⟩ | ⟨_, he, _⟩)
  · have hc := core_eq_bot_of_alternating (by rcases hn with rfl | rfl <;> decide)
      e hcenter
    let eq : (L ⧸ pCore 2 L) ≃* L :=
      (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
    have hcard := Nat.card_congr (eq.trans e).toEquiv
    rcases hn with rfl | rfl
    · rw [nat_card_alternatingGroup] at hcard
      norm_num only [Nat.card_fin, Nat.factorial] at hcard
      exact quotient_card_ne_360 (L := L) hm hcard
    · rw [nat_card_alternatingGroup] at hcard
      norm_num only [Nat.card_fin, Nat.factorial] at hcard
      exact quotient_card_ne_2520 (L := L) hm hcard
  · exact not_three_center hcenter he

/-- All six source cases are inspected. Once the alternating cases are
excluded, the source provides a literal inner automorphism of the seed. -/
theorem inner_of_model_action (hm : RankOneQuotientModel L)
    (hcenter : center L = pCore 2 L) {α : MulAut L} (ha : ModelAction115 L α) :
    α ∈ (MulAut.conj (G := L)).range := by
  cases ha with
  | lie _ _ hi => exact hi
  | two_cover _ _ _ hi => exact hi
  | six σ _ ha => exact (not_alternating_action hm hcenter (Or.inl rfl) σ ha).elim
  | seven σ _ ha => exact (not_alternating_action hm hcenter (Or.inr rfl) σ ha).elim
  | odd _ hi => exact hi
  | sporadic _ _ _ ha => exact ha.1

end OrdinaryReduction.RankOneModels

variable {G : Type*} [Group G] [Finite G]

/-- Every source actor is implemented by an element of the actual ordinary
seed. No simple-model or model-disjointness premise is assumed. -/
theorem rank_one_seed_inner {κ : GroupClass} (hG : IsSimpleQTKE κ G)
    (earlier : Chapter15.Section03.Candidates.ComponentStructure.Earlier115Three κ G)
    {d : Source.Geometry G} {i j : Bool} {H K U : Subgroup G}
    (s : SourceContext d i j H K U) (b : PairEmbedding H K U)
    (hodd : pPrimeCore 2 H = ⊥) (hcomponent : IsComponent H b.seed) :
    CentralInnerAction (b.seed.map H.subtype) d.Z := by
  intro z
  by_cases hz : z = 1
  · subst z
    exact ⟨1, by intro x; simp⟩
  obtain ⟨P, M, hlocal⟩ := s.local115 z z.property (fun he => hz (Subtype.ext he))
  obtain ⟨_, _, α, hα, hm⟩ := earlier hG H P M z hlocal b.seed hcomponent
  obtain ⟨l, hl⟩ := inner_of_model_action b.model
    (Chapter15.Section03.component_center_eq_twoCore hcomponent hodd) hm
  let e := b.seed.equivMapOfInjective H.subtype H.subtype_injective
  refine ⟨e l, ?_⟩
  intro x
  obtain ⟨x, rfl⟩ := e.surjective x
  change (z : G) * (x : G) * (z : G)⁻¹ = (l : G) * (x : G) * (l : G)⁻¹
  rw [← hα x]
  exact (congrArg (fun f : MulAut b.seed => ((f x : H) : G)) hl).symm

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination
