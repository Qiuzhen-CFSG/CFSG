module

public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexSetup
public import Stellmacher.SectionEight.GeneratedEightSixBaseSetup
public import Stellmacher.SectionEight.GeneratedEightSixFirstCommutator
public import Stellmacher.SectionFiveToSeven.NeighborJoinCore

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem eight_six_twice_next_core_card_le
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph) :
    2 * Nat.card (QAt graph path.firstStep) ≤ Nat.card S := by
  have hle := (SevenSix.local_cores_le_edge_sylow hyp graph path).2
  have hne : S ≠ QAt graph path.firstStep := by
    change S ≠ graph.twoCoreAt path.firstStep
    rw [graph.twoCoreAt_def]
    exact (SevenSix.edge_local_data hyp graph path).2.1.1.2.2.2
  have hindex := ((QAt graph path.firstStep).subgroupOf S).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at hindex
  have hpos : 0 < ((QAt graph path.firstStep).subgroupOf S).index := by
    have hS : 0 < Nat.card S := Nat.card_pos
    nlinarith
  have hnotone : ((QAt graph path.firstStep).subgroupOf S).index ≠ 1 := by
    intro hone
    have hreverse : S ≤ QAt graph path.firstStep := Subgroup.relIndex_eq_one.mp hone
    exact hne (le_antisymm hreverse hle)
  have htwo : 2 ≤ ((QAt graph path.firstStep).subgroupOf S).index := by omega
  exact hindex ▸ Nat.mul_le_mul_right (Nat.card (QAt graph path.firstStep)) htwo

public theorem eight_six_next_core_noncommutative_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hlength : ctx.criticalPath.length = 2)
    (hcomm : ⁅VAt ctx.Γ ctx.criticalPath.firstStep,
      QAt ctx.Γ ctx.criticalPath.firstStep⁆ = ZAt ctx.Γ ctx.criticalPath.firstStep) :
    ¬ IsMulCommutative (QAt ctx.Γ ctx.criticalPath.firstStep) := by
  intro habelian
  have hV := SevenSix.neighbor_join_le_core_of_length_gt_one
    ctx.Γ ctx.criticalPath (by omega) ctx.criticalPath.firstStep
  have hzero := Subgroup.commutator_self_eq_bot_iff.mpr habelian
  have hline : ZAt ctx.Γ ctx.criticalPath.firstStep = ⊥ := by
    rw [← hcomm]
    exact le_bot_iff.mp ((Subgroup.commutator_mono hV le_rfl).trans_eq hzero)
  have htwo := (eight_six_first_step_fixed_line_local ctx hcenter hcard).1
  rw [hline, Subgroup.card_bot] at htwo
  omega

public theorem eight_six_next_core_bounds
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (hyp : SectionSevenHypotheses G S P1 P2)
    (graph : CosetGraphContext G S P1 P2) (path : CriticalPath graph)
    {D Q : Subgroup G} (orders : EightSixSmallIndexOrderData graph path D Q)
    (hquot : QuotientIsModel (GAt graph path.a) (QAt graph path.a) SL2Two)
    (hcard : Nat.card (ZAt graph path.a) = 4) :
    Nat.card S ≤ 64 ∧ Nat.card (QAt graph path.firstStep) ≤ 32 ∧
      (Nat.card (QAt graph path.firstStep) = 32 → Nat.card D = 8) := by
  have hScases := orders.sylow_card hyp graph path hquot hcard
  have hdouble := eight_six_twice_next_core_card_le hyp graph path
  have hSbound : Nat.card S ≤ 64 := by rcases hScases with hS | hS <;> omega
  refine ⟨hSbound, by omega, ?_⟩
  intro hnext
  have hDcases : Nat.card D = 4 ∨ Nat.card D = 8 := by
    rcases orders.center_index with hD | hD
    · change Nat.card D = 1 * Nat.card (ZAt graph path.a) at hD
      left
      omega
    · change Nat.card D = 2 * Nat.card (ZAt graph path.a) at hD
      right
      omega
  rcases hDcases with hD | hD
  · have hQ : Nat.card Q = 16 := by
      have hratio := orders.quotient_card
      change Nat.card Q = 4 * Nat.card D at hratio
      omega
    have hle : Q ≤ GAt graph path.a := by
      rw [orders.core_eq]
      change graph.twoCoreAt path.a ≤ graph.vertexStabilizer path.a
      rw [graph.twoCoreAt_def]
      exact Subgroup.map_subtype_le _
    rw [← orders.core_eq] at hquot
    obtain ⟨projection, hsurjective, hkernel⟩ := hquot
    have hlocal := projection.ker.index_mul_card
    rw [Subgroup.index_ker, projection.range_eq_top_of_surjective hsurjective,
      Subgroup.card_top, hkernel,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hQ,
      SectionOne.RankOneThreeGroupAssembly.isSL2Two_card
        (show IsSL2Two SL2Two from ⟨MulEquiv.refl _⟩)] at hlocal
    obtain ⟨_, sylow, hsylow⟩ := (SevenSix.edge_sylow_data hyp graph path).1
    have hindex : Nat.card S = 32 := by
      rw [← hsylow, Subgroup.card_map_of_injective (GAt graph path.a).subtype_injective,
        sylow.card_eq_multiplicity, ← hlocal]
      change 2 ^ (Nat.factorization (3 * 2 ^ 5)) 2 = 32
      rw [Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
      norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
    omega
  · exact hD

public theorem eight_six_central_quotient_core_data_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hlength : ctx.criticalPath.length = 2)
    {D Q : Subgroup G}
    (orders : EightSixSmallIndexOrderData ctx.Γ ctx.criticalPath D Q)
    (hD : D ≤ QAt ctx.Γ ctx.criticalPath.firstStep)
    (helementary : IsElementaryAbelianSubgroup 2 D)
    (hcomm : ⁅VAt ctx.Γ ctx.criticalPath.firstStep,
      QAt ctx.Γ ctx.criticalPath.firstStep⁆ = ZAt ctx.Γ ctx.criticalPath.firstStep) :
    Nat.card S ≤ 64 ∧
      ¬ IsMulCommutative (QAt ctx.Γ ctx.criticalPath.firstStep) ∧
      Nat.card (QAt ctx.Γ ctx.criticalPath.firstStep) ≤ 32 ∧
      (Nat.card (QAt ctx.Γ ctx.criticalPath.firstStep) = 32 →
        ∃ elementary : Subgroup G, elementary ≤ QAt ctx.Γ ctx.criticalPath.firstStep ∧
          IsElementaryAbelianSubgroup 2 elementary ∧ Nat.card elementary = 8) := by
  obtain ⟨hS, hcore, hmax⟩ := eight_six_next_core_bounds ctx.sectionSeven ctx.Γ
    ctx.criticalPath orders hquot hcard
  exact ⟨hS, eight_six_next_core_noncommutative_local ctx hcenter hcard hlength hcomm,
    hcore, fun htop => ⟨D, hD, helementary, hmax htop⟩⟩

end Stellmacher.SectionEight
