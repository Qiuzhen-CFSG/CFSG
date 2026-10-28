module

public import Stellmacher.SectionEight.GeneratedEightSixEquationOneSetup
public import Theory.GroupTheory.CenterFreeOddImageCore
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# Initial-center generation by the residual in (8.6)

The central first-step hypothesis makes the initial stabilizer center-free.
Its two-residual supplements the edge Sylow subgroup, so its centralizer
in the normal four-element initial center is trivial. The residual
commutator is therefore nontrivial. It is normal in the initial stabilizer,
and cannot have order two, since a normal order-two subgroup is central.
Consequently the commutator is the entire initial center.

This is the initial-center lower bound used in (8.6)(1), printed p.41 of
`refs/files/stellmacher-n-group.pdf`. Neither quotient recognition nor a
critical-length hypothesis is needed. The local context keeps Hypothesis
Two on the ambient group when applied through the generated adapter.
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

private theorem four_commutator_eq_of_centerfree_supplement
    {G : Type*} [Group G] [Finite G] (sylow : Sylow 2 G)
    (residual center : Subgroup G) [residual.Normal] [center.Normal]
    (hcover : residual ⊔ (sylow : Subgroup G) = ⊤)
    (hcenter : Subgroup.center G = ⊥) (hcard : Nat.card center = 4) :
    ⁅center, residual⁆ = center := by
  have htwo : IsPGroup 2 center := IsPGroup.of_card (n := 2) hcard
  have hfixed := Subgroup.inf_centralizer_eq_bot_of_centerfree_sylow_supplement
    sylow residual center hcover htwo hcenter
  have hne : ⁅center, residual⁆ ≠ ⊥ := by
    intro hbot
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    rw [inf_eq_left.mpr hle] at hfixed
    simp [hfixed] at hcard
  have hle : ⁅center, residual⁆ ≤ center := Subgroup.commutator_le_left _ _
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hcard] at hdvd
  have hcases : Nat.card (⁅center, residual⁆ : Subgroup G) = 1 ∨
      Nat.card (⁅center, residual⁆ : Subgroup G) = 2 ∨
      Nat.card (⁅center, residual⁆ : Subgroup G) = 4 := by
    have hbound := Nat.le_of_dvd (by decide : 0 < 4) hdvd
    interval_cases horder : Nat.card (⁅center, residual⁆ : Subgroup G) <;>
      norm_num at *
  rcases hcases with hone | htwo | hfour
  · exact (hne ((Subgroup.eq_bot_iff_card _).mpr hone)).elim
  · have hcentral := Subgroup.central_of_normal_card_two ⁅center, residual⁆ htwo
    rw [hcenter] at hcentral
    exact (hne (le_bot_iff.mp hcentral)).elim
  · exact Subgroup.eq_of_le_of_card_ge hle (by omega)

/-- The initial two-residual generates the four-element initial center
through its commutator action, under the central first-step hypothesis. -/
public theorem eight_six_initial_center_residual_local
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4) :
    ⁅ZAt ctx.Γ ctx.criticalPath.a, EAt ctx.Γ ctx.criticalPath.a⁆ =
      ZAt ctx.Γ ctx.criticalPath.a := by
  let graph := ctx.Γ
  let path := ctx.criticalPath
  let initial := GAt graph path.a
  let center := ZAt graph path.a
  let residual := EAt graph path.a
  have hfirst : path.firstStep ∈ neighborhood graph path.a :=
    (SevenSix.mem_neighborhood_iff_adjacent graph).mpr path.firstStep_adj
  have hcenterLe : center ≤ initial :=
    ((lemma_seven_three ctx.sectionSeven graph).center_core path.a path.firstStep
      hfirst).trans ((Subgroup.map_subtype_le _).trans (by
        change graph.twoCoreAt path.a ≤ initial
        rw [graph.twoCoreAt_def]
        exact Subgroup.map_subtype_le _))
  have hresidualEq : residual = twoResidualIn initial := by
    change graph.twoResidualAt path.a = _
    rw [graph.twoResidualAt_def]
    rfl
  have hresidualLe : residual ≤ initial :=
    hresidualEq ▸ SevenSix.twoResidualIn_le initial
  let centerNative := center.subgroupOf initial
  let residualNative := residual.subgroupOf initial
  let : centerNative.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcenterLe).mpr
      (stabilizer_le_normalizer_z graph path.a)
  let : residualNative.Normal := by
    change (residual.subgroupOf initial).Normal
    rw [hresidualEq]
    exact SevenSix.twoResidualIn_normal initial
  obtain ⟨hS, sylow, hsylow⟩ :=
    (SevenSix.edge_sylow_data ctx.sectionSeven graph path).1
  have hcover : residualNative ⊔ (sylow : Subgroup initial) = ⊤ := by
    apply Subgroup.map_injective initial.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hresidualLe, hsylow,
      hresidualEq, SevenSix.twoResidualIn_sup_sylow ⟨hS, sylow, hsylow⟩,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have htrivial : Subgroup.center initial = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective _ initial.subtype_injective).mp
    exact eight_six_initial_center_trivial_local ctx hcenter
  have hcardNative : Nat.card centerNative = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcenterLe).toEquiv).trans hcard
  have heq := four_commutator_eq_of_centerfree_supplement sylow residualNative
    centerNative hcover htrivial hcardNative
  have hmapped := congrArg (fun subgroup : Subgroup initial =>
    subgroup.map initial.subtype) heq
  simpa only [centerNative, residualNative, Subgroup.map_commutator,
    Subgroup.map_subgroupOf_eq_of_le hcenterLe,
    Subgroup.map_subgroupOf_eq_of_le hresidualLe] using hmapped

end Stellmacher.SectionEight
