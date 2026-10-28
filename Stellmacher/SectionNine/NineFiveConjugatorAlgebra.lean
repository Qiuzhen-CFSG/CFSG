module

public import Stellmacher.SectionNine.NineFiveTransvectionInputs
public import Stellmacher.SectionNine.NineNextCenterCommutator

/-!
# Conjugator extraction algebra for (9.5)

An index-two subgroup and any element outside it generate the entire upper
subgroup. Applying this to an element commutator yields the precise
inverse-conjugation bound required in (9.5), provided that the residual-core
commutator lies in the penultimate center but not in the terminal center.

The center layer is transported from the initial edge using the order-four
initial center. Neither the ambient core-action assertions nor the order-four
initial center are asserted here without their required proofs.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement

universe u

public theorem nine_five_index_two_span_of_element
    {G : Type u} [Group G] [Finite G]
    (line plane container : Subgroup G)
    (hline : line ≤ plane)
    (hindex : QuotientCardEq plane line 2)
    (hcontainer : line ≤ container)
    (vector : G) (hvector : vector ∈ plane)
    (houtside : vector ∉ line) (hinside : vector ∈ container) :
    plane ≤ container := by
  let middle := plane ⊓ container
  have hsmall : line ≤ middle := le_inf hline hcontainer
  have hstrict : Nat.card line < Nat.card middle := by
    apply lt_of_le_of_ne (Subgroup.card_le_of_le hsmall)
    intro hequal
    have heq := Subgroup.eq_of_le_of_card_ge hsmall hequal.ge
    exact houtside (heq ▸ (show vector ∈ middle from ⟨hvector, hinside⟩))
  obtain ⟨factor, hfactor⟩ := Subgroup.card_dvd_of_le
    (show middle ≤ plane from inf_le_left)
  have hpositive : 0 < Nat.card plane := Nat.card_pos
  change Nat.card plane = 2 * Nat.card line at hindex
  have hfactor_one : factor = 1 := by
    by_contra hnot
    have hfactor_two : 2 ≤ factor := by
      by_cases hzero : factor = 0
      · simp [hzero] at hfactor
        omega
      · omega
    nlinarith
  have hequal : middle = plane := by
    apply Subgroup.eq_of_le_of_card_ge inf_le_left
    change Nat.card plane ≤ Nat.card middle
    simpa [hfactor_one] using hfactor.le
  exact hequal ▸ (show middle ≤ container from inf_le_right)

public theorem nine_five_conjugator_of_core_commutator
    {G : Type u} [Group G] [Finite G]
    (core residual line plane : Subgroup G)
    (hline : line ≤ plane)
    (hindex : QuotientCardEq plane line 2)
    (hbound : ⁅core, residual⁆ ≤ plane)
    (hescape : ¬ ⁅core, residual⁆ ≤ line) :
    ∃ conjugator : G, conjugator ∈ core ∧
      plane ≤ (line ⊔ residual) ⊔
        residual.map (MulAut.conj conjugator⁻¹).toMonoidHom := by
  rw [Subgroup.commutator_le] at hescape
  push Not at hescape
  obtain ⟨mover, hmover, vector, hvector, houtside⟩ := hescape
  refine ⟨mover⁻¹, core.inv_mem hmover, ?_⟩
  apply nine_five_index_two_span_of_element line plane _ hline hindex
    (le_sup_left.trans le_sup_left) ⁅mover, vector⁆
    (hbound (Subgroup.commutator_mem_commutator hmover hvector)) houtside
  have hconjugate : mover * vector * mover⁻¹ ∈
      residual.map (MulAut.conj (mover⁻¹)⁻¹).toMonoidHom := by
    refine ⟨vector, hvector, ?_⟩
    simp
  change mover * vector * mover⁻¹ * vector⁻¹ ∈ _
  exact Subgroup.mul_mem _
    ((show residual.map (MulAut.conj (mover⁻¹)⁻¹).toMonoidHom ≤
      (line ⊔ residual) ⊔ residual.map (MulAut.conj (mover⁻¹)⁻¹).toMonoidHom
      from le_sup_right) hconjugate)
    ((show residual ≤ (line ⊔ residual) ⊔
      residual.map (MulAut.conj (mover⁻¹)⁻¹).toMonoidHom
      from le_sup_right.trans le_sup_left) (residual.inv_mem hvector))

public theorem nine_five_penultimate_center_layer_of_initial_four
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4) :
    let penultimate := ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    ZAt ctx.Γ ctx.criticalPath.a' ≤ ZAt ctx.Γ penultimate ∧
      QuotientCardEq (ZAt ctx.Γ penultimate) (ZAt ctx.Γ ctx.criticalPath.a') 2 := by
  have hinitial : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      ZAt ctx.Γ ctx.criticalPath.a := by
    change z ctx.Γ ctx.criticalPath.firstStep ≤ z ctx.Γ ctx.criticalPath.a
    rw [(lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath
      ctx.commutator_eq).next_center.1]
    obtain ⟨_, sylow, hsylow⟩ :=
      (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1
    rw [z, ctx.Γ.zAt_def]
    exact le_sSup ⟨sylow, congrArg omegaOneCenter hsylow.symm⟩
  obtain ⟨mover, hpenultimate, hterminal⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have htwo := nine_next_center_order_of_initial_four ctx hfour
  dsimp only
  rw [← hpenultimate, ← hterminal]
  change z ctx.Γ (ctx.Γ.act mover ctx.criticalPath.firstStep) ≤
    z ctx.Γ (ctx.Γ.act mover ctx.criticalPath.a) ∧ _
  rw [z_act, z_act]
  refine ⟨Subgroup.map_mono hinitial, ?_⟩
  change Nat.card (z ctx.Γ (ctx.Γ.act mover ctx.criticalPath.a)) =
    2 * Nat.card (z ctx.Γ (ctx.Γ.act mover ctx.criticalPath.firstStep))
  rw [z_act, z_act,
    Subgroup.card_map_of_injective (MulAut.conj mover⁻¹).injective,
    Subgroup.card_map_of_injective (MulAut.conj mover⁻¹).injective]
  change Nat.card (ZAt ctx.Γ ctx.criticalPath.a) =
    2 * Nat.card (ZAt ctx.Γ ctx.criticalPath.firstStep)
  rw [hfour, htwo]

public theorem nine_five_penultimate_conjugator_of_core_action
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (actor : G)
    (hfour : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (hbound : ⁅twoCoreIn (EAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)),
      ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆⁆ ≤
      ZAt ctx.Γ (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩))
    (hescape : ¬ ⁅twoCoreIn (EAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)),
      ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.a') :
    let penultimate := ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
      Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    let residual := ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆
    ∃ conjugator : G, conjugator ∈ twoCoreIn (EAt ctx.Γ penultimate) ∧
      ZAt ctx.Γ penultimate ≤ (ZAt ctx.Γ ctx.criticalPath.a' ⊔ residual) ⊔
        residual.map (MulAut.conj conjugator⁻¹).toMonoidHom := by
  obtain ⟨hline, hindex⟩ :=
    nine_five_penultimate_center_layer_of_initial_four ctx.toLocalContext hfour
  exact nine_five_conjugator_of_core_commutator _ _ _ _ hline hindex hbound hescape

end Stellmacher.SectionNine
