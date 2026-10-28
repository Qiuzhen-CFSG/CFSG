module
public import Stellmacher.SectionNine.NineThreeSecondCenterRelations
public import Theory.GroupTheory.IndexTwoIntersectionLine

/-!
# The two outer center indices in (9.3)(4)

In the two actual geometric extractions, each new center has index two over
its intersection with the other new vertex stabilizer. The first geometric
coatom has index two in the first actor module, and the second coatom has
index two in the terminal actor module. Each relevant center lies in that
actor module and escapes the opposite stabilizer.

Restrict an index-two subgroup to a subgroup not contained in it. Its
relative index remains two; the finite index-cardinality identity converts
this to the stated exact cardinality equalities. The second center's escape
comes from the proved repeated center-intersection argument. The first
center's escape follows directly from the prescribed second actor.

Source: Stellmacher (9.3)(4), Journal of Algebra 190 (1997), p.49,
`refs/files/stellmacher-n-group.pdf`. The two vertices are still the actual
extracted neighbors before their simultaneous edge normalization.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem card_intersection_of_index_two
    {G : Type u} [Group G] [Finite G] (V K Z : Subgroup G)
    (hZV : Z ≤ V) (hVcard : Nat.card V = 2 * Nat.card (V ⊓ K : Subgroup G))
    (hnot : ¬ Z ≤ K) : Nat.card Z = 2 * Nat.card (Z ⊓ K : Subgroup G) := by
  have hcard := ((V ⊓ K).subgroupOf V).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show V ⊓ K ≤ V from inf_le_left)).toEquiv] at hcard
  change (V ⊓ K).relIndex V * Nat.card (V ⊓ K : Subgroup G) = Nat.card V at hcard
  have hi : K.relIndex V = 2 := by
    rw [Subgroup.inf_relIndex_left] at hcard
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hcard.trans hVcard)
  have hni : ¬ Z.subgroupOf V ≤ K.subgroupOf V := by
    intro hle
    exact hnot fun z hz => hle (show (⟨z,hZV hz⟩ : V) ∈ Z.subgroupOf V from hz)
  have hZindex := Subgroup.subgroupOf_index_eq_two (K.subgroupOf V) (Z.subgroupOf V) hi hni
  change (K.subgroupOf V).relIndex (Z.subgroupOf V) = 2 at hZindex
  rw [Subgroup.relIndex_subgroupOf hZV] at hZindex
  have hZcard := ((Z ⊓ K).subgroupOf Z).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show Z ⊓ K ≤ Z from inf_le_left)).toEquiv] at hZcard
  change (Z ⊓ K).relIndex Z * Nat.card (Z ⊓ K : Subgroup G) = Nat.card Z at hZcard
  rw [Subgroup.inf_relIndex_left,hZindex] at hZcard
  exact hZcard.symm

public theorem nine_three_mutual_outer_indices
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first) :
    let m := ctx.Γ.act first.extraction.x⁻¹ first.l
    let n := ctx.Γ.act second.extraction.x⁻¹ second.l
    Nat.card (ZAt ctx.Γ n) = 2 * Nat.card (ZAt ctx.Γ n ⊓ GAt ctx.Γ m : Subgroup G) ∧
      Nat.card (ZAt ctx.Γ m) = 2 * Nat.card (ZAt ctx.Γ m ⊓ GAt ctx.Γ n : Subgroup G) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let m := Γ.act first.extraction.x⁻¹ first.l
  let n := Γ.act second.extraction.x⁻¹ second.l
  have hZnV : ZAt Γ n ≤ VAt Γ cp.firstStep := by
    change z Γ n ≤ v Γ cp.firstStep
    rw [v,Γ.vAt_def]
    exact le_sSup ⟨n,second.extraction.neighbor,rfl⟩
  have hZmV : ZAt Γ m ≤ VAt Γ cp.a' := by
    change z Γ m ≤ v Γ cp.a'
    rw [v,Γ.vAt_def]
    exact le_sSup ⟨m,first.extraction.neighbor,rfl⟩
  have hVfirst : Nat.card (VAt Γ cp.firstStep) =
      2 * Nat.card (VAt Γ cp.firstStep ⊓ GAt Γ m : Subgroup G) := by
    rw [← first.extraction.coatom_eq]
    exact first.extraction.coatom_card
  have hVend : Nat.card (VAt Γ cp.a') =
      2 * Nat.card (VAt Γ cp.a' ⊓ GAt Γ n : Subgroup G) := by
    rw [← second.extraction.coatom_eq]
    exact second.extraction.coatom_card
  have hnnot : ¬ ZAt Γ n ≤ GAt Γ m :=
    (nine_three_second_center_relations ctx hb hlarge first second).2.2
  have hmnot : ¬ ZAt Γ m ≤ GAt Γ n := fun hle =>
    second.extraction.actor_outside (hle second.actor_first_center)
  exact ⟨card_intersection_of_index_two _ _ _ hZnV hVfirst hnnot,
    card_intersection_of_index_two _ _ _ hZmV hVend hmnot⟩

end Stellmacher.SectionNine
