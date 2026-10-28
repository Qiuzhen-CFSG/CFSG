module

public import Stellmacher.SectionNine.NineThreeFinalCoreFrattiniAction

/-!
# Small displacement on the actual mixed core section in (9.3)

Conjugation displacements on a quotient of a normal core lie in the
projected core/vector intersection. A contained subgroup killed by the
projection embeds in its restricted kernel. The kernel-image cardinality
formula therefore bounds the product of the killed subgroup order and the
displacement order by the original intersection order. In particular, an
intersection of order eight and a killed line of order two give displacement
order at most four; the bound also applies to the final order-four case.

This preliminary estimate neither asserts transvection displacement of
order two nor proves the final odd-layer containment. It applies to the
literal Frattini/mixed-line quotient action constructed in the imported
module, without replacing the original ambient group or action.

Source: Stellmacher (9.3), printed p.50/PDF p.40, the final R₀,C₀ paragraph
of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine

open scoped commutatorElement

universe u

public theorem core_quotient_displacement_card_mul_le_intersection
    {C : Type u} [Group C] [Finite C]
    (core vectors line : Subgroup C) [core.Normal] [line.Normal]
    (layer : Subgroup core) [layer.Normal]
    (hline : line ≤ vectors ⊓ core)
    (hlayer : line.subgroupOf core ≤ layer)
    (hcommutator : ⁅core, vectors⁆ ≤ vectors ⊓ core)
    (action : C →* MulAut (core ⧸ layer))
    (hformula : ∀ actor : C, ∀ vector : core,
      action actor (QuotientGroup.mk' layer vector) =
        QuotientGroup.mk' layer (MulAut.conjNormal actor vector)) :
    Nat.card line * Nat.card (commutatorAction (vectors.map action) (core ⧸ layer)) ≤
      Nat.card (vectors ⊓ core : Subgroup C) := by
  let intersection := (vectors ⊓ core).subgroupOf core
  let projection := QuotientGroup.mk' layer
  have htransport : commutatorAction (vectors.map action) (core ⧸ layer) ≤
      intersection.map projection := by
    rw [commutatorAction_eq_closure, Subgroup.closure_le]
    rintro _ ⟨actor, vector, rfl⟩
    obtain ⟨representative, hrepresentative, heq⟩ := actor.property
    obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective layer vector
    change (projection lift)⁻¹ *
      (actor : MulAut (core ⧸ layer)) (projection lift) ∈ _
    rw [← heq, hformula, ← map_inv, ← map_mul]
    apply Subgroup.mem_map_of_mem
    apply hcommutator
    change (lift : C)⁻¹ * (representative * (lift : C) * representative⁻¹) ∈ _
    simpa only [commutatorElement_def, inv_inv, mul_assoc] using
      Subgroup.commutator_mem_commutator (core.inv_mem lift.property) hrepresentative
  have hsection : Nat.card intersection = Nat.card (vectors ⊓ core : Subgroup C) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show vectors ⊓ core ≤ core from inf_le_right)).toEquiv]
  have hkernel : Nat.card line ≤ Nat.card (layer.subgroupOf intersection) := by
    apply Nat.card_le_card_of_injective
      (fun vector : line =>
        (⟨⟨⟨vector.val, (hline vector.property).2⟩, hline vector.property⟩,
          hlayer vector.property⟩ : layer.subgroupOf intersection))
    intro first second heq
    exact Subtype.ext (congrArg (fun vector : layer.subgroupOf intersection =>
      ((vector.val : intersection).val : C)) heq)
  have hindex : layer.relIndex intersection = Nat.card (intersection.map projection) := by
    simpa only [projection, QuotientGroup.ker_mk'] using intersection.relIndex_ker projection
  have hcount := (layer.subgroupOf intersection).card_mul_index
  change Nat.card (layer.subgroupOf intersection) * layer.relIndex intersection =
    Nat.card intersection at hcount
  rw [hindex, hsection] at hcount
  exact (Nat.mul_le_mul hkernel (Subgroup.card_le_of_le htransport)).trans_eq hcount

public theorem core_quotient_displacement_card_le_four
    {C : Type u} [Group C] [Finite C]
    (core vectors line : Subgroup C) [core.Normal] [line.Normal]
    (layer : Subgroup core) [layer.Normal]
    (hline : line ≤ vectors ⊓ core)
    (hlineCard : Nat.card line = 2)
    (hintersection : Nat.card (vectors ⊓ core : Subgroup C) = 8)
    (hlayer : line.subgroupOf core ≤ layer)
    (hcommutator : ⁅core, vectors⁆ ≤ vectors ⊓ core)
    (action : C →* MulAut (core ⧸ layer))
    (hformula : ∀ actor : C, ∀ vector : core,
      action actor (QuotientGroup.mk' layer vector) =
        QuotientGroup.mk' layer (MulAut.conjNormal actor vector)) :
    Nat.card (commutatorAction (vectors.map action) (core ⧸ layer)) ≤ 4 := by
  have hbound := core_quotient_displacement_card_mul_le_intersection
    core vectors line layer hline hlayer hcommutator action hformula
  rw [hlineCard, hintersection] at hbound
  omega

end Stellmacher.SectionNine
