module
public import Theory.Representation.BinaryOffender.SimpleNormalActor

/-!
# Actors on sections moved by their commutator-generated factors

If K = [K,A], an invariant section moved by K is also moved by A:
otherwise its normal action kernel contains [K,A] = K. Thus a binary
actor of rank at most two loses at most one rank on any such section.
No simplicity or faithful conjugation hypothesis is needed here.

Source: Aschbacher--Smith 13.1.9, printed pp.870--871. The odd-prime
line consumer supplies commutator generation and the actual actor bound.
-/

public noncomputable section
open Subgroup
namespace Representation.BinaryOffender.RepeatedSectionBudget
variable {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) Q V} {K A : Subgroup Q}

/-- A section moved by an actor-generated factor is moved by the actor itself. -/
theorem MovedSection.actor_ne_bot_of_generated
    (d : MovedSection ρ K A) (hgen : ⁅K,A⁆ = K) :
    actor ρ d.overgroup A d.lower d.upper ≠ ⊥ := by
  let E := d.overgroup
  let σ := sectionRepresentation (ρ.comp E.subtype) d.lower d.upper
  have hgenE : ⁅K.subgroupOf E,A.subgroupOf E⁆ = K.subgroupOf E := by
    apply Subgroup.map_injective E.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le d.factor_le,
      map_subgroupOf_eq_of_le d.actor_le,hgen]
  intro hz
  have hAk : A.subgroupOf E ≤ σ.ker := by
    intro a ha
    have he : actionHom σ a = 1 := mem_bot.mp (hz ▸ mem_map_of_mem (actionHom σ) ha)
    exact LinearMap.ext ((actionHom_eq_one_iff σ a).mp he)
  apply d.moves
  rw [←hgenE]
  exact (commutator_mono le_rfl hAk).trans (commutator_le_right _ σ.ker)

/-- Rank at most two loses at most one dimension on a moved section. -/
theorem MovedSection.rankLoss_le_one_of_generated [Finite Q]
    (d : MovedSection ρ K A) (hgen : ⁅K,A⁆ = K)
    (hA : IsElementaryTwo A) (hr : rank A ≤ 2) : d.rankLoss ≤ 1 :=
  epsilon_le_one d.actor_le hA d.lower d.upper (d.actor_ne_bot_of_generated hgen) hr
end Representation.BinaryOffender.RepeatedSectionBudget
