module
public import Theory.Representation.BinaryOffender.RepeatedSectionBudget
public import Theory.GroupTheory.FaithfulNormalRestriction
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Faithful actors on sections moved by a simple normal subgroup

A nontrivial homomorphism on a simple normal subgroup is injective there.
Its kernel centralizes that subgroup, so any actor with faithful conjugation
acts faithfully on the section. For a binary invariant section, this makes
the rank lost by the actor exactly zero.

Source: Aschbacher--Smith 13.1.9, printed p.870. The literal candidate
application is FFContradiction.SimpleSection in Chapter 13.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]

/-- A nontrivial section action of a simple normal subgroup detects any actor
whose conjugation action on that subgroup is faithful. -/
theorem simple_normal_inclusion_actor_faithful (K E A : Subgroup Q)
    [K.Normal] [IsSimpleGroup K] (hKE : K ≤ E)
    (σ : Representation (ZMod 2) E V)
    (hm : ¬ K.subgroupOf E ≤ σ.ker)
    (hc : A ⊓ centralizer (K : Set Q) = ⊥) :
    ∀ a ∈ A.subgroupOf E, (∀ v, σ a v = v) → a = 1 := by
  have hf : Function.Injective (σ.comp (inclusion hKE)) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rcases (σ.comp (inclusion hKE)).normal_ker.eq_bot_or_eq_top with hz | ht
    · exact hz
    · exfalso
      apply hm
      intro k hk
      exact (show (⟨k.val,hk⟩ : K) ∈ (σ.comp (inclusion hKE)).ker from
        ht.symm ▸ mem_top _)
  have hf' : Function.Injective (σ.comp (K.subgroupOf E).subtype) :=
    hf.comp (subgroupOfEquivOfLe hKE).injective
  have hk := σ.ker_le_centralizer_of_injective_normal_restriction (K.subgroupOf E) hf'
  intro a ha hfix
  have hac : (a : Q) ∈ centralizer (K : Set Q) := by
    have haC := hk (show a ∈ σ.ker from LinearMap.ext hfix)
    intro k hkK
    exact congrArg Subtype.val (haC ⟨k,hKE hkK⟩ hkK)
  apply Subtype.ext
  exact mem_bot.mp (hc ▸ (show (a : Q) ∈ A ⊓ centralizer (K : Set Q) from ⟨ha,hac⟩))

namespace RepeatedSectionBudget
variable {ρ : Representation (ZMod 2) Q V} {E A : Subgroup Q}

/-- No rank is lost on a section moved by the simple normal factor. -/
theorem epsilon_eq_zero_of_simple (hAE : A ≤ E) (K : Subgroup Q)
    [K.Normal] [IsSimpleGroup K] (hKE : K ≤ E)
    (U W : Subrepresentation (ρ.comp E.subtype))
    (hm : ¬ K.subgroupOf E ≤ (sectionRepresentation (ρ.comp E.subtype) U W).ker)
    (hc : A ⊓ centralizer (K : Set Q) = ⊥) : epsilon ρ E A U W = 0 :=
  epsilon_eq_zero hAE U W
    (simple_normal_inclusion_actor_faithful K E A hKE _ hm hc)

/-- A literal invariant section moved by a specified factor. The source
assembly must construct the section and its movement. -/
structure MovedSection (ρ : Representation (ZMod 2) Q V) (K A : Subgroup Q) where
  overgroup : Subgroup Q
  factor_le : K ≤ overgroup
  actor_le : A ≤ overgroup
  lower : Subrepresentation (ρ.comp overgroup.subtype)
  upper : Subrepresentation (ρ.comp overgroup.subtype)
  lower_le_upper : lower ≤ upper
  moves : ¬ K.subgroupOf overgroup ≤
    (sectionRepresentation (ρ.comp overgroup.subtype) lower upper).ker

/-- The rank loss on the recorded section, using its original quotient action. -/
@[expose] noncomputable def MovedSection.rankLoss {K : Subgroup Q}
    (d : MovedSection ρ K A) : ℕ := epsilon ρ d.overgroup A d.lower d.upper

/-- Section movement and conjugation faithfulness eliminate the kernel. -/
theorem MovedSection.rankLoss_eq_zero {K : Subgroup Q} [K.Normal] [IsSimpleGroup K]
    (d : MovedSection ρ K A) (hc : A ⊓ centralizer (K : Set Q) = ⊥) :
    d.rankLoss = 0 :=
  epsilon_eq_zero_of_simple d.actor_le K d.factor_le d.lower d.upper d.moves hc
end RepeatedSectionBudget
end Representation.BinaryOffender
