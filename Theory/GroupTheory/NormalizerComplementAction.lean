module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# A marked cyclic complement in a subgroup normalizer

This record specifies an internal cyclic complement and its literal
conjugation action. It asserts no existence. It is the model interface
for the PGL₂(9) calculation used in Aschbacher, *Sporadic Groups* (1994),
47.3(3), p.262. Its faithful, transitive action is on the subgroup itself;
a covering-group consumer must separately identify its Frattini quotient.
-/

@[expose] public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- A cyclic complement in the full normalizer, with its actual action. -/
structure NormalizerComplementAction (U : Subgroup G) (n : ℕ) where
  complement : Subgroup (normalizer (U : Set G))
  cyclic : IsCyclic complement
  card : Nat.card complement = n
  split : (U.subgroupOf (normalizer (U : Set G))).IsComplement' complement
  faithful : Function.Injective (U.normalizerMonoidHom.comp complement.subtype)
  transitive : ∀ u v : U, u ≠ 1 → v ≠ 1 →
    ∃ b : complement, U.normalizerMonoidHom b u = v

end Subgroup
