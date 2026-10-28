module

public import CFSG.Quasithin.Defs

/-!
# Finite simple guards in the known-group hypothesis

For a finite ambient group, every simple section quantified over by `IsKGroup`
is already finite and simple. Consequently a catalogue predicate can be
restricted to finite simple groups without changing the K-group or proper
K-subgroup hypothesis.

This separates describing the concrete catalogue from certifying every
catalogue entry's intrinsic order and simplicity. It does not supply or alter
the catalogue: the full source-faithful class of known group carriers must
still be constructed independently of quasithinness.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, §0.1,
the definition of K-groups on printed pp. 4 and 482. Finiteness descends along
the surjection from a subgroup; simplicity is part of the section hypothesis.
-/

namespace CFSG.Quasithin

universe u

public theorem isKGroup_finiteSimple_guard_iff
    (K : GroupClass.{u}) (G : Type u) [Group G] [Finite G] :
    IsKGroup (fun (S : Type u) _ => Finite S ∧ IsSimpleGroup S ∧ K S) G ↔
      IsKGroup K G := by
  constructor
  · intro h S _ hs U f hf
    exact (h S hs U f hf).2.2
  · intro h S _ hs U f hf
    exact ⟨Finite.of_surjective f hf, hs, h S hs U f hf⟩

public theorem hasProperKSubgroups_finiteSimple_guard_iff
    (K : GroupClass.{u}) (G : Type u) [Group G] [Finite G] :
    HasProperKSubgroups
      (fun (S : Type u) _ => Finite S ∧ IsSimpleGroup S ∧ K S) G ↔
      HasProperKSubgroups K G := by
  constructor
  · intro h U hU
    exact (isKGroup_finiteSimple_guard_iff K U).mp (h U hU)
  · intro h U hU
    exact (isKGroup_finiteSimple_guard_iff K U).mpr (h U hU)

end CFSG.Quasithin
