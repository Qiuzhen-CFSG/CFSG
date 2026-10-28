module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.Transitivity
public import Theory.GroupAction.AutomorphismNormalizer
public import Theory.GroupTheory.NormalizerOuterQuotient

/-!
# A permutation route to the HS outer restriction

The fixed ATLAS action is transitive. Therefore an automorphism preserving
the family of point stabilizers is induced by a permutation normalizing
the carrier. A two-power index in that normalizer then makes Out(HS) a
two-group.

Both model inputs remain explicit: this module neither proves that all
automorphisms preserve the point-stabilizer family nor computes the
normalizer index. These are the missing model calculations for the outer
entry in GLS3, Table 5.3m, printed p.274, used on Aschbacher–Smith p.510.
-/

public section
namespace Sporadic.LeechRelated.HS
open Subgroup MulAction

/-- The stabilizer of zero in the exact published degree-100 action. -/
abbrev pointStabilizer : Subgroup Carrier := stabilizer Carrier (0 : Fin 100)

/-- Stabilizer preservation covers the actual full automorphism group. -/
theorem normalizer_surjective_of_pointStabilizer_map
    (h : ∀ α : MulAut Carrier, ∃ y : Fin 100,
      pointStabilizer.map α.toMonoidHom = stabilizer Carrier y) :
    Function.Surjective generated.normalizerMonoidHom := by
  intro α
  obtain ⟨y, hy⟩ := h α
  exact generated.exists_normalizer_of_stabilizer_map_eq α (0 : Fin 100) y hy

/-- The two independent permutation-model calculations imply the outer restriction. -/
theorem outer_isPGroup_two_of_pointStabilizer_map
    (h : ∀ α : MulAut Carrier, ∃ y : Fin 100,
      pointStabilizer.map α.toMonoidHom = stabilizer Carrier y)
    (hi : ∃ n : ℕ,
      generated.relIndex (normalizer (generated : Set (Equiv.Perm (Fin 100)))) ∣ 2 ^ n) :
    IsPGroup 2 (MulAut.Outer Carrier) := by
  obtain ⟨n, hn⟩ := hi
  exact generated.outer_isPGroup_of_normalizer_relIndex
    (normalizer_surjective_of_pointStabilizer_map h) hn

end Sporadic.LeechRelated.HS
