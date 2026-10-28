module

public import Theory.GroupTheory.LocalCoreFromPrimeCentralizers
public import Theory.SpecificGroups.PSL3Three.EvenLocals

/-!
# All nontrivial two-local normalizers in PSL3(3)

Every involution centralizer in SL3(3) is GL2(3), with self-centralizing
two-core. The prime-centralizer criterion gives the full normalizer of any
nontrivial two-subgroup, and the canonical SL3(3)-PSL3(3) isomorphism
transports it to the projective model. This is the PSL3(3) local assertion
used in Aschbacher--Smith 2.5.3(4), printed p.553.
-/

namespace Matrix.PSL3Three
open Subgroup

/-- Every nontrivial two-subgroup of SL3(3) has a characteristic-two normalizer. -/
public theorem normalizer_twoCore_selfCentralizing_SL
    (R : Subgroup SL) (hp : IsPGroup 2 R) (hne : R ≠ ⊥) :
    centralizer (pCore 2 (normalizer (R : Set SL)) : Set (normalizer (R : Set SL))) ≤
      pCore 2 (normalizer (R : Set SL)) :=
  normalizer_core_selfCentralizing_of_prime_centralizers
    involutionCentralizer_twoCore_selfCentralizing_SL R hp hne

/-- The same conclusion on the actual projective model. -/
public theorem normalizer_twoCore_selfCentralizing
    (R : Subgroup PSL) (hp : IsPGroup 2 R) (hne : R ≠ ⊥) :
    centralizer (pCore 2 (normalizer (R : Set PSL)) : Set (normalizer (R : Set PSL))) ≤
      pCore 2 (normalizer (R : Set PSL)) := by
  apply normalizer_core_selfCentralizing_of_equiv equiv.symm R
  apply normalizer_twoCore_selfCentralizing_SL _ (hp.map _)
  intro hbot
  exact hne ((map_eq_bot_iff_of_injective _ equiv.symm.injective).mp hbot)

end Matrix.PSL3Three
