module

public import CFSG.Quasithin.MainConverse.SolvableSections
public import Theory.SpecificGroups.PSL3Three.ProperSubgroups
public import Theory.SpecificGroups.LinearCoefficientEquiv

/-!
# Proper simple sections of PSL₃(3)

Every proper subgroup of the concrete PSL₃(3) model is solvable, by the
intrinsic subgroup classification in `Theory.SpecificGroups.PSL3Three`.
Entrywise transport from an arbitrary three-element field identifies the
model supplied by `ClassicalGroup.IsPSL` with that concrete group. Solvability
then passes to subgroups and their quotients, so every simple section is
actually isomorphic to the additive group of a prime field.

Sources: Aschbacher–Smith, Theorem 0.1.2(4) and condition K, printed pp.4
and 482 of `refs/quasithin.pdf`; GLS III, Theorem 6.5.3(a–c), specialized
to PSL₃(3), in `refs/KGroup/GLS3/chapter6.tex`. The intrinsic theorem proves
the needed proper-subgroup classification; it is not an extra hypothesis.
Only inclusion of the constructed carriers in the full catalogue is left
to the main converse assembly.
-/

namespace CFSG.Quasithin.MainConverse

open CFSG.KnownSimple

/-- Proper subgroups of any model satisfying `IsPSL G 3 3` are solvable. -/
public theorem psl3_three_properSubgroup_isSolvable
    {G : Type*} [Group G] (hG : ClassicalGroup.IsPSL G 3 3)
    (U : Subgroup G) (hU : U ≠ ⊤) : Group.IsSolvable U := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hG
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 3 :=
    (ZMod.ringEquivOfPrime F Nat.prime_three
      (by simpa only [Nat.card_eq_fintype_card] using hcard)).symm
  let eG : G ≃* Matrix.PSL3Three.PSL :=
    e.trans (Matrix.ProjectiveSpecialLinearGroup.ringEquiv eF)
  have hproper : U.map eG.toMonoidHom ≠ ⊤ := by
    intro h
    apply hU
    apply Subgroup.map_injective (f := eG.toMonoidHom) eG.injective
    rw [h, Subgroup.map_top_of_surjective _ eG.surjective]
  let : Group.IsSolvable (U.map eG.toMonoidHom) :=
    Matrix.PSL3Three.isSolvable_of_ne_top _ hproper
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.equivMapOfInjective U eG.toMonoidHom eG.injective).toMonoidHom)
    (Subgroup.equivMapOfInjective U eG.toMonoidHom eG.injective).injective

/-- Every simple section of a subgroup of a proper subgroup is prime cyclic.
The target may lie in a different universe from the ambient group. -/
public theorem psl3_three_simpleSection_isPrimeCyclic
    {G : Type*} [Group G] (hG : ClassicalGroup.IsPSL G 3 3)
    (U : Subgroup G) (hU : U ≠ ⊤) (V : Subgroup U)
    {S : Type*} [Group S] [IsSimpleGroup S]
    (f : V →* S) (hf : Function.Surjective f) : IsPrimeCyclicCarrier S := by
  let : Group.IsSolvable U := psl3_three_properSubgroup_isSolvable hG U hU
  let : Group.IsSolvable S := Group.isSolvable_of_surjective (f := f) hf
  exact primeCyclic_of_solvable_simple S

/-- Quotient form of the section theorem: normality is inside `V`. -/
public theorem psl3_three_simpleQuotient_isPrimeCyclic
    {G : Type*} [Group G] (hG : ClassicalGroup.IsPSL G 3 3)
    (U : Subgroup G) (hU : U ≠ ⊤) (V : Subgroup U)
    (N : Subgroup V) [N.Normal] [IsSimpleGroup (V ⧸ N)] :
    IsPrimeCyclicCarrier (V ⧸ N) :=
  psl3_three_simpleSection_isPrimeCyclic hG U hU V
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

/-- The cyclic part of the constructed catalogue contains every proper section. -/
public theorem psl3_three_properK_constructed
    {G : Type*} [Group G] (hG : ClassicalGroup.IsPSL G 3 3) :
    HasProperKSubgroups IsConstructedCarrier G := by
  intro U hU
  let : Group.IsSolvable U := psl3_three_properSubgroup_isSolvable hG U hU
  exact solvable_isKGroup_constructed U

/-- The PSL₃(3) proper-K branch, with only finite simple catalogue inclusion
left to the main converse assembly. -/
public theorem psl3_three_properK_of_catalogue
    {G : Type*} [Group G] [Finite G] {K : GroupClass}
    (hK : ∀ (S : Type _) [Group S] [Finite S] [IsSimpleGroup S],
      IsConstructedCarrier S → K S)
    (hG : ClassicalGroup.IsPSL G 3 3) : HasProperKSubgroups K G := by
  intro U hU S _ hS V f hf
  let := hS
  let : Finite S := Finite.of_surjective f hf
  exact hK S (psl3_three_properK_constructed hG U hU S hS V f hf)

end CFSG.Quasithin.MainConverse
