module

public import Theory.GroupTheory.CComponent.TwoComponent.IndexTwoCover
public import Theory.GroupTheory.SelfCentralizingCore
public import Theory.GroupTheory.PPrimeCoreReduction
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Outer
public import Theory.SpecificGroups.Held.TwoLocalCandidates.Cores.Max5Centralizer

/-!
# B₂ for the implemented Held involutions

The two inner classes and the implemented outer class are covered by the
checked degree-2058 calculations. The 2A and outer rows contain normal
quasisimple subgroups of index two. The 2B fixed subgroup is the literal
max5 subgroup, whose normal two-subgroup is self-centralizing; consequently
its odd core is trivial. Each case therefore has only quasisimple
two-components.

This proves the assertion for every involution induced by the full permutation
normalizer. The final theorem still takes abstract automorphism realization
as an explicit premise; it does not assert that missing realization result.
No simplicity, ambient order or Sylow-fixation premise is used in the local
calculation.

Sources: GLS II, Definition 2.4; GLS3, Table 5.3p and the covering conventions
on printed pp.260–261. In particular the outer row is the genuine `3.A₇.2`.
-/

public section
open Subgroup Theory.GroupTheory

namespace Held.InvolutoryB2
open TwoLocalCandidates InvolutionFixedData

/-- The literal max5 group has trivial odd core, by its self-centralizing two-core. -/
theorem max5_oddCore_eq_bot : pPrimeCore 2 max5 = ⊥ := by
  let := Cores.core_normal 2
  have hle : Cores.core 2 ≤ pCore 2 (subgroup 2) :=
    le_sSup ⟨inferInstance, Cores.core_isPGroup 2⟩
  exact pPrimeCore_eq_bot_of_centralizer_pCore_le 2
    ((Subgroup.centralizer_le hle).trans (Cores.max5_selfCentralizing.trans hle))

/-- Transport uses equality with the actual element centralizer, not its order. -/
theorem twoB_fixed_oddCore_eq_bot :
    pPrimeCore 2 (MulAut.conj (max5First ^ 4)).fixedSubgroup = ⊥ := by
  rw [MulAut.fixedSubgroup_conj, TwoB.centralizer_eq_max5]
  exact max5_oddCore_eq_bot

/-- Both inner involution classes satisfy the literal two-component conclusion. -/
theorem inner_twoComponent_quasisimple (g : He) (hg : orderOf (MulAut.conj g) = 2)
    (L : Subgroup (MulAut.conj g).fixedSubgroup) (hL : L.IsTwoComponent) :
    IsQuasisimple L := by
  have hg' : orderOf g = 2 := (orderOf_conj g).symm.trans hg
  rcases Coverage.innerInvolutionCoverage g hg' with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact (TwoA.hasPSL3FourNormalOfIndexTwo.of_mulEquiv
      (innerFixedEquiv (MulAut.conj c) a)).forget.isQuasisimple_of_isTwoComponent hL
  · have ho := pPrimeCore_eq_bot_of_equiv
      (innerFixedEquiv (MulAut.conj c) (max5First ^ 4)).symm twoB_fixed_oddCore_eq_bot
    exact (hL.isComponent_of_oddCore_eq_bot ho).2

/-- Every involutory action of the full permutation normalizer satisfies B₂. -/
theorem normalizer_twoComponent_quasisimple
    (n : normalizer (permutationGroup : Set (Equiv.Perm (Fin 2058))))
    (hn : orderOf (permutationGroup.normalizerMonoidHom n) = 2)
    (L : Subgroup (permutationGroup.normalizerMonoidHom n).fixedSubgroup)
    (hL : L.IsTwoComponent) : IsQuasisimple L := by
  by_cases hi : ∃ g : He, MulAut.conj g = permutationGroup.normalizerMonoidHom n
  · obtain ⟨g, hg⟩ := hi
    have h := inner_twoComponent_quasisimple g ((congrArg orderOf hg).trans hn)
    rw [hg] at h
    exact h L hL
  · exact (outerRow n hn hi).isQuasisimple_of_isTwoComponent hL

/-- Abstract realization is the sole remaining premise for the full Held B₂ property. -/
theorem hasInvolutoryB2_of_normalizer_surjective
    (hreal : Function.Surjective permutationGroup.normalizerMonoidHom) :
    HasInvolutoryB2 He := by
  intro f hf L hL
  obtain ⟨n, rfl⟩ := hreal f
  exact normalizer_twoComponent_quasisimple n hf L hL

end Held.InvolutoryB2
