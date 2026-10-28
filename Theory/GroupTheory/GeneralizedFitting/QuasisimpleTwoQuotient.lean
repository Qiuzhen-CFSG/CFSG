module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.PGroup.CharacteristicKernel

/-!
# Generalized Fitting subgroup with a quasisimple two-group quotient

If L is normal and quasisimple, G/L is a two-group, and O₂(G) is trivial,
then F*(G) = L. Every component is perfect and hence lies in L. Each odd
prime core has trivial image in the two-group quotient, while the two-core
is trivial by hypothesis. Thus the Fitting subgroup also lies in L.

This is the intrinsic group-theoretic step used in Aschbacher–Smith,
*The Classification of Quasithin Groups*, B.1.11, printed p. 73.
-/

public section

open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A normal quasisimple subgroup with two-group quotient is all of F* when O₂ = 1. -/
theorem generalizedFitting_eq_of_quasisimple_two_quotient
    (L : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hquot : IsPGroup 2 (G ⧸ L)) (hcore : pCore 2 G = ⊥) :
    generalizedFitting G = L := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Group.IsNilpotent (G ⧸ L) := hquot.isNilpotent
  apply le_antisymm
  · apply sup_le
    · rw [fitting_eq_sup_pCore]
      apply iSup_le
      intro p
      by_cases hp : p.val.val = 2
      · rw [hp, hcore]
        exact bot_le
      · let : Fact (Nat.Prime p.val.val) := ⟨(Nat.mem_primeFactors.mp p.val.property).1⟩
        let f := QuotientGroup.mk' L
        have hi : IsPGroup 2 ((pCore p.val.val G).map f) := hquot.to_subgroup _
        have hdis := IsPGroup.disjoint_of_ne p.val.val 2 hp
          ((pCore p.val.val G).map f) ((pCore p.val.val G).map f)
          (pCore_isPGroup.map f) hi
        have hz : (pCore p.val.val G).map f = ⊥ := by simpa using hdis.eq_bot
        simpa only [Subgroup.map_eq_bot_iff, f, QuotientGroup.ker_mk'] using hz
    · apply sSup_le
      intro M hM
      let : IsQuasisimple M := hM.2
      exact le_of_isPerfect_of_solvable_quotient M L
  · exact component_le_generalizedFitting G L
      ⟨(inferInstance : L.Normal).isSubnormal, inferInstance⟩
end Theory.GroupTheory
