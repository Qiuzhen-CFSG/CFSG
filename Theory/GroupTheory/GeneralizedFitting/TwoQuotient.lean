module

public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient

/-!
# Generalized Fitting subgroups across a two-group quotient

Let L be normal, contained in F*(G), with G/L a two-group. If O₂(G)=1,
then F*(G)=L: all odd prime cores have trivial image in the quotient,
and every component is perfect and hence lies in L. This extends the
quasisimple version to the semisimple and odd-prime actors in D.3.4(5).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma D.3.4(5), printed p.194.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
theorem generalizedFitting_eq_of_le_two_quotient
    (L : Subgroup G) [L.Normal] (hLF : L ≤ generalizedFitting G)
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
  · exact hLF

end Theory.GroupTheory
