module
public import Theory.Alternating.TripleSevenLocalRank.CentralSix
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Local cubic rank in genuine triple covers of A₇

Extend the actual six-letter alternating action by fixing the seventh
letter. Pulling this concrete A₆ subgroup back through the specified
central quotient produces a central extension with kernel of order three.
The arbitrary-extension A₆ obstruction gives an actual two-local of
three-rank at least two, and subgroup embedding preserves the lower bound.

This is the A₇ model exclusion used for centered component pairs in
Aschbacher–Smith A.2.12(I.i), printed p.36. The original quotient and
center cardinality are the only covering data supplied as hypotheses.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace GLS3.Chapter5.OddCentralCovers

def sixToSeven : alternatingGroup (Fin 6) →* alternatingGroup (Fin 7) :=
  (((Equiv.Perm.extendDomainHom (Fin.castLEEmb (by decide : 6≤7)).toEquivRange).comp
    (alternatingGroup (Fin 6)).subtype)).codRestrict _ (by
      intro x
      change Equiv.Perm.sign (x.val.extendDomain _) = 1
      rw [Equiv.Perm.sign_extendDomain]
      exact x.prop)

theorem sixToSeven_injective : Function.Injective sixToSeven := by
  intro x y h
  apply Subtype.ext
  exact Equiv.Perm.extendDomainHom_injective
    (Fin.castLEEmb (by decide : 6≤7)).toEquivRange (congrArg Subtype.val h)

theorem triple_seven_twoLocalThreeRank_ge_two {L : Type*} [Group L] [Finite L]
    (e : L ⧸ center L ≃* alternatingGroup (Fin 7))
    (hc : Nat.card (center L) = 3) : 2 ≤ twoLocalPrimeRank 3 L := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center L := by
    ext x
    change e (QuotientGroup.mk' (center L) x) = 1 ↔ x ∈ center L
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  exact twoLocalThreeRank_ge_two_of_embedded_six f hf hk.le (hk ▸ hc)
    sixToSeven sixToSeven_injective

end GLS3.Chapter5.OddCentralCovers
