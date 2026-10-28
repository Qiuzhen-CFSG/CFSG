module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.CandidateQuotient
public import Theory.GroupTheory.PrimeRankWitness
public import Theory.Quasithin.Rank

/-!
# An elementary nine in the Hall–Janko group

The certified local candidate has a quotient S₃ × C₃ by its explicit radical
of order 64. The product of a three-cycle and the second factor has rank two.
Schur–Zassenhaus lifts its odd rank through the radical. Only the candidate
subgroup and its quotient are needed; no full-normalizer coverage is used.

Source application: Aschbacher–Smith, 16.3.10, combined manuscript of
1 March 2004, printed p.1181.
-/

namespace Sporadic.LeechRelated.J2
open Subgroup Theory.GroupTheory
open ExceptionalParabolics ExceptionalParabolics.PairNormalizer

private abbrev E := Multiplicative (ZMod 3 × ZMod 3)

private def planeAction : E →* (Equiv.Perm (ZMod 3) × Multiplicative (ZMod 3)) where
  toFun a := (Equiv.addLeft a.toAdd.1, Multiplicative.ofAdd a.toAdd.2)
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp

private theorem planeAction_injective : Function.Injective planeAction := by
  intro a b h
  have hi := congrArg (fun x : Equiv.Perm (ZMod 3) × Multiplicative (ZMod 3) => x.1 0) h
  have hj := congrArg (fun x : Equiv.Perm (ZMod 3) × Multiplicative (ZMod 3) => x.2.toAdd) h
  apply (Multiplicative.toAdd : E ≃ _).injective
  exact Prod.ext (by simpa [planeAction] using hi) hj

private theorem plane_cube (a : E) : a ^ 3 = 1 := by
  change Multiplicative.ofAdd (3 • a.toAdd) = Multiplicative.ofAdd 0
  exact congrArg Multiplicative.ofAdd (Prod.ext
    (ZModModule.char_nsmul_eq_zero 3 a.toAdd.1)
    (ZModModule.char_nsmul_eq_zero 3 a.toAdd.2))

private theorem quotient_three_rank_ge_two : 2 ≤ primeRank 3 QuotientModel := by
  let e : ZMod 3 ≃ Fin 3 := (ZMod.finEquiv 3).symm.toEquiv
  let f := ((Equiv.permCongrHom e).prodCongr (MulEquiv.refl (Multiplicative (ZMod 3)))).toMonoidHom
  exact primeRank_ge_of_elementary_embedding plane_cube
    (by simp [E, Nat.card_eq_fintype_card]) (f.comp planeAction)
    (((Equiv.permCongrHom e).prodCongr (MulEquiv.refl (Multiplicative (ZMod 3)))).injective.comp
      planeAction_injective)

/-- Odd rank lifts from the concrete S₃ × C₃ local quotient to the J₂ carrier. -/
public theorem three_rank_ge_two : 2 ≤ primeRank 3 Carrier := by
  obtain ⟨e⟩ := candidate_quotient_equiv
  have hq : IsPGroup 2 (Seed.q₂.subgroupOf candidate) :=
    q₂_isPGroup.of_equiv (subgroupOfEquivOfLe q₂_le_candidate).symm
  have hr : 2 ≤ primeRank 3 (candidate ⧸ Seed.q₂.subgroupOf candidate) := by
    rw [primeRank_congr 3 e]
    exact quotient_three_rank_ge_two
  exact hr.trans ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ hq).trans
    (primeRank_le_of_injective 3 candidate.subtype Subtype.val_injective))

end Sporadic.LeechRelated.J2
