module

public import CFSG.Quasithin.MainConverse.AlternatingSections.SymmetricEight.PrimitiveSeven.Order168Recognition.Involutions
public import CFSG.Quasithin.MainConverse.AlternatingSections.SymmetricEight.PrimitiveSeven.Order168Recognition.LinearComparison
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.GroupAction.Primitive

/-!
# Recognition of the simple degree-seven group of order 168

Cauchy's theorem supplies a seven-cycle and an involution. Simplicity forces
the sign character to be trivial, so the involution is a double transposition.
After normalizing the seven-cycle, checked permutation words force one of
the two explicit binary-plane groups into the given subgroup. The actual
matrix equivalences show that this inclusion is an equality by cardinality.
This constructs a multiplicative equivalence with PSL₃(2).

The primitivity hypothesis is retained to match the degree-seven consumer;
the proof in fact only needs simplicity and the given order inside S₇.
No primitive subgroup catalogue or symmetric-group section classification
is assumed.

Source context: Aschbacher–Smith, Theorem 0.1.2(3), printed p.4, and Main
Hypothesis (K), printed p.482. This recognizes the remaining faithful simple
quotient needed for the alternating examples' condition (K) calculation.
-/

namespace CFSG.Quasithin.MainConverse

open Order168Recognition
private abbrev P := Equiv.Perm (Fin 7)

private theorem sign_eq_one (U : Subgroup P) [IsSimpleGroup U] (hcard : Nat.card U = 168)
    (u : U) : Equiv.Perm.sign (u : P) = 1 := by
  let f : U →* ℤˣ := Equiv.Perm.sign.comp U.subtype
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker inferInstance with h | h
  · have hi := (MonoidHom.ker_eq_bot_iff f).mp h
    have hc := Nat.card_le_card_of_injective f hi
    have htwo : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card]; decide
    rw [hcard, htwo] at hc
    omega
  · exact congrArg (fun f : U →* ℤˣ => f u) (MonoidHom.ker_eq_top_iff.mp h)

private theorem normalize_cycle (s : P) (hs : orderOf s = 7) :
    ∃ q : P, MulAut.conj q s = cycle := by
  have hsc := Equiv.Perm.isCycle_of_prime_order'' (by decide) hs
  have hc : cycle.IsCycle := by
    apply Equiv.Perm.isCycle_of_prime_order'' (by decide)
    change orderOf cycle = 7
    have : Fact (Nat.Prime 7) := ⟨by decide⟩
    exact orderOf_eq_prime (by decide) (by decide)
  apply isConj_iff.mp
  apply hsc.isConj hc
  rw [← hsc.orderOf, ← hc.orderOf, hs]
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact (orderOf_eq_prime (by decide : cycle ^ 7 = 1) (by decide : cycle ≠ 1)).symm

/-- A simple primitive subgroup of S₇ of order 168 is the actual PSL₃(2) model. -/
public theorem primitiveSeven_order168_equiv_psl3Two
    (U : Subgroup (Equiv.Perm (Fin 7)))
    (_hp : MulAction.IsPreprimitive U (Fin 7)) (hsimple : IsSimpleGroup U)
    (hcard : Nat.card U = 168) :
    Nonempty (U ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := by
  let : IsSimpleGroup U := hsimple
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := U) 7 (by rw [hcard]; decide)
  obtain ⟨q, hq⟩ := normalize_cycle s ((Subgroup.orderOf_coe s).trans hs)
  let V := U.map (MulAut.conj q).toMonoidHom
  let eUV : U ≃* V := (MulAut.conj q).subgroupMap U
  have : IsSimpleGroup V := eUV.symm.isSimpleGroup
  have hV : Nat.card V = 168 := (Nat.card_congr eUV.toEquiv).symm.trans hcard
  have hc : cycle ∈ V := by
    exact ⟨s, s.property, hq⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := V) 2 (by rw [hV]; decide)
  obtain ⟨b, hb⟩ := seed_le_of_even_involution V hc hV t ht (sign_eq_one V hV t)
  let e := modelEquiv b
  have hcardSeed : Nat.card (seed b) = 168 :=
    (Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_PSL
  have heq : seed b = V := Subgroup.eq_of_le_of_card_ge hb (by rw [hcardSeed, hV])
  exact ⟨(eUV.trans (MulEquiv.subgroupCongr heq.symm)).trans e⟩

end CFSG.Quasithin.MainConverse
