module
public import Theory.ElementaryAbelian.AutomorphismCardEight
public import Theory.GroupTheory.CentralQuotientCommutatorForms
public import Theory.LinearAlgebra.BinaryAlternatingThree

/-!
# Odd center-fixed automorphisms of a central quotient of order eight

If the central quotient is elementary abelian of order eight, an automorphism
of odd prime order fixing the center acts trivially on the quotient.
Its nontrivial quotient action would have order three or seven, by the order
168 of GL₃(2). The faithful commutator pairing gives a separating family of
invariant alternating scalar forms; the rank-three common-radical obstruction
excludes both orders. Individual scalar forms need not be nondegenerate.

Source: MacWilliams, *On 2-groups with no normal abelian subgroups of rank 3*
(1970), §3, pp.366–374.
-/
open scoped IsMulCommutative

namespace IsElementaryAbelian

/-- An odd prime order automorphism fixing the center acts trivially on an
elementary binary central quotient of order eight. -/
public theorem quotientAut_eq_one_of_card_eight_of_odd_prime
    {P : Type*} [Group P] [Finite P]
    (hquot : IsElementaryAbelian 2 (P ⧸ Subgroup.center P))
    (hcard : Nat.card (P ⧸ Subgroup.center P) = 8)
    {q : ℕ} (hq : q.Prime) (hodd : Odd q)
    (a : MulAut P) (horder : orderOf a = q)
    (hfix : ∀ z : Subgroup.center P, a z = z) :
    Subgroup.quotientAut (Subgroup.center P) a = 1 := by
  classical
  let := hquot
  let E := P ⧸ Subgroup.center P
  let b : MulAut E := Subgroup.quotientAut (Subgroup.center P) a
  by_contra hn
  change b ≠ 1 at hn
  have hord : orderOf b = q := by
    have hd := orderOf_map_dvd (Subgroup.quotientAut (Subgroup.center P)) a
    rw [horder] at hd
    exact ((Nat.dvd_prime hq).mp hd).resolve_left (fun h => hn (orderOf_eq_one_iff.mp h))
  have hdiv : q ∣ 168 := by
    rw [← card_mulAut_of_elementary_eight E hcard, ← hord]
    exact orderOf_dvd_natCard b
  have hcases : q = 3 ∨ q = 7 := by
    have hf : q ∣ 2 * (2 * (2 * (3 * 7))) := hdiv
    rcases (hq.dvd_mul.mp hf) with h | h
    · have he := (Nat.dvd_prime Nat.prime_two).mp h
      rcases he with he | he
      · exact (hq.ne_one he).elim
      · rw [he] at hodd; norm_num at hodd
    rcases hq.dvd_mul.mp h with h | h
    · have he := (Nat.dvd_prime Nat.prime_two).mp h
      rcases he with he | he
      · exact (hq.ne_one he).elim
      · rw [he] at hodd; norm_num at hodd
    rcases hq.dvd_mul.mp h with h | h
    · have he := (Nat.dvd_prime Nat.prime_two).mp h
      rcases he with he | he
      · exact (hq.ne_one he).elim
      · rw [he] at hodd; norm_num at hodd
    rcases hq.dvd_mul.mp h with h | h
    · exact Or.inl (((Nat.dvd_prime (by decide : Nat.Prime 3)).mp h).resolve_left hq.ne_one)
    · exact Or.inr (((Nat.dvd_prime (by decide : Nat.Prime 7)).mp h).resolve_left hq.ne_one)
  let linearize : MulAut E ≃* (Additive E ≃ₗ[ZMod 2] Additive E) :=
    { toFun := fun a => { a.toAdditive with map_smul' := ZMod.map_smul a.toAdditive }
      invFun := fun a => MulEquiv.toAdditive.symm a.toAddEquiv
      left_inv := by intro a; ext; rfl
      right_inv := by intro a; ext; rfl
      map_mul' := by intro a b; ext; rfl }
  have hdim : Module.finrank (ZMod 2) (Additive E) = 3 := by
    have hs := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
    have hp : 2 ^ Module.finrank (ZMod 2) (Additive E) = 2 ^ 3 := by
      change Nat.card E = _ at hs
      simpa only [Nat.card_zmod, show Nat.card E = 8 from hcard, show (2 : ℕ) ^ 3 = 8 by decide] using hs.symm
    exact Nat.pow_right_injective (by decide : 1 < 2) hp
  obtain ⟨forms, halt, hsep, hpres⟩ :=
    exists_separating_invariant_central_quotient_forms (P := P)
  have hp : linearize b ^ 3 = 1 ∨ linearize b ^ 7 = 1 := by
    have hb : b ^ q = 1 := by rw [← hord]; exact pow_orderOf_eq_one b
    have hl : linearize b ^ q = 1 := by rw [← map_pow, hb, map_one]
    rcases hcases with rfl | rfl
    · exact Or.inl hl
    · exact Or.inr hl
  have he := BinaryAlternatingThree.eq_one_of_separating_forms hdim forms halt hsep
    (linearize b) hp (hpres a hfix)
  exact hn (linearize.injective (he.trans linearize.map_one.symm))

end IsElementaryAbelian
