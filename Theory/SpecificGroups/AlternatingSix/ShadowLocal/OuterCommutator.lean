module
public import Theory.SpecificGroups.AlternatingSix.OuterInvolutionExtension.Exceptional
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.NaturalFixed
/-!
# Odd-order commutators of outer involutions of A₆

For a natural odd involution, four explicit cubic conjugators supply a
nonidentity commutator of order three. Every exceptional involution is a
permutation conjugate of the canonical exceptional automorphism; its action
on (345) gives a commutator of order five. The conjugacy transport retains
the actual component element and automorphism action.

Source: Aschbacher–Smith 14.6.24(2), printed p.1041, and GLS3 5.2.7(a).
The finite certificates use six-letter permutations and are kernel checked.
-/

public section
open Subgroup GLS3.Chapter5
namespace AlternatingSix.ShadowLocal
private abbrev S := Equiv.Perm (Fin 6)
private def cubicPerm : Fin 4 → S := ![
  Equiv.swap 0 1 * Equiv.swap 1 2,
  Equiv.swap 0 3 * Equiv.swap 3 4,
  Equiv.swap 0 1 * Equiv.swap 1 3,
  Equiv.swap 0 2 * Equiv.swap 2 4]
private theorem cubic_even (i : Fin 4) : cubicPerm i ∈ alternatingGroup (Fin 6) := by
  change (cubicPerm i).sign = 1
  fin_cases i <;> decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem natural_certificate : ∀ s : S, s ^ 2 = 1 → s.sign ≠ 1 →
    ∃ i : Fin 4,
      (s*cubicPerm i*s⁻¹*(cubicPerm i)⁻¹)^3=1 ∧
      s*cubicPerm i*s⁻¹*(cubicPerm i)⁻¹≠1 := by decide +kernel
private def exceptionalTest : S := Equiv.swap 3 4 * Equiv.swap 4 5
private def exceptionalValue : S := Equiv.swap 0 1 * Equiv.swap 1 4 *
  (Equiv.swap 2 5 * Equiv.swap 5 3)
private theorem exceptional_value :
    canonicalExceptionalAut (⟨exceptionalTest,by change exceptionalTest.sign = 1; decide +kernel⟩ : A6) =
      ⟨exceptionalValue,by change exceptionalValue.sign = 1; decide +kernel⟩ := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  change outerAct (canonicalTwistPerm * exceptionalTest * canonicalTwistPerm⁻¹) i = _
  apply pentadAt_injective
  rw [outerAct_spec]
  fin_cases i <;> decide +kernel

private theorem canonical_odd_commutator :
    ∃ g : A6, orderOf (canonicalExceptionalAut g * g⁻¹) = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  refine ⟨⟨exceptionalTest,by change exceptionalTest.sign = 1; decide +kernel⟩,?_⟩
  rw [exceptional_value]
  apply orderOf_eq_prime <;> decide +kernel

/-- Every outer involution of Aut(A₆) has an actual component commutator
of order three or five. -/
theorem outer_involution_odd_commutator (β : AutA6) (hβ : orderOf β = 2)
    (hout : β ∉ inner) :
    ∃ g : A6, orderOf (β g * g⁻¹) = 3 ∨ orderOf (β g * g⁻¹) = 5 := by
  have hb2 : β ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one β
  by_cases hn : β ∈ natural
  · obtain ⟨s,hs⟩ := hn
    change permutationAction s = β at hs
    have hs2 : s ^ 2 = 1 := by
      apply permutationAction_injective
      rw [map_pow,hs,hb2,map_one]
    have hsign : s.sign ≠ 1 := by
      intro he
      exact hout ⟨⟨s,he⟩,(permutationAction_coe ⟨s,he⟩).symm.trans hs⟩
    obtain ⟨i,hi,hi'⟩ := natural_certificate s hs2 hsign
    refine ⟨⟨cubicPerm i,cubic_even i⟩,Or.inl ?_⟩
    rw [←hs]
    apply orderOf_eq_prime
    · apply Subtype.ext
      exact hi
    · intro hz
      exact hi' (congrArg Subtype.val hz)
  · obtain ⟨s,hs⟩ := exceptionalAut_eq_twist β hn
    obtain ⟨c,hc⟩ := exceptionalTwistAut_conjugate_canonical s (hs ▸ hb2)
    let a : MulAut A6 := MulAut.conjNormal c
    have he : β = a * canonicalExceptionalAut * a⁻¹ := hs.trans hc
    obtain ⟨g,hg⟩ := canonical_odd_commutator
    refine ⟨a g,Or.inr ?_⟩
    have hh : β (a g) * (a g)⁻¹ = a (canonicalExceptionalAut g * g⁻¹) := by
      rw [he]
      simp only [MulAut.mul_apply,MulAut.inv_apply,a.symm_apply_apply,map_mul,map_inv]
    rw [hh]
    exact (orderOf_injective a.toMonoidHom a.injective _).trans hg
end AlternatingSix.ShadowLocal
