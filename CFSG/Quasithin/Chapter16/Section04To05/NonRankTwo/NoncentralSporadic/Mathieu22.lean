module

public import CFSG.Quasithin.Chapter16.Section04To05.NonRankTwo.NoncentralSporadic.Basic
public import CFSG.Quasithin.Chapter16.Section04To05.NonRankTwo.Models
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.Fusion

/-!
# Excluding M₂₂ from the noncentral-projection branch

The genuine involution-fusion theorem for the degree-22 Mathieu carrier,
combined with the nontrivial center of a Sylow two-subgroup, makes every
involution two-central. Transport through the specified L/Z(L) isomorphism
contradicts the branch assumption. No class-count label is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
16.5.11, printed p.1199. The imported Mathieu fusion proof works with actual
permutation conjugators.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.NonRankTwo.NoncentralSporadic

open Subgroup
open scoped IsMulCommutative

/-- M₂₂ is impossible in the noncentral-projection branch, using its proved
single involution class and the actual central-quotient isomorphism. -/
theorem quotient_not_m22_of_noncentral
    {L : Type*} [Group L] [Finite L] {v : L ⧸ center L}
    (hv : orderOf v = 2) (hnot : ¬ TwoCentral v) :
    ¬ Nonempty ((L ⧸ center L) ≃* Sporadic.Mathieu.M22) := by
  rintro ⟨e⟩
  have hm : TwoCentral (e v) := twoCentral_of_single_involution_class
    Sporadic.Mathieu.m22_involutions_isConj ((e.orderOf_eq v).trans hv)
  exact hnot (by simpa using hm.map e.symm)

/-- Remove exactly M₂₂ from 16.5.10(2), retaining the actual quotient
equivalences for each of the remaining six names. -/
theorem sporadic_remainder_cases_of_noncentral
    {L : Type*} [Group L] [Finite L] {v : L ⧸ center L}
    (hv : orderOf v = 2) (hnot : ¬ TwoCentral v) (hL : SporadicRemainder L) :
    ∃ name : ClassificationModels.SporadicName,
      (name = .m12 ∨ name = .m24 ∨ name = .j2 ∨ name = .j4 ∨
        name = .hs ∨ name = .ru) ∧ Nonempty ((L ⧸ center L) ≃* name.Carrier) := by
  obtain ⟨name, hn, he⟩ := hL
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.m12, Or.inl rfl, he⟩
  · exact (quotient_not_m22_of_noncentral hv hnot he).elim
  · exact ⟨.m24, Or.inr (Or.inl rfl), he⟩
  · exact ⟨.j2, Or.inr (Or.inr (Or.inl rfl)), he⟩
  · exact ⟨.j4, Or.inr (Or.inr (Or.inr (Or.inl rfl))), he⟩
  · exact ⟨.hs, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), he⟩
  · exact ⟨.ru, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), he⟩

end CFSG.Quasithin.Chapter16.Intersections.NonRankTwo.NoncentralSporadic
