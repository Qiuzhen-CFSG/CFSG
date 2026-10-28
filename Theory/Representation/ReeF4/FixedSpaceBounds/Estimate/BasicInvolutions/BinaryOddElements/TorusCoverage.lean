module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements.TorusData
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements.TorusCoverage.Inputs

/-!
# Assembly of binary Ree torus placement and the short-weight spectrum

An order-five or order-thirteen binary Ree element has the same order as the
parameter tuple in any presentation by a conjugate of the positive coroot
product. Thus its four parameters satisfy the appropriate prime power equation
and are not all one. The finite balanced-spectrum bound then gives at most four
fixed short-root characters, hence the twenty moving characters required by
`BinaryOddTorusCoverage`.

This module currently proves the conditional assembly. Its independent inputs
are actual torus placement, short/long balance from the Ree fixed-point equation,
and the finite balanced-spectrum bound. All three remain to be supplied before
asserting unconditional coverage. The representation-theoretic consumer remains
`binaryOddDisplacement_of_torusCoverage` in `BinaryOddElements`.

Source: Guralnick--Malle II, Lemma 8.8 (internal p.57), and GLS3, Sections 1.14
and 2.8. In particular, the source degree exclusion alone is not this spectrum.
-/

public section

open Theory.AlgebraicGroup
open ReeF4.BinaryDegree.ExceptionalTensor
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements.TorusCoverage

variable {F : Type*} [Field F] [IsAlgClosed F]

theorem coverage_of_placement_balance_spectrum
    (hp : Placement F) (hb : Balance F) (hs : PrimeSpectrumBound F) :
    BinaryOddTorusCoverage F := by
  intro f x hx
  obtain ⟨c, t, he⟩ := hp f x hx
  have horder : orderOf t = orderOf x := parameter_orderOf_of_conjugate f x c t he
  have ht : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at horder
    omega
  obtain ⟨p, hprime, hxp⟩ : ∃ p : ℕ, (p = 5 ∨ p = 13) ∧ orderOf x = p := by
    rcases hx with hx | hx
    · exact ⟨5, Or.inl rfl, hx⟩
    · exact ⟨13, Or.inr rfl, hx⟩
  have hpow : t ^ p = 1 := by
    rw [← hxp, ← horder]
    exact pow_orderOf_eq_one t
  have hcoords (i : Fin 4) : t i ^ p = 1 := congrFun hpow i
  refine ⟨c, t, he, (endWeightMovement_iff_fixedWeightCount_le t).mpr ?_⟩
  exact hs p hprime t ht hcoords (hb f x hx c t he)

end ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements.TorusCoverage
