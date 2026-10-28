module

public import Theory.SpecificGroups.Monster.Construction.LocalC.ShortFamilies.Basic

/-!
# Checking the standard-generator index in the actual quotient

For the singleton cocode at x, the induced standard automorphism is odd and
has trivial Golay coordinate projection. Thus the odd right side printed in
29.6(3), evaluated at the loop identity, is `r(x,1)`. Nevertheless its second
standard generator does not fix this element in `N/K`.

For any odd standard automorphism, the first and second standard generators
induce the distinct axis transpositions (23) and (13). Their two products
send axis 1 to different axes. Every element of the actual four-group K
preserves axis 1, so the two products remain distinct in the quotient.
Specializing to the singleton cocode proves the asserted counterexample.
This verifies the need for the first-standard-generator formula used by
29.8, rather than assuming that a source-numbered interface is correct.

Source: Michael Aschbacher, *Sporadic Groups*, Section 14, printed pp. 58–61
(PDF pp. 35–36), 27.8(3), printed p. 150 (PDF p. 81), and 29.6(3), 29.8,
printed pp. 156–157 (PDF p. 84). The formulas use left composition and the
literal quotient by K.
-/

@[expose] public section
open Atlas.Codes Atlas.Fischer Atlas.Lattices
open Sporadic.Monster.Construction LocalC ShortFamilies TrialitySpin
noncomputable section
namespace Sporadic.Monster.Construction.NMonomial.ZeroAction

private theorem point_odd (x : Omega) :
    (parkerCocodeStandard (Submodule.Quotient.mk (pointWord x))).val parkerOmega ≠
      parkerOmega := by
  intro h
  have hh := congrArg Prod.snd h
  change 0 + cocodePairing golayOne (Submodule.Quotient.mk (pointWord x)) = 0 at hh
  rw [zero_add, cocodePairing, cocodeDualEquiv_mk] at hh
  simp [golayOne, pointWord, binaryDot_apply, allOnes, Pi.single_apply] at hh

private theorem kernel_axis1 (k : N) (hk : k ∈ TrialitySpin.K) :
    ∃ b : ParkerLoop, k.val (axis1 loopOne) = axis1 b := by
  rcases (mem_K_iff k).mp hk with rfl | rfl | rfl | rfl
  · exact ⟨loopOne,rfl⟩
  · exact ⟨parkerSign 1 loopOne, by simp [axis1, k1_apply]⟩
  · exact ⟨parkerLoopMultiply loopOne (parkerSign 1 parkerOmega), by simp [axis1, k2_apply]⟩
  · exact ⟨parkerLoopMultiply loopOne parkerOmega, by simp [axis1, k3_apply]⟩

private theorem odd_generators_not_commute (α : ParkerStandardGroup)
    (hα : α.val parkerOmega ≠ parkerOmega) :
    nQuotientMap (psiAut2N α) * nQuotientMap (psiAut1N α) ≠
      nQuotientMap (psiAut1N α) * nQuotientMap (psiAut2N α) := by
  intro hh
  rw [← map_mul, ← map_mul] at hh
  obtain ⟨k,hk,he⟩ := (QuotientGroup.mk'_eq_mk' (N := TrialitySpin.K)).mp hh
  obtain ⟨b,hb⟩ := kernel_axis1 k hk
  have ht := congrArg (fun t : N => (t.val (axis1 loopOne)).2.1.isSome) he
  simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, hb] at ht
  change (psiAut2 α.val (psiAut1 α.val (axis1 b))).2.1.isSome =
    (psiAut1 α.val (psiAut2 α.val (axis1 loopOne))).2.1.isSome at ht
  simp [psiAut1, psiAut2, hα, diagonal, flip1, flip2, axis1] at ht

private theorem odd_one (x : Omega) : rOddElement x loopOne = cocodeImage (pointWord x) := by
  simp only [rOddElement, loopOne, Submodule.coe_zero, Pi.zero_apply,
    show (0 : ParkerBit).val = 0 from rfl, pow_zero, mul_one]
  have he : loopImage (0,0) = 1 := by
    apply Subtype.ext
    rw [loopImage_val, show (0,0) = loopOne from rfl,
      LocalC.TrialityGeneratorCalculation.psi1_one, map_one]
    rfl
  rw [he, one_mul]

/-- The singleton-cocode second standard generator does not fix the odd word at the loop identity, even modulo K. -/
theorem rOddElement_one_conjugation_psiAut2_ne (x : Omega) :
    let α := parkerCocodeStandard (Submodule.Quotient.mk (pointWord x))
    nQuotientMap (psiAut2N α) * (rOddElement x loopOne).val *
      (nQuotientMap (psiAut2N α))⁻¹ ≠ (rOddElement x loopOne).val := by
  dsimp only
  intro h
  rw [odd_one, cocodeImage_val] at h
  have hh := congrArg (fun q : NQuotient =>
    q * nQuotientMap (psiAut2N (parkerCocodeStandard (Submodule.Quotient.mk (pointWord x))))) h
  apply odd_generators_not_commute _ (point_odd x)
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh

/-- A concrete failure of the odd clause printed in 29.6(3), with its literal
right side. Its projection fixes the point and its right side is `r(x,1)`. -/
theorem rOddElement_conjugation_psiAut2_counterexample (x : Omega) :
    let α := parkerCocodeStandard (Submodule.Quotient.mk (pointWord x))
    nQuotientMap (psiAut2N α) * (rOddElement x loopOne).val *
      (nQuotientMap (psiAut2N α))⁻¹ ≠
      (rOddElement ((parkerStandardProjection α).val x)
        (parkerSign (loopOne.1.val x + golayQuarterWeight loopOne.1) (α.val loopOne))).val := by
  dsimp only
  simpa [loopOne, cocodePairing] using rOddElement_one_conjugation_psiAut2_ne x

end Sporadic.Monster.Construction.NMonomial.ZeroAction
