module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.OddComparison.StandardConjugation.IndexCorrection
public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.OddComparison.Stability
public import Theory.SpecificGroups.Monster.Construction.LocalC.LatticeComparison.TrialityGenerators.Relations

/-!
# Standard automorphisms on the actual odd short family

Conjugating the three factors of `rOddElement` gives exact identities in
`Q1Image`, including the central sign. Standard automorphisms transport the
point cocode by their actual Golay coordinate permutation. In the odd case,
inversion of the loop contributes its quarter-weight, while negation of the
all-ones loop contributes the point's code bit. The genuine restricted local
representation carries these identities to signed odd-family vectors.

These are the first-standard-generator formulas required in the proof of
Aschbacher 29.8. The printed subscript 2 in 29.6(3) is inconsistent with the
Section 14 definitions and with the first generator used in that proof.
The companion `StandardConjugation.IndexCorrection` checks the discrepancy
in the actual quotient by the four-group, using the singleton cocode and
the loop identity element.

Source: Michael Aschbacher, *Sporadic Groups*, Section 14, printed pp. 58–61
(PDF pp. 35–36), 27.8(3), printed p. 150 (PDF p. 81), and 29.6(3), 29.8,
printed pp. 156–157 (PDF p. 84). Products reverse the book's right-action
order; conjugation here is `g * q * g⁻¹`. Existing private triality lemmas
remain private; the calculation uses the published Section 14 relations.
-/

@[expose] public section
open Atlas.Codes Atlas.Fischer Atlas.Lattices
open Sporadic.Monster.Construction LocalC ShortFamilies TrialitySpin
open LocalC.TrialityGeneratorCalculation
noncomputable section
namespace Sporadic.Monster.Construction.NMonomial.ZeroAction

private theorem standard_coordinate (α : ParkerStandardGroup) (b : ParkerLoop) (x : Omega) :
    (α.val b).1.val ((parkerStandardProjection α).val x) = b.1.val x := by
  rw [parkerStandardProjection_spec]
  change b.1.val ((parkerStandardProjection α).val.symm
    ((parkerStandardProjection α).val x)) = _
  rw [Equiv.symm_apply_apply]

private theorem point_pairing (b : golay) (x : Omega) :
    cocodePairing b (Submodule.Quotient.mk (pointWord x)) = b.val x := by
  simp [cocodePairing, cocodeDualEquiv_mk, pointWord, binaryDot_apply, Pi.single_apply]

private theorem conjugation_val (g : N1) (q : Q1Image) :
    (q1ImageConjugation g q).val =
      nQuotientMap g.val * q.val * (nQuotientMap g.val)⁻¹ := rfl

private theorem conjugation_point (α : ParkerStandardGroup) (x : Omega) :
    q1ImageConjugation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (cocodeImage (pointWord x)) =
      cocodeImage (pointWord ((parkerStandardProjection α).val x)) := by
  have h : α * parkerCocodeStandard (Submodule.Quotient.mk (pointWord x)) =
      parkerCocodeStandard (Submodule.Quotient.mk
        (pointWord ((parkerStandardProjection α).val x))) * α := by
    apply Subtype.ext
    ext d : 1
    change α.val (parkerSign (cocodePairing d.1 (Submodule.Quotient.mk (pointWord x))) d) =
      parkerSign (cocodePairing (α.val d).1 (Submodule.Quotient.mk
        (pointWord ((parkerStandardProjection α).val x)))) (α.val d)
    rw [parkerStandard_preserves_sign, point_pairing, point_pairing, standard_coordinate]
  have hm := congrArg psiAut1N h
  rw [aut_mul, aut_mul] at hm
  apply Subtype.ext
  rw [conjugation_val, cocodeImage_val, cocodeImage_val]
  change nQuotientMap (psiAut1N α) * nQuotientMap (psiAut1N _) *
    (nQuotientMap (psiAut1N α))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul, hm, mul_inv_cancel_right]

private theorem conjugation_loop_even (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) (d : ParkerLoop) :
    q1ImageConjugation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (loopImage d) =
      loopImage (α.val d) := by
  apply Subtype.ext
  rw [conjugation_val, loopImage_val, loopImage_val]
  change nQuotientMap (psiAut1N α) * nQuotientMap (psi1N d) *
    (nQuotientMap (psiAut1N α))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul, aut_psi1_even α hα, mul_inv_cancel_right]

private theorem conjugation_loop_odd (α : ParkerStandardGroup)
    (hα : α.val parkerOmega ≠ parkerOmega) (d : ParkerLoop) :
    q1ImageConjugation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (loopImage d) =
      loopImage (α.val (loopInverse d)) := by
  apply Subtype.ext
  rw [conjugation_val, loopImage_val, loopImage_val]
  change nQuotientMap (psiAut1N α) * nQuotientMap (psi1N d) *
    (nQuotientMap (psiAut1N α))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul, aut_psi1_odd α hα, mul_inv_cancel_right]

private theorem omega_odd (α : ParkerStandardGroup)
    (hα : α.val parkerOmega ≠ parkerOmega) :
    α.val parkerOmega = parkerSign 1 parkerOmega := by
  have h := parkerStandard_omega α
  rcases bit_cases (α.val parkerOmega).2 with he | he
  · exact False.elim (hα (by simpa [he] using h))
  · simpa only [he] using h

/-- Even standard automorphisms transport the literal odd word without a sign correction. -/
theorem rOddElement_conjugation_standard_even (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) (x : Omega) (b : ParkerLoop) :
    q1ImageConjugation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (rOddElement x b) =
      rOddElement ((parkerStandardProjection α).val x) (α.val b) := by
  simp only [rOddElement, map_mul, map_pow, conjugation_loop_even α hα,
    conjugation_point, hα, standard_coordinate]

/-- Odd standard automorphisms contribute the coordinate and quarter-weight central signs. -/
theorem rOddElement_conjugation_standard_odd (α : ParkerStandardGroup)
    (hα : α.val parkerOmega ≠ parkerOmega) (x : Omega) (b : ParkerLoop) :
    q1ImageConjugation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (rOddElement x b) =
      rOddElement ((parkerStandardProjection α).val x)
        (parkerSign (b.1.val x + golayQuarterWeight b.1) (α.val b)) := by
  rw [rOddElement_sign]
  simp only [rOddElement, map_mul, map_pow, conjugation_loop_odd α hα,
    conjugation_point, loopInverse_omega, omega_odd α hα, standard_coordinate]
  rw [loopInverse, parkerStandard_preserves_sign]
  simp only [loopImage_sign]
  have hc : loopImage (α.val b) * q1ImageCenterGenerator =
      q1ImageCenterGenerator * loopImage (α.val b) :=
    Subgroup.mem_center_iff.mp centerGenerator_mem _
  rcases bit_cases (b.1.val x) with hb | hb <;>
    rcases bit_cases (golayQuarterWeight b.1) with hq | hq <;>
    simp only [hb, hq, zero_add, add_zero, CharTwo.add_self_eq_zero,
      show (0 : ParkerBit).val = 0 from rfl,
      show (1 : ParkerBit).val = 1 from rfl, pow_zero, pow_one, one_mul, mul_one]
  · simp only [mul_assoc]
  · simp only [← mul_assoc, hc]
  · have hz : q1ImageCenterGenerator * loopImage (α.val b) *
        q1ImageCenterGenerator = loopImage (α.val b) := by
      rw [mul_assoc, hc, ← mul_assoc, ← pow_two, q1ImageCenterGenerator_sq, one_mul]
    simp only [← mul_assoc, hz]

/-- The even standard generator on the actual signed odd-family vectors. -/
theorem oddRepresentation_standard_even (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) (x : Omega) (b : ParkerLoop) :
    oddRepresentation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (zeroOdd x b).1 =
      (zeroOdd ((parkerStandardProjection α).val x) (α.val b)).1 :=
  oddRepresentation_vector_of_conjugation _ _ _ _ _
    (rOddElement_conjugation_standard_even α hα x b)

/-- The odd standard generator retains both contributions to the central sign. -/
theorem oddRepresentation_standard_odd (α : ParkerStandardGroup)
    (hα : α.val parkerOmega ≠ parkerOmega) (x : Omega) (b : ParkerLoop) :
    oddRepresentation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (zeroOdd x b).1 =
      (zeroOdd ((parkerStandardProjection α).val x)
        (parkerSign (b.1.val x + golayQuarterWeight b.1) (α.val b))).1 :=
  oddRepresentation_vector_of_conjugation _ _ _ _ _
    (rOddElement_conjugation_standard_odd α hα x b)

end Sporadic.Monster.Construction.NMonomial.ZeroAction
