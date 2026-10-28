module

public import Theory.SpecificGroups.Monster.Construction.LocalC.Action
public import Theory.SpecificGroups.Monster.Construction.LocalC.ShortFamilies.PureFour

/-!
# Conjugation on the two literal pure-four lifts

The source words `r_u` and `r_v` are evaluated in the actual extraspecial
image inside `N/K`. The even pair cocode acts by its two-coordinate sign.
The identity `k1 = z2 * psi1(omega)` identifies the image of `z2` with the
omega loop word, giving the second-loop interchange of `r_u` and `r_v`.
Standard automorphisms transport the coordinates; odd parity contributes
precisely the central involution to `r_u`.

The short-vector consumer is `LocalCompatibility.ShortAction`; these are
identities of the fixed group elements, retaining their central signs.
Source: Aschbacher, *Sporadic Groups*, 14.2, 14.3, 27.8(4), and the proof
of 29.4, printed pp. 58–61, 150, 155. Products use left composition.
-/

@[expose] public section
noncomputable section
open Atlas.Codes Atlas.Fischer
namespace Sporadic.Monster.Construction.NMonomial.EAction
open TrialitySpin LocalC LocalC.ShortFamilies LocalC.TrialityGeneratorCalculation

private theorem pair_pairing (d : golay) (x y : Omega) :
    cocodePairing d (Submodule.Quotient.mk (pairWord x y)) = d.val x + d.val y := by
  simp [cocodePairing, cocodeDualEquiv_mk, pairWord, pointWord, binaryDot_apply,
    Pi.single_apply]

private theorem pair_even (x y : Omega) :
    (parkerCocodeStandard (Submodule.Quotient.mk (pairWord x y))).val parkerOmega =
      parkerOmega := by
  rw [parkerCocodeStandard_apply, pair_pairing]
  simp [parkerOmega, golayOne, allOnes]

private theorem pair_aut (x y : Omega) (d : ParkerLoop) :
    (parkerCocodeStandard (Submodule.Quotient.mk (pairWord x y))).val d =
      parkerSign (d.1.val x + d.1.val y) d := by
  rw [parkerCocodeStandard_apply, pair_pairing]
  rfl

private theorem pair_aut_twice (x y : Omega) (d : ParkerLoop) :
    (parkerCocodeStandard (Submodule.Quotient.mk (pairWord x y))).val
      ((parkerCocodeStandard (Submodule.Quotient.mk (pairWord x y))).val d) = d := by
  simp [parkerCocodeStandard_apply, add_assoc]

private theorem center_commute (q : Q1Image) :
    Commute q1ImageCenterGenerator q := by
  have h : q1ImageCenterGenerator ∈ Subgroup.center Q1Image := by
    rw [Q1Image_center]
    exact Subgroup.mem_zpowers _
  exact (Subgroup.mem_center_iff.mp h q).symm

private theorem image_conjugation_val (g : N1) (q : Q1Image) :
    (q1ImageConjugation g q).val =
      nQuotientMap g.val * q.val * (nQuotientMap g.val)⁻¹ := rfl

private theorem omega_inv : (psi1N parkerOmega)⁻¹ = psi1N parkerOmega := by
  rw [psi1N_inv, loopInverse_omega]

private theorem omega_square : loopImage parkerOmega * loopImage parkerOmega = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, loopImage_val, ← map_mul]
  nth_rw 1 [← omega_inv]
  rw [inv_mul_cancel, map_one]
  rfl

private theorem quotient_z2 : nQuotientMap z2N = (loopImage parkerOmega).val := by
  have h := congrArg nQuotientMap k1_eq_z2_mul_psi1_omega
  rw [(nQuotientMap_eq_one k1).mpr ((mem_K_iff k1).mpr (by simp)), map_mul] at h
  have hi := eq_inv_of_mul_eq_one_left h.symm
  rw [← map_inv, omega_inv] at hi
  simpa only [loopImage_val] using hi

private theorem conjugation_omega_one (d : ParkerLoop) :
    q1ImageConjugation ⟨psi1N d, psi1N_mem_N1 d⟩ (loopImage parkerOmega) =
      loopImage parkerOmega := by
  have hc : Commute (psi1N d) (psi1N parkerOmega) := by
    apply Subtype.ext
    ext ⟨a,b,c⟩ : 1
    change psi1 d (psi1 parkerOmega (a,b,c)) = psi1 parkerOmega (psi1 d (a,b,c))
    simp [psi1_apply, loopInverse_omega]
  apply Subtype.ext
  rw [image_conjugation_val, loopImage_val, ← map_inv, ← map_mul, ← map_mul,
    hc.eq, mul_inv_cancel_right]

private theorem conjugation_omega_two (d : ParkerLoop) :
    q1ImageConjugation ⟨psi2N d, psi2N_mem_N1 d⟩ (loopImage parkerOmega) =
      loopImage parkerOmega := by
  have hc : Commute (psi2N d) z2N := by
    apply Subtype.ext
    ext ⟨a,b,c⟩ : 1
    change psi2 d (z2 (a,b,c)) = z2 (psi2 d (a,b,c))
    simp
  apply Subtype.ext
  rw [image_conjugation_val, ← quotient_z2, ← map_inv, ← map_mul, ← map_mul,
    hc.eq, mul_inv_cancel_right]

private theorem cocode_one (d : ParkerLoop) (x y : Omega) :
    q1ImageConjugation ⟨psi1N d, psi1N_mem_N1 d⟩ (cocodeImage (pairWord x y)) =
      cocodeImage (pairWord x y) * q1ImageCenterGenerator ^ (d.1.val x + d.1.val y).val := by
  let α := parkerCocodeStandard (Submodule.Quotient.mk (pairWord x y))
  have hm := aut_psi1_even α (pair_even x y) (α.val d)
  rw [pair_aut_twice] at hm
  rw [pair_aut, psi1N_sign] at hm
  apply Subtype.ext
  rw [image_conjugation_val, cocodeImage_val]
  rw [Subgroup.coe_mul, Subgroup.coe_pow, cocodeImage_val]
  have hz : q1ImageCenterGenerator.val = nQuotientMap z1N := rfl
  rw [hz, ← map_pow, ← map_mul, ← map_inv, ← map_mul, ← map_mul, ← hm]
  simp only [mul_assoc, mul_inv_cancel, mul_one]
  rfl


private theorem cocode_two (d : ParkerLoop) (x y : Omega) :
    q1ImageConjugation ⟨psi2N d, psi2N_mem_N1 d⟩ (cocodeImage (pairWord x y)) =
      cocodeImage (pairWord x y) * loopImage parkerOmega ^ (d.1.val x + d.1.val y).val := by
  let α := parkerCocodeStandard (Submodule.Quotient.mk (pairWord x y))
  have hm := aut_psi2_even α (pair_even x y) (α.val d)
  rw [pair_aut_twice, pair_aut, psi2_sign] at hm
  apply Subtype.ext
  rw [image_conjugation_val, Subgroup.coe_mul, Subgroup.coe_pow, ← quotient_z2,
    cocodeImage_val, ← map_pow, ← map_mul, ← map_inv, ← map_mul, ← map_mul]
  have hs : psi2N (0,d.1.val x + d.1.val y) = z2N ^ (d.1.val x + d.1.val y).val := by
    have hb : ∀ b : ParkerBit, b = 0 ∨ b = 1 := by decide
    rcases hb (d.1.val x + d.1.val y) with h | h
    · simp only [h]; exact psi2_one
    · simp only [h]; rfl
  rw [hs] at hm
  rw [← hm]
  simp only [mul_assoc, mul_inv_cancel, mul_one]
  rfl

private theorem omega_cocode_commute (x y : Omega) :
    Commute (loopImage parkerOmega) (cocodeImage (pairWord x y)) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, loopImage_val, cocodeImage_val,
    ← map_mul, ← map_mul]
  have h := aut_psi1_even _ (pair_even x y) parkerOmega
  rw [pair_even] at h
  exact congrArg nQuotientMap h.symm

private theorem standard_pair_interchange (α : ParkerStandardGroup) (x y : Omega) :
    α * parkerCocodeStandard (Submodule.Quotient.mk (pairWord x y)) =
      parkerCocodeStandard (Submodule.Quotient.mk (pairWord
        ((parkerStandardProjection α).val x) ((parkerStandardProjection α).val y))) * α := by
  apply Subtype.ext
  apply Equiv.ext
  intro d
  simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply]
  rw [pair_aut, parkerStandard_preserves_sign, pair_aut]
  congr 1
  rw [parkerStandardProjection_spec]
  simp [parkerCodeEquiv, Atlas.Codes.coordinatePermutation]

private theorem cocode_standard (α : ParkerStandardGroup) (x y : Omega) :
    q1ImageConjugation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (cocodeImage (pairWord x y)) =
      cocodeImage (pairWord ((parkerStandardProjection α).val x)
        ((parkerStandardProjection α).val y)) := by
  have h := congrArg psiAut1N (standard_pair_interchange α x y)
  rw [aut_mul, aut_mul] at h
  apply Subtype.ext
  rw [image_conjugation_val, cocodeImage_val, cocodeImage_val,
    ← map_inv, ← map_mul, ← map_mul, h, mul_inv_cancel_right]

private theorem omega_standard_even (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) :
    q1ImageConjugation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (loopImage parkerOmega) =
      loopImage parkerOmega := by
  apply Subtype.ext
  rw [image_conjugation_val, loopImage_val, ← map_inv, ← map_mul, ← map_mul,
    aut_psi1_even α hα, hα, mul_inv_cancel_right]

private theorem omega_standard_odd (α : ParkerStandardGroup)
    (hα : α.val parkerOmega ≠ parkerOmega) :
    q1ImageConjugation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (loopImage parkerOmega) =
      q1ImageCenterGenerator * loopImage parkerOmega := by
  rw [← show q1ImageCenterGenerator ^ (1 : ParkerBit).val = q1ImageCenterGenerator by rfl,
    ← loopImage_sign]
  apply Subtype.ext
  rw [image_conjugation_val, loopImage_val, loopImage_val,
    ← map_inv, ← map_mul, ← map_mul, aut_psi1_odd α hα, loopInverse_omega,
    parkerStandard_omega_odd α hα, mul_inv_cancel_right]

/-- Actual first-loop conjugation on the source `r_u` lift. -/
theorem ruElement_conjugation_loopOne (d : ParkerLoop) (x y : Omega) :
    q1ImageConjugation ⟨psi1N d, psi1N_mem_N1 d⟩ (ruElement x y) =
      ruElement x y * q1ImageCenterGenerator ^ (d.1.val x + d.1.val y).val := by
  simp only [ruElement, map_mul, conjugation_omega_one, cocode_one, mul_assoc]

/-- Actual first-loop conjugation on the source `r_v` lift. -/
theorem rvElement_conjugation_loopOne (d : ParkerLoop) (x y : Omega) :
    q1ImageConjugation ⟨psi1N d, psi1N_mem_N1 d⟩ (rvElement x y) =
      rvElement x y * q1ImageCenterGenerator ^ (d.1.val x + d.1.val y).val :=
  cocode_one d x y

/-- The second loop interchanges the two actual lifts at odd pair parity. -/
theorem ruElement_conjugation_loopTwo (d : ParkerLoop) (x y : Omega) :
    q1ImageConjugation ⟨psi2N d, psi2N_mem_N1 d⟩ (ruElement x y) =
      if d.1.val x + d.1.val y = 0 then ruElement x y else rvElement x y := by
  rw [ruElement, map_mul, conjugation_omega_two, cocode_two]
  have hb : ∀ b : ParkerBit, b = 0 ∨ b = 1 := by decide
  rcases hb (d.1.val x + d.1.val y) with h | h
  · simp only [h, ZMod.val_zero, pow_zero, mul_one, ↓reduceIte]
  · simp only [h, one_ne_zero, ↓reduceIte, ZMod.val_one, pow_one]
    rw [← mul_assoc, (omega_cocode_commute x y).eq, mul_assoc, omega_square, mul_one]
    rfl

/-- The complementary second-loop interchange. -/
theorem rvElement_conjugation_loopTwo (d : ParkerLoop) (x y : Omega) :
    q1ImageConjugation ⟨psi2N d, psi2N_mem_N1 d⟩ (rvElement x y) =
      if d.1.val x + d.1.val y = 0 then rvElement x y else ruElement x y := by
  rw [rvElement, cocode_two]
  have hb : ∀ b : ParkerBit, b = 0 ∨ b = 1 := by decide
  rcases hb (d.1.val x + d.1.val y) with h | h
  · simp only [h, ZMod.val_zero, pow_zero, mul_one, ↓reduceIte]
  · simp only [h, one_ne_zero, ↓reduceIte, ZMod.val_one, pow_one]
    exact (omega_cocode_commute x y).eq.symm

/-- Even standard automorphisms transport both coordinates of the actual `u` lift. -/
theorem ruElement_conjugation_standard_even (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) (x y : Omega) :
    q1ImageConjugation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (ruElement x y) =
      ruElement ((parkerStandardProjection α).val x) ((parkerStandardProjection α).val y) := by
  simp only [ruElement, map_mul, omega_standard_even α hα, cocode_standard]

/-- Odd standard automorphisms change the central sign of the actual `u` lift. -/
theorem ruElement_conjugation_standard_odd (α : ParkerStandardGroup)
    (hα : α.val parkerOmega ≠ parkerOmega) (x y : Omega) :
    q1ImageConjugation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (ruElement x y) =
      ruElement ((parkerStandardProjection α).val x) ((parkerStandardProjection α).val y) *
        q1ImageCenterGenerator := by
  rw [ruElement, map_mul, omega_standard_odd α hα, cocode_standard, mul_assoc]
  exact (center_commute _).eq

/-- Every standard automorphism transports `v` without a central sign. -/
theorem rvElement_conjugation_standard (α : ParkerStandardGroup) (x y : Omega) :
    q1ImageConjugation ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ (rvElement x y) =
      rvElement ((parkerStandardProjection α).val x) ((parkerStandardProjection α).val y) :=
  cocode_standard α x y

end Sporadic.Monster.Construction.NMonomial.EAction
