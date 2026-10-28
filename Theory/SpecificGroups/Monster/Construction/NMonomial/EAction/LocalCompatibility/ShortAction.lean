module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.EAction.PairModel
public import Theory.SpecificGroups.Monster.Construction.NMonomial.EAction.LocalCompatibility.Conjugation

/-!
# The source action on the literal wPlus and wMinus families

Actual conjugation of the fixed short lifts gives their signed-vector
action through `cShort_vector`. The first loop signs both families, while
the second interchanges `u` and `v`, fixing `wPlus` and signing `wMinus`.
A standard automorphism transports both marked coordinates and, in odd
parity, swaps `wPlus` with `wMinus`.

These formulas supply the short branches of `LocalCompatibility` and prove
Aschbacher 29.4 on the existing vectors, without an equivariance premise.
Source: Aschbacher, *Sporadic Groups*, 27.8(4–5), 29.4 and 29.10(3),
printed pp. 150, 155, 158–159.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.NMonomial.EAction
open TrialitySpin LocalC LocalC.ShortFamilies Atlas.Codes Atlas.Fischer

private theorem ru_val (x y : Omega) (hxy : x ≠ y) : (ru x y hxy).val = ruElement x y := rfl
private theorem rv_val (x y : Omega) (hxy : x ≠ y) : (rv x y hxy).val = rvElement x y := rfl

private theorem short_of_conjugation (g : N1) (q r : Lift)
    (h : q1ImageConjugation g q.val = r.val) :
    cShort (n1ToC g) (shortVector sourceLatticeComparison q) =
      shortVector sourceLatticeComparison r := by
  rw [cShort_vector]
  congr 1
  apply Subtype.ext
  change cConjugation (pullbackToC (n1Pullback g)) q.val = r.val
  rw [cConjugation_pullback]
  exact h

private theorem short_of_conjugation_sign (g : N1) (q r : Lift) (b : ParkerBit)
    (h : q1ImageConjugation g q.val = r.val * q1ImageCenterGenerator ^ b.val) :
    cShort (n1ToC g) (shortVector sourceLatticeComparison q) =
      sign b • shortVector sourceLatticeComparison r := by
  have hb : ∀ b : ParkerBit, b = 0 ∨ b = 1 := by decide
  obtain hb := hb b
  rcases hb with rfl | rfl
  · simpa only [ZMod.val_zero, pow_zero, mul_one, sign_zero, one_smul] using
      short_of_conjugation g q r (by simpa using h)
  · calc
      _ = shortVector sourceLatticeComparison ((shortLiftSigns sourceLatticeComparison).flip r) :=
        short_of_conjugation g q ((shortLiftSigns sourceLatticeComparison).flip r)
          (by
            change q1ImageConjugation g q.val = r.val * q1ImageCenterGenerator
            simpa only [ZMod.val_one, pow_one] using h)
      _ = -shortVector sourceLatticeComparison r := shortVector_sign _ r
      _ = _ := (neg_one_smul ℝ _).symm


private theorem short_u_loopOne (d : ParkerLoop) (x y : Omega) (hxy : x ≠ y) :
    cShort (n1ToC ⟨psi1N d, psi1N_mem_N1 d⟩) (u x y hxy) =
      sign (d.1.val x + d.1.val y) • u x y hxy :=
  short_of_conjugation_sign _ (ru x y hxy) (ru x y hxy) _
    (ruElement_conjugation_loopOne d x y)

private theorem short_v_loopOne (d : ParkerLoop) (x y : Omega) (hxy : x ≠ y) :
    cShort (n1ToC ⟨psi1N d, psi1N_mem_N1 d⟩) (v x y hxy) =
      sign (d.1.val x + d.1.val y) • v x y hxy :=
  short_of_conjugation_sign _ (rv x y hxy) (rv x y hxy) _
    (rvElement_conjugation_loopOne d x y)

private theorem short_u_loopTwo (d : ParkerLoop) (x y : Omega) (hxy : x ≠ y) :
    cShort (n1ToC ⟨psi2N d, psi2N_mem_N1 d⟩) (u x y hxy) =
      if d.1.val x + d.1.val y = 0 then u x y hxy else v x y hxy := by
  split_ifs with h
  · exact short_of_conjugation _ (ru x y hxy) (ru x y hxy)
      (by simpa only [ru_val, rv_val, if_pos h] using ruElement_conjugation_loopTwo d x y)
  · exact short_of_conjugation _ (ru x y hxy) (rv x y hxy)
      (by simpa only [ru_val, rv_val, if_neg h] using ruElement_conjugation_loopTwo d x y)

private theorem short_v_loopTwo (d : ParkerLoop) (x y : Omega) (hxy : x ≠ y) :
    cShort (n1ToC ⟨psi2N d, psi2N_mem_N1 d⟩) (v x y hxy) =
      if d.1.val x + d.1.val y = 0 then v x y hxy else u x y hxy := by
  split_ifs with h
  · exact short_of_conjugation _ (rv x y hxy) (rv x y hxy)
      (by simpa only [ru_val, rv_val, if_pos h] using rvElement_conjugation_loopTwo d x y)
  · exact short_of_conjugation _ (rv x y hxy) (ru x y hxy)
      (by simpa only [ru_val, rv_val, if_neg h] using rvElement_conjugation_loopTwo d x y)

private theorem short_u_standard_even (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) (x y : Omega) (hxy : x ≠ y) :
    cShort (n1ToC ⟨psiAut1N α, psiAut1N_mem_N1 α⟩) (u x y hxy) =
      u ((parkerStandardProjection α).val x) ((parkerStandardProjection α).val y)
        (fun e => hxy ((parkerStandardProjection α).val.injective e)) :=
  short_of_conjugation _ (ru x y hxy) _ (ruElement_conjugation_standard_even α hα x y)

private theorem short_u_standard_odd (α : ParkerStandardGroup)
    (hα : α.val parkerOmega ≠ parkerOmega) (x y : Omega) (hxy : x ≠ y) :
    cShort (n1ToC ⟨psiAut1N α, psiAut1N_mem_N1 α⟩) (u x y hxy) =
      -u ((parkerStandardProjection α).val x) ((parkerStandardProjection α).val y)
        (fun e => hxy ((parkerStandardProjection α).val.injective e)) := by
  rw [← neg_one_smul ℝ]
  exact short_of_conjugation_sign _ (ru x y hxy) _ 1
    (by simpa only [ru_val, ZMod.val_one, pow_one] using ruElement_conjugation_standard_odd α hα x y)

private theorem short_v_standard (α : ParkerStandardGroup) (x y : Omega) (hxy : x ≠ y) :
    cShort (n1ToC ⟨psiAut1N α, psiAut1N_mem_N1 α⟩) (v x y hxy) =
      v ((parkerStandardProjection α).val x) ((parkerStandardProjection α).val y)
        (fun e => hxy ((parkerStandardProjection α).val.injective e)) :=
  short_of_conjugation _ (rv x y hxy) _ (rvElement_conjugation_standard α x y)

/-- Aschbacher 29.4(1), for the literal `wPlus = v + u`. -/
theorem cShort_wPlus_loopOne (d : ParkerLoop) (x y : Omega) (hxy : x ≠ y) :
    cShort (n1ToC ⟨psi1N d, psi1N_mem_N1 d⟩) (wPlus x y hxy) =
      sign (d.1.val x + d.1.val y) • wPlus x y hxy := by
  simp only [wPlus, map_add, short_u_loopOne, short_v_loopOne, smul_add]

/-- Aschbacher 29.4(1), for the literal `wMinus = v - u`. -/
theorem cShort_wMinus_loopOne (d : ParkerLoop) (x y : Omega) (hxy : x ≠ y) :
    cShort (n1ToC ⟨psi1N d, psi1N_mem_N1 d⟩) (wMinus x y hxy) =
      sign (d.1.val x + d.1.val y) • wMinus x y hxy := by
  simp only [wMinus, map_sub, short_u_loopOne, short_v_loopOne, smul_sub]

/-- Aschbacher 29.4(2): the second family fixes `wPlus`. -/
theorem cShort_wPlus_loopTwo (d : ParkerLoop) (x y : Omega) (hxy : x ≠ y) :
    cShort (n1ToC ⟨psi2N d, psi2N_mem_N1 d⟩) (wPlus x y hxy) = wPlus x y hxy := by
  simp only [wPlus, map_add, short_u_loopTwo, short_v_loopTwo]
  split_ifs <;> abel

/-- Aschbacher 29.4(2): the second family signs `wMinus`. -/
theorem cShort_wMinus_loopTwo (d : ParkerLoop) (x y : Omega) (hxy : x ≠ y) :
    cShort (n1ToC ⟨psi2N d, psi2N_mem_N1 d⟩) (wMinus x y hxy) =
      sign (d.1.val x + d.1.val y) • wMinus x y hxy := by
  simp only [wMinus, map_sub, short_u_loopTwo, short_v_loopTwo]
  have hb : ∀ b : ParkerBit, b = 0 ∨ b = 1 := by decide
  rcases hb (d.1.val x + d.1.val y) with h | h
  · simp only [h, ↓reduceIte, sign_zero, one_smul]
  · simp only [h, one_ne_zero, ↓reduceIte]
    change u x y hxy - v x y hxy = (-1 : ℝ) • (v x y hxy - u x y hxy)
    calc
      _ = -(v x y hxy - u x y hxy) := by abel
      _ = _ := (neg_one_smul ℝ _).symm

/-- Aschbacher 29.4(3–4): all coordinates move, and odd automorphisms swap the families. -/
theorem cShort_wPlus_standard (α : ParkerStandardGroup) (x y : Omega) (hxy : x ≠ y) :
    cShort (n1ToC ⟨psiAut1N α, psiAut1N_mem_N1 α⟩) (wPlus x y hxy) =
      if α.val parkerOmega = parkerOmega then
        wPlus ((parkerStandardProjection α).val x) ((parkerStandardProjection α).val y)
          (fun e => hxy ((parkerStandardProjection α).val.injective e))
      else wMinus ((parkerStandardProjection α).val x) ((parkerStandardProjection α).val y)
          (fun e => hxy ((parkerStandardProjection α).val.injective e)) := by
  rw [wPlus, map_add, short_v_standard]
  split_ifs with h
  · rw [short_u_standard_even α h]; rfl
  · rw [short_u_standard_odd α h]; rfl

/-- The complementary standard-automorphism action, with the same coordinate transport. -/
theorem cShort_wMinus_standard (α : ParkerStandardGroup) (x y : Omega) (hxy : x ≠ y) :
    cShort (n1ToC ⟨psiAut1N α, psiAut1N_mem_N1 α⟩) (wMinus x y hxy) =
      if α.val parkerOmega = parkerOmega then
        wMinus ((parkerStandardProjection α).val x) ((parkerStandardProjection α).val y)
          (fun e => hxy ((parkerStandardProjection α).val.injective e))
      else wPlus ((parkerStandardProjection α).val x) ((parkerStandardProjection α).val y)
          (fun e => hxy ((parkerStandardProjection α).val.injective e)) := by
  rw [wMinus, map_sub, short_v_standard]
  split_ifs with h
  · rw [short_u_standard_even α h]; rfl
  · rw [short_u_standard_odd α h, sub_neg_eq_add]; rfl

end Sporadic.Monster.Construction.NMonomial.EAction
