module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.EAction.LocalCompatibility.ShortAction
public import Theory.SpecificGroups.Monster.Construction.NMonomial.EAction.LocalCompatibility.SymmetricAction

/-!
# Literal N1/C compatibility of the three E pair families

The short-lift conjugation formulas and the symmetric-square natural action
prove the generator cases of Aschbacher 29.4 and 29.10. Compatibility is
closed under composition by the intrinsic coordinate-sign cocycle. The
proved normal form `standard * loopTwo * loopOne` then gives the comparison
for every element of the actual `N1`, with its fixed map into `C`.

All three vectors are the existing `literalPair` inclusions: the matrix pair,
`wPlus = v + u`, and `wMinus = v - u`. Odd standard automorphisms exchange
the latter families while transporting both coordinates. The geometric
pair-space isomorphism and the full E-space representation remain separate.

Source: Aschbacher, *Sporadic Groups*, 29.4 and 29.10(3), printed pp. 155,
158–159 (PDF pp. 83, 85), using Sections 14 and 27. The source's right-action
normal-form word is reversed for Lean's left composition.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.NMonomial.EAction
open TrialitySpin SignedModules.Natural LocalC LocalC.ShortFamilies Atlas.Codes Atlas.Fischer

private theorem representation_short (g : C) (w : ShortFamilies.Space) :
    cRepresentation g (shortInclusion sourceLatticeComparison w) =
      shortInclusion sourceLatticeComparison (cShort g w) := by
  rw [cRepresentation_apply]
  change (g.val 0, cShort g w, cSymmetric g 0) = (0, cShort g w, 0)
  rw [map_zero, map_zero]

private def Compatible (g : N1) : Prop :=
  ∀ (i : Axis) (x y : Omega) (hxy : x ≠ y),
    cRepresentation (n1ToC g) (eInclusion (literalPair i x y hxy)) =
      sign (coordinateShift g.val i x + coordinateShift g.val i y) •
        eInclusion (literalPair (axisPermutation g.val i)
          (coordinatePermutation g.val x) (coordinatePermutation g.val y)
          (fun e => hxy ((coordinatePermutation g.val).injective e)))

private theorem compatible_mul (g h : N1) (hg : Compatible g) (hh : Compatible h) :
    Compatible (g*h) := by
  intro i x y hxy
  rw [map_mul, map_mul, Module.End.mul_apply, hh, map_smul, hg, smul_smul]
  simp only [Subgroup.coe_mul, coordinateShift_mul, map_mul, Equiv.Perm.mul_apply]
  rw [show coordinateShift h.val i x +
      coordinateShift g.val (axisPermutation h.val i) (coordinatePermutation h.val x) +
      (coordinateShift h.val i y +
      coordinateShift g.val (axisPermutation h.val i) (coordinatePermutation h.val y)) =
      (coordinateShift h.val i x + coordinateShift h.val i y) +
      (coordinateShift g.val (axisPermutation h.val i) (coordinatePermutation h.val x) +
      coordinateShift g.val (axisPermutation h.val i) (coordinatePermutation h.val y)) by abel]
  simp only [sign_add]

private theorem compatible_loopOne (d : ParkerLoop) :
    Compatible ⟨psi1N d, psi1N_mem_N1 d⟩ := by
  intro i x y hxy
  change _ = sign (coordinateShift (loopGenerator 0 d) i x +
    coordinateShift (loopGenerator 0 d) i y) •
      eInclusion (literalPair (axisPermutation (loopGenerator 0 d) i)
        (coordinatePermutation (loopGenerator 0 d) x) (coordinatePermutation (loopGenerator 0 d) y)
        (fun he => hxy ((coordinatePermutation (loopGenerator 0 d)).injective he)))
  simp only [coordinateShift_loop, axisPermutation_loop, coordinatePermutation_loop,
    Equiv.Perm.one_apply]
  rcases ((show ∀ i : Axis, i = 0 ∨ i = 1 ∨ i = 2 by decide) i) with rfl | rfl | rfl
  · have h := localCompatibility_zero ⟨psi1N d, psi1N_mem_N1 d⟩ x y hxy
    change _ = sign (coordinateShift (loopGenerator 0 d) 0 x +
      coordinateShift (loopGenerator 0 d) 0 y) • eInclusion
      (literalPair 0 (coordinatePermutation (loopGenerator 0 d) x)
        (coordinatePermutation (loopGenerator 0 d) y)
        (fun he => hxy ((coordinatePermutation (loopGenerator 0 d)).injective he))) at h
    simpa only [coordinateShift_loop, coordinatePermutation_loop, Equiv.Perm.one_apply, ↓reduceIte] using h
  · simp only [show (0 : Axis) ≠ 1 by decide, ↓reduceIte, literalPair_one,
      eInclusion_pairTwo, representation_short, cShort_wPlus_loopOne, map_smul]
  · simp only [show (0 : Axis) ≠ 2 by decide, ↓reduceIte, literalPair_two,
      eInclusion_pairThree, representation_short, cShort_wMinus_loopOne, map_smul]

private theorem compatible_loopTwo (d : ParkerLoop) :
    Compatible ⟨psi2N d, psi2N_mem_N1 d⟩ := by
  intro i x y hxy
  change _ = sign (coordinateShift (loopGenerator 1 d) i x +
    coordinateShift (loopGenerator 1 d) i y) •
      eInclusion (literalPair (axisPermutation (loopGenerator 1 d) i)
        (coordinatePermutation (loopGenerator 1 d) x) (coordinatePermutation (loopGenerator 1 d) y)
        (fun he => hxy ((coordinatePermutation (loopGenerator 1 d)).injective he)))
  simp only [coordinateShift_loop, axisPermutation_loop, coordinatePermutation_loop,
    Equiv.Perm.one_apply]
  rcases ((show ∀ i : Axis, i = 0 ∨ i = 1 ∨ i = 2 by decide) i) with rfl | rfl | rfl
  · have h := localCompatibility_zero ⟨psi2N d, psi2N_mem_N1 d⟩ x y hxy
    change _ = sign (coordinateShift (loopGenerator 1 d) 0 x +
      coordinateShift (loopGenerator 1 d) 0 y) • eInclusion
      (literalPair 0 (coordinatePermutation (loopGenerator 1 d) x)
        (coordinatePermutation (loopGenerator 1 d) y)
        (fun he => hxy ((coordinatePermutation (loopGenerator 1 d)).injective he))) at h
    simpa only [coordinateShift_loop, coordinatePermutation_loop, Equiv.Perm.one_apply, ↓reduceIte] using h
  · simp only [↓reduceIte, zero_add, sign_zero, one_smul, literalPair_one,
      eInclusion_pairTwo, representation_short, cShort_wPlus_loopTwo]
  · simp only [show (1 : Axis) ≠ 2 by decide, ↓reduceIte, literalPair_two,
      eInclusion_pairThree, representation_short, cShort_wMinus_loopTwo, map_smul]

private theorem compatible_standard (α : ParkerStandardGroup) :
    Compatible ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ := by
  intro i x y hxy
  change _ = sign (coordinateShift (standardGenerator 0 α) i x +
    coordinateShift (standardGenerator 0 α) i y) •
      eInclusion (literalPair (axisPermutation (standardGenerator 0 α) i)
        (coordinatePermutation (standardGenerator 0 α) x)
        (coordinatePermutation (standardGenerator 0 α) y)
        (fun he => hxy ((coordinatePermutation (standardGenerator 0 α)).injective he)))
  simp only [coordinateShift_standard, axisPermutation_standard, coordinatePermutation_standard,
    zero_add, sign_zero, one_smul]
  rcases ((show ∀ i : Axis, i = 0 ∨ i = 1 ∨ i = 2 by decide) i) with rfl | rfl | rfl
  · have h := localCompatibility_zero ⟨psiAut1N α, psiAut1N_mem_N1 α⟩ x y hxy
    change _ = sign (coordinateShift (standardGenerator 0 α) 0 x +
      coordinateShift (standardGenerator 0 α) 0 y) • eInclusion
      (literalPair 0 (coordinatePermutation (standardGenerator 0 α) x)
        (coordinatePermutation (standardGenerator 0 α) y)
        (fun he => hxy ((coordinatePermutation (standardGenerator 0 α)).injective he))) at h
    simpa only [coordinateShift_standard, coordinatePermutation_standard, zero_add,
      sign_zero, one_smul, standardAxes, Equiv.coe_fn_mk, autTarget, oddAxis, ite_self] using h
  · rw [literalPair_one, eInclusion_pairTwo, representation_short, cShort_wPlus_standard]
    by_cases h : α.val parkerOmega = parkerOmega
    · simp only [h, ↓reduceIte, standardAxes, Equiv.coe_fn_mk, autTarget,
        literalPair_one, eInclusion_pairTwo]
    · simp only [h, ↓reduceIte, standardAxes, Equiv.coe_fn_mk, autTarget, oddAxis,
        literalPair_two, eInclusion_pairThree]
  · rw [literalPair_two, eInclusion_pairThree, representation_short, cShort_wMinus_standard]
    by_cases h : α.val parkerOmega = parkerOmega
    · simp only [h, ↓reduceIte, standardAxes, Equiv.coe_fn_mk, autTarget,
        literalPair_two, eInclusion_pairThree]
    · simp only [h, ↓reduceIte, standardAxes, Equiv.coe_fn_mk, autTarget, oddAxis,
        literalPair_one, eInclusion_pairTwo]

/-- Aschbacher 29.10(3) on every literal E pair, for the fixed map from `N1` into `C`.
The three factors in the normal form act in left-composition order. -/
theorem localCompatibility (g : N1) (i : Axis) (x y : Omega) (hxy : x ≠ y) :
    cRepresentation (n1ToC g) (eInclusion (literalPair i x y hxy)) =
      sign (coordinateShift g.val i x + coordinateShift g.val i y) •
        eInclusion (literalPair (axisPermutation g.val i)
          (coordinatePermutation g.val x) (coordinatePermutation g.val y)
          (fun e => hxy ((coordinatePermutation g.val).injective e))) := by
  obtain ⟨⟨d,e,α⟩,rfl⟩ := normalForm_surjective g
  exact compatible_mul _ _
    (compatible_mul _ _ (compatible_standard α) (compatible_loopTwo e))
    (compatible_loopOne d) i x y hxy

/-- Literal first-loop case of 29.4, on all three included E families. -/
theorem literalPair_loopOne (d : ParkerLoop) (i : Axis) (x y : Omega) (hxy : x ≠ y) :
    cRepresentation (n1ToC ⟨psi1N d, psi1N_mem_N1 d⟩) (eInclusion (literalPair i x y hxy)) =
      sign (if (0 : Axis) = i then 0 else d.1.val x + d.1.val y) •
        eInclusion (literalPair i x y hxy) := by
  have h := compatible_loopOne d i x y hxy
  change _ = sign (coordinateShift (loopGenerator 0 d) i x +
    coordinateShift (loopGenerator 0 d) i y) •
      eInclusion (literalPair (axisPermutation (loopGenerator 0 d) i)
        (coordinatePermutation (loopGenerator 0 d) x) (coordinatePermutation (loopGenerator 0 d) y)
        (fun he => hxy ((coordinatePermutation (loopGenerator 0 d)).injective he))) at h
  by_cases hi : (0 : Axis) = i
  · simpa only [coordinateShift_loop, axisPermutation_loop, coordinatePermutation_loop,
      Equiv.Perm.one_apply, if_pos hi, add_zero] using h
  · simpa only [coordinateShift_loop, axisPermutation_loop, coordinatePermutation_loop,
      Equiv.Perm.one_apply, if_neg hi] using h

/-- Literal second-loop case of 29.4, including its fixed `wPlus` family. -/
theorem literalPair_loopTwo (d : ParkerLoop) (i : Axis) (x y : Omega) (hxy : x ≠ y) :
    cRepresentation (n1ToC ⟨psi2N d, psi2N_mem_N1 d⟩) (eInclusion (literalPair i x y hxy)) =
      sign (if (1 : Axis) = i then 0 else d.1.val x + d.1.val y) •
        eInclusion (literalPair i x y hxy) := by
  have h := compatible_loopTwo d i x y hxy
  change _ = sign (coordinateShift (loopGenerator 1 d) i x +
    coordinateShift (loopGenerator 1 d) i y) •
      eInclusion (literalPair (axisPermutation (loopGenerator 1 d) i)
        (coordinatePermutation (loopGenerator 1 d) x) (coordinatePermutation (loopGenerator 1 d) y)
        (fun he => hxy ((coordinatePermutation (loopGenerator 1 d)).injective he))) at h
  by_cases hi : (1 : Axis) = i
  · simpa only [coordinateShift_loop, axisPermutation_loop, coordinatePermutation_loop,
      Equiv.Perm.one_apply, if_pos hi, add_zero] using h
  · simpa only [coordinateShift_loop, axisPermutation_loop, coordinatePermutation_loop,
      Equiv.Perm.one_apply, if_neg hi] using h

/-- Literal standard-automorphism case, including the odd interchange and coordinate transport. -/
theorem literalPair_standard (α : ParkerStandardGroup) (i : Axis) (x y : Omega) (hxy : x ≠ y) :
    cRepresentation (n1ToC ⟨psiAut1N α, psiAut1N_mem_N1 α⟩) (eInclusion (literalPair i x y hxy)) =
      eInclusion (literalPair (autTarget 0 α.val i)
        ((parkerStandardProjection α).val x) ((parkerStandardProjection α).val y)
        (fun e => hxy ((parkerStandardProjection α).val.injective e))) := by
  have h := compatible_standard α i x y hxy
  change _ = sign (coordinateShift (standardGenerator 0 α) i x +
    coordinateShift (standardGenerator 0 α) i y) •
      eInclusion (literalPair (axisPermutation (standardGenerator 0 α) i)
        (coordinatePermutation (standardGenerator 0 α) x)
        (coordinatePermutation (standardGenerator 0 α) y)
        (fun he => hxy ((coordinatePermutation (standardGenerator 0 α)).injective he))) at h
  simpa only [coordinateShift_standard, axisPermutation_standard, coordinatePermutation_standard,
    zero_add, sign_zero, one_smul, standardAxes, Equiv.coe_fn_mk] using h

end Sporadic.Monster.Construction.NMonomial.EAction
