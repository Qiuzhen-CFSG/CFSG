module

public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.Coordinates
-- This leaf reuses the internal equality between the already proved native
-- root layout and its coordinate table. No private names enter the public API.
import all Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.FixedRootFactorization.RootAlignment

/-!
# A degree separating the short roots in the Ree fixed words

Give the long simple roots degree two and the short simple roots degree one.
The resulting Euclidean linear functional is `(11,5,3,1)`. In each native
positive Ree block the long partner has higher degree than the short root,
and every correction factor also has higher degree. The proved complete
pair/quartet partition supplies all twelve short positive roots.

Source: GLS3 Table 2.4 and 2.4.5(d); Steinberg, *Representations of Algebraic
Groups* (1963), the root-action argument in Section 12.
-/

public section
noncomputable section

namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.RootCurves

open Theory.AlgebraicGroup StandardRootSystem
open Parabolics RadicalCoordinates RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration

local instance rootNeg : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

/-- Long simple roots have degree two, short simple roots degree one. -/
@[expose] def degree (v : Vec 4) : ℝ := 11 * v 0 + 5 * v 1 + 3 * v 2 + v 3

/-- The additive degree of a literal native F4 root. -/
@[expose] def rootDegree (r : F4Chevalley.Root) : ℝ := degree r.val

theorem degree_add (v w : Vec 4) : degree (v + w) = degree v + degree w := by
  simp only [degree, Pi.add_apply]
  ring

theorem degree_smul (a : ℝ) (v : Vec 4) : degree (a • v) = a * degree v := by
  simp only [degree, Pi.smul_apply, smul_eq_mul]
  ring

theorem degree_neg (v : Vec 4) : degree (-v) = -degree v := by
  simp only [degree, Pi.neg_apply]
  ring

theorem rootDegree_neg (r : F4Chevalley.Root) : rootDegree (-r) = -rootDegree r := by
  have hv : (-r).val = -r.val := by
    change typeF4RootPairing.root (-r) = -typeF4RootPairing.root r
    simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self]
  exact (congrArg degree hv).trans (degree_neg r.val)

theorem degree_simple (i : Fin 4) :
    rootDegree (typeF4SimpleRootIndex i) = if i.val < 2 then 2 else 1 := by
  fin_cases i <;> norm_num [rootDegree, typeF4SimpleRootIndex_val, degree,
    typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three]

/-- Every positive root has strictly positive degree. -/
theorem rootDegree_pos {r : F4Chevalley.Root} (hr : typeF4RootPairing_base.IsPos r) :
    0 < rootDegree r := by
  have hs (i : F4Chevalley.Root) (hi : i ∈ typeF4RootPairing_base.support) :
      0 < rootDegree i := by
    obtain ⟨j, hj⟩ := typeF4RootPairing_baseEquiv.surjective ⟨i, hi⟩
    have he : typeF4SimpleRootIndex j = i := congrArg Subtype.val hj
    rw [← he, degree_simple]
    split_ifs <;> norm_num
  apply hr.induction_on_add
  · exact hs
  · intro i j k hk hi hj
    change k.val = i.val + j.val at hk
    change 0 < degree k.val
    rw [hk, degree_add]
    exact add_pos hi (hs j hj)

private theorem layout_val (a : Slot .positive) :
    (positiveRootWordLayout.blocks.roots a).val.val = RootPartition.table
      (RootPartition.index .positive a) :=
  rootBlocks_roots_val .positive a

private theorem pair_degrees (j : Fin 4) :
    rootDegree (shortRoot (positiveRootWordLayout.pairIndex j)) <
      rootDegree (longRoot (positiveRootWordLayout.pairIndex j)) := by
  rw [← positiveRootWordLayout.pair_short j, ← positiveRootWordLayout.pair_long j]
  change degree _ < degree _
  rw [layout_val, layout_val]
  fin_cases j <;> norm_num [degree, RootPartition.index, RootPartition.pairRow,
    RootPartition.table, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem quartet_degrees (j : Fin 4) :
    rootDegree (shortRoot (positiveRootWordLayout.quartetIndex j)) <
      rootDegree (longRoot (positiveRootWordLayout.quartetIndex j)) ∧
    rootDegree (shortRoot (positiveRootWordLayout.quartetIndex j)) <
      rootDegree (mixedRoot (positiveRootWordLayout.quartetIndex j)) ∧
    rootDegree (mixedRoot (positiveRootWordLayout.quartetIndex j)) <
      rootDegree (highRoot (positiveRootWordLayout.quartetIndex j)) := by
  rw [← positiveRootWordLayout.quartet_short j, ← positiveRootWordLayout.quartet_long j,
    ← positiveRootWordLayout.quartet_mixed j, ← positiveRootWordLayout.quartet_high j]
  change degree _ < degree _ ∧ degree _ < degree _ ∧ degree _ < degree _
  simp only [layout_val]
  fin_cases j <;> norm_num [degree, RootPartition.index, RootPartition.quartetRow,
    RootPartition.table, Matrix.cons_val_two, Matrix.cons_val_three]

/-- Every positive short root is the short member of a main curve or the
short member of a central curve; all other factors have strictly higher degree. -/
theorem positive_short_cases {r : F4Chevalley.Root}
    (hr : typeF4RootPairing_base.IsPos r) (hs : IsShortRoot r) :
    (∃ i : Fin 8, r = shortRoot i ∧ rootDegree r < rootDegree (longRoot i) ∧
      (i.val % 2 = 0 → rootDegree r < rootDegree (mixedRoot i))) ∨
    (∃ i : Fin 8, i.val % 2 = 0 ∧ r = mixedRoot i ∧
      rootDegree r < rootDegree (highRoot i)) := by
  let rr : Root .positive := ⟨r, hr⟩
  obtain ⟨a, ha⟩ := positiveRootWordLayout.blocks.roots.surjective rr
  have he : (positiveRootWordLayout.blocks.roots a).val = r := congrArg Subtype.val ha
  cases a with
  | inl a =>
    rcases a with ⟨j, k⟩
    fin_cases k <;> dsimp only at he
    · exact (hs (he ▸ positiveRootWordLayout.blocks.pair_long j)).elim
    · have h : r = shortRoot (positiveRootWordLayout.pairIndex j) :=
        he.symm.trans (positiveRootWordLayout.pair_short j)
      refine Or.inl ⟨positiveRootWordLayout.pairIndex j, h, ?_, ?_⟩
      · simpa only [h] using pair_degrees j
      · intro hh
        exact (positiveRootWordLayout.pair_odd j hh).elim
  | inr a =>
    rcases a with ⟨j, k⟩
    fin_cases k <;> dsimp only at he
    · exact (hs (he ▸ positiveRootWordLayout.blocks.quartet_long j)).elim
    · have h : r = shortRoot (positiveRootWordLayout.quartetIndex j) :=
        he.symm.trans (positiveRootWordLayout.quartet_short j)
      exact Or.inl ⟨positiveRootWordLayout.quartetIndex j, h,
        by simpa only [h] using (quartet_degrees j).1, fun _ => by simpa only [h] using (quartet_degrees j).2.1⟩
    · have h : r = mixedRoot (positiveRootWordLayout.quartetIndex j) :=
        he.symm.trans (positiveRootWordLayout.quartet_mixed j)
      exact Or.inr ⟨positiveRootWordLayout.quartetIndex j,
        positiveRootWordLayout.quartet_even j, h, by simpa only [h] using (quartet_degrees j).2.2⟩
    · have hlong : IsLongRoot (positiveRootWordLayout.blocks.roots (.inr (j, 3))).val := by
        rw [← positiveRootWordLayout.blocks.quartet_dual_two j]
        exact (exceptionalRootPermutation_short_iff _).mp
          (positiveRootWordLayout.blocks.quartet_short_two j)
      exact (hs (he ▸ hlong)).elim

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.RootCurves
