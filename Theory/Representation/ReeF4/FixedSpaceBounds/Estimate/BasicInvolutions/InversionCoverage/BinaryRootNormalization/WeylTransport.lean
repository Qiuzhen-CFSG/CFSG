module

public import Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.Roots
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.BinaryRootNormalization.Layout

/-!
# Fixed Weyl changes for the two binary root markings

The middle--end--middle Weyl word carries the paired end curve to the fourth
relative curve. Two middle--end rotations carry the central parameter of
the first B₂ block to the fifth block. The absolute high and mixed roots
are checked against the published positive-root table, and integral root
transport supplies their exact parameter-preserving conjugations.

Both Weyl actors are products of the existing twist-fixed orbit words,
so their conjugations take place in the literal Ree model. These formulas
connect the binary matrix markings and torus scalings in the parent module.

Source: GLS3, Table 2.4 and §2.4; Parrott (1972), §5, p.683;
Guralnick--Malle, *Classification of 2F-modules, II*, Lemma 8.8, p.57.
-/

public section
noncomputable section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.Normalization
open ReeF4.NormalizedRootCentralizers.CenterExponent
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Parabolics Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations
open Parabolics.Binary.FixedGeometry


private theorem simpleWord_append (m : ℕ) (u v : List (Fin 4)) :
    simpleWord m (u ++ v) = simpleWord m u * simpleWord m v := by
  simp [simpleWord]

private def shortWord : List (Fin 4) :=
  sideWord .suzuki ++ sideWord .linear ++ sideWord .suzuki

private def longWord : List (Fin 4) :=
  (sideWord .suzuki ++ sideWord .linear) ++ (sideWord .suzuki ++ sideWord .linear)

private theorem shortWord_fixed (m : ℕ) :
    reeTwist m (simpleWord m shortWord) = simpleWord m shortWord := by
  simp only [shortWord, simpleWord_append, map_mul, sideWord_fixed]

private theorem longWord_fixed (m : ℕ) :
    reeTwist m (simpleWord m longWord) = simpleWord m longWord := by
  simp only [longWord, simpleWord_append, map_mul, sideWord_fixed]

def shortWeyl (m : ℕ) : Model m :=
  ⟨simpleWord m shortWord, (mem_fixedSubgroup m _).mpr (shortWord_fixed m)⟩

def longWeyl (m : ℕ) : Model m :=
  ⟨simpleWord m longWord, (mem_fixedSubgroup m _).mpr (longWord_fixed m)⟩

theorem shortWeyl_conjugate (m : ℕ) (t : CoefficientField m) :
    toSplitGroup m (shortWeyl m) * endRootWord m t *
      (toSplitGroup m (shortWeyl m))⁻¹ = rootWord m 3 t := by
  have hl (u : CoefficientField m) :
      simpleWord m shortWord * rootGeneratorInGroup m (typeF4SimpleRootIndex 0) u *
        (simpleWord m shortWord)⁻¹ = rootGeneratorInGroup m (longRoot 3) u :=
    simpleWord_conjugate_simple m shortWord 0 _ (longRoot_pos 3) rfl u
  have hs := congrArg (reeTwist m) (hl t)
  simp only [map_mul, map_inv, shortWord_fixed, reeTwist_rootGenerator,
    ← rootFieldEnd_apply] at hs
  rw [exceptionalRootPermutation_simple] at hs
  change simpleWord m shortWord * rootGeneratorInGroup m (typeF4SimpleRootIndex 3)
    (rootFieldEnd m (typeF4SimpleRootIndex 0) t) * (simpleWord m shortWord)⁻¹ = _ at hs
  simp only [toSplitGroup_apply]
  change simpleWord m shortWord * endRootWord m t * (simpleWord m shortWord)⁻¹ = _
  calc
    _ = (simpleWord m shortWord * rootGeneratorInGroup m (typeF4SimpleRootIndex 0) t *
        (simpleWord m shortWord)⁻¹) *
        (simpleWord m shortWord * rootGeneratorInGroup m (typeF4SimpleRootIndex 3)
        (rootFieldEnd m (typeF4SimpleRootIndex 0) t) * (simpleWord m shortWord)⁻¹) := by
      simp [endRootWord, mul_assoc]
    _ = _ := by rw [hl, hs]; simp [rootWord, shortRoot]

private theorem high_coordinates (j : Fin 4) :
    (highRoot (positiveRootWordLayout.quartetIndex j)).val =
      RootPartition.table (RootPartition.index .positive (.inr (j, 3))) := by
  erw [← positiveRootWordLayout.quartet_high j]
  erw [positive_layout_blocks]
  exact rootBlocks_roots_val .positive (.inr (j, 3))

private theorem mixed_coordinates (j : Fin 4) :
    (mixedRoot (positiveRootWordLayout.quartetIndex j)).val =
      RootPartition.table (RootPartition.index .positive (.inr (j, 2))) := by
  erw [← positiveRootWordLayout.quartet_mixed j]
  erw [positive_layout_blocks]
  exact rootBlocks_roots_val .positive (.inr (j, 2))

private theorem high_pos (j : Fin 4) :
    typeF4RootPairing_base.IsPos (highRoot (positiveRootWordLayout.quartetIndex j)) := by
  erw [← positiveRootWordLayout.quartet_high j]
  exact (positiveRootWordLayout.blocks.roots (.inr (j, 3))).property

private theorem mixed_pos (j : Fin 4) :
    typeF4RootPairing_base.IsPos (mixedRoot (positiveRootWordLayout.quartetIndex j)) := by
  erw [← positiveRootWordLayout.quartet_mixed j]
  exact (positiveRootWordLayout.blocks.roots (.inr (j, 2))).property

private def reflectedVector : Fin 4 → Vec 4 → Vec 4
  | 0, v => ![v 0, v 2, v 1, v 3]
  | 1, v => ![v 0, v 1, v 3, v 2]
  | 2, v => ![v 0, v 1, v 2, -v 3]
  | 3, v => ![(v 0 + v 1 + v 2 + v 3) / 2,
      (v 0 + v 1 - v 2 - v 3) / 2,
      (v 0 - v 1 + v 2 - v 3) / 2,
      (v 0 - v 1 - v 2 + v 3) / 2]

private theorem reflection_val (i : Fin 4) (r : F4Chevalley.Root) :
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val =
      reflectedVector i r.val := by
  change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm _ r) = _
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    typeF4RootPairing_pairing, typeF4CorootScale_simpleRoot]
  simp only [typeF4RootPairing_root, typeF4SimpleRootIndex_val]
  fin_cases i <;> ext k <;> fin_cases k <;>
    simp [reflectedVector, typeF4SimpleRoot, dot, Fin.sum_univ_four] <;> ring

private theorem route_high (b : Bool) :
    reflectionWord (P := typeF4RootPairing)
      (((if b then longWord else []) ++ [2]).map typeF4RootPairing_baseEquiv)
      (typeF4SimpleRootIndex 1) = highRoot (if b then 4 else 0) := by
  apply Subtype.ext
  cases b
  · rw [show highRoot (if false then 4 else 0) =
        highRoot (positiveRootWordLayout.quartetIndex (0 : Fin 4)) from by rw [positive_quartet_indices]; rfl, high_coordinates]
    norm_num [reflectionWord, longWord, sideWord, reflection_val, reflectedVector,
      RootPartition.index, RootPartition.quartetRow, RootPartition.table, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three]
  · rw [show highRoot (if true then 4 else 0) =
        highRoot (positiveRootWordLayout.quartetIndex (1 : Fin 4)) from by rw [positive_quartet_indices]; rfl, high_coordinates]
    norm_num [reflectionWord, longWord, sideWord, reflection_val, reflectedVector,
      RootPartition.index, RootPartition.quartetRow, RootPartition.table, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem route_mixed (b : Bool) :
    reflectionWord (P := typeF4RootPairing)
      (((if b then longWord else []) ++ [1]).map typeF4RootPairing_baseEquiv)
      (typeF4SimpleRootIndex 2) = mixedRoot (if b then 4 else 0) := by
  apply Subtype.ext
  cases b
  · rw [show mixedRoot (if false then 4 else 0) =
        mixedRoot (positiveRootWordLayout.quartetIndex (0 : Fin 4)) from by rw [positive_quartet_indices]; rfl, mixed_coordinates]
    norm_num [reflectionWord, longWord, sideWord, reflection_val, reflectedVector,
      RootPartition.index, RootPartition.quartetRow, RootPartition.table, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three]
  · rw [show mixedRoot (if true then 4 else 0) =
        mixedRoot (positiveRootWordLayout.quartetIndex (1 : Fin 4)) from by rw [positive_quartet_indices]; rfl, mixed_coordinates]
    norm_num [reflectionWord, longWord, sideWord, reflection_val, reflectedVector,
      RootPartition.index, RootPartition.quartetRow, RootPartition.table, typeF4SimpleRoot, Matrix.cons_val_two, Matrix.cons_val_three]

theorem longWeyl_conjugate (m : ℕ) (t : CoefficientField m) :
    toSplitGroup m (longWeyl m) * centralWord m 0 t *
      (toSplitGroup m (longWeyl m))⁻¹ = centralWord m 4 t := by
  have hh (u : CoefficientField m) :
      simpleWord m longWord * rootGeneratorInGroup m (highRoot 0) u *
        (simpleWord m longWord)⁻¹ = rootGeneratorInGroup m (highRoot 4) u := by
    have h0 := simpleWord_conjugate_simple m [2] 1 (highRoot 0) (by simpa only [positive_quartet_indices, Matrix.cons_val_zero] using high_pos 0) (route_high false) u
    have h4 := simpleWord_conjugate_simple m (longWord ++ [2]) 1 (highRoot 4) (by simpa only [positive_quartet_indices, Matrix.cons_val_one, Matrix.cons_val_zero] using high_pos 1) (route_high true) u
    rw [simpleWord_append] at h4
    rw [← h0]
    convert h4 using 1
    group
  have hc (u : CoefficientField m) :
      simpleWord m longWord * rootGeneratorInGroup m (mixedRoot 0) u *
        (simpleWord m longWord)⁻¹ = rootGeneratorInGroup m (mixedRoot 4) u := by
    have h0 := simpleWord_conjugate_simple m [1] 2 (mixedRoot 0) (by simpa only [positive_quartet_indices, Matrix.cons_val_zero] using mixed_pos 0) (route_mixed false) u
    have h4 := simpleWord_conjugate_simple m (longWord ++ [1]) 2 (mixedRoot 4) (by simpa only [positive_quartet_indices, Matrix.cons_val_one, Matrix.cons_val_zero] using mixed_pos 1) (route_mixed true) u
    rw [simpleWord_append] at h4
    rw [← h0]
    convert h4 using 1
    group
  have hf : rootFieldEnd m (longRoot 0) = rootFieldEnd m (longRoot 4) := by
    simp only [rootFieldEnd, if_pos (longRoot_isLong _)]
  simp only [toSplitGroup_apply]
  change simpleWord m longWord * centralWord m 0 t * (simpleWord m longWord)⁻¹ = _
  calc
    _ = (simpleWord m longWord * rootGeneratorInGroup m (highRoot 0) t *
          (simpleWord m longWord)⁻¹) *
        (simpleWord m longWord * rootGeneratorInGroup m (mixedRoot 0)
          (rootFieldEnd m (longRoot 0) t) * (simpleWord m longWord)⁻¹) := by
      simp [centralWord, mul_assoc]
    _ = _ := by rw [hh, hc, hf]; rfl

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.Normalization
