module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.Basic
public import Theory.AlgebraicGroup.RootSystems.IntegralRootCurveSimpleGeneration

/-!
# Split generation by the four Ree simple blocks

The exceptional node orbits partition the four simple F₄ nodes. Their signed
blocks contain all signed simple root curves. The integral Tits-word theorem
then puts every root curve in the subgroup they generate. We also verify that
negation exchanges the two signs, including every nonsimple root of the B₂ block.

These are split-group calculations. Fixed intersections do not automatically
preserve generation, so fixed-group generation requires a separate argument.

Source: GLS3, §§2.3–2.4, especially the relative root groups of 2.3.6 and
Table 2.4; Steinberg, Lectures on Chevalley Groups, simple-root generation.
-/

@[expose] public section
namespace ReeF4.LocalBlockInput.PairRigidity
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open LargeLocalSeeds RootPairing.IntegralGeckConstruction
variable {m : ℕ}
noncomputable local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

/-- A simple root belongs to the positive block of its exceptional node orbit. -/
theorem isSimpleBlockRoot_simple (s : Side) (i : Fin 4) (hi : i ∈ leviNodes s) :
    IsSimpleBlockRoot s true (typeF4SimpleRootIndex i) := by
  refine ⟨?_, typeF4RootPairing_base.isPos_of_mem_support
    (typeF4RootPairing_baseEquiv i).property⟩
  intro j hj
  cases s <;> fin_cases i <;> fin_cases j <;>
    norm_num [leviNodes, typeF4SimpleCoefficient, typeF4SimpleRoot, basisVector,
      Fin.ext_iff, Matrix.cons_val_two, Matrix.cons_val_three] at *

private theorem coefficient_neg (x : Vec 4) (i : Fin 4) :
    typeF4SimpleCoefficient (-x) i = -typeF4SimpleCoefficient x i := by
  fin_cases i <;> simp [typeF4SimpleCoefficient] <;> ring

/-- Negation reverses the sign of a block without changing its Levi support. -/
theorem isSimpleBlockRoot_neg_iff (s : Side) (positive : Bool) (r : F4Chevalley.Root) :
    IsSimpleBlockRoot s (!positive) (-r) ↔ IsSimpleBlockRoot s positive r := by
  have hv : (-r).val = -r.val := by
    change typeF4RootPairing.root (-r) = -typeF4RootPairing.root r
    simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self]
  cases positive <;>
    simp only [IsSimpleBlockRoot, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      if_false, if_true, hv, coefficient_neg, neg_eq_zero,
      RootPairing.Base.IsPos.neg_iff_not, not_not]

/-- The opposite simple root belongs to the corresponding negative block. -/
theorem isSimpleBlockRoot_neg_simple (s : Side) (i : Fin 4) (hi : i ∈ leviNodes s) :
    IsSimpleBlockRoot s false (-typeF4SimpleRootIndex i) :=
  (isSimpleBlockRoot_neg_iff s true _).mpr (isSimpleBlockRoot_simple s i hi)

/-- Split seed containment follows on the defining root generators. Descending
this join containment to the fixed group requires a separate collection theorem. -/
theorem splitSeed_le_unipotent_sup_negativeBlock (m : ℕ) (s : Side) :
    splitSeed m s ≤ splitUnipotent m ⊔ splitSimpleBlock m s false := by
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨r, t, hr, rfl⟩
  rcases hr with hpos | ⟨i, hi, rfl⟩
  · exact Subgroup.mem_sup_left (subset_closure ⟨r, t, hpos, rfl⟩)
  · exact Subgroup.mem_sup_right
      (subset_closure ⟨_, t, isSimpleBlockRoot_neg_simple s i hi, rfl⟩)

/-- The four split blocks contain all signed simple curves and generate the split group.
This makes no assertion about generation after taking twist-fixed intersections. -/
theorem splitSimpleBlocks_iSup_eq_top (m : ℕ) :
    (⨆ s, ⨆ positive, splitSimpleBlock m s positive) = ⊤ := by
  let H := ⨆ s, ⨆ positive, splitSimpleBlock m s positive
  have hmem (s : Side) (positive : Bool) (r : F4Chevalley.Root)
      (t : CoefficientField m) (hr : IsSimpleBlockRoot s positive r) :
      rootGeneratorInGroup m r t ∈ H := by
    have hle : splitSimpleBlock m s positive ≤ H :=
      le_iSup_of_le s (le_iSup (fun positive => splitSimpleBlock m s positive) positive)
    exact hle (subset_closure ⟨r, t, hr, rfl⟩)
  have hnode (i : Fin 4) : ∃ s, i ∈ leviNodes s := by
    fin_cases i
    · exact ⟨.linear, by simp [leviNodes]⟩
    · exact ⟨.suzuki, by simp [leviNodes]⟩
    · exact ⟨.suzuki, by simp [leviNodes]⟩
    · exact ⟨.linear, by simp [leviNodes]⟩
  have hs : allRootCurveSubgroup typeF4RootPairing_base (CoefficientField m) ≤
      H.map (SplitGroup m).subtype := by
    rw [allRootCurveSubgroup_eq_simpleSubgroup]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨positive, i⟩, t, rfl⟩
    obtain ⟨j, rfl⟩ := typeF4RootPairing_baseEquiv.surjective i
    obtain ⟨s, hj⟩ := hnode j
    cases positive
    · change RootPairing.SimpleGeckGroup.negativeUnit _ t ∈ _
      rw [← rootCurveUnit_neg_simple]
      exact ⟨rootGeneratorInGroup m (-typeF4SimpleRootIndex j) t,
        hmem s false _ t (isSimpleBlockRoot_neg_simple s j hj), rfl⟩
    · change RootPairing.SimpleGeckGroup.positiveUnit _ t ∈ _
      rw [← rootCurveUnit_simple]
      exact ⟨rootGeneratorInGroup m (typeF4SimpleRootIndex j) t,
        hmem s true _ t (isSimpleBlockRoot_simple s j hj), rfl⟩
  apply top_unique
  intro x _
  have hx : (x : MatrixUnits m) ∈ allRootCurveSubgroup typeF4RootPairing_base
      (CoefficientField m) := x.property
  obtain ⟨y, hy, he⟩ := hs hx
  exact (Subtype.ext he : y = x) ▸ hy

end ReeF4.LocalBlockInput.PairRigidity
end
